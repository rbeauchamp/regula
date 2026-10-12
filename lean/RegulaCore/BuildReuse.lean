import Regula.Contract
import Regula.Decision

/-! # Reuse of the first acceptance step's build by the documentation step

The documentation step (`docFenceAudit --acceptance-link`) builds the claimed surface in a copy of
the project that it makes with no build output. The first acceptance step built the same targets
in a copy that the verification driver made, and in a checkout with no build output the driver
moves that build output to the checkout's `.lake/build` (`RegulaVerification.Copy.adopt`). The
driver then records, in the acceptance link, the targets of that build, the SHA-256 of every file
of its copy outside `.lake` (the tree) and the SHA-256 of every file below `lib` and `ir` of the
build output it moved (the artifacts).

The documentation step stages only the artifacts of the modules its own claimed build compiles:
the modules of the claimed targets and those they import transitively, as Lake reports them
(`closure`). A module that step built for another target, such as a diagnostic executable, stays
out, so a documentation example sees exactly the modules a fresh build of the step leaves. It copies
those artifacts from the checkout's `.lake/build` into a staging directory outside its copy,
takes the SHA-256 of each staged file and of each file of its copy outside `.lake`, and asks
`reuse`. A module that the later Verso build needs beyond the closure is compiled in the copy, as
on the fresh path. Only when `reuse` accepts does it move the staging directory to
its copy's `.lake/build`; otherwise its copy stays as it made it, with no build output, and the
step builds as it did before this decision existed. Either way the step then runs the same build:
Lake decides from its own traces whether to use a placed artifact or to compile the module again in
the copy, and the build still requires exit status 0, no warning, and a trace that records an
elaboration for each claimed module (`Regula.Checker.Lake.Build.run`), whose log Lake replays when
it uses the trace. So every compiled artifact of the root package the step reads was compiled, in a
copy that held no earlier build output, from files equal to those of the copy the step captures and
checks: in this run, or in the first step whose record `reuse` accepted (`reuse_iff`).

Assumes:
- SHA-256 is collision resistant: equal digests are taken to mean equal bytes. The digests are
  computed by the external `shasum -a 256`, trusted as the acceptance link's identity trusts it.
- The verification driver made its copy new, with no build output (trusted for the first step's
  `driverCopy` origin already, `AxiomGate.driverCopy`).
- The elaboration of the root package reads no file outside its project tree other than the pinned
  toolchain: `include_str` (Lean v4.34.1, `Lean/Elab/BuiltinTerm.lean`, `elabIncludeStr`) reads a
  path relative to the module's source, and the root package's uses name files of its tree. Trusted.
- Both builds use the root package's own Lean options and no artifact cache: the driver's
  `lake build` with `LAKE_ARTIFACT_CACHE=false` (`RegulaVerification.start`) and the documentation
  step's `Build.run` with no option override.
- Lake writes each artifact of a module below `lib/lean` or `ir` of the build directory at the
  module's path with an extension (Lean v4.34.1, `Lean.modToFilePath`; Lake `Module.oleanFile` and
  the other module artifact files), and the root package's build directory holds artifacts of its
  own modules only. Trusted. -/

namespace Regula.Checker.BuildReuse

/-- A file by its path, relative to a directory and written with `/`, and its SHA-256 in lowercase
hexadecimal. -/
abbrev Digest := String × String

/-- What the first acceptance step's record says about the build it left: the targets of its
build command, the digests of every file of its copy outside `.lake`, and the digests of every file
below `lib` and `ir` of the build output it moved to the checkout's `.lake/build`. -/
structure Retained where
  /-- The targets of the first step's build command. -/
  targets : List String
  /-- Every file of the first step's copy outside `.lake`, with its digest, taken when the copy was
  made and before any command ran in it. -/
  tree : List Digest
  /-- Every file below `lib` and `ir` of the build output the first step moved, by its path below
  `.lake/build`, with its digest. -/
  artifacts : List Digest
  deriving Repr, DecidableEq

/-- The parts of the acceptance link that `reuse` reads. -/
structure Link where
  /-- The record has schema version 1 and the status `accepted`. -/
  accepted : Bool
  /-- The identity of the inputs that the first step's gate accepted. -/
  identity : String
  /-- Where the build output that the gate audited came from (`AxiomGate.Origin.spelling`). -/
  origin : String
  /-- The build the first step left, when the driver recorded one. -/
  build : Option Retained
  deriving Repr, DecidableEq

/-- What the documentation step observed of its own run. -/
structure Run where
  /-- The identity of its own captured inputs. -/
  identity : String
  /-- The targets of its claimed build: each claimed library and executable. -/
  targets : List String
  /-- The module path (`moduleOf`) of every module of the root package: each module of its
  libraries and each root of its executables. -/
  modules : List String
  /-- The module path of each root-package module of its claimed build: the modules of the claimed
  targets and those they import transitively, as Lake reports them. -/
  closure : List String
  /-- Every file of its copy outside `.lake`, with its digest. -/
  tree : List Digest
  /-- Every file it staged from the checkout's `.lake/build`, with the digest of the staged file. -/
  staged : List Digest
  deriving Repr, DecidableEq

/-- Whether a recorded artifact path names a place below the directory it is joined to: no
component is empty, `.` or `..`, so it is neither absolute nor leaves the directory. The
documentation step stages only artifacts whose every path is so. -/
def below (path : String) : Bool :=
  (path.splitOn "/").all fun component => component != "" && component != "." && component != ".."

/-- The module path of the module a file of a build directory belongs to: for `lib/lean/D/F` or
`ir/D/F`, where `F` holds a dot, the path `D/N` with `N` the part of `F` before its first dot;
`none` for any other path. Lake writes each artifact of a module below `lib/lean` or `ir` at the
module's path with an extension (`Lean.modToFilePath`), so when no component of a module name holds
a dot (`plain`), this is the path of the module that wrote the file. -/
def moduleOf (path : String) : Option String :=
  let stem (rest : List String) : Option String :=
    match rest.reverse with
    | file :: dirs =>
      match file.splitOn "." with
      | name :: _ :: _ => some ("/".intercalate (dirs.reverse ++ [name]))
      | _ => none
    | [] => none
  match path.splitOn "/" with
  | "lib" :: "lean" :: rest => stem rest
  | "ir" :: rest => stem rest
  | _ => none

/-- Whether a module path has no empty component and no component that holds a dot, so that
`moduleOf` maps each file of its module to it and no file of another module to it. -/
def plain (stem : String) : Bool :=
  (stem.splitOn "/").all fun component => component != "" && (component.splitOn ".").length == 1

/-- The recorded artifacts that belong to a module of `closure` (`moduleOf`): the files the
documentation step stages. -/
def selected (closure : List String) (artifacts : List Digest) : List Digest :=
  artifacts.filter fun artifact => match moduleOf artifact.1 with
    | some stem => closure.contains stem
    | none => false

/-- Reuse the first step's build exactly when the link is an accepted record of a gate that audited
the driver's copy, over the run's own identity; it records a build whose targets include each of
the run's; every recorded artifact path stays below `.lake/build`; every module path of the root
package is `plain`; the files of the two copies outside `.lake` are the same with the same digests;
and the staged files are exactly the recorded artifacts of the modules of the run's closure, with
the same digests (`reuse_iff`). -/
@[regula_decision]
def reuse (link : Link) (run : Run) : Bool :=
  match link.build with
  | none => false
  | some build =>
      link.accepted && link.identity == run.identity && link.origin == "driverCopy" &&
        run.targets.all build.targets.contains && build.artifacts.all (below ·.1) &&
        run.modules.all plain && build.tree.isPerm run.tree &&
        (selected run.closure build.artifacts).isPerm run.staged

/-- The recorded artifacts that `selected` keeps are those whose `moduleOf` is a module path of the
closure. -/
theorem selected_eq (closure : List String) (artifacts : List Digest) :
    selected closure artifacts =
      artifacts.filter fun artifact =>
        decide (∃ stem ∈ closure, moduleOf artifact.1 = some stem) := by
  unfold selected
  congr 1
  funext artifact
  cases h : moduleOf artifact.1 <;> simp

/-- `reuse` accepts exactly a link that is accepted, has the run's identity and the `driverCopy`
origin, and records a build that names each target of the run, whose artifact paths have no empty,
`.` or `..` component, whose tree is a permutation of the run's tree, and whose artifacts
that belong to a module of the run's closure are a permutation of the staged files' digests, when
no module path of the root package has an empty component or a component that holds a dot. -/
theorem reuse_iff (link : Link) (run : Run) :
    reuse link run = true ↔
      link.accepted = true ∧ link.identity = run.identity ∧ link.origin = "driverCopy" ∧
        ∃ build, link.build = some build ∧ (∀ target ∈ run.targets, target ∈ build.targets) ∧
          (∀ artifact ∈ build.artifacts, ∀ component ∈ artifact.1.splitOn "/",
            component ≠ "" ∧ component ≠ "." ∧ component ≠ "..") ∧
          (∀ stem ∈ run.modules, ∀ component ∈ stem.splitOn "/",
            component ≠ "" ∧ (component.splitOn ".").length = 1) ∧
          build.tree.Perm run.tree ∧
          (build.artifacts.filter fun artifact =>
            decide (∃ stem ∈ run.closure, moduleOf artifact.1 = some stem)).Perm run.staged := by
  obtain ⟨accepted, identity, origin, build⟩ := link
  cases build with
  | none => simp [reuse]
  | some build =>
    simp only [reuse, ← selected_eq]
    simp [below, plain, List.isPerm_iff, List.all_eq_true, Bool.and_eq_true, and_assoc]

/-- `reuse` accepts exactly the links that `reuse_iff` states: it accepts a link that records an
empty build of the run's identity, and refuses one that records no build. -/
theorem checked_reuse : Regula.ExecutableContract reuse (fun decide =>
    Regula.Decides (· = true)
      (fun input : Link × Run =>
        input.1.accepted = true ∧ input.1.identity = input.2.identity ∧
          input.1.origin = "driverCopy" ∧
          ∃ build, input.1.build = some build ∧
            (∀ target ∈ input.2.targets, target ∈ build.targets) ∧
            (∀ artifact ∈ build.artifacts, ∀ component ∈ artifact.1.splitOn "/",
              component ≠ "" ∧ component ≠ "." ∧ component ≠ "..") ∧
            (∀ stem ∈ input.2.modules, ∀ component ∈ stem.splitOn "/",
              component ≠ "" ∧ (component.splitOn ".").length = 1) ∧
            build.tree.Perm input.2.tree ∧
            (build.artifacts.filter fun artifact =>
              Decidable.decide (∃ stem ∈ input.2.closure, moduleOf artifact.1 = some stem)).Perm
                input.2.staged)
      (Function.uncurry decide)) :=
  ⟨.of_iff (fun input => reuse_iff input.1 input.2)
    ⟨(⟨true, "", "driverCopy", some ⟨[], [], []⟩⟩, ⟨"", [], [], [], [], []⟩), by decide⟩
    ⟨(⟨true, "", "driverCopy", none⟩, ⟨"", [], [], [], [], []⟩), by decide⟩⟩

end Regula.Checker.BuildReuse
