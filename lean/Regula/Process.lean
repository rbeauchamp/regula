module

public import Lake.Config.InstallPath
public import Lake.Config.Env
public import Lean
public import Regula.Assumption
public import RegulaPolicy.StateTriple
public import RegulaPolicy.Compiler
import all RegulaPolicy.StateTriple
public meta import Lake.Config.InstallPath
public meta import Lean
meta import Regula.Assumption

/-! # The process and environment observer

Every project process start consumes a typed selection. The common implementation is elaborated
by Lean's own frontend here and in the cold-start drivers, where no package artifacts exist.
The compiled reach check admits this module's observer operations and names the drivers' bounded
bootstrap exemptions. The kernel proves path admission; process execution, environment reads,
compiler self-report and the installation's contents remain trusted external boundaries. -/

public section

namespace Regula.Process

-- The included definitions are generated at this directive. Lean's user-command range API
-- records that real origin, rather than interpreting the included buffer's offsets in this file
-- (v4.34.1 Lean/Elab/DeclarationRange.lean:50-55). Only newly generated declarations are tagged.
run_cmd do
  let origin ← Lean.getRef
  let before ← Lean.getEnv
  let input := Lean.Parser.mkInputContext (include_str "ProcessSource.inc") "Regula/ProcessSource.inc"
  let result ← Lean.Elab.IO.processCommands input {} (← get)
  set result.commandState
  for (name, _) in result.commandState.env.constants.toList do
    unless before.contains name do
      Lean.Elab.addDeclarationRangesFromSyntax name origin

/-- The installed observer's cache stores only tokens whose constructor is private. As with the
observer itself, deliberate access to private constructors is outside the honest-code boundary. -/
initialize installationCache : IO.Ref (Option Installation) ← IO.mkRef none

/-- This compiled observer retains the checked token for its process. Cold-source drivers
elaborate the same implementation with its initializer-free default cache context. -/
instance : Cache where
  find := installationCache.get
  save := installationCache.set ∘ some

attribute [regula_observer environment] readEnv currentDir appPath setCurrentDir
attribute [regula_observer process] candidateRoot identified spawn output

/-- Initial options for source elaboration in a Regula executable. Lean's builtin bv_decide
otherwise looks beside this executable, then on PATH for cadical, instead of beside the selected
Lean. Use its own sat.solver option to supply the checked toolchain path. This covers the solver
only while elaborated source leaves the option unset. A source setting sat.solver, including a
reset to empty, selects its own program, as run_cmd can do; that route remains uncovered.
Assumes: Lean v4.34.1 `Lean/Meta/Tactic/BVDecide/TacticContext.lean:55-66` uses a nonempty
sat.solver option directly, so the checked initial option avoids its sibling/PATH fallback only
while source leaves it unset. Issue 411 owns source-option refusal after issue 279's observer. -/
def leanOptions : IO Lean.Options := do
  return ({} : Lean.Options).set `sat.solver (← toolPath .cadical).toString

/-- The Lake environment of the toolchain's identity-checked installation (`lakeSysroot`), with the
Lake installed beside its Lean (`LakeInstall.ofLean`), as the toolchain's `lake` command computes it
for itself: a listed entry of the process and environment rows of `Regula.Removal.boundaries` for
each of its three Lake calls. Lake's own `findInstall?` is not run: it reads the running program as
a `lake`, so a `lean` beside this checker's executable would select the checker's build directory
as the installation, and it reads `LAKE_HOME`, which a parent `lake` sets to the toolchain's root,
as the root of a Lake build tree. The installation's commit is the one `identified` checked its
`lean` reports. -/
@[noinline] def lakeEnvironment : IO _root_.Lake.Env := do
  let sysroot ← lakeSysroot
  let elan? ← _root_.Lake.findElanInstall?
  let lean ← _root_.Lake.LeanInstall.get sysroot (collocated := true)
  let lean := { lean with githash := RegulaPolicy.Compiler.commit }
  let lake := _root_.Lake.LakeInstall.ofLean lean
  match ← EIO.toIO' (_root_.Lake.Env.compute lake lean elan?) with
  | .ok env => return env
  | .error error => throw <| IO.userError s!"lake-workspace-load-failed: {error}"

/-- Initialize Lean's module search path, `Lean.initSearchPath`, at the identity-checked
installation (`sysroot`): a listed entry of the environment row of `Regula.Removal.boundaries`. -/
@[noinline] def initSearchPath : IO Unit := do
  Lean.initSearchPath (← sysroot)

/-- Lean's source search path, `Lean.getSrcSearchPath`: a listed entry of the environment row of
`Regula.Removal.boundaries`. -/
@[noinline] def srcSearchPath : IO System.SearchPath :=
  Lean.getSrcSearchPath

open Regula.StateTriple

/-- The external facts of a launch, read over the very worlds its IO implementation runs on.
The target and environment describe the child's launch configuration, not successful execution:
Lean's POSIX spawn returns after fork, before the child's exec can fail. -/
structure Model where
  /-- The current process's environment in each world. -/
  environment : Void IO.RealWorld → String → Option String
  /-- The pathname selected for a returned child's launch, even if its exec later fails. -/
  target : Void IO.RealWorld → UInt32 → String → Prop
  /-- The environment configured for that child at launch, before its own code changes it. -/
  childEnvironment : Void IO.RealWorld → UInt32 → String → Option String
  /-- Every native setenv/unsetenv operation for this launch succeeds. The runtime ignores their
  return values (`runtime/process.cpp:463-469`), so valid strings alone do not establish this. -/
  updatesSucceeded : Void IO.RealWorld → IO.Process.SpawnArgs → Prop

/-- The environment primitive reports the named variable's value and changes no world state.
Concurrent changes to the process environment are excluded by this hypothesis. -/
@[regula_assumption environment
  (lean "v4.34.1" "Init/System/IO.lean#L951-L955")
  (lean "v4.34.1" "runtime/io.cpp#L976-L1011")
  (document environment "POSIX.1-2024, getenv()")]
def ReadsEnvironment (model : Model) : Prop :=
  ∀ name before, (readEnv name before).val = model.environment before name ∧
    (readEnv name before).state = before

/-- An absolute command is the pathname selected for the child, without PATH substitution.
This does not assert that exec succeeds, that the file is uncompromised, or that it stays unchanged. -/
@[regula_assumption process
  (lean "v4.34.1" "Init/System/IO.lean#L1489-L1502")
  (lean "v4.34.1" "runtime/process.cpp#L191-L196")
  (lean "v4.34.1" "runtime/process.cpp#L453-L515")
  (lean "v4.34.1" "runtime/process.cpp#L565-L590")
  (document process "POSIX.1-2024, execvp(): a pathname containing slash is used without PATH search")
  (document process "Microsoft Win32: Naming Files, Paths, and Namespaces, Fully Qualified vs. Relative Paths")
  (trusted "Windows CreateProcess resolves the quoted absolute command with its explicit .exe extension; no Windows runner qualifies it here")]
def StartsAbsolute (model : Model) : Prop :=
  ∀ (args : IO.Process.SpawnArgs) before, (System.FilePath.mk args.cmd).isAbsolute = true →
    nativeProgram args.cmd = true →
    RunsTo id (IO.Process.spawn args before)
      (fun child after => model.target after child.pid args.cmd) (fun _ _ => True)

/-- With inheritEnv true and successful native updates, the configured child environment has
the parent's values with the one env array's changes applied left to right. Lean ignores the
setenv/unsetenv return values, so update success is a separate external condition. Parent stability
and the runtime's child setup remain hypotheses, not kernel facts. -/
@[regula_assumption environment
  (lean "v4.34.1" "Init/System/IO.lean#L1439-L1455")
  (lean "v4.34.1" "runtime/process.cpp#L453-L469")
  (trusted "The parent environment stays stable and every native setenv/unsetenv update succeeds; the runtime ignores their return values. Windows environment construction is unqualified")]
def InheritsEnvironment (model : Model) : Prop :=
  System.Platform.isWindows = false →
  ∀ (args : IO.Process.SpawnArgs) name before, args.inheritEnv = true → nativeChanges args.env = true →
    model.updatesSucceeded before args →
    RunsTo id (IO.Process.spawn args before)
      (fun child after => model.childEnvironment after child.pid name =
        effective (model.environment before name) args.env name) (fun _ _ => True)

/-- The actual toolchain resolution returns an absolute native command on every successful run.
The proof follows the returned token, not a separate model of the path-selection code. Its
installation identity and contents remain the observer's stated trusted boundary. -/
theorem resolution_absolute [Cache] (tool : Tool) (known : Option Installation)
    (before : Void IO.RealWorld) :
    RunsTo id (resolution (.toolchain tool) known before)
      (fun selected _ => (System.FilePath.mk selected.command).isAbsolute = true ∧
        nativeProgram selected.command = true) (fun _ _ => True) := by
  cases ran : resolution (.toolchain tool) known before with
  | error error after => simp only [RunsTo]
  | ok selected after =>
    simp only [RunsTo]
    exact ⟨selected.absolute tool rfl, selected.native⟩

attribute [regula_checked process resolution_absolute
  (lean "v4.34.1" "Init/System/FilePath.lean#L102-L120")
  (trusted "Absolute-path and native-string admission are proved by the returned token; compiler self-report and installation integrity remain trusted")]
  resolution

/-- The actual environment observer's result, conditional on the named runtime hypothesis. -/
theorem readEnv_spec (model : Model) (reads : ReadsEnvironment model) (name : String)
    (before : Void IO.RealWorld) :
    (readEnv name before).val = model.environment before name ∧
      (readEnv name before).state = before := reads name before

/-- Every successful actual toolchain spawn selects an absolute command for the child, under
the runtime's absolute-start hypothesis. The path belongs to an identity-checked installation
by the resolution's proof-bearing construction; child exec success is not asserted. -/
theorem spawn_toolchain (model : Model) (starts : StartsAbsolute model) (tool : Tool)
    (args : IO.Process.SpawnArgs) (before : Void IO.RealWorld) :
    RunsTo id (spawn (.toolchain tool) args before)
      (fun child after => ∃ command : String, (System.FilePath.mk command).isAbsolute = true ∧
        nativeProgram command = true ∧
        model.target after child.pid command) (fun _ _ => True) := by
  unfold spawn
  cases ran : prepare (.toolchain tool) args before with
  | error error after => rw [eio_bind_error ran]; trivial
  | ok prepared after =>
    rw [eio_bind_ok ran]
    have chosen := starts prepared.emit after (prepared.absolute tool) prepared.native
    cases launched : IO.Process.spawn prepared.emit after with
    | error error final => simp only [RunsTo, launched] at chosen ⊢
    | ok child final =>
      simp only [RunsTo, launched, id] at chosen ⊢
      exact ⟨prepared.emit.cmd, prepared.absolute tool, prepared.native, chosen⟩

/-- The emitted array's child environment at the actual native start, under the runtime's
environment hypothesis and successful native updates. This concerns the one array emitted, and makes no claim that a separately
recorded array or a running child's later environment agrees with it. -/
theorem Prepared.environment {program : Program} {args : IO.Process.SpawnArgs}
    (prepared : Prepared program args) (model : Model) (inherits : InheritsEnvironment model)
    (name : String) (before : Void IO.RealWorld) (posix : System.Platform.isWindows = false)
    (inherited : args.inheritEnv = true) (valid : nativeChanges prepared.env = true)
    (updated : model.updatesSucceeded before prepared.emit) :
    RunsTo id (IO.Process.spawn prepared.emit before)
      (fun child after => model.childEnvironment after child.pid name =
        effective (model.environment before name) prepared.env name) (fun _ _ => True) :=
  inherits posix prepared.emit name before inherited valid updated

end Regula.Process
