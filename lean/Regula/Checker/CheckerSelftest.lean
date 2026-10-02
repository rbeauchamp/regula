import Regula.Checker.PolicyCodec
import Regula.Checker.Documentation
import Regula.Checker.Lake
import Regula.Checker.CompilerPaths
import Regula.Checker.PolicyQualification
import Regula.Checker.BuildLintQualification
import Regula.Checker.LintQualification
import Regula.Checker.Inspection

/-!
# Checker qualification suite

Focused qualification suite for the repository's Lean-native checkers.

The suite runs in two tiers that share one invariant prefix instead of
re-paying it per verdict:

* The **default tier** attacks declaration policy with every fixed fixture,
  attacks the Markdown protocol in memory and through the in-process fence
  auditor, attacks strict manifest parsing, and applies every structural and
  compiler-path mutation in parallel isolated projects. Fixture verdicts are computed
  in this process: all fixture sources compile in bounded parallel batches and
  are then inspected by isolated group workers, using
  the same `SourceAudit`/`Environment`/`Frontend`/`Policy` functions the public
  gate uses. A thin real-CLI smoke tier (a handful of fixtures through actual
  `axiomGate --file` spawns) keeps end-to-end evidence for the public
  interface contract.
* The **conditional tier** (`--build-bound`) holds the inherently build-bound
  controls that cannot be sub-second by construction: the full real-CLI
  fixture sweep, the end-to-end fence-corpus run, external adoption of the
  checker package from scratch projects in both lakefile formats, and the
  clean-checkout environment, public-surface, and fresh-plan controls. Its
  trigger is unchanged: checker policy, fixture, or claimed detection-behavior
  changes, plus CI.

With `--build-bound`, the closed partitions are `fixtures` (in-process fixtures,
scanner, and fence corpus), `structural` (structural and manifest controls),
`execution` (the compiler-path mutations and the correspondence controls), `cli` (the
complete CLI sweep), `environments` (packaging and fresh-state controls), `build-policy`
(ordinary-build enforcement), and `lint-driver` (`lake lint` dispatch and exit classes).
Each starts with the baseline build of what its own controls read from the repository's build
(`Partition.baseline`).
Their disjoint union is the full run; no partition alone reports full qualification.

The structural and correspondence clusters run in the structural project
(`StructuralProject`): the repository's package restricted to the application, so a gate there
builds and inspects the application alone. The one control that needs the checker's own
package as the audited project runs in copies of the repository (`structuralSelfHosted`,
`structuralSelfHostedPositive`).

The controls of the structural and of the execution partition each carry one of two shards
(`Shard`); `--shard` runs the controls of one, and the two together run every control once
(`inShard_cover`).

It is intentionally qualification-only, not an ordinary build.
-/

namespace Regula.Checker.CheckerSelftest

open Lean System
open Regula.Checker
open Regula.Checker.Documentation
open Regula.Checker.Policy

/-- The verdict a fixture declares in `fixtures.json` (`expect`). -/
inductive Expectation where
  /-- The checker must accept the fixture. -/
  | pass
  /-- The checker must reject the fixture, for the declared reasons. -/
  | fail
  deriving Repr, BEq

/-- One entry of `Fixtures/fixtures.json`, resolved to its Lake fixture module. -/
structure FixtureSpec where
  /-- The fixture's module name, the entry's key. -/
  moduleName : String
  /-- The fixture's source file, as Lake resolves it in the `Fixtures` library. -/
  source : FilePath
  /-- Whether the checker must accept or reject the fixture. -/
  expectation : Expectation
  /-- For a rejection, the exact set of `VIOLATION[...]` and `INCOMPLETE[...]` reasons expected,
  `#["compile-error"]` for a fixture that must fail to compile, or `#["audit-incomplete"]` for one
  whose audit must stop without a verdict. -/
  reasons : Array String := #[]
  /-- The foundation profile passed as `--claim`, when the entry sets one. -/
  claim : Option Profile := none
  /-- The execution mode passed as `--execution`, when the entry sets one. -/
  execution : Option String := none
  /-- For an accepted fixture, a foundation label some declaration must be reported with. -/
  label : Option String := none
  /-- For a compile-error or audit-incomplete fixture, the pattern its output must match (default
  `error`). -/
  pattern : Option String := none
  /-- Texts the checker output must contain, whatever the verdict. -/
  output : Array String := #[]
  deriving Repr

/-- Disjoint groups whose union is the complete build-bound qualification. -/
inductive Partition where
  /-- In-process fixture verdicts, the Markdown scanner and the fence corpus. -/
  | fixtures
  /-- Structural and manifest controls. -/
  | structural
  /-- Execution-evidence controls: the compiler-path mutations and the correspondence
  controls, each with its positive and fresh restoration. -/
  | execution
  /-- Every fixture through a real `axiomGate --file` invocation, and the source-attribution
  controls. -/
  | cli
  /-- The end-to-end fence corpus and the external-adopter and clean-checkout controls. -/
  | environments
  /-- Ordinary-build enforcement controls (`build-policy`). -/
  | buildPolicy
  /-- `lake lint` dispatch and exit-class controls (`lint-driver`). -/
  | lintDriver
  deriving Repr, BEq, DecidableEq

private def Partition.label : Partition → String
  | .fixtures => "fixtures"
  | .structural => "structural"
  | .execution => "execution"
  | .cli => "cli"
  | .environments => "environments"
  | .buildPolicy => "build-policy"
  | .lintDriver => "lint-driver"

/-- The full run enumerates each supported partition exactly once. -/
private def Partition.all : List Partition :=
    [.fixtures, .structural, .execution, .cli, .environments, .buildPolicy, .lintDriver]

private theorem Partition.all_complete (partition : Partition) : partition ∈ all := by
  cases partition <;> simp [all]

private theorem Partition.all_nodup : all.Nodup := by decide

/-- The checker executables the self-test's controls run from the repository's build. -/
private def checkerTools : List String := ["axiomGate", "lint", "docFenceAudit", "freshChecker"]

/-- What the controls of a partition read from the repository's own build output, which the
baseline build therefore completes before they start. -/
private structure Baseline where
  /-- The checker executables the controls run from the repository's build directory. -/
  tools : List String
  /-- Whether the controls also read the fixture import anchor, the fixture modules other fixtures
  import (`importedFixtures`), and the claimed positive surface there (fixture sources import the
  owned library, e.g. `import AuditApp`). -/
  surface : Bool

/-- Each partition's baseline. The structural and execution controls run their gates in
projects of their own (the structural project, a copy of the repository, a scratch project),
where the gate builds and inspects that project's targets itself; the manifest controls run
`axiomGate` on the repository with a manifest it refuses before any build. So from the
repository's build they read only the executables they run: `axiomGate` in both partitions, and
in the structural clusters `docFenceAudit` and `freshChecker`. The other partitions keep the
complete baseline. -/
private def Partition.baseline : Partition → Baseline
  | .structural => ⟨["axiomGate", "docFenceAudit", "freshChecker"], false⟩
  | .execution => ⟨["axiomGate"], false⟩
  | .fixtures | .cli | .environments | .buildPolicy | .lintDriver => ⟨checkerTools, true⟩

/-- Every partition's baseline build names `axiomGate`: the executable that controls of every
partition run, some by its path in the repository's build instead of through `toolPath`
(`CompilerPaths`, `PolicyQualification`), and that the cold-start driver builds together with the
self-test (`RegulaVerification.commands`). -/
private theorem Partition.baseline_axiomGate (partition : Partition) :
    "axiomGate" ∈ partition.baseline.tools := by
  cases partition <;> simp [baseline, checkerTools]

/-- One of the two shards the controls of the structural and of the execution partition are
divided into, so that each shard runs under the deadline of its own invocation. -/
inductive Shard where
  /-- `1/2`. -/
  | first
  /-- `2/2`. -/
  | second
  deriving DecidableEq, Repr

private def Shard.label : Shard → String
  | .first => "1/2"
  | .second => "2/2"

/-- The controls a run executes: all of `items`, or those assigned to the selected shard. Each
item carries its one shard. -/
private def inShard {α : Type} (shard : Option Shard) (items : List (Shard × α)) :
    List (Shard × α) :=
  match shard with
  | none => items
  | some selected => items.filter (·.1 == selected)

/-- The two shards of a list of controls are together a rearrangement of the list: every control
runs in exactly one shard, and the two shards together run what an unsharded run does. This is a
statement about the selection. That the two shards select from the same list rests on their
running the same sources, which it does not state. -/
private theorem inShard_cover {α : Type} (items : List (Shard × α)) :
    (inShard (some .first) items ++ inShard (some .second) items).Perm (inShard none items) := by
  have second : (fun item : Shard × α => item.1 == Shard.second) =
      fun item => !(item.1 == Shard.first) := by
    funext item
    obtain ⟨shard, _⟩ := item
    cases shard <;> rfl
  simp only [inShard, second]
  exact List.filter_append_perm _ _

/-- The baseline of a run of `partition`, of one of its shards when `shard` selects one. The
second structural shard holds no cluster that runs `docFenceAudit`. -/
private def baselineOf (partition : Partition) (shard : Option Shard) : Baseline :=
  match partition, shard with
  | .structural, some .second => ⟨["axiomGate", "freshChecker"], false⟩
  | _, _ => partition.baseline

/-- Every run's baseline build names `axiomGate` (`Partition.baseline_axiomGate`), a shard's
too. -/
private theorem baselineOf_axiomGate (partition : Partition) (shard : Option Shard) :
    "axiomGate" ∈ (baselineOf partition shard).tools := by
  unfold baselineOf
  split
  · simp
  · exact partition.baseline_axiomGate

/-- The checker executables `baselines` name, each once. -/
private def baselineTools (baselines : List Baseline) : List String :=
  (baselines.flatMap (·.tools)).eraseDups

/-- The parsed `checkerSelftest` command-line options. -/
structure Options where
  /-- `--jobs N`: the number of parallel workers; must be positive. -/
  jobs : Nat := 4
  /-- `--structural-only`: run only the structural and execution controls after the baseline
  build. -/
  structuralOnly : Bool := false
  /-- `--build-bound`: also run the conditional, build-bound tier. -/
  buildBound : Bool := false
  /-- `--partition NAME`: run only this build-bound group; requires `--build-bound`. -/
  partition : Option Partition := none
  /-- `--shard 1/2` or `--shard 2/2`: run only that shard of the selected structural or
  execution partition. -/
  shard : Option Shard := none
  /-- `--help` or `-h`: print the usage and exit. -/
  help : Bool := false

private def usage : String :=
  "usage: lake exe checkerSelftest -- [--jobs N] [--structural-only] [--build-bound [--partition \
    fixtures|structural|execution|cli|environments|build-policy|lint-driver \
    [--shard 1/2|2/2]]]\n" ++
  "--fences-only: focused in-process and public fence qualification, without the full suite\n" ++
  "default tier: every planted-defect verdict in one process plus a real-CLI smoke tier\n" ++
  "--build-bound: additionally run the conditional tier (real-CLI sweep, end-to-end\n" ++
  "fence corpus, external adopters, clean-checkout environment, public controls)\n" ++
  "--partition: run only the named build-bound group; all seven groups are required for full \
    qualification\n" ++
  "--shard: run only that half of the structural or execution group; both halves are required \
    for the group"

private def parseArgs : List String → Options → IO Options
  | [], options => do
      if options.partition.isSome && !options.buildBound then
        throw <| IO.userError "--partition requires --build-bound"
      if options.shard.isSome && !(options.partition == some .structural ||
          options.partition == some .execution) then
        throw <| IO.userError "--shard requires --partition structural or --partition execution"
      if options.structuralOnly && (options.buildBound || options.partition.isSome) then
        throw <| IO.userError "--structural-only conflicts with --build-bound and --partition"
      return options
  | "--" :: rest, options => parseArgs rest options
  | "--jobs" :: value :: rest, options => do
      let jobs ← parseNatArg "--jobs" value
      parseArgs rest { options with jobs }
  | "--structural-only" :: rest, options => do
      if options.structuralOnly then throw <| IO.userError "duplicate --structural-only"
      parseArgs rest { options with structuralOnly := true }
  | "--build-bound" :: rest, options => do
      if options.buildBound then throw <| IO.userError "duplicate --build-bound"
      parseArgs rest { options with buildBound := true }
  | "--partition" :: value :: rest, options => do
      if options.partition.isSome then throw <| IO.userError "duplicate --partition"
      let partition ← match value with
        | "fixtures" => pure Partition.fixtures
        | "structural" => pure Partition.structural
        | "execution" => pure Partition.execution
        | "cli" => pure Partition.cli
        | "environments" => pure Partition.environments
        | "build-policy" => pure Partition.buildPolicy
        | "lint-driver" => pure Partition.lintDriver
        | _ => throw <| IO.userError s!"unknown partition: {value}"
      parseArgs rest { options with partition := some partition }
  | "--shard" :: value :: rest, options => do
      if options.shard.isSome then throw <| IO.userError "duplicate --shard"
      let shard ← match value with
        | "1/2" => pure Shard.first
        | "2/2" => pure Shard.second
        | _ => throw <| IO.userError s!"unknown shard: {value}"
      parseArgs rest { options with shard := some shard }
  | "--help" :: rest, options | "-h" :: rest, options =>
      parseArgs rest { options with help := true }
  | flag :: _, _ => throw <| IO.userError s!"unknown or incomplete argument: {flag}"

private def requiredString (value : Json) (key where_ : String) : IO String := do
  let field ← IO.ofExcept <| value.getObjVal? key
  match field with
  | .str text => return text
  | _ => throw <| IO.userError s!"{where_}.{key} must be a string"

private def optionalString (value : Json) (key where_ : String) : IO (Option String) :=
  match value.getObjVal? key with
  | .error _ => return none
  | .ok (.str text) => return some text
  | .ok _ => throw <| IO.userError s!"{where_}.{key} must be a string"

/-- The library the structural project claims: the complete-application dogfooding surface. -/
private def structuralApplication : String := "AuditApp"

/-- The module of an excluded library that the structural project starts with: the
contamination controls import it into the claimed library. -/
private def structuralFixture : Name := `Fixtures.Mutations.DirectAxiom

/-- The modules of the `Fixtures` library that a fixture's header imports (`Lean.parseImports'`),
for the baseline build. A fixture compiles against the repository's build, in the in-process
controls and through `axiomGate --file` alike, and no other target the baseline names builds a
fixture module it imports. A header that does not parse contributes none: that fixture's own
compilation then fails and is assessed as such. -/
private def importedFixtures (repo : FilePath) : IO (Array Name) := do
  let inventory ← Lake.surfaceInventory repo
  let some library := inventory.libraries.find? (·.library == "Fixtures")
    | throw <| IO.userError "fixture imports: Lake omitted the Fixtures library"
  let mut imported : Array Name := #[]
  for entry in library.sources do
    let modules ← try
        pure ((← Lean.parseImports' (← IO.FS.readFile entry.source)
          entry.source.toString).imports.map (·.module))
      catch _ => pure #[]
    for name in modules do
      if library.modules.contains name && !imported.contains name then
        imported := imported.push name
  return imported

/-- The structural project: the repository's own package restricted to its application. Its
root targets are the application library, the executables the repository's manifest claims on
it, and the libraries owning the excluded fixture module or a root-package module the
application imports; its sources are the application's modules, those executables' roots, the
fixture module and every root-package module they import, directly or not. The package keeps
the repository's name, source directory and Lean options, and each target the roots, globs,
source directory and Lean options of its own configuration, as Lake reports them, so a kept
library owns in the project exactly its modules whose sources are present, and a target a
control adds inherits the package's options as it would in the repository. The project
requires no package, and the checker probe's own imports outside it resolve to the running
checker's library, so no gate in it builds or inspects a library the application does not
import. -/
private structure StructuralProject where
  /-- The project's `lakefile.lean`. -/
  lakefile : String
  /-- The project's sources, relative to the repository root. -/
  sources : Array FilePath
  /-- The project's root libraries, as the manifest spells them. -/
  libraries : Array String
  /-- The application's claimed executables, as the manifest spells them. -/
  executables : Array String

/-- A configuration's own Lean options, as the `leanOptions` field of a `lakefile.lean`. -/
private def renderOptions (options : Array Lean.LeanOption) : String :=
  let values := options.toList.map fun option =>
    let value := match option.value with
      | .ofString s => s!".ofString {repr s}"
      | .ofBool b => s!".ofBool {b}"
      | .ofNat n => s!".ofNat {n}"
    s!"⟨`{option.name}, {value}⟩"
  s!"#[{", ".intercalate values}]"

/-- The structural project carries Lean options only: a target Lake builds with extra `lean`
arguments is refused, not built without them. -/
private def refuseArguments (target : String)
    (options : RegulaPolicy.Community.BuildOptions) : IO Unit :=
  unless options.arguments.isEmpty do
    throw <| IO.userError s!"self-test: the structural project cannot carry the extra lean \
      arguments of {target}: {options.arguments}"

private def renderGlob : _root_.Lake.Glob → String
  | .one name => s!".one `{name}"
  | .submodules name => s!".submodules `{name}"
  | .andSubmodules name => s!".andSubmodules `{name}"

/-- Derive the structural project from the repository's loaded workspace and parsed manifest.
Module ownership, sources, imports of root-package modules and target configuration are Lake's
own (`Workspace.findModule?`, `Lean.parseImports'`); nothing is a fixed file list. -/
private def structuralProject (manifest : Manifest) (ws : _root_.Lake.Workspace) :
    IO StructuralProject := do
  let pkg := ws.root
  let spelling (name : Name) := Manifest.targetSpelling name
  let some application := pkg.leanLibs.find? (spelling ·.name == structuralApplication)
    | throw <| IO.userError s!"self-test: Lake omitted the {structuralApplication} library"
  let some fixture := ws.findModule? structuralFixture
    | throw <| IO.userError s!"self-test: Lake omitted the module {structuralFixture}"
  let claimed := (manifest.surfaces.filter (·.library == structuralApplication)).flatMap
    (·.executables)
  let executables := pkg.leanExes.filter (claimed.contains <| spelling ·.name)
  unless executables.size == claimed.size do
    throw <| IO.userError
      s!"self-test: Lake omitted a claimed executable of {structuralApplication}"
  let mut pending := (← application.getModuleArray).toList ++ [fixture] ++
    executables.toList.map (·.root)
  let mut modules : Array _root_.Lake.Module := #[]
  repeat
    let next :: rest := pending | break
    pending := rest
    if modules.any (·.name == next.name) then continue
    modules := modules.push next
    let header ← Lean.parseImports' (← IO.FS.readFile next.leanFile) next.leanFile.toString
    for imported in header.imports do
      if let some found := ws.findModule? imported.module then
        if found.pkg.keyName == pkg.keyName then pending := found :: pending
  let libraries := pkg.leanLibs.filter fun library =>
    modules.any (·.lib.name == library.name)
  let base := pkg.dir.normalize.components
  let mut sources : Array FilePath := #[]
  for owned in modules do
    let components := owned.leanFile.normalize.components
    unless base.isPrefixOf components do
      throw <| IO.userError s!"self-test: {owned.leanFile} is outside the repository"
    sources := sources.push (System.mkFilePath (components.drop base.length))
  let mut lakefile := "import Lake\nopen Lake DSL\n\n" ++
    s!"package «{pkg.baseName}» where\n  srcDir := {repr pkg.config.srcDir.toString}\n" ++
    s!"  leanOptions := {renderOptions pkg.config.leanOptions}\n"
  for library in libraries do
    refuseArguments (spelling library.name) (Lake.libraryOptions library)
    lakefile := lakefile ++ s!"\nlean_lib «{library.name}» where\n" ++
      s!"  srcDir := {repr library.config.srcDir.toString}\n" ++
      s!"  roots := #[{", ".intercalate (library.config.roots.toList.map (s!"`{·}"))}]\n" ++
      s!"  globs := #[{", ".intercalate (library.config.globs.toList.map renderGlob)}]\n" ++
      s!"  leanOptions := {renderOptions library.config.leanOptions}\n"
  for executable in executables do
    refuseArguments (spelling executable.name) (Lake.executableOptions executable)
    lakefile := lakefile ++ s!"\nlean_exe «{executable.name}» where\n" ++
      s!"  root := `{executable.root.name}\n" ++
      s!"  supportInterpreter := {executable.supportInterpreter}\n" ++
      s!"  leanOptions := {renderOptions executable.config.leanOptions}\n"
  return {
    lakefile, sources
    libraries := libraries.map (spelling ·.name)
    executables := executables.map (spelling ·.name) }

/-- Immutable Lake-derived coordinates, acquired before fixture imports can
register additional environment extensions. Scratch controls reanchor the
relative directory without loading cold Lake configurations in this process. -/
private structure SourceLayout where
  relativeDir : FilePath
  /-- The structural project derived from the repository (`structuralProject`). -/
  project : StructuralProject

private def loadSourceLayout (repo : FilePath) : IO SourceLayout := do
  let manifestPath := Manifest.defaultPath repo
  let manifest ← IO.ofExcept <|
    Manifest.parse manifestPath.toString (← IO.FS.readFile manifestPath)
  Workspace.withRootWorkspace repo fun ws => do
    let relativeDir := ws.root.config.srcDir.normalize
    if relativeDir.isAbsolute || relativeDir.components.contains ".." then
      throw <| IO.userError
        "self-test: package source directory must stay inside the copied repository"
    return { relativeDir, project := ← structuralProject manifest ws }

private def loadFixtureManifest (layout : SourceLayout) (repo : FilePath) : IO
    (Array FixtureSpec) := do
  let path := (repo / layout.relativeDir) / "Fixtures" / "fixtures.json"
  let inventory ← Lake.surfaceInventory repo
  let some library := inventory.libraries.find? (·.library == "Fixtures")
    | throw <| IO.userError "fixture manifest: Lake omitted the Fixtures library"
  let value ← readJson path
  let object ← IO.ofExcept value.getObj?
  let allowed :=
      #["expect", "reason", "reasons", "claim", "execution", "label", "pattern", "output"]
  let mut fixtures : Array FixtureSpec := #[]
  for moduleName in object.keysArray.qsort (· < ·) do
    let some source := library.sources.find? (·.«module» == moduleName.toName)
      | throw <| IO.userError s!"{moduleName}: manifest entry has no Lake fixture module"
    let spec ← IO.ofExcept <| value.getObjVal? moduleName
    let specObject ← IO.ofExcept spec.getObj?
    let unknown := specObject.keysArray.filter fun key => !allowed.contains key
    if !unknown.isEmpty then
      throw <|
          IO.userError s!"{moduleName}: fixture manifest has unknown keys {repr unknown.toList}"
    let expectation ← match ← requiredString spec "expect" moduleName with
      | "pass" => pure Expectation.pass
      | "fail" => pure Expectation.fail
      | _ => throw <| IO.userError s!"{moduleName}: expect must be pass or fail"
    let reason ← optionalString spec "reason" moduleName
    let reasons ← match spec.getObjVal? "reasons" with
      | .error _ => pure #[]
      | .ok value => jsonStringArray s!"{moduleName}.reasons" value
    if reason.isSome && !reasons.isEmpty then
      throw <| IO.userError s!"{moduleName}: use exactly one of reason or reasons"
    let reasons := match reason with
      | some text => #[text]
      | none => reasons
    let claim ← match ← optionalString spec "claim" moduleName with
      | none => pure none
      | some text => match Profile.parse? text with
        | some claim => pure (some claim)
        | none => throw <| IO.userError s!"{moduleName}: unknown claim {text}"
    let execution ← optionalString spec "execution" moduleName
    if let some mode := execution then
      if (ExecutionClaim.parse? mode).isNone then
        throw <| IO.userError s!"{moduleName}: unknown execution mode {mode}"
    let label ← optionalString spec "label" moduleName
    let pattern ← optionalString spec "pattern" moduleName
    let output ← match spec.getObjVal? "output" with
      | .error _ => pure #[]
      | .ok value => jsonStringArray s!"{moduleName}.output" value
    fixtures := fixtures.push {
      moduleName, source := source.source, expectation, reasons, claim, execution, label,
          pattern, output }
  if library.modules.size != fixtures.size then
    throw <| IO.userError <|
      s!"fixture manifest/Lake module count mismatch: {fixtures.size}/{library.modules.size}"
  return fixtures

private def uniqueSorted (values : Array String) : Array String :=
  values.foldl (fun found value => if found.contains value then found else found.push value) #[]
    |>.qsort (· < ·)

/-- The reasons of every `VIOLATION[...]` and `INCOMPLETE[...]` tag, the latter a kernel-admission
failure's (`Admission.failureTag`). -/
private def violationReasons (output : String) : Array String := Id.run do
  let mut reasons : Array String := #[]
  for line in output.splitOn "\n" do
    for tag in #["VIOLATION[", "INCOMPLETE["] do
      match line.splitOn tag with
      | _ :: suffix :: _ =>
          if let some reason := (suffix.splitOn "]").head? then reasons := reasons.push reason
      | _ => pure ()
  uniqueSorted reasons

/-- The checker executables this run's baseline build completed; `none` before it, as in the
focused `--…-only` controls, which build what they run themselves. -/
initialize builtTools : IO.Ref (Option (List String)) ← IO.mkRef none

/-- The path of the checker executable `name` in the build of `repo`. After the baseline build,
an executable that build did not name is refused: its file could be left from an earlier build
of other sources, and on a clean checkout it is absent. -/
private def toolPath (repo : FilePath) (name : String) : IO FilePath := do
  if let some built ← builtTools.get then
    unless built.contains name do
      throw <| IO.userError s!"self-test: the baseline build of this run names {built}, not \
        {name}; add it to the baseline of the partition that runs it (Partition.baseline)"
  return repo / ".lake" / "build" / "bin" / name

/-- How a fixture's run ended, apart from what it printed. -/
inductive RunEnd where
  /-- The gate accepted: exit 0, or a report with no failure. -/
  | accepted
  /-- The gate ended with a verdict against the fixture: exit 1 or 2, a report with a failure, a
  source that does not compile, or a refusal that is a violation. -/
  | rejected
  /-- The audit stopped without a verdict: exit 3, an inspection that threw, or a refused
  admission. -/
  | incomplete
  deriving Repr, BEq

/-- The run end an `axiomGate` exit code states (`Lint.Observation.exitCode`). -/
def RunEnd.ofExit (code : UInt32) : RunEnd :=
  if code == 0 then .accepted else if code == 3 then .incomplete else .rejected

/-- Whether a rejected fixture is assessed by its `pattern` over the whole output, not by its
violation tags: one that must fail to compile, or one whose audit must stop without a verdict. -/
private def assessedByPattern (fixture : FixtureSpec) : Bool :=
  fixture.reasons == #["compile-error"] || fixture.reasons == #["audit-incomplete"]

/-- Whether a fixture's inspection fails as a whole, so that it is inspected alone: a
kernel-admission failure invalidates an environment before it has a report, and an incomplete
audit stops the report of every module inspected with it. -/
private def inspectedAlone (fixture : FixtureSpec) : Bool :=
  fixture.reasons.contains "kernel-admission" || fixture.reasons.contains "audit-incomplete"

private def runBinary (repo : FilePath) (name : String)
    (args : Array String) : IO ProcessResult := do
  runProcess repo (← toolPath repo name).toString args

private def runBinaryFrom (binaryRepo cwd : FilePath) (name : String)
    (args : Array String) : IO ProcessResult := do
  runProcess cwd (← toolPath binaryRepo name).toString args

/-- Exact verdict assessment for one fixture against gate (or gate-equivalent)
output. The same function assesses real CLI output and the in-process batch
verdicts, so both paths assert identical intended reasons. -/
private def assessFixtureOutput (fixture : FixtureSpec) (ended : RunEnd)
    (output : String) : Option String := Id.run do
  if let some missing := fixture.output.find? fun needle => !output.contains needle then
    return some s!"{fixture.moduleName}: missing expected output {repr missing}:\n{output}"
  match fixture.expectation with
  | .pass =>
      if ended != .accepted then
        return some s!"{fixture.moduleName}: expected PASS:\n{output}"
      if let some label := fixture.label then
        if !output.contains s!"-> {label}" then
          return some s!"{fixture.moduleName}: no declaration had expected label {label}:\n{output}"
      return none
  | .fail =>
      if ended == .accepted then
        return some s!"{fixture.moduleName}: expected failure, checker passed"
      -- An incomplete audit is its own outcome: no verdict, so no violation, and exit 3. A
      -- rejection whose text happens to match the pattern does not satisfy it.
      if fixture.reasons == #["audit-incomplete"] then
        if ended != .incomplete then
          return some
            s!"{fixture.moduleName}: expected an incomplete audit, got a verdict:\n{output}"
        if (output.splitOn "VIOLATION[").length > 1 then
          return some
            s!"{fixture.moduleName}: an incomplete audit reported a violation:\n{output}"
      if assessedByPattern fixture then
        let pattern := fixture.pattern.getD "error"
        if !Documentation.matchesPattern pattern.toLower output.toLower then
          return some
              s!"{fixture.moduleName}: failure missed pattern {repr pattern}:\n{output}"
        return none
      let actual := violationReasons output
      let expected := uniqueSorted fixture.reasons
      if actual != expected then
        return some <| s!"{fixture.moduleName}: intended exact reason set " ++
          s!"{repr expected.toList}, got {repr actual.toList}:\n{output}"
      return none

/-- Real-CLI fixture control: one actual `axiomGate --file --verbose` invocation, which prints
every classified declaration with its label. -/
private def checkFixtureCli (repo : FilePath) (fixture : FixtureSpec) : IO (Option String) := do
  let args := #["--file", fixture.source.toString, "--verbose"] ++ match fixture.claim with
    | some claim => #["--claim", claim.toString]
    | none => #[]
  let args := args ++ match fixture.execution with
    | some mode => #["--execution", mode]
    | none => #[]
  let result ← runBinary repo "axiomGate" args
  return assessFixtureOutput fixture (.ofExit result.exitCode) result.output

private structure CompiledFixture where
  index : Nat
  fixture : FixtureSpec
  compilation : SourceAudit.Compilation
  constantNames : Array String
  importNames : Array Name
  wantsTranscript : Bool

private def disjointNames (left right : Array String) : Bool :=
  left.all fun name => !right.contains name

/-- Render the exact per-declaration and execution-coverage lines the public
`axiomGate --file --verbose` audit prints for one elaborated fixture, using the same
`Policy` functions, so the shared assessment sees an equivalent report. -/
private def renderFileAudit (fixture : FixtureSpec) (_moduleName : String)
    (declarations : Array Regula.Report.Declaration)
    (roots : Array Regula.Report.ExecutionRoot)
    (transcripts : Array Frontend.Transcript) : String × Bool := Id.run do
  let .ok scope := Policy.admitScope declarations transcripts
    | return ("invalid policy observation inventory", false)
  let execution := match fixture.execution with
    | some mode => (ExecutionClaim.parse? mode).getD .report
    | none => .report
  let mut lines : Array String := #[]
  let mut failed := false
  for h : decl in scope.inventory.declarations do
    let rule := Policy.ruleForMember decl fixture.claim scope h
    failed := failed || rule.isSome
    let (verdict, classification) := match rule with
      | none => ("OK", Policy.classifyMember decl scope h)
      | some id => (s!"VIOLATION[{(Regula.descriptor id).applicability}]",
          Policy.subjectDetail decl scope h)
    lines := lines.push s!"[{verdict}] {classification}"
  let .ok executionInventory := Policy.admitExecution roots
    | return ("invalid execution inventory", false)
  let executionViolations := Policy.executionFailures executionInventory execution
  let toolchainBase := Policy.toolchainBase #[(fixture.source.toString, executionInventory)]
  lines := lines ++ Policy.executionAccountLines executionInventory ++
    Policy.toolchainBaseLines toolchainBase true
  for violation in executionViolations do
    let reason := (violation.splitOn ":").head?.getD "execution-unresolved"
    lines := lines.push s!"[VIOLATION[{reason}]] {violation}"
  return ("\n".intercalate lines.toList, !failed && executionViolations.isEmpty)

/-- Batched in-process fixture qualification: every fixture compiles in
bounded parallel batches, fresh-frontend transcripts are re-elaborated by
isolated spawned worker processes (the checker's own pinned frontend, exactly
the process environment the public CLI provides) before one
isolated environment worker per compatible import group (split further whenever
constant names collide), reusing the checker's own `SourceAudit`, `Environment`,
`Frontend`, and `Policy` functions. Compile failures are assessed against the
compiler output, exactly as the public gate's file mode reports them. -/
private unsafe def fixtureVerdicts (repo scratch : FilePath) (jobs : Nat)
    (fixtures : Array FixtureSpec) (leanPath : Array FilePath) : IO (Array (Option String)) := do
  let indexed := fixtures.mapIdx fun index fixture => (index, fixture)
  let compilations ← mapConcurrent jobs indexed fun (index, fixture) => do
    let outcome ← SourceAudit.compile repo scratch {
      «module» := s!"SelftestFixture_{index + 1}"
      source := ← IO.FS.readFile fixture.source
    }
    let compilation ← IO.ofExcept <| outcome.mapError (·.detail)
    return (index, fixture, compilation)
  let mut results : Array (Option String) := Array.replicate fixtures.size none
  let mut pending : Array CompiledFixture := #[]
  for (index, fixture, compilation) in compilations do
    if !SourceAudit.compilationPassed compilation then
      results := results.set! index
        (assessFixtureOutput fixture .rejected compilation.process.output)
    else
      let (moduleData, _) ← Lean.readModuleData compilation.oleanPath
      pending := pending.push {
        index, fixture, compilation
        constantNames := moduleData.constNames.map (·.toString)
        importNames := moduleData.imports.map (·.module)
        -- Same transcript predicate as the post-load check, applied to the
        -- raw module constant records with the probe's own kind mapping, so
        -- only fixtures that can need a transcript pay for one. A divergence
        -- (post-load need with no worker transcript) fails closed below.
        wantsTranscript := moduleData.constants.any fun info =>
          Policy.declarationNeedsTranscript (Regula.Probe.kindOf info) info.name
      }
  -- Group by exact constant-name disjointness (the `Documentation.auditTasks`
  -- strategy): one environment load per collision group covers every fixture
  -- whose names do not collide, so the large shared dependency closure is
  -- loaded once. In-process imports run initializers through Lean's global
  -- importing flag, so group loads stay sequential on this thread, exactly as
  -- in `Documentation.auditTasks`.
  let mut groups : Array (Array String × Array CompiledFixture) := #[]
  for item in pending do
    let mut placed := false
    for groupIndex in [:groups.size] do
      let (names, items) := groups[groupIndex]!
      -- Keep the single-fault controls whose inspection fails as a whole isolated from
      -- unrelated fixtures.
      if !inspectedAlone item.fixture && !(items.any (inspectedAlone ·.fixture)) &&
          (items.all fun other => other.importNames == item.importNames) &&
          disjointNames item.constantNames names then
        groups := groups.set! groupIndex (names ++ item.constantNames, items.push item)
        placed := true
        break
    if !placed then
      groups := groups.push (item.constantNames, #[item])
  IO.println (s!"fixture compilations complete: {fixtures.size}; " ++
    s!"inspecting {pending.size} elaborated fixture(s) in {groups.size} collision group(s)")
  (← IO.getStdout).flush
  let selfLib ← checkerPackageLibDir
  let oldSearchPath ← Lean.searchPathRef.get
  let scopedPath := scratch :: leanPath.toList ++ selfLib.toList ++ oldSearchPath
  -- Transcript workers run in isolated spawned processes and finish before
  -- the parent loads environments, avoiding simultaneous large imports. Spawning
  -- keeps each transcript byte-identical in provenance to the public CLI's
  -- fresh re-elaboration (a fresh process can never see this harness's
  -- attribute state). Failures are tolerated here (a `sorry` fixture fails
  -- its warning-free transcript by design); consumers below fail closed on a
  -- missing transcript with the same text the CLI path reports.
  let leanPathEnv := SearchPath.toString scopedPath
  let transcriptTask ← IO.asTask (prio := .dedicated) do
    mapConcurrent jobs pending fun item => do
      let moduleName := item.compilation.spec.«module»
      if !item.wantsTranscript then return (moduleName, none)
      try
        let out := scratch / s!"transcript-{item.index + 1}.json"
        let spawned ← runProcess repo
          (repo / ".lake" / "build" / "bin" / "checkerSelftest").toString
          #["--transcript-worker", (Regula.RegistryCodec.nameJson moduleName.toName).compress,
              item.compilation.sourcePath.toString,
            out.toString]
          #[("LEAN_PATH", some leanPathEnv)]
        if !spawned.succeeded then return (moduleName, none)
        match Regula.Checker.PolicyCodec.parse (← IO.FS.readFile out) with
        | .error _ => return (moduleName, none)
        | .ok json =>
          let payload := readWorkerPacket (sourceWorkerRequest "transcript" moduleName.toName
            item.compilation.sourcePath item.compilation.spec.source) json
          match payload >>= fromJson? with
          | .error _ => return (moduleName, none)
          | .ok transcript => return (moduleName, some (transcript : Frontend.Transcript))
      catch _ => return (moduleName, none)
  -- Complete all transcript workers before starting isolated report workers.
  let transcripts ← IO.ofExcept (← IO.wait transcriptTask)
  let mut inspected : Array (CompiledFixture × Array Regula.Report.Declaration ×
      Array Regula.Report.ExecutionRoot) := #[]
  Lean.searchPathRef.set scopedPath
  try
    for (_, items) in groups do
      try
        let outcome ← SourceAudit.inspectGroupCurrentSearchPath
          (items.map (·.compilation.spec.«module».toName))
          (compiledSources := items.map fun item => {
            moduleName := item.compilation.spec.module.toName
            path := item.compilation.sourcePath.toString
            content := item.compilation.spec.source })
        match outcome with
        | .error refusal =>
          -- The refusal keeps its type: a refused admission is incomplete evidence, and owned
          -- build output outside every owned module is a violation.
          let ended : RunEnd := match refusal with
            | .admission _ => .incomplete
            | .unowned _ => .rejected
          for item in items do
            results := results.set! item.index
              (assessFixtureOutput item.fixture ended refusal.detail)
        | .ok inspectedGroup =>
          let report := inspectedGroup.report
          for item in items do
            let moduleName := item.compilation.spec.«module»
            let declarations := report.declarations.filter (·.«module» == moduleName.toName)
              |>.qsort fun left right => Name.quickLt left.name right.name
            let roots := report.execution.filter (·.«module» == moduleName.toName)
            inspected := inspected.push (item, declarations, roots)
      catch error =>
        -- An inspection that throws has no report: the gate reports it as incomplete.
        for item in items do
          results := results.set! item.index
            (assessFixtureOutput item.fixture .incomplete error.toString)
    pure ()
  finally Lean.searchPathRef.set oldSearchPath
  for (item, declarations, roots) in inspected do
    let moduleName := item.compilation.spec.«module»
    if Policy.needsFrontendTranscript declarations then
      match transcripts.find? (·.1 == moduleName) with
      | some (_, some transcript) =>
        let (output, succeeded) := renderFileAudit item.fixture moduleName
          declarations roots #[transcript]
        results := results.set! item.index
          (assessFixtureOutput item.fixture (if succeeded then .accepted else .rejected) output)
      | _ =>
        results := results.set! item.index
          (assessFixtureOutput item.fixture .rejected
            (if item.wantsTranscript then
              s!"fresh frontend elaboration failed for {moduleName}"
            else
              s!"transcript need pre-filter diverged for {moduleName}"))
    else
      let (output, succeeded) := renderFileAudit item.fixture moduleName
        declarations roots #[]
      results := results.set! item.index
        (assessFixtureOutput item.fixture (if succeeded then .accepted else .rejected) output)
  return results

/-- Real-CLI smoke tier: a small diverse set of fixtures through actual
`axiomGate --file` invocations, keeping end-to-end evidence for the public
interface contract in the default tier. -/
private def smokeFixtureNames : Array String :=
  #["Fixtures.Positive.KernelOnly", "Fixtures.Mutations.DirectAxiom",
    "Fixtures.Positive.ExternBoundary", "Fixtures.Positive.DependentCorrespondence",
    "Fixtures.Mutations.ConditionalCorrespondence"]

/-- Counterexample aid, not correctness evidence (standard §0 "The Role of Testing"):
concrete `Documentation.scan` inputs for each marker/fence problem class. A universal
statement of the scanner's problem coverage is not yet proved; until it is, these cases
only search for counterexamples. -/
private def scannerQualification : Array String := Id.run do
  let cases : Array (String × String × String) := #[
    ("positive", "```lean\ntheorem ok : True := trivial\n```\n", ""),
    ("unclosed", "```lean\ntheorem x : True := trivial\n", "never closed"),
    ("empty-pattern", "<!-- lean-fail: -->\n```lean\ndef n : Nat := \"x\"\n```\n",
        "pattern is empty"),
    ("invalid-pattern", "<!-- lean-fail: [ -->\n```lean\ndef n : Nat := \"x\"\n```\n",
        "unsupported"),
    ("malformed-marker", "<!-- lean-fail -->\n```lean\ndef n : Nat := \"x\"\n```\n", "malformed"),
    ("marker-typo", "<!--lean-fail: Type mismatch-->\n```lean\ntheorem t : 1 = 1 := rfl\n```\n",
        "malformed"),
    ("marker-truncated", "<!-- lean-trusted -->\n```lean\ntheorem t : 1 = 1 := rfl\n```\n",
        "malformed"),
    ("duplicate-marker", "<!-- lean-fail: Type mismatch -->\n<!-- lean-trusted-compiler \
      -->\n```lean\ndef n : Nat := \"x\"\n```\n", "multiple markers"),
    ("blank-separation",
        "<!-- lean-fail: Type mismatch -->\n\n```lean\ndef n : Nat := \"x\"\n```\n",
            "not immediately adjacent"),
    ("prose-orphan",
        "<!-- lean-fail: Type mismatch -->\nprose\n```lean\ndef n : Nat := \"x\"\n```\n",
            "not immediately adjacent"),
    ("nonlean-target", "<!-- lean-fail: Type mismatch -->\n```text\ndef n : Nat := \"x\"\n```\n",
        "not attached"),
    ("eof-marker", "<!-- lean-fail: Type mismatch -->", "left at end")
  ]
  let mut failures : Array String := #[]
  for (name, text, expectedProblem) in cases do
    let result := Documentation.scan text name
    if expectedProblem.isEmpty then
      if result.fences.size != 1 || !result.problems.isEmpty then
        failures := failures.push s!"scanner/{name}: expected one clean fence"
    else if !result.problems.any (·.contains expectedProblem) then
      failures :=
          failures.push s!"scanner/{name}: missing problem containing {repr expectedProblem}"
  if !Documentation.matchesPattern "(?s)failed.*law|Fields missing"
      "prefix failed\nfor a law suffix" then
    failures := failures.push "scanner/pattern: ordered/alternative matching failed"
  failures

/-- A committed LRAT certificate for `(x &&& y) + (x ||| y) = x + y` over `BitVec 2`, which
`bv_check` reads by absolute path because a fence compiles in a scratch directory. -/
private def bvCheckCertificate (repo : FilePath) : FilePath :=
  repo / "lean" / "Fixtures" / "BvCheck.lrat"

/-- The adversarial fence corpus shared by the in-process default-tier audit
and the end-to-end public `docFenceAudit` control in the conditional tier. -/
private def fenceCorpusCases (repo : FilePath) : Array (String × String × String) := #[
  ("unclosed", "```lean\ntheorem x : True := trivial\n", "never closed"),
  ("empty-pattern", "<!-- lean-fail: -->\n```lean\ndef n : Nat := \"x\"\n```\n",
      "pattern is empty"),
  ("invalid-pattern", "<!-- lean-fail: [ -->\n```lean\ndef n : Nat := \"x\"\n```\n", "unsupported"),
  ("malformed-marker", "<!-- lean-fail -->\n```lean\ndef n : Nat := \"x\"\n```\n",
      "malformed Lean fence marker"),
  ("duplicate-marker", "<!-- lean-fail: Type mismatch -->\n<!-- lean-trusted-compiler \
    -->\n```lean\ndef n : Nat := \"x\"\n```\n", "multiple markers target one fence"),
  ("blank-separation", "<!-- lean-fail: Type mismatch -->\n\n```lean\ndef n : Nat := \"x\"\n```\n",
      "not immediately adjacent"),
  ("prose-orphan", "<!-- lean-fail: Type mismatch -->\nprose\n```lean\ndef n : Nat := \"x\"\n```\n",
      "not immediately adjacent"),
  ("nonlean-target", "<!-- lean-fail: Type mismatch -->\n```text\ndef n : Nat := \"x\"\n```\n",
      "not attached to a ```lean fence"),
  ("eof-marker", "<!-- lean-fail: Type mismatch -->", "left at end of file"),
  ("positive", "```lean\ntheorem nested_ok : 1 = 1 := rfl\n```\n", "positive.md:1 PASS"),
  ("raw-import", "```lean\ntheorem missing_import : Glossary.Time = Glossary.Time := rfl\n```\n",
      "did not elaborate verbatim"),
  ("warning", "```lean\nset_option warningAsError false in\ndef hidden_warning (unused : Nat) : \
    Nat := 1\n```\n", "emitted warning"),
  ("hole", "```lean\ntheorem docs_hole : False := by sorry\n```\n", "hole.md:1 FAIL"),
  ("project-axiom", "```lean\naxiom docs_axiom : False\n```\n", "project-axiom"),
  ("valid-negative", "<!-- lean-fail: Type mismatch -->\n```lean\ndef n : Nat := \"x\"\n```\n",
      "valid-negative.md:2 PASS_NEG"),
  ("negative-info-only", "<!-- lean-fail: expectedOnlyInfo -->\n```lean\n#eval IO.println \
    \"expectedOnlyInfo\"\n#check missingActualError\n```\n", "negative-info-only.md:2 FAIL"),
  ("negative-cross-errors", "<!-- lean-fail: missingFirst.*missingSecond -->\n```lean\n#check \
    missingFirst\n#check missingSecond\n```\n", "negative-cross-errors.md:2 FAIL"),
  ("negative-multiline",
      "<!-- lean-fail: Type mismatch.*String.*Nat -->\n```lean\ndef n : Nat := \"x\"\n```\n",
          "negative-multiline.md:2 PASS_NEG"),
  ("negative-import",
      "<!-- lean-fail: unknown module prefix -->\n```lean\nimport MissingDiagnosticModule\n```\n",
          "negative-import.md:2 PASS_NEG"),
  ("negative-promoted-warning", "<!-- lean-fail: promotedWarning -->\n```lean\nimport \
    Lean\nset_option warningAsError true in\nrun_cmd Lean.logWarning \"promotedWarning\"\n```\n",
        "negative-promoted-warning.md:2 PASS_NEG"),
  ("negative-header-syntax", "<!-- lean-fail: unexpected -->\n```lean\nimport (\n```\n",
      "negative-header-syntax.md:2 PASS_NEG"),
  ("negative-abnormal", "<!-- lean-fail: deliberate -->\n```lean\nimport Lean\nrun_cmd do\n  let \
    child ← IO.Process.spawn { cmd := \"echo\", args := #[\"error: deliberate\"] }\n  discard \
    child.wait\n  Lean.logError \"deliberate\"\nrun_cmd (IO.Process.exit 7 : IO Unit)\n```\n",
        "diagnostic worker did not complete"),
  ("trusted-native", "<!-- lean-trusted-compiler -->\n```lean\nimport Init\ntheorem docs_native : \
    Nat.gcd 1071 462 = 21 := by native_decide\n```\n", "trusted-native.md:2 PASS_TRUSTED"),
  ("trusted-spoof", "<!-- lean-trusted-compiler -->\n```lean\naxiom \
    Attack._native.native_decide.ax_1 : False\n```\n", "trusted-spoof.md:2 FAIL"),
  -- `decide +native` and `bv_decide` add their axioms through the same `nativeEqTrue`, named
  -- after their own tactic: authenticated teaching passes, a positive fence reports the
  -- compiler-trusting rule (not a project or unknown axiom), and a spoofed name still fails.
  ("trusted-decide-native", "<!-- lean-trusted-compiler -->\n```lean\nimport Init\ntheorem \
    docs_decide_native : Nat.gcd 1071 462 = 21 := by decide +native\n```\n",
      "trusted-decide-native.md:2 PASS_TRUSTED"),
  ("trusted-bv-decide", "<!-- lean-trusted-compiler -->\n```lean\nimport Std.Tactic.BVDecide\n\
    theorem docs_bv_decide (x y : BitVec 8) : x * y = y * x := by bv_decide\n```\n",
      "trusted-bv-decide.md:2 PASS_TRUSTED"),
  ("positive-decide-native", "```lean\nimport Init\ntheorem docs_positive_decide_native : \
    Nat.gcd 1071 462 = 21 := by decide +native\n```\n",
      "compiler-trusting: docs_positive_decide_native"),
  ("positive-bv-decide", "```lean\nimport Std.Tactic.BVDecide\ntheorem docs_positive_bv_decide \
    (x y : BitVec 8) : x * y = y * x := by bv_decide\n```\n",
      "compiler-trusting: docs_positive_bv_decide"),
  ("trusted-tactic-spoof", "<!-- lean-trusted-compiler -->\n```lean\naxiom \
    Attack._native.decide.ax_1 : False\naxiom Attack._native.bv_decide.ax_1 : False\n```\n",
      "trusted-tactic-spoof.md:2 FAIL"),
  -- A public theorem of a `module` file elaborates its proof without exporting, so its generated
  -- names are private to the module; each native tactic is still authenticated.
  ("trusted-module-native", "<!-- lean-trusted-compiler -->\n```lean\nmodule\nimport \
    Std.Tactic.BVDecide\nmeta import Std.Tactic.BVDecide.Reflect\npublic theorem \
    docs_module_native_decide : (2 : Nat) = 2 := by native_decide\npublic theorem \
    docs_module_decide_native : Nat.gcd 1071 462 = 21 := by decide +native\npublic theorem \
    docs_module_bv_decide (x y : BitVec 8) : x * y = y * x := by bv_decide\n```\n",
      "trusted-module-native.md:2 PASS_TRUSTED"),
  -- `bv_decide?` and `bv_check` reach the same `nativeEqTrue` call through their own evaluators.
  ("trusted-bv-trace", "<!-- lean-trusted-compiler -->\n```lean\nimport Std.Tactic.BVDecide\n\
    theorem docs_bv_trace (x y : BitVec 2) : (x &&& y) + (x ||| y) = x + y := by bv_decide?\n\
    ```\n", "trusted-bv-trace.md:2 PASS_TRUSTED"),
  ("trusted-bv-check", s!"<!-- lean-trusted-compiler -->\n```lean\nimport Std.Tactic.BVDecide\n\
    theorem docs_bv_check (x y : BitVec 2) : (x &&& y) + (x ||| y) = x + y := by\n  bv_check \
    -binaryProofs \"{bvCheckCertificate repo}\"\n```\n", "trusted-bv-check.md:2 PASS_TRUSTED"),
  -- Authentication does not depend on the surrounding syntax: `grind =>` and `sym =>` blocks,
  -- namespaced names, attributes, `set_option … in` and reverted parameters are all covered.
  ("trusted-grind-native", s!"<!-- lean-trusted-compiler -->\n```lean\nimport \
    Std.Tactic.BVDecide\ntheorem docs_grind_bv_decide (x y : BitVec 2) : (x &&& y) + (x ||| y) = \
    x + y := by grind => bv_decide\ntheorem docs_sym_bv_trace (x y : BitVec 2) : (x &&& y) + \
    (x ||| y) = x + y := by sym => bv_decide?\ntheorem docs_grind_bv_check (x y : BitVec 2) : \
    (x &&& y) + (x ||| y) = x + y := by\n  grind => bv_check -binaryProofs \
    \"{bvCheckCertificate repo}\"\n```\n", "trusted-grind-native.md:2 PASS_TRUSTED"),
  ("trusted-namespaced-native", "<!-- lean-trusted-compiler -->\n```lean\nimport \
    Std.Tactic.BVDecide\ntheorem Docs.namespaced_native_decide : (2 : Nat) = 2 := by \
    native_decide\ntheorem Docs.Grind.namespaced_bv_decide (x y : BitVec 2) : (x &&& y) + \
    (x ||| y) = x + y := by sym => bv_decide\n```\n",
      "trusted-namespaced-native.md:2 PASS_TRUSTED"),
  ("positive-grind-bv-decide", "```lean\nimport Std.Tactic.BVDecide\ntheorem \
    docs_positive_grind_bv_decide (x y : BitVec 2) : (x &&& y) + (x ||| y) = x + y := by \
    grind => bv_decide\n```\n", "compiler-trusting: docs_positive_grind_bv_decide"),
  -- An axiom with a generated name, used only through a theorem named like `grind`'s auxiliary
  -- proof, is still a project axiom.
  ("trusted-grind-spoof", "<!-- lean-trusted-compiler -->\n```lean\naxiom \
    Attack._native.bv_decide.ax_1 : False\ntheorem Attack._proof_1 : False := \
    Attack._native.bv_decide.ax_1\ntheorem Attack : False := Attack._proof_1\n```\n",
      "trusted-grind-spoof.md:2 FAIL"),
  ("trusted-wrapped-native", "<!-- lean-trusted-compiler -->\n```lean\nimport Init\n@[simp] \
    theorem docs_attribute_native : (2 : Nat) = 2 := by native_decide\nset_option maxRecDepth 1000 \
    in\ntheorem docs_option_native : (3 : Nat) = 3 := by native_decide\ntheorem docs_revert_native \
    (x : Fin 4) : x.val < 4 := by decide +native +revert\n```\n",
      "trusted-wrapped-native.md:2 PASS_TRUSTED"),
  -- An authored `axiom` with a native name and a natively true statement stays a project axiom,
  -- whether declared in its own command or with its user through one macro-produced command.
  ("trusted-declared-native", "<!-- lean-trusted-compiler -->\n```lean\naxiom \
    docs_declared._native.native_decide.ax_1 : decide (2 = 2) = true\ntheorem docs_declared : \
    2 = 2 := of_decide_eq_true docs_declared._native.native_decide.ax_1\n```\n",
      "project-axiom: docs_declared._native.native_decide.ax_1"),
  ("trusted-macro-declared-native", "<!-- lean-trusted-compiler -->\n```lean\nimport Lean\nopen \
    Lean in\nmacro \"declared_native\" : command => do\n  let ax := mkIdent \
    `docs_macro._native.native_decide.ax_1\n  let th := mkIdent `docs_macro\n  let a ← `(axiom \
    $ax : decide (2 = 2) = true)\n  let t ← `(theorem $th : 2 = 2 := of_decide_eq_true $ax)\n  \
    return ⟨mkNullNode #[a, t]⟩\ndeclared_native\n```\n",
      "project-axiom: docs_macro._native.native_decide.ax_1"),
  -- The same, with the axiom's attribute failing after the axiom is added and the error dropped:
  -- the `axiom` declaration is read from syntax, so it is still refused.
  ("trusted-guarded-declared-native", "<!-- lean-trusted-compiler -->\n```lean\nimport \
    Lean\nopen Lean in\nmacro \"guarded_native\" : command => do\n  let ax := mkIdent \
    `docs_guarded._native.native_decide.ax_1\n  let th := mkIdent `docs_guarded\n  let a ← \
    `(#guard_msgs (drop error) in @[csimp] axiom $ax : decide (2 = 2) = true)\n  let t ← \
    `(theorem $th : 2 = 2 := of_decide_eq_true $ax)\n  return ⟨mkNullNode #[a, t]⟩\n\
    guarded_native\n```\n",
      "project-axiom: docs_guarded._native.native_decide.ax_1"),
  ("negative-compiles", "<!-- lean-fail: Type mismatch -->\n```lean\ndef n : Nat := 1\n```\n",
      "negative example elaborated successfully"),
  ("negative-other-diagnostic",
      "<!-- lean-fail: Unknown constant -->\n```lean\ndef n : Nat := \"x\"\n```\n",
          "failed, but not with expected diagnostic"),
  ("trusted-without-mechanism",
      "<!-- lean-trusted-compiler -->\n```lean\ntheorem plain : 1 = 1 := rfl\n```\n",
          "trusted marker found no compiler-trusting declaration"),
  -- The pinned renderer prints a named diagnostic as `warning(name):`
  -- (`Lean.mkErrorStringWithPos`); the audit must reject that form too.
  ("named-warning", "```lean\nimport Lean\nopen Lean\nset_option warningAsError false in\nrun_cmd \
    Lean.logNamedWarningAt (← getRef) `lean.selftestNamedWarning m!\"named\"\n```\n",
        "emitted warning")
]

/-- Corpus cases that only the public `docFenceAudit` control can exercise:
they depend on the process environment the public command runs its fence
workers in, which the in-process auditor does not reproduce. -/
private def publicOnlyFenceCases : Array (String × String × String) := #[
  -- Resolvable only through an inherited `LEAN_PATH`: the control injects a
  -- search-path entry holding a compiled module that no Lake workspace owns.
  ("stale-import",
      "```lean\nimport StaleImport\ntheorem stale_ok : staleImportValue = 1 := rfl\n```\n",
          "did not elaborate verbatim")
]

/-- A valid source rejection must not be satisfied by an import setup error.
Use a private package and the real diagnostic-worker/classification path. -/
private unsafe def diagnosticSetupQualification (repo scratch : FilePath) : IO (Array String) := do
  let project := scratch / "diagnostic-project"
  let output := project / ".lake" / "build" / "lib" / "lean"
  let compiled := project / "compiled"
  IO.FS.createDirAll output
  IO.FS.createDirAll compiled
  IO.FS.writeFile (project / "lean-toolchain") (← IO.FS.readFile (repo / "lean-toolchain"))
  IO.FS.writeFile (project / "lakefile.toml") <|
    "name = \"diagnostic_control\"\n[leanOptions]\nautoImplicit = false\n" ++
      "relaxedAutoImplicit = false\nlinter.missingDocs = true\n[[lean_lib]]\nname = \
        \"SetupSentinel\"\n"
  let source := project / "SetupSentinel.lean"
  let artifact := output / "SetupSentinel.olean"
  IO.FS.writeFile source "def setupValue : Nat := 0\n"
  let build := runProcess project "lake" #["env", "lean", "-o", artifact.toString, source.toString]
  let first ← build
  if !first.succeeded then return #[s!"diagnostic setup baseline failed: {first.output}"]
  let check (body pattern : String) := do
    let text := s!"<!-- lean-fail: {pattern} -->\n```lean\n{body}```\n"
    let scan := Documentation.scan text "setup.md"
    let tasks := scan.fences.map fun fence =>
      ({ fence, origin := "setup.md:2", kind := .negative } : Documentation.Task)
    Documentation.auditTasks project compiled 1 tasks #[] #[]
  let body := "import SetupSentinel\ndef invalid : Nat := \"value\"\n"
  let mut failures := #[]
  for phase in #["baseline", "corrupt", "restored"] do
    if phase == "corrupt" then
      IO.FS.writeFile artifact "invalid serialized artifact"
    if phase == "restored" then
      let restored ← build
      if !restored.succeeded then
        failures := failures.push s!"diagnostic setup restoration failed: {restored.output}"
    let results ← check body (if phase == "corrupt" then "SetupSentinel" else "Type mismatch")
    let accepted := results.size == 1 && results.all fun result =>
      if phase == "corrupt" then
        result.status == .fail && result.detail.contains "diagnostic worker did not complete"
      else result.status == .passNegative
    if !accepted then
      failures := failures.push s!"diagnostic setup/{phase}: {repr (results.map (·.detail))}"
  -- A direct source module-mode error remains a legitimate rejection.
  let moduleResults ← check "module\nimport SetupSentinel\n" "cannot import non-"
  if moduleResults.size != 1 || !(moduleResults.all (·.status == .passNegative)) then
    failures := failures.push "diagnostic setup/module-mode: source rejection was not preserved"
  return failures

/-- Associate each expected diagnostic with its own rendered file record.
A different failing case cannot satisfy this case's expected reason. -/
private def fenceOriginOutput (output filename : String) : String := Id.run do
  let mut active := false
  let mut selected : Array String := #[]
  for line in output.splitOn "\n" do
    if line.startsWith "[" then active := line.contains s!" {filename}:"
    if line.isEmpty then active := false
    if active then selected := selected.push line
  return "\n".intercalate selected.toList

/-- The public command prints a success label only with accepted evidence, which
the failing corpus never has. A passing fence there keeps its status mark and is
labelled as observed; failing records keep their expected diagnostic. -/
private def publicExpectation (expected : String) : String :=
  match expected.splitOn " " with
  | [origin, "PASS"] => s!"[.] {origin} OBSERVED (audit incomplete)"
  | [origin, "PASS_NEG"] => s!"[n] {origin} OBSERVED (audit incomplete)"
  | [origin, "PASS_TRUSTED"] => s!"[t] {origin} OBSERVED (audit incomplete)"
  | _ => expected

/-- In-process fence-corpus qualification: the same corpus the public
`docFenceAudit` control audits end-to-end, scanned and assessed through the
checker's own `Documentation.auditTasks` batch auditor without the
clean-checkout rebuild. -/
private unsafe def fenceCorpusQualification (repo scratch : FilePath) (jobs : Nat)
    : IO (Array String) := do
  let mut tasks : Array Documentation.Task := #[]
  let mut structural : Array String := #[]
  for (name, text, _) in fenceCorpusCases repo do
    let scan := Documentation.scan text s!"{name}.md"
    structural := structural ++ scan.problems
    for fence in scan.fences do
      tasks := tasks.push {
        fence
        origin := s!"{name}.md:{fence.line}"
        kind := kindOf fence
      }
  let results ← Documentation.auditTasks repo scratch jobs tasks #[] #[]
  let mut rendered : Array String := structural.map (s!"[X] {·}")
  for result in results do
    let mark := match result.status with
      | .pass => "." | .passNegative => "n" | .passTrusted => "t" | .fail => "X"
    rendered := rendered.push s!"[{mark}] {result.task.origin} {statusName result.status}"
    if result.status == .fail then
      rendered := rendered.push s!"      {result.detail}"
  let output := "\n".intercalate rendered.toList
  let mut failures : Array String := #[]
  let mut failCount := 0
  for result in results do
    if result.status == .fail then failCount := failCount + 1
  if structural.isEmpty && failCount == 0 then
    failures := failures.push "scanner/corpus: malformed corpus unexpectedly passed"
  for (name, _, expected) in fenceCorpusCases repo do
    if !(fenceOriginOutput output s!"{name}.md").contains expected then
      failures :=
          failures.push s!"scanner/corpus/{name}: missing diagnostic {repr expected}:\n{output}"
  return failures ++ (← diagnosticSetupQualification repo scratch)

/-- End-to-end public `docFenceAudit` control over the adversarial corpus
(conditional tier: it re-runs the auditor against a clean-checkout copy). -/
private unsafe def publicScannerQualification (repo scratch : FilePath) : IO (Array String) := do
  let cases := fenceCorpusCases repo ++ publicOnlyFenceCases
  let docsRoot := scratch / "docs"
  IO.FS.createDirAll docsRoot
  for (name, text, _) in cases do
    IO.FS.writeFile (docsRoot / s!"{name}.md") text
  -- A compiled module outside every Lake workspace, reachable only through
  -- the inherited `LEAN_PATH` the public command must not pass to its workers.
  let staleDir := scratch / "stale-lean-path"
  IO.FS.createDirAll staleDir
  IO.FS.writeFile (staleDir / "StaleImport.lean") "def staleImportValue : Nat := 1\n"
  let compiled ← runProcess repo "lake" #["env", "lean", "-o",
    (staleDir / "StaleImport.olean").toString, (staleDir / "StaleImport.lean").toString]
  if !compiled.succeeded then
    return #[s!"scanner/public/stale-setup: {compiled.output}"]
  let inheritedLeanPath := (← IO.getEnv "LEAN_PATH").getD ""
  let result ← runProcess repo (← toolPath repo "docFenceAudit").toString
    #["--jobs", "4", "--docs-root", docsRoot.toString]
    #[("LEAN_PATH", some (if inheritedLeanPath.isEmpty then staleDir.toString
      else s!"{staleDir}:{inheritedLeanPath}"))]
  let mut failures : Array String := #[]
  if result.succeeded then
    failures := failures.push "scanner/public: malformed corpus unexpectedly passed"
  -- A malformed marker is reported at its own file and line; it must not abort
  -- the run with a bare, unlocated failure.
  if !result.output.contains
      "[X] empty-pattern.md:1: invalid lean-fail pattern: diagnostic pattern is empty"
      || result.output.contains "FAIL: diagnostic pattern is empty" then
    failures := failures.push s!"scanner/public/located-marker: missing located malformed-marker \
      diagnostic:\n{result.output}"
  for (name, _, expected) in cases do
    if !(fenceOriginOutput result.output s!"{name}.md").contains (publicExpectation expected) then
      failures := failures.push s!"scanner/public/{name}: missing \
        diagnostic {repr (publicExpectation expected)}:\n{result.output}"
  return failures

/-- The manifest file at `path` as the pure `Manifest.parse` reads it. The harness has no Lake
inventory of the project here and only derives control manifests and build targets from the
result; the gate each control runs reads its own manifest for its inventory
(`Manifest.loadFor`). -/
private def parsedManifest (path : FilePath) : IO Manifest := do
  IO.ofExcept <| Manifest.parse path.toString (← IO.FS.readFile path)

private def expectManifestPublicFailure (repo : FilePath) (name : String)
    (path : FilePath) (expected : String) : IO (Option String) := do
  let result ← runBinary repo "axiomGate"
    #["--manifest", path.toString, "--incremental"]
  if result.succeeded then return some s!"manifest/public/{name}: expected failure"
  if result.output.contains expected then return none
  return some s!"manifest/public/{name}: wrong diagnostic:\n{result.output}"

/-- External manifest controls only: the real repository manifest, and the public `axiomGate`
CLI rendering the missing-file, malformed, incomplete, wrong-version, unknown-key and
bad-execution refusal classes and a Lake-inventory refusal. The pure parser is proved for every
input instead of sampled in process: `Manifest.parse_sound` and `Manifest.parse_input` for what
it accepts, `Manifest.parseValue_ok` for exactly which JSON values its value stage accepts,
`Manifest.parse_emptyExclusions` for empty exclusions, and the refusal-class
theorems (`parse_malformed`, `topLevel_emptySurfaces`, `topLevel_schemaVersion`,
`objectWithKeys_unknown`, `parseSurface_execution_refuses` and their lifts) for the
message of each of those defects. -/
private def manifestQualification (repo scratch : FilePath) : IO (Array String) := do
  let mut failures : Array String := #[]
  let valid ← parsedManifest (Manifest.defaultPath repo)
  if valid.surfaces.isEmpty then failures := failures.push "manifest/valid: no surfaces"
  if valid.excludedExecutables.isEmpty then
    failures := failures.push "manifest/valid: no excluded executables"
  let missing := scratch / "missing.json"
  if let some failure ← expectManifestPublicFailure repo "missing" missing "manifest-missing" then
    failures := failures.push failure
  let malformed := scratch / "malformed.json"
  IO.FS.writeFile malformed "{"
  if let some failure ← expectManifestPublicFailure repo "malformed" malformed
      "manifest-malformed" then
    failures := failures.push failure
  let incomplete := scratch / "incomplete.json"
  IO.FS.writeFile incomplete
    "{\"schema-version\":2,\"surfaces\":[],\"excluded-libraries\":[],\"excluded-executables\":[]}"
  if let some failure ← expectManifestPublicFailure repo "incomplete" incomplete
      "manifest-incomplete: surfaces must be a nonempty array" then
    failures := failures.push failure
  let wrongVersion := scratch / "wrong-version.json"
  IO.FS.writeFile wrongVersion <| "{\"schema-version\":1,\"surfaces\":[{" ++
    "\"library\":\"AuditApp\",\"claim\":\"standard-logical\",\"rationale\":\"control\"}]," ++
    "\"excluded-libraries\":[],\"excluded-executables\":[]}"
  if let some failure ← expectManifestPublicFailure repo "wrong-version" wrongVersion
      "manifest-schema: schema-version must be exactly 2" then
    failures := failures.push failure
  let unknown := scratch / "unknown.json"
  IO.FS.writeFile unknown <| "{\"schema-version\":2,\"surfaces\":[{" ++
    "\"library\":\"AuditApp\",\"claim\":\"standard-logical\",\"rationale\":\"control\",\"extra\":true}\
      ]," ++
    "\"excluded-libraries\":[{\"library\":\"Fixtures\",\"rationale\":\"mutations\"}]," ++
    "\"excluded-executables\":[]}"
  if let some failure ← expectManifestPublicFailure repo "unknown" unknown
      "manifest-schema: surfaces[0] has unknown key(s)" then
    failures := failures.push failure
  let badExecution := scratch / "bad-execution.json"
  IO.FS.writeFile badExecution <| "{\"schema-version\":2,\"surfaces\":[{" ++
    "\"library\":\"AuditApp\",\"claim\":\"standard-logical\",\"execution\":\"bogus\",\"rationale\":\"c\
      ontrol\"}]," ++
    "\"excluded-libraries\":[],\"excluded-executables\":[]}"
  if let some failure ← expectManifestPublicFailure repo "bad-execution" badExecution
      "manifest-schema: surfaces[0].execution must be \"report\" or \"checked\"" then
    failures := failures.push failure
  let unknownLibrary := scratch / "unknown-library.json"
  IO.FS.writeFile unknownLibrary <| "{\"schema-version\":2,\"surfaces\":[{" ++
    "\"library\":\"NoSuchLibrary\",\"claim\":\"standard-logical\",\"rationale\":\"negative\"}]," ++
    "\"excluded-libraries\":[{\"library\":\"Fixtures\",\"rationale\":\"mutations\"}," ++
    "{\"library\":\"Regula\",\"rationale\":\"checker\"}]," ++
    "\"excluded-executables\":[{\"executable\":\"axiomGate\",\"rationale\":\"tooling\"}," ++
    "{\"executable\":\"docFenceAudit\",\"rationale\":\"tooling\"}," ++
    "{\"executable\":\"freshChecker\",\"rationale\":\"tooling\"}," ++
    "{\"executable\":\"checkerSelftest\",\"rationale\":\"tooling\"}]}"
  if let some failure ← expectManifestPublicFailure repo "unknown-library" unknownLibrary
      "manifest-incomplete: library 'NoSuchLibrary' is not a root Lean library" then
    failures := failures.push failure
  return failures

private def appendFailure (failures : IO.Ref (Array String)) (value : Option String) : IO Unit :=
  if let some failure := value then failures.modify (·.push failure) else pure ()

/-- Preserve project-relative source and asset locations using the same fresh
copy operation as the public gate, rather than a second fixed source list. -/
private def prepareScratchRepo (repo scratch : FilePath) : IO Unit :=
  copyProject repo scratch scratch

private def withNewFile {α : Type} (path : FilePath) (text : String) (action : IO α) : IO α := do
  if ← path.pathExists then
    throw <| IO.userError s!"refusing to overwrite structural fixture {path}"
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path text
  try action
  finally if ← path.pathExists then IO.FS.removeFile path

private def withReplacedFile {α : Type} (path : FilePath) (text : String) (action : IO α) :
    IO α := do
  let original ← IO.FS.readFile path
  IO.FS.writeFile path text
  try action
  finally IO.FS.writeFile path original

private def withRemovedFile {α : Type} (path : FilePath) (action : IO α) : IO α := do
  let original ← IO.FS.readFile path
  IO.FS.removeFile path
  try action
  finally IO.FS.writeFile path original

private def expectedFailure (name : String) (result : ProcessResult)
    (needles : Array String) : Option String :=
  if result.succeeded then
    some s!"structural/{name}: mutation unexpectedly passed:\n{result.output}"
  else if let some missing := needles.find? fun needle => !result.output.contains needle then
    some s!"structural/{name}: missing diagnostic {repr missing}:\n{result.output}"
  else none

/-- Manifest of the structural project: the actual repository manifest's entries for the
project's libraries, so the application surface keeps its actual claim, execution claim and
executables, and every other library of the project its actual classification. It is derived
from the actual manifest: `Manifest.restrict_libraries` makes its classified libraries exactly
the actual ones among the project's, and `Manifest.executables_restrict` its executables
exactly those the kept surfaces claim. `Manifest.restrict_roundtrip` proves that the JSON value
stage of the gate's `parse` recovers this manifest exactly from `Manifest.toJson` and that its
identity stage (`Manifest.recordTargets`) returns it unchanged. Its hypothesis that the
restriction keeps a surface is what the first guard below checks at run time, not a theorem.
The second guard requires the application to be the only claimed library of the project, so
its executables are exactly the project's (`StructuralProject.executables`) and no gate in the
project inspects another library. Rendering with `Json.compress` and reading with
`PolicyCodec.parse` stay trusted, as do the `auditAppVariant` rewrites. The mutations' intended
reasons are surface-content-agnostic; the heavy-surface end-to-end coverage stays in the
conditional tier's public-surface control and the standalone CI gate. -/
private def structuralBase (layout : SourceLayout) (repo : FilePath) : IO Manifest := do
  let actual ← parsedManifest (Manifest.defaultPath repo)
  let base := Manifest.restrict actual layout.project.libraries
  unless base.surfaces.any (·.library == structuralApplication) do
    throw <| IO.userError s!"structural control requires the actual {structuralApplication} surface"
  unless base.surfaces.all (·.library == structuralApplication) do
    throw <| IO.userError s!"structural control: {structuralApplication} imports a module of \
      another claimed library, which the structural project would have to claim too: \
      {base.surfaces.map (·.library)}"
  return base

private def structuralManifestText (layout : SourceLayout) (repo : FilePath) : IO String := do
  return (Manifest.toJson (← structuralBase layout repo)).compress

/-- `AuditApp` and the policy library the probe imports; every other library stays excluded. -/
private def selfHostedClaims : Array String := #[structuralApplication, "RegulaPolicy"]

/-- Manifest claimed inside the self-hosted copy (`structuralSelfHosted`): the actual repository
manifest's `AuditApp` surface and the `RegulaPolicy` surface, with every other actual library
and executable excluded. `RegulaPolicy` must stay claimed because the checker probe's own
imports resolve to it inside a self-hosted copy. `Manifest.structural_libraries` and
`structural_executables` make the classified names of this in-memory manifest exactly the
actual ones, and `Manifest.structural_roundtrip` covers what the gate reads of it, under the
hypothesis the guard below checks at run time. -/
private def selfHostedManifestText (repo : FilePath) : IO String := do
  let actual ← parsedManifest (Manifest.defaultPath repo)
  for library in selfHostedClaims do
    unless actual.surfaces.any (·.library == library) do
      throw <| IO.userError s!"structural control requires the actual {library} surface"
  return (Manifest.toJson (Manifest.structuralManifest actual selfHostedClaims)).compress

/-- A structural manifest whose `AuditApp` surface claims exactly `executables`; the actual
`AuditApp` executables it no longer claims are excluded when `excludeApp`, and otherwise
left unclassified. -/
private def auditAppVariant (layout : SourceLayout) (repo : FilePath)
    (executables : Array String) (excludeApp : Bool) : IO String := do
  let base ← structuralBase layout repo
  let released := (base.surfaces.filter (·.library == structuralApplication)).flatMap
    (·.executables) |>.filter (!executables.contains ·)
  let surfaces := base.surfaces.map fun s =>
    if s.library == structuralApplication then { s with executables } else s
  let excludedExecutables := if excludeApp then
    base.excludedExecutables ++ released.map (⟨·, "application"⟩) else base.excludedExecutables
  return (Manifest.toJson { base with surfaces, excludedExecutables }).compress

/-- The structural project in `copy` (`StructuralProject`): its sources at their places in the
repository, its Lake configuration, the repository's toolchain pin and lock manifest, and the
manifest of `structuralBase`. -/
private def prepareStructuralProject (layout : SourceLayout) (repo copy : FilePath) :
    IO Unit := do
  for relative in layout.project.sources do
    let destination := copy / relative
    if let some parent := destination.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile destination (← IO.FS.readBinFile (repo / relative))
  for file in #["lean-toolchain", "lake-manifest.json"] do
    IO.FS.writeBinFile (copy / file) (← IO.FS.readBinFile (repo / file))
  IO.FS.writeFile (copy / "lakefile.lean") layout.project.lakefile
  IO.FS.writeFile (copy / "foundation_manifest.json")
    ((← structuralManifestText layout repo) ++ "\n")

/-- Structural mutation cluster: discovery of added modules, suppressed
warnings, and contamination of the claimed library root by excluded fixture
modules (direct and exact-prefix-lookalike). -/
private unsafe def structuralPartA (layout : SourceLayout) (repo copy : FilePath) : IO
    (Array String) := do
  let sources := copy / layout.relativeDir
  let failures ← IO.mkRef (#[] : Array String)
  let gate (args : Array String := #["--incremental"]) :=
    runBinaryFrom repo copy "axiomGate" args
  let unchecked := "import Lean\nopen Lean Elab Command\n" ++
    "run_cmd do\n  let d := Declaration.thmDecl { name := `admissionFalse, " ++
    "levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }\n" ++
    "  match (← getEnv).addDeclCore 200000 1000 d none false with\n" ++
    "  | .ok env => setEnv env\n  | .error _ => throwError \"construction failed\"\n"
  withNewFile (sources / "AuditApp" / "AdmissionProbe.lean") unchecked do
    for (name, args) in #[("project-admission", #["--incremental"]),
        ("build-admission", #["--build-lint"])] do
      if let some failure := expectedFailure name (← gate args)
          #["kernel-admission", "admissionFalse"] then
        failures.modify (·.push failure)
    let imported :=
        "import AuditApp.AdmissionProbe\ntheorem importedAdmission : False := admissionFalse\n"
    withNewFile (copy / "ImportedAdmission.lean") imported do
      if let some failure := expectedFailure "file-imported-admission"
          (← gate #["--file", "ImportedAdmission.lean"])
          #["kernel-admission", "admissionFalse"] then
        failures.modify (·.push failure)
    withNewFile (copy / "admission-docs" / "example.md") ("```lean\n" ++ imported ++ "```\n") do
      if let some failure := expectedFailure "fence-imported-admission"
          (← runBinaryFrom repo copy "docFenceAudit" #["--docs-root", "admission-docs"])
          #["kernel-admission", "admissionFalse"] then
        failures.modify (·.push failure)
  withNewFile (sources / "AuditApp" / "DiscoveryAxiom.lean")
      "/-! Discovery control for an otherwise unused owned axiom. -/\n/-- An unused owned axiom, \
        which RG1001 rejects. -/\naxiom selftest_discovered_axiom : False\n" do
    if let some failure := expectedFailure "add-only-discovery" (← gate)
        #["project-axiom", "selftest_discovered_axiom"] then
      failures.modify (·.push failure)
  withNewFile (sources / "AuditApp" / "SuppressedWarning.lean")
      "set_option warningAsError false in\ndef selftest_suppressed_warning (unused : Nat) : Nat := \
        1\n" do
    -- `linter.unusedVariables` occurs only on the warning's continuation
    -- line, so the transcript must carry the whole diagnostic block.
    if let some failure := expectedFailure "warning-suppression" (← gate)
        #["build-failed", "warning", "linter.unusedVariables"] then
      failures.modify (·.push failure)
  let appRoot := sources / "AuditApp.lean"
  let originalRoot ← IO.FS.readFile appRoot
  let contaminated := originalRoot.replace "import AuditApp.Demo\n"
    "import AuditApp.Demo\nimport Fixtures.Mutations.DirectAxiom\n"
  withReplacedFile appRoot contaminated do
    if let some failure := expectedFailure "fixture-contamination" (← gate)
        #["unexpected-project-module", "Fixtures.Mutations.DirectAxiom"] then
      failures.modify (·.push failure)
  let prefixFixture := sources / "Fixtures" / "Mutations" / "PrefixLookalike.lean"
  withNewFile prefixFixture "axiom AuditApp.lookalike_project_axiom : False\n" do
    let prefixed := originalRoot.replace "import AuditApp.Demo\n"
      "import AuditApp.Demo\nimport Fixtures.Mutations.PrefixLookalike\n"
    withReplacedFile appRoot prefixed do
      if let some failure := expectedFailure "exact-prefix-lookalike" (← gate)
          #["unexpected-project-module", "Fixtures.Mutations.PrefixLookalike"] then
        failures.modify (·.push failure)
  let restored ← gate #[]
  if !restored.succeeded then
    failures.modify (·.push s!"structural/restored: final fresh gate failed:\n{restored.output}")
  failures.get

/-- The self-hosted copy in `copy`: a copy of the repository, by the fresh gate's own copy
operation, that claims `selfHostedManifestText`. Its content is a function of the repository's
files and manifest alone. -/
private def prepareSelfHosted (repo copy : FilePath) : IO Unit := do
  prepareScratchRepo repo copy
  IO.FS.writeFile (copy / "foundation_manifest.json") ((← selfHostedManifestText repo) ++ "\n")

/-- What a fresh gate reads of `project`: the entries its own copy operation (`copyProject`)
copies into `snapshot`, each by its path below the project, a file with its bytes, in path
order. The copy operation's own `.lake` there (the link to the shared packages, the path
overrides) is not an entry: it copies nothing from the project's `.lake`. -/
private def freshInput (project snapshot : FilePath) :
    IO (Array (String × Option ByteArray)) := do
  prepareScratchRepo project snapshot
  let base := snapshot.normalize.components
  let own (path : FilePath) : List String := path.normalize.components.drop base.length
  let lake := _root_.Lake.defaultLakeDir.toString
  let mut entries : Array (String × Option ByteArray) := #[]
  for path in ← snapshot.walkDir (fun path => pure (own path != [lake])) do
    if own path == [lake] then continue
    let content ← if ← path.isDir then pure none else some <$> IO.FS.readBinFile path
    entries := entries.push ("/".intercalate (own path), content)
  return entries.qsort (·.1 < ·.1)

/-- The first entry by which two fresh inputs differ, for a failure message. -/
private def freshInputDifference (before after : Array (String × Option ByteArray)) :
    Option String :=
  if before == after then none
  else some <| match (before.zip after).find? (fun (b, a) => b != a) with
    | some (b, a) => if b.1 == a.1 then b.1 else s!"{b.1} / {a.1}"
    | none => s!"{before.size} entries before, {after.size} after"

/-- The one structural control that needs the checker's own package as the audited project: in
a copy of the repository, the probe modules are exempt from the environment-level exclusion
check (the force import always brings them in), and a claimed module importing the probe's
report records must still be rejected as excluded-module contamination. The structural
project has no source for that module, so the import there could not be this contamination.
The copy claims `selfHostedManifestText`, so its gate builds and inspects `RegulaPolicy` too.

This control was changed when the partition was divided into shards. No fresh gate runs on
the copy this cluster mutated and restored. That accepting gate is replaced by two things: a
checked identity, here, of the restored copy's fresh input (`freshInput`) with that of a copy
prepared anew, and the accepting fresh gate on a copy prepared anew
(`structuralSelfHostedPositive`), which is in the other shard and so may be another
invocation's. The identity is compared path by path and byte by byte, and any difference fails
this cluster. That the two together stand for the replaced gate rests on two facts, neither of
them a theorem:

1. A fresh gate reads the audited project only through its copy operation (`copyProject`,
   which prunes the project's `.lake`), and builds that copy from empty output; without
   `--with-docs`, as here, it reads no other file of the project, and the packages directory
   it links is the repository's for every copy. `freshInput` is that operation's output. So
   equal fresh input gives the same gate run, and the setup build, the incremental gate and the
   restoration are observed to leave the prepared input.
2. The two shards are jobs of one workflow matrix, so whenever the diagnostics workflow runs
   them it starts both on the one commit it checks out, where `prepareSelfHosted` prepares the
   same copy for each. That both pass before merging is enforced by the ruleset of `main`, not
   by this module, which observes nothing of the other job. The workflow runs the matrix on a
   pull request exactly when the pull request changes one of the paths
   `Regula.DiagnosticsGate.inputs` lists, and its last job, `diagnostics`, a required check that
   reports on every pull request, passes on a run where the matrix applies only when the matrix
   job succeeded in that run (`Regula.DiagnosticsGate.verdict_iff`). That GitHub reports a
   matrix job succeeded only when every job of it did is GitHub's behaviour, trusted. -/
private unsafe def structuralSelfHosted (layout : SourceLayout) (repo copy : FilePath) : IO
    (Array String) := do
  let failures ← IO.mkRef (#[] : Array String)
  let gate (args : Array String := #["--incremental"]) :=
    runBinaryFrom repo copy "axiomGate" args
  let appRoot := copy / layout.relativeDir / "AuditApp.lean"
  let originalRoot ← IO.FS.readFile appRoot
  let probeContaminated := originalRoot.replace "import AuditApp.Demo\n"
    "import AuditApp.Demo\nimport Regula.Report\n"
  withReplacedFile appRoot probeContaminated do
    if let some failure := expectedFailure "probe-contamination" (← gate)
        #["unexpected-project-module", "Regula.Report"] then
      failures.modify (·.push failure)
  let some parent := copy.parent
    | throw <| IO.userError s!"self-test: the self-hosted copy {copy} has no parent directory"
  let prepared := parent / "self-hosted-prepared"
  prepareSelfHosted repo prepared
  let before ← freshInput prepared (parent / "self-hosted-input-prepared")
  let after ← freshInput copy (parent / "self-hosted-input-restored")
  if let some difference := freshInputDifference before after then
    failures.modify (·.push s!"structural/self-hosted/restored: the restored copy is not the \
      prepared one for a fresh gate; first difference: {difference}")
  failures.get

/-- The positive of `structuralSelfHosted`: the fresh gate accepts the self-hosted copy without
the mutation. It is not a gate on the mutated and restored copy, which no fresh gate audits any
more. Its project is the copy as prepared (`prepareSelfHosted`), whose fresh input
`structuralSelfHosted` checks equal to that of its own copy once the mutation is restored; the
docstring there states the substitution and the two facts it rests on. -/
private unsafe def structuralSelfHostedPositive (repo copy : FilePath) : IO (Array String) := do
  prepareSelfHosted repo copy
  let accepted ← runBinaryFrom repo copy "axiomGate" #[]
  if accepted.succeeded then return #[]
  return #[s!"structural/self-hosted/positive: fresh gate failed:\n{accepted.output}"]

/-- Structural mutation cluster: unlisted root-owned modules, unclassified
Lake libraries and executables, claimed standalone executable roots, and
executable contamination. -/
private unsafe def structuralPartB (layout : SourceLayout) (repo copy : FilePath) : IO
    (Array String) := do
  let sources := copy / layout.relativeDir
  let failures ← IO.mkRef (#[] : Array String)
  let gate (args : Array String := #["--incremental"]) :=
    runBinaryFrom repo copy "axiomGate" args
  let appRoot := sources / "AuditApp.lean"
  let originalRoot ← IO.FS.readFile appRoot
  -- Library-only variant of the structural manifest: the unlisted root-owned
  -- module mutation must only build the claimed library (linking the
  -- application executable would require the unlisted module's initializer,
  -- which Lake never compiled), so this control claims the `AuditApp` library
  -- and classifies the application executable as excluded.
  let libOnlyManifest := copy / "lib-only.json"
  IO.FS.writeFile libOnlyManifest (← auditAppVariant layout repo #[] true)
  withNewFile (sources / "AuditLookalike.lean") "axiom Attack.lookalikeAxiom : False\n" do
    let outputDir := copy / ".lake" / "build" / "lib" / "lean"
    IO.FS.createDirAll outputDir
    let compiled ← runProcess copy "lake" #["env", "lean", "-R", sources.toString, "-o",
      (outputDir / "AuditLookalike.olean").toString,
      (sources / "AuditLookalike.lean").toString]
    if !compiled.succeeded then
      failures.modify (·.push s!"structural/unlisted-root-setup: {compiled.output}")
    else
      let unlisted := originalRoot.replace "import AuditApp.Demo\n"
        "import AuditApp.Demo\nimport AuditLookalike\n"
      withReplacedFile appRoot unlisted do
        if let some failure := expectedFailure "unlisted-root-module"
            (← gate #["--manifest", libOnlyManifest.toString, "--incremental"])
            #["unexpected-project-module", "AuditLookalike"] then
          failures.modify (·.push failure)
  let lakefile := copy / "lakefile.lean"
  let originalLakefile ← IO.FS.readFile lakefile
  withNewFile (sources / "ExtraSurface.lean") "def extraSurfaceValue : Nat := 1\n" do
    withReplacedFile lakefile
        (originalLakefile ++ "\nlean_lib «ExtraSurface» where\n  roots := #[`ExtraSurface]\n") do
      if let some failure := expectedFailure "unclassified-library" (← gate)
          #["manifest-incomplete", "ExtraSurface"] then
        failures.modify (·.push failure)
  let exeDecl :=
    "\nlean_exe «selftestTool» where\n  root := `SelftestMain\n"
  let claimedManifest := copy / "claimed-exe.json"
  -- The claimed-exe controls claim the added executable beside the application's: both roots
  -- define `main`, so the positive control also requires each root to be inspected in an
  -- environment of its own (`census_executable_alone`).
  let claimedManifestText ← auditAppVariant layout repo #["auditApp", "selftestTool"] true
  let claimedGate := gate #["--manifest", claimedManifest.toString, "--incremental"]
  withNewFile (sources / "SelftestMain.lean") "/-! Standalone no-effect IO entrypoint. -/\n/-- \
    Does nothing. -/\ndef main : IO Unit := pure ()\n" do
    withReplacedFile lakefile (originalLakefile ++ exeDecl) do
      if let some failure := expectedFailure "unclassified-exe" (← gate)
          #["manifest-incomplete", "selftestTool"] then
        failures.modify (·.push failure)
      IO.FS.writeFile claimedManifest claimedManifestText
      let claimed ← claimedGate
      if !claimed.succeeded then
        failures.modify (·.push
          s!"structural/claimed-exe: claimed standalone exe root did not pass:\n{claimed.output}")
      else
        let plan ← runBinaryFrom repo copy "freshChecker"
          #["--plan-only", "--manifest", claimedManifest.toString]
        if !plan.succeeded || !plan.output.contains "SelftestMain" then
          failures.modify (·.push
            s!"structural/claimed-exe-fresh: exe root missing its own fresh coverage \
              root:\n{plan.output}")
      withRemovedFile (sources / "SelftestMain.lean") do
        if let some failure := expectedFailure "claimed-exe-source-removed" (← claimedGate)
            #["lake-query-malformed", "invalid source"] then
          failures.modify (·.push failure)
  withNewFile (sources / "SelftestMain.lean")
      "import Fixtures.Mutations.DirectAxiom\n/-! Standalone import-contamination control. -/\n/-- \
        Does nothing. -/\ndef main : IO Unit := pure ()\n" do
    withReplacedFile lakefile (originalLakefile ++ exeDecl) do
      IO.FS.writeFile claimedManifest claimedManifestText
      if let some failure := expectedFailure "exe-contamination" (← claimedGate)
          #["unexpected-project-module", "Fixtures.Mutations.DirectAxiom"] then
        failures.modify (·.push failure)
  let restored ← gate #[]
  if !restored.succeeded then
    failures.modify (·.push s!"structural/restored: final fresh gate failed:\n{restored.output}")
  failures.get

/-- Structural mutation cluster: omitted executable classification,
application-surface proof erasure and admission weakening. -/
private unsafe def structuralPartC (layout : SourceLayout) (repo copy : FilePath) : IO
    (Array String) := do
  let sources := copy / layout.relativeDir
  let failures ← IO.mkRef (#[] : Array String)
  let gate (args : Array String := #["--incremental"]) :=
    runBinaryFrom repo copy "axiomGate" args
  let appOmittedManifest := copy / "app-omitted-exe.json"
  IO.FS.writeFile appOmittedManifest (← auditAppVariant layout repo #[] false)
  if let some failure := expectedFailure "app-omitted-exe"
      (← gate #["--manifest", appOmittedManifest.toString, "--incremental"])
      #["manifest-incomplete", "auditApp"] then
    failures.modify (·.push failure)
  let appCore := sources / "AuditApp" / "Limiter.lean"
  let originalCore ← IO.FS.readFile appCore
  -- Change exactly one source fragment; a stale fixture is a setup failure.
  -- Every negative uses the public gate and every restoration builds fresh.
  let mutate (name before after : String) (needles : Array String) : IO Unit := do
    if (originalCore.splitOn before).length != 2 then
      failures.modify (·.push s!"structural/{name}: expected exactly one source fragment")
      return
    withReplacedFile appCore (originalCore.replace before after) do
      if let some failure := expectedFailure name (← gate) needles then
        failures.modify (·.push failure)
    let restored ← gate #[]
    if !restored.succeeded then
      failures.modify (·.push s!"structural/{name}/restored: fresh gate failed:\n{restored.output}")
  let resetProof := "/-- A reset limiter has no slots in use. -/\n" ++
    "theorem reset_inUse (l : Limiter) : (reset l).inUse = 0 := rfl\n"
  mutate "app-unproved-update" resetProof ""
    #["build-failed", "Unknown identifier", "reset_inUse"]
  mutate "app-trivial-update" resetProof
    "/-- Deliberately unrelated proof. -/\ntheorem reset_inUse : True := True.intro\n"
    #["build-failed", "Type mismatch", "reset_inUse", "∀ (l : Limiter), (reset l).inUse = 0"]
  mutate "app-weakened-update" resetProof
    ("/-- Deliberately conditional proof. -/\n" ++
      "theorem reset_inUse (l : Limiter) (_h : l.inUse = 0) : (reset l).inUse = 0 := rfl\n")
    #["build-failed", "Type mismatch", "reset_inUse", "∀ (l : Limiter), (reset l).inUse = 0"]
  mutate "app-missing-contract-field" "  reset_empty := reset_inUse\n" ""
    #["build-failed", "Fields missing", "reset_empty"]
  mutate "app-weakened-admission"
    "if _h : 0 < capacity then" "if _h : 0 ≤ capacity then"
    #["build-failed", "hpos", "0 <", "0 ≤"]
  -- Empty-exclusion acceptance is covered by adopterQualification's fresh
  -- standalone library/executable controls in both Lake formats.
  -- The last mutation's own fresh restored gate is this cluster's final restored control: the
  -- manifest control before the mutations changes no file of the copy, and nothing follows it.
  failures.get

/-- A claimed module in which `simp` realizes `Except.mapError.eq_1`, which the toolchain's
`Std.Do.WP.SimpLemmas` also contains (issue #128). -/
private def realizedLemmaSource : String :=
  "/-! Realizes `Except.mapError.eq_1`, which `Std.Do.WP.SimpLemmas` also contains. -/\n\n" ++
  "/-- Mapping the error of a success keeps the value. -/\n" ++
  "theorem selftestMapErrorOk (value : Nat) :\n" ++
  "    (Except.ok value : Except String Nat).mapError String.length = .ok value := by\n" ++
  "  simp [Except.mapError]\n"

/-- The body of a file importing the realizing module and the toolchain module with the same
lemma, in the order its caller writes before it. -/
private def realizedDuplicateSource : String :=
  "\n/-! Imports two modules that both contain `Except.mapError.eq_1`. -/\n\n" ++
  "/-- The claimed module's theorem, restated. -/\n" ++
  "theorem selftestRealizedDuplicate (value : Nat) :\n" ++
  "    (Except.ok value : Except String Nat).mapError String.length = .ok value :=\n" ++
  "  selftestMapErrorOk value\n"

/-- A checked theorem of which `uncheckedDuplicateSource` adds an unchecked copy. -/
private def checkedDuplicateSource : String :=
  "/-! A checked theorem that `AuditApp.DuplicateUnchecked` duplicates without checking. -/\n\n" ++
  "/-- A checked proof of `True`. -/\ntheorem selftestDuplicateFact : True := trivial\n"

/-- The same theorem statement with the proof `value`, added without kernel checking. -/
private def uncheckedDuplicateSource (value : String) : String :=
  "import Lean\nopen Lean Elab Command\n" ++
  "run_cmd do\n  let d := Declaration.thmDecl { name := `selftestDuplicateFact, " ++
  s!"levelParams := [], type := mkConst ``True, value := {value} }\n" ++
  "  match (← getEnv).addDeclCore 200000 1000 d none false with\n" ++
  "  | .ok env => setEnv env\n  | .error _ => throwError \"construction failed\"\n"

/-- The same theorem statement proved by `sorry`, which the kernel accepts. -/
private def sorryDuplicateSource : String :=
  "/-! A copy of `selftestDuplicateFact` whose proof is `sorry`. -/\n\n" ++
  "set_option warn.sorry false in\n/-- An unproved copy. -/\n" ++
  "theorem selftestDuplicateFact : True := sorry\n"

/-- Unchecked copies of the toolchain's `Except.mapError.eq_1` and `Except.mapError.eq_2`, each
proved through the other, so the audited environment keeps a cycle over two base theorems while
each copy alone is fine in the replayed kernel, where the other name denotes the toolchain's. -/
private def keptCycleSource : String :=
  "import Lean\nopen Lean Elab Command\n" ++
  "run_cmd do\n" ++
  "  let env ← getEnv\n" ++
  "  let some (.thmInfo one) := env.find? `Except.mapError.eq_1 | throwError \"no eq_1\"\n" ++
  "  let some (.thmInfo two) := env.find? `Except.mapError.eq_2 | throwError \"no eq_2\"\n" ++
  "  let use (target other : TheoremVal) : Expr := mkApp (.lam `h other.type target.value " ++
  ".default) (mkConst other.name (other.levelParams.map mkLevelParam))\n" ++
  "  let mut env := env\n" ++
  "  for (target, other) in [(one, two), (two, one)] do\n" ++
  "    match env.addDeclCore 200000 1000 (.thmDecl { target with value := use target other }) " ++
  "none false with\n" ++
  "    | .ok next => env := next\n" ++
  "    | .error _ => throwError \"construction failed\"\n" ++
  "  setEnv env\n"

/-- External-boundary controls for a name several owned or imported modules contain, where the
copies Lean realizes, imports, keeps and kernel-checks are the external mechanism
(`Admission.replayMap_sound`, `Admission.replayMap_complete` and `Admission.checkCopies_sound`
state the admission decision). The positive controls are issue #128's shape in both import
orders; on the pinned toolchain the two realized copies are identical, so they exercise the
identical-copy path and would catch an over-strict check. The mutations import an unchecked copy
of a checked theorem: an ill-typed one first (the kernel rejects it under a fresh name), the same
one last (the audited environment keeps it, so replay rejects it), a circular one first (its
proof reaches its own name), and a `sorry` one last: the audited environment keeps it while the
name is attributed to the checked copy, whose axioms the report would show, so the copies must
have equal axioms. The last mutation keeps two unchecked toolchain-lemma copies that prove each
other over the toolchain's copies; only the check of the audited environment's kept copies
refuses it.
Each refusal is asserted by its own message. -/
private def duplicateAdmissionControls (sources copy : FilePath)
    (gate : Array String → IO ProcessResult) : IO (Array String) := do
  let failures ← IO.mkRef (#[] : Array String)
  withNewFile (sources / "AuditApp" / "RealizedLemma.lean") realizedLemmaSource do
    for (name, imports) in #[
        ("realized-duplicate", "import AuditApp.RealizedLemma\nimport Std.Do.WP.SimpLemmas\n"),
        ("realized-duplicate-kept",
          "import Std.Do.WP.SimpLemmas\nimport AuditApp.RealizedLemma\n")] do
      withNewFile (copy / "RealizedDuplicate.lean") (imports ++ realizedDuplicateSource) do
        let result ← gate #["--file", "RealizedDuplicate.lean"]
        if !result.succeeded then
          failures.modify (·.push s!"structural/{name}: expected PASS:\n{result.output}")
  withNewFile (sources / "AuditApp" / "DuplicateChecked.lean") checkedDuplicateSource do
    for (name, bogus, first, second, needle) in #[
        ("unchecked-duplicate-first", uncheckedDuplicateSource "mkConst ``False", "Unchecked",
          "Checked", "checked as"),
        ("unchecked-duplicate-last", uncheckedDuplicateSource "mkConst ``False", "Checked",
          "Unchecked", "while replaying declaration"),
        ("circular-duplicate-first", uncheckedDuplicateSource "mkConst `selftestDuplicateFact",
          "Unchecked", "Checked", "uses the name"),
        ("sorry-duplicate-last", sorryDuplicateSource, "Checked", "Unchecked",
          "axioms differ")] do
      withNewFile (sources / "AuditApp" / "DuplicateUnchecked.lean") bogus do
        withNewFile (copy / "DuplicateAdmission.lean")
            s!"import AuditApp.Duplicate{first}\nimport AuditApp.Duplicate{second}\n" do
          if let some failure := expectedFailure name
              (← gate #["--file", "DuplicateAdmission.lean"])
              #["kernel-admission", "selftestDuplicateFact", needle] then
            failures.modify (·.push failure)
  withNewFile (sources / "AuditApp" / "KeptCycle.lean") keptCycleSource do
    withNewFile (copy / "KeptCycle.lean")
        "import Std.Do.WP.SimpLemmas\nimport AuditApp.KeptCycle\n" do
      if let some failure := expectedFailure "kept-cycle"
          (← gate #["--file", "KeptCycle.lean"])
          #["kernel-admission", "Except.mapError.eq_", "audited environment keeps",
            "uses the name"] then
        failures.modify (·.push failure)
  failures.get

/-- A file with a declaration of every `GeneratedFamily` Lean generates: the constructor,
projection, recursors, constructor lemmas and type constructions of a structure whose field type
uses `Classical.choice`, a structure field's default, a matcher, the `_f` and `_sunfold` of a
structural recursion, the equation lemmas and auxiliary proof of a well-founded definition, the
`_unary` and functional induction principle of one with two arguments, the compiled recursion
helper `_unsafe_rec` of a computable one whose value carries a proof that uses `propext`, and the
auxiliary proof only its `eq_def` states, the auxiliary index proof only the `_unsafe_rec` of
another uses, the auxiliary proof only another auxiliary proof of a non-recursive definition
uses, the action of an `initialize` whose value carries such a proof, of a type no other
proof here has, so Lean abstracts it into an auxiliary proof named under the action's hygienic
name; and
declarations Lean does not generate from the declaration they are named under: a theorem a
metaprogram adds without a source range, a user-written `ofNat`, a name Lean generates only for an
enumeration deriving `DecidableEq`, an elaborator Lean names `«_aux_…»` inside the
structure's namespace, and user-written theorems named like auxiliary proofs or an equation lemma:
two of a definition that does not use them, one using the other and a theorem named under the
definition using the first; one in a namespace, which a theorem of the namespace uses; and two
declared before the definition they are named under, which uses the one named like an auxiliary
proof. Every one exceeds a Kernel-only claim, so each has an RG1005 finding. Last, a
`macro_rules` command over two syntax kinds, whose first kind's definition carries a proof that
uses `propext`: Lean records for that definition a selection range that leaves its range
(`RegulaPolicy.Ranges.admitted`). -/
private def sourceAttributionSource : String :=
  "import Lean\n\n/-! # Source attribution control\n\nDeclarations Lean generates. -/\n\n" ++
  "open Lean Elab Command\n\n" ++
  "/-- A value chosen with `Classical.choice`. -/\n" ++
  "noncomputable def pick : Nat := Classical.choose (⟨0, rfl⟩ : ∃ n : Nat, n = n)\n\n" ++
  "/-- A structure whose field type uses `pick`. -/\nstructure Channel where\n" ++
  "  /-- The bounded value. -/\n  value : Fin (pick + 1)\n\n" ++
  "/-- A structure with a conversion of its own. -/\nstructure Word where\n" ++
  "  /-- The bounded value. -/\n  val : Fin (pick + 1)\n\n" ++
  "/-- A user-written conversion from `Nat`. -/\n" ++
  "noncomputable def Word.ofNat (n : Nat) : Word :=\n" ++
  "  ⟨⟨n % (pick + 1), Nat.mod_lt n (Nat.succ_pos pick)⟩⟩\n\n" ++
  "/-- A structure whose field default uses `pick`. -/\nstructure Rec where\n" ++
  "  /-- A bounded value with a default. -/\n  x : Fin (pick + 1) := ⟨0, Nat.succ_pos pick⟩\n\n" ++
  "/-- A definition by pattern matching on a value whose type uses `pick`. -/\n" ++
  "def firstIndex (c : Channel) : Nat :=\n  match c.value with\n  | ⟨0, _⟩ => 0\n" ++
  "  | ⟨k + 1, _⟩ => k\n\n" ++
  "/-- A definition by structural recursion. -/\n" ++
  "noncomputable def walkDown : Nat → Nat\n  | 0 => pick\n  | n + 1 => walkDown n\n\n" ++
  "namespace Channel\n\n/-- A term elaborated in `Channel`'s namespace. -/\n" ++
  "elab \"vzero\" : term => Term.elabTerm (Syntax.mkNumLit \"0\") none\n\nend Channel\n\n" ++
  "/-- A definition by well-founded recursion. -/\n" ++
  "def countdown (n : Nat) : Nat := if h : n = 0 then 0 else countdown (n - 1)\n" ++
  "termination_by n\ndecreasing_by omega\n\n" ++
  "/-- Unfolding `countdown` realizes its equation lemmas. -/\n" ++
  "theorem countdown_zero : countdown 0 = 0 := by\n  simp [countdown]\n\n" ++
  "/-- A definition by well-founded recursion on two arguments. -/\n" ++
  "def countPair (m n : Nat) : Nat := if h : m = 0 then n else countPair (m - 1) (n + 1)\n" ++
  "termination_by m\ndecreasing_by omega\n\n" ++
  "/-- A use of `countPair`'s functional induction principle, which realizes it. -/\n" ++
  "theorem countPair_induct_used : True := (fun _ => trivial) (@countPair.induct)\n\n" ++
  "/-- A computable definition by well-founded recursion whose value carries a proof that uses \
    `propext`. -/\n" ++
  "def countUp (n : Nat) : Nat :=\n  have _ : True = True := propext (Iff.refl True)\n" ++
  "  if h : n = 0 then 0 else countUp (n - 1)\ntermination_by n\ndecreasing_by omega\n\n" ++
  "/-- A computable definition by well-founded recursion whose index proof uses `propext`. -/\n" ++
  "def sumButLast (a : Array Nat) (i : Nat) : Nat :=\n" ++
  "  if h : i + 1 < a.size then a[i]'(by omega) + sumButLast a (i + 1) else 0\n" ++
  "termination_by a.size - i\n\n" ++
  "/-- A definition whose index proof Lean abstracts into two lemmas, one used only by the \
    other. -/\n" ++
  "def middle (a : Array Nat) (h : 2 < a.size) : Nat := a[a.size / 2]'(by omega)\n\n" ++
  "/-- A user-written theorem named like an auxiliary proof of `middle`. -/\n" ++
  "theorem middle._proof_8 : pick = pick := rfl\n\n" ++
  "/-- A user-written theorem named like an auxiliary proof, which uses the one above. -/\n" ++
  "theorem middle._proof_9 : pick = pick := middle._proof_8\n\n" ++
  "/-- A user-written theorem named under `middle`, which uses the first one above. -/\n" ++
  "theorem middle.spec : pick = pick := middle._proof_8\n\n" ++
  "namespace Util\n\n" ++
  "/-- A user-written theorem named like an auxiliary proof, in a namespace. -/\n" ++
  "theorem _proof_8 : pick = pick := rfl\n\n" ++
  "/-- A user-written theorem of the namespace, which uses the one above. -/\n" ++
  "theorem spec : pick = pick := Util._proof_8\n\nend Util\n\n" ++
  "/-- A user-written theorem named like an auxiliary proof of `later`, declared before it. -/\n" ++
  "theorem later._proof_8 : pick = pick := rfl\n\n" ++
  "/-- A user-written theorem named like an equation lemma of `later`, declared before it. -/\n" ++
  "theorem later.eq_7 : pick = pick := rfl\n\n" ++
  "/-- A definition that uses the theorem named like its auxiliary proof. -/\n" ++
  "noncomputable def later : Nat := (fun (_ : pick = pick) => pick) later._proof_8\n\n" ++
  "/-- A reference whose initialization action carries a proof that uses `propext`. -/\n" ++
  "initialize counter : IO.Ref Nat ← do\n" ++
  "  have _ : (True ∧ True) = True := propext ⟨And.left, fun h => ⟨h, h⟩⟩\n  IO.mkRef 0\n\n" ++
  "/-- A command that expands to nothing. -/\nsyntax \"#nothing\" : command\n\n" ++
  "/-- The same command with a marker. -/\nsyntax \"#nothing!\" : command\n\n" ++
  "macro_rules\n  | `(#nothing) => do\n" ++
  "    have _ : (True ∧ True ∧ True) = True := propext ⟨fun _ => trivial, fun h => ⟨h, h, h⟩⟩\n" ++
  "    `(section end)\n  | `(#nothing!) => `(section end)\n\n" ++
  "run_cmd liftTermElabM do\n  addDecl <| .thmDecl {\n" ++
  "    name := `Channel.fact, levelParams := []\n" ++
  "    type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkConst ``pick) (mkConst ``pick)\n" ++
  "    value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkConst ``pick) }\n"

/-- The first failed expectation of the source-attribution report, if any: a declaration of every
`GeneratedFamily` (`Channel`'s constructor, projection, recursor, constructor lemmas and type
constructions, `Rec.x._default`, `firstIndex.match_1`, `walkDown._f` and `walkDown._sunfold`,
`countdown`'s equation lemma and auxiliary proof, `countPair._unary` and `countPair.induct`, and
the admitted recursion helper `countUp._unsafe_rec`), the auxiliary proofs `countUp._proof_3`,
which only `countUp.eq_def` states, `sumButLast._proof_1`, which only the admitted helper
`sumButLast._unsafe_rec` uses and whose chain runs through it, and `middle._proof_1`, which only
`middle._proof_2` uses and whose chain runs through it, the action of `initialize counter`
and that action's auxiliary proof, whose chain runs through the action, is attributed to the
declaration Lean generated it from. One without a range of its own is located at that
declaration's range, with its own module as a related location; one with a range of its own keeps
it, with no related location: `Channel.value` at its field and the action at its `initialize`
command, both other than their source's, and `Channel.mk` at the structure's name, where Lean
records an implicit constructor (`expandCtor`, `Lean/Elab/Structure.lean:235-246`). `Rec`'s
range is read from its own finding or, when it has none, from its implicit constructor's finding,
at the same name: Lean's `exportedAxiomsExt`
(`Lean/Util/CollectAxioms.lean:118-140` in the v4.34.0 toolchain source) computes a module's
axioms in one shared cache, and when it reaches an inductive first through its constructor, it
caches the inductive with that constructor's in-progress empty entry, so the inductive can record
no axiom while its constructor records `Classical.choice`. The claim is still rejected, because
the constructor is flagged. None of
`Channel.fact`, which has no source range, `Word.ofNat` and the `vzero` elaborator in `Channel`'s
namespace is attributed, though each is named under a structure: Lean did not generate them from
it. `Channel.fact` keeps module attribution, and `Word.ofNat` and the elaborator their own
range. Neither is a user-written theorem named like a generated declaration, which has a
declaration range where the ones Lean generates have none: `middle._proof_8`, which the
user-written `middle._proof_9` and `middle.spec` use, `middle._proof_9`, which nothing uses,
`Util._proof_8`, which `Util.spec` uses in a namespace no declaration names, and `later._proof_8`
and `later.eq_7`, declared before `later`, which uses the first. Each keeps its own range. The
definition Lean generates for the first syntax kind of the `macro_rules` command has a recorded
selection range that ends after its range does, and its finding is located at its recorded
range, which is the admitted selection range too (`RegulaPolicy.Ranges.admitted`). -/
private def sourceAttributionFailure (report : Json) : Option String := Id.run do
  let some diagnostics := (report.getObjValAs? (Array Json) "diagnostics").toOption
    | return some "no diagnostics"
  let find (name : String) : Option Json := diagnostics.find? fun d =>
    (d.getObjValD "arguments").getObjValD "declaration" == .str name
  let selection (d : Json) : Json := (d.getObjValD "location").getObjValD "selectionRange"
  let kind (d : Json) : Json := (d.getObjValD "location").getObjValD "kind"
  let source (d : Json) : Json := (d.getObjValD "arguments").getObjValD "sourceDeclaration"
  let relation (d : Json) : Option Json :=
    ((d.getObjValD "related").getArrVal? 0).toOption.map (·.getObjValD "relation")
  let attributed (d owner : Json) (ownerName : String) : Bool :=
    source d == .str ownerName && kind d == .str "source" && selection d == selection owner &&
      relation d == some (.str "declared in module")
  let keepsOwn (d owner : Json) (ownerName : String) (distinct : Bool) : Bool :=
    source d == .str ownerName && kind d == .str "source" &&
      d.getObjValD "related" == Json.arr #[] && (!distinct || selection d != selection owner)
  let some channel := find "Channel" | return some "no Channel finding"
  for (name, distinct) in #[("Channel.mk", false), ("Channel.value", true)] do
    let some d := find name | return some s!"no {name} finding"
    unless keepsOwn d channel "Channel" distinct do
      return some s!"{name} is not attributed to Channel at its own range"
  for (name, ownerName) in #[
      ("Channel.rec", "Channel"), ("Channel.casesOn", "Channel"), ("countdown.eq_1", "countdown"),
      ("countPair.induct", "countPair"), ("firstIndex.match_1", "firstIndex"),
      ("countPair._unary", "countPair"), ("walkDown._f", "walkDown"),
      ("walkDown._sunfold", "walkDown"), ("countdown._proof_1", "countdown"),
      ("Channel.mk.injEq", "Channel"), ("Channel.mk.sizeOf_spec", "Channel"),
      ("Channel.mk._flat_ctor", "Channel"), ("Channel.ctorIdx", "Channel"),
      ("Channel.noConfusionType", "Channel"), ("Channel._sizeOf_1", "Channel"),
      ("Channel._sizeOf_inst", "Channel"), ("Rec.x._default", "Rec"),
      ("countUp._unsafe_rec", "countUp"), ("countUp._proof_3", "countUp"),
      ("sumButLast._proof_1", "sumButLast"), ("middle._proof_1", "middle"),
      ("middle._proof_2", "middle")] do
    let some owner := find ownerName <|> find (ownerName ++ ".mk")
      | return some s!"no {ownerName} finding"
    let some d := find name | return some s!"no {name} finding"
    unless attributed d owner ownerName do
      return some s!"{name} is not attributed to and located at {ownerName}"
  let userName? (d : Json) : Option Name :=
    match Regula.RegistryCodec.parsePrintedNameJson
        ((d.getObjValD "arguments").getObjValD "declaration") with
    | .ok name => some (privateToUserName name.eraseMacroScopes)
    | _ => none
  let some counter := find "counter" | return some "no counter finding"
  let some action := diagnostics.find? (userName? · == some `initFn)
    | return some "no finding for the action of initialize counter"
  unless keepsOwn action counter "counter" true do
    return some "the action of initialize counter is not attributed to counter at its own range"
  let some proof := diagnostics.find? fun d => match userName? d with
      | some (.str (.str .anonymous "initFn") s) => s.startsWith "_proof_"
      | _ => false
    | return some "no finding for the auxiliary proof of initialize counter's action"
  unless attributed proof counter "counter" do
    return some "the auxiliary proof of initialize counter's action is not attributed to and \
      located at counter"
  let some fact := find "Channel.fact" | return some "no Channel.fact finding"
  unless source fact == .null && kind fact == .str "module" do
    return some "Channel.fact, which Lean did not generate, was attributed"
  let some word := find "Word" | return some "no Word finding"
  let some ofNat := find "Word.ofNat" | return some "no Word.ofNat finding"
  unless source ofNat == .null && kind ofNat == .str "source" &&
      selection ofNat != selection word && ofNat.getObjValD "related" == Json.arr #[] do
    return some "Word.ofNat, which Lean did not generate, was attributed"
  for name in #["middle._proof_8", "middle._proof_9", "Util._proof_8", "later._proof_8",
      "later.eq_7"] do
    let some d := find name | return some s!"no {name} finding"
    unless source d == .null && kind d == .str "source" &&
        d.getObjValD "related" == Json.arr #[] do
      return some s!"{name}, which Lean did not generate, was attributed"
  let some elaborator := diagnostics.find? fun d =>
      match Regula.RegistryCodec.parsePrintedNameJson
          ((d.getObjValD "arguments").getObjValD "declaration") with
      | .ok (.str (.str .anonymous "Channel") s) => s.startsWith "_aux_" && s.contains "termVzero"
      | _ => false
    | return some "no finding for the vzero elaborator in Channel's namespace"
  unless source elaborator == .null && kind elaborator == .str "source" &&
      selection elaborator != selection channel && elaborator.getObjValD "related" == Json.arr #[] do
    return some "the vzero elaborator, which Lean did not generate from Channel, was attributed"
  let rulesName (name : Json) : Bool :=
    match Regula.RegistryCodec.parsePrintedNameJson name with
    | .ok (.str .anonymous s) =>
      s.startsWith "_aux_" && s.endsWith "___macroRules_command#nothing_1"
    | _ => false
  let some recorded := (((report.getObjValD "scope").getObjValD "report").getObjValAs?
      (Array Json) "declarations").toOption.bind
        (·.find? fun declaration => rulesName (declaration.getObjValD "name"))
    | return some "no record of the macro_rules definition of the first syntax kind"
  let recordedEnd (range : String) : Json :=
    ((recorded.getObjValD "ranges").getObjValD range).getObjValD "end"
  if recordedEnd "range" == recordedEnd "selectionRange" then
    return some "Lean recorded a selection range inside the range of the macro_rules definition"
  let some rules := diagnostics.find? fun d =>
      rulesName ((d.getObjValD "arguments").getObjValD "declaration")
    | return some "no finding for the macro_rules definition of the first syntax kind"
  let lastLine := (((rules.getObjValD "location").getObjValD "lspRange").getObjValD
    "end").getObjValD "line"
  unless source rules == .null && kind rules == .str "source" &&
      (rules.getObjValD "location").getObjValD "range" == selection rules &&
      (lastLine.getNat?.toOption.map (· + 1)) ==
        ((recordedEnd "range").getObjValD "line").getNat?.toOption do
    return some "the macro_rules definition is not located at its recorded range"
  return none

/-- External-boundary controls for source attribution through the public `axiomGate --file`
audit. Which declarations Lean generates, and what the environment records about them, is the
compiler's behavior; `Findings.sourceName?_eq_some_iff` states the attribution decision over the
recorded relation and `groupFindings_flatten` the grouping. The positive controls are the
attributed findings, a declaration of every `GeneratedFamily`, and their printed blocks; the
negative controls are a theorem a metaprogram adds without a source range under a declaration's
name, a user-written `ofNat` under a structure's, an elaborator Lean names `«_aux_…»` in a
structure's namespace, and user-written theorems named like a definition's auxiliary proofs or
equation lemma that the definition or a declaration named beside them uses, none of which Lean
generated from it (`sourceAttributionFailure`). The same audit is the control for a recorded
selection range that leaves its range: which ranges Lean records for the definitions of a
`macro_rules` command over several syntax kinds is the compiler's behavior, which no theorem here
states; `RegulaPolicy.Ranges.admitted_validForLines` states what admission requires of a recorded
pair, and the audit is refused with RG2005 unless it admits this one. -/
private def sourceAttributionControls (dir : FilePath)
    (gate : Array String → IO ProcessResult) : IO (Array String) := do
  let report := dir / "source-attribution.json"
  let source := dir / "SourceAttribution.lean"
  withNewFile source sourceAttributionSource do
    try
      let result ← gate #["--file", source.toString, "--claim", "kernel-only",
        "--json-out", report.toString]
      let failed (detail : String) :=
        #[s!"cli/source-attribution: {detail}:\n{result.output}"]
      if result.succeeded then return failed "expected RG1005 findings"
      let json ← match Json.parse (← IO.FS.readFile report) with
        | .ok json => CompilerMode.readObservation json
        | .error error => return failed s!"unreadable report: {error}"
      if let some detail := sourceAttributionFailure json then return failed detail
      unless result.output.contains
            "countdown: it and 3 declarations Lean generated from it exceed the claim" &&
          result.output.contains
            "  attributed: 3 declarations of these are generated by Lean from countdown and reported \
              under it" do
        return failed "the attributed findings did not print as one block under countdown"
      unless result.output.contains "Channel: it and " && !result.output.contains "]: Channel.mk:" do
        return failed "the findings Lean generated from Channel at its location did not print as \
          one block"
      return #[]
    finally
      if ← report.pathExists then IO.FS.removeFile report

/-- Structural mutation cluster: fresh-checker coverage of an added module, controls for several
copies of one name, and the final restored-state control. -/
private unsafe def structuralPartD (layout : SourceLayout) (repo copy : FilePath) : IO
    (Array String) := do
  let sources := copy / layout.relativeDir
  let failures ← IO.mkRef (#[] : Array String)
  let gate (args : Array String := #["--incremental"]) :=
    runBinaryFrom repo copy "axiomGate" args
  for failure in ← duplicateAdmissionControls sources copy (fun args => gate args) do
    failures.modify (·.push failure)
  withNewFile (sources / "AuditApp" / "UnimportedSafe.lean")
      "namespace AuditApp.UnimportedSafe\ndef value : Nat := 1\nend AuditApp.UnimportedSafe\n" do
    let plan ← runBinaryFrom repo copy "freshChecker" #["--plan-only"]
    if !plan.succeeded || !plan.output.contains "AuditApp.UnimportedSafe" then
      failures.modify
          (·.push s!"structural/fresh-coverage: added module was omitted:\n{plan.output}")
  -- Restored control in fresh mode (empty-output elaboration of the copy), so the
  -- harness's green-restore evidence covers stale-artifact freedom, not only
  -- incremental rebuilds.
  let restored ← gate #[]
  if !restored.succeeded then
    failures.modify (·.push s!"structural/restored: final fresh gate failed:\n{restored.output}")
  failures.get

/-- Each restricted-domain/universe mutation starts from its own passing source
and restores that source through a fresh public file audit. `--file` creates and
removes a separate elaboration directory for every invocation. The fixed
negative sweep additionally asserts the exact violation set. -/
private def correspondenceRestoration (layout : SourceLayout) (repo scratch : FilePath) : IO
    (Array String) := do
  let failures ← IO.mkRef (#[] : Array String)
  let controls := #[
    ("RepeatedCorrespondence", "Nat := _n\n", "Nat := _m\n"),
    ("OmittedCorrespondence", "Nat := m\n", "Nat := m + _n\n"),
    ("SpecializedUniverseCorrespondence", "{α : Type}", "{α : Type u}")]
  for (fixture, restricted, general) in controls do
    let negative ← IO.FS.readFile
        ((repo / layout.relativeDir) / "Fixtures" / "Mutations" / s!"{fixture}.lean")
    let positive := negative.replace restricted general
    if positive == negative then
      failures.modify (·.push s!"correspondence/{fixture}: mutation anchor missing")
      continue
    let source := scratch / s!"{fixture}.lean"
    withNewFile source positive do
      -- In this cluster's own project: its file audits build only that project's claimed
      -- targets, so they run no Lake build in the repository beside the other items.
      let gate := runBinaryFrom repo scratch "axiomGate"
        #["--file", source.toString, "--claim", "standard-logical", "--execution", "checked"]
      let green ← gate
      if !green.succeeded || !green.output.contains "correspondence=checked" then
        failures.modify
            (·.push s!"correspondence/{fixture}: expected checked PASS:\n{green.output}")
      withReplacedFile source negative do
        if let some failure := expectedFailure fixture (← gate)
            #["execution-trusted-boundary", "no kernel-checked unconditional correspondence proof"]
                then
          failures.modify (·.push failure)
      let restored ← gate
      if !restored.succeeded || !restored.output.contains "correspondence=checked" then
        failures.modify
            (·.push s!"correspondence/{fixture}: fresh restored control failed:\n{restored.output}")
  failures.get

/-- Public project-surface correspondence control, the exact conditional-premise
mutation, and a fresh restored control. Only the reference body changes: the
positive reference equals the replacement by reduction; the mutation removes
that equality and leaves only a theorem requiring False. -/
private unsafe def structuralCorrespondence (layout : SourceLayout) (repo copy : FilePath) : IO
    (Array String) := do
  let sources := copy / layout.relativeDir
  let failures ← IO.mkRef (#[] : Array String)
  let lakefile := copy / "lakefile.lean"
  let originalLakefile ← IO.FS.readFile lakefile
  let manifest := copy / "foundation_manifest.json"
  let originalManifest ← IO.FS.readFile manifest
  let checkedManifest := originalManifest.replace "\"surfaces\":["
    ("\"surfaces\":[{\"library\":\"CorrespondenceControl\",\"claim\":\"standard-logical\"," ++
      "\"execution\":\"checked\",\"rationale\":\"correspondence control\"},")
  if checkedManifest == originalManifest then
      return #["correspondence/control: manifest anchor missing"]
  let negative ← IO.FS.readFile
      ((repo / layout.relativeDir) / "Fixtures" / "Mutations" / "ConditionalCorrespondence.lean")
  let positive := negative.replace "def falseReference (n : Nat) : Nat := n\n"
    "def falseReference (n : Nat) : Nat := n + 1\n"
  if positive == negative then return #["correspondence/control: mutation anchor missing"]
  let source := sources / "CorrespondenceControl.lean"
  -- Boundary evidence text is printed only in verbose mode.
  let gate := runBinaryFrom repo copy "axiomGate" #["--verbose"]
  withReplacedFile lakefile (originalLakefile ++ "\nlean_lib CorrespondenceControl\n") do
    withReplacedFile manifest checkedManifest do
      withNewFile source positive do
        let green ← gate
        if !green.succeeded || !green.output.contains "kernel-defeq" then
          failures.modify
              (·.push s!"correspondence/control: expected checked PASS:\n{green.output}")
        withReplacedFile source negative do
          if let some failure := expectedFailure "conditional-correspondence" (← gate)
              #["execution-trusted-boundary", "falseReference",
                "no kernel-checked unconditional correspondence proof"] then
            failures.modify (·.push failure)
        let restored ← gate
        if !restored.succeeded || !restored.output.contains "kernel-defeq" then
          failures.modify
              (·.push s!"correspondence/restored: fresh control failed:\n{restored.output}")
  failures.get

/-- Flush phase boundaries so CI timestamps and elapsed times identify the
actual work, even when stdout is redirected. Timings are observations only. -/
private def timedPhase {α : Type} (label : String) (action : IO α) : IO α := do
  IO.println s!"phase {label}: start"
  (← IO.getStdout).flush
  let started ← IO.monoNanosNow
  try action finally
    IO.println s!"phase {label}: {((← IO.monoNanosNow) - started) / 1000000}ms"
    (← IO.getStdout).flush

/-- One cluster of controls: its own isolated project below `scratch`, prepared by `prepare`
and built, then the controls of `part` in it. A baseline that does not build is the cluster's
failure. -/
private def cluster (repo scratch : FilePath) (name : String) (prepare : FilePath → IO Unit)
    (targets : Array String) (part : FilePath → FilePath → IO (Array String)) :
    String × IO (Array String) :=
  (name, do
    let copy := scratch / s!"copy-{name}"
    let setup ← timedPhase s!"cluster {name} setup" do
      prepare copy
      runProcess copy "lake" (#["build"] ++ targets)
    if !setup.succeeded then
      return #[s!"structural/setup: copy-{name} baseline did not build:\n{setup.output}"]
    part repo copy)

/-- The application's library and claimed executables, as Lake targets. -/
private def applicationTargets (layout : SourceLayout) : Array String :=
  #[structuralApplication] ++ layout.project.executables

/-- A cluster whose project is the structural project (`prepareStructuralProject`). Its gates
only read the checker's output that the baseline build completed. -/
private def projectCluster (layout : SourceLayout) (repo scratch : FilePath) (name : String)
    (part : FilePath → FilePath → IO (Array String)) : String × IO (Array String) :=
  cluster repo scratch name (prepareStructuralProject layout repo)
    ((applicationTargets layout).push structuralFixture.toString) part

/-- Run the named items on `jobs` workers, each taking the next waiting item as soon as it is
free, and collect their failures. Every item prints its own elapsed time. -/
private def qualifyItems (label : String) (jobs : Nat)
    (items : Array (String × IO (Array String))) : IO (Array String) := do
  let results ← mapWorkQueue (max 1 jobs) items fun (name, run) =>
    timedPhase s!"{label} {name}" run
  return results.foldl (· ++ ·) #[]

/-- The structural mutation clusters, each in its own isolated project, so no two concurrent
Lake builds ever write one build directory, and each with its shard. Each cluster's project is
the structural project; the two self-hosted clusters' are copies of the repository, and they
are in different shards, each of whose gates builds and inspects `RegulaPolicy`. The longest
observed clusters are first. -/
private unsafe def structuralClusters (layout : SourceLayout) (repo scratch : FilePath) :
    List (Shard × String × IO (Array String)) :=
  [(.first, cluster repo scratch "self-hosted" (prepareSelfHosted repo)
      (applicationTargets layout) (structuralSelfHosted layout)),
    (.second, "self-hosted-positive",
      structuralSelfHostedPositive repo (scratch / "copy-self-hosted-positive")),
    (.first, projectCluster layout repo scratch "a" (structuralPartA layout)),
    (.second, projectCluster layout repo scratch "d" (structuralPartD layout)),
    (.second, projectCluster layout repo scratch "c" (structuralPartC layout)),
    (.first, projectCluster layout repo scratch "b" (structuralPartB layout))]

/-- Structural qualification: the mutation clusters (`structuralClusters`) on `jobs` workers. -/
private unsafe def structuralQualification (layout : SourceLayout) (repo scratch : FilePath)
    (jobs : Nat)
    : IO (Array String) :=
  qualifyItems "structural" jobs ((structuralClusters layout repo scratch).map (·.2)).toArray

/-- Execution qualification: the correspondence controls, in two clusters whose projects are
the structural project, and the compiler-path cases, each phase of each case in a scratch
project of its own below `scratch`. All run on `jobs` workers with no batch barrier between
them, the longest observed first. Each control has its shard: the two correspondence clusters
are in different shards, and the compiler-path cases alternate in their listed order. With
`shard`, only that shard's controls run. Returns the names of the controls run and their
failures. -/
private unsafe def executionQualification (layout : SourceLayout) (repo scratch : FilePath)
    (jobs : Nat) (shard : Option Shard := none) : IO (Array String × Array String) := do
  let compilerPaths := scratch / "compiler-paths"
  IO.FS.createDirAll compilerPaths
  let controls : List (Shard × String × IO (Array String)) :=
    [(Shard.second, projectCluster layout repo scratch "correspondence-restoration"
        (correspondenceRestoration layout)),
      (Shard.first, projectCluster layout repo scratch "correspondence"
        (structuralCorrespondence layout))] ++
    (CompilerPaths.qualifications repo compilerPaths).toList.mapIdx fun index (name, run) =>
      (if index % 2 == 0 then Shard.first else Shard.second, s!"compiler path {name}", run)
  let selected := ((inShard shard controls).map (·.2)).toArray
  return (selected.map (·.1), ← qualifyItems "execution" jobs selected)

/-- Two mutually independent modules, so the fresh control has two maximal roots. -/
private def freshControlStems : Array String := #["Left", "Right"]

/-- The fresh control claims only `FreshControl`; every repository library and
executable is excluded, so the classification stays complete as they change. -/
private def freshControlManifest (manifest : Manifest) : Json :=
  let excluded (kind : String) (names : Array String) := Json.arr <| names.map fun name =>
    Json.mkObj [(kind, .str name), ("rationale", .str "outside the fresh-checker control")]
  Json.mkObj [
    ("schema-version", (2 : Nat)),
    ("surfaces", Json.arr #[Json.mkObj [("library", .str "FreshControl"),
      ("claim", .str "kernel-only"), ("rationale", .str "clean-checkout freshChecker control")]]),
    ("excluded-libraries", excluded "library" <|
      manifest.surfaces.map (·.library) ++ manifest.excludedLibraries.map (·.library)),
    ("excluded-executables", excluded "executable" <|
      manifest.surfaces.flatMap (·.executables) ++ manifest.excludedExecutables.map (·.executable))]

/-- Clean-checkout environment controls: each public checker that builds
project-owned modules must itself build the claimed libraries when the main
build directory is empty, instead of relying on a prior `lake build`. Each
control starts from a copied repository with no `.lake/build` at all. -/
private unsafe def fenceEnvironmentQualification (layout : SourceLayout) (repo scratch : FilePath) :
    IO (Array String) := do
  let failures ← IO.mkRef (#[] : Array String)
  let runScrubbed (dir : FilePath) (name : String) (args : Array String) : IO ProcessResult := do
    runProcess dir (← toolPath repo name).toString args
      scrubbedLeanPathEnv
  let unbuilt (name : String) (action : FilePath → IO Unit) : IO Unit := do
    let dir := scratch / name
    IO.FS.createDirAll dir
    prepareScratchRepo repo dir
    if ← (dir / ".lake" / "build").pathExists then
      failures.modify (·.push s!"fence-env/{name}: setup unexpectedly has a build directory")
    action dir
  timedPhase "clean-checkout/doc-fences" <| unbuilt "doc-fences" fun dir => do
    let corpus := dir / "fence-corpus"
    IO.FS.createDirAll corpus
    IO.FS.writeFile (corpus / "owned-import.md")
      "```lean\nimport AuditApp.Limiter\n\ntheorem fence_uses_owned : 1 = 1 := rfl\n```\n"
    let result ← runScrubbed dir "docFenceAudit"
      #["--jobs", "4", "--docs-root", corpus.toString]
    if !result.succeeded || !result.output.contains "conforming-positive-pass=1/1" then
      failures.modify (·.push
        s!"fence-env/doc-fences: fence importing an owned module failed from unbuilt \
          state:\n{result.output}")
  timedPhase "clean-checkout/file-mode" <| unbuilt "file-mode" fun dir => do
    let result ← runScrubbed dir "axiomGate"
      #["--file",
          ((dir / layout.relativeDir) / "Fixtures" / "Positive" / "ExternalUse.lean").toString,
        "--claim", "standard-logical"]
    if !result.succeeded then
      failures.modify (·.push
        s!"fence-env/file-mode: --file importing the owned library failed from unbuilt \
          state:\n{result.output}")
  -- The driver's build and root selection depend only on the manifest and Lake's
  -- import graph, never on which declarations a module holds. So this control
  -- claims two import-free `prelude` modules instead of the repository surface:
  -- `leanchecker --fresh` on the real claimed graph replays Init, Lean and
  -- Mathlib once per root, which is the separate optional serialized-graph
  -- claim (`scripts/verify.sh serialized-graph`), not a clean-checkout property.
  timedPhase "clean-checkout/fresh-checker" <| unbuilt "fresh-checker" fun dir => do
    let sources := dir / layout.relativeDir
    let expected := freshControlStems.map (s!"FreshControl.{·}")
    IO.FS.createDirAll (sources / "FreshControl")
    for stem in freshControlStems do
      IO.FS.writeFile ((sources / "FreshControl") / s!"{stem}.lean")
        s!"prelude\n/-! Import-free clean-checkout freshChecker root. -/\n/-- A type with one \
          value. -/\ninductive FreshControl.{stem} : Type where\n  /-- Its one value. -/\n  | \
          unit\n"
    let lakefile := dir / "lakefile.lean"
    IO.FS.writeFile lakefile ((← IO.FS.readFile lakefile) ++
      "\nlean_lib FreshControl where\n  globs := #[.submodules `FreshControl]\n")
    let manifest := dir / "foundation_manifest.json"
    writeJson manifest (freshControlManifest (← parsedManifest manifest))
    let reportPath := dir / "fresh-report.json"
    let result ← runScrubbed dir "freshChecker" #["--json-out", reportPath.toString]
    if !result.succeeded then
      failures.modify (·.push
        s!"fence-env/fresh-checker: freshChecker failed from unbuilt state:\n{result.output}")
    else
      -- Reconcile the actual run against the modules written above: each is a
      -- maximal root, and every root's successful check must cover it.
      let report ← readJson reportPath
      let status ← IO.ofExcept <| report.getObjValAs? String "status"
      let modules ← jsonStringArray "fresh control modules" <| ← IO.ofExcept <|
        report.getObjVal? "modules"
      let roots ← jsonStringArray "fresh control roots" <| ← IO.ofExcept <|
        report.getObjVal? "roots"
      let checks ← IO.ofExcept <| report.getObjValAs? (Array Json) "checks"
      let mut checked : Array String := #[]
      for check in checks do
        let exitCode ← IO.ofExcept <| check.getObjValAs? Nat "exitCode"
        if exitCode != 0 then
          failures.modify (·.push "fence-env/fresh-checker: a root was not checked successfully")
        let covered ← jsonStringArray "fresh control coveredModules" <| ← IO.ofExcept <|
          check.getObjVal? "coveredModules"
        checked := checked ++ covered
      if status != "completed" || checks.size != expected.size
          || uniqueSorted modules != uniqueSorted expected || uniqueSorted roots !=
              uniqueSorted expected
          || uniqueSorted checked != uniqueSorted expected then
        failures.modify (·.push
          s!"fence-env/fresh-checker: accepted root checks did not cover \
            exactly {expected}:\n{result.output}")
  failures.get

private def adopterManifestText : String :=
  "{\"schema-version\":2,\"surfaces\":[{" ++
  "\"library\":\"Widget\",\"executables\":[\"widget_tool\"]," ++
  "\"claim\":\"choice-free\",\"rationale\":\"external adopter control\"}]," ++
  "\"excluded-libraries\":[],\"excluded-executables\":[]}"

private def adopterOmittedExeText : String :=
  "{\"schema-version\":2,\"surfaces\":[{" ++
  "\"library\":\"Widget\",\"claim\":\"choice-free\"," ++
  "\"rationale\":\"omitted executable control\"}]," ++
  "\"excluded-libraries\":[],\"excluded-executables\":[]}"

private def adopterTomlLakefile (checkerPath : String) : String :=
  "name = \"widget_adopter\"\n\n" ++
  "[leanOptions]\nautoImplicit = false\nrelaxedAutoImplicit = false\nlinter.missingDocs = \
    true\n\n" ++
  "[[require]]\nname = \"regula\"\n" ++
  s!"path = \"{checkerPath}\"\n\n" ++
  "[[lean_lib]]\nname = \"Widget\"\nglobs = [\"Widget\", \"Widget.+\"]\n\n" ++
  "[[lean_exe]]\nname = \"widget_tool\"\nroot = \"Main\"\n"

private def adopterLeanLakefile (checkerPath : String) : String :=
  "import Lake\nopen Lake DSL\n\n" ++
  "package «widget_adopter» where\n" ++
  "  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`linter.missingDocs, \
    true⟩]\n\n" ++
  s!"require «regula» from \"{checkerPath}\"\n\n" ++
  "@[default_target]\nlean_lib «Widget» where\n  globs := #[.andSubmodules `Widget]\n\n" ++
  "lean_exe «widget_tool» where\n  root := `Main\n"

/-- The adopting workspace inherits every transitive dependency through the
checker package's own `require`, pinned exactly as in this repository. -/
private def adopterLakeManifest (repo : FilePath) (checkerDir : String) : IO Json := do
  let base ← readJson (repo / "lake-manifest.json")
  let .arr packages ← IO.ofExcept (base.getObjVal? "packages")
    | throw <| IO.userError "adopter manifest setup: no packages array"
  let inherited := packages.map fun entry =>
    entry.setObjVal! "inherited" (Json.bool true)
  let pathEntry := Json.mkObj [
    ("name", Json.str "regula"),
    ("scope", Json.str ""),
    ("configFile", Json.str "lakefile.lean"),
    ("manifestFile", Json.str "lake-manifest.json"),
    ("inherited", Json.bool false),
    ("type", Json.str "path"),
    ("dir", Json.str checkerDir)
  ]
  return base.setObjVal! "packages" (Json.arr (#[pathEntry] ++ inherited))

/-- External adopter qualification: a scratch project that requires the
checker package by local path in each lakefile format, with one conforming
library, a standalone `Main` executable root, and empty exclusion arrays. The
scratch projects contain nothing named `Audit` or `Fixtures` and share only
the pinned dependency checkouts. The `relative` variant requires the checker
by a relative path (the form a project nested inside another repository
uses), which the §7.3 isolated copy must re-anchor to the original project;
its setup verifies that the relative path really names this repository. -/
private unsafe def adopterQualification (repo scratch : FilePath) : IO (Array String) := do
  let failures ← IO.mkRef (#[] : Array String)
  let depth := (← IO.FS.realPath scratch).components.length + 1 -
    (← IO.FS.realPath repo).components.length
  let variants : Array (String × String × String × (String → String)) := #[
    ("toml", "toml", repo.toString, adopterTomlLakefile),
    ("lean", "lean", repo.toString, adopterLeanLakefile),
    ("relative", "toml", "/".intercalate (List.replicate depth ".."), adopterTomlLakefile)
  ]
  for (label, format, checkerDir, lakefileText) in variants do
    let adopter := scratch / label
    IO.FS.createDirAll (adopter / "Widget")
    if !(FilePath.mk checkerDir).isAbsolute then
      let resolved ← IO.FS.realPath (adopter / checkerDir)
      if resolved != (← IO.FS.realPath repo) then
        throw <| IO.userError <|
          s!"adopter/{label}/setup: relative checker path {checkerDir} resolves to {resolved}, \
            not {repo}"
    let lakeManifest ← adopterLakeManifest repo checkerDir
    IO.FS.writeFile (adopter / s!"lakefile.{format}") (lakefileText checkerDir)
    IO.FS.writeBinFile (adopter / "lean-toolchain")
      (← IO.FS.readBinFile (repo / "lean-toolchain"))
    IO.FS.writeFile
        (adopter / "Widget.lean")
            "import Widget.Extra\n/-! Re-export the arithmetic identity in Widget.Extra. -/\n"
    IO.FS.writeFile (adopter / "Widget" / "Extra.lean")
      "/-! Closed natural-number arithmetic identity. -/\ntheorem widget_extra_thm : 1 + 1 = 2 := \
        rfl\n"
    IO.FS.writeFile (adopter / "Main.lean") "/-! Standalone no-effect IO entrypoint. -/\n/-- Does \
      nothing. -/\ndef main : IO Unit := pure ()\n"
    IO.FS.writeFile (adopter / "foundation_manifest.json") (adopterManifestText ++ "\n")
    writeJson (adopter / "lake-manifest.json") lakeManifest
    IO.FS.createDirAll (adopter / ".lake")
    let link ← runProcess adopter "ln" #["-s", (repo / ".lake" / "packages").toString,
      (adopter / ".lake" / "packages").toString]
    if !link.succeeded then
      throw <| IO.userError s!"could not link pinned Lake packages: {link.output}"
    let gate (args : Array String := #[]) :=
      runBinaryFrom repo adopter "axiomGate" args
    let positive ← gate #["--verbose"]
    if !positive.succeeded then
      failures.modify (·.push
        s!"adopter/{label}/positive: fresh gate failed:\n{positive.output}")
    else
      for needle in #["module Widget.Extra", "module Main", "widget_extra_thm",
          "-> kernel-only", "claimed profile for Widget: choice-free"] do
        if !positive.output.contains needle then
          failures.modify (·.push
            s!"adopter/{label}/positive: missing classification {repr needle}:\n{positive.output}")
    let viaProject ← runBinary repo "axiomGate" #["--project", adopter.toString]
    if !viaProject.succeeded then
      failures.modify (·.push
        s!"adopter/{label}/project-flag: gate from foreign cwd failed:\n{viaProject.output}")
    let omittedManifest := adopter / "omitted-exe.json"
    IO.FS.writeFile omittedManifest (adopterOmittedExeText ++ "\n")
    if let some failure := expectedFailure s!"adopter/{label}/omitted-exe"
        (← gate #["--manifest", omittedManifest.toString, "--incremental"])
        #["manifest-incomplete", "widget_tool"] then
      failures.modify (·.push failure)
    withNewFile (adopter / "Widget" / "Rogue.lean")
        "/-! Discovery control for a glob-owned axiom. -/\n/-- A glob-owned axiom, which RG1001 \
          rejects. -/\naxiom widget_rogue_axiom : False\n" do
      if let some failure := expectedFailure s!"adopter/{label}/rogue-module" (← gate)
          #["project-axiom", "widget_rogue_axiom"] then
        failures.modify (·.push failure)
    if label == "toml" then
      let originalExtra ← IO.FS.readFile (adopter / "Widget" / "Extra.lean")
      let unlistedSource := adopter / "WidgetRogue.lean"
      IO.FS.writeFile unlistedSource "axiom widget_unlisted_axiom : False\n"
      let outDir := adopter / ".lake" / "build" / "lib" / "lean"
      IO.FS.createDirAll outDir
      let compiled ← runProcess adopter "lake" #["env", "lean", "-o",
        (outDir / "WidgetRogue.olean").toString, unlistedSource.toString]
      if !compiled.succeeded then
        failures.modify (·.push s!"adopter/toml/unlisted-setup: {compiled.output}")
      else
        withReplacedFile (adopter / "Widget" / "Extra.lean")
            ("import WidgetRogue\n" ++ originalExtra) do
          if let some failure := expectedFailure "adopter/toml/unlisted-module"
              (← gate #["--incremental"])
              #["unexpected-project-module", "WidgetRogue"] then
            failures.modify (·.push failure)
      let fresh ← runBinaryFrom repo adopter "freshChecker" #["--plan-only"]
      if !fresh.succeeded || !fresh.output.contains "Widget" || !fresh.output.contains "Main" then
        failures.modify (·.push
          s!"adopter/toml/fresh-plan: exact adopter coverage plan failed:\n{fresh.output}")
  failures.get

/-- In-process fixture, scanner, and fence-corpus controls. Imports
remain serialized, and transcript workers finish before parent imports. -/
private unsafe def runFixtures (repo : FilePath) (jobs : Nat)
    (fixtures : Array FixtureSpec) (failures : IO.Ref (Array String)) : IO Unit := do
  let inventory ← Lake.surfaceInventory repo
  withScratch repo "checker-fixtures" fun scratch => do
    let fixtureResults ← timedPhase "in-process fixtures" <|
      fixtureVerdicts repo scratch jobs fixtures inventory.leanPath
    for result in fixtureResults do appendFailure failures result
    IO.println (s!"self-test fixtures: " ++
      (if fixtureResults.all (·.isNone) then "PASS" else "FAIL") ++
      s!" ({fixtures.size} in one process, one environment load per import closure)")
  for failure in scannerQualification do failures.modify (·.push failure)
  withScratch repo "checker-fence-corpus" fun scratch => do
    let corpus ← timedPhase "in-process fence corpus" <|
      fenceCorpusQualification repo scratch jobs
    for failure in corpus do failures.modify (·.push failure)
    IO.println <| "self-test Markdown: " ++
      (if corpus.isEmpty then "PASS" else "FAIL") ++
      s!" (scanner controls + {(fenceCorpusCases repo).size} in-process corpus cases)"

/-- External-boundary control for the frozen `.olean` parts that admission reuse rests on, where
reading the files is the external mechanism (`Admission.reuseJustified_frozen`,
`Admission.replayed_of_changed` and `Admission.replayed_of_changed_import` state the decision
over the readings). It reads through the coordinator's own path (`Inspection.readings`, then
`Admission.currentOffers`) with one completed admission that replayed the module. For a module
with all three parts and for one with only its `.olean`, the admission is offered while nothing
changes, is not offered when a byte of the `.olean`, `.olean.server` or `.olean.private` changes
at the same size, when such a part is removed and when an absent part appears, and is offered
again once the part is restored; `Inspection.changedArtifact?` reports the same changes. -/
private def frozenArtifactControls (scratch : FilePath) : IO (Array String) := do
  let olean := scratch / "Frozen.olean"
  let levels := #[(Lean.OLeanLevel.exported, ".olean"), (.server, ".olean.server"),
    (.private, ".olean.private")]
  let frozenBytes := ByteArray.mk #[1, 2, 3]
  let mut failures := #[]
  for (layout, present) in #[("three parts", #[true, true, true]),
      ("one part", #[true, false, false])] do
    for ((level, _), isPresent) in levels.zip present do
      let part := level.adjustFileName olean
      if isPresent then IO.FS.writeBinFile part frozenBytes
      else if ← part.pathExists then IO.FS.removeFile part
    let some artifact ← Inspection.freezeArtifact `Frozen olean
      | failures := failures.push s!"frozen-artifact/{layout}: the artifact was not frozen"
        continue
    -- A completed admission that replayed the module, loaded from the frozen path.
    let completed : Admission.Completed := {
      receipt := { modules := #[`Frozen], required := #[(`Frozen, `frozenFact)],
                   admitted := #[(`Frozen, `frozenFact)], reused := #[], shared := #[] }
      origins := #[{ name := `Frozen, olean := artifact.canonical, imports := #[] }] }
    let offered : IO Bool := do
      let offers := Admission.currentOffers (NameSet.empty.insert `Frozen)
        (← Inspection.readings #[artifact]) #[completed]
      return offers.any (·.modules.contains `Frozen)
    let reportedChanged : IO Bool := do
      return !(← offered) && (← Inspection.changedArtifact? #[artifact]) == some `Frozen
    let reportedUnchanged : IO Bool := do
      return (← offered) && (← Inspection.changedArtifact? #[artifact]).isNone
    unless ← reportedUnchanged do
      failures := failures.push s!"frozen-artifact/{layout}: not offered while unchanged"
    for ((level, extension), isPresent) in levels.zip present do
      let part := level.adjustFileName olean
      let restore : IO Unit :=
        if isPresent then IO.FS.writeBinFile part frozenBytes else IO.FS.removeFile part
      let mutations : Array (String × IO Unit) :=
        if isPresent then #[("changed", IO.FS.writeBinFile part (ByteArray.mk #[1, 2, 4])),
          ("removed", IO.FS.removeFile part)]
        else #[("added", IO.FS.writeBinFile part frozenBytes)]
      for (mutation, mutate) in mutations do
        mutate
        unless ← reportedChanged do
          failures := failures.push
            s!"frozen-artifact/{layout}: still offered with a {mutation} {extension}"
        restore
        unless ← reportedUnchanged do
          failures := failures.push
            s!"frozen-artifact/{layout}: not offered again with the {extension} restored"
  return failures

/-- External-boundary control for claimed libraries that import one another, where the report
workers, Lean's import and the kernel are the external mechanism
(`Admission.reuseJustified_admitted` and `Admission.replayed_of_loaded` state the coordinator's
decision). `Left.Top` imports `Right.Base` and `Right.Top` imports `Left.Base`: the modules form
no cycle, the two libraries do, so the first library's environment loads a module of the second
before the second's own environment does. The fresh audit must accept; the first environment
replays `Right.Base`; the second reuses it, though it is one of its own requested modules, and
still requires its declaration's key; so each of the four modules is replayed in exactly one
environment. -/
private def libraryCycleControl (repo : FilePath) : IO (Array String) :=
  withScratch repo "library-cycle-control" fun project =>
    withScratch repo "library-cycle-result" fun output => do
  IO.FS.writeFile (project / "lean-toolchain") (← IO.FS.readFile (repo / "lean-toolchain"))
  IO.FS.writeFile (project / "lakefile.toml") <|
    "name = \"library_cycle_control\"\n[leanOptions]\nautoImplicit = false\n" ++
      "relaxedAutoImplicit = false\nlinter.missingDocs = true\n" ++
      "[[lean_lib]]\nname = \"Left\"\nglobs = [\"Left.+\"]\n" ++
      "[[lean_lib]]\nname = \"Right\"\nglobs = [\"Right.+\"]\n"
  let surface (library : String) : String :=
    "{\"library\":\"" ++ library ++ "\",\"executables\":[],\"claim\":\"standard-logical\"," ++
      "\"execution\":\"report\",\"rationale\":\"Library cycle control\"}"
  IO.FS.writeFile (Manifest.defaultPath project) <|
    "{\"schema-version\":2,\"surfaces\":[" ++ surface "Left" ++ "," ++ surface "Right" ++
      "],\"excluded-libraries\":[],\"excluded-executables\":[]}"
  for (library, other, fact, otherFact) in #[("Left", "Right", "left", "right"),
      ("Right", "Left", "right", "left")] do
    IO.FS.createDirAll (project / library)
    IO.FS.writeFile (project / library / "Base.lean") <|
      s!"/-! The base module of the {library} library. -/\n\n" ++
        s!"theorem {fact}Base : True := True.intro\n"
    IO.FS.writeFile (project / library / "Top.lean") <|
      s!"import {other}.Base\n\n/-! Uses the base module of the {other} library. -/\n\n" ++
        s!"theorem {fact}Top : True := {otherFact}Base\n"
  -- Lake writes the lock manifest of this package without dependencies; without one the fresh
  -- copy's build would create it, a configuration change during the audit.
  let locked ← runProcess project "lake" #["update"] scrubbedLeanPathEnv
  unless locked.succeeded do return #[s!"library-cycle/setup: lake update failed:\n{locked.output}"]
  let result := output / "result.json"
  let gate ← runProcess project (← toolPath repo "axiomGate").toString
    #["--project", project.toString, "--json-out", result.toString] scrubbedLeanPathEnv
  unless gate.succeeded do return #[s!"library-cycle/accepted: expected PASS:\n{gate.output}"]
  let modules := #["Left.Base", "Left.Top", "Right.Base", "Right.Top"]
  let json ← CompilerMode.readObservation (← IO.ofExcept (Json.parse (← IO.FS.readFile result)))
  let surfaces ← IO.ofExcept <|
    (json.getObjVal? "scope").bind (·.getObjValAs? (Array Json) "surfaces")
  let mut found : Array (String × Array String × Array String × Array (String × String)) := #[]
  for surface in surfaces do
    let library ← IO.ofExcept <| surface.getObjValAs? String "library"
    let admission ← IO.ofExcept <|
      (surface.getObjVal? "report").bind (·.getObjVal? "admission")
    let reused ← IO.ofExcept <| admission.getObjValAs? (Array String) "reused"
    let required ← IO.ofExcept <| admission.getObjValAs? (Array (String × String)) "required"
    let replayed := modules.filter fun m => !reused.contains m && required.any (·.1 == m)
    found := found.push (library, replayed, modules.filter reused.contains, required)
  let expected : Array (String × Array String × Array String) := #[
    ("Left", #["Left.Base", "Left.Top", "Right.Base"], #[]),
    ("Right", #["Right.Top"], #["Left.Base", "Right.Base"])]
  let mut failures := #[]
  unless found.map (fun (library, replayed, reused, _) => (library, replayed, reused)) ==
      expected do
    failures := failures.push s!"library-cycle/replayed-once: expected {expected}, found \
      {found.map fun (library, replayed, reused, _) => (library, replayed, reused)}"
  unless found.any (fun (library, _, _, required) =>
      library == "Right" && required.contains ("Right.Base", "rightBase")) do
    failures := failures.push "library-cycle/reused-key: the Right environment does not require \
      the key of its reused module Right.Base"
  return failures

/-- The groups of controls the structural partition reports separately. -/
private inductive StructuralGroup where
  | frozen
  | clusters
  | cycle
  | manifest
  deriving BEq

/-- What a sharded run printed in place of the description of every control of its group: the
controls it ran, which are not all of the group's. -/
private def shardDescription (shard : Shard) (names : Array String) : String :=
  s!" (shard {shard.label}: {", ".intercalate names.toList}; the other shard runs the rest)"

/-- Structural mutations and manifest controls retain their isolated projects, worker joins,
and complete failure accumulation. The frozen-artifact controls, the mutation clusters, the
library cycle control and the manifest controls share one queue of `jobs` workers, so no more
than `jobs` of them run at once. The two short controls wait behind the clusters and take the
workers the first clusters free, instead of competing with the first clusters for the
processors. Each control has its shard; with `shard`, only that shard's controls run, and only
the groups it ran report. -/
private unsafe def runStructural (layout : SourceLayout) (repo : FilePath) (jobs : Nat)
    (shard : Option Shard) (failures : IO.Ref (Array String)) : IO Unit := do
  -- Every result carries its group, so none is found by its position in the queue.
  let results ← timedPhase "structural controls" <|
    withScratch repo "checker-structural" fun scratch =>
      withScratch repo "checker-manifest" fun manifests => do
        let controls : List (Shard × StructuralGroup × String × IO (Array String)) :=
          [(Shard.first, StructuralGroup.frozen, "frozen artifact controls",
              withScratch repo "checker-frozen-artifacts" frozenArtifactControls)] ++
          (structuralClusters layout repo scratch).map (fun (assigned, name, run) =>
            (assigned, StructuralGroup.clusters, s!"structural {name}", run)) ++
          [(Shard.second, StructuralGroup.cycle, "library cycle control", libraryCycleControl repo),
            (Shard.second, StructuralGroup.manifest, "manifest controls",
              manifestQualification repo manifests)]
        mapWorkQueue (max 1 jobs) ((inShard shard controls).map (·.2)).toArray
          fun (group, label, run) => do return (group, label, ← timedPhase label run)
  let ran (group : StructuralGroup) : Bool := results.any (·.1 == group)
  let failuresOf (group : StructuralGroup) : Array String :=
    (results.filter (·.1 == group)).foldl (· ++ ·.2.2) #[]
  let verdict (group : StructuralGroup) : String :=
    if (failuresOf group).isEmpty then "PASS" else "FAIL"
  for (_, _, found) in results do
    for failure in found do failures.modify (·.push failure)
  if ran .frozen then
    IO.println <| "self-test frozen artifacts: " ++ verdict .frozen ++
      " (an admission is offered over an unchanged artifact and not over a changed, removed or \
        added .olean, .olean.server or .olean.private; restored parts are offered again)"
  if ran .manifest then
    IO.println "self-test manifest: completed (valid in-process; missing, malformed, \
      incomplete, wrong-version, unknown-key, bad-execution and unknown-library public cases)"
  if ran .clusters then
    IO.println <| "self-test structural: " ++ verdict .clusters ++ match shard with
      | none =>
        " (discovery, warning, contamination, exact ownership, unlisted root module, " ++
        "library and exe classification, claimed exe root, exe contamination, app exe omission, " ++
        "app missing/trivial/weakened update evidence, missing proof field, weakened admission, " ++
        "fresh coverage, realized and unchecked duplicate copies, restore; " ++
        "isolated projects, bounded parallelism)"
      | some selected => shardDescription selected
          ((results.filter (·.1 == StructuralGroup.clusters)).map (·.2.1))
  if ran .cycle then
    IO.println <| "self-test library cycle: " ++ verdict .cycle ++
      " (two claimed libraries that import one another: accepted, each module replayed in one \
        environment, a requested module reused with its keys)"

/-- Execution-evidence controls: the correspondence controls and every compiler-path case,
each with its positive, mutation and fresh restoration in an isolated project. With `shard`,
only that shard's controls run and are named. -/
private unsafe def runExecution (layout : SourceLayout) (repo : FilePath) (jobs : Nat)
    (shard : Option Shard) (failures : IO.Ref (Array String)) : IO Unit := do
  let (names, execution) ← timedPhase "execution controls" <|
    withScratch repo "checker-execution" fun scratch =>
      executionQualification layout repo scratch jobs shard
  for failure in execution do failures.modify (·.push failure)
  IO.println <| "self-test execution: " ++
    (if execution.isEmpty then "PASS" else "FAIL") ++ match shard with
    | none =>
      s!" ({CompilerPaths.caseCount} compiler-path cases, conditional correspondence, " ++
      "restricted-domain and universe correspondence restorations; positive, mutation and " ++
      "fresh restoration each; isolated projects, bounded parallelism)"
    | some selected => shardDescription selected names

/-- Public CLI fixtures: the complete sweep for qualification, or the unchanged
smoke subset for the default development tier. -/
private def runCli (repo : FilePath) (jobs : Nat) (fullCli : Bool)
    (fixtures : Array FixtureSpec) (failures : IO.Ref (Array String)) : IO Unit := do
  let smokeFixtures := fixtures.filter (smokeFixtureNames.contains ·.moduleName)
  if smokeFixtures.size != smokeFixtureNames.size then
    failures.modify (·.push "smoke: expected smoke fixtures are missing from the manifest")
  -- The build-bound sweep contains every smoke control; each runs once.
  let cliFixtures := if fullCli then fixtures else smokeFixtures
  let cliLabel := if fullCli then "full CLI sweep" else "CLI smoke"
  let cliResults ← timedPhase cliLabel <|
    mapConcurrent jobs cliFixtures (checkFixtureCli repo)
  for result in cliResults do appendFailure failures result
  IO.println <| s!"self-test {cliLabel}: " ++
    (if cliResults.all (·.isNone) then "PASS" else "FAIL") ++
    s!" ({cliFixtures.size} real axiomGate --file invocations)"
  if fullCli then
    let attribution ← timedPhase "source attribution" <|
      withScratch repo "checker-source-attribution" fun scratch =>
        sourceAttributionControls scratch (runBinary repo "axiomGate" ·)
    for failure in attribution do failures.modify (·.push failure)
    IO.println <| "self-test source attribution: " ++
      (if attribution.isEmpty then "PASS" else "FAIL") ++
      " (a declaration of every generated family attributed, those at one location printed in one \
        block; a metaprogram theorem, a user-written ofNat and an elaborator under a structure's \
        name, and user-written theorems named like auxiliary proofs, not attributed)"

/-- Build-bound packaging and fresh-state controls, each retaining its isolated
source/build directory and exact failure accumulation. -/
private unsafe def runEnvironments (layout : SourceLayout) (repo : FilePath)
    (failures : IO.Ref (Array String)) : IO Unit := do
  -- This tier only starts after the earlier subprocess tasks have joined.
  -- Its builds live in isolated copies; the other public controls cannot
  -- consume or alter those owned outputs.
  let fenceEnvTask ← IO.asTask (prio := .dedicated) do
    timedPhase "clean-checkout environments" <|
      withScratch repo "checker-fence-env" fun scratch =>
        fenceEnvironmentQualification layout repo scratch
  withScratch repo "checker-scanner" fun scratch => do
    for failure in ← timedPhase "public fence corpus" (publicScannerQualification repo scratch) do
      failures.modify (·.push failure)
  IO.println s!"self-test public fence corpus: completed \
    ({(fenceCorpusCases repo ++ publicOnlyFenceCases).size} end-to-end cases)"
  withScratch repo "checker-adopter" fun scratch => do
    let adopter ← timedPhase "external adopters" (adopterQualification repo scratch)
    for failure in adopter do failures.modify (·.push failure)
    IO.println <| "self-test external adopters: " ++
      (if adopter.isEmpty then "PASS" else "FAIL") ++
      " (lakefile.toml + lakefile.lean + relative-path require: empty exclusions, fresh positive \
        gate, --project, omitted exe, " ++
      "rogue module, unlisted-module contamination, fresh plan)"
  let fenceEnv ← IO.ofExcept (← IO.wait fenceEnvTask)
  for failure in fenceEnv do failures.modify (·.push failure)
  IO.println <| "self-test fence environment: " ++
    (if fenceEnv.isEmpty then "PASS" else "FAIL") ++
    " (clean-checkout doc fences, --file, freshChecker with no prior build on a two-root control \
      surface)"
  let surface ← timedPhase "public surface" <| runBinary repo "axiomGate" #["--incremental"]
  if !surface.succeeded then
    failures.modify (·.push s!"surface/baseline: public incremental gate failed:\n{surface.output}")
  IO.println "self-test public controls: completed (surface)"

/-- Ordinary-build controls are a separate required partition so they do not
share the clean-checkout environment controls' CI time budget. -/
private def runBuildPolicy (repo : FilePath) (jobs : Nat)
    (failures : IO.Ref (Array String)) : IO Unit := do
  withScratch repo "checker-build-lint" fun scratch => do
    let buildLint ← timedPhase "ordinary-build policy controls" <|
      BuildLintQualification.qualify repo scratch jobs
    for failure in buildLint do failures.modify (·.push failure)
    IO.println <| "self-test build policy linter: " ++
      (if buildLint.isEmpty then "PASS" else "FAIL")

/-- `lake lint` driver controls: Lake dispatch in both lakefile formats and exit classes.
The shared audit body's detectors are qualified by the build-policy partition. -/
private def runLintDriver (repo : FilePath) (jobs : Nat)
    (failures : IO.Ref (Array String)) : IO Unit := do
  withScratch repo "checker-lake-lint" fun scratch => do
    let lint ← timedPhase "lake lint driver controls" <|
      LintQualification.qualify repo scratch jobs
    for failure in lint do failures.modify (·.push failure)
    IO.println <| "self-test lake lint driver: " ++ (if lint.isEmpty then "PASS" else "FAIL")

/-- Full and selected runs use the same group implementations. This exhaustive
match assigns each supported partition exactly one implementation. `fullCli` selects the
complete CLI sweep of the build-bound tier instead of the default tier's smoke subset, and
`shard` one shard of the structural or execution partition (`parseArgs` admits it with no
other). -/
private unsafe def runPartition (layout : SourceLayout) (partition : Partition) (repo : FilePath)
    (jobs : Nat) (fullCli : Bool) (shard : Option Shard)
    (fixtures : Array FixtureSpec) (failures : IO.Ref (Array String)) : IO Unit :=
  match partition with
  | .fixtures => runFixtures repo jobs fixtures failures
  | .structural => runStructural layout repo jobs shard failures
  | .execution => runExecution layout repo jobs shard failures
  | .cli => runCli repo jobs fullCli fixtures failures
  | .environments => runEnvironments layout repo failures
  | .buildPolicy => runBuildPolicy repo jobs failures
  | .lintDriver => runLintDriver repo jobs failures

/-- The combined public command must preserve Markdown discovery even in
subdirectories pruned by the generic project copier. Exercise a fresh positive,
a single invalid fence, and its restored positive in an isolated tiny project. -/
private def combinedSnapshotQualification (repo : FilePath) : IO (Array String) :=
  withScratch repo "combined-snapshot-control" fun project => do
    IO.FS.writeFile (project / "lean-toolchain") (← IO.FS.readFile (repo / "lean-toolchain"))
    IO.FS.writeFile (project / "lakefile.toml") <|
      "name = \"snapshot_control\"\n[leanOptions]\nautoImplicit = false\n" ++
        "relaxedAutoImplicit = false\nlinter.missingDocs = true\n[[lean_lib]]\nname = \
          \"Snapshot\"\n" ++
        "[[lean_lib]]\nname = \"Companion\"\n"
    IO.FS.writeFile (Manifest.defaultPath project)
      "{\"schema-version\":2,\"surfaces\":[{\"library\":\"Snapshot\",\"executables\":[],\"claim\":\
        \"standard-logical\",\"execution\":\"report\",\"rationale\":\"Control\"},{\"library\":\"Com\
        panion\",\"executables\":[],\"claim\":\"standard-logical\",\"execution\":\"report\",\"ratio\
        nale\":\"Parallel surface \
        control\"}],\"excluded-libraries\":[],\"excluded-executables\":[]}"
    let docs := project / "docs" / ".cache"
    IO.FS.createDirAll docs
    let mut failures := #[]
    for phase in
        #["baseline", "invalid", "restored", "invalid-source", "invalid-companion",
            "source-restored"] do
      IO.FS.writeFile (project / "Snapshot.lean") <|
        "/-! Source used for fence-import isolation qualification. -/\n" ++
        (if phase == "invalid-source" then "axiom unproved : True\n"
        else "theorem snapshot_ok : True := True.intro\n")
      IO.FS.writeFile (project / "Companion.lean") <|
        "/-! Companion surface for fence-import isolation qualification. -/\n" ++
        (if phase == "invalid-companion" then "axiom companion_unproved : True\n"
        else "theorem companion_ok : True := True.intro\n")
      let body := if phase == "invalid" then "def docWitness : Nat := \"bad\""
        else "theorem docWitness : True := True.intro"
      IO.FS.writeFile (docs / "sentinel.md") s!"```lean\n{body}\n```\n"
      let result ← runProcess project (← toolPath repo "axiomGate").toString
        #["--project", project.toString, "--with-docs", "--verbose"] scrubbedLeanPathEnv
      let accepted := if phase == "invalid" then
          !result.succeeded && result.output.contains "[X] .cache/sentinel.md:"
            && result.output.contains "Type mismatch"
        else if phase == "invalid-source" || phase == "invalid-companion" then
          !result.succeeded && result.output.contains "project-axiom"
            && !(result.output.contains "fence compilation: start")
        else result.succeeded && result.output.contains "conforming-positive-pass=1/1"
      if !accepted then failures := failures.push s!"combined snapshot/{phase}: {result.output}"
    return failures

/-- Distinguish the canonical force-loaded collector from a real import of an
excluded root-library module, through the public fresh project entry point. -/
private def forcedCollectorQualification (repo scratch : FilePath) : IO (Array String) := do
  let layout ← loadSourceLayout repo
  prepareScratchRepo repo scratch
  -- Retain the complete original manifest, including pure-policy dependencies.
  -- Excluding them would reject the positive for an unrelated import reason.
  let root := scratch / layout.relativeDir / "AuditApp.lean"
  let source ← IO.FS.readFile root
  let invoke := runBinaryFrom repo scratch "axiomGate" #[]
  let positive ← invoke
  unless positive.succeeded do return #[s!"forced-collector-positive: {positive.output}"]
  IO.FS.writeFile root ("import Regula.Collect\n" ++ source)
  let negative ← invoke
  IO.FS.writeFile root source
  let restored ← invoke
  let mut failures := #[]
  if let some failure := expectedFailure "source-imported-excluded-collector" negative
      #["unexpected-project-module", "excluded module Regula.Collect"] then
    failures := failures.push failure
  unless restored.succeeded do failures :=
                                failures.push s!"forced-collector-restored: {restored.output}"
  return failures

/-- Runs the qualification suite: one of the focused `--…-only` controls or the internal
transcript worker when the arguments name it, otherwise the baseline build and then the
selected tiers or partition. Prints each failure and returns `1` when any control fails, `0`
otherwise. -/
unsafe def run (args : List String) : IO UInt32 := do
  if args == ["--forced-collector-only"] then
    let repo ← repoRoot
    let build ← runProcess repo "lake" #["build", "axiomGate"]
    if !build.succeeded then IO.println build.output; return 1
    let failures ← withScratch repo "forced-collector-control" (forcedCollectorQualification repo)
    for failure in failures do IO.println s!"FAIL: {failure}"
    if failures.isEmpty then
        IO.println "forced collector qualification: PASS (fresh positive, excluded-source refusal, \
          restored)"
    return if failures.isEmpty then 0 else 1
  if args == ["--policy-transport-only"] then
    let failures := PolicyQualification.transport
    for failure in failures do IO.println s!"FAIL: {failure}"
    if failures.isEmpty then IO.println "policy transport qualification: PASS"
    return if failures.isEmpty then 0 else 1
  if args == ["--native-adopter-only"] then
    let repo ← repoRoot
    let build ← runProcess repo "lake" #["build", "axiomGate", "Regula.Linter"]
    if !build.succeeded then IO.println build.output; return 1
    let failures ← withScratch repo "native-adopter-control" (PolicyQualification.nativeImport repo)
    for failure in failures do IO.println s!"FAIL: {failure}"
    return if failures.isEmpty then 0 else 1
  if args == ["--policy-domain-only"] then
    let repo ← repoRoot
    let build ← runProcess repo "lake" #["build", "axiomGate"]
    if !build.succeeded then IO.println build.output; return 1
    let failures ← withScratch repo "policy-domain-controls" fun scratch => do
      return PolicyQualification.transport ++ (← PolicyQualification.publicPaths repo scratch)
    for failure in failures do IO.println s!"FAIL: {failure}"
    if failures.isEmpty then
        IO.println "policy domain qualification: PASS (transport and public paths)"
    return if failures.isEmpty then 0 else 1
  if args == ["--combined-snapshot-only"] then
    let failures ← combinedSnapshotQualification (← repoRoot)
    for failure in failures do IO.println s!"FAIL: {failure}"
    if failures.isEmpty then IO.println "combined snapshot qualification: PASS"
    return if failures.isEmpty then 0 else 1
  if args == ["--fences-only"] then
    let repo ← repoRoot
    let inProcess ← withScratch repo "checker-focused-fences" fun scratch =>
      fenceCorpusQualification repo scratch 4
    let publicCases ← withScratch repo "checker-focused-public-fences" fun scratch =>
      publicScannerQualification repo scratch
    let failures := inProcess ++ publicCases ++ (← combinedSnapshotQualification repo)
    for failure in failures do IO.println s!"FAIL: {failure}"
    if failures.isEmpty then
      IO.println "focused fence qualification: PASS (in-process, import setup/restoration, public \
        corpus; not full qualification)"
    return if failures.isEmpty then 0 else 1
  if args == ["--build-lint-only"] then
    let repo ← repoRoot
    let build ← runProcess repo "lake" #["build", "axiomGate"]
    if !build.succeeded then IO.println build.output; return 1
    return ← withScratch repo "build-lint-controls" fun scratch => do
      let failures ← BuildLintQualification.qualify repo scratch 4
      for failure in failures do IO.println s!"FAIL: {failure}"
      if failures.isEmpty then IO.println "build policy linter qualification: PASS"
      return if failures.isEmpty then 0 else 1
  if args == ["--compiler-paths-only"] then
    let repo ← repoRoot
    let build ← runProcess repo "lake" #["build", "axiomGate"]
    if !build.succeeded then IO.println build.output; return 1
    return ← withScratch repo "compiler-path-controls" fun scratch => do
      let failures ← CompilerPaths.qualify repo scratch
      for failure in failures do IO.println s!"FAIL: {failure}"
      return if failures.isEmpty then 0 else 1
  -- Internal transcript worker: one isolated fresh-frontend re-elaboration
  -- with the checker's own pinned frontend, serialized as JSON. The batched
  -- fixture pipeline spawns these so every transcript is built in exactly the
  -- isolated process environment the public CLI provides (a fresh process can
  -- never see the harness's imported attribute state), before the parent
  -- shared environment load.
  if let ["--transcript-worker", moduleWire, source, out] := args then
    let moduleName ← IO.ofExcept <| Regula.RegistryCodec.parseName
        (← IO.ofExcept <| Regula.Checker.PolicyCodec.parse moduleWire)
    let transcript ← Frontend.buildCurrentSearchPath moduleName source
    writeJson out
        (workerPacket (sourceWorkerRequest "transcript" moduleName source transcript.sourceContent)
            (toJson transcript))
    return 0
  let options ← parseArgs args {}
  if options.help then IO.println usage; return 0
  if options.jobs == 0 then throw <| IO.userError "--jobs must be positive"
  let repo ← repoRoot
  let started ← IO.monoNanosNow
  let failures ← IO.mkRef (#[] : Array String)
  -- The partitions this run executes: the selected one, both of `--structural-only`, every one
  -- in the build-bound tier, and the default tier's four otherwise.
  let selected : List Partition :=
    if options.structuralOnly then [.structural, .execution]
    else match options.partition with
      | some partition => [partition]
      | none => if options.buildBound then Partition.all
          else [.fixtures, .structural, .execution, .cli]
  -- One baseline build pays the prefix of the selected partitions once (`baselineOf`):
  -- the checker executables their controls run and, where one of them reads it, the fixture
  -- import anchor, the fixture modules other fixtures import and the claimed positive surface, so
  -- every later phase sees it built.
  let surfaceManifest ← parsedManifest (Manifest.defaultPath repo)
  let baselines := selected.map (baselineOf · options.shard)
  let tools := baselineTools baselines
  let fixtureTargets ← if baselines.any (·.surface) then
      pure (((← importedFixtures repo).filter (· != structuralFixture)).push structuralFixture)
    else pure #[]
  let build ← timedPhase "baseline build" <| runProcess repo "lake"
    (#["build"] ++ tools.toArray ++
      (if baselines.any (·.surface) then
        fixtureTargets.map (·.toString) ++ Manifest.positiveTargets surfaceManifest
      else #[]))
  if !build.succeeded then
    IO.println s!"FAIL: baseline checker and claimed-surface build failed:\n{build.output}"
    return 1
  builtTools.set (some tools)
  let layout ← loadSourceLayout repo
  if options.structuralOnly then
    return ← withScratch repo "checker-structural" fun scratch => do
      let structural := (← structuralQualification layout repo scratch options.jobs) ++
        (← executionQualification layout repo scratch options.jobs).2
      if structural.isEmpty then
        IO.println s!"checker structural self-test: PASS (including {CompilerPaths.caseCount} \
          compiler-path mutations with fresh restorations)"
        return 0
      IO.println s!"FAIL: {structural.size} structural qualification failure(s)"
      for failure in structural do IO.println s!"\n{failure}"
      return 1
  let fixtures ← loadFixtureManifest layout repo
  -- The same partitions the baseline was built for; only the build-bound tier runs the complete
  -- CLI sweep.
  for partition in selected do
    runPartition layout partition repo options.jobs options.buildBound options.shard fixtures
      failures
  let failures ← failures.get
  if !failures.isEmpty then
    IO.println s!"FAIL: {failures.size} checker qualification failure(s)"
    for failure in failures do IO.println s!"\n{failure}"
    return 1
  let elapsed := (← IO.monoNanosNow) - started
  if let some partition := options.partition then
    IO.println <| match options.shard with
      | none => s!"checker self-test partition {partition.label}: PASS \
          ({elapsed / 1000000000}s; this partition alone is not full qualification)"
      | some shard => s!"checker self-test partition {partition.label} shard {shard.label}: PASS \
          ({elapsed / 1000000000}s; this shard alone is not the partition, and no partition \
          alone is full qualification)"
    return 0
  IO.println <| s!"checker self-test: PASS ({fixtures.size} fixed fixtures in-process; " ++
    (if options.buildBound then
        s!"{fixtures.size} real-CLI controls (including all smoke controls); "
      else s!"{smokeFixtureNames.size} real-CLI smoke controls; ") ++
    s!"{(fenceCorpusCases repo).size + publicOnlyFenceCases.size} Markdown cases plus import-setup \
      controls; 9 manifest cases; structural controls including explicit contract mutations; " ++
    s!"{CompilerPaths.caseCount} imported compiler-path mutations with fresh restorations; " ++
    (if options.buildBound then
      "build-bound tier: full real-CLI fixture sweep, end-to-end fence corpus, " ++
      "external adopter controls in both lakefile formats, " ++
      "clean-checkout fence environment controls, public surface and fresh-plan controls; "
    else "") ++
    s!"{elapsed / 1000000000}s)"
  return 0

end Regula.Checker.CheckerSelftest

/-- The `checkerSelftest` executable: initializes Lean's search path, enables initializer
execution and runs `Regula.Checker.CheckerSelftest.run`, printing any exception as `FAIL:` and
returning `1`. -/
unsafe def main (args : List String) : IO UInt32 := do
  try
    Regula.Checker.initializeLeanSearchPath
    Lean.enableInitializersExecution
    Regula.Checker.CheckerSelftest.run args
  catch error =>
    IO.eprintln s!"FAIL: {error}"
    return 1
