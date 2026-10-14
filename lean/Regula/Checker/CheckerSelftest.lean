import Regula.Removal
import Regula.TaskManagerCheck
import Regula.Checker.PolicyCodec
import Regula.Checker.Documentation
import Regula.Checker.Lake
import Regula.Checker.CompilerPaths
import Regula.Checker.PolicyQualification
import Regula.Checker.BuildLintQualification
import Regula.Checker.LintQualification
import Regula.Checker.Inspection
import RegulaCore.ScratchCopy
import Regula.ToolchainProgram
import Regula.Checker.AcceptanceLink
import Regula.Checker.ResultProtocol
import Regula.Checker.SelftestArguments
import Regula.Site.Build

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
(`partitionBaseline`).
Their disjoint union is the full run; no partition alone reports full qualification.

The structural and correspondence clusters run in the structural project
(`StructuralProject`): the repository's package restricted to the application, so a gate there
builds and inspects the application alone. The controls that need the checker's own
package as the audited project run in copies of the repository (`structuralSelfHosted`,
`structuralSelfHostedPositive`).

Every partition's controls are divided into its `Partition.shards` shards: those of the structural
partition each carry one of `structuralShards`, those of the execution partition one of
`executionShards`, the lint-driver control groups one of `LintQualification.shards` and the
build-policy controls one of `BuildLintQualification.shards`. A fixture of the fixtures and cli
partitions is in the shard its position in module-name order gives (`fixtureShard`), the order of
the sorted manifest `loadFixtureManifest` reads, not the file order of `fixtures.json`, and each
other control of those two and of the environments partition has a shard of its own choosing.
`--shard` runs the controls of one, and the shards of a partition together run every control once
(`shards_cover`, `inShard_cover`).

It is intentionally qualification-only, not an ordinary build.
-/

namespace Regula.Checker.CheckerSelftest

open Lean System
open Regula.Checker
open Regula.Checker.Documentation
open Regula.Checker.Policy
open Regula.Checker.SelftestArguments

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
  /-- For each named declaration, texts that its own record in the output must contain
  (`declarationRecord`). -/
  records : Array (String × Array String) := #[]
  /-- Why the cli partition's real `axiomGate --file` sweep leaves the fixture out, when the entry
  states a reason (`fileAuditExclusion`); the in-process fixtures partition still checks it. -/
  fileAuditExclusion : Option String := none
  deriving Repr

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
  /-- Modules of the repository's own package that the controls' projects import from its build,
  which the baseline build names so that no control builds them there. -/
  modules : List String

/-- Each partition's baseline. The structural and execution controls run their gates in
projects of their own (the structural project, a copy of the repository, a scratch project),
where the gate builds and inspects that project's targets itself; the manifest controls run
`axiomGate` on the repository with a manifest it refuses before any build. So from the
repository's build they read only the executables they run: `axiomGate` in both partitions, and
in the structural clusters `docFenceAudit` and `freshChecker`, and in the retained build control
`docFenceAudit`. The lint-driver controls run
adopters of their own, which import `Regula.Contract` or `Regula.Linter`, and a fresh audit
builds in a copy of its own. From the repository's build they read `lint`, the driver that Lake
runs for `lake lint`, `axiomGate`, which that driver and some controls run, `ruleExamples`, whose
corpus-producer marker one control runs, and the modules the adopters import, so the baseline
names `Regula.Linter`, which imports `Regula.Linter.Rules`. That `axiomGate` or `lint` imports
each of the other modules the adopters import, such as `Regula.Contract`, is a reading of import
lines. Neither `toolPath` nor `baselineOf_axiomGate` covers that reading, and a module missing
from this baseline is not absent on a clean checkout: the adopters require `regula` as a Lake path
dependency of the checkout
(`BuildLintQualification.setup`), so an adopter's Lake builds such a module into the repository's
build on demand, possibly in several groups at once, instead of a refusal, and no guard detects
that. The other partitions keep the complete baseline. -/
private def partitionBaseline : Partition → Baseline
  | .structural => ⟨["axiomGate", "docFenceAudit", "freshChecker"], false, []⟩
  | .execution => ⟨["axiomGate"], false, []⟩
  | .lintDriver => ⟨["axiomGate", "lint", "ruleExamples"], false, ["Regula.Linter"]⟩
  | .fixtures | .cli | .environments | .buildPolicy => ⟨checkerTools, true, []⟩

/-- Every partition's baseline build names `axiomGate`: the executable that controls of every
partition run, some by its path in the repository's build instead of through `toolPath`
(`CompilerPaths`, `PolicyQualification`), and that the cold-start driver builds together with the
self-test (`RegulaVerification.commands`). -/
private theorem partitionBaseline_axiomGate (partition : Partition) :
    "axiomGate" ∈ (partitionBaseline partition).tools := by
  cases partition <;> simp [partitionBaseline, checkerTools]

/-- The number of shards the structural partition's controls are divided into, so that each
shard runs under the deadline of its own invocation (`Partition.shards`). -/
def structuralShards : Nat := Partition.structural.shards

/-- The number of shards the execution partition's controls are divided into. -/
def executionShards : Nat := Partition.execution.shards

/-- The number of shards the fixtures partition's controls are divided into. -/
def fixturesShards : Nat := Partition.fixtures.shards

/-- The number of shards the cli partition's controls are divided into. -/
def cliShards : Nat := Partition.cli.shards

/-- The number of shards the environments partition's controls are divided into. -/
def environmentsShards : Nat := Partition.environments.shards

/-- The lint-driver and build-policy partitions are divided into the shards their qualifications
select from. -/
theorem qualification_shards :
    Partition.lintDriver.shards = LintQualification.shards ∧
      Partition.buildPolicy.shards = BuildLintQualification.shards :=
  ⟨rfl, rfl⟩

/-- `INDEX/COUNT`, `INDEX` counted from 1. -/
private def shardLabel {shards : Nat} (shard : Fin shards) : String :=
  s!"{shard.val + 1}/{shards}"

/-- The shards of a list of controls are together a rearrangement of the list: every control
runs in exactly one shard, and the shards together run what an unsharded run does
(`inShard_cover`). This is a statement about the selection. That the shards select from the
same list rests on their running the same sources, which it does not state. -/
private theorem shards_cover {shards : Nat} {α : Type} (items : List (Fin shards × α)) :
    ((List.finRange shards).flatMap fun selected => inShard (some selected) items).Perm
      (inShard none items) :=
  inShard_cover _ (List.nodup_finRange shards) List.mem_finRange items

/-- The structural shard `index`, counted from 0. -/
private def structuralShard (index : Nat) (bound : index < structuralShards := by decide) :
    Fin structuralShards :=
  ⟨index, bound⟩

/-- The execution shard `index`, counted from 0. -/
private def executionShard (index : Nat) (bound : index < executionShards := by decide) :
    Fin executionShards :=
  ⟨index, bound⟩

/-- The shard of the fixture at `position` in module-name order, of a partition of `shards`
shards that divides the fixtures among them in turn. -/
private def fixtureShard {shards : Nat} (position : Nat) (positive : 0 < shards := by decide) :
    Fin shards :=
  ⟨position % shards, Nat.mod_lt _ positive⟩

/-- The environments shard `index`, counted from 0. -/
private def environmentsShard (index : Nat) (bound : index < environmentsShards := by decide) :
    Fin environmentsShards :=
  ⟨index, bound⟩

/-- What a sharded run of a partition whose controls are not named one by one prints after its
verdict: the shard it ran, which is not the whole partition. -/
private def shardNote {shards : Nat} : Option (Fin shards) → String
  | none => ""
  | some selected => s!" (shard {shardLabel selected}; the other shards run the rest)"

/-- Whether a control assigned to `assigned` runs in a run of `shard`: in every unsharded run and
in that shard alone (`inShard`). -/
private def runsIn {shards : Nat} (shard : Option (Fin shards)) (assigned : Fin shards) : Bool :=
  !(inShard shard [(assigned, ())]).isEmpty

/-- The shard of `structuralSelfHostedPositive`, which holds no other control: its one accepting
fresh gate builds `RegulaPolicy` from empty output in a copy of the repository, and no cut divides
it, so it has the processors to itself (`SelfHosted.shard`). -/
private def selfHostedShard : Fin structuralShards := SelfHosted.positive.shard

/-- The shard of `structuralSelfHosted`, whose restored copy's fresh input a sharded run compares
with the positive's through their digests (`selfHostedDigest`, `SelfHosted.shard`). -/
private def selfHostedRestoredShard : Fin structuralShards := SelfHosted.restored.shard

/-- The shard of the source-attribution controls of the complete CLI sweep: the last. It also runs
the control of a process without Lean's task manager (`taskManagerControl`) and the control of a
run that stops early (`earlyStopControl`). -/
private def cliAttributionShard : Fin cliShards := ⟨cliShards - 1, by decide⟩

/-- The baseline of a run of `partition`, of one of its shards when `shard` selects one. The
shard of the self-hosted positive (`selfHostedShard`) runs `axiomGate` alone; a run of the cli
partition that runs its last shard (`cliAttributionShard`), sharded or not, also runs `qualify` and
`site`, in the control of a process without Lean's task manager and in the control of a run that
stops early, and `ruleExamples` and `ruleExampleQualification` in the latter; every other shard
keeps the partition's baseline. -/
private def baselineOf (partition : Partition) (shard : Option (Nat × Nat)) : Baseline :=
  if partition = .structural ∧ (shard.bind (shardOf? structuralShards)) = some selfHostedShard
  then ⟨["axiomGate"], false, []⟩
  else if partition = .cli ∧
      (shard.isNone ∨ shard.bind (shardOf? cliShards) = some cliAttributionShard) then
    ⟨checkerTools ++ ["qualify", "site", "ruleExamples", "ruleExampleQualification"], true, []⟩
  else partitionBaseline partition

/-- Every run's baseline build names `axiomGate` (`partitionBaseline_axiomGate`), a shard's
too. -/
private theorem baselineOf_axiomGate (partition : Partition) (shard : Option (Nat × Nat)) :
    "axiomGate" ∈ (baselineOf partition shard).tools := by
  unfold baselineOf
  split
  · simp
  · split
    · simp [checkerTools]
    · exact partitionBaseline_axiomGate partition

/-- The checker executables `baselines` name, each once. -/
private def baselineTools (baselines : List Baseline) : List String :=
  (baselines.flatMap (·.tools)).eraseDups

private def usage : String :=
  "usage: lake exe checkerSelftest -- [--jobs N] [--structural-only] [--build-bound [--partition \
    fixtures|structural|execution|cli|environments|build-policy|lint-driver \
    [--shard INDEX/COUNT]]]\n" ++
  "--fences-only: focused in-process and public fence qualification, without the full suite\n" ++
  "default tier: every planted-defect verdict in one process plus a real-CLI smoke tier\n" ++
  "--build-bound: additionally run the conditional tier (real-CLI sweep, end-to-end\n" ++
  "fence corpus, external adopters, clean-checkout environment, public controls)\n" ++
  "--partition: run only the named build-bound group; all seven groups are required for full \
    qualification\n" ++
  "--shard: run only that shard of the group, INDEX from 1 and COUNT its number of shards: " ++
    ", ".intercalate
      (Partition.all.map fun partition => s!"{partition.shards} of {partition.label}") ++
    "; all its shards are required for the group"

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
control adds inherits the package's options as it would in the repository. The project also
declares the repository's weak-arguments `extraDep` facet, verbatim. The project
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

/-- Render a target's `plugins` for the structural project. The repository's targets load only
Regula's elaboration observer, as `@/RegulaObserver:shared`; any other plugin is refused. -/
private def renderPlugins (target : String) (keys : Array _root_.Lake.PartialBuildKey) :
    IO String := do
  if keys.isEmpty then return ""
  unless keys.all (Observer.observerKey (Name.mkSimple Observer.regulaPackage)) do
    throw <| IO.userError s!"self-test: {target} loads a plugin other than Regula's observer"
  return s!"  plugins := #[`@/{Observer.observerLibrary}:shared]\n"

/-- Render the observer's entry of a target's `needs` for the structural project, which each
target that loads the observer lists beside its `plugins` entry (`Lake.isObserverNeed`), so that
Lake builds it once. The project renders no other `needs` entry, such as the input file of the
library `Regula`: it holds only the modules that its targets build. -/
private def renderNeeds (keys : Array _root_.Lake.PartialBuildKey) : String :=
  if keys.any (Observer.observerKey (Name.mkSimple Observer.regulaPackage)) then
    s!"  needs := #[`@/{Observer.observerLibrary}:shared]\n"
  else ""

/-- Derive the structural project from the repository's loaded workspace and parsed manifest.
It holds the claimed application, the fixture, their root-package imports and the elaboration
observer library the targets load as a plugin. Module ownership, sources, imports of root-package
modules and target configuration, `plugins` and `needs` included, are Lake's own
(`Workspace.findModule?`, `Lean.parseImports'`); nothing is a fixed file list. -/
private def structuralProject (manifest : Manifest) (ws : _root_.Lake.Workspace) :
    IO StructuralProject := do
  let pkg := ws.root
  let spelling (name : Name) := Manifest.targetSpelling name
  let some application := pkg.leanLibs.find? (spelling ·.name == structuralApplication)
    | throw <| IO.userError s!"self-test: Lake omitted the {structuralApplication} library"
  let some fixture := ws.findModule? structuralFixture
    | throw <| IO.userError s!"self-test: Lake omitted the module {structuralFixture}"
  let some observer := pkg.leanLibs.find? (·.name == Observer.observerLibrary)
    | throw <| IO.userError s!"self-test: Lake omitted the {Observer.observerLibrary} library"
  let claimed := (manifest.surfaces.filter (·.library == structuralApplication)).flatMap
    (·.executables)
  let executables := pkg.leanExes.filter (claimed.contains <| spelling ·.name)
  unless executables.size == claimed.size do
    throw <| IO.userError
      s!"self-test: Lake omitted a claimed executable of {structuralApplication}"
  let mut pending := (← application.getModuleArray).toList ++ [fixture] ++
    executables.toList.map (·.root) ++
    (← observer.getModuleArray).toList
  let mut modules : Array _root_.Lake.Module := #[]
  repeat
    let next :: rest := pending | break
    pending := rest
    if modules.any (·.name == next.name) then continue
    modules := modules.push next
    let header ← Lean.parseImports' (← Regula.Filesystem.readFile next.leanFile) next.leanFile.toString
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
    s!"  leanOptions := {renderOptions pkg.config.leanOptions}\n" ++
    (← renderPlugins pkg.baseName.toString (pkg.config.plugins.map (·.key)))
  for library in libraries do
    refuseArguments (spelling library.name) (Lake.libraryOptions library)
    lakefile := lakefile ++ s!"\nlean_lib «{library.name}» where\n" ++
      s!"  srcDir := {repr library.config.srcDir.toString}\n" ++
      s!"  roots := #[{", ".intercalate (library.config.roots.toList.map (s!"`{·}"))}]\n" ++
      s!"  globs := #[{", ".intercalate (library.config.globs.toList.map renderGlob)}]\n" ++
      s!"  leanOptions := {renderOptions library.config.leanOptions}\n" ++
      (← renderPlugins (spelling library.name) (library.config.plugins.map (·.key))) ++
      renderNeeds library.config.needs
  for executable in executables do
    refuseArguments (spelling executable.name) (Lake.executableOptions executable)
    lakefile := lakefile ++ s!"\nlean_exe «{executable.name}» where\n" ++
      s!"  root := `{executable.root.name}\n" ++
      s!"  supportInterpreter := {executable.supportInterpreter}\n" ++
      s!"  leanOptions := {renderOptions executable.config.leanOptions}\n" ++
      (← renderPlugins (spelling executable.name) (executable.config.plugins.map (·.key))) ++
      renderNeeds executable.config.needs
  -- The repository's `extraDep` facet, which records the `weakLeanArgs` of the root package in
  -- each module's trace, so an incremental gate decides a module it replays (RG2003) as it does
  -- in the repository, and the module artifacts seeded from the repository's build match.
  let some facet := Lake.weakArgsDeclarations (← IO.FS.readFile pkg.configFile)
    | throw <| IO.userError s!"self-test: {pkg.configFile} has no weak-arguments facet"
  lakefile := lakefile ++ facet
  return {
    lakefile, sources
    libraries := libraries.map (spelling ·.name)
    executables := executables.map (spelling ·.name) }

/-- Immutable Lake-derived coordinates, acquired before fixture imports can
register additional environment extensions. Scratch controls reanchor the
relative directories without loading cold Lake configurations in this process. -/
private structure SourceLayout where
  relativeDir : FilePath
  /-- The structural project derived from the repository (`structuralProject`). -/
  project : StructuralProject
  /-- Where Lake puts the root package's module artifacts, relative to the package directory:
  its `leanLibDir` and its `irDir` (`seedModuleArtifacts`). -/
  artifactDirs : Array FilePath

private def loadSourceLayout (repo : FilePath) : IO SourceLayout := do
  let manifestPath := Manifest.defaultPath repo
  let manifest ← IO.ofExcept <|
    Manifest.parse manifestPath.toString (← IO.FS.readFile manifestPath)
  Workspace.withRootWorkspace repo fun ws => do
    let relativeDir := ws.root.config.srcDir.normalize
    if relativeDir.isAbsolute || relativeDir.components.contains ".." then
      throw <| IO.userError
        "self-test: package source directory must stay inside the copied repository"
    let root := ws.root.dir.normalize.components
    let artifactDirs ← #[ws.root.leanLibDir, ws.root.irDir].mapM fun place => do
      let components := place.normalize.components
      let relative := components.drop root.length
      unless root.isPrefixOf components && !relative.isEmpty && !relative.contains ".." do
        throw <| IO.userError
          s!"self-test: the build directory {place} must stay inside the copied repository"
      return System.mkFilePath relative
    return { relativeDir, project := ← structuralProject manifest ws, artifactDirs }

private def loadFixtureManifest (layout : SourceLayout) (repo : FilePath) : IO
    (Array FixtureSpec) := do
  let path := (repo / layout.relativeDir) / "Fixtures" / "fixtures.json"
  let inventory ← Lake.surfaceInventory repo
  let some library := inventory.libraries.find? (·.library == "Fixtures")
    | throw <| IO.userError "fixture manifest: Lake omitted the Fixtures library"
  let value ← readJson path
  let object ← IO.ofExcept value.getObj?
  let allowed :=
      #["expect", "reason", "reasons", "claim", "execution", "label", "pattern", "output",
        "records", "fileAuditExclusion"]
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
    let reason ← match spec.getObjVal? "reason" with
      | .error _ => pure none
      | .ok reason =>
        match reason.getStr? with
        | .ok text => pure (some text)
        | .error _ =>
          IO.ofExcept <| PolicyCodec.exactFields reason ["present", "absent"]
          let present ← requiredString reason "present" moduleName
          let absent ← requiredString reason "absent" moduleName
          pure (some (match RegulaPolicy.Compiler.legacyCompilerTrust with
            | .present => present
            | .absent => absent))
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
    let records ← match spec.getObjVal? "records" with
      | .error _ => pure #[]
      | .ok value => do
        let object ← IO.ofExcept value.getObj?
        object.keysArray.qsort (· < ·) |>.mapM fun declaration => do
          let texts ← IO.ofExcept <| value.getObjVal? declaration
          return (declaration, ← jsonStringArray s!"{moduleName}.records.{declaration}" texts)
    let fileAuditExclusion ← optionalString spec "fileAuditExclusion" moduleName
    if fileAuditExclusion == some "" then
      throw <| IO.userError s!"{moduleName}: fileAuditExclusion must state a reason"
    fixtures := fixtures.push {
      moduleName, source := source.source, expectation, reasons, claim, execution, label,
          pattern, output, records, fileAuditExclusion }
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
        {name}; add it to the baseline of the partition that runs it (partitionBaseline)"
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

/-- The record of the declaration `name` in a gate output: the line whose text after its verdict
tag, `[OK] ` or `[VIOLATION[...]] `, begins with `name (`, then the lines after it up to the next
one that begins with `[`, which hold the rest of a type that Lean prints on several lines. `none`
when no line begins the record. -/
private def declarationRecord (output name : String) : Option String := Id.run do
  let mut record : Option (Array String) := none
  for line in output.splitOn "\n" do
    match record with
    | some lines =>
      if line.startsWith "[" then break
      record := some (lines.push line)
    | none =>
      if line.startsWith "[" && ("] ".intercalate ((line.splitOn "] ").drop 1)).startsWith
          s!"{name} (" then
        record := some #[line]
  return record.map ("\n".intercalate ·.toList)

/-- Exact verdict assessment for one fixture against gate (or gate-equivalent)
output. The same function assesses real CLI output and the in-process batch
verdicts, so both paths assert identical intended reasons. -/
private def assessFixtureOutput (fixture : FixtureSpec) (ended : RunEnd)
    (output : String) : Option String := Id.run do
  if let some missing := fixture.output.find? fun needle => !output.contains needle then
    return some s!"{fixture.moduleName}: missing expected output {repr missing}:\n{output}"
  for (name, needles) in fixture.records do
    let some record := declarationRecord output name
      | return some s!"{fixture.moduleName}: no record of {name}:\n{output}"
    if let some missing := needles.find? fun needle => !record.contains needle then
      return some s!"{fixture.moduleName}: the record of {name} lacks {repr missing}:\n{record}"
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
private def renderFileAudit (observed : RegulaPolicy.Compiler.LegacyCompilerTrust)
    (fixture : FixtureSpec) (_moduleName : String)
    (declarations : Array Regula.Report.Declaration)
    (roots : Array Regula.Report.ExecutionRoot)
    (transcripts : Array Frontend.Transcript) (imported : Array Regula.Report.Declaration) :
    String × Bool := Id.run do
  let .ok scope := Policy.admitScope observed declarations transcripts imported
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
      -- Every part of a `module` file, so the census holds its private constants, such as the
      -- private axiom of a public native proof (`readModuleCensus`).
      let (moduleData, constants) ← readModuleCensus compilation.oleanPath
      pending := pending.push {
        index, fixture, compilation
        constantNames := constants.map (·.name.toString)
        importNames := moduleData.imports.map (·.module)
        -- Same transcript predicate as the post-load check, applied to the
        -- raw module constant records with the probe's own kind mapping, so
        -- only fixtures that can need a transcript pay for one. A divergence
        -- (post-load need with no worker transcript) fails closed below.
        wantsTranscript := constants.any fun info =>
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
  -- attribute state). As there, a transcript refuses a warning exactly when
  -- its fixture's compilation does. Failures are tolerated here; consumers
  -- below fail closed on a missing transcript with the same text the CLI path
  -- reports.
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
              item.compilation.sourcePath.toString, toString item.compilation.spec.rejectWarnings,
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
      Array Regula.Report.ExecutionRoot × RegulaPolicy.Compiler.LegacyCompilerTrust ×
      Array Regula.Report.Declaration) := #[]
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
            inspected := inspected.push
              (item, declarations, roots, report.compilerCapability, report.imported)
      catch error =>
        -- An inspection that throws has no report: the gate reports it as incomplete.
        for item in items do
          results := results.set! item.index
            (assessFixtureOutput item.fixture .incomplete error.toString)
    pure ()
  finally Lean.searchPathRef.set oldSearchPath
  for (item, declarations, roots, observed, imported) in inspected do
    let moduleName := item.compilation.spec.«module»
    if Policy.needsFrontendTranscript declarations then
      match transcripts.find? (·.1 == moduleName) with
      | some (_, some transcript) =>
        let (output, succeeded) := renderFileAudit observed item.fixture moduleName
          declarations roots #[transcript] imported
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
      let (output, succeeded) := renderFileAudit observed item.fixture moduleName
        declarations roots #[] imported
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

/-- The controls of the shape rule of the Markdown scanner (standard §7.7): one text for each
form that the rule refuses, with words of the violation, and texts that the rule accepts, with
the fence that passes. The forms are a Lean fence in a container or after indentation, a line of
Lean shape inside a fence that the scanner thinks is open, a closing run of a Lean fence after
indentation, a different spelling of the language, a character before the language that a
reader can remove, a `&` or a backslash in the first word after a run, a carriage return that no
line feed follows, the character U+0000, and the start tag of a code element of raw HTML: each
of the five names, in upper and in mixed case, before characters that end a name and at the end
of a line, and inside a fence of a different language. Two lines of text with an inline span of
three back-ticks are refused on purpose: the shape is conservative, and these controls pin that.
A `&` after a tab is refused on purpose too: a word ends at a space for each reader, and not at a
tab for each reader. The texts with line endings of a carriage return and a line feed are
controls of a boundary outside the proofs: Lean reads a carriage return before a line feed as a
line feed. -/
private def shapeCases : Array (String × String × String) :=
  let column := "does not open a `lean` fence in the first column"
  let inside := "is inside a fence"
  let closing := "closing line of a Lean fence does not start in the first column"
  let raw := "raw HTML opens a code element"
  let body := "theorem t : True := trivial"
  #[("quoted-fence", s!"> ```lean\n> {body}\n> ```\n", column),
    ("quoted-list-fence", s!"> - ```lean\n>   {body}\n>   ```\n", column),
    ("list-marker-fence", s!"- ```lean\n  {body}\n  ```\n", column),
    ("ordered-marker-fence", s!"1. ```lean\n   {body}\n   ```\n", column),
    ("task-marker-fence", s!"- [ ] ```lean\n      {body}\n      ```\n", column),
    ("footnote-fence", s!"[^1]: ```lean\n    {body}\n    ```\n", column),
    ("list-item-fence", s!"- item\n\n  ```lean\n  {body}\n  ```\n", column),
    ("indented-fence", s!" ```lean\n{body}\n```\n", column),
    ("four-space-fence", s!"    ```lean\n    {body}\n    ```\n", column),
    ("prose-fence-run", "see ```lean in the text\n", column),
    ("run-in-indented-code", s!"prose\n\n    ```\n```lean\n{body}\n```\n", inside),
    ("backtick-info", s!"```text`x\nprose\n```lean\n{body}\n```\n", inside),
    ("run-in-comment", s!"<!--\n```\n-->\n```lean\n{body}\n```\n", inside),
    ("run-in-html-block", s!"<details>\n```\n</details>\n\n```lean\n{body}\n```\n", inside),
    ("indented-close-other", s!"```text\n    ```\n```\n```lean\n{body}\n```\n```\n```\n", inside),
    ("sample-in-longer", s!"````markdown\n```lean\n{body}\n```\n````\n", inside),
    ("indented-close-lean",
      "```lean\ntheorem early : True := trivial\n    ```\ntheorem late : True := trivial\n\
        ```\n```\n", closing),
    ("spelling-capital", s!"```Lean\n{body}\n```\n", column),
    ("spelling-lean4", s!"```lean4\n{body}\n```\n", column),
    ("spelling-braces", "```{.lean}\n" ++ body ++ "\n```\n", column),
    ("spelling-reference", s!"```l&#101;an\n{body}\n```\n", column),
    ("spelling-backslash", s!"```le\\an\n{body}\n```\n", column),
    ("raw-pre", s!"<pre>\n{body}\n</pre>\n", raw),
    ("raw-code-space", "text <code class=\"x\">y</code>\n", raw),
    ("raw-xmp-tab", "<xmp\tclass=\"x\">\n", raw),
    ("raw-listing-slash", "<listing/>\n", raw),
    ("raw-plaintext-end", "text <plaintext\n", raw),
    ("raw-upper", "<PRE>\n", raw),
    ("raw-mixed", "<CoDe>x\n", raw),
    ("raw-in-fence", "```html\n<pre>\n```\n", raw),
    ("lone-return",
      "```lean\raxiom hidden : False\r```\ntheorem ok : True := trivial\n```\n",
      "carriage return that no line feed follows"),
    ("return-return-line-feed", "prose\r\r\n", "carriage return that no line feed follows"),
    ("raw-return", "<pre\r\nclass=\"language-lean\">\naxiom hidden : False\n</pre>\n", raw),
    ("raw-form-feed", "<pre\x0c>\n", raw),
    ("inline-span-lean", "See ```x``` lean examples.\n", column),
    ("inline-span-path", "See ```x``` lean/Regula.\n", column),
    ("form-feed-before-word", s!"```\x0clean\n{body}\n```\n", column),
    ("vertical-tab-before-word", s!"```\x0blean\n{body}\n```\n", column),
    ("no-break-space-before-word", s!"``` lean\n{body}\n```\n", column),
    ("reference-before-word", s!"```&#32;lean\n{body}\n```\n", column),
    ("reference-after-tab", "```sh\ta&b\nprose\n```\n", column),
    ("null-in-body", "```lean\nexample : \"\x00\" = \"\\x00\" := rfl\n```\n", "U+0000"),
    ("null-in-prose", "a\x00b\n", "U+0000"),
    ("reference-after-word",
      "```sh title=\"a&b\"\necho\n```\n\n```lean\ntheorem after_reference : True := trivial\n```\n",
      "reference-after-word.md:5 PASS"),
    ("backslash-after-word",
      "```toml path=\"C:\\work\"\nx = 1\n```\n\n```lean\n\
        theorem after_backslash : True := trivial\n```\n",
      "backslash-after-word.md:5 PASS"),
    ("return-line-feed", "```lean\r\ntheorem with_return : True := trivial\r\n```\r\n",
      "return-line-feed.md:1 PASS"),
    ("return-line-feed-string",
      "```lean\r\nexample : \"a\r\nb\" = \"a\\nb\" := rfl\r\n```\r\n",
      "return-line-feed-string.md:1 PASS"),
    ("return-line-feed-marker",
      "<!-- lean-fail: isolated carriage returns -->\r\n```lean\r\n\
        theorem marked_return : True := trivial\r\n```\r\n",
      "return-line-feed-marker.md:2 FAIL"),
    ("second-word-lean",
      "```text lean\nprose\n```\n\n```lean\ntheorem second_word : True := trivial\n```\n",
      "second-word-lean.md:5 PASS"),
    ("raw-near", "a <prefix> b and <codec x\n```lean\ntheorem raw_near : True := trivial\n```\n",
      "raw-near.md:2 PASS"),
    ("fence-in-comment", "<!--\n```lean\ntheorem in_comment : True := trivial\n```\n-->\n",
      "fence-in-comment.md:2 PASS"),
    ("other-indented",
      "- item\n\n  ```sh\n  ls\n  ```\n\n```lean\ntheorem after_item : True := trivial\n```\n",
      "other-indented.md:7 PASS"),
    ("sketch-name",
      "```leanSketch\nx\n```\n\n```lean\ntheorem after_sketch : True := trivial\n```\n",
      "sketch-name.md:5 PASS"),
    ("tilde-fence", "~~~lean\ntheorem tilde : True := trivial\n~~~\n", "tilde-fence.md:1 PASS")]

/-- The controls of the shape rule of the Verso scanner: a `lean` block after a tab, after a
carriage return and after a space, in a quotation and in a list item, a line of Lean shape
inside a block, a closing run of a Lean example after indentation, a source with carriage
returns, a source with the character U+0000, and two sources that the rule accepts. -/
private def versoShapeCases : Array (String × String × String) :=
  let column := "does not open a `lean` block in the first column"
  let body := "theorem t : True := trivial"
  #[("verso-tab", s!"\t```lean\n{body}\n```\n", column),
    ("verso-carriage-return", s!"\r```lean\n{body}\n```\n", "a carriage return"),
    ("verso-space", s!" ```lean\n{body}\n```\n", column),
    ("verso-quoted", s!"> ```lean\n> {body}\n> ```\n", column),
    ("verso-list-item", s!"* item\n\n  ```lean\n  {body}\n  ```\n", column),
    ("verso-inside-block", "```text\n```lean\n```\n", "is inside a code block"),
    ("verso-indented-close", s!"```lean\n{body}\n  ```\n",
      "closing line of a Lean example does not start in the first column"),
    ("verso-return", s!"```lean\r\n{body}\r\n```\r\n", "a carriage return"),
    ("verso-null", "```lean\nexample : \"\x00\" = \"\\x00\" := rfl\n```\n", "U+0000"),
    ("verso-first-column", s!"```lean\n{body}\n```\n", "verso-first-column:1 PASS"),
    ("verso-sketch", s!"```leanSketch\nx\n```\n```lean\n{body}\n```\n", "verso-sketch:4 PASS")]

/-- Counterexample aid, not correctness evidence (standard §0 "The Role of Testing"):
concrete `Documentation.scan` inputs for each marker/fence problem class. The universal
statement is `Documentation.checked_scanLines`: the scanner reports no violation exactly for a
document with lines that the protocol admits. These cases also read the text of a violation and
the number of fences of a clean text, which that statement does not cover. -/
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
  -- The shape rule: each refused form has its violation, and each accepted text has one fence
  -- and no violation. An expectation that ends with ` PASS` or ` FAIL` is the result of the
  -- audit for the fence of a text that the scanner accepts.
  for (verso, shape) in [(false, shapeCases), (true, versoShapeCases)] do
    for (name, text, expected) in shape do
      let result :=
        if verso then Documentation.scanVerso text name else Documentation.scan text name
      if expected.endsWith " PASS" || expected.endsWith " FAIL" then
        if result.fences.size != 1 || !result.problems.isEmpty then
          failures := failures.push
            s!"scanner/shape/{name}: expected one clean fence, got {result.problems}"
      else if !result.problems.any (·.contains expected) then
        failures := failures.push
          s!"scanner/shape/{name}: missing problem containing {repr expected}"
  if !Documentation.matchesPattern "(?s)failed.*law|Fields missing"
      "prefix failed\nfor a law suffix" then
    failures := failures.push "scanner/pattern: ordered/alternative matching failed"
  failures

/-- Generate certificates with the compiler that will check them. The direct and grind
frontends may normalize differently, so each keeps its own certificate. Setup failure or
ambiguous output aborts qualification; the corpus still executes `bv_check` independently. -/
private def bvCheckCertificates (repo scratch : FilePath) : IO (FilePath × FilePath) := do
  let generate (name tactic : String) : IO FilePath := do
    let dir := scratch / s!"certificate-{name}"
    IO.FS.createDirAll dir
    let source := dir / "Certificate.lean"
    IO.FS.writeFile source <| "import Std.Tactic.BVDecide\n" ++
      s!"theorem certificate (x y : BitVec 2) : (x &&& y) + (x ||| y) = x + y := by {tactic}\n"
    let result ← runProcess repo "lake" #["env", "lean", source.toString]
    unless result.succeeded do
      throw <| IO.userError s!"{name} LRAT setup failed: {result.output}"
    let files := (← Regula.Filesystem.Construction.listDirectory dir).filter
      (·.path.extension == some "lrat")
    let [entry] := files.toList
      | throw <| IO.userError s!"{name} LRAT setup requires exactly one generated certificate"
    let path := entry.path
    if (← IO.FS.readBinFile path).isEmpty then
      throw <| IO.userError s!"{name} LRAT setup generated an empty certificate"
    return path
  return (← generate "direct" "bv_decide? -binaryProofs",
    ← generate "grind" "grind => bv_decide? -binaryProofs")

/-- The adversarial fence corpus shared by the in-process default-tier audit
and the end-to-end public `docFenceAudit` control in the conditional tier. The controls of the
shape rule (`shapeCases`) are part of it. -/
private def fenceCorpusCases (certificate grindCertificate : FilePath) : Array (String × String × String) := #[
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
  -- The unused-variables linter runs after the `in` scope, under the compile's
  -- `warningAsError`, so its warning is an error.
  ("warning", "```lean\nset_option warningAsError false in\ndef hidden_warning (unused : Nat) : \
    Nat := 1\n```\n", "error: Variable name `unused` is not explicitly referenced"),
  -- Lean prints an information message as its bare text; this one reads as a warning line.
  ("information", "```lean\n#print \"information.md:1:0: warning: an information message\"\n\
    theorem information_ok : 1 = 1 := rfl\n```\n", "information.md:1 PASS"),
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
    -binaryProofs \"{certificate}\"\n```\n", "trusted-bv-check.md:2 PASS_TRUSTED"),
  -- Authentication does not depend on the surrounding syntax: `grind =>` and `sym =>` blocks,
  -- namespaced names, attributes, `set_option … in` and reverted parameters are all covered.
  ("trusted-grind-native", s!"<!-- lean-trusted-compiler -->\n```lean\nimport \
    Std.Tactic.BVDecide\ntheorem docs_grind_bv_decide (x y : BitVec 2) : (x &&& y) + (x ||| y) = \
    x + y := by grind => bv_decide\ntheorem docs_sym_bv_trace (x y : BitVec 2) : (x &&& y) + \
    (x ||| y) = x + y := by sym => bv_decide?\ntheorem docs_grind_bv_check (x y : BitVec 2) : \
    (x &&& y) + (x ||| y) = x + y := by\n  grind => bv_check -binaryProofs \
    \"{grindCertificate}\"\n```\n", "trusted-grind-native.md:2 PASS_TRUSTED"),
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
  -- (`Lean.mkErrorStringWithPos`); its severity is still `warning`, which the audit rejects.
  ("named-warning", "```lean\nimport Lean\nopen Lean\nset_option warningAsError false in\nrun_cmd \
    Lean.logNamedWarningAt (← getRef) `lean.selftestNamedWarning m!\"named\"\n```\n",
        "emitted warning")
] ++ shapeCases

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
  Regula.Filesystem.copyFile (repo / "lean-toolchain") (project / "lean-toolchain")
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
  let (certificate, grindCertificate) ← bvCheckCertificates repo scratch
  let cases := fenceCorpusCases certificate grindCertificate
  let mut tasks : Array Documentation.Task := #[]
  let mut structural : Array String := #[]
  for (name, text, _) in cases do
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
  for (name, _, expected) in cases do
    let expected := expected.replace " PASS_TRUSTED" (" " ++ statusName .passTrusted)
      |>.replace " PASS_NEG" (" " ++ statusName .passNegative)
      |>.replace " PASS" (" " ++ statusName .pass)
    if !(fenceOriginOutput output s!"{name}.md").contains expected then
      failures :=
          failures.push s!"scanner/corpus/{name}: missing diagnostic {repr expected}:\n{output}"
  return failures ++ (← diagnosticSetupQualification repo scratch)

/-- End-to-end public `docFenceAudit` control over the adversarial corpus
(conditional tier: it re-runs the auditor against a clean-checkout copy). -/
private unsafe def publicScannerQualification (repo scratch : FilePath) : IO (Array String) := do
  let (certificate, grindCertificate) ← bvCheckCertificates repo scratch
  let cases := fenceCorpusCases certificate grindCertificate ++ publicOnlyFenceCases
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
CLI rendering the missing-file, malformed, incomplete, wrong-version, unknown-key,
bad-execution and unknown-`decides` refusal classes and a Lake-inventory refusal. The pure parser is proved for every
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
  let unknownDecides := scratch / "unknown-decides.json"
  IO.FS.writeFile unknownDecides <| "{\"schema-version\":2,\"surfaces\":[{" ++
    "\"library\":\"AuditApp\",\"claim\":\"standard-logical\",\"rationale\":\"control\"," ++
    "\"decides\":[\"NoSuchLibrary\"]}],\"excluded-libraries\":[],\"excluded-executables\":[]}"
  if let some failure ← expectManifestPublicFailure repo "unknown-decides" unknownDecides
      "manifest-schema: surface 'AuditApp' decides 'NoSuchLibrary', which is not a claimed" then
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
copy operation as the public gate, rather than a second fixed source list. The running Regula's
observer library is placed in each copied package `regula` (`Lake.ProjectCopy.placeObservers`);
the result is the exact paths written there (`Lake.ProjectCopy.placedPaths`). -/
private def prepareScratchRepo (repo scratch : FilePath) : IO (Array FilePath) := do
  let copy ← Lake.copyProject repo scratch scratch
  copy.placeObservers
  return copy.placedPaths

private def withNewFile {α : Type} (path : FilePath) (text : String) (action : IO α) : IO α := do
  if ← Regula.Filesystem.isPresent path then
    throw <| IO.userError s!"refusing to overwrite structural fixture {path}"
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path text
  try action
  finally Regula.Filesystem.removePath .file path

private def withReplacedFile {α : Type} (path : FilePath) (text : String) (action : IO α) :
    IO α := do
  let original ← IO.FS.readFile path
  IO.FS.writeFile path text
  try action
  finally IO.FS.writeFile path original

private def withRemovedFile {α : Type} (path : FilePath) (action : IO α) : IO α := do
  let original ← IO.FS.readFile path
  Regula.Filesystem.removePath .file path
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
repository, its Lake configuration, the repository's toolchain pin and lock manifest, the
manifest of `structuralBase`, and the running Regula's observer library in its build directory
(`Observer.placeRunning`), which the setup build and each gate then load unchanged while the
copy's observer source is the running Regula's. -/
private def prepareStructuralProject (layout : SourceLayout) (repo copy : FilePath) :
    IO Unit := do
  let mut items := []
  for relative in layout.project.sources.toList.eraseDups do
    items := items ++ (← Regula.Filesystem.Construction.capture (repo / relative) relative.components)
  for file in #["lean-toolchain", "lake-manifest.json"] do
    items := items ++ (← Regula.Filesystem.Construction.capture (repo / file) [file])
  items := items ++ [⟨["lakefile.lean"], .file layout.project.lakefile.toUTF8⟩,
    ⟨["foundation_manifest.json"], .file ((← structuralManifestText layout repo) ++ "\n").toUTF8⟩]
  Regula.Filesystem.construct copy (Regula.Filesystem.Construction.layout items)
  Observer.placeRunning copy

/-- The restored control that ends a structural cluster: once each of its mutations is restored,
the fresh gate (empty-output elaboration of a copy of the cluster's project) accepts it. A
cluster cut from a longer chain ends with its own, so every mutation is still followed by the
fresh gate of a restored copy. -/
private def restoredControl (repo copy : FilePath) (failures : IO.Ref (Array String)) :
    IO Unit := do
  let restored ← runBinaryFrom repo copy "axiomGate" #[]
  if !restored.succeeded then
    failures.modify (·.push s!"structural/restored: final fresh gate failed:\n{restored.output}")

/-- Structural mutation cluster: a claimed module whose theorem the kernel never checked, refused
by the project audit and the build lint (`imported` false), or by the audit of a file and of a
documentation fence that import it (`imported` true), then the restored control. -/
private unsafe def structuralPartAAdmission (layout : SourceLayout) (imported : Bool)
    (repo copy : FilePath) : IO (Array String) := do
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
    if !imported then
      for (name, args) in #[("project-admission", #["--incremental"]),
          ("build-admission", #["--build-lint"])] do
        if let some failure := expectedFailure name (← gate args)
            #["kernel-admission", "admissionFalse"] then
          failures.modify (·.push failure)
    else
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
  restoredControl repo copy failures
  failures.get

/-- Structural mutation cluster: discovery of an added module and a suppressed warning
(`contamination` false), or contamination of the claimed library root by excluded fixture
modules, direct and exact-prefix-lookalike (`contamination` true), then the restored control. -/
private unsafe def structuralPartA (layout : SourceLayout) (contamination : Bool)
    (repo copy : FilePath) : IO (Array String) := do
  let sources := copy / layout.relativeDir
  let failures ← IO.mkRef (#[] : Array String)
  let gate (args : Array String := #["--incremental"]) :=
    runBinaryFrom repo copy "axiomGate" args
  if !contamination then
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
  else
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
  restoredControl repo copy failures
  failures.get

/-- The self-hosted copy in `copy`: a copy of the repository, by the fresh gate's own copy
operation, that claims `selfHostedManifestText`. Its content is a function of the repository's
files and manifest alone. -/
private def prepareSelfHosted (repo copy : FilePath) : IO Unit := do
  discard <| prepareScratchRepo repo copy
  IO.FS.writeFile (copy / "foundation_manifest.json") ((← selfHostedManifestText repo) ++ "\n")

/-- Copy the module artifacts of the repository's build, the directories Lake gives its root
package for `.olean` and `.ilean` files (`leanLibDir`) and for compiler output (`irDir`) with
their traces (`SourceLayout.artifactDirs`, read once at startup), to the same places below
`copy`, byte for byte. The copy's Lake configuration is the repository's, so these are the
places Lake reads there. Lake rebuilds a module whose saved trace does not match the hash of its
inputs, which are content hashes and options, not paths, so a module of the copy that the
repository's build made from the same sources is reused there and any other is built: the
copied files decide only what is rebuilt, not what a build gives. This is a reading of Lake's
module build, not a theorem. -/
private def seedModuleArtifacts (layout : SourceLayout) (repo copy : FilePath) : IO Unit := do
  for relative in layout.artifactDirs do
    let place := repo / relative
    unless ← Regula.Filesystem.isDirectory place do continue
    let destination := copy / relative
    let some parent := destination.parent | throw <| IO.userError "artifact copy has no parent"
    Regula.Filesystem.Construction.ensureDirectory 4096 parent
    discard <| Regula.Filesystem.copy place destination

/-- What a fresh gate reads of `project`: the entries its own copy operation (`copyProject`)
copies into `snapshot`, each by its path below the project, a file with its bytes, in path
order. The copy operation's own `.lake` there (the typed path overrides) is not an entry: it
copies nothing from the project's `.lake`. -/
private def freshInput (project snapshot : FilePath) :
    IO (Array (String × Option ByteArray)) := do
  discard <| prepareScratchRepo project snapshot
  let base := snapshot.normalize.components
  let own (path : FilePath) : List String := path.normalize.components.drop base.length
  let lake := _root_.Lake.defaultLakeDir.toString
  let mut entries : Array (String × Option ByteArray) := #[]
  for path in ← Regula.Filesystem.Construction.walkDirectory snapshot
      (fun path => pure (own path != [lake])) do
    if own path == [lake] then continue
    let content ← if ← Regula.Filesystem.isDirectory path then pure none
      else some <$> IO.FS.readBinFile path
    entries := entries.push ("/".intercalate (own path), content)
  return entries.qsort (·.1 < ·.1)

/-- The first entry by which two fresh inputs differ, for a failure message. -/
private def freshInputDifference (before after : Array (String × Option ByteArray)) :
    Option String :=
  if before == after then none
  else some <| match (before.zip after).find? (fun (b, a) => b != a) with
    | some (b, a) => if b.1 == a.1 then b.1 else s!"{b.1} / {a.1}"
    | none => s!"{before.size} entries before, {after.size} after"

/-- The fresh inputs (`freshInput`) that the two self-hosted clusters record: that of the
restored copy, which `structuralSelfHosted` records after its last restoration, and that of the
positive's own copy, which `structuralSelfHostedPositive` records before its fresh gate runs on
that copy and keeps only when that gate accepted. -/
private structure SelfHostedInputs where
  restored : IO.Ref (Option (Array (String × Option ByteArray)))
  positive : IO.Ref (Option (Array (String × Option ByteArray)))

private def SelfHostedInputs.new : IO SelfHostedInputs :=
  return { restored := ← IO.mkRef none, positive := ← IO.mkRef none }

/-- The recorded fresh input of `input`. -/
private def SelfHostedInputs.of (inputs : SelfHostedInputs) :
    SelfHosted → IO.Ref (Option (Array (String × Option ByteArray)))
  | .positive => inputs.positive
  | .restored => inputs.restored

/-- The comparison that replaces an accepting fresh gate on the restored copy, run by an
unsharded run after the queue has finished both self-hosted clusters: the restored copy's fresh
input must be that of the copy the positive's fresh gate accepted, path by path and byte by
byte. A missing input, from a cluster that stopped or a positive that was refused, fails it. -/
private def selfHostedIdentity (inputs : SelfHostedInputs) : IO (Array String) := do
  let (some restored, some positive) := (← inputs.restored.get, ← inputs.positive.get)
    | return #["structural/self-hosted/restored: the restored copy's fresh input was not \
        compared with that of the copy the positive accepted, because a self-hosted cluster \
        stopped or the positive was refused"]
  return match freshInputDifference positive restored with
    | none => #[]
    | some difference => #[s!"structural/self-hosted/restored: the restored copy is not the \
        copy the positive accepted, for a fresh gate; first difference: {difference}"]

/-- Write the canonical serialization of a fresh input to `path`: its number of entries, then for
each entry in order its path's UTF-8 length and bytes, then `0` for a directory, or `1` and the
length and bytes of a file. Every length is eight big-endian bytes, so the serialization is
prefix-free and two inputs have the same bytes exactly when they are equal. -/
private def writeFreshInput (path : FilePath) (input : Array (String × Option ByteArray)) :
    IO Unit := do
  let word (n : Nat) : ByteArray :=
    ⟨((List.range 8).reverse.map fun i => (n >>> (8 * i)).toUInt8).toArray⟩
  IO.FS.withFile path .write fun handle => do
    handle.write (word input.size)
    for (entry, content) in input do
      let name := entry.toUTF8
      handle.write (word name.size ++ name)
      match content with
      | none => handle.write ⟨#[0]⟩
      | some bytes =>
        handle.write (⟨#[1]⟩ ++ word bytes.size)
        handle.write bytes

/-- Where a sharded run writes the SHA-256 digest of the self-hosted fresh input `name`
(`positive` or `restored`): below the repository's `tmp/`, the place from which the `campaign`
job uploads it and to which the `diagnostics` job of `.github/workflows/diagnostics.yml`
downloads it for `Regula.DiagnosticsGate.digestPath`. -/
private def selfHostedDigestPath (repo : FilePath) (input : SelfHosted) : FilePath :=
  repo / "tmp" / "self-hosted-digest" / s!"{input.name}.sha256"

/-- Remove the digest of `input` at `selfHostedDigestPath`, so that the `diagnostics` gate refuses
it as missing until a run writes it again: the writer that a run of its shard runs when it starts
(`markIncomplete`) and before it writes the digest (`selfHostedDigest`), and that a refusal runs
in its place. -/
def clearSelfHostedDigest (repo : FilePath) (input : SelfHosted) : IO Unit := do
  let evidence := selfHostedDigestPath repo input
  Regula.Filesystem.removePath .file evidence

/-- What a sharded run does in place of `selfHostedIdentity`, after its queue, in the shard of
`input` (`SelfHosted.shard`): remove any earlier digest (`clearSelfHostedDigest`), then write
the SHA-256 digest of the canonical serialization of the fresh input that its cluster recorded in
`recorded` (`writeFreshInput`), by replacing the entry at the digest's path below the repository's
`tmp/` (`Regula.Filesystem.writeReplacing`). The `diagnostics` gate compares the two shards'
digests. A missing input fails the shard and writes no digest. -/
private def selfHostedDigest (repo scratch : FilePath) (input : SelfHosted)
    (recorded : IO.Ref (Option (Array (String × Option ByteArray)))) : IO (Array String) := do
  let name := input.name
  let evidence := selfHostedDigestPath repo input
  clearSelfHostedDigest repo input
  let some recorded ← recorded.get
    | return #[s!"structural/self-hosted/{name}: no fresh input was recorded, because its \
        cluster stopped or the positive was refused, so no digest was written"]
  let serialized := scratch / s!"self-hosted-input-{name}.bin"
  writeFreshInput serialized recorded
  let digest ← sha256File scratch serialized
  Regula.Filesystem.writeReplacing evidence (digest ++ "\n").toUTF8
  return #[]

/-- Structural controls that need the checker's own package as the audited project: in
a copy of the repository, the probe modules are exempt from the environment-level exclusion
check (the force import always brings them in), and a claimed module importing the probe's
report records, collector or compiler observer must still be rejected as excluded-module contamination. The structural
project has no source for that module, so the import there could not be this contamination.
The copy claims `selfHostedManifestText`, so its gates build `RegulaPolicy` and inspect its
module scope too.

On its own copy, the cluster runs the incremental gate on each of the three contaminations,
each restored before the next, and then records the restored copy's fresh input (`freshInput`)
in `inputs`. It must equal the fresh input of the copy on which `structuralSelfHostedPositive`
ran its accepting fresh gate. An unsharded run compares the two after the queue
(`selfHostedIdentity`), path by path and byte by byte. A sharded run, where the positive is in
another shard, writes each one's SHA-256 digest (`selfHostedDigest`), and the `diagnostics` gate
compares the two digests. No fresh gate runs in this cluster.

The copy's build directory starts with the module artifacts of the repository's build
(`seedModuleArtifacts`), so the setup build and the contamination gates build only what that
build did not make, such as `AuditApp` and the contaminated root, instead of `RegulaPolicy` and
the probe modules from empty output. A contamination gate's verdict comes from its
claimed-source build, the manifest, the Lake inventory and the module graph: the name, `.olean`
place and recorded imports of each loaded module. The graph worker finds every `Regula` module,
the probe modules among them, in the running checker's own library ahead of the copy's output
(`withProbeSearch`), so it reads none of the copy's files for them, seeded or built.

Lake reuses a seeded `RegulaPolicy` or `AuditApp` artifact only when its saved trace matches
the hash of that module's inputs in the copy, the bytes of its source among them. So a reused
`.olean` records the imports of the copy's own source and lies where the copy's build puts it,
and the contaminated root is built from its contaminated source whatever the seed holds. Each
gate therefore sees the graph it sees without the seed. That is a reading of Lake's
module build and of `withProbeSearch`, not a theorem.

The identity stands for an accepting fresh gate on the restored copy, which this cluster ran
before as the last step of its serial chain. What it establishes is a run-time fact: the
restorations left the copy with exactly the input that a fresh gate copies from the positive's
copy, the input that gate accepted. Between shards, equal SHA-256 digests are read as equal
inputs, an assumption of collision resistance, not a theorem. That a fresh gate on the restored
copy would then accept too rests on a fact that is not a theorem: a fresh gate reads the audited project only through
its copy operation (`copyProject`, which prunes the project's `.lake`, so the incremental gates'
build output and the seed here are not read), and builds that copy from empty output; without
`--with-docs`, as here, it reads no other file of the project, and the packages directory it
links is the repository's for every copy. `freshInput` is that operation's output. The restored
fresh gates of the structural project's clusters (`structuralPartA` and the others) run that
same path on a project whose `.lake` holds the build output of incremental contamination gates.
Dropping the gate here was the operator's decision (#305). -/
private unsafe def structuralSelfHosted (layout : SourceLayout) (repo copy : FilePath)
    (inputs : SelfHostedInputs) : IO (Array String) := do
  let failures ← IO.mkRef (#[] : Array String)
  let gate (label : String) (args : Array String := #["--incremental"]) := do
    loggedPhase s!"structural/self-hosted/{label}" do
      if ← timing.get then
        runProcessShowing copy (← toolPath repo "axiomGate").toString
          args #[(timingVariable, some "1")] (·.startsWith "verification phase ")
      else
        runBinaryFrom repo copy "axiomGate" args
  let appRoot := copy / layout.relativeDir / "AuditApp.lean"
  let originalRoot ← IO.FS.readFile appRoot
  for name in #["Regula.Report", "Regula.Collect", "Regula.CompilerObservation"] do
    let contaminated := originalRoot.replace "import AuditApp.Demo\n"
      s!"import AuditApp.Demo\nimport {name}\n"
    withReplacedFile appRoot contaminated do
      if let some failure := expectedFailure s!"probe-contamination/{name}" (← gate name)
          #["unexpected-project-module", name] then
        failures.modify (·.push failure)
  let some parent := copy.parent
    | throw <| IO.userError s!"self-test: the self-hosted copy {copy} has no parent directory"
  inputs.restored.set (some (← freshInput copy (parent / "self-hosted-input-restored")))
  failures.get

/-- The positive of `structuralSelfHosted`, alone in a shard of its own: the fresh gate accepts
the self-hosted copy as prepared (`prepareSelfHosted`), with no setup build and no mutation.
Before that gate runs, it reads the copy's fresh input, which it records in `inputs` when the gate
accepted. An unsharded run compares that input with the restored copy's after the queue
(`selfHostedIdentity`); a sharded run writes its digest (`selfHostedDigest`) for the `diagnostics`
gate. Nothing writes outside the copy's `.lake` between that reading and the gate's own copy
operation; that is a reading of this code and of the gate, not a theorem. -/
private unsafe def structuralSelfHostedPositive (repo copy : FilePath)
    (inputs : SelfHostedInputs) : IO (Array String) := do
  prepareSelfHosted repo copy
  let some parent := copy.parent
    | throw <| IO.userError s!"self-test: the self-hosted copy {copy} has no parent directory"
  let input ← freshInput copy (parent / "self-hosted-input-positive")
  let accepted ← runBinaryFrom repo copy "axiomGate" #[]
  if accepted.succeeded then
    inputs.positive.set (some input)
    return #[]
  return #[s!"structural/self-hosted/positive: fresh gate failed:\n{accepted.output}"]

/-- Structural mutation cluster: an unlisted root-owned module, an unclassified Lake library and an
elaboration observer library other than the running Regula's: an observer source changed in its
compiled code, a changed record module that a library whose only glob is its root links through
an import, and a stale library where Lake reuses it (`executables` false),
or an unclassified Lake executable, a claimed standalone executable root
and executable contamination (`executables` true), then the restored control. -/
private unsafe def structuralPartB (layout : SourceLayout) (executables : Bool)
    (repo copy : FilePath) : IO (Array String) := do
  let sources := copy / layout.relativeDir
  let failures ← IO.mkRef (#[] : Array String)
  let gate (args : Array String := #["--incremental"]) :=
    runBinaryFrom repo copy "axiomGate" args
  let lakefile := copy / "lakefile.lean"
  let originalLakefile ← IO.FS.readFile lakefile
  if !executables then
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
    withNewFile (sources / "ExtraSurface.lean") "def extraSurfaceValue : Nat := 1\n" do
      withReplacedFile lakefile
          (originalLakefile ++ "\nlean_lib «ExtraSurface» where\n  roots := #[`ExtraSurface]\n") do
        if let some failure := expectedFailure "unclassified-library" (← gate)
            #["manifest-incomplete", "ExtraSurface"] then
          failures.modify (·.push failure)
    -- The copy holds the running Regula's observer library (`Observer.placeRunning`). Each mutation
    -- below leaves the claimed modules loading a library whose bytes are not the running observer's,
    -- and the audit reports them as not observed (RG2003). Each puts the placed library, its trace
    -- and its hash back afterwards, so the restored control below admits the library of the
    -- unchanged source again.
    let notObserved := #["RG2003",
      "not observed: Regula's elaboration observer was not among the plugins"]
    let library := copy / ".lake" / "build" / "lib" /
      _root_.Lake.nameToSharedLib
        (Lean.mkModuleInitializationStem Observer.observerLibrary (some Observer.regulaPackage))
    let placed ← #["", ".trace", ".hash"].mapM fun suffix => do
      let path : FilePath := ⟨library.toString ++ suffix⟩
      return (path, ← IO.FS.readBinFile path)
    let observerMutation (name : String) (mutate : IO Unit) (restore : IO Unit) : IO Unit := do
      try
        mutate
        if let some failure := expectedFailure name (← gate) notObserved then
          failures.modify (·.push failure)
      finally
        restore
        for (path, bytes) in placed do IO.FS.writeBinFile path bytes
    -- A changed observer source that compiles to other code: an added public definition gives
    -- the module's C file another declaration, and Lake compiles its object from the C file's
    -- content (`Module.cFacetConfig`, `Lake/Build/Module.lean` lines 1184 to 1198), so the object
    -- the library links changes and Lake links the library again, whose bytes differ. A change
    -- that leaves the C file as it was, such as a comment, leaves the placed library current.
    let observerSource := sources / "RegulaObserver.lean"
    let observerText ← IO.FS.readFile observerSource
    observerMutation "observer-source-changed"
      (IO.FS.writeFile observerSource (observerText ++
        "\n/-- A changed observer module. -/\ndef changedObserverModule : Nat := 1\n"))
      (IO.FS.writeFile observerSource observerText)
    -- The same for an unchanged `RegulaObserver.lean` whose imported `RegulaObserver.Record`
    -- changed, in an observer library whose only glob is its root, `.one RegulaObserver`, so that
    -- `RegulaObserver.Record` is one of its modules only through that import
    -- (`LeanLib.recCollectLocalModules`, `Lake/Build/Library.lean` lines 36 to 61), and Lake links
    -- it into the library for that reason alone (`LeanLib.recBuildShared`). This reproduces the
    -- omission that reading 17 found: a check of the library's glob modules alone misses a
    -- changed module that the library links through an import.
    let recordSource := sources / "RegulaObserver" / "Record.lean"
    let recordText ← IO.FS.readFile recordSource
    let observerGlob := renderGlob (.andSubmodules Observer.observerLibrary)
    let bareLakefile := originalLakefile.replace s!"  globs := #[{observerGlob}]\n"
      s!"  globs := #[{renderGlob (.one Observer.observerLibrary)}]\n"
    if bareLakefile == originalLakefile then
      failures.modify (·.push s!"structural/observer-record-changed: the copy's lakefile declares \
        no observer library whose only glob is {observerGlob}")
    else
      withReplacedFile lakefile bareLakefile do
        observerMutation "observer-record-changed"
          (IO.FS.writeFile recordSource (recordText ++
            "\n/-- A changed record module. -/\ndef changedRecordModule : Nat := 1\n"))
          (IO.FS.writeFile recordSource recordText)
    -- A stale library where Lake reuses it: other bytes under the placed library's name, trace and
    -- hash, so that Lake links nothing. Neither its name nor its path admits it; only the bytes of
    -- the running observer do (`Observer.matchingPlugins`).
    observerMutation "observer-library-stale"
      (do IO.FS.writeBinFile library ((← IO.FS.readBinFile library).push 0)) (pure ())
  else
    let exeDecl :=
      "\n" ++ observedTargetLean .executable "«selftestTool»" "  root := `SelftestMain\n"
        (own := true)
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
  restoredControl repo copy failures
  failures.get

/-- Structural mutation cluster: omitted executable classification and an unproved update
(`group` 0), trivial and weakened update evidence (`group` 1), or a missing proof field and
weakened admission (`group` 2) of the application surface. Each mutation is followed by a
fresh restored gate. -/
private unsafe def structuralPartC (layout : SourceLayout) (group : Nat) (repo copy : FilePath) :
    IO (Array String) := do
  let sources := copy / layout.relativeDir
  let failures ← IO.mkRef (#[] : Array String)
  let gate (args : Array String := #["--incremental"]) :=
    runBinaryFrom repo copy "axiomGate" args
  if group == 0 then
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
  if group == 0 then
    mutate "app-unproved-update" resetProof ""
      #["build-failed", "Unknown identifier", "reset_inUse"]
  if group == 1 then
    mutate "app-trivial-update" resetProof
      "/-- Deliberately unrelated proof. -/\ntheorem reset_inUse : True := True.intro\n"
      #["build-failed", "Type mismatch", "reset_inUse", "∀ (l : Limiter), (reset l).inUse = 0"]
    mutate "app-weakened-update" resetProof
      ("/-- Deliberately conditional proof. -/\n" ++
        "theorem reset_inUse (l : Limiter) (_h : l.inUse = 0) : (reset l).inUse = 0 := rfl\n")
      #["build-failed", "Type mismatch", "reset_inUse", "∀ (l : Limiter), (reset l).inUse = 0"]
  if group == 2 then
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
Each refusal is asserted by its own message. `group` selects the controls of one cluster: 0 the
two positives and the kept cycle, 1 the ill-typed copies first and last, 2 the circular and the
`sorry` copy. -/
private def duplicateAdmissionControls (group : Nat) (sources copy : FilePath)
    (gate : Array String → IO ProcessResult) : IO (Array String) := do
  let failures ← IO.mkRef (#[] : Array String)
  if group == 0 then
    withNewFile (sources / "AuditApp" / "RealizedLemma.lean") realizedLemmaSource do
      for (name, imports) in #[
          ("realized-duplicate", "import AuditApp.RealizedLemma\nimport Std.Do.WP.SimpLemmas\n"),
          ("realized-duplicate-kept",
            "import Std.Do.WP.SimpLemmas\nimport AuditApp.RealizedLemma\n")] do
        withNewFile (copy / "RealizedDuplicate.lean") (imports ++ realizedDuplicateSource) do
          let result ← gate #["--file", "RealizedDuplicate.lean"]
          if !result.succeeded then
            failures.modify (·.push s!"structural/{name}: expected PASS:\n{result.output}")
  let duplicates := #[
      (1, "unchecked-duplicate-first", uncheckedDuplicateSource "mkConst ``False", "Unchecked",
        "Checked", "checked as"),
      (1, "unchecked-duplicate-last", uncheckedDuplicateSource "mkConst ``False", "Checked",
        "Unchecked", "while replaying declaration"),
      (2, "circular-duplicate-first", uncheckedDuplicateSource "mkConst `selftestDuplicateFact",
        "Unchecked", "Checked", "uses the name"),
      (2, "sorry-duplicate-last", sorryDuplicateSource, "Checked", "Unchecked",
        "axioms differ")].filter (·.1 == group)
  unless duplicates.isEmpty do
    withNewFile (sources / "AuditApp" / "DuplicateChecked.lean") checkedDuplicateSource do
      for (_, name, bogus, first, second, needle) in duplicates do
        withNewFile (sources / "AuditApp" / "DuplicateUnchecked.lean") bogus do
          withNewFile (copy / "DuplicateAdmission.lean")
              s!"import AuditApp.Duplicate{first}\nimport AuditApp.Duplicate{second}\n" do
            if let some failure := expectedFailure name
                (← gate #["--file", "DuplicateAdmission.lean"])
                #["kernel-admission", "selftestDuplicateFact", needle] then
              failures.modify (·.push failure)
  if group == 0 then
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

/-- Whether a value read from a report differs from another value: the first has search trees and
does not agree with the second (`differs_iff`). A value without search trees is never taken as a
different one, so a check that requires two values to differ refuses it (`differs_irregular`). -/
private def differs (received other : Json) : Bool :=
  JsonAgreement.regular received && !JsonAgreement.agrees received other

/-- `differs` holds exactly when the first value has search trees and does not agree with the
second. -/
private theorem differs_iff (received other : Json) :
    differs received other = true ↔
      JsonAgreement.Regular received ∧ ¬JsonAgreement.Agree received other := by
  rw [← JsonAgreement.regular_iff, ← JsonAgreement.agrees_iff]
  simp [differs]

/-- An end position whose tree is rooted at `line` with `column` in its right subtree: not a search
tree, since `column` comes before `line`. -/
private def irregularEnd : Json :=
  .obj ⟨⟨.inner 2 "line" (.num 1) .leaf (.inner 1 "column" (.num 1) .leaf .leaf)⟩⟩

/-- Control: `irregularEnd` differs from no value, so a check that requires a recorded end to
differ from another refuses it. -/
private theorem differs_irregular (other : Json) : differs irregularEnd other = false := by
  have irregular : JsonAgreement.regular irregularEnd = false := by decide
  simp [differs, irregular]

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
records an implicit constructor (`expandCtor`, `Lean/Elab/Structure.lean:235-246`). `Rec` has
a finding of its own: the checker reads each declaration's axioms in the kernel that replayed it,
where `Rec` reaches its constructor and so `Classical.choice`. Lean's `exportedAxiomsExt`
(`Lean/Util/CollectAxioms.lean:118-140` in the v4.34.0 toolchain source) can record no axiom for
it: it computes a module's axioms in one shared cache, and when it reaches an inductive first
through its constructor, it caches the inductive with that constructor's in-progress empty entry.
None of
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
  let same (received built : Json) : Bool := JsonAgreement.conforms received built
  let some diagnostics := (report.getObjValAs? (Array Json) "diagnostics").toOption
    | return some "no diagnostics"
  let find (name : String) : Option Json := diagnostics.find? fun d =>
    same ((d.getObjValD "arguments").getObjValD "declaration") (.str name)
  let selection (d : Json) : Json := (d.getObjValD "location").getObjValD "selectionRange"
  let kind (d : Json) : Json := (d.getObjValD "location").getObjValD "kind"
  let source (d : Json) : Json := (d.getObjValD "arguments").getObjValD "sourceDeclaration"
  let relation (d : Json) : Option Json :=
    ((d.getObjValD "related").getArrVal? 0).toOption.map (·.getObjValD "relation")
  let attributed (d owner : Json) (ownerName : String) : Bool :=
    same (source d) (.str ownerName) && same (kind d) (.str "source") &&
      same (selection d) (selection owner) &&
      (relation d).any (same · (.str "declared in module"))
  let keepsOwn (d owner : Json) (ownerName : String) (distinct : Bool) : Bool :=
    same (source d) (.str ownerName) && same (kind d) (.str "source") &&
      same (d.getObjValD "related") (.arr #[]) &&
        (!distinct || differs (selection d) (selection owner))
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
    let some owner := find ownerName | return some s!"no {ownerName} finding"
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
  unless same (source fact) .null && same (kind fact) (.str "module") do
    return some "Channel.fact, which Lean did not generate, was attributed"
  let some word := find "Word" | return some "no Word finding"
  let some ofNat := find "Word.ofNat" | return some "no Word.ofNat finding"
  unless same (source ofNat) .null && same (kind ofNat) (.str "source") &&
      differs (selection ofNat) (selection word) && same (ofNat.getObjValD "related") (.arr #[]) do
    return some "Word.ofNat, which Lean did not generate, was attributed"
  for name in #["middle._proof_8", "middle._proof_9", "Util._proof_8", "later._proof_8",
      "later.eq_7"] do
    let some d := find name | return some s!"no {name} finding"
    unless same (source d) .null && same (kind d) (.str "source") &&
        same (d.getObjValD "related") (.arr #[]) do
      return some s!"{name}, which Lean did not generate, was attributed"
  let some elaborator := diagnostics.find? fun d =>
      match Regula.RegistryCodec.parsePrintedNameJson
          ((d.getObjValD "arguments").getObjValD "declaration") with
      | .ok (.str (.str .anonymous "Channel") s) => s.startsWith "_aux_" && s.contains "termVzero"
      | _ => false
    | return some "no finding for the vzero elaborator in Channel's namespace"
  unless same (source elaborator) .null && same (kind elaborator) (.str "source") &&
      differs (selection elaborator) (selection channel) &&
      same (elaborator.getObjValD "related") (.arr #[]) do
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
  unless differs (recordedEnd "range") (recordedEnd "selectionRange") do
    return some "the range and the selection range recorded for the macro_rules definition do not \
      end at different positions"
  let some rules := diagnostics.find? fun d =>
      rulesName ((d.getObjValD "arguments").getObjValD "declaration")
    | return some "no finding for the macro_rules definition of the first syntax kind"
  let lastLine := (((rules.getObjValD "location").getObjValD "lspRange").getObjValD
    "end").getObjValD "line"
  unless same (source rules) .null && same (kind rules) (.str "source") &&
      same ((rules.getObjValD "location").getObjValD "range") (selection rules) &&
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
        | .ok json => requireAuditDocument json
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
      Regula.Filesystem.removePath .file report

/-- Controls for a decision registered from another module of its inventory (standard §7.11).
`AuditApp.DownstreamDecision` declares `downstreamCheck` without importing `Regula.Decision`, and
`AuditApp.DownstreamRegistration` imports it and writes `attribute [regula_decision]
downstreamCheck`. While no contract decides `downstreamCheck`, the project audit must report it
under RG1008; once the registering module holds its contract, the audit must accept it and record
it as registered. Both are run for two plain files and for two `module`s (`asModules`), each in a cluster of its
own. The registering `module` imports the declaring one privately, so Lean saves the registration
with that module's private data only, which the audit loads. -/
private def downstreamRegistrationControls (asModules : Bool) (sources : FilePath)
    (gate : Array String → IO ProcessResult) : IO (Array String) := do
  let declaring (asModule : Bool) : String :=
    (if asModule then "module\n\n" else "") ++
      "/-! A decision declared without the registration interface. -/\n\n" ++
      (if asModule then "@[expose] public section\n\n" else "") ++
      "/-- Whether `n` is positive. -/\ndef downstreamCheck (n : Nat) : Bool := decide (0 < n)\n"
  let contract :=
    "\n/-- `downstreamCheck` accepts exactly the positive numbers. -/\n" ++
      "theorem downstreamCheck_decides :\n" ++
      "    Regula.ExecutableContract downstreamCheck\n" ++
      "      (Regula.Decides (· = true) fun n => 0 < n) :=\n" ++
      "  ⟨{ sound := fun _ accepted => of_decide_eq_true accepted\n" ++
      "     accepted := ⟨1, by decide⟩\n" ++
      "     complete := fun _ holds => decide_eq_true holds\n" ++
      "     refused := ⟨0, by decide⟩ }⟩\n"
  let registering (asModule decided : Bool) : String :=
    (if asModule then "module\n\n" else "") ++ "import AuditApp.DownstreamDecision\n" ++
      (if decided then "import Regula.Contract\n" else "") ++
      (if asModule then "meta import Regula.Decision\n" else "import Regula.Decision\n") ++
      "\n/-! Registers the decision the imported module declares. -/\n" ++
      (if decided then contract else "") ++ "\nattribute [regula_decision] downstreamCheck\n"
  let registration := sources / "AuditApp" / "DownstreamRegistration.lean"
  let arguments := #["--incremental", "--verbose"]
  let mut failures := #[]
  for (form, asModule) in #[("files", false), ("modules", true)].filter (·.2 == asModules) do
    let found ← withNewFile (sources / "AuditApp" / "DownstreamDecision.lean")
        (declaring asModule) do
      let unmet ← withNewFile registration (registering asModule false) do
        return expectedFailure s!"downstream-registration-{form}" (← gate arguments)
          #["RG1008", "downstreamCheck (def)"]
      let met ← withNewFile registration (registering asModule true) do
        let result ← gate arguments
        if result.succeeded && result.output.contains
            "downstreamCheck (def) type=Nat → Bool axioms=[] -> kernel-only decision-result=other"
        then pure none
        else pure <| some s!"structural/downstream-contract-{form}: expected the registered \
          decision accepted and recorded:\n{result.output}"
      return #[unmet, met].filterMap id
    failures := failures ++ found
  return failures

/-- Structural mutation cluster: controls for several copies of one name (`group` 0 to 2,
`duplicateAdmissionControls`), or for a decision registered from another module, as plain files
(`group` 3) or as `module`s with fresh-checker coverage of an added module (`group` 4), then
the restored control in fresh mode (empty-output elaboration of the copy), so the harness's
green-restore evidence covers stale-artifact freedom, not only incremental rebuilds. -/
private unsafe def structuralPartD (layout : SourceLayout) (group : Nat) (repo copy : FilePath) :
    IO (Array String) := do
  let sources := copy / layout.relativeDir
  let failures ← IO.mkRef (#[] : Array String)
  let gate (args : Array String := #["--incremental"]) :=
    runBinaryFrom repo copy "axiomGate" args
  if group < 3 then
    for failure in ← duplicateAdmissionControls group sources copy (fun args => gate args) do
      failures.modify (·.push failure)
  else
    for failure in ← downstreamRegistrationControls (group == 4) sources (fun args => gate args) do
      failures.modify (·.push failure)
  if group == 4 then
    withNewFile (sources / "AuditApp" / "UnimportedSafe.lean")
        "namespace AuditApp.UnimportedSafe\ndef value : Nat := 1\nend AuditApp.UnimportedSafe\n" do
      let plan ← runBinaryFrom repo copy "freshChecker" #["--plan-only"]
      if !plan.succeeded || !plan.output.contains "AuditApp.UnimportedSafe" then
        failures.modify
            (·.push s!"structural/fresh-coverage: added module was omitted:\n{plan.output}")
  restoredControl repo copy failures
  failures.get

/-- Each restricted-domain/universe mutation starts from its own passing source
and restores that source through a fresh public file audit. `--file` creates and
removes a separate elaboration directory for every invocation. The fixed
negative sweep additionally asserts the exact violation set. A cluster runs the control of one
`fixture`. -/
private def correspondenceRestoration (layout : SourceLayout) (fixture : String)
    (repo scratch : FilePath) : IO (Array String) := do
  let failures ← IO.mkRef (#[] : Array String)
  let controls := #[
    ("RepeatedCorrespondence", "Nat := _n\n", "Nat := _m\n"),
    ("OmittedCorrespondence", "Nat := m\n", "Nat := m + _n\n"),
    ("SpecializedUniverseCorrespondence", "{α : Type}", "{α : Type u}")].filter (·.1 == fixture)
  if controls.isEmpty then return #[s!"correspondence/{fixture}: no such control"]
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
that equality and leaves only a theorem requiring False. The positive (`mutation` false) and the
mutation with its fresh restored control (`mutation` true) run in clusters of their own; a fresh
gate reads no build output of its project, so neither reads what the other built. -/
private unsafe def structuralCorrespondence (layout : SourceLayout) (mutation : Bool)
    (repo copy : FilePath) : IO (Array String) := do
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
  withReplacedFile lakefile
      (originalLakefile ++ "\n" ++
        observedTargetLean .library "CorrespondenceControl" (own := true)) do
    withReplacedFile manifest checkedManifest do
      withNewFile source positive do
        if !mutation then
          let green ← gate
          if !green.succeeded || !green.output.contains "kernel-defeq" then
            failures.modify
                (·.push s!"correspondence/control: expected checked PASS:\n{green.output}")
        else
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

/-- One cluster of controls: its own isolated project below `scratch`, prepared by `prepare`
and built, then the controls of `part` in it. A baseline that does not build is the cluster's
failure. -/
private def cluster (repo scratch : FilePath) (name : String) (prepare : FilePath → IO Unit)
    (targets : Array String) (part : FilePath → FilePath → IO (Array String)) :
    String × IO (Array String) :=
  (name, do
    let copy := scratch / s!"copy-{name}"
    let setup ← loggedPhase s!"cluster {name} setup" do
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
    loggedPhase s!"{label} {name}" run
  return results.foldl (· ++ ·) #[]

/-- The structural mutation clusters, each in its own isolated project, so no two concurrent
Lake builds ever write one build directory, and each with its shard. Each cluster's project is
the structural project; the self-hosted clusters' are copies of the repository. The positive is
alone in `selfHostedShard`, and the self-hosted cluster is in `selfHostedRestoredShard`; both
record their fresh inputs in `inputs`, for the caller's comparison after the queue. The other
clusters are cut from four serial chains (`a` to `d`) at
points where each chain has restored every file it changed, and each cut ends with a restored
control of its own (`restoredControl`, or the fresh restored gate of its last mutation). The
other shards divide them, with the controls of `runStructural`, so that the sums of their
observed times are similar; the longest observed are first. -/
private unsafe def structuralClusters (layout : SourceLayout) (repo scratch : FilePath)
    (inputs : SelfHostedInputs) : List (Fin structuralShards × String × IO (Array String)) :=
  let part (name : String) (run : FilePath → FilePath → IO (Array String)) :=
    projectCluster layout repo scratch name run
  [(selfHostedShard, "self-hosted-positive",
      structuralSelfHostedPositive repo (scratch / "copy-self-hosted-positive") inputs),
    (structuralShard 1, part "c-update" (structuralPartC layout 1)),
    (structuralShard 2, part "c-contract" (structuralPartC layout 2)),
    (structuralShard 3, part "d-realized" (structuralPartD layout 0)),
    (selfHostedRestoredShard, cluster repo scratch "self-hosted"
      (fun copy => do prepareSelfHosted repo copy; seedModuleArtifacts layout repo copy)
      (applicationTargets layout) (structuralSelfHosted layout · · inputs)),
    (structuralShard 4, part "b-executables" (structuralPartB layout true)),
    (structuralShard 1, part "d-modules" (structuralPartD layout 4)),
    (structuralShard 2, part "a-admission" (structuralPartAAdmission layout false)),
    (structuralShard 3, part "a-imported-admission" (structuralPartAAdmission layout true)),
    (structuralShard 2, part "a-contamination" (structuralPartA layout true)),
    (structuralShard 3, part "a-discovery" (structuralPartA layout false)),
    (structuralShard 4, part "c-manifest" (structuralPartC layout 0)),
    (structuralShard 2, part "d-unchecked" (structuralPartD layout 1)),
    (structuralShard 3, part "d-circular" (structuralPartD layout 2)),
    (structuralShard 4, part "d-files" (structuralPartD layout 3)),
    (structuralShard 2, part "b-library" (structuralPartB layout false))]

/-- Structural qualification: the mutation clusters (`structuralClusters`) on `jobs` workers,
then the comparison of the self-hosted fresh inputs (`selfHostedIdentity`). -/
private unsafe def structuralQualification (layout : SourceLayout) (repo scratch : FilePath)
    (jobs : Nat)
    : IO (Array String) := do
  let inputs ← SelfHostedInputs.new
  let clusters ← qualifyItems "structural" jobs
    ((structuralClusters layout repo scratch inputs).map (·.2)).toArray
  return clusters ++ (← selfHostedIdentity inputs)

/-- The execution shard of the compiler-path case `name`, chosen so that the sums of the observed
times of the shards' controls are similar. A case this list does not name runs in the first. -/
private def compilerPathShard : String → Fin executionShards
  | "imported" | "csimp-implemented-by" | "partial-target"
    | "overwritten-inlined-implementation" => executionShard 0
  | "init-module-origin" | "implemented-by-csimp" | "partial-helper" => executionShard 1
  | "lean-module-origin" | "unsupported-history-evaluator" | "unsafe-target" | "overwritten-csimp"
    | "replacement-cycle" => executionShard 2
  | "module-system" | "csimp-partial-implementation" | "chained" | "local-csimp"
    | "proof-valued-csimp" => executionShard 3
  | _ => executionShard 0

/-- Execution qualification: the correspondence controls, in clusters whose projects are the
structural project (the positive and the mutation of the conditional correspondence, and each of
the three restricted-domain and universe restorations), and the compiler-path cases, each phase
of each case in a scratch project of its own below `scratch`. All run on `jobs` workers with no
batch barrier between them, the longest observed first. Each control has its shard
(`compilerPathShard` for the cases). With `shard`, only that shard's controls run. Returns the
names of the controls run and their failures. -/
private unsafe def executionQualification (layout : SourceLayout) (repo scratch : FilePath)
    (jobs : Nat) (shard : Option (Fin executionShards) := none) :
    IO (Array String × Array String) := do
  let compilerPaths := scratch / "compiler-paths"
  IO.FS.createDirAll compilerPaths
  let restoration (index : Fin executionShards) (fixture : String) :=
    (index, projectCluster layout repo scratch s!"restoration-{fixture}"
      (correspondenceRestoration layout fixture))
  let cases := (CompilerPaths.qualifications repo compilerPaths).toList.map fun (name, run) =>
    (compilerPathShard name, name, run)
  -- The four cases observed to take 60 s or more start first, one in each shard.
  let long := ["imported", "init-module-origin", "lean-module-origin", "module-system"]
  let named := fun (cases : List (Fin executionShards × String × IO (Array String))) =>
    cases.map fun (index, name, run) => (index, s!"compiler path {name}", run)
  let controls : List (Fin executionShards × String × IO (Array String)) :=
    named (cases.filter (long.contains ·.2.1)) ++
    [(executionShard 3, projectCluster layout repo scratch "correspondence-mutation"
        (structuralCorrespondence layout true))] ++
    restoration (executionShard 0) "RepeatedCorrespondence" ::
    restoration (executionShard 1) "OmittedCorrespondence" ::
    restoration (executionShard 2) "SpecializedUniverseCorrespondence" ::
    [(executionShard 1, projectCluster layout repo scratch "correspondence"
        (structuralCorrespondence layout false))] ++ named (cases.filter (!long.contains ·.2.1))
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

/-- A part of the clean-checkout environment controls (`fenceEnvironmentQualification`). -/
private inductive FenceEnvironmentPart where
  /-- A documentation fence that imports an owned module, audited by `docFenceAudit`. -/
  | docFences
  /-- `axiomGate --file` on a file that imports the owned library. -/
  | fileMode
  /-- `freshChecker` on a two-root control surface whose workspace provides a failing
  `leanchecker`. -/
  | freshChecker
  deriving DecidableEq

/-- Every part of the clean-checkout environment controls. -/
private def FenceEnvironmentPart.all : List FenceEnvironmentPart :=
  [docFences, fileMode, freshChecker]

/-- `FenceEnvironmentPart.all` lists every part. -/
private theorem FenceEnvironmentPart.mem_all (part : FenceEnvironmentPart) :
    part ∈ FenceEnvironmentPart.all := by
  cases part <;> decide

/-- `FenceEnvironmentPart.all` lists no part twice. -/
private theorem FenceEnvironmentPart.all_nodup : FenceEnvironmentPart.all.Nodup := by
  decide

/-- The name of a part in its phase, scratch directory and failures. -/
private def FenceEnvironmentPart.label : FenceEnvironmentPart → String
  | docFences => "doc-fences"
  | fileMode => "file-mode"
  | freshChecker => "fresh-checker"

/-- The controls of a part, as the summary line of a run names them. -/
private def FenceEnvironmentPart.controls : FenceEnvironmentPart → String
  | docFences => "clean-checkout doc fences"
  | fileMode => "--file"
  | freshChecker => "freshChecker with no prior build on a two-root control surface whose \
      workspace provides a failing leanchecker"

/-- Run the repository's tool `name` in `dir` with `LEAN_PATH` scrubbed. -/
private def runScrubbed (repo dir : FilePath) (name : String) (args : Array String) :
    IO ProcessResult := do
  runProcess dir (← toolPath repo name).toString args scrubbedLeanPathEnv

/-- The control of `part` in the copied repository `dir`, which has no `.lake/build`, adding each
failure to `failures`. -/
private unsafe def fenceEnvironmentControl (layout : SourceLayout) (repo : FilePath)
    (failures : IO.Ref (Array String)) : FenceEnvironmentPart → FilePath → IO Unit
  | .docFences, dir => do
    let corpus := dir / "fence-corpus"
    IO.FS.createDirAll corpus
    IO.FS.writeFile (corpus / "owned-import.md")
      "```lean\nimport AuditApp.Limiter\n\ntheorem fence_uses_owned : 1 = 1 := rfl\n```\n"
    let result ← runScrubbed repo dir "docFenceAudit"
      #["--jobs", "4", "--docs-root", corpus.toString]
    if !result.succeeded || !result.output.contains s!"{Documentation.positiveSummary}=1/1" then
      failures.modify (·.push
        s!"fence-env/doc-fences: fence importing an owned module failed from unbuilt \
          state:\n{result.output}")
  | .fileMode, dir => do
    let result ← runScrubbed repo dir "axiomGate"
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
  -- `leanchecker --fresh` on the real claimed graph replays Init and Lean
  -- once per root, which is the separate optional serialized-graph
  -- claim (`scripts/verify.sh serialized-graph`), not a clean-checkout property.
  | .freshChecker, dir => do
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
      "\n" ++ observedTargetLean .library "FreshControl"
        "  globs := #[.submodules `FreshControl]\n" (own := true))
    let manifest := dir / "foundation_manifest.json"
    writeJson manifest (freshControlManifest (← parsedManifest manifest))
    -- A counterexample aid at the process boundary: the workspace provides a `leanchecker` in the
    -- root package's binary directory, which `lake env` puts first on `PATH`. It is a link to the
    -- toolchain's own `lean` (`Regula.Toolchain.program`), which refuses the `--fresh` option, and
    -- the control first runs it with the arguments a `leanchecker` gets for each root below and
    -- requires each run to fail, so an accepted run below did not run it.
    let failing ← Regula.Toolchain.program "lean"
    let workspaceBin := dir / ".lake" / "build" / "bin"
    IO.FS.createDirAll workspaceBin
    let plantedPath := workspaceBin / "leanchecker"
    let planted ← runProcess dir "ln" #["-s", failing.toString, plantedPath.toString]
    if !planted.succeeded then throw <| IO.userError planted.output
    unless (← IO.FS.realPath plantedPath) == (← IO.FS.realPath failing) do
      throw <| IO.userError "fence-env/fresh-checker: the planted leanchecker does not resolve \
        to the toolchain's lean"
    for root in expected do
      let refused ← runProcess dir plantedPath.toString #["--fresh", root]
      if refused.succeeded then
        throw <| IO.userError s!"fence-env/fresh-checker: the planted leanchecker accepted \
          --fresh {root}, so it cannot show that freshChecker did not run it"
    let reportPath := dir / "fresh-report.json"
    let result ← runScrubbed repo dir "freshChecker" #["--json-out", reportPath.toString]
    if !result.succeeded then
      failures.modify (·.push
        s!"fence-env/fresh-checker: freshChecker failed from unbuilt state:\n{result.output}")
    else
      -- Reconcile the actual run against the modules written above: each is a
      -- maximal root, and every root's successful check must cover it.
      let report ← readJson reportPath
      let read {α : Type} (decoded : Except String α) := IO.ofExcept (RegulaQualification.Member.within reportPath decoded)
      let status ← read (RegulaQualification.Member.text report "status")
      let modules ← read (memberStrings report "modules")
      let roots ← read (memberStrings report "roots")
      let checks ← read (RegulaQualification.Member.array report "checks")
      let mut checked : Array String := #[]
      for check in checks do
        let exitCode ← read (RegulaQualification.Member.get Nat check "exitCode")
        if exitCode != 0 then
          failures.modify (·.push "fence-env/fresh-checker: a root was not checked successfully")
        let covered ← read (memberStrings check "coveredModules")
        checked := checked ++ covered
      if status != "completed" || checks.size != expected.size
          || uniqueSorted modules != uniqueSorted expected || uniqueSorted roots !=
              uniqueSorted expected
          || uniqueSorted checked != uniqueSorted expected then
        failures.modify (·.push
          s!"fence-env/fresh-checker: accepted root checks did not cover \
            exactly {expected}:\n{result.output}")

/-- Clean-checkout environment controls: each public checker that builds
project-owned modules must itself build the claimed libraries when the main
build directory is empty, instead of relying on a prior `lake build`. Each
control starts from a copied repository whose `.lake/build` holds exactly the files that
`prepareScratchRepo` reports it placed, the running Regula's observer library with its trace and
hash: no module output. `--file` and `freshChecker` build the copy's claimed libraries in place, and
their audit admits only a plugin with that library's bytes (`Observer.matchingPlugins`). The
freshChecker control then gives its workspace a `leanchecker` that fails, which an accepted run
never ran. Only the parts in `parts` run (`fenceEnvironmentParts`). -/
private unsafe def fenceEnvironmentQualification (layout : SourceLayout) (repo scratch : FilePath)
    (parts : List FenceEnvironmentPart) : IO (Array String) := do
  let failures ← IO.mkRef (#[] : Array String)
  for part in parts do
    let name := part.label
    loggedPhase s!"clean-checkout/{name}" do
      let dir := scratch / name
      IO.FS.createDirAll dir
      let placed ← prepareScratchRepo repo dir
      let build := dir / ".lake" / "build"
      let outputs ← if ← Regula.Filesystem.isPresent build then
          Regula.Filesystem.Construction.walkDirectory build
        else pure #[]
      let mut unexpected := #[]
      for path in outputs do
        unless (← Regula.Filesystem.isDirectory path) || placed.contains path do
          unexpected := unexpected.push path
      unless unexpected.isEmpty do
        failures.modify (·.push s!"fence-env/{name}: setup unexpectedly has build output \
          other than the placed observer library: {unexpected}")
      fenceEnvironmentControl layout repo failures part dir
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
  "name = \"widget_adopter\"\n" ++ observerPluginToml ++ "\n" ++
  "[leanOptions]\nautoImplicit = false\nrelaxedAutoImplicit = false\nlinter.missingDocs = \
    true\n\n" ++
  "[[require]]\nname = \"regula\"\n" ++
  s!"path = \"{checkerPath}\"\n\n" ++
  observedTargetToml .library "Widget" "globs = [\"Widget\", \"Widget.+\"]\n" ++
  "\n" ++
  observedTargetToml .executable "widget_tool" "root = \"Main\"\n"

private def adopterLeanLakefile (checkerPath : String) : String :=
  "import Lake\nopen Lake DSL\n\n" ++
  "package «widget_adopter» where\n" ++
  observerPluginLean ++
  "  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`linter.missingDocs, \
    true⟩]\n\n" ++
  s!"require «regula» from \"{checkerPath}\"\n\n" ++
  "@[default_target]\n" ++
  observedTargetLean .library "«Widget»" "  globs := #[.andSubmodules `Widget]\n" ++ "\n" ++
  observedTargetLean .executable "«widget_tool»" "  root := `Main\n"

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

/-- A variant of the external-adopter controls (`adopterQualification`). -/
private inductive AdopterVariant where
  /-- A `lakefile.toml` adopter that requires the checker by absolute path. It also runs the
  unlisted-module and fresh-plan controls. -/
  | toml
  /-- A `lakefile.lean` adopter that requires the checker by absolute path. -/
  | lean
  /-- A `lakefile.toml` adopter that requires the checker by relative path. -/
  | relative
  deriving DecidableEq

/-- Every variant of the external-adopter controls. -/
private def AdopterVariant.all : List AdopterVariant := [toml, lean, relative]

/-- `AdopterVariant.all` lists every variant. -/
private theorem AdopterVariant.mem_all (variant : AdopterVariant) :
    variant ∈ AdopterVariant.all := by
  cases variant <;> decide

/-- `AdopterVariant.all` lists no variant twice. -/
private theorem AdopterVariant.all_nodup : AdopterVariant.all.Nodup := by
  decide

/-- The name of a variant in its scratch directory and failures. -/
private def AdopterVariant.label : AdopterVariant → String
  | toml => "toml"
  | lean => "lean"
  | relative => "relative"

/-- External adopter qualification: a scratch project that requires the
checker package by local path in each lakefile format, with one conforming
library, a standalone `Main` executable root, and empty exclusion arrays. Each
scratch project is a Git repository of its own, so the checker package is a
trusted dependency whose own `Main` executable root is not a second provider.
The scratch projects contain nothing named `Audit` or `Fixtures` and share only
the pinned dependency checkouts. The `relative` variant requires the checker
by a relative path (the form a project nested inside another repository
uses), which the §7.3 isolated copy must re-anchor to the original project;
its setup verifies that the relative path really names this repository. Only the variants in
`parts` run (`adopterParts`). -/
private unsafe def adopterQualification (repo scratch : FilePath) (parts : List AdopterVariant) :
    IO (Array String) := do
  let failures ← IO.mkRef (#[] : Array String)
  let depth := (← IO.FS.realPath scratch).components.length + 1 -
    (← IO.FS.realPath repo).components.length
  for variant in parts do
    let label := variant.label
    let (format, checkerDir, lakefileText) : String × String × (String → String) :=
      match variant with
      | .toml => ("toml", repo.toString, adopterTomlLakefile)
      | .lean => ("lean", repo.toString, adopterLeanLakefile)
      | .relative => ("toml", "/".intercalate (List.replicate depth ".."), adopterTomlLakefile)
    let adopter := scratch / label
    IO.FS.createDirAll (adopter / "Widget")
    if !(FilePath.mk checkerDir).isAbsolute then
      let resolved ← IO.FS.realPath (adopter / checkerDir)
      if resolved != (← IO.FS.realPath repo) then
        throw <| IO.userError <|
          s!"adopter/{label}/setup: relative checker path {checkerDir} resolves to {resolved}, \
            not {repo}"
    IO.FS.writeFile (adopter / s!"lakefile.{format}") (lakefileText checkerDir)
    Regula.Filesystem.copyFile (repo / "lean-toolchain") (adopter / "lean-toolchain")
    IO.FS.writeFile
        (adopter / "Widget.lean")
            "import Widget.Extra\n/-! Re-export the arithmetic identity in Widget.Extra. -/\n"
    IO.FS.writeFile (adopter / "Widget" / "Extra.lean")
      "/-! Closed natural-number arithmetic identity. -/\ntheorem widget_extra_thm : 1 + 1 = 2 := \
        rfl\n"
    IO.FS.writeFile (adopter / "Main.lean") "/-! Standalone no-effect IO entrypoint. -/\n/-- Does \
      nothing. -/\ndef main : IO Unit := pure ()\n"
    IO.FS.writeFile (adopter / "foundation_manifest.json") (adopterManifestText ++ "\n")
    Lake.pinAdopter repo adopter
    -- An adopter is a repository of its own, so `regula`, which it requires from this checkout, is
    -- a dependency in a different Git work tree, which the audit trusts, as an adopter's is.
    let initialized ← runProcess adopter "git" #["init", "-q"]
    if !initialized.succeeded then
      throw <| IO.userError s!"adopter/{label}/setup: git init failed: {initialized.output}"
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
    if variant == .toml then
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

/-- The fixtures a run of a partition of `shards` shards that divides the fixtures among them in
turn checks: each fixture in the shard of its position in `fixtures`, which `loadFixtureManifest`
sorts by module name (`fixtureShard`), every fixture without `shard`. -/
private def fixturesOfShard {shards : Nat} (positive : 0 < shards) (shard : Option (Fin shards))
    (fixtures : Array FixtureSpec) : Array FixtureSpec :=
  ((inShard shard (fixtures.toList.mapIdx fun position fixture =>
    (fixtureShard position positive, fixture))).map (·.2)).toArray

/-- The shard of the scanner controls and the in-process fence corpus: the last. -/
private def fenceCorpusShard : Fin fixturesShards := ⟨fixturesShards - 1, by decide⟩

/-- In-process fixture, scanner, and fence-corpus controls. Imports
remain serialized, and transcript workers finish before parent imports. With `shard`, the
fixtures of that shard (`fixturesOfShard`) are checked, and the scanner controls and the fence
corpus run in their shard alone (`fenceCorpusShard`).

The recursion-helper fixtures among them (the positive recursion modules and the
`…UnsafeRecForge` mutations of `Fixtures/fixtures.json`) test an external boundary: the observing
pass of the comparison and the regeneration, against the pinned toolchain. They are not tests of
the comparison's rules: `RegulaPolicy.Erasure.equalWithin_iff` proves the executed comparison
against its relation for every pair of terms and every observation, and no fixture stands in for
that theorem. -/
private unsafe def runFixtures (repo : FilePath) (jobs : Nat) (shard : Option (Fin fixturesShards))
    (fixtures : Array FixtureSpec) (failures : IO.Ref (Array String)) : IO Unit := do
  let inventory ← Lake.surfaceInventory repo
  let selected := fixturesOfShard (by decide) shard fixtures
  withScratch repo "checker-fixtures" fun scratch => do
    let fixtureResults ← loggedPhase "in-process fixtures" <|
      fixtureVerdicts repo scratch jobs selected inventory.leanPath
    for result in fixtureResults do appendFailure failures result
    IO.println (s!"self-test fixtures: " ++
      (if fixtureResults.all (·.isNone) then "PASS" else "FAIL") ++
      s!" ({selected.size} in one process, one environment load per import closure)" ++
      shardNote shard)
  if runsIn shard fenceCorpusShard then
    for failure in scannerQualification do failures.modify (·.push failure)
    withScratch repo "checker-fence-corpus" fun scratch => do
      let corpus ← loggedPhase "in-process fence corpus" <|
        fenceCorpusQualification repo scratch jobs
      for failure in corpus do failures.modify (·.push failure)
      IO.println <| "self-test Markdown: " ++
        (if corpus.isEmpty then "PASS" else "FAIL") ++
        s!" (scanner controls + {(fenceCorpusCases "" "").size} in-process corpus cases)"

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
      else Regula.Filesystem.removePath .file part
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
        if isPresent then IO.FS.writeBinFile part frozenBytes
        else Regula.Filesystem.removePath .file part
      let mutations : Array (String × IO Unit) :=
        if isPresent then #[("changed", IO.FS.writeBinFile part (ByteArray.mk #[1, 2, 4])),
          ("removed", Regula.Filesystem.removePath .file part)]
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
  Regula.Filesystem.copyFile (repo / "lean-toolchain") (project / "lean-toolchain")
  IO.FS.writeFile (project / "lakefile.toml") <|
    "name = \"library_cycle_control\"\n" ++ observerPluginToml ++
      "[leanOptions]\nautoImplicit = false\n" ++
      "relaxedAutoImplicit = false\nlinter.missingDocs = true\n" ++
      observedTargetToml .library "Left" "globs = [\"Left.+\"]\n" ++
      observedTargetToml .library "Right" "globs = [\"Right.+\"]\n" ++
      regulaRequireToml repo
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
  -- This generated configuration has no requirements; update creates only its initial manifest.
  let locked ← runProcess project "lake" #["update"] scrubbedLeanPathEnv
  unless locked.succeeded do return #[s!"library-cycle/setup: lake update failed:\n{locked.output}"]
  let result := output / "result.json"
  let gate ← runProcess project (← toolPath repo "axiomGate").toString
    #["--project", project.toString, "--json-out", result.toString] scrubbedLeanPathEnv
  unless gate.succeeded do return #[s!"library-cycle/accepted: expected PASS:\n{gate.output}"]
  let modules := #["Left.Base", "Left.Top", "Right.Base", "Right.Top"]
  let json ← requireAuditDocument (← IO.ofExcept (Json.parse (← IO.FS.readFile result)))
  let read {α : Type} (decoded : Except String α) := IO.ofExcept (RegulaQualification.Member.within result decoded)
  let surfaces ← read do RegulaQualification.Member.array (← RegulaQualification.Member.object json "scope") "surfaces"
  let mut found : Array (String × Array String × Array String × Array (String × String)) := #[]
  for surface in surfaces do
    let library ← read (RegulaQualification.Member.text surface "library")
    let admission ← read do RegulaQualification.Member.object (← RegulaQualification.Member.object surface "report") "admission"
    let reused ← read (RegulaQualification.Member.get (Array String) admission "reused")
    let required ← read (RegulaQualification.Member.get (Array (String × String)) admission "required")
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

/-- Observer identity control: a gate admits only the observer library that it read at its start
(`Observer.running`), even when its audit's build writes other bytes at the very path it read.

A tool package below the scratch directory holds a copy of the running Regula's `axiomGate` (a
hard link, so the gate's real path, and with it the place it reads its observer from,
`Observer.runningPackageDir`, is the tool's), the running observer library placed in its build
directory (`Observer.placeRunning`), and a copy of the repository's sources. Each compiled module
of the repository other than the observer's is a symbolic link to the repository's: no module that
the audit builds reaches them, since the project's module imports nothing and the observer's modules
import only Lean. A project that requires `regula` from the tool loads the tool's library as a
plugin.

- Rebuilt in place: the observer source gains a public definition, so its C file and object change
  (`Module.cFacetConfig`, `Lake/Build/Module.lean` lines 1184 to 1198), and Lake links the
  library again at its `sharedLibFile`, the path the gate read at its start
  (`LeanLib.recBuildShared`, `Lake/Build/Library.lean` lines 128 to 152), with other bytes. The
  audit must refuse the project under RG2003. An admission by the library's path, or by an
  identity read after the build, admits that library, so this control fails under either.
- Restored: the source and the placed library, trace and hash put back, Lake reuses the library,
  and the audit must accept the project. -/
private def observerIdentityControl (repo : FilePath) : IO (Array String) :=
  withScratch repo "observer-identity" fun dir => withScratch repo "observer-identity-result"
      fun output => do
  let tool := dir / "tool"
  let project := dir / "project"
  let link (source target : FilePath) : IO Unit := do
    let linked ← runProcess dir "ln" #["-s", source.toString, target.toString]
    unless linked.succeeded do
      throw <| IO.userError s!"observer identity: cannot link {target}: {linked.output}"
  let observerEntry (name : String) : Bool :=
    name.startsWith Observer.observerLibrary.toString
  IO.FS.createDirAll (tool / "lean")
  for file in #["lakefile.lean", "lean-toolchain", "lake-manifest.json"] do
    IO.FS.writeBinFile (tool / file) (← IO.FS.readBinFile (repo / file))
  -- The sources are copies: the audit admits a dependency's source only at a real path inside the
  -- package (`checkSource`).
  let sources := (repo / "lean").normalize.components.length
  for path in ← Regula.Filesystem.Construction.walkDirectory (repo / "lean") do
    if ← Regula.Filesystem.isDirectory path then continue
    let destination :=
      (path.normalize.components.drop sources).foldl (· / FilePath.mk ·) (tool / "lean")
    if let some parent := destination.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile destination (← IO.FS.readBinFile path)
  let compiled := tool / ".lake" / "build" / "lib" / "lean"
  IO.FS.createDirAll compiled
  for entry in ← Regula.Filesystem.Construction.listDirectory
      (repo / ".lake" / "build" / "lib" / "lean") do
    unless observerEntry entry.fileName do link entry.path (compiled / entry.fileName)
  Observer.placeRunning tool
  let snapshot ← Observer.running
  let library := tool / ".lake" / "build" / "lib" / snapshot.fileName
  let bin := tool / ".lake" / "build" / "bin"
  IO.FS.createDirAll bin
  let gate := bin / "axiomGate"
  let hardLinked ← runProcess dir "ln" #[(← toolPath repo "axiomGate").toString, gate.toString]
  unless hardLinked.succeeded do
    return #[s!"observer-identity/setup: cannot link the gate: {hardLinked.output}"]
  IO.FS.createDirAll project
  IO.FS.writeFile (project / "lean-toolchain") (← IO.FS.readFile (repo / "lean-toolchain"))
  IO.FS.writeFile (project / "lakefile.toml") <|
    "name = \"observer_identity_control\"\n" ++ observerPluginToml ++
      "[leanOptions]\nautoImplicit = false\n" ++
      "relaxedAutoImplicit = false\nlinter.missingDocs = true\n" ++
      observedTargetToml .library "Example" ++ regulaRequireToml tool
  IO.FS.writeFile (Manifest.defaultPath project) <|
    "{\"schema-version\":2,\"surfaces\":[{\"library\":\"Example\",\"executables\":[]," ++
      "\"claim\":\"kernel-only\",\"execution\":\"report\"," ++
      "\"rationale\":\"Observer identity control\"}]," ++
      "\"excluded-libraries\":[],\"excluded-executables\":[]}"
  IO.FS.writeFile (project / "Example.lean")
    "/-! Observer identity control. -/\n\n/-- A value. -/\ndef value : Nat := 1\n"
  -- The project is a Git work tree of its own, so the tool, in the repository's, is a
  -- dependency the fresh copy loads in place.
  let initialized ← runProcess project "git" #["init", "-q"]
  let locked ← runProcess project "lake" #["update"] scrubbedLeanPathEnv
  unless initialized.succeeded && locked.succeeded do
    return #[s!"observer-identity/setup: {initialized.output}{locked.output}"]
  let audit (name : String) : IO ProcessResult :=
    runProcess project gate.toString
      #["--project", project.toString, "--json-out", (output / s!"{name}.json").toString]
      scrubbedLeanPathEnv
  let mut failures := #[]
  let observerSource := tool / "lean" / "RegulaObserver.lean"
  let observerText ← IO.FS.readFile observerSource
  IO.FS.writeFile observerSource (observerText ++
    "\n/-- A changed observer module. -/\ndef changedObserverModule : Nat := 1\n")
  let rebuilt ← audit "rebuilt"
  if (← IO.FS.readBinFile library).data == snapshot.library.data then
    failures := failures.push s!"observer-identity/rebuilt-in-place: the build did not write other \
      bytes at {library}:\n{rebuilt.output}"
  else if let some failure := expectedFailure "observer-identity/rebuilt-in-place" rebuilt
      #["RG2003", "not observed: Regula's elaboration observer was not among the plugins"] then
    failures := failures.push failure
  IO.FS.writeFile observerSource observerText
  Observer.placeRunning tool
  let restored ← audit "restored"
  unless restored.succeeded do
    failures := failures.push s!"observer-identity/restored: expected PASS:\n{restored.output}"
  unless (← IO.FS.readBinFile library).data == snapshot.library.data do
    failures := failures.push s!"observer-identity/restored: the build wrote other bytes at \
      {library}, so the restored control did not run on the placed library"
  return failures

/-- External-boundary control for reuse with shared copies, where Lean's realization and import
of several copies of one name, the report workers and the kernel are the external mechanism
(`Admission.copiesAgree_iff`, `Admission.referencesWithin_iff` and `Admission.ownedAgrees_iff`
state the decisions, and `Admission.agreesIn_iff` when copies agree). `Lib.Left` and `Lib.Right`
do not import each other. Each realizes its own copy of `positive.eq_1` of `Lib.Base`, and the two
copies are identical. Each also realizes its own copy of `classify.eq_2`, whose proof uses the
match equation Lean realizes privately in that module, and uses it only by that name. The two
copies differ only in those private names, and the reuse this control expects requires
`Admission.agrees` to accept the name, through `Admission.uniformUpToPrivate` and
`Admission.declaredOwned`. `Lib.Near` and `Lib.Far` each realize a copy of `grade.eq_2` the same
way, but their own theorems also refer to the private match equation, so a check of one in an
environment that holds the other module's copy would read the private names of both modules, and
the copies do not agree. `Lib.Odd` and
`Lib.Even` each declare `sharedFact` with a different proof. `Lib.Up` and `Lib.Down` each declare
`helperFact` through a private `helper` with a different proof, so exchanging the names of
`helper` does not relate its two copies. `App.Main` imports the eight. The fresh audit must
accept; the `Lib` environment replays its nine modules, with both copies of each name, and lists
only `Lib.Near`, `Lib.Far`, `Lib.Odd`, `Lib.Even`, `Lib.Up` and `Lib.Down` as `shared`; the `App`
environment reuses `Lib.Base`, `Lib.Left` and `Lib.Right`, though it attributes the copies of
`Lib.Right` to `Lib.Left`, and replays the other six and `App.Main`, again listing those six as
`shared`. Each constant that reaches `Lean.reduceBool` reaches the axiom `Lean.trustCompiler`,
which no claim admits, so the exclusion of native reduction has its witnesses in `Admission`. -/
private def sharedCopiesControl (repo : FilePath) : IO (Array String) :=
  withScratch repo "shared-copies-control" fun project =>
    withScratch repo "shared-copies-result" fun output => do
  IO.FS.writeFile (project / "lean-toolchain") (← IO.FS.readFile (repo / "lean-toolchain"))
  IO.FS.writeFile (project / "lakefile.toml") <|
    "name = \"shared_copies_control\"\n" ++ observerPluginToml ++
      "[leanOptions]\nautoImplicit = false\n" ++
      "relaxedAutoImplicit = false\nlinter.missingDocs = true\n" ++
      observedTargetToml .library "Lib" "globs = [\"Lib.+\"]\n" ++
      observedTargetToml .library "App" "globs = [\"App.+\"]\n" ++
      regulaRequireToml repo
  let surface (library : String) : String :=
    "{\"library\":\"" ++ library ++ "\",\"executables\":[],\"claim\":\"standard-logical\"," ++
      "\"execution\":\"report\",\"rationale\":\"Shared copies control\"}"
  IO.FS.writeFile (Manifest.defaultPath project) <|
    "{\"schema-version\":2,\"surfaces\":[" ++ surface "Lib" ++ "," ++ surface "App" ++
      "],\"excluded-libraries\":[],\"excluded-executables\":[]}"
  IO.FS.createDirAll (project / "Lib")
  IO.FS.createDirAll (project / "App")
  IO.FS.writeFile (project / "Lib" / "Base.lean") <|
    "/-! The definitions whose equation lemmas several modules realize. -/\n\n" ++
      "/-- A positive number. -/\ndef positive (n : Nat) : Prop := 0 < n\n\n" ++
      "/-- One for the option of zero, two otherwise. -/\n" ++
      "def classify : Option Nat → Nat\n  | some 0 => 1\n  | _ => 2\n\n" ++
      "/-- Zero for the option of one, three otherwise. -/\n" ++
      "def grade : Option Nat → Nat\n  | some 1 => 0\n  | _ => 3\n"
  for side in #["left", "right"] do
    IO.FS.writeFile (project / "Lib" / s!"{side.capitalize}.lean") <|
      "import Lib.Base\n\n/-! Realizes its own copies of `positive.eq_1` and of the equation " ++
        "lemmas of `classify`. -/\n\n" ++
        s!"theorem {side}Unfold (n : Nat) : positive n = (0 < n) := positive.eq_1 n\n\n" ++
        s!"theorem {side}Classify (x : Option Nat) (h : x ≠ some 0) : classify x = 2 :=\n" ++
        "  classify.eq_2 x h\n"
  for side in #["near", "far"] do
    IO.FS.writeFile (project / "Lib" / s!"{side.capitalize}.lean") <|
      "import Lib.Base\n\n/-! Realizes its own copies of the equation lemmas of `grade` and " ++
        "refers to its own private match equation of `grade`. -/\n\n" ++
        s!"theorem {side}Grade (x : Option Nat) (h : x ≠ some 1) : grade x = 3 := by\n" ++
        "  simp only [grade]\n"
  for (parity, proof) in #[("Odd", "True.intro"), ("Even", "trivial")] do
    IO.FS.writeFile (project / "Lib" / s!"{parity}.lean") <|
      s!"/-! Declares `sharedFact` with the proof `{proof}`. -/\n\n" ++
        s!"theorem sharedFact : True := {proof}\n"
  for (direction, proof) in #[("Up", "True.intro"), ("Down", "trivial")] do
    IO.FS.writeFile (project / "Lib" / s!"{direction}.lean") <|
      s!"/-! Declares `helperFact` through a private `helper` with the proof `{proof}`. -/\n\n" ++
        s!"private theorem helper : True := {proof}\n\ntheorem helperFact : True := helper\n"
  IO.FS.writeFile (project / "App" / "Main.lean") <|
    "import Lib.Left\nimport Lib.Right\nimport Lib.Near\nimport Lib.Far\nimport Lib.Odd\n" ++
      "import Lib.Even\nimport Lib.Up\nimport Lib.Down\n\n" ++
      "/-! Loads both copies of `positive.eq_1`, `classify.eq_2`, `grade.eq_2`, `sharedFact` " ++
      "and `helperFact`. -/\n\n" ++
      "theorem appFact : positive 1 = (0 < 1) ∧ True := ⟨rightUnfold 1, sharedFact⟩\n"
  -- Lake writes the lock manifest of this package without dependencies; without one the fresh
  -- copy's build would create it, a configuration change during the audit.
  let locked ← runProcess project "lake" #["update"] scrubbedLeanPathEnv
  unless locked.succeeded do
    return #[s!"shared-copies/setup: lake update failed:\n{locked.output}"]
  let result := output / "result.json"
  let gate ← runProcess project (← toolPath repo "axiomGate").toString
    #["--project", project.toString, "--json-out", result.toString] scrubbedLeanPathEnv
  unless gate.succeeded do
    return #[s!"shared-copies/accepted: expected PASS:\n{gate.output}"]
  let modules := #["Lib.Base", "Lib.Down", "Lib.Even", "Lib.Far", "Lib.Left", "Lib.Near", "Lib.Odd",
    "Lib.Right", "Lib.Up", "App.Main"]
  let json ← requireAuditDocument (← IO.ofExcept (Json.parse (← IO.FS.readFile result)))
  let read {α : Type} (decoded : Except String α) := IO.ofExcept (RegulaQualification.Member.within result decoded)
  let surfaces ← read do RegulaQualification.Member.array (← RegulaQualification.Member.object json "scope") "surfaces"
  let mut found : Array (String × Array String × Array String × Array String) := #[]
  let mut required : Array (String × String) := #[]
  for surface in surfaces do
    let library ← read (RegulaQualification.Member.text surface "library")
    let admission ← read do RegulaQualification.Member.object (← RegulaQualification.Member.object surface "report") "admission"
    let reused ← read (RegulaQualification.Member.get (Array String) admission "reused")
    let shared ← read (RegulaQualification.Member.get (Array String) admission "shared")
    let keys ← read (RegulaQualification.Member.get (Array (String × String)) admission "required")
    let replayed := modules.filter fun m => !reused.contains m && keys.any (·.1 == m)
    found := found.push (library, replayed, modules.filter reused.contains,
      modules.filter shared.contains)
    if library == "Lib" then required := keys
  let shared := #["Lib.Down", "Lib.Even", "Lib.Far", "Lib.Near", "Lib.Odd", "Lib.Up"]
  let expected : Array (String × Array String × Array String × Array String) := #[
    ("Lib", #["Lib.Base", "Lib.Down", "Lib.Even", "Lib.Far", "Lib.Left", "Lib.Near", "Lib.Odd",
        "Lib.Right", "Lib.Up"], #[], shared),
    ("App", #["Lib.Down", "Lib.Even", "Lib.Far", "Lib.Near", "Lib.Odd", "Lib.Up", "App.Main"],
      #["Lib.Base", "Lib.Left", "Lib.Right"], shared)]
  let mut failures := #[]
  -- Each copy is a key of the module that declares it, so both copies of each name exist.
  for key in #[("Lib.Left", "positive.eq_1"), ("Lib.Right", "positive.eq_1"),
      ("Lib.Left", "classify.eq_2"), ("Lib.Right", "classify.eq_2"), ("Lib.Near", "grade.eq_2"),
      ("Lib.Far", "grade.eq_2"), ("Lib.Odd", "sharedFact"), ("Lib.Even", "sharedFact"),
      ("Lib.Up", "helperFact"), ("Lib.Down", "helperFact")] do
    unless required.contains key do
      failures := failures.push s!"shared-copies/copies: the Lib environment does not \
        require {key}, so the project does not hold the copies this control is about"
  unless found == expected do
    failures := failures.push s!"shared-copies/reuse: expected {expected}, found {found}"
  return failures

/-- Writes the project of `crossSurfaceDecisionControl` into the empty directory `project`. It
requires the checker at `repo` by path and has two libraries. `Exec` imports only
`Regula.Decision` and declares `crossCheck`, registered with `@[regula_decision]`. `Proofs`
imports `Exec`, and with `decided` it imports `Regula.Contract` and holds the only decision
registration of `crossCheck`; without it, it holds an unrelated theorem. With `relation` the
manifest names `Exec` in the `decides` of `Proofs`. -/
private def writeCrossSurfaceProject (repo project : FilePath) (relation decided : Bool) :
    IO Unit := do
  Regula.Filesystem.copyFile (repo / "lean-toolchain") (project / "lean-toolchain")
  IO.FS.writeFile (project / "lakefile.toml") <|
    "name = \"cross_surface_control\"\n" ++ observerPluginToml ++
      "[leanOptions]\nautoImplicit = false\n" ++
      "relaxedAutoImplicit = false\nlinter.missingDocs = true\n" ++
      s!"[[require]]\nname = \"regula\"\npath = {(Json.str repo.toString).compress}\n" ++
      observedTargetToml .library "Exec" "globs = [\"Exec.+\"]\n" ++
      observedTargetToml .library "Proofs" "globs = [\"Proofs.+\"]\n"
  writeJson (project / "lake-manifest.json") <|
    (← adopterLakeManifest repo repo.toString).setObjVal! "name" (Json.str "cross_surface_control")
  IO.FS.createDirAll (project / "Exec")
  IO.FS.createDirAll (project / "Proofs")
  IO.FS.writeFile (project / "Exec" / "Check.lean") <|
    "import Regula.Decision\n\n/-! A decision whose kind another library states. -/\n\n" ++
      "/-- Whether `n` is positive. -/\n@[regula_decision]\n" ++
      "def crossCheck (n : Nat) : Bool := decide (0 < n)\n"
  IO.FS.writeFile (project / "Proofs" / "Kind.lean") <| if decided then
      "import Exec.Check\nimport Regula.Contract\n\n/-! The decision kind of `crossCheck`. -/\n\n" ++
        "/-- `crossCheck` accepts exactly the positive numbers. -/\n" ++
        "theorem crossCheck_decides :\n" ++
        "    Regula.ExecutableContract crossCheck\n" ++
        "      (Regula.Decides (· = true) fun n => 0 < n) :=\n" ++
        "  ⟨{ sound := fun _ accepted => of_decide_eq_true accepted\n" ++
        "     accepted := ⟨1, by decide⟩\n" ++
        "     complete := fun _ holds => decide_eq_true holds\n" ++
        "     refused := ⟨0, by decide⟩ }⟩\n"
    else
      "import Exec.Check\n\n/-! No decision kind of `crossCheck`. -/\n\n" ++
        "/-- A fact of the proof library. -/\ntheorem kindAbsent : True := True.intro\n"
  let surface (library decides : String) : String :=
    "{\"library\":\"" ++ library ++ "\",\"claim\":\"standard-logical\"," ++ decides ++
      "\"rationale\":\"Cross-surface decision control\"}"
  IO.FS.writeFile (Manifest.defaultPath project) <|
    "{\"schema-version\":2,\"surfaces\":[" ++ surface "Exec" "" ++ "," ++
      surface "Proofs" (if relation then "\"decides\":[\"Exec\"]," else "") ++
      "],\"excluded-libraries\":[],\"excluded-executables\":[]}"

/-- External-boundary control for a decision registration that one claimed surface counts toward
a registered function of another (standard §7.11). The manifest field, the freeze of the counted
records, the account and the public gate are the external mechanism;
`RegulaPolicy.census_decided_iff` states the decided implementations over the census, and
`RegulaPolicy.accepted_counted_judgment` that each counted registration met its own requirements.
Each case runs in a fresh disposable project of its own (`writeCrossSurfaceProject`), so no
mutation shares a workspace or a build artifact with the green control (standard §7.8). The green
control has the relation and the registration: the audit must accept, and the account must name
`Proofs` as the surface of the one counted registration. One mutation removes the relation and
the other the registration: each must report `crossCheck` under RG1008. The green control
(`refusals` false) and the two mutations (`refusals` true) are two items of the queue. -/
private def crossSurfaceDecisionControl (refusals : Bool) (repo : FilePath) :
    IO (Array String) := do
  let gate (project : FilePath) (args : Array String) := do
    runProcess project (← toolPath repo "axiomGate").toString
      (#["--project", project.toString, "--incremental"] ++ args) scrubbedLeanPathEnv
  if !refusals then
    let green ← withScratch repo "cross-surface-green" fun project =>
      withScratch repo "cross-surface-result" fun output => do
        writeCrossSurfaceProject repo project true true
        let result := output / "result.json"
        let accepted ← gate project #["--json-out", result.toString]
        if !accepted.succeeded then
          return some s!"cross-surface/related: expected PASS:\n{accepted.output}"
        let json ← requireAuditDocument (← IO.ofExcept (Json.parse (← IO.FS.readFile result)))
        let counted ← IO.ofExcept <| RegulaQualification.Member.within result do
          RegulaQualification.Member.array (← RegulaQualification.Member.object (← RegulaQualification.Member.object json "acceptance") "account") "countedContracts"
        let named (entry : Json) : Bool :=
          (entry.getObjValAs? String "surface").toOption == some "Exec" &&
            (entry.getObjValAs? String "source").toOption == some "Proofs" &&
            (entry.getObjValAs? String "registration").toOption == some "crossCheck_decides" &&
            (entry.getObjValAs? String "implementation").toOption == some "crossCheck"
        if counted.size == 1 && counted.all named then return none
        return some s!"cross-surface/account: expected one counted registration of Proofs for \
          crossCheck of Exec, found {(Json.arr counted).compress}"
    return green.toArray
  let mut failures := #[]
  for (name, relation, decided) in #[("unrelated", false, true), ("removed", true, false)] do
    let refused ← withScratch repo s!"cross-surface-{name}" fun project => do
      writeCrossSurfaceProject repo project relation decided
      return expectedFailure s!"cross-surface/{name}" (← gate project #[])
        #["RG1008", "crossCheck (def)"]
    if let some failure := refused then failures := failures.push failure
  return failures

/-- External-boundary controls of the copy that the verification driver makes for the first
acceptance step (`RegulaVerification.makeCopy`) and of the gate's admission of such a copy
(`AxiomGate.driverCopy`). The boundary is the driver's own code for the copy, the lock and the
marker, the filesystem, and the scratch protocol between the driver and the checker.
`ScratchCopy.checked_name?`, `ScratchCopy.checked_inside` and
`RegulaVerification.removal_remove_iff` prove the decisions; no control here stands in for those
theorems. The positive case of the admission is the first acceptance step itself, on each run:
only a copy that built the gate is admitted, and these controls build no gate.

Each copy is made by the driver itself, through its private entry (`lean --run
lean/RegulaVerification.lean --copy-control`), in a project with one library and no dependency:

* While the driver lives, its copy holds the project's files and an empty `.lake`, and the pending
  record of the run is beside the copy; a file in the
  project's build output from before is still there and is not in the copy; and a scratch user
  of the checker in the same project (`Regula.Scratch.withScratch`, which reclaims) does not
  remove the copy.
* The gate refuses that copy while it has no build directory, and then because the gate was not
  built there; it refuses a directory outside the scratch area, a directory of the right shape
  with no ownership marker, and the option together with `--incremental`.
* The driver leaves a project's build output as it is, and gives a project with none the copy's
  by a rename. With a symbolic link at the project's `.lake/build` it leaves the link and the
  marked content of its target.
* A driver that is killed leaves the directory and its marker. The next scratch user of the
  checker removes both, and so does the next driver, before it makes its own copy.
* With a symbolic link at `_site`, the driver's `--begin-attempt site` stops and the marked
  content of the target stays; a `_site` directory that holds no `build.json` of a build of the
  site makes it stop and keeps its files; and a `_site` directory whose `build.json` identifies
  a build is removed (`RegulaVerification.siteRefusal`).
* With a file that is not a document of Regula at `tmp/rule-examples.json` and at
  `tmp/acceptance-link.json`, the driver's `--begin-attempt` stops with the reason of each and
  each keeps its bytes (`RegulaVerification.ownershipRefusal`). -/
private def driverCopyControl (repo : FilePath) : IO (Array String) :=
  withScratch repo "driver-copy-control" fun scratch => do
  let project := scratch / "project"
  IO.FS.createDirAll (project / "Solo")
  Regula.Filesystem.copyFile (repo / "lean-toolchain") (project / "lean-toolchain")
  IO.FS.writeFile (project / "lakefile.toml") <|
    "name = \"driver_copy_control\"\n[leanOptions]\nautoImplicit = false\n" ++
      "relaxedAutoImplicit = false\nlinter.missingDocs = true\n" ++
      "[[lean_lib]]\nname = \"Solo\"\nglobs = [\"Solo.+\"]\n"
  IO.FS.writeFile (Manifest.defaultPath project) <|
    "{\"schema-version\":2,\"surfaces\":[{\"library\":\"Solo\",\"executables\":[]," ++
      "\"claim\":\"standard-logical\",\"execution\":\"report\"," ++
      "\"rationale\":\"Driver copy control\"}]," ++
      "\"excluded-libraries\":[],\"excluded-executables\":[]}"
  IO.FS.writeFile (project / "Solo" / "Base.lean")
    "/-! The base module of the control. -/\n\ntheorem soloBase : True := True.intro\n"
  -- This generated configuration has no requirements; update creates only its initial manifest.
  let locked ← runProcess project "lake" #["update"] scrubbedLeanPathEnv
  unless locked.succeeded do
    return #[s!"driver-copy/setup: lake update failed:\n{locked.output}"]
  let driver := (repo / "lean" / "RegulaVerification.lean").toString
  let area := Regula.Scratch.directory project
  let build := project / ".lake" / "build"
  let marked := scratch / "marked"
  IO.FS.createDirAll marked
  IO.FS.writeFile (marked / "kept.txt") "kept"
  let link (target place : FilePath) : IO Unit := do
    let made ← runProcess scratch "ln" #["-s", target.toString, place.toString]
    unless made.succeeded do throw <| IO.userError s!"could not make a link: {made.output}"
  let gate ← toolPath repo "axiomGate"
  let refused (label needle : String) (args : Array String) : IO (Array String) := do
    let result ← runProcess project gate.toString args scrubbedLeanPathEnv
    if result.succeeded then
      return #[s!"driver-copy/{label}: unexpectedly accepted:\n{result.output}"]
    else if !result.output.contains needle then
      return #[s!"driver-copy/{label}: missing {repr needle}:\n{result.output}"]
    else return #[]
  let expect (label : String) (holds : Bool) : Array String :=
    if holds then #[] else #[s!"driver-copy/{label}"]
  -- Whether the checker's scratch protocol, used in the same project, leaves `path` there.
  let survivesReclamation (path : FilePath) : IO Bool := do
    discard <| Regula.Scratch.withScratch project "reclaim-probe" fun _ => pure ()
    Regula.Filesystem.isPresent path
  -- The driver's answer to a line: its next line that is not one of its progress lines.
  let answer (out : IO.FS.Handle) : IO String := do
    let mut line := (← out.getLine)
    while line.startsWith "verification: " do line ← out.getLine
    return line.trimAscii.toString
  let mut failures := #[]
  -- 1. A live copy, in a project that has build output.
  IO.FS.createDirAll build
  IO.FS.writeFile (build / "kept.txt") "from before the step"
  let child ← IO.Process.spawn {
    cmd := "lean", args := #["--run", driver, "--copy-control"], cwd := some project
    env := scrubbedLeanPathEnv, stdin := .piped, stdout := .piped, stderr := .inherit }
  let (input, child) ← child.takeStdin
  let copy := FilePath.mk (← answer child.stdout)
  let some name := ScratchCopy.name? (← IO.FS.realPath area).normalize.components
      copy.normalize.components
    | return #[s!"driver-copy/place: the driver's copy {copy} is not in the scratch area {area}"]
  let marker := area / s!"{name}.{Regula.Scratch.markerExtension}"
  failures := failures ++ expect "copy: a file of the project is missing"
    (← Regula.Filesystem.isPresent (copy / "Solo" / "Base.lean"))
  failures := failures ++ expect "copy: Lake state is not initially empty"
    (← Regula.Filesystem.Construction.listDirectory (copy / ".lake")).isEmpty
  failures := failures ++
    expect "copy: no ownership marker" (← Regula.Filesystem.isPresent marker)
  failures := failures ++ expect "copy: the run has no pending record of its own beside its copy"
    ((← IO.FS.readFile ((copy.parent.getD copy) / "acceptance-link.pending.json")).contains
      "\"status\":\"incomplete\"")
  failures := failures ++ expect "project: its build output changed"
    (← Regula.Filesystem.isPresent (build / "kept.txt"))
  failures := failures ++ expect "live: the checker's reclamation removed a live copy"
    (← survivesReclamation copy)
  failures := failures ++ (← refused "no-build-directory" "has no build directory"
    #["--driver-copy", copy.toString])
  IO.FS.createDirAll (copy / ".lake" / "build")
  IO.FS.writeFile (copy / ".lake" / "build" / "made.txt") "made in the copy"
  failures := failures ++ (← refused "other-gate" "did not build this gate"
    #["--driver-copy", copy.toString])
  failures := failures ++ (← refused "outside-scratch" "is not the directory `project`"
    #["--driver-copy", (project / "Solo").toString])
  IO.FS.createDirAll (area / "unmarked" / "project")
  failures := failures ++ (← refused "no-marker" "has no ownership marker"
    #["--driver-copy", (area / "unmarked" / "project").toString])
  failures := failures ++ (← refused "incremental" "applies only to"
    #["--driver-copy", copy.toString, "--incremental"])
  input.putStrLn "adopt"
  input.flush
  failures := failures ++ expect "adopt: a project with build output did not keep it"
    ((← answer child.stdout) == "kept" && (← Regula.Filesystem.isPresent (build / "kept.txt"))
      && !(← Regula.Filesystem.isPresent (build / "made.txt")))
  input.putStrLn "remove"
  input.flush
  failures := failures ++ expect "remove: the driver did not end with exit code 0"
    ((← child.wait) == 0)
  failures := failures ++ expect "remove: the copy or its marker is still there"
    (!(← Regula.Filesystem.isPresent copy) && !(← Regula.Filesystem.isPresent marker))
  -- 2. A project with a symbolic link at `.lake/build`, and then a driver that is killed.
  Regula.Filesystem.removePath .directory build
  link marked build
  let child ← IO.Process.spawn {
    cmd := "lean", args := #["--run", driver, "--copy-control"], cwd := some project
    env := scrubbedLeanPathEnv, stdin := .piped, stdout := .piped, stderr := .inherit
    setsid := true }
  let (input, child) ← child.takeStdin
  let copy := FilePath.mk (← answer child.stdout)
  let some name := ScratchCopy.name? (← IO.FS.realPath area).normalize.components
      copy.normalize.components
    | return failures.push s!"driver-copy/place: the second copy {copy} is not in {area}"
  let marker := area / s!"{name}.{Regula.Scratch.markerExtension}"
  IO.FS.createDirAll (copy / ".lake" / "build")
  IO.FS.writeFile (copy / ".lake" / "build" / "made.txt") "made in the copy"
  input.putStrLn "adopt"
  input.flush
  failures := failures ++ expect "adopt: a link at the build directory's place was not kept"
    ((← answer child.stdout) == "kept" &&
      (← Regula.Filesystem.isPresent (marked / "kept.txt")) &&
      !(← Regula.Filesystem.isPresent (marked / "made.txt")) &&
      (← build.symlinkMetadata).type == .symlink)
  -- A killed driver removes nothing, and its lock ends with its process.
  child.kill
  discard child.wait
  failures := failures ++ expect "left: a killed driver left no copy or no marker"
    ((← Regula.Filesystem.isPresent copy) && (← Regula.Filesystem.isPresent marker))
  failures := failures ++ expect "left: the checker's reclamation did not remove the copy of a \
    killed driver" (!(← survivesReclamation copy) && !(← Regula.Filesystem.isPresent marker))
  -- 3. A second killed driver, and then a project with no build output: the next driver removes
  -- the copy of the dead one before it makes its own, and the project gets the copy's output.
  Regula.Filesystem.removePath .link build
  let child ← IO.Process.spawn {
    cmd := "lean", args := #["--run", driver, "--copy-control"], cwd := some project
    env := scrubbedLeanPathEnv, stdin := .piped, stdout := .piped, stderr := .inherit
    setsid := true }
  let dead := FilePath.mk (← answer child.stdout)
  let some deadName := ScratchCopy.name? (← IO.FS.realPath area).normalize.components
      dead.normalize.components
    | return failures.push s!"driver-copy/place: the third copy {dead} is not in {area}"
  let deadMarker := area / s!"{deadName}.{Regula.Scratch.markerExtension}"
  child.kill
  discard child.wait
  failures := failures ++ expect "dead: a killed driver left no copy or no marker"
    ((← Regula.Filesystem.isPresent dead) && (← Regula.Filesystem.isPresent deadMarker))
  let child ← IO.Process.spawn {
    cmd := "lean", args := #["--run", driver, "--copy-control"], cwd := some project
    env := scrubbedLeanPathEnv, stdin := .piped, stdout := .piped, stderr := .inherit }
  let (input, child) ← child.takeStdin
  let copy := FilePath.mk (← answer child.stdout)
  failures := failures ++ expect "dead: the next driver did not remove the copy of a dead driver"
    (!(← Regula.Filesystem.isPresent dead) && !(← Regula.Filesystem.isPresent deadMarker) &&
      (← Regula.Filesystem.isPresent copy))
  IO.FS.createDirAll (copy / ".lake" / "build")
  IO.FS.writeFile (copy / ".lake" / "build" / "made.txt") "made in the copy"
  input.putStrLn "adopt"
  input.flush
  failures := failures ++ expect "adopt: a project with no build output did not get the copy's"
    ((← answer child.stdout) == "adopted" &&
      (← Regula.Filesystem.isPresent (build / "made.txt")) &&
      !(← Regula.Filesystem.isPresent (copy / ".lake" / "build")))
  input.putStrLn "remove"
  input.flush
  failures := failures ++ expect "remove: the driver did not end with exit code 0 after adopt"
    ((← child.wait) == 0 && !(← Regula.Filesystem.isPresent copy))
  -- 4. The site artifact of an earlier run. The attempt removes `_site` only when it holds an
  -- artifact that a build of the site identifies (`siteRefusal`): a link there and a directory
  -- that holds anything else keep what they hold.
  let site := project / "_site"
  link marked site
  let stopped ← runProcess project "lean" #["--run", driver, "--begin-attempt", "site"]
    scrubbedLeanPathEnv
  failures := failures ++ expect "site: a link at _site was followed or removed"
    (!stopped.succeeded && stopped.output.contains "so the attempt removes nothing" &&
      (← Regula.Filesystem.isPresent (marked / "kept.txt")) &&
      (← site.symlinkMetadata).type == .symlink)
  Regula.Filesystem.removePath .link site
  IO.FS.createDirAll (site / "pages")
  IO.FS.writeFile (site / "pages" / "old.html") "an earlier artifact"
  let kept ← runProcess project "lean" #["--run", driver, "--begin-attempt", "site"]
    scrubbedLeanPathEnv
  failures := failures ++ expect "site: a directory that holds no build.json was removed"
    (!kept.succeeded && kept.output.contains "holds neither a build.json" &&
      (← Regula.Filesystem.isPresent (site / "pages" / "old.html")))
  IO.FS.writeFile (site / "build.json")
    "{\"schemaVersion\":2,\"site\":\"seed\",\"producerVersion\":\"0.0.0\"}\n"
  let removed ← runProcess project "lean" #["--run", driver, "--begin-attempt", "site"]
    scrubbedLeanPathEnv
  failures := failures ++ expect "site: an earlier artifact was not removed"
    (removed.succeeded && !(← Regula.Filesystem.isPresent site))
  -- 5. Files that are not documents of Regula at the corpus receipt and at the acceptance link,
  -- which the begin-attempt of the first acceptance step marks: it refuses each and keeps its
  -- bytes.
  let foreign := "# Notes\n\nNot a document of Regula.\n"
  let receipt := project / "tmp" / "rule-examples.json"
  let accepted := project / "tmp" / "acceptance-link.json"
  IO.FS.createDirAll (project / "tmp")
  IO.FS.writeFile receipt foreign
  IO.FS.writeFile accepted foreign
  let begun ← runProcess project "lean" #["--run", driver, "--begin-attempt"] scrubbedLeanPathEnv
  failures := failures ++ expect "begin-attempt: a file that is not a document of Regula was \
    replaced or not refused"
    (!begun.succeeded &&
      begun.output.contains "rule-examples.json is a file that is not a JSON document" &&
      begun.output.contains "acceptance-link.json is a file that is not a JSON document" &&
      (← IO.FS.readFile receipt) == foreign && (← IO.FS.readFile accepted) == foreign)
  return failures

/-- External-boundary controls of the documentation step's reuse of the first acceptance step's
build output (`AcceptanceLink.placeRetained`): the filesystem, `shasum` and Lake between the record
and the fence audit's copy. `BuildReuse.reuse_iff` proves the decision; no control here stands in
for that theorem. In a project with one claimed library, the gate writes an accepted acceptance link, and
the project is then built. The control writes the `build` field the driver writes
(`RegulaVerification.Copy.recordBuild`) from that build and the project's files, with the origin of
a driver copy, which only the first acceptance step gives; the positive case with a real driver
copy is that step and the documentation step on each run. Before the gate runs, `docFenceAudit
--acceptance-link` must refuse the missing link at once, before any build. After it,
the audit must build fresh in its own copy for a link with no `build` field, for one artifact of
the build altered, for one file of the project outside `.lake` altered and for the file named `-`
altered, which `shasum` would read as standard input, and must place the recorded build output when
every digest matches. Each of those cases must pass the audit. The project declares the
weak-arguments facet of Regula's shipped `lakefile.lean`, as the repository does, so the recorded
build's traces record each module's weak arguments and the audit establishes the modules it replays
from that build. The project has a second library
that the claimed build does not compile but the recorded build holds, as the first step's
diagnostic targets are, and a documentation example that must fail because its module has no
compiled file: the audit stages only the modules of its claimed build. -/
private def retainedBuildControl (repo : FilePath) : IO (Array String) :=
  withScratch repo "retained-build-control" fun scratch => do
  let project := scratch / "project"
  IO.FS.createDirAll (project / "Solo")
  IO.FS.createDirAll (project / "docs")
  Regula.Filesystem.copyFile (repo / "lean-toolchain") (project / "lean-toolchain")
  -- The weak-arguments facet of Regula's shipped `lakefile.lean`, so the ordinary build records
  -- each module's weak arguments in its trace, as the first acceptance step's build does. Only
  -- that section is copied (`Lake.weakArgsDeclarations`); the package requires `regula` and loads
  -- its elaboration observer as a plugin (RG2006), which each library lists in `needs`.
  let some facet := Lake.weakArgsDeclarations (← IO.FS.readFile (repo / "lakefile.lean"))
    | return #["retained-build/setup: Regula's lakefile has no weak-arguments facet"]
  IO.FS.writeFile (project / "lakefile.lean") <|
    "import Lake\nopen Lake DSL\n\npackage retained_build_control where\n" ++
      "  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩,\n" ++
      "    ⟨`linter.missingDocs, true⟩]\n" ++ observerPluginLean ++
      s!"\nrequire regula from {(Json.str repo.toString).compress}\n\n" ++
      observedTargetLean .library "Solo" "  globs := #[.submodules `Solo]\n" ++ "\n" ++
      observedTargetLean .library "Extra" "  globs := #[.submodules `Extra]\n" ++ facet
  IO.FS.writeFile (Manifest.defaultPath project) <|
    "{\"schema-version\":2,\"surfaces\":[{\"library\":\"Solo\",\"executables\":[]," ++
      "\"claim\":\"standard-logical\",\"execution\":\"report\"," ++
      "\"rationale\":\"Retained build control\"}]," ++
      "\"excluded-libraries\":[{\"library\":\"Extra\",\"rationale\":\"outside the claim\"}]," ++
      "\"excluded-executables\":[]}"
  IO.FS.writeFile (project / "Solo" / "Base.lean")
    "/-! The base module of the control. -/\n\n/-- The base value. -/\ndef soloBase : Nat := 7\n"
  IO.FS.createDirAll (project / "Extra")
  IO.FS.writeFile (project / "Extra" / "Diag.lean")
    "/-! A module outside the claimed build. -/\n\n/-- An extra value. -/\ndef extra : Nat := 1\n"
  IO.FS.writeFile (project / "docs" / "control.md") <|
    "```lean\nimport Solo.Base\nexample : soloBase = 7 := rfl\n```\n\n" ++
      "<!-- lean-fail: unknown module prefix|does not exist -->\n```lean\nimport Extra.Diag\n```\n"
  -- A file that no module reads and the link's identity does not capture.
  IO.FS.writeFile (project / "notes.txt") "a file of the project tree\n"
  -- A file that `shasum` reads as standard input when it is given as an operand alone.
  IO.FS.writeFile (project / "-") "a file named -\n"
  let env := scrubbedLeanPathEnv.push ("LAKE_ARTIFACT_CACHE", some "false")
  let step (label : String) (cmd : String) (args : Array String) : IO (Option String) := do
    let result ← runProcess project cmd args env
    return if result.succeeded then none else some s!"retained-build/{label}:\n{result.output}"
  -- This generated configuration has no requirements; update creates only its initial manifest.
  if let some failure ← step "setup" "lake" #["update"] then return #[failure]
  let link := scratch / "acceptance-link.json"
  let fresh (reason : String) :=
    s!"claimed surface built fresh in this run, in a copy with no earlier build output ({reason})"
  let unlinked ← runProcess project (← toolPath repo "docFenceAudit").toString
    #["--project", project.toString, "--acceptance-link", link.toString, "--jobs", "1"] env
  let mut failures := #[]
  unless !unlinked.succeeded &&
      unlinked.output.contains "acceptance link missing: run ordinary acceptance first" &&
      !unlinked.output.contains "claimed surface built" do
    failures := failures.push s!"retained-build/no-gate: expected the refusal of the missing link \
      before any build:\n{unlinked.output}"
  if let some failure ← step "gate" (← toolPath repo "axiomGate").toString
      #["--acceptance-link", link.toString] then return failures.push failure
  -- The first step builds more than the claimed targets.
  if let some failure ← step "build" "lake" #["build", "Solo", "Extra"] then
    return failures.push failure
  let gateRecord ← readJson link
  let build := project / ".lake" / "build"
  let mut artifacts := #[]
  for part in ["lib", "ir"] do
    unless ← Regula.Filesystem.isDirectory (build / part) do continue
    for path in ← Regula.Filesystem.Construction.walkDirectory (build / part) do
      if (← path.symlinkMetadata).type == .file then
        artifacts := artifacts.push ("/".intercalate
          (path.normalize.components.drop build.normalize.components.length))
  let artifactDigests ← AcceptanceLink.digests build artifacts.toList
  unless artifactDigests.any (·.1.startsWith "lib/lean/Extra/Diag.") do
    return failures.push "retained-build/setup: the build holds no artifact of Extra.Diag"
  let tree ← AcceptanceLink.digests project (← AcceptanceLink.treeFiles project)
  let recorded := (gateRecord.setObjVal! "origin" (.str "driverCopy")).setObjVal! "build"
    (Json.mkObj [("targets", toJson ["Solo"]), ("tree", toJson tree),
      ("artifacts", toJson artifactDigests)])
  let audit (label : String) (record : Json) (expected : String) : IO (Array String) := do
    writeJson link record
    let result ← runProcess project (← toolPath repo "docFenceAudit").toString
      #["--project", project.toString, "--acceptance-link", link.toString, "--jobs", "1"] env
    if !result.succeeded then
      return #[s!"retained-build/{label}: the audit failed:\n{result.output}"]
    else if !result.output.contains expected then
      return #[s!"retained-build/{label}: missing {repr expected}:\n{result.output}"]
    else return #[]
  failures := failures ++ (← audit "no-build-field" gateRecord
    (fresh "the acceptance link records no build of the first acceptance step"))
  failures := failures ++
    (← audit "matching" recorded "claimed surface built from the first acceptance step's")
  -- One altered artifact, then one altered file of the project, each restored afterwards.
  let some (artifact, _) := artifactDigests.find? (·.1.startsWith "lib/lean/Solo/Base.")
    | return failures.push "retained-build/setup: the build left no artifact of Solo.Base"
  let altered := build / artifact
  let original ← IO.FS.readBinFile altered
  IO.FS.writeBinFile altered (original.push 0)
  failures := failures ++ (← audit "altered-artifact" recorded (fresh
    "the checkout's .lake/build does not hold the recorded files of the claimed build's modules \
      with their recorded digests"))
  IO.FS.writeBinFile altered original
  IO.FS.writeFile (project / "notes.txt") "an altered file of the project tree\n"
  failures := failures ++ (← audit "altered-tree-file" recorded
    (fresh "a file of this copy differs from the first acceptance step's copy"))
  IO.FS.writeFile (project / "notes.txt") "a file of the project tree\n"
  IO.FS.writeFile (project / "-") "an altered file named -\n"
  failures := failures ++ (← audit "altered-dash-file" recorded
    (fresh "a file of this copy differs from the first acceptance step's copy"))
  IO.FS.writeFile (project / "-") "a file named -\n"
  return failures

/-- The groups of controls the structural partition reports separately. -/
private inductive StructuralGroup where
  | frozen
  | clusters
  | cycle
  | copies
  | crossSurface
  | driverCopy
  | retainedBuild
  | manifest
  | observerIdentity
  deriving BEq

/-- What a sharded run printed in place of the description of every control of its group: the
controls it ran, which are not all of the group's. -/
private def shardDescription (label : String) (others : Nat) (names : Array String) : String :=
  s!" (shard {label}: {", ".intercalate names.toList}; " ++
    (if others == 1 then "the other shard runs the rest)" else "the other shards run the rest)")

/-- Structural mutations and manifest controls retain their isolated projects, worker joins,
and complete failure accumulation. The frozen-artifact controls, the mutation clusters, the
cross-surface decision control, the library cycle control, the observer identity control, the
shared copies control, the driver copy control, the retained build control and the manifest
controls share one queue of `jobs` workers, so no more than `jobs` of them run at once. The short
controls wait behind the
clusters and take the
workers the first clusters free, instead of competing with the first clusters for the
processors. Each control has its shard; with `shard`, only that shard's controls run, and only
the groups it ran report. The two parts of the cross-surface decision control share a shard, so
the shard that reports that control ran all of it. After the queue, an unsharded run compares the
self-hosted fresh inputs (`selfHostedIdentity`), and the shard of each self-hosted cluster writes
the digest of the input it recorded (`selfHostedDigest`). -/
private unsafe def runStructural (layout : SourceLayout) (repo : FilePath) (jobs : Nat)
    (shard : Option (Fin structuralShards)) (failures : IO.Ref (Array String)) : IO Unit := do
  -- Every result carries its group, so none is found by its position in the queue.
  let results ← loggedPhase "structural controls" <|
    withScratch repo "checker-structural" fun scratch =>
      withScratch repo "checker-manifest" fun manifests => do
        let inputs ← SelfHostedInputs.new
        let controls : List (Fin structuralShards × StructuralGroup × String × IO (Array String)) :=
          (structuralClusters layout repo scratch inputs).map (fun (assigned, name, run) =>
            (assigned, StructuralGroup.clusters, s!"structural {name}", run)) ++
          [(structuralShard 1, StructuralGroup.crossSurface, "cross-surface decision refusals",
              crossSurfaceDecisionControl true repo),
            (structuralShard 1, StructuralGroup.driverCopy, "driver copy control",
              driverCopyControl repo),
            (structuralShard 3, StructuralGroup.retainedBuild, "retained build control",
              retainedBuildControl repo),
            (structuralShard 1, StructuralGroup.crossSurface, "cross-surface decision control",
              crossSurfaceDecisionControl false repo),
            (structuralShard 4, StructuralGroup.cycle, "library cycle control",
              libraryCycleControl repo),
            (structuralShard 4, StructuralGroup.observerIdentity, "observer identity control",
              observerIdentityControl repo),
            (structuralShard 1, StructuralGroup.copies, "shared copies control",
              sharedCopiesControl repo),
            (structuralShard 1, StructuralGroup.manifest, "manifest controls",
              manifestQualification repo manifests),
            (structuralShard 1, StructuralGroup.frozen, "frozen artifact controls",
              withScratch repo "checker-frozen-artifacts" frozenArtifactControls)]
        let mut results ← mapWorkQueue (max 1 jobs) ((inShard shard controls).map (·.2)).toArray
          fun (group, label, run) => do return (group, label, ← loggedPhase label run)
        -- The queue has finished, so each self-hosted cluster this run ran has recorded its input.
        let afterQueue : List (Fin structuralShards × StructuralGroup × String × IO (Array String)) :=
          match shard with
          | none => [(selfHostedShard, StructuralGroup.clusters, "structural self-hosted identity",
              selfHostedIdentity inputs)]
          -- Each digest in the shard that the selection names as its destination
          -- (`Selection.destinations`).
          | some _ => SelfHosted.all.map fun input =>
            (input.shard, StructuralGroup.clusters, s!"structural self-hosted {input.name} digest",
              selfHostedDigest repo scratch input (inputs.of input))
        for (group, label, run) in (inShard shard afterQueue).map (·.2) do
          results := results.push (group, label, ← loggedPhase label run)
        return results
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
      incomplete, wrong-version, unknown-key, bad-execution, unknown-decides and unknown-library \
      public cases)"
  if ran .clusters then
    IO.println <| "self-test structural: " ++ verdict .clusters ++ match shard with
      | none =>
        " (discovery, warning, contamination, exact ownership, unlisted root module, " ++
        "library and exe classification, claimed exe root, exe contamination, app exe omission, " ++
        "app missing/trivial/weakened update evidence, missing proof field, weakened admission, " ++
        "fresh coverage, realized and unchecked duplicate copies, restore; " ++
        "isolated projects, bounded parallelism)"
      | some selected => shardDescription (shardLabel selected) (structuralShards - 1)
          ((results.filter (·.1 == StructuralGroup.clusters)).map (·.2.1)) ++
          (if selected == selfHostedShard || selected == selfHostedRestoredShard then
            s!". The self-hosted identity is decided only where both digests are compared: the \
              CI diagnostics gate compares {selfHostedDigestPath repo .positive} and \
              {selfHostedDigestPath repo .restored}, so a local claim needs the unsharded \
              structural run or a comparison of those two files."
          else "")
  if ran .cycle then
    IO.println <| "self-test library cycle: " ++ verdict .cycle ++
      " (two claimed libraries that import one another: accepted, each module replayed in one \
        environment, a requested module reused with its keys)"
  if ran .observerIdentity then
    IO.println <| "self-test observer identity: " ++ verdict .observerIdentity ++
      " (a copied gate whose audit links the observer library again at the path the gate read it \
        from: refused under RG2003; restored, the library reused: accepted)"
  if ran .copies then
    IO.println <| "self-test shared copies: " ++ verdict .copies ++
      " (two modules that realize copies of two lemmas, identical or equal up to their private \
        match equations, which only those copies use: reused in a later environment; two \
        modules whose own theorems use their private match equations, and two pairs of modules \
        with different copies of one theorem, or of its private helper: replayed again)"
  if ran .crossSurface then
    IO.println <| "self-test cross-surface decisions: " ++ verdict .crossSurface ++
      " (a registered function whose only decision registration is in another claimed library: \
        accepted with the manifest relation and named with that surface in the account, RG1008 \
        without the relation and without the registration)"
  if ran .driverCopy then
    IO.println <| "self-test driver copy: " ++ verdict .driverCopy ++
      " (the driver's copy holds the project and no build output, and the checker's reclamation \
        keeps it while the driver lives and removes it after; the gate refuses a copy that did \
        not build it, a directory outside the scratch area, one with no marker and \
        --incremental; a project keeps its build output or a link at its place, and one with \
        none gets the copy's; the next driver removes the copy of a killed one; a link at _site \
        is not followed)"
  if ran .retainedBuild then
    IO.println <| "self-test retained build: " ++ verdict .retainedBuild ++
      " (docFenceAudit refuses the missing link before any build, before any gate ran; it \
        builds fresh in its own copy for a link with no build record, for an altered artifact, \
        for an altered file of the project and for an altered file named -, and places the \
        recorded build output of its claimed modules when every digest matches, without a \
        module of another library; each of those audits passes)"

/-- Execution-evidence controls: the correspondence controls and every compiler-path case,
each with its positive, mutation and fresh restoration in an isolated project. With `shard`,
only that shard's controls run and are named. -/
private unsafe def runExecution (layout : SourceLayout) (repo : FilePath) (jobs : Nat)
    (shard : Option (Fin executionShards)) (failures : IO.Ref (Array String)) : IO Unit := do
  let (names, execution) ← loggedPhase "execution controls" <|
    withScratch repo "checker-execution" fun scratch =>
      executionQualification layout repo scratch jobs shard
  for failure in execution do failures.modify (·.push failure)
  IO.println <| "self-test execution: " ++
    (if execution.isEmpty then "PASS" else "FAIL") ++ match shard with
    | none =>
      s!" ({CompilerPaths.caseCount} compiler-path cases, conditional correspondence, " ++
      "restricted-domain and universe correspondence restorations; positive, mutation and " ++
      "fresh restoration each; isolated projects, bounded parallelism)"
    | some selected => shardDescription (shardLabel selected) (executionShards - 1) names

/-- Copy the document at `source` to `target`. -/
private def copyDocument (source target : FilePath) : IO Unit := do
  IO.FS.writeFile target (← IO.FS.readFile source)

/-- Whether the reader of result documents (`ResultProtocol.readDocument`) admits the document at
`path` with the status `completed`. -/
private def completedResult (path : FilePath) : IO Bool := do
  match ← (ResultProtocol.readDocument path).toBaseIO with
  | .ok document => return (document.getObjValAs? String "status").toOption == some "completed"
  | .error _ => return false

/-- Whether the reader of the acceptance link (`AcceptanceLink.require`) admits the record at
`path` as accepted with the identity `digest`. -/
private def linkAccepted (path : FilePath) (digest : String) : IO Bool := do
  return (← (AcceptanceLink.require path digest).toBaseIO) matches .ok _

/-- The JSON at `path`, parsed strictly, or `none`. -/
private def parsedAt (path : FilePath) : IO (Option Json) := do
  match ← (do IO.ofExcept <| PolicyCodec.parse (← IO.FS.readFile path) : IO Json).toBaseIO with
  | .ok value => return some value
  | .error _ => return none

/-- Whether the reader of worker packets (`readWorkerPacket`) admits the packet at `path` for
`request`. -/
private def packetAdmitted (request : Json) (path : FilePath) : IO Bool := do
  return (← parsedAt path).any fun value => (readWorkerPacket request value).isOk

/-- Whether the document at `path` is the producer campaign's export: one with the member
`examples` (`Regula.Qualification.Producer.check`). -/
private def exportCompleted (path : FilePath) : IO Bool := do
  return (← parsedAt path).any fun value => (value.getObjVal? "examples").isOk

/-- A destination of a run in the task-manager control (`taskManagerControl`) or in the control of
an early stop (`earlyStopControl`): the completed document of its own format that it starts with,
and whether that format's reader admits a document as completed. -/
private structure Seeded where
  /-- The destination. -/
  path : FilePath
  /-- Write a completed document of the destination's format there. -/
  seed : IO Unit
  /-- Whether the reader of the format admits the document there as a completed one. -/
  completed : IO Bool
  /-- Whether the destination holds what the run must leave there, given the run's standard
  error: a document marked incomplete with the reason (`markedWith`, `markedWithError`), or nothing
  for a digest or a site artifact. -/
  marked : String → IO Bool

/-- A completed admission of no module, the seed of a published admission in the task-manager
control (`taskManagerControl`). -/
private def emptyAdmission : Admission.Completed where
  receipt := { modules := #[], required := #[], admitted := #[], reused := #[], shared := #[] }
  origins := #[]

/-- Whether the document at `path` holds `incomplete` in `status`, and `reason` in `member`:
`unresolved`, a list, or `reason`, a string. -/
private def markedWith (path : FilePath) (member reason : String)
    (status : String × String := ("status", "incomplete")) : IO Bool := do
  let some marked ← parsedAt path | return false
  let stated := match member with
    | "unresolved" => (marked.getObjValAs? (Array String) member).toOption == some #[reason]
    | _ => (marked.getObjValAs? String member).toOption == some reason
  return stated && (marked.getObjValAs? String status.1).toOption == some status.2

/-- Whether the document at `path` holds `incomplete` in `status`, and in `member` one reason that
is not the guard's (`Regula.TaskManager.startedReason`) and that the standard error `stderr` holds
right after `lead`: the text of the error that the run printed. `member` is `unresolved`, a list,
or `reason`, a string. -/
private def markedWithError (path : FilePath) (member lead stderr : String) : IO Bool := do
  let some marked ← parsedAt path | return false
  let stated : Option String := match member with
    | "unresolved" => (marked.getObjValAs? (Array String) member).toOption.bind fun reasons =>
      if reasons.size == 1 then reasons[0]? else none
    | _ => (marked.getObjValAs? String member).toOption
  return (marked.getObjValAs? String "status").toOption == some "incomplete" &&
    stated.any fun reason => !reason.isEmpty && reason != Regula.TaskManager.startedReason &&
      stderr.contains (lead ++ reason)

/-- The control of a process without Lean's task manager (issue 393), one refused run for each
shape of program. Each of the actual `axiomGate`, `lint`, `docFenceAudit`, `qualify`, `site` and
this self-test, run with `LEAN_NUM_THREADS=0` and without `REGULA_TIMING`, `REGULA_RECEIPT_TIMER`
and `REGULA_QUALIFICATION_WRAPPER`, which only the run of the proxy sets, must refuse before its run
starts (`Regula.TaskManager.guard`): its standard error must hold the guard's reason line, its exit
code must be the one of its incomplete run, and it must print nothing to standard output, so no
result line. Each destination that the run names starts with a completed document of its own
format, which the format's reader admits as completed: a result of the gate's own run on
`Fixtures.Positive.KernelOnly` with the claim `kernel-only` for the `--json-out` of the gate, of
`lint` and of the proxy of `axiomGate` that `qualify` runs under
`REGULA_QUALIFICATION_WRAPPER=acceptance`
(`ResultProtocol.readDocument`), an accepted acceptance link with its identity
(`AcceptanceLink.require`), a worker packet for the gate's `--frontend-worker` and
`--declaration-report-worker` and the self-test's `--transcript-worker` (`readWorkerPacket`), the
completed admission that the report worker's request names as `publish` (`Admission.Completed`),
the export of `qualify producers --evidence`, the passing report of `qualify native-launcher`, a
digest of the self-hosted positive for the self-test's first structural shard, and a clean,
publishable artifact of `site build --out` (`Regula.Site.Deployment.gate`). The runs of the
launcher and of the structural shard run in a planted project root, where their fixed paths lie.
The refused run must replace each document with one marked incomplete with the reason, or remove
the digest or the artifact, so that the reader no longer admits it as completed. `docFenceAudit`
names no destination. The processes and Lean's runtime are its subject, an external boundary: it
observes this build's programs and proves nothing. -/
private def taskManagerControl (repo : FilePath) : IO (Option String) :=
  withScratch repo "checker-task-manager" fun scratch => do
    let reason := Regula.Probe.taskManagerMissingReason
    let gate := (← toolPath repo "axiomGate").toString
    let qualify := (← toolPath repo "qualify").toString
    -- A completed result of the gate's own run, the seed of each result destination.
    let completed := scratch / "completed.json"
    let fixture := repo / "lean" / "Fixtures" / "Positive" / "KernelOnly.lean"
    let seeded ← runProcess repo gate #["--file", fixture.toString, "--claim", "kernel-only",
      "--json-out", completed.toString] (env := #[("REGULA_TIMING", none)])
    unless seeded.exitCode == 0 && (← completedResult completed) do
      return some s!"task manager: the gate's run on {fixture} did not record a completed result \
        (exit {seeded.exitCode}):\n{seeded.output}"
    let result (name : String) : Seeded :=
      { path := scratch / name, seed := copyDocument completed (scratch / name),
        completed := completedResult (scratch / name),
        marked := fun _ => markedWith (scratch / name) "unresolved" reason }
    let digest := String.ofList (List.replicate 64 'a')
    let link : Seeded :=
      { path := scratch / "link.json",
        marked := fun _ => markedWith (scratch / "link.json") "reason" reason,
        seed := writeJson (scratch / "link.json") (Json.mkObj [("schemaVersion", toJson (1 : Nat)),
          ("status", .str "accepted"), ("identity", .str digest),
          ("acceptedJobs", toJson (#[] : Array Json)), ("origin", .str "isolatedCopy")]),
        completed := linkAccepted (scratch / "link.json") digest }
    let request := Json.mkObj [("control", .str "task manager")]
    let packet (name : String) : Seeded :=
      { path := scratch / name, marked := fun _ => markedWith (scratch / name) "reason" reason,
        seed := writeJson (scratch / name) (workerPacket request (.str "seed")),
        completed := packetAdmitted request (scratch / name) }
    let evidence : Seeded :=
      { path := scratch / "producers.json",
        marked := fun _ => markedWith (scratch / "producers.json") "reason" reason,
        seed := writeJson (scratch / "producers.json") (Json.mkObj
          [("schemaVersion", toJson (1 : Nat)), ("examples", toJson (#[] : Array Json))]),
        completed := exportCompleted (scratch / "producers.json") }
    -- A planted project root, where the fixed paths of the launcher's report and the digests lie.
    let project := scratch / "project"
    IO.FS.createDirAll project
    IO.FS.writeFile (project / "lakefile.lean") ""
    IO.FS.writeFile (project / "lean-toolchain") (← IO.FS.readFile (repo / "lean-toolchain"))
    let project ← IO.FS.realPath project
    let report := project / "tmp" / "native-launcher-diagnostic.json"
    let launcher : Seeded :=
      { path := report,
        marked := fun _ => markedWith report "reason" reason ("outcome", "INCOMPLETE"),
        seed := do
          IO.FS.createDirAll (project / "tmp")
          writeJson report (Json.mkObj [("outcome", .str "PASS"), ("equivalent", .bool true),
            ("totalMillis", toJson (0 : Nat))]),
        completed := return (← parsedAt report).any fun value =>
          (value.getObjValAs? String "outcome").toOption == some "PASS" }
    let positive := selfHostedDigestPath project .positive
    let selfHosted : Seeded :=
      { path := positive, marked := fun _ => do return !(← Regula.Filesystem.isPresent positive),
        seed := do
          if let some parent := positive.parent then IO.FS.createDirAll parent
          IO.FS.writeFile positive (digest ++ "\n"),
        completed := do
          unless ← Regula.Filesystem.isPresent positive do return false
          return (← IO.FS.readFile positive) == digest ++ "\n" }
    IO.FS.writeFile (scratch / "request.json") request.compress
    -- The request of the declaration-report worker names the file where the worker publishes its
    -- admission; the coordinator reads it as an `Admission.Completed` (`publishedAdmission`).
    let publish := scratch / "publish.json"
    let admission : Seeded :=
      { path := publish, marked := fun _ => markedWith publish "reason" reason,
        seed := writeJson publish (toJson emptyAdmission),
        completed := do
          unless ← Regula.Filesystem.isPresent publish do return false
          let read : Except String Admission.Completed :=
            (PolicyCodec.parse (← IO.FS.readFile publish)).bind fromJson?
          return read.isOk }
    let report : Inspection.ReportWorkerRequest :=
      { modules := #[], searchRoots := #[], sourceRoots := #[], sourceBindings := #[],
        ownership := {}, historyMemo := (scratch / "history").toString, priors := #[],
        publish := publish.toString }
    IO.FS.writeFile (scratch / "report-request.json") (toJson report).compress
    -- An artifact of `site build`, whose `build.json` the deployment gate reads: a clean build
    -- that is publishable (`Regula.Site.Deployment.gate`).
    let site := scratch / "site"
    let artifact : Seeded :=
      { path := site, marked := fun _ => do return !(← Regula.Filesystem.isPresent site),
        seed := do
          IO.FS.createDirAll site
          writeJson (site / "build.json") (Json.mkObj [("schemaVersion", toJson (2 : Nat)),
            ("site", .str "seed"), ("producerVersion", .str "0.0.0"), ("dirty", .bool false),
            ("revision", .str digest), ("publishable", .bool true)]),
        completed := do
          let some build ← parsedAt (site / "build.json") | return false
          return (build.getObjValAs? Bool "dirty").toOption == some false &&
            (build.getObjValAs? Bool "publishable").toOption == some true }
    let issue := repo / "lean" / "Fixtures" / "Positive" / "HeartbeatCorrespondence.lean"
    let gateArgs (out : FilePath) : Array String :=
      #["--file", issue.toString, "--claim", "choice-free", "--execution", "checked", "--json-out",
        out.toString]
    -- No variable of the caller selects a mode: only the proxy run sets the wrapper's.
    let wrapper (mode : Option String) : Array (String × Option String) :=
      #[("LEAN_NUM_THREADS", some "0"), ("REGULA_TIMING", none),
        ("REGULA_QUALIFICATION_WRAPPER", mode), ("REGULA_RECEIPT_TIMER", none)]
    let without := wrapper none
    let proxy := result "proxy.json"
    -- Each refused run: the program's name in the guard's line, its path, working directory,
    -- arguments and environment, its exit code and each destination it names.
    let runs : List (String × String × FilePath × Array String ×
        Array (String × Option String) × UInt32 × List Seeded) := [
      ("axiomGate", gate, repo, gateArgs (scratch / "gate.json"), without,
        Lint.Outcome.incomplete.exitCode, [result "gate.json"]),
      ("axiomGate", gate, repo, #["--acceptance-link", link.path.toString], without,
        Lint.Outcome.incomplete.exitCode, [link]),
      ("axiomGate", gate, repo, #["--frontend-worker", (scratch / "request.json").toString,
        (scratch / "frontend.json").toString], without, Lint.Outcome.incomplete.exitCode,
        [packet "frontend.json"]),
      ("axiomGate", gate, repo, #["--declaration-report-worker",
        (scratch / "report-request.json").toString, (scratch / "report.json").toString], without,
        Lint.Outcome.incomplete.exitCode, [packet "report.json", admission]),
      ("lint", (← toolPath repo "lint").toString, repo,
        #["--json-out", (scratch / "lint.json").toString], without,
        Lint.Outcome.incomplete.exitCode, [result "lint.json"]),
      ("docFenceAudit", (← toolPath repo "docFenceAudit").toString, repo, #[], without, 1, []),
      ("checkerSelftest", (← IO.appPath).toString, repo, #["--transcript-worker", "\"Planted\"",
        issue.toString, "true", (scratch / "transcript.json").toString], without, 1,
        [packet "transcript.json"]),
      ("checkerSelftest", (← IO.appPath).toString, project,
        #["--build-bound", "--partition", "structural", "--shard", "1/5"], without, 1,
        [selfHosted]),
      ("qualify", qualify, repo, #["producers", "--evidence", evidence.path.toString], without, 1,
        [evidence]),
      ("qualify", qualify, project, #["native-launcher"], without, 1, [launcher]),
      ("qualify", qualify, repo, gateArgs proxy.path, wrapper (some "acceptance"),
        Lint.Outcome.incomplete.exitCode, [proxy]),
      ("site", (← toolPath repo "site").toString, repo,
        #["build", "--out", site.toString, "--evidence", (scratch / "evidence.json").toString],
        without, 1, [artifact])]
    for (program, path, cwd, args, env, code, destinations) in runs do
      for destination in destinations do
        destination.seed
        unless ← destination.completed do
          return some s!"task manager: the seed of {destination.path} is not a completed \
            document of its format"
      let result ← runProcess cwd path args (env := env)
      let line := Regula.TaskManager.refusalLine program reason
      if result.exitCode != code || !result.stdout.isEmpty ||
          !(result.stderr.splitOn "\n").contains line then
        return some s!"task manager: {program} {args} with LEAN_NUM_THREADS=0 did not refuse with \
          exit {code}, the line {repr line} and no standard output (exit {result.exitCode}):\n\
          {result.output}"
      for destination in destinations do
        unless (← destination.marked result.stderr) && !(← destination.completed) do
          let held ← match ← Regula.Filesystem.metadataIfPresent destination.path with
            | some { type := .dir, .. } => pure "a directory"
            | some _ => IO.FS.readFile destination.path
            | none => pure "nothing"
          return some s!"task manager: {program} {args} with LEAN_NUM_THREADS=0 left \
            {destination.path} without the incomplete mark and the reason, or admitted as \
            completed; it holds {held}"
    return none

/-- The control of a run that stops early in a process with Lean's task manager (issue 423): one run
of an actual program of this build for each early stop, with the failure injected from outside. The
injections are `lean` absent from `PATH` and no `LEAN_SYSROOT`, so the first step of the program,
the initialization of Lean's search path (`initializeLeanSearchPath`), fails before the program's
own marks, for `ruleExamples --policy-negative` and `--documentation`, `axiomGate --json-out`,
`freshChecker --json-out` and the self-test's `--transcript-worker`; a facts file that does not
exist, for both forms of `ruleExamples --injected-git-facts`; a planted project root without the
documented examples that `qualify --under-deadline producers --evidence` reads first, and an extra
argument that its parser refuses; no GNU timeout on `PATH`, which `qualify producers --evidence`
selects before it starts the command under its deadline; GNU coreutils `env` as the one `timeout` on
`PATH`, which the bounded start of `qualify producers --evidence` selects and which ends with status
125 before the command runs; an invalid shard of `qualify --under-deadline rule-examples
--evidence`; the proxy of `axiomGate` that `qualify` runs under
`REGULA_QUALIFICATION_WRAPPER=acceptance` with no gate beside it to start; and `site build --out`
without its evidence, which the parser refuses. Each destination that the run names starts with a
completed document of its own format, which the format's reader admits as completed, as in the
task-manager control (`taskManagerControl`); for `freshChecker` a document with the status
`completed`, and for `qualify rule-examples` an export of no rule that the site's reader admits
(`Site.Build.admitShard`). The run must stop with the exit code of its early stop, and each
destination must then hold a document marked incomplete with the reason, or be removed for the site
artifact, so that the reader no longer admits it as completed. For a production of `ruleExamples`,
the export of `qualify producers` and the evidence of a command under the deadline that its
arguments refuse, the reason is the error's text that the run printed (`markedWithError`), and for
the start that ran no command it gives the status and the option that the stand-in refused. For the
other runs, it is the reason with which the guard marks each destination before any code of the
program runs (`Regula.TaskManager.guard`, `Regula.TaskManager.startedReason`).

The verification wrapper, `scripts/verify.sh`, runs in a copy of its files with no `lean` on its
`PATH`, after the export of the first corpus shard was recorded against the current sources with
the text of `foundation_manifest.json` changed. Its attempt must stop with Bash's exit 127 before
the driver runs, and leave that export and the corpus receipt `tmp/rule-examples.json` with their
bytes, since no code of the attempt ran. The site's reader (`Site.Build.admitShard`) must then
refuse the export.

A run whose destination holds a file that is not a document of Regula is refused, and its mark
writes nothing there (`Regula.Destination.write`, `Regula.Destination.refusal`), so the guard's mark
replaces no file that the run reads: the declaration-report worker of `axiomGate` with its request
as its output, the frontend worker with a Lean source as its output, the audit of `axiomGate --file`
with its source as its `--json-out`, and a symbolic link to a completed result as that `--json-out`;
`axiomGate --registry-out` with a JSON document that holds only the member `rules`; `freshChecker`
with a hard link to its `--manifest`, or the configuration of a dependency, as its `--json-out`;
`qualify producers --evidence`, bounded and under the deadline, with a Lean source as its export;
`ruleExamples --injected-git-facts` with its facts as the audit's `--json-out`, `ruleExamples
--policy-negative` with its source as its result, named through a directory and `..`, and
`ruleExamples --documentation` with a Markdown document as its result. Each must exit with its
refusal's code and the reason, and each file must keep its bytes, or stay absent. The published
admission that the report worker's request names must then hold a mark that the reader of an
admission refuses. The gate with two destinations whose names differ only in case, the first holding
a completed result, must mark them and refuse.
`site build --out` a directory that holds a Markdown document must fail and keep it: without its
evidence the guard's refusal removes no directory that holds no artifact
(`Regula.Site.Build.invalidateRefused`), and with evidence the build refuses it
(`Regula.Site.Build.artifactRefusal`). An empty file, a hard link to a completed result, a completed
result at a name of 255 bytes, and a mark that an earlier version of Regula wrote at a worker's
output are each replaced by the guard's mark when the gate stops early. The other name of the
linked result keeps its bytes.

The processes and Lean's runtime are its subject, an external boundary: it observes
this build's programs and proves nothing.

Assumes: Lean 4.34.1's `Lean.findSysroot` returns `LEAN_SYSROOT` when it is set, and otherwise runs
`lean --print-prefix` and fails when that run fails (`src/lean/Lean/Util/Path.lean:180-187`).
Trusted: the runtime finds a command given by a bare name, such as `lean` or `timeout`, only in
the directories of `PATH`; its process code is not among the toolchain's sources. Trusted: GNU
coreutils `env`, run under the name `timeout`, prints GNU coreutils for `--version` and ends with
its own failure status 125 at the option `--signal=KILL`, naming that option on standard error.
Trusted: Bash ends a script that runs under `set -e` with 127 when a command is not found, and
`/usr/bin` and `/bin`, the wrapper's `PATH`, hold no `lean`, which the control checks first;
`ln` makes a hard link, and with `-s` a symbolic link. -/
private def earlyStopControl (repo : FilePath) : IO (Option String) :=
  withScratch repo "checker-early-stop" fun scratch => do
    let started := Regula.TaskManager.startedReason
    let gate := (← toolPath repo "axiomGate").toString
    let qualify := (← toolPath repo "qualify").toString
    let ruleExamples := (← toolPath repo "ruleExamples").toString
    -- A completed result of the gate's own run, the seed of each result destination.
    let completed := scratch / "completed.json"
    let fixture := repo / "lean" / "Fixtures" / "Positive" / "KernelOnly.lean"
    let seeded ← runProcess repo gate #["--file", fixture.toString, "--claim", "kernel-only",
      "--json-out", completed.toString] (env := #[("REGULA_TIMING", none)])
    unless seeded.exitCode == 0 && (← completedResult completed) do
      return some s!"early stop: the gate's run on {fixture} did not record a completed result \
        (exit {seeded.exitCode}):\n{seeded.output}"
    -- A result destination: marked with the error's text that follows `lead` on standard error,
    -- or with the guard's reason when there is no `lead`.
    let result (name : String) (lead : Option String) : Seeded :=
      { path := scratch / name, seed := copyDocument completed (scratch / name),
        completed := completedResult (scratch / name),
        marked := fun stderr => match lead with
          | some lead => markedWithError (scratch / name) "unresolved" lead stderr
          | none => markedWith (scratch / name) "unresolved" started }
    let request := Json.mkObj [("control", .str "early stop")]
    let packet : Seeded :=
      { path := scratch / "transcript.json",
        marked := fun _ => markedWith (scratch / "transcript.json") "reason" started,
        seed := writeJson (scratch / "transcript.json") (workerPacket request (.str "seed")),
        completed := packetAdmitted request (scratch / "transcript.json") }
    let graph : Seeded :=
      { path := scratch / "graph.json",
        marked := fun _ => markedWith (scratch / "graph.json") "unresolved" started,
        seed := writeJson (scratch / "graph.json") (Json.mkObj [("mode", .str "serializedGraph"),
          ("status", .str "completed"), ("moduleSets", Json.mkObj []),
          ("modules", toJson (#[] : Array Json)), ("roots", toJson (#[] : Array Json)),
          ("coverage", Json.mkObj []), ("checks", toJson (#[] : Array Json))]),
        completed := do return (← parsedAt (scratch / "graph.json")).any fun value =>
          (value.getObjValAs? String "status").toOption == some "completed" }
    let producerExport (name : String) : Seeded :=
      { path := scratch / name,
        marked := markedWithError (scratch / name) "reason" "",
        seed := writeJson (scratch / name) (Json.mkObj
          [("schemaVersion", toJson (1 : Nat)), ("examples", toJson (#[] : Array Json))]),
        completed := exportCompleted (scratch / name) }
    -- A completed corpus export that the site's reader admits (`Site.Build.admitShard`, which also
    -- runs the qualifier executable): of no rule, recorded against the sources of this checkout as
    -- they are now (`Site.Build.currentSources`).
    discard <| toolPath repo "ruleExampleQualification"
    let current ← Regula.Site.Build.currentSources repo
    let shardAdmitted (path : FilePath) : IO Bool := do
      return (← (Regula.Site.Build.admitShard repo current path).toBaseIO) matches .ok _
    let writeShard (path : FilePath) : IO Unit :=
      writeJson path (Json.mkObj [("outcome", .str "COMPLETED"),
        ("schemaVersion", toJson (1 : Nat)), ("selected", toJson (#[] : Array Json)),
        ("completeCorpus", .bool false), ("checkerBefore", current), ("checkerAfter", current),
        ("records", toJson (#[] : Array Json))])
    let corpus : Seeded :=
      { path := scratch / "rule-examples.json",
        marked := fun _ => markedWith (scratch / "rule-examples.json") "reason"
          "invalid rule-example shard: planted" ("outcome", "INCOMPLETE"),
        seed := writeShard (scratch / "rule-examples.json"),
        completed := shardAdmitted (scratch / "rule-examples.json") }
    let site := scratch / "site"
    let artifact : Seeded :=
      { path := site, marked := fun _ => do return !(← Regula.Filesystem.isPresent site),
        seed := do
          IO.FS.createDirAll site
          writeJson (site / "build.json") (Json.mkObj [("schemaVersion", toJson (2 : Nat)),
            ("site", .str "seed"), ("producerVersion", .str "0.0.0"), ("dirty", .bool false),
            ("revision", .str (String.ofList (List.replicate 64 'a'))),
            ("publishable", .bool true)]),
        completed := do
          let some build ← parsedAt (site / "build.json") | return false
          return (build.getObjValAs? Bool "dirty").toOption == some false &&
            (build.getObjValAs? Bool "publishable").toOption == some true }
    -- A planted project root, without the documented examples that the producer campaign reads.
    let project := scratch / "project"
    IO.FS.createDirAll project
    IO.FS.writeFile (project / "lakefile.lean") ""
    IO.FS.writeFile (project / "lean-toolchain") (← IO.FS.readFile (repo / "lean-toolchain"))
    let project ← IO.FS.realPath project
    -- The first file named one of `names` in an entry of this process's `PATH` that runs with
    -- `--version`, exits 0 and prints a text that `accepted` admits.
    let onPath (names : List String) (accepted : String → Bool) : IO (Option FilePath) := do
      let mut found : Option FilePath := none
      for name in names do
        for directory in ((← IO.getEnv "PATH").getD "").splitOn ":" do
          let candidate := FilePath.mk directory / name
          if found.isNone && !directory.isEmpty && (← Regula.Filesystem.isPresent candidate) then
            if let .ok version ← (runProcess scratch candidate.toString #["--version"]).toBaseIO then
              if version.exitCode == 0 && accepted version.stdout then
                found := some candidate
      return found
    -- `directory/name` as a link to `target`, or why it could not be made.
    let link (target directory : FilePath) (name : String) : IO (Option String) := do
      IO.FS.createDirAll directory
      let linked ← runProcess scratch "ln" #["-s", target.toString, (directory / name).toString]
      if linked.exitCode == 0 then return none
      return some s!"early stop: could not link {target} as {directory / name}:\n{linked.output}"
    -- The guard of each started program queries Git before the program runs
    -- (`Regula.TaskManager.guard`), so each `PATH` below holds a link to the Git of this process's
    -- `PATH`: the run then passes the guard and stops at the failure that its `PATH` plants.
    let some git ← onPath ["git"] fun _ => true
      | return some "early stop: no git on PATH that runs with --version, which the guard of each \
          started program queries before the program runs"
    -- A directory that holds only Git as the whole `PATH`, so no `lean` is found, and no
    -- `LEAN_SYSROOT`.
    let noLean := scratch / "no-lean"
    if let some failure ← link git noLean "git" then return some failure
    let plain : Array (String × Option String) := #[("REGULA_TIMING", none),
      ("REGULA_QUALIFICATION_WRAPPER", none), ("REGULA_RECEIPT_TIMER", none)]
    let withoutLean := plain ++ #[("PATH", some noLean.toString), ("LEAN_SYSROOT", none)]
    -- GNU coreutils `env` as the one `timeout` of the whole `PATH`, beside Git: the bounded start
    -- selects it, since its `--version` names GNU coreutils
    -- (`Regula.Qualification.timeoutCommand`), and it ends with status 125 at the option
    -- `--signal=KILL` before it runs the command.
    let some gnuEnv ← onPath ["genv", "env"] (·.contains "GNU coreutils")
      | return some "early stop: no GNU coreutils env (genv or env) on PATH, which installs GNU \
          coreutils timeout beside it, to stand in for the timeout of a bounded start"
    let standIn := scratch / "stand-in"
    if let some failure ← link gnuEnv standIn "timeout" then return some failure
    if let some failure ← link git standIn "git" then return some failure
    let withStandIn := plain ++ #[("PATH", some standIn.toString)]
    -- The export of a bounded start that ended without running its command: its reason must give
    -- the status and the standard error of the stand-in, which names the option it refused.
    let startup := scratch / "startup.json"
    let startupExport : Seeded := { producerExport "startup.json" with
      marked := fun stderr => do
        let reason := ((← parsedAt startup).bind fun marked =>
          (marked.getObjValAs? String "reason").toOption).getD ""
        return (← markedWithError startup "reason" "" stderr) &&
          reason.contains "ended with exit status 125" && reason.contains "--signal=KILL" }
    let missing := (scratch / "missing-facts.json").toString
    let fileArgs (out : FilePath) : Array String :=
      #["--file", fixture.toString, "--claim", "kernel-only", "--json-out", out.toString]
    let production := "rule example production incomplete: "
    -- Each run: its label, its path, working directory, arguments and environment, the exit code
    -- of its early stop (`none`: any but 0) and each destination it names.
    let runs : List (String × String × FilePath × Array String ×
        Array (String × Option String) × Option UInt32 × List Seeded) := [
      ("ruleExamples", ruleExamples, repo, #["--policy-negative", repo.toString,
        fixture.toString, (scratch / "policy.json").toString], withoutLean, some 4,
        [result "policy.json" (some production)]),
      ("ruleExamples", ruleExamples, repo, #["--documentation", repo.toString,
        (repo / "docs").toString, (scratch / "documentation.json").toString], withoutLean, some 4,
        [result "documentation.json" (some production)]),
      ("ruleExamples", ruleExamples, repo, #["--injected-git-facts", missing, "--policy-negative",
        repo.toString, fixture.toString, (scratch / "facts.json").toString], plain, some 4,
        [result "facts.json" (some production)]),
      ("ruleExamples", ruleExamples, repo, #["--injected-git-facts", missing, "axiomGate"] ++
        fileArgs (scratch / "facts-gate.json"), plain, some 4,
        [result "facts-gate.json" (some production)]),
      ("axiomGate", gate, repo, fileArgs (scratch / "gate.json"), withoutLean,
        some Lint.Outcome.incomplete.exitCode, [result "gate.json" none]),
      ("freshChecker", (← toolPath repo "freshChecker").toString, repo,
        #["--json-out", graph.path.toString], withoutLean, some 1, [graph]),
      ("checkerSelftest", (← IO.appPath).toString, repo, #["--transcript-worker", "\"Planted\"",
        fixture.toString, "true", packet.path.toString], withoutLean, some 1, [packet]),
      ("qualify", qualify, project,
        #["--under-deadline", "producers", "--evidence", (scratch / "producers.json").toString],
        plain, some 1, [producerExport "producers.json"]),
      ("qualify", qualify, project, #["--under-deadline", "producers", "--evidence",
        (scratch / "extra.json").toString, "unexpected"], plain, some 1,
        [producerExport "extra.json"]),
      ("qualify", qualify, project,
        #["producers", "--evidence", (scratch / "bounded.json").toString], withoutLean, some 1,
        [producerExport "bounded.json"]),
      ("qualify", qualify, project,
        #["producers", "--evidence", startup.toString], withStandIn, some 1, [startupExport]),
      ("qualify", qualify, repo, #["--under-deadline", "rule-examples", "--evidence",
        corpus.path.toString, "--shard", "planted"], plain, some 1, [corpus]),
      ("qualify", qualify, repo, fileArgs (scratch / "proxy.json"),
        #[("REGULA_TIMING", none), ("REGULA_QUALIFICATION_WRAPPER", some "acceptance"),
          ("REGULA_RECEIPT_TIMER", none)], none, [result "proxy.json" none]),
      ("site", (← toolPath repo "site").toString, repo, #["build", "--out", site.toString], plain,
        some 2, [artifact])]
    for (program, path, cwd, args, env, code, destinations) in runs do
      for destination in destinations do
        destination.seed
        unless ← destination.completed do
          return some s!"early stop: the seed of {destination.path} is not a completed document \
            of its format"
      let result ← runProcess cwd path args (env := env)
      if result.exitCode == 0 || code.any (· != result.exitCode) then
        return some s!"early stop: {program} {args} did not stop early with exit \
          {(code.map toString).getD "other than 0"} (exit {result.exitCode}):\n{result.output}"
      for destination in destinations do
        unless (← destination.marked result.stderr) && !(← destination.completed) do
          let held ← match ← Regula.Filesystem.metadataIfPresent destination.path with
            | some { type := .dir, .. } => pure "a directory"
            | some _ => IO.FS.readFile destination.path
            | none => pure "nothing"
          return some s!"early stop: {program} {args} left {destination.path} without the \
            incomplete mark and the reason, or admitted as completed; it holds {held}\n\
            {result.output}"
    -- The verification wrapper, `scripts/verify.sh`, in a copy of its files, so that its `tmp` is
    -- the copy's. With no `lean` on its `PATH`, the first corpus shard's attempt stops before the
    -- driver's begin-attempt (`RegulaVerification.beginAttempt`), so no code of the attempt runs:
    -- the export of an earlier attempt and the corpus receipt (`RegulaVerification.corpusEvidence`)
    -- each keep their bytes. The export was recorded before `foundation_manifest.json` changed:
    -- the current sources (`Site.Build.sourcePathsAt`) with that manifest's text changed. Right
    -- after the stopped attempt, the site's reader (`Site.Build.admitShard`) must refuse it.
    let wrapper := scratch / "wrapper"
    IO.FS.createDirAll (wrapper / "scripts")
    IO.FS.createDirAll (wrapper / "lean")
    IO.FS.createDirAll (wrapper / "tmp")
    let files : List FilePath :=
      ["scripts" / "verify.sh", "lean" / "RegulaVerification.lean", "lean-toolchain"]
    for file in files do
      IO.FS.writeFile (wrapper / file) (← IO.FS.readFile (repo / file))
    let manifestPath := (repo / "foundation_manifest.json").toString
    let captured ←
      Regula.Qualification.RuleExamples.capture (← Regula.Site.Build.sourcePathsAt repo)
    let earlier := Regula.Qualification.RuleExamples.snapshotOf <| captured.map fun (uri, text) =>
      (uri, if uri == manifestPath then text ++ "\n" else text)
    -- The export of the first of the three corpus shards (`RegulaVerification.shardEvidence`).
    let shard := wrapper / "tmp" / "rule-examples-1of3.json"
    writeJson shard (Json.mkObj [("outcome", .str "COMPLETED"),
      ("schemaVersion", toJson (1 : Nat)), ("selected", toJson (#[] : Array Json)),
      ("completeCorpus", .bool false), ("checkerBefore", earlier), ("checkerAfter", earlier),
      ("records", toJson (#[] : Array Json))])
    let seeded ← IO.FS.readBinFile shard
    let receipt := wrapper / "tmp" / "rule-examples.json"
    writeShard receipt
    let receipted ← IO.FS.readBinFile receipt
    let shellPath := "/usr/bin:/bin"
    for directory in ["/usr/bin", "/bin"] do
      if ← Regula.Filesystem.isPresent (FilePath.mk directory / "lean") then
        return some s!"early stop: {directory} holds lean, so the wrapper's PATH {shellPath} \
          cannot leave it out"
    let stopped ← runProcess wrapper "/bin/bash"
      #[(wrapper / "scripts" / "verify.sh").toString, "diagnostics", "rule-examples", "1/3"]
      (env := #[("PATH", some shellPath)])
    unless stopped.exitCode == 127 && (← IO.FS.readBinFile shard).data == seeded.data &&
        (← IO.FS.readBinFile receipt).data == receipted.data do
      return some s!"early stop: scripts/verify.sh diagnostics rule-examples 1/3 with no lean on \
        its PATH did not stop with exit 127 and leave the earlier shard export and corpus receipt \
        (exit {stopped.exitCode}):\n{stopped.output}"
    if ← shardAdmitted shard then
      return some s!"early stop: right after scripts/verify.sh stopped without lean, the site's \
        reader admitted a shard export recorded before {manifestPath} changed"
    -- Each run whose destination holds a file that is not a document of Regula, such as a file
    -- that the run reads, is refused, and its mark writes nothing there
    -- (`Regula.Destination.write`, `Regula.Destination.refusal`): it must exit
    -- with its refusal's code and the reason, and each file must keep its bytes, or stay absent.
    let request := scratch / "alias-request.json"
    let publish := scratch / "alias-publish.json"
    let requested : Inspection.ReportWorkerRequest := {
      modules := #[], searchRoots := #[], sourceRoots := #[], sourceBindings := #[],
      ownership := {}, historyMemo := (scratch / "history").toString, priors := #[],
      publish := publish.toString }
    IO.FS.writeFile request (toJson requested).compress
    let facts := scratch / "alias-facts.json"
    IO.FS.writeFile facts "[]\n"
    let source := scratch / "AliasSource.lean"
    IO.FS.writeFile source (← IO.FS.readFile fixture)
    let manifest := scratch / "alias-manifest.json"
    IO.FS.writeFile manifest (← IO.FS.readFile (repo / "foundation_manifest.json"))
    -- A second name of the manifest, which `realPath` does not join with the first.
    let hardLink := scratch / "alias-hard-link.json"
    let linked ← runProcess scratch "ln" #[manifest.toString, hardLink.toString]
    unless linked.exitCode == 0 do
      return some s!"early stop: could not link {manifest} as {hardLink}:\n{linked.output}"
    -- A symbolic link to a completed result.
    let symbolic := scratch / "alias-symbolic.json"
    let pointed ← runProcess scratch "ln" #["-s", completed.toString, symbolic.toString]
    unless pointed.exitCode == 0 do
      return some s!"early stop: could not link {symbolic} to {completed}:\n{pointed.output}"
    -- The configuration of a dependency, which Lake loads with the workspace.
    let dependency := scratch / "vendor" / "lakefile.toml"
    IO.FS.createDirAll (scratch / "vendor")
    IO.FS.writeFile dependency "name = \"vendor\"\n"
    let documentation := scratch / "Documentation.md"
    IO.FS.writeFile documentation "# Documentation\n"
    -- A JSON document with the member `rules` of a registry export and none of its identity
    -- members, which no reader of Regula identifies as Regula's
    -- (`Regula.Destination.regulaDocument`).
    let rulesOnly := scratch / "rules-only.json"
    IO.FS.writeFile rulesOnly "{\"rules\":[]}\n"
    -- A JSON document with the identity members of a registry export and not its rules, which the
    -- reader of a registry refuses (`validateRegistry`), so no signature of a kind recognizes it.
    let identityOnly := scratch / "identity-only.json"
    IO.FS.writeFile identityOnly "{\"schemaVersion\":4,\"producerVersion\":\"0.0.0\",\
      \"toolchain\":\"leanprover/lean4:v4.34.0\",\"sourceRevision\":\"0000000\"}\n"
    IO.FS.createDirAll (scratch / "through")
    let configuration := Lint.Outcome.configuration.exitCode
    let notRegula := "not a document that Regula wrote"
    let aliases : List (String × String × Array String × UInt32 × String × List FilePath) := [
      ("axiomGate", gate, #["--declaration-report-worker", request.toString, request.toString],
        configuration, notRegula, [request]),
      ("axiomGate", gate, #["--frontend-worker", request.toString, source.toString],
        configuration, notRegula, [request, source]),
      ("axiomGate", gate, fileArgs source, configuration, notRegula, [source]),
      ("axiomGate", gate, #["--registry-out", rulesOnly.toString], configuration, notRegula,
        [rulesOnly]),
      ("axiomGate", gate, #["--registry-out", identityOnly.toString], configuration, notRegula,
        [identityOnly]),
      ("axiomGate", gate, fileArgs symbolic, configuration, "is a symbolic link",
        [symbolic, completed]),
      ("freshChecker", (← toolPath repo "freshChecker").toString,
        #["--manifest", manifest.toString, "--json-out", hardLink.toString], 1, notRegula,
        [manifest, hardLink]),
      ("freshChecker", (← toolPath repo "freshChecker").toString,
        #["--json-out", dependency.toString], 1, notRegula, [dependency]),
      ("qualify", qualify, #["--under-deadline", "producers", "--evidence", source.toString], 1,
        notRegula, [source]),
      ("qualify", qualify, #["producers", "--evidence", source.toString], 1, notRegula, [source]),
      ("ruleExamples", ruleExamples, #["--injected-git-facts", facts.toString, "axiomGate"] ++
        fileArgs facts, configuration, notRegula, [facts]),
      ("ruleExamples", ruleExamples, #["--policy-negative", repo.toString, source.toString,
        (scratch / "through" / ".." / "AliasSource.lean").toString], 4, notRegula, [source]),
      ("ruleExamples", ruleExamples, #["--documentation", repo.toString, (repo / "docs").toString,
        documentation.toString], 4, notRegula, [documentation])]
    -- The report worker's published admission, which the request names, is a destination of its
    -- own: the refused worker marks it, and the reader of an admission must refuse the mark.
    let publishRefused : IO Bool := do
      unless ← Regula.Filesystem.isPresent publish do return true
      let some marked ← parsedAt publish | return false
      let read : Except String Admission.Completed := fromJson? marked
      return (marked.getObjValAs? String "status").toOption == some "incomplete" && !read.isOk
    for (program, path, args, code, phrase, files) in aliases do
      let held : IO (List (Option ByteArray)) := files.mapM fun file => do
        if ← Regula.Filesystem.isPresent file then return some (← IO.FS.readBinFile file)
        else return none
      let before ← held
      let result ← runProcess repo path args (env := plain)
      unless result.exitCode == code && result.stderr.contains phrase &&
          (← held).map (·.map (·.data)) == before.map (·.map (·.data)) && (← publishRefused) do
        return some s!"early stop: {program} {args} was not refused with exit {code} and the \
          reason that holds \"{phrase}\", leaving {files} as they were and {publish} absent or \
          marked (exit {result.exitCode}):\n{result.output}"
    unless ← Regula.Filesystem.isPresent publish do
      return some s!"early stop: the refused report worker did not mark its published admission \
        {publish}"
    -- Two destinations that may be one entry, as on a file system that folds case: the run marks
    -- them, so the earlier result there is gone, then refuses (`Regula.Destination.sameEntry`).
    let lower := scratch / "one.json"
    let upper := scratch / "ONE.json"
    copyDocument completed lower
    let overlapping ← runProcess repo gate #["--json-out", lower.toString, "--acceptance-link",
      upper.toString] (env := plain)
    let marks ← [lower, upper].filterMapM fun path => do
      if ← Regula.Filesystem.isPresent path then return some (← parsedAt path) else return none
    unless overlapping.exitCode == configuration &&
        overlapping.stderr.contains "may name one entry" && !marks.isEmpty &&
        marks.all (·.any fun mark =>
          (mark.getObjValAs? String "status").toOption == some "incomplete") do
      return some s!"early stop: axiomGate with --json-out {lower} and --acceptance-link {upper} \
        did not mark them incomplete and refuse (exit {overlapping.exitCode}):\n\
        {overlapping.output}"
    -- A destination with a `..` below an absent directory names an entry that depends on what the
    -- run makes: the run refuses it before it makes anything, so the directory stays absent and
    -- the result that the path would reach keeps its bytes (`Regula.Destination.place`).
    let absent := scratch / "absent"
    let escaping := absent / ".." / "completed.json"
    let held ← IO.FS.readBinFile completed
    let refused ← runProcess repo gate #["--registry-out", escaping.toString] (env := plain)
    unless refused.exitCode == configuration && refused.stderr.contains "has a `..` component" &&
        !(← Regula.Filesystem.isPresent absent) &&
        (← IO.FS.readBinFile completed).data == held.data do
      return some s!"early stop: axiomGate with --registry-out {escaping} was not refused before \
        it made {absent} (exit {refused.exitCode}):\n{refused.output}"
    -- A destination whose last component names no file, `new/` or `new/.`, names a directory and
    -- not a file in it: the run refuses it by its name before it makes anything, so `new` stays
    -- absent (`Regula.Destination.place`).
    let unnamed := scratch / "new"
    for named in [s!"{unnamed}/", s!"{unnamed}/."] do
      let refused ← runProcess repo gate #["--registry-out", named] (env := plain)
      unless refused.exitCode == configuration && refused.stderr.contains "names no file" &&
          !(← Regula.Filesystem.isPresent unnamed) do
        return some s!"early stop: axiomGate with --registry-out {named} was not refused by its \
          name before it made {unnamed} (exit {refused.exitCode}):\n{refused.output}"
    -- A directory at the `--out` of `site build` that holds something other than an artifact of a
    -- build, such as the documentation of a repository, keeps its files. Without its evidence the
    -- parser refuses the run, and the guard's refusal removes no directory that holds no artifact
    -- (`Regula.Site.Build.invalidateRefused`). With evidence the build's first step refuses it
    -- (`Regula.Site.Build.artifactRefusal`).
    let foreignSite := scratch / "foreign-site"
    IO.FS.createDirAll foreignSite
    IO.FS.writeFile (foreignSite / "README.md") "# Documentation\n"
    let missing := (scratch / "missing-evidence.json").toString
    let runs : List (Array String × Option String) :=
      [(#[], none), (#["--evidence", missing], some "holds neither a build.json")]
    for (args, refusal) in runs do
      let built ← runProcess repo (← toolPath repo "site").toString
        (#["build", "--out", foreignSite.toString] ++ args) (env := plain)
      let readme ← (IO.FS.readFile (foreignSite / "README.md")).toBaseIO
      unless built.exitCode != 0 && refusal.all (fun text => built.stderr.contains text) &&
          readme.toOption == some "# Documentation\n" do
        return some s!"early stop: site build --out {foreignSite} {args} was not refused with its \
          files kept (exit {built.exitCode}):\n{built.output}"
    -- An empty file holds no bytes to lose, and a hard link to a result of Regula names a file
    -- that another name shares: each is replaced, and the other name keeps its bytes.
    let empty := scratch / "empty.json"
    IO.FS.writeFile empty ""
    let shared := scratch / "shared.json"
    copyDocument completed shared
    let sharing := scratch / "sharing.json"
    let shares ← runProcess scratch "ln" #[shared.toString, sharing.toString]
    unless shares.exitCode == 0 do
      return some s!"early stop: could not link {shared} as {sharing}:\n{shares.output}"
    -- A destination name of 255 bytes, the longest that a file system with a 255-byte limit admits,
    -- holding a completed result: the new file beside it has a short name of its own
    -- (`Regula.Filesystem.writeReplacing`).
    let long := scratch / (String.ofList (List.replicate 250 'r') ++ ".json")
    copyDocument completed long
    -- A mark that an earlier version of Regula wrote at a worker's output, a document of Regula of
    -- a different kind from a result, with no identity member: it is replaced too.
    let earlierMark := scratch / "earlier-mark.json"
    IO.FS.writeFile earlierMark "{\"status\":\"incomplete\",\"reason\":\"stopped\"}\n"
    let kept ← IO.FS.readBinFile shared
    for destination in [empty, sharing, long, earlierMark] do
      let result ← runProcess repo gate (fileArgs destination) (env := withoutLean)
      unless result.exitCode == Lint.Outcome.incomplete.exitCode &&
          (← markedWith destination "unresolved" started) &&
          (← IO.FS.readBinFile shared).data == kept.data do
        return some s!"early stop: axiomGate with --json-out {destination} did not mark it \
          incomplete and leave {shared} as it was (exit {result.exitCode}):\n{result.output}"
    return none

/-- Public CLI fixtures: the complete sweep for qualification, or the unchanged smoke subset for
the default development tier, then, in the complete sweep, the source-attribution controls. With
`shard`, the sweep checks that shard's fixtures (`fixturesOfShard`), and the source-attribution
controls run in their shard alone (`cliAttributionShard`). -/
private def runCli (repo : FilePath) (jobs : Nat) (fullCli : Bool)
    (shard : Option (Fin cliShards)) (fixtures : Array FixtureSpec)
    (failures : IO.Ref (Array String)) : IO Unit := do
  let smokeFixtures := fixtures.filter (smokeFixtureNames.contains ·.moduleName)
  if smokeFixtures.size != smokeFixtureNames.size then
    failures.modify (·.push "smoke: expected smoke fixtures are missing from the manifest")
  for fixture in smokeFixtures do
    if fixture.fileAuditExclusion.isSome then
      failures.modify (·.push s!"smoke: {fixture.moduleName} is excluded from the file audits")
  -- The build-bound sweep contains every smoke control; each runs once. A fixture whose entry
  -- states a `fileAuditExclusion` keeps its shard, so the exclusion moves no other fixture.
  let selected := if fullCli then fixturesOfShard (by decide) shard fixtures else smokeFixtures
  let cliFixtures := selected.filter (·.fileAuditExclusion.isNone)
  let excluded := selected.filter (·.fileAuditExclusion.isSome)
  let cliLabel := if fullCli then "full CLI sweep" else "CLI smoke"
  let cliResults ← loggedPhase cliLabel <|
    mapConcurrent jobs cliFixtures (checkFixtureCli repo)
  for result in cliResults do appendFailure failures result
  IO.println <| s!"self-test {cliLabel}: " ++
    (if cliResults.all (·.isNone) then "PASS" else "FAIL") ++
    s!" ({cliFixtures.size} real axiomGate --file invocations)" ++ shardNote shard
  for fixture in excluded do
    IO.println s!"self-test {cliLabel}: {fixture.moduleName} not run through axiomGate --file \
      (the fixtures partition checks it): {fixture.fileAuditExclusion.getD ""}"
  if runsIn shard cliAttributionShard then
    let refused ← loggedPhase "task manager" (taskManagerControl repo)
    appendFailure failures refused
    IO.println <| "self-test task manager: " ++ (if refused.isNone then "PASS" else "FAIL") ++
      " (axiomGate, lint, docFenceAudit, qualify, site and the self-test with LEAN_NUM_THREADS=0 \
        refuse before their runs, with the incomplete exit code, the guard's reason line and no \
        result line; each destination they name, a result, an acceptance link, a worker packet, \
        the report worker's published admission, an evidence export or the launcher's report \
        that held a completed document of its format, ends marked incomplete with the reason, \
        including the proxy of axiomGate and the workers, and a self-hosted digest and a site \
        artifact end removed)"
    let stopped ← loggedPhase "early stop" (earlyStopControl repo)
    appendFailure failures stopped
    IO.println <| "self-test early stop: " ++ (if stopped.isNone then "PASS" else "FAIL") ++
      " (ruleExamples, axiomGate, freshChecker, qualify, site and the self-test, each stopped \
        early with Lean's task manager by an injected failure, end with the exit code of their \
        early stop; each destination they name that held a completed document of its format ends \
        marked incomplete with the reason, the error's text for a production of ruleExamples and \
        the export of qualify producers, and a site artifact ends removed; a destination that \
        holds a file that is not a document of Regula is refused and keeps its bytes, \
        overlapping destinations are marked and refused, and an empty file, a hard link to a \
        result, a 255-byte name and an earlier version's worker mark are marked; after \
        scripts/verify.sh stops with no lean, the site's reader refuses a shard export recorded \
        before foundation_manifest.json changed)"
  if fullCli && runsIn shard cliAttributionShard then
    let attribution ← loggedPhase "source attribution" <|
      withScratch repo "checker-source-attribution" fun scratch =>
        sourceAttributionControls scratch (runBinary repo "axiomGate" ·)
    for failure in attribution do failures.modify (·.push failure)
    IO.println <| "self-test source attribution: " ++
      (if attribution.isEmpty then "PASS" else "FAIL") ++
      " (a declaration of every generated family attributed, those at one location printed in one \
        block; a metaprogram theorem, a user-written ofNat and an elaborator under a structure's \
        name, and user-written theorems named like auxiliary proofs, not attributed)"

/-- The parts of the clean-checkout environment controls (`fenceEnvironmentQualification`), each
with its shard. -/
private def fenceEnvironmentParts : List (Fin environmentsShards × FenceEnvironmentPart) :=
  [(environmentsShard 3, .docFences), (environmentsShard 4, .fileMode),
    (environmentsShard 3, .freshChecker)]

/-- `fenceEnvironmentParts` gives every part exactly one shard: its parts are
`FenceEnvironmentPart.all`, in order, which lists every part (`FenceEnvironmentPart.mem_all`) and
none twice (`FenceEnvironmentPart.all_nodup`). -/
private theorem fenceEnvironmentParts_parts :
    fenceEnvironmentParts.map (·.2) = FenceEnvironmentPart.all :=
  rfl

/-- The variants of the external-adopter controls (`adopterQualification`), each with its shard:
the `lakefile.toml` adopter, which also runs the unlisted-module and fresh-plan controls, in one,
and the `lakefile.lean` and relative-path adopters in the next. -/
private def adopterParts : List (Fin environmentsShards × AdopterVariant) :=
  [(environmentsShard 1, .toml), (environmentsShard 2, .lean), (environmentsShard 2, .relative)]

/-- `adopterParts` gives every variant exactly one shard: its variants are `AdopterVariant.all`, in
order, which lists every variant (`AdopterVariant.mem_all`) and none twice
(`AdopterVariant.all_nodup`). -/
private theorem adopterParts_variants : adopterParts.map (·.2) = AdopterVariant.all :=
  rfl

/-- Build-bound packaging and fresh-state controls, each retaining its isolated
source/build directory and exact failure accumulation. With `shard`, each runs in its shard alone:
the public fence corpus in the first, the external-adopter variants in theirs (`adopterParts`), the
parts of the clean-checkout environment controls in theirs (`fenceEnvironmentParts`) and the public
surface in the last. -/
private unsafe def runEnvironments (layout : SourceLayout) (repo : FilePath)
    (shard : Option (Fin environmentsShards)) (failures : IO.Ref (Array String)) : IO Unit := do
  let fenceParts := (inShard shard fenceEnvironmentParts).map (·.2)
  let adopters := (inShard shard adopterParts).map (·.2)
  -- This tier only starts after the earlier subprocess tasks have joined.
  -- Its builds live in isolated copies; the other public controls cannot
  -- consume or alter those owned outputs.
  let fenceEnvTask ← IO.asTask (prio := .dedicated) do
    if fenceParts.isEmpty then return #[]
    loggedPhase "clean-checkout environments" <|
      withScratch repo "checker-fence-env" fun scratch =>
        fenceEnvironmentQualification layout repo scratch fenceParts
  if runsIn shard (environmentsShard 0) then
    withScratch repo "checker-scanner" fun scratch => do
      for failure in ← loggedPhase "public fence corpus" (publicScannerQualification repo scratch) do
        failures.modify (·.push failure)
    IO.println s!"self-test public fence corpus: completed \
      ({(fenceCorpusCases "" "" ++ publicOnlyFenceCases).size} end-to-end cases)"
  unless adopters.isEmpty do
    withScratch repo "checker-adopter" fun scratch => do
      let adopter ← loggedPhase "external adopters" (adopterQualification repo scratch adopters)
      for failure in adopter do failures.modify (·.push failure)
      IO.println <| "self-test external adopters: " ++
        (if adopter.isEmpty then "PASS" else "FAIL") ++
        s!" ({", ".intercalate (adopters.map (·.label))} adopters: empty exclusions, fresh \
          positive gate, --project, omitted exe, rogue module" ++
        (if adopters.contains .toml then
          "; the toml adopter also unlisted-module contamination and fresh plan)" else ")")
  let fenceEnv ← IO.ofExcept (← IO.wait fenceEnvTask)
  for failure in fenceEnv do failures.modify (·.push failure)
  unless fenceParts.isEmpty do
    IO.println <| "self-test fence environment: " ++
      (if fenceEnv.isEmpty then "PASS" else "FAIL") ++
      s!" ({", ".intercalate (fenceParts.map (·.controls))})"
  if runsIn shard (environmentsShard 5) then
    let surface ← loggedPhase "public surface" <| runBinary repo "axiomGate" #["--incremental"]
    if !surface.succeeded then
      failures.modify (·.push
        s!"surface/baseline: public incremental gate failed:\n{surface.output}")
    IO.println "self-test public controls: completed (surface)"

/-- Ordinary-build controls are a separate required partition so they do not
share the clean-checkout environment controls' CI time budget. With `shard`, only that shard's
controls run (`BuildLintQualification.qualify`). -/
private def runBuildPolicy (repo : FilePath) (jobs : Nat)
    (shard : Option (Fin BuildLintQualification.shards)) (failures : IO.Ref (Array String)) :
    IO Unit := do
  withScratch repo "checker-build-lint" fun scratch => do
    let buildLint ← loggedPhase "ordinary-build policy controls" <|
      BuildLintQualification.qualify repo scratch jobs shard
    for failure in buildLint do failures.modify (·.push failure)
    IO.println <| "self-test build policy linter: " ++
      (if buildLint.isEmpty then "PASS" else "FAIL") ++ shardNote shard

/-- `lake lint` driver controls: Lake dispatch in both lakefile formats and exit classes, and
the cold compiler guard of `lakefile.lean`, which refuses an inherited `LEAN_SYSROOT` child
that fails and one that succeeds without reporting the running compiler's identity, then loads
the same package again. The shared audit body's detectors are qualified by the build-policy
partition. With `shard`, only that shard's control groups run and are named
(`LintQualification.qualify`). -/
private def runLintDriver (repo : FilePath) (jobs : Nat)
    (shard : Option (Fin LintQualification.shards)) (failures : IO.Ref (Array String)) :
    IO Unit := do
  withScratch repo "checker-lake-lint" fun scratch => do
    let (names, lint) ← loggedPhase "lake lint driver controls" <|
      LintQualification.qualify repo scratch jobs shard
    for failure in lint do failures.modify (·.push failure)
    IO.println <| "self-test lake lint driver: " ++ (if lint.isEmpty then "PASS" else "FAIL") ++
      match shard with
      | none => ""
      | some selected => shardDescription (shardLabel selected) (LintQualification.shards - 1) names

/-- Full and selected runs use the same group implementations. This exhaustive
match assigns each supported partition exactly one implementation. `fullCli` selects the
complete CLI sweep of the build-bound tier instead of the default tier's smoke subset, and
`shard` one shard of the partition (`Options.validate` admits only a shard the partition has). -/
private unsafe def runPartition (layout : SourceLayout) (partition : Partition) (repo : FilePath)
    (jobs : Nat) (fullCli : Bool) (shard : Option (Nat × Nat))
    (fixtures : Array FixtureSpec) (failures : IO.Ref (Array String)) : IO Unit :=
  match partition with
  | .fixtures => runFixtures repo jobs (shard.bind (shardOf? fixturesShards)) fixtures failures
  | .structural => runStructural layout repo jobs (shard.bind (shardOf? structuralShards)) failures
  | .execution => runExecution layout repo jobs (shard.bind (shardOf? executionShards)) failures
  | .cli => runCli repo jobs fullCli (shard.bind (shardOf? cliShards)) fixtures failures
  | .environments =>
      runEnvironments layout repo (shard.bind (shardOf? environmentsShards)) failures
  | .buildPolicy =>
      runBuildPolicy repo jobs (shard.bind (shardOf? BuildLintQualification.shards)) failures
  | .lintDriver => runLintDriver repo jobs (shard.bind (shardOf? LintQualification.shards)) failures

/-- The combined public command must preserve Markdown discovery even in
subdirectories pruned by the generic project copier. Exercise a fresh positive,
a single invalid fence, and its restored positive in an isolated tiny project. -/
private def combinedSnapshotQualification (repo : FilePath) : IO (Array String) :=
  withScratch repo "combined-snapshot-control" fun project => do
    Regula.Filesystem.copyFile (repo / "lean-toolchain") (project / "lean-toolchain")
    IO.FS.writeFile (project / "lakefile.toml") <|
      "name = \"snapshot_control\"\n" ++ observerPluginToml ++
        "[leanOptions]\nautoImplicit = false\n" ++
        "relaxedAutoImplicit = false\nlinter.missingDocs = true\n" ++
        observedTargetToml .library "Snapshot" ++
        observedTargetToml .library "Companion" ++
        regulaRequireToml repo
    IO.FS.writeFile (Manifest.defaultPath project)
      "{\"schema-version\":2,\"surfaces\":[{\"library\":\"Snapshot\",\"executables\":[],\"claim\":\
        \"standard-logical\",\"execution\":\"report\",\"rationale\":\"Control\"},{\"library\":\"Com\
        panion\",\"executables\":[],\"claim\":\"standard-logical\",\"execution\":\"report\",\"ratio\
        nale\":\"Parallel surface \
        control\"}],\"excluded-libraries\":[],\"excluded-executables\":[]}"
    -- Lake writes the lock manifest of a project that has none at its first build; written
    -- before the audits, it is not a configuration change during one.
    -- This generated configuration has no requirements; update creates only its initial manifest.
    let updated ← runProcess project "lake" #["update"] scrubbedLeanPathEnv
    unless updated.succeeded do return #[s!"combined snapshot/update: {updated.output}"]
    let docs := project / "docs" / ".cache"
    IO.FS.createDirAll docs
    let mut failures := #[]
    for phase in
        #["baseline", "invalid", "restored", "invalid-source", "invalid-companion",
            "source-restored"] do
      IO.FS.writeFile (project / "Snapshot.lean") <|
        "/-! Source used for fence-import isolation qualification. -/\n" ++
        (if phase == "invalid-source" then "/-- An unproved assumption. -/\naxiom unproved : True\n"
        else "/-- A proved control. -/\ntheorem snapshot_ok : True := True.intro\n")
      IO.FS.writeFile (project / "Companion.lean") <|
        "/-! Companion surface for fence-import isolation qualification. -/\n" ++
        (if phase == "invalid-companion" then
          "/-- An unproved assumption. -/\naxiom companion_unproved : True\n"
        else "/-- A proved control. -/\ntheorem companion_ok : True := True.intro\n")
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
        else result.succeeded && result.output.contains s!"{Documentation.positiveSummary}=1/1"
      if !accepted then failures := failures.push s!"combined snapshot/{phase}: {result.output}"
    return failures

/-- Distinguish the canonical force-loaded collector from a real import of an
excluded root-library module, through the public fresh project entry point. -/
private def forcedCollectorQualification (repo scratch : FilePath) : IO (Array String) := do
  let layout ← loadSourceLayout repo
  discard <| prepareScratchRepo repo scratch
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

/-- Runs one focused control, each over the repository's own build. Prints each failure and
returns `1` when any control fails, `0` otherwise. -/
private unsafe def runFocused : Focused → IO UInt32
  | .forcedCollector => do
    let repo ← repoRoot
    let build ← runProcess repo "lake" #["build", "axiomGate"]
    if !build.succeeded then IO.println build.output; return 1
    let failures ← withScratch repo "forced-collector-control" (forcedCollectorQualification repo)
    for failure in failures do IO.println s!"FAIL: {failure}"
    if failures.isEmpty then
        IO.println "forced collector qualification: PASS (fresh positive, excluded-source refusal, \
          restored)"
    return if failures.isEmpty then 0 else 1
  | .policyTransport => do
    let failures := PolicyQualification.transport
    for failure in failures do IO.println s!"FAIL: {failure}"
    if failures.isEmpty then IO.println "policy transport qualification: PASS"
    return if failures.isEmpty then 0 else 1
  | .nativeAdopter => do
    let repo ← repoRoot
    let build ← runProcess repo "lake" #["build", "axiomGate", "Regula.Linter"]
    if !build.succeeded then IO.println build.output; return 1
    let failures ← withScratch repo "native-adopter-control" (PolicyQualification.nativeImport repo)
    for failure in failures do IO.println s!"FAIL: {failure}"
    return if failures.isEmpty then 0 else 1
  | .policyDomain => do
    let repo ← repoRoot
    let build ← runProcess repo "lake" #["build", "axiomGate"]
    if !build.succeeded then IO.println build.output; return 1
    let failures ← withScratch repo "policy-domain-controls" fun scratch => do
      return PolicyQualification.transport ++ (← PolicyQualification.publicPaths repo scratch)
    for failure in failures do IO.println s!"FAIL: {failure}"
    if failures.isEmpty then
        IO.println "policy domain qualification: PASS (transport and public paths)"
    return if failures.isEmpty then 0 else 1
  | .combinedSnapshot => do
    let failures ← combinedSnapshotQualification (← repoRoot)
    for failure in failures do IO.println s!"FAIL: {failure}"
    if failures.isEmpty then IO.println "combined snapshot qualification: PASS"
    return if failures.isEmpty then 0 else 1
  | .fences => do
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
  | .buildLint => do
    let repo ← repoRoot
    let build ← runProcess repo "lake" #["build", "axiomGate"]
    if !build.succeeded then IO.println build.output; return 1
    return ← withScratch repo "build-lint-controls" fun scratch => do
      let failures ← BuildLintQualification.qualify repo scratch 4
      for failure in failures do IO.println s!"FAIL: {failure}"
      if failures.isEmpty then IO.println "build policy linter qualification: PASS"
      return if failures.isEmpty then 0 else 1
  | .compilerPaths => do
    let repo ← repoRoot
    let build ← runProcess repo "lake" #["build", "axiomGate"]
    if !build.succeeded then IO.println build.output; return 1
    return ← withScratch repo "compiler-path-controls" fun scratch => do
      let failures ← CompilerPaths.qualify repo scratch
      for failure in failures do IO.println s!"FAIL: {failure}"
      return if failures.isEmpty then 0 else 1

/-- Internal transcript worker: one isolated fresh-frontend re-elaboration with the checker's own
pinned frontend, serialized as JSON. The batched fixture pipeline spawns these so every transcript
is built in exactly the isolated process environment the public CLI provides (a fresh process can
never see the harness's imported attribute state), before the parent shared environment load. -/
private unsafe def runTranscriptWorker (moduleWire source rejectWarnings out : String) :
    IO UInt32 := do
  let moduleName ← IO.ofExcept <| Regula.RegistryCodec.parseName
      (← IO.ofExcept <| Regula.Checker.PolicyCodec.parse moduleWire)
  let transcript ← Frontend.buildCurrentSearchPath moduleName source (rejectWarnings != "false")
  writeDestination out
      (workerPacket (sourceWorkerRequest "transcript" moduleName source transcript.sourceContent)
          (toJson transcript))
  return 0

/-- Mark each file that `selection` writes for a later reader (`Selection.destinations`)
incomplete: a worker's packet with `reason` (`invalidateOutput`), and a self-hosted digest by its
removal (`clearSelfHostedDigest`), which the `diagnostics` gate refuses as missing. Prints a line
for each file that cannot be marked; a selection that writes none marks nothing. -/
def markIncomplete (selection : Selection) (reason : String) : IO Unit := do
  for destination in selection.destinations do
    let (shown, mark) : String × IO Unit := match destination with
      | .packet out => (out, invalidateOutput out reason)
      | .selfHostedDigest input =>
        (s!"the {input.name} self-hosted digest", do clearSelfHostedDigest (← repoRoot) input)
    try mark
    catch error =>
      IO.eprintln s!"checkerSelftest: could not mark the destination {shown} incomplete: {error}"

/-- The reason to refuse `selection`, if the file of a worker's packet that it writes holds
something that the run may not replace (`Regula.Destination.refusal`). The mark leaves such a file
as it was (`Regula.Destination.write`), and the worker's write would replace it. The digest of
a self-hosted input is a file below the repository's `tmp/` that the mark removes
(`clearSelfHostedDigest`). -/
def refusalOf (selection : Selection) : IO (Option String) :=
  Regula.Destination.refusal (selection.destinations.filterMap fun
    | .packet out => some ⟨out⟩
    | .selfHostedDigest _ => none)

/-- Runs the qualification suite: one of the focused `--…-only` controls or the internal
transcript worker when the arguments name it (`Selection.parse`), otherwise the baseline build and
then the selected tiers or partition. It marks the files that the selection writes incomplete
(`markIncomplete`), so a run that stops before its write leaves no earlier packet or digest at a
destination that it marked. It then refuses a selection whose packet file it may not replace
(`refusalOf`): a packet file that is a symbolic link, for one, is refused and keeps whatever it
points to. Prints each failure and returns `1` when any control fails, `0` otherwise. -/
unsafe def run (args : List String) : IO UInt32 := do
  let selection ← IO.ofExcept ((Selection.parse args).mapError IO.userError)
  markIncomplete selection "the job has not completed"
  if let some reason ← refusalOf selection then throw <| IO.userError s!"refused: {reason}"
  let mut options : SelftestArguments.Options := {}
  match selection with
  | .focused control => return ← runFocused control
  | .transcriptWorker moduleWire source rejectWarnings out =>
    return ← runTranscriptWorker moduleWire source rejectWarnings out
  | .suite selected => options := selected
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
  -- the checker executables their controls run, the modules their projects import from it and,
  -- where one of them reads it, the fixture import anchor, the fixture modules other fixtures
  -- import and the claimed positive surface, so every later phase sees it built.
  let surfaceManifest ← parsedManifest (Manifest.defaultPath repo)
  let baselines := selected.map (baselineOf · options.shard)
  let tools := baselineTools baselines
  let fixtureTargets ← if baselines.any (·.surface) then
      pure (((← importedFixtures repo).filter (· != structuralFixture)).push structuralFixture)
    else pure #[]
  let build ← loggedPhase "baseline build" <| runProcess repo "lake"
    (#["build"] ++ tools.toArray ++ (baselines.flatMap (·.modules)).eraseDups.toArray ++
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
      | some (index, count) => s!"checker self-test partition {partition.label} shard \
          {index}/{count}: PASS \
          ({elapsed / 1000000000}s; this shard alone is not the partition, and no partition \
          alone is full qualification)"
    return 0
  IO.println <| s!"checker self-test: PASS ({fixtures.size} fixed fixtures in-process; " ++
    (if options.buildBound then
        s!"{(fixtures.filter (·.fileAuditExclusion.isNone)).size} real-CLI controls \
          (including all smoke controls; \
          {(fixtures.filter (·.fileAuditExclusion.isSome)).size} excluded from the file audits); "
      else s!"{smokeFixtureNames.size} real-CLI smoke controls; ") ++
    s!"{(fenceCorpusCases "" "").size + publicOnlyFenceCases.size} Markdown cases plus import-setup \
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

/-- Initializes Lean's search path, enables initializer execution and runs
`Regula.Checker.CheckerSelftest.run`, printing any exception as `FAIL:` and returning `1`. -/
unsafe def checkerSelftestMain (args : List String) : IO UInt32 := do
  try
    Regula.Checker.initializeLeanSearchPath
    Lean.enableInitializersExecution
    Regula.Checker.CheckerSelftest.run args
  catch error =>
    IO.eprintln s!"FAIL: {error}"
    return 1

/-- The refusal of the self-test, which the guard runs before each run and, in a process without
Lean's task manager, in the run's place (`Regula.TaskManager.guard`): it reads the arguments as
`run` does (`Selection.parse`), marks the files of that selection incomplete with `reason`
(`markIncomplete`): the transcript worker's output and the digest of a shard of the structural
partition that writes one. A packet file that is not Regula's keeps its bytes
(`Regula.Destination.write`). It returns 1. -/
def refuseCheckerSelftest (reason : String) (args : List String) : IO UInt32 := do
  if let .ok selection := Regula.Checker.SelftestArguments.Selection.parse args then
    Regula.Checker.CheckerSelftest.markIncomplete selection reason
  return 1

/-- The `checkerSelftest` executable: `checkerSelftestMain` on the command-line arguments. A
process without Lean's task manager is refused before the self-test starts, with exit code 1
(`Regula.TaskManager.guard`). -/
unsafe def main : List String → IO UInt32 :=
  Regula.TaskManager.guard "checkerSelftest" refuseCheckerSelftest checkerSelftestMain

-- The removals and the writes that the compiled code of the program reaches from its roots
-- (`Regula.Removal.rawRemovals`) are those of the filesystem observer and those that
-- `Regula.Removal.sharedPairs` lists, and those named here, each by the declaration of a source
-- that makes it: the build of this module fails otherwise, and when a name here admits no call
-- (`Regula.Removal.checkProgram`). The program elaborates Lean source, so its check states it.
run_cmd Regula.Removal.checkProgram (elaborates := true) (named := [
  -- The projects of the build-integration controls (`Regula.Checker.BuildLintQualification`).
  (`Regula.Checker.BuildLintQualification.disabledControl, ``IO.FS.writeFile),
  (`Regula.Checker.BuildLintQualification.runCase, ``IO.FS.writeFile),
  (``Regula.Checker.BuildLintQualification.addSupport, ``IO.FS.createDirAll),
  (``Regula.Checker.BuildLintQualification.addSupport, ``IO.FS.writeFile),
  -- The fixtures of the self-test's controls, among them the seeded destinations of the guard's
  -- controls, in the projects and scratch directories that they make.
  (`Regula.Checker.CheckerSelftest.adopterQualification, ``IO.FS.createDirAll),
  (`Regula.Checker.CheckerSelftest.adopterQualification, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.bvCheckCertificates, ``IO.FS.createDirAll),
  (`Regula.Checker.CheckerSelftest.bvCheckCertificates, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.combinedSnapshotQualification, ``IO.FS.createDirAll),
  (`Regula.Checker.CheckerSelftest.combinedSnapshotQualification, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.copyDocument, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.diagnosticSetupQualification, ``IO.FS.createDirAll),
  (`Regula.Checker.CheckerSelftest.diagnosticSetupQualification, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.driverCopyControl, ``IO.FS.createDirAll),
  (`Regula.Checker.CheckerSelftest.driverCopyControl, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.earlyStopControl, ``IO.FS.createDirAll),
  (`Regula.Checker.CheckerSelftest.earlyStopControl, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.executionQualification, ``IO.FS.createDirAll),
  (`Regula.Checker.CheckerSelftest.fenceEnvironmentControl, ``IO.FS.createDirAll),
  (`Regula.Checker.CheckerSelftest.fenceEnvironmentControl, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.fenceEnvironmentQualification, ``IO.FS.createDirAll),
  (`Regula.Checker.CheckerSelftest.forcedCollectorQualification, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.frozenArtifactControls, ``IO.FS.writeBinFile),
  (`Regula.Checker.CheckerSelftest.libraryCycleControl, ``IO.FS.createDirAll),
  (`Regula.Checker.CheckerSelftest.libraryCycleControl, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.manifestQualification, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.observerIdentityControl, ``IO.FS.createDirAll),
  (`Regula.Checker.CheckerSelftest.observerIdentityControl, ``IO.FS.writeBinFile),
  (`Regula.Checker.CheckerSelftest.observerIdentityControl, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.prepareSelfHosted, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.publicScannerQualification, ``IO.FS.createDirAll),
  (`Regula.Checker.CheckerSelftest.publicScannerQualification, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.retainedBuildControl, ``IO.FS.createDirAll),
  (`Regula.Checker.CheckerSelftest.retainedBuildControl, ``IO.FS.writeBinFile),
  (`Regula.Checker.CheckerSelftest.retainedBuildControl, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.sharedCopiesControl, ``IO.FS.createDirAll),
  (`Regula.Checker.CheckerSelftest.sharedCopiesControl, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.structuralPartB, ``IO.FS.createDirAll),
  (`Regula.Checker.CheckerSelftest.structuralPartB, ``IO.FS.writeBinFile),
  (`Regula.Checker.CheckerSelftest.structuralPartB, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.structuralPartC, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.taskManagerControl, ``IO.FS.createDirAll),
  (`Regula.Checker.CheckerSelftest.taskManagerControl, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.withNewFile, ``IO.FS.createDirAll),
  (`Regula.Checker.CheckerSelftest.withNewFile, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.withRemovedFile, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.withReplacedFile, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.writeCrossSurfaceProject, ``IO.FS.createDirAll),
  (`Regula.Checker.CheckerSelftest.writeCrossSurfaceProject, ``IO.FS.writeFile),
  (`Regula.Checker.CheckerSelftest.writeFreshInput, ``IO.FS.Handle.mk),
  -- The fixtures of the controls of the compiler's paths (`Regula.Checker.CompilerPaths`).
  (`Regula.Checker.CompilerPaths.phase, ``IO.FS.createDirAll),
  (`Regula.Checker.CompilerPaths.phase, ``IO.FS.writeFile),
  -- The adopter projects of the `lake lint` controls (`Regula.Checker.LintQualification`).
  (`Regula.Checker.LintQualification.WeakArgsAdopter.hidden, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.WeakArgsAdopter.requireOverride, ``IO.FS.createDirAll),
  (`Regula.Checker.LintQualification.WeakArgsAdopter.requireOverride, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.cachedWarning, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.compilerGuard, ``IO.FS.createDirAll),
  (`Regula.Checker.LintQualification.dependencyCachedWarning, ``IO.FS.createDirAll),
  (`Regula.Checker.LintQualification.dependencyCachedWarning, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.emptyFacetsWarning, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.escapedNameWarning, ``IO.FS.createDirAll),
  (`Regula.Checker.LintQualification.escapedNameWarning, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.facetReport, ``IO.FS.createDirAll),
  (`Regula.Checker.LintQualification.facetReport, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.lakeNew, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.leanArguments, ``IO.FS.createDirAll),
  (`Regula.Checker.LintQualification.leanArguments, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.leanAudit, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.leanDecisions, ``IO.FS.createDirAll),
  (`Regula.Checker.LintQualification.leanDecisions, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.leanRefusals, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.mutate, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.observerEscapes, ``IO.FS.createDirAll),
  (`Regula.Checker.LintQualification.observerEscapes, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.pathConfig, ``IO.FS.createDirAll),
  (`Regula.Checker.LintQualification.pathConfig, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.pathEscapes, ``IO.FS.createDirAll),
  (`Regula.Checker.LintQualification.pathEscapes, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.pathForged, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.pathOverrides, ``IO.FS.createDirAll),
  (`Regula.Checker.LintQualification.pathOverrides, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.pathOwnedChecks, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.pathReserved, ``IO.FS.createDirAll),
  (`Regula.Checker.LintQualification.pathReserved, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.pathSetup, ``IO.FS.createDirAll),
  (`Regula.Checker.LintQualification.pathTrusted, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.restore, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.tomlAudit, ``IO.FS.createDirAll),
  (`Regula.Checker.LintQualification.tomlAudit, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.tomlPlain, ``IO.FS.createDirAll),
  (`Regula.Checker.LintQualification.tomlPlain, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.tomlTargets, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.weakArgsDeclared, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.weakArgsModes, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.weakArgsOverrides, ``IO.FS.writeFile),
  (`Regula.Checker.LintQualification.weakArgsProbes, ``IO.FS.createDirAll),
  (`Regula.Checker.LintQualification.weakArgsProbes, ``IO.FS.writeFile),
  -- The projects of the policy controls (`Regula.Checker.PolicyQualification`).
  (`Regula.Checker.PolicyQualification.setup, ``IO.FS.createDirAll),
  (``Regula.Checker.PolicyQualification.nativeImport, ``IO.FS.writeFile),
  (``Regula.Checker.PolicyQualification.publicPaths, ``IO.FS.writeFile),
  -- The writes of the site build that `site` runs and names (`Regula.Site.Main`), in
  -- `Regula.Site.Build`, which this program links: its generated modules, the release that it
  -- downloads and unpacks, and its output.
  (`Regula.Site.Build.writeModule, ``IO.FS.createDirAll),
  (`Regula.Site.Build.writeModule, ``IO.FS.writeFile),
  (``Regula.Site.Build.downloadRelease, ``IO.FS.createDirAll),
  (``Regula.Site.Build.extractRelease, ``IO.FS.createDirAll),
  (``Regula.Site.Build.generate, ``IO.FS.createDirAll),
  (``Regula.Site.Build.generate, ``IO.FS.writeFile),
  (``Regula.Site.Build.writeTree, ``IO.FS.createDirAll),
  (``Regula.Site.Build.writeTree, ``IO.FS.writeBinFile),
  -- The writes of the campaigns that `qualify` runs and names (`Regula.Qualification.Main`), in
  -- the modules of them that this program links: their projects and slots, and the raw
  -- observations of a rule-example production beside its evidence
  -- (`Regula.Qualification.RuleExamples`). The compiled code of those modules is among the
  -- program's roots (`Regula.Removal.programRoots`).
  (``Regula.Qualification.prepareCoreProject, ``IO.FS.createDirAll),
  (``Regula.Qualification.rootImportsGuardControl, ``IO.FS.writeFile),
  (`Regula.Qualification.RuleExamples.observe, ``IO.FS.Handle.mk),
  (`Regula.Qualification.RuleExamples.produce, ``IO.FS.createDir),
  (`Regula.Qualification.RuleExamples.produce, ``IO.FS.createDirAll),
  (`Regula.Qualification.RuleExamples.produce, ``IO.FS.writeBinFile),
  (`Regula.Qualification.RuleExamples.produce, ``IO.FS.writeFile),
  (``Regula.Qualification.RuleExamples.check, ``IO.FS.createDirAll),
  (``Regula.Qualification.Slot.prepareSlot, ``IO.FS.writeFile)])

-- A program that needs Lean's task manager starts through its guard (`Regula.TaskManager.guard`),
-- and its refusal needs none: the build of this module fails otherwise
-- (`Regula.TaskManagerCheck.checkProgram`).
run_cmd Regula.TaskManagerCheck.checkProgram
