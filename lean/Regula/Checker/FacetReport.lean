module
public import Lake.Config.Workspace
public import Regula.Checker.LakeConfig
import all Lake.Load.Lean.Elab
import all Lake.Load.Lean.Eval

/-! # Replaced root library facets

Report a root package's `extraDep` library facet that Regula's loaded declaration replaces.
The decision is over supplied declaration records. Lake's compiled configuration, its runtime
evaluation and its insertion order are trusted observations, not proved by that decision.
-/

public section

namespace Regula.Checker.FacetReport

open Lean System

/-- One library facet evaluated from a package's loaded configuration. -/
structure Declaration where
  /-- Lake's assigned package name. -/
  package : Name
  /-- The constant tagged with Lake's library-facet attribute. -/
  declaration : Name
  /-- This declaration's position in its package's library-facet attribute inventory. -/
  ordinal : Nat
  /-- The evaluated facet name, which Lake uses as the insertion key. -/
  facet : Name
  /-- Whether Lake identifies this package as the root. -/
  root : Bool
  /-- Whether the source and provider guards authenticated this package's checker module. -/
  regula : Bool
  deriving DecidableEq

/-- A non-root Regula declaration with the evaluated `extraDep` key, regardless of its constant
name. Declaration names are report text, not facet insertion keys. -/
@[expose] def RegulaExtraDep (entry : Declaration) : Prop :=
  entry.root = false ∧ entry.regula = true ∧ entry.facet = _root_.Lake.LeanLib.extraDepFacet

instance (entry : Declaration) : Decidable (RegulaExtraDep entry) := by
  unfold RegulaExtraDep
  infer_instance

/-- `candidate` is the last root `extraDep` declaration, and the supplied records include a
declaration of that facet from a non-root Regula package. Under Lake's root-before-dependencies
insertion order, Regula replaces the root facet, even if a later dependency replaces Regula's.
This proposition says nothing about the final facet or the behavior of the displaced job. -/
def Replaced (declarations : Array Declaration) (candidate : Declaration) : Prop :=
  candidate.root = true ∧
    candidate.facet = _root_.Lake.LeanLib.extraDepFacet ∧
    (∀ other ∈ declarations, other.root = true → other.facet = candidate.facet →
      other.ordinal ≤ candidate.ordinal) ∧
    ∃ replacing ∈ declarations, RegulaExtraDep replacing

/-- The one decision of `Replaced`, computed from the finite supplied records. -/
def replacementDecision (declarations : Array Declaration) (candidate : Declaration) :
    Decidable (Replaced declarations candidate) := by
  unfold Replaced
  infer_instance

/-- Exactly the supplied declarations decided to be replaced by Regula. -/
def replaced (declarations : Array Declaration) : Array Declaration :=
  declarations.filter fun candidate =>
    @decide (Replaced declarations candidate) (replacementDecision declarations candidate)

/-- For every array of records and candidate, the executed selection contains the candidate
exactly when `Replaced` holds. Its domain is supplied values, not a Lake execution. -/
theorem mem_replaced_iff (declarations : Array Declaration) (candidate : Declaration) :
    candidate ∈ replaced declarations ↔
      candidate ∈ declarations ∧ Replaced declarations candidate := by
  simp only [replaced, Array.mem_filter, decide_eq_true_eq]

/-- Read library facets from the already compiled configuration of `package` in `ws`, with
Lake's own environment importer, attribute inventory and evaluator. The file's text is not read.
An unreadable or unevaluable configuration fails the observation.

Assumes:
- Lake v4.34.1 stores the loaded configuration at `LoadConfig.configDir` with its configuration
  file name and `.olean` extension (`Lake/Load/Lean/Elab.lean:180-187`).
- Lake v4.34.1 imports that file with `importConfigFileCore`, including imported and local
  library-facet entries (`Lake/Load/Lean/Elab.lean:103-159`).
- Lake v4.34.1 evaluates every `libraryFacetAttr.getAllEntries` entry with `evalConstCheck` as
  `LibraryFacetDecl` (`Lake/Load/Lean/Eval.lean:181-192`).
- Lake v4.34.1 loads no facet declaration from TOML (`Lake/Load/Toml.lean:483-502` and
  `Lake/Config/LakefileConfig.lean:28`).
- Lake v4.34.1 selects the language from `relConfigFile`, not the resolved `configFile`
  (`Lake/Load/Package.lean:100`), under `LakeConfig.language`'s assumptions.
- The loaded files and package directories stay unchanged during this read: trusted filesystem
  and process boundary; this observer does not lock out other processes.
- `regulaPackages` are the authenticated checker providers, under `observe`'s assumptions. -/
def packageDeclarations (ws : _root_.Lake.Workspace) (regulaPackages : Array Name)
    (package : _root_.Lake.Package) : IO (Array Declaration) := do
  if (← IO.ofExcept (LakeConfig.language package.relConfigFile)) == .toml then return #[]
  let some file := package.configFile.fileName
    | throw <| IO.userError s!"facet-report: configuration {package.configFile} names no file"
  let config : _root_.Lake.LoadConfig :=
    { lakeEnv := ws.lakeEnv, wsDir := ws.dir, pkgIdx := package.wsIdx }
  let compiled := config.configDir / (FilePath.mk file).withExtension "olean"
  let env ← _root_.Lake.importConfigFileCore compiled {}
  let regula := regulaPackages.contains package.keyName
  _root_.Lake.libraryFacetAttr.getAllEntries env |>.mapIdxM fun ordinal name => do
    let facet ← IO.ofExcept <| _root_.Lake.evalConstCheck env {} _root_.Lake.LibraryFacetDecl name
    return {
      package := package.baseName, declaration := name, ordinal, facet := facet.name
      root := package.isRoot, regula := regula }

/-- Observe every loaded package's library-facet declarations, retaining the package that
contributes each entry, including entries imported by its configuration.

Assumes:
- Lake v4.34.1 inserts the root's facets first (`Lake/Load/Workspace.lean:36-39`), then each
  dependency's (`Lake/Load/Resolve.lean:69-74`); insertion overwrites the same facet key
  (`Lake/Config/FacetConfig.lean:43-45`).
- Each package's compiled configuration has the entries read by `packageDeclarations`, under
  that observer's assumptions.
- `regulaPackages` come from `Lake.checkReservedModules` over the actual source inventory of
  `Lake.packageModules`, after `Lake.checkOneProvider` passes over every package inventory that
  completed. Each provides `Regula.Checker.Lake` with the running checker's source text. A
  package whose inventory failed supplies no key. This is the audit's existing
  trusted source-authentication boundary, not an independent glob lookup or an assertion about
  the configured facet's job. All authenticated providers are retained; the existing provider
  guard permits duplicate providers among trusted packages. -/
def observe (ws : _root_.Lake.Workspace) (regulaPackages : Array Name) : IO (Array Declaration) := do
  return (← ws.packages.mapM (packageDeclarations ws regulaPackages)).flatten

/-- What an inventory of the workspace prints of the facet report. Only the documented entry
points request a report, each from one inventory, so a process prints it once. -/
inductive Output where
  /-- Nothing: every internal consumer of an inventory. -/
  | silent
  /-- Each replaced declaration: the project audit, which `lake lint` also runs. -/
  | replaced
  /-- The completed census too: the `--explain-config` path. -/
  | census
  deriving DecidableEq

/-- Print each replaced declaration, its consequence and remedy, as `output` requests, and with
`census` first the decision's completed census. This is an advisory about the build
configuration; it changes no audit exit class and does not restore an overridden configuration.
Lake loading must have completed first. -/
def report (ws : _root_.Lake.Workspace) (regulaPackages : Array Name) (output : Output) :
    IO Unit := do
  if output = .silent then return
  let declarations ← observe ws regulaPackages
  let collisions := replaced declarations
  let replacing := declarations.toList.reverse.find? fun entry => decide (RegulaExtraDep entry)
  if output = .census then
    IO.eprintln s!"regula facet report: checked {declarations.size} loaded library facet \
      declarations; {collisions.size} root extraDep declarations replaced by Regula"
  for entry in collisions do
    let some replacing := replacing
      | throw <| IO.userError "facet-report: replacement selection has no supplying declaration"
    IO.eprintln s!"regula facet report: root package '{entry.package}' library facet \
      '{entry.declaration}' (extraDep) has its configuration overridden by Regula's \
      '{replacing.declaration}' \
      from package '{replacing.package}'. \
      Work unique to the overridden facet may be lost. Move that work to extraDepTargets or needs, \
      which Lake's own extraDep facet runs."

end Regula.Checker.FacetReport
