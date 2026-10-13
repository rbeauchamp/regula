module
public import Lake.Build.Infos
public import Lake.Config.Workspace
public import Regula.Checker.LakeConfig
import all Lake.Load.Lean.Elab
import all Lake.Load.Lean.Eval

/-! # Replaced root facets

Report a root package's facet that a loaded declaration of Regula replaces: its `extraDep`
library facet (`weakLeanArgsTrace`) or its `presetup` module facet (`elaborationObserver`).
The decision is over supplied declaration records. Lake's compiled configuration, its runtime
evaluation and its insertion order are trusted observations, not proved by that decision.
-/

public section

namespace Regula.Checker.FacetReport

open Lean System

/-- The facet attribute that tags a declaration, in the order Lake v4.34.1 evaluates them for
one package (`Lake/Load/Lean/Eval.lean:181-192`). -/
inductive Kind where
  /-- `@[module_facet]`. -/
  | module
  /-- `@[package_facet]`. -/
  | package
  /-- `@[library_facet]`. -/
  | library
  deriving DecidableEq

/-- The report's name for a declaration of `kind`. -/
def Kind.text : Kind → String
  | .module => "module facet"
  | .package => "package facet"
  | .library => "library facet"

/-- One facet evaluated from a package's loaded configuration. -/
structure Declaration where
  /-- Lake's assigned package name. -/
  package : Name
  /-- The constant tagged with Lake's facet attribute. -/
  declaration : Name
  /-- The attribute that tags the constant. -/
  kind : Kind
  /-- This declaration's position in its package's facet inventory, in Lake's insertion order. -/
  ordinal : Nat
  /-- The evaluated facet name, which Lake uses as the insertion key of every kind. -/
  facet : Name
  /-- Whether Lake identifies this package as the root. -/
  root : Bool
  /-- Whether the source and provider guards authenticated this package's checker module. -/
  regula : Bool
  deriving DecidableEq

/-- The facet keys that Regula's `lakefile.lean` declares: `extraDep` of a library and
`presetup` of a module. -/
def regulaFacets : List Name :=
  [_root_.Lake.LeanLib.extraDepFacet, _root_.Lake.Module.presetupFacet]

/-- A non-root Regula declaration of `facet`, one of `regulaFacets`, regardless of its constant
name. Declaration names are report text, not facet insertion keys. -/
@[expose] def RegulaFacet (facet : Name) (entry : Declaration) : Prop :=
  entry.root = false ∧ entry.regula = true ∧ entry.facet = facet ∧ facet ∈ regulaFacets

instance (facet : Name) (entry : Declaration) : Decidable (RegulaFacet facet entry) := by
  unfold RegulaFacet
  infer_instance

/-- `candidate` is the root's last declaration of a key in `regulaFacets`, of any kind, and the
supplied records include a declaration of that key from a non-root Regula package. Lake keeps one
configuration for each key (`Lake/Config/FacetConfig.lean:40-42`), so under its
root-before-dependencies insertion order Regula replaces the root facet, even if a later
dependency replaces Regula's. This proposition says nothing about the final facet or the behavior
of the displaced job. -/
def Replaced (declarations : Array Declaration) (candidate : Declaration) : Prop :=
  candidate.root = true ∧
    candidate.facet ∈ regulaFacets ∧
    (∀ other ∈ declarations, other.root = true → other.facet = candidate.facet →
      other.ordinal ≤ candidate.ordinal) ∧
    ∃ replacing ∈ declarations, RegulaFacet candidate.facet replacing

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

/-- Read the module, package and library facets, in that order, from the already compiled
configuration of `package` in `ws`, with Lake's own environment importer, attribute inventory and
evaluator. The file's text is not read. An unreadable or unevaluable configuration fails the
observation.

Assumes:
- Lake v4.34.1 stores the loaded configuration at `LoadConfig.configDir` with its configuration
  file name and `.olean` extension (`Lake/Load/Lean/Elab.lean:180-187`).
- Lake v4.34.1 imports that file with `importConfigFileCore`, including imported and local
  facet entries (`Lake/Load/Lean/Elab.lean:103-159`).
- Lake v4.34.1 evaluates every `moduleFacetAttr`, then `packageFacetAttr`, then
  `libraryFacetAttr` entry of `getAllEntries` with `evalConstCheck` as `ModuleFacetDecl`,
  `PackageFacetDecl` and `LibraryFacetDecl`, and inserts them in that order
  (`Lake/Load/Lean/Eval.lean:181-192`, `Lake/Load/Workspace.lean:39`,
  `Lake/Load/Resolve.lean:49-50`).
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
  let modules ← _root_.Lake.moduleFacetAttr.getAllEntries env |>.mapM fun name => do
    let decl ← IO.ofExcept <| _root_.Lake.evalConstCheck env {} _root_.Lake.ModuleFacetDecl name
    return (name, Kind.module, decl.name)
  let packages ← _root_.Lake.packageFacetAttr.getAllEntries env |>.mapM fun name => do
    let decl ← IO.ofExcept <| _root_.Lake.evalConstCheck env {} _root_.Lake.PackageFacetDecl name
    return (name, Kind.package, decl.name)
  let libraries ← _root_.Lake.libraryFacetAttr.getAllEntries env |>.mapM fun name => do
    let decl ← IO.ofExcept <| _root_.Lake.evalConstCheck env {} _root_.Lake.LibraryFacetDecl name
    return (name, Kind.library, decl.name)
  let regula := regulaPackages.contains package.keyName
  return (modules ++ packages ++ libraries).mapIdx fun ordinal (declaration, kind, facet) =>
    { package := package.baseName, declaration, kind, ordinal, facet
      root := package.isRoot, regula }

/-- Observe every loaded package's facet declarations, retaining the package that contributes
each entry, including entries imported by its configuration.

Assumes:
- Lake v4.34.1 inserts the root's facets first (`Lake/Load/Workspace.lean:36-39`), then each
  dependency's (`Lake/Load/Resolve.lean:69-74`); insertion overwrites the same facet key, whatever
  the facet's kind (`Lake/Config/FacetConfig.lean:40-42`).
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

/-- The report's name of a key in `regulaFacets`, and the remedy for work unique to a root facet
of that key: where Lake's own facet of the key, which Regula's runs, reads that work. -/
def remedy (facet : Name) : String × String :=
  if facet = _root_.Lake.Module.presetupFacet then
    ("presetup", "Move that work to the library's plugins or dynlibs, \
      which Lake's own presetup facet reads.")
  else
    ("extraDep", "Move that work to extraDepTargets or needs, which Lake's own extraDep facet runs.")

/-- Print each replaced declaration, its consequence and remedy, as `output` requests, and with
`census` first the decision's completed census. This is an advisory about the build
configuration; it changes no audit exit class and does not restore an overridden configuration.
Lake loading must have completed first. -/
def report (ws : _root_.Lake.Workspace) (regulaPackages : Array Name) (output : Output) :
    IO Unit := do
  if output = .silent then return
  let declarations ← observe ws regulaPackages
  let collisions := replaced declarations
  if output = .census then
    IO.eprintln s!"regula facet report: checked {declarations.size} loaded facet \
      declarations; {collisions.size} root extraDep or presetup declarations replaced by Regula"
  for entry in collisions do
    let some replacing := declarations.toList.reverse.find? fun other =>
        decide (RegulaFacet entry.facet other)
      | throw <| IO.userError "facet-report: replacement selection has no supplying declaration"
    let (key, remedy) := remedy entry.facet
    IO.eprintln s!"regula facet report: root package '{entry.package}' {entry.kind.text} \
      '{entry.declaration}' ({key}) has its configuration overridden by Regula's \
      '{replacing.declaration}' \
      from package '{replacing.package}'. \
      Work unique to the overridden facet may be lost. {remedy}"

end Regula.Checker.FacetReport
