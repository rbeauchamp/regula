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

/-- The declaration of the `extraDep` library facet shipped in Regula's configuration. -/
def regulaFacetName : Name := `weakLeanArgsTrace

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
  /-- Whether this package has the key of Regula's provider in the loaded workspace. -/
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
- `regulaPackage` identifies Regula's provider in this workspace, under `observe`'s assumptions. -/
def packageDeclarations (ws : _root_.Lake.Workspace) (regulaPackage : Option Name)
    (package : _root_.Lake.Package) : IO (Array Declaration) := do
  if (← IO.ofExcept (LakeConfig.language package.relConfigFile)) == .toml then return #[]
  let some file := package.configFile.fileName
    | throw <| IO.userError s!"facet-report: configuration {package.configFile} names no file"
  let config : _root_.Lake.LoadConfig :=
    { lakeEnv := ws.lakeEnv, wsDir := ws.dir, pkgIdx := package.wsIdx }
  let compiled := config.configDir / (FilePath.mk file).withExtension "olean"
  let env ← _root_.Lake.importConfigFileCore compiled {}
  let regula := regulaPackage == some package.keyName
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
- Lake v4.34.1's `Workspace.findModule?` gives the package key of the provider of
  `Regula.Checker.Lake` (`Lake/Config/Workspace.lean:279-280`, `Lake/Config/Module.lean:41-59`).
  This module identifies Regula under the audit's module-provider and reserved-source guards.
  The configuration query alone does not authenticate that provider's source. -/
def observe (ws : _root_.Lake.Workspace) : IO (Array Declaration) := do
  let regulaPackage := (ws.findModule? `Regula.Checker.Lake).map (·.pkg.keyName)
  return (← ws.packages.mapM (packageDeclarations ws regulaPackage)).flatten

/-- Print the decision's completed census and each replaced declaration, its consequence and
remedy. This is an advisory about the build configuration; it changes no audit exit class and
does not restore a displaced build step. Lake loading must have completed first. -/
def report (ws : _root_.Lake.Workspace) : IO Unit := do
  let declarations ← observe ws
  let collisions := replaced declarations
  let replacing := declarations.toList.reverse.find? fun entry => decide (RegulaExtraDep entry)
  IO.eprintln s!"regula facet report: checked {declarations.size} loaded library facet \
    declarations; {collisions.size} root extraDep declarations replaced by Regula"
  for entry in collisions do
    let some replacing := replacing
      | throw <| IO.userError "facet-report: replacement selection has no supplying declaration"
    IO.eprintln s!"regula facet report: root package '{entry.package}' library facet \
      '{entry.declaration}' (extraDep) is replaced by Regula's '{replacing.declaration}' \
      from package '{replacing.package}'. \
      Its build step does not run. Move that work to extraDepTargets or needs, \
      which Lake's own extraDep facet runs."

end Regula.Checker.FacetReport
