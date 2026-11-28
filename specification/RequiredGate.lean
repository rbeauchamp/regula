import Lean
import LeanIntent.Implementation.Read
import LeanIntent.Required.Read

unsafe def main (args : List String) : IO UInt32 := do
  unless args.isEmpty do
    throw <| IO.userError "usage: lake env lean -DwarningAsError=true --run RequiredGate.lean"
  let some path ← IO.getEnv "REGULA_BUILT_MODULES"
    | throw <| IO.userError "REGULA_BUILT_MODULES is not set"
  if path.isEmpty then
    throw <| IO.userError "REGULA_BUILT_MODULES is empty"
  let built ← match LeanIntent.Required.Read.queryModules (← IO.FS.readFile path) with
    | .ok built => pure built
    | .error e => throw <| IO.userError s!"the build's module list cannot be read: {e}"
  Lean.enableInitializersExecution
  let env ← Lean.importModules
    #[{ module := `RegulaSpecification, importAll := true }] {} (loadExts := true) (level := .private)
  let ctx : Lean.Core.Context := { fileName := "RequiredGate.lean", fileMap := default }
  let (implCount, reqCount, casesCount, unprovedCount) ← (Lean.Meta.MetaM.run' (do
    let implemented ← LeanIntent.Implementation.Read.check built
    let required ← LeanIntent.Required.Read.check built
    unless implemented.findings.isEmpty do
      throwError "the deliverables are not implemented: {repr implemented.findings}"
    unless implemented.awaiting.isEmpty do
      throwError "deliverables still await implementation: {repr implemented.awaiting}"
    unless required.findings.isEmpty do
      throwError "required-theorems check failed:\n{"\n".intercalate (required.findings.map (·.message))}"
    unless required.deferredO2Run.isEmpty do
      throwError "deliverables still defer O2Run: {repr required.deferredO2Run}"
    if implemented.implementations.isEmpty then
      throwError "no deliverables were read"
    if required.theorems.isEmpty then
      throwError "no required theorems were read"
    pure (implemented.implementations.length, required.theorems.length,
      required.casesComparisons.length, required.unprovedComparisons.length)
  )).toIO' ctx { env }
  IO.println s!"lean-intent gate: {implCount} deliverables implemented, {reqCount} required theorems verified across {built.size} built modules ({casesCount} cases comparisons, {unprovedCount} unproved directions)"
  return 0
