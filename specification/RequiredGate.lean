import LeanIntent.Implementation.Read
import LeanIntent.Required.Read
import RegulaSpecification

run_meta do
  let some path ← IO.getEnv "REGULA_BUILT_MODULES"
    | throwError "REGULA_BUILT_MODULES is not set"
  if path.isEmpty then
    throwError "REGULA_BUILT_MODULES is empty"
  let built ← match LeanIntent.Required.Read.queryModules (← IO.FS.readFile path) with
    | .ok built => pure built
    | .error e => throwError "the build's module list cannot be read: {e}"
  let implemented ← LeanIntent.Implementation.Read.check built
  let required ← LeanIntent.Required.Read.check built
  unless implemented.findings.isEmpty do
    throwError "the deliverables are not implemented: {repr implemented.findings}"
  unless implemented.awaiting.isEmpty do
    throwError "deliverables still await implementation: {repr implemented.awaiting}"
  unless required.findings.isEmpty do
    throwError "required theorems lie outside the build:\n{"\n".intercalate (required.findings.map (·.message))}"
  if implemented.implementations.isEmpty then
    throwError "no deliverables were read"
  if required.theorems.isEmpty then
    throwError "no required theorems were read"
  Lean.logInfo m!"lean-intent gate: {implemented.implementations.length} deliverables implemented, {required.theorems.length} required theorems verified across {built.size} built modules"
