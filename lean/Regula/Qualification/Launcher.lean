import Regula.Qualification.Support
import RegulaQualification.Launcher

/-! # Shared-environment compiler launcher

Reuse Lake's actual environment within one immutable parent environment/workspace.
Only explicit child search-path overrides vary. Each control still has a new compiler
process. Captured values are never printed or persisted; acquisition is trusted IO. -/
namespace Regula.Qualification.Launcher
open Lean System RegulaQualification.Launcher

/-- One validated mapping plus its actual PATH-resolved executable. -/
structure Captured where
  environment : {env : RegulaQualification.Launcher.Environment // Valid env}
  executable : String

/-- Invocation-local cache. No state survives a qualification invocation. -/
structure State where
  cache : IO.Ref (Array (Array (String × Option String) × Captured))
  records : IO.Ref (Array Observation)
  timings : IO.Ref (Array Nat)
  captureMillis : IO.Ref Nat
  legacy : Bool := false

/-- Allocate an empty launcher; it cannot reuse artifacts or verdicts. -/
def create (legacy : Bool := false) : IO State :=
  return ⟨← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef 0, legacy⟩

/-- Capture via argv, not shell syntax; validate before using any variable. -/
def environment (root : FilePath) (state : State) (overrides : Array (String × Option String)) : IO Captured := do
  let start ← IO.monoMsNow
  let result ← if let some (_, capture) := (← state.cache.get).find? (·.1 == overrides) then pure capture else do
    let output ← run root "lake" #["env", "/usr/bin/env", "-0"] overrides
    requireChecks [⟨"Lake environment capture", output.exitCode == 0⟩]
    let env ← IO.ofExcept (admit output.stdout)
    let resolved ← run root "/usr/bin/which" #["lean"] (env.val.map fun (k, v) => (k, some v))
    requireChecks [⟨"Lean executable resolution", resolved.exitCode == 0 && resolved.stderr.isEmpty &&
      (resolved.stdout.trimAscii.toString.splitOn "\n").length == 1⟩]
    let executable := (root / resolved.stdout.trimAscii.toString).toString
    let captured : Captured := ⟨env, executable⟩
    state.cache.modify (·.push (overrides, captured))
    pure captured
  let elapsed := (← IO.monoMsNow) - start
  state.captureMillis.modify (· + elapsed)
  return result

/-- Launch the same compiler argv/cwd/environment; baseline mode retains Lake startup.
Record source and full environment in memory for the separate paired diagnostic only. -/
def runLean (root : FilePath) (state : State) (args : Array String)
    (overrides : Array (String × Option String)) : IO IO.Process.Output := do
  let capture ← environment root state overrides
  let some path := args.back? | throw <| IO.userError "missing compiler source argument"
  let source ← IO.FS.readFile path
  let start ← IO.monoMsNow
  let output ← if state.legacy then run root "lake" (#["env", "lean"] ++ args) overrides
    else run root capture.executable args (capture.environment.val.map fun (k, v) => (k, some v))
  let elapsed := (← IO.monoMsNow) - start
  state.timings.modify (·.push elapsed)
  state.records.modify (·.push {
    label := (FilePath.mk path).fileStem.getD path, args, source, exitCode := output.exitCode.toNat,
    stdout := output.stdout, stderr := output.stderr,
    environment := capture.environment.val, executable := capture.executable })
  return output

/-- Preserve the original stripped LEAN_PATH query, then capture the augmented actual
Lake environment separately for imported-artifact controls. -/
def leanPath (root : FilePath) (state : State) : IO String := do
  if state.legacy then
    let output ← run root "lake" #["env", "printenv", "LEAN_PATH"]
    requireChecks [⟨"Lake path query", output.exitCode == 0⟩]
    return output.stdout.trimAscii.toString
  let captured ← environment root state #[]
  let some (_, path) := captured.environment.val.find? (·.1 == "LEAN_PATH")
    | throw <| IO.userError "missing admitted Lean path"
  return path.trimAscii.toString
end Regula.Qualification.Launcher
