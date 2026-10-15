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
  /-- The variables `lake env /usr/bin/env -0` printed, admitted by `admit` as `Valid`. -/
  environment : {env : RegulaQualification.Launcher.Environment // Valid env}
  /-- The `lean` path that `which` resolved under that environment, joined to the root
  (`resolvedLean`). -/
  executable : String

/-- Invocation-local cache. No state survives a qualification invocation. -/
structure State where
  /-- Captured environments, keyed by the exact overrides they were captured with. -/
  cache : IO.Ref (Array (Array (String × Option String) × Captured))
  /-- One record per compiler launch: argv, source, exit code, output and environment. -/
  records : IO.Ref (Array Observation)
  /-- Wall-clock milliseconds of each compiler launch, in launch order. -/
  timings : IO.Ref (Array Nat)
  /-- Total milliseconds spent obtaining environments, cache hits included. -/
  captureMillis : IO.Ref Nat
  /-- Baseline mode: launch every compile through `lake env lean` instead of the captured
  environment and executable. -/
  legacy : Bool := false

/-- Allocate an empty launcher; it cannot reuse artifacts or verdicts. -/
def create (legacy : Bool := false) : IO State :=
  return ⟨← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef 0, legacy⟩

/-- The `lean` executable that `/usr/bin/which` finds in `root` under the variables `env`, joined to
`root`. The path it prints is read exactly (`Regula.Filesystem.Construction.printedLine?`: only the
final newline is removed), and a failure, any standard error, or output that is not one line is
thrown.

Assumes: `/usr/bin/which lean` prints the path it finds, the entry of `PATH` (`.` for an empty one)
followed by `/lean`, then a newline, and nothing else (macOS `shell_cmds-329`
`which/which.c:105-121`, `:123-146`; Debian `debianutils` 5.17 `which.debianutils:11-14`, `:49-57`).
When the entry is relative, so is that path, from the directory that `which` runs in, `root`.
`FilePath.join` keeps an absolute path as it is. -/
def resolvedLean (root : FilePath) (env : Array (String × String)) : IO String := do
  let resolved ← run root "/usr/bin/which" #["lean"] (env.map fun (k, v) => (k, some v))
  unless resolved.exitCode == 0 && resolved.stderr.isEmpty do
    throw <| IO.userError s!"Lean executable resolution failed (exit {resolved.exitCode}): \
      {resolved.stderr}"
  let some line := Regula.Filesystem.Construction.printedLine? resolved.stdout
    | throw <| IO.userError s!"Lean executable resolution printed {resolved.stdout.quote}, not \
        one path"
  return (root / line).toString

/-- Capture via argv, not shell syntax; validate before using any variable. -/
def environment (root : FilePath) (state : State) (overrides : Array (String × Option String)) :
    IO Captured := do
  let start ← IO.monoMsNow
  let result ← if let some (_, capture) := (← state.cache.get).find? (·.1 == overrides) then
      pure capture else do
    let output ← run root "lake" #["env", "/usr/bin/env", "-0"] overrides
    requireChecks [⟨"Lake environment capture", output.exitCode == 0⟩]
    let env ← IO.ofExcept (admit output.stdout)
    let executable ← resolvedLean root env.val
    let captured : Captured := ⟨env, executable⟩
    state.cache.modify (·.push (overrides, captured))
    pure captured
  let elapsed := (← IO.monoMsNow) - start
  state.captureMillis.modify (· + elapsed)
  return result

/-- Launch the same compiler argv/cwd/environment; baseline mode retains Lake startup.
Record source and full environment in memory for the separate paired diagnostic only.
With `first`, the launch puts `first` ahead of the captured `LEAN_PATH` and runs the captured
executable in either mode: `lake env` puts the workspace's own entries before an inherited
`LEAN_PATH`, so no launch through it can put a directory first. The record holds the environment
the launch used. -/
def runLean (root : FilePath) (state : State) (args : Array String)
    (overrides : Array (String × Option String)) (first : Option FilePath := none) :
    IO IO.Process.Output := do
  let capture ← environment root state overrides
  let some path := args.back? | throw <| IO.userError "missing compiler source argument"
  let source ← IO.FS.readFile path
  let variables ← match first with
    | none => pure capture.environment.val
    | some first =>
      unless capture.environment.val.any (·.1 == "LEAN_PATH") do
        throw <| IO.userError "missing admitted Lean path"
      pure <| capture.environment.val.map fun (key, value) =>
        (key, if key == "LEAN_PATH" then SearchPath.toString (first :: SearchPath.parse value)
          else value)
  let start ← IO.monoMsNow
  let output ←
    if state.legacy && first.isNone then run root "lake" (#["env", "lean"] ++ args) overrides
    else run root capture.executable args (variables.map fun (k, v) => (k, some v))
  let elapsed := (← IO.monoMsNow) - start
  state.timings.modify (·.push elapsed)
  state.records.modify (·.push {
    label := (FilePath.mk path).fileStem.getD path, args, source, exitCode := output.exitCode.toNat,
    stdout := output.stdout, stderr := output.stderr,
    environment := variables, executable := capture.executable })
  return output

/-- The `LEAN_PATH` that `lake env` gives in `root` with `overrides`, as `printenv` prints it, read
exactly (`Regula.Filesystem.Construction.printedLine?`: only the final newline is removed). A
failure, or output that is not one line, is thrown.

Assumes: `printenv LEAN_PATH` prints the variable's value followed by a newline and exits with 0:
GNU coreutils 9.4 for each entry of the environment with that name (`src/printenv.c:119-153`), so
that two entries print two lines, which are thrown, and macOS `shell_cmds-329` for the first
(`printenv/printenv.c:93-102`). -/
def printedLeanPath (root : FilePath) (overrides : Array (String × Option String) := #[]) :
    IO String := do
  let output ← run root "lake" #["env", "printenv", "LEAN_PATH"] overrides
  unless output.exitCode == 0 do
    throw <| IO.userError s!"Lake path query failed (exit {output.exitCode}): {output.stderr}"
  let some path := Regula.Filesystem.Construction.printedLine? output.stdout
    | throw <| IO.userError s!"Lake path query printed {output.stdout.quote}, not one search path"
  return path

/-- The `LEAN_PATH` of Lake's environment in `root`, for imported-artifact controls: in baseline
mode the one that `lake env` gives (`printedLeanPath`), and otherwise the captured environment's
value, as it is. -/
def leanPath (root : FilePath) (state : State) : IO String := do
  if state.legacy then return ← printedLeanPath root
  let captured ← environment root state #[]
  let some (_, path) := captured.environment.val.find? (·.1 == "LEAN_PATH")
    | throw <| IO.userError "missing admitted Lean path"
  return path
end Regula.Qualification.Launcher
