import Regula.Qualification.Support

/-! # Group termination qualification

Focused operational qualification of group termination, not a timing theorem.
A timed child launches a long-lived descendant with inherited output handles. The outer
observer must receive refusal, observe the descendant stopped, and run a clean control.
Run separately from ordinary acceptance: this intentionally kills its owned test group. -/
open Regula.Qualification System

private def selfArgs (args : Array String) : Array String :=
  #["env", "lean", "--run", "lean/Regula/Qualification/TimeoutControl.lean"] ++ args

private def observe (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd := "lake", args := selfArgs args }

/-- Test-only child modes and the positive/timeout/restored campaign. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["descendant", pidPath] =>
    IO.FS.writeFile ⟨pidPath⟩ (toString (← IO.Process.getPID))
    IO.println "descendant-ready"
    (← IO.getStdout).flush
    IO.sleep 60000
    return 0
  | ["parent", pidPath] =>
    let child ← IO.Process.spawn {
      cmd := "lake", args := selfArgs #["descendant", pidPath],
      stdout := .inherit, stderr := .inherit }
    child.wait
  | ["bounded", pidPath] =>
    runBounded (← IO.currentDir) 5 "lake" (selfArgs #["parent", pidPath])
  | ["positive"] => IO.println "restored-control"; return 0
  | [] =>
    let root ← rootDirectory
    withScratch root "timeout-control" fun scratch => do
      let positive ← observe #["positive"]
      requireChecks
          [⟨"positive process control", positive.exitCode == 0 &&
              positive.stdout.contains "restored-control"⟩]
      let pidPath := scratch / "descendant.pid"
      let start ← IO.monoMsNow
      let negative ← observe #["bounded", pidPath.toString]
      let elapsed := (← IO.monoMsNow) - start
      requireChecks
          [⟨"timed descendant really started", negative.stdout.contains "descendant-ready"⟩,
        ⟨"group timeout refused", negative.exitCode == 137⟩,
        ⟨"pipes drained within observation allowance", elapsed < 15000⟩]
      let pid ← IO.FS.readFile pidPath
      let status ← IO.Process.output { cmd := "ps", args := #["-o", "stat=", "-p", pid] }
      let state := status.stdout.trimAscii.toString
      requireChecks
          [⟨"descendant terminated (absent or unreaped zombie)", state.isEmpty ||
              state.startsWith "Z"⟩]
      let restored ← observe #["positive"]
      requireChecks
          [⟨"restored process control", restored.exitCode == 0 &&
              restored.stdout.contains "restored-control"⟩]
      IO.println s!"group timeout: positive / live descendant with inherited pipes / refusal \
        ({elapsed}ms) / terminated / restored PASS"
      return 0
  | _ => throw <| IO.userError "timeout control takes no public arguments"
