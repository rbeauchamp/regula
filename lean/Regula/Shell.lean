import Regula.Load
import Regula.Rules
import RegulaCore.Allowlist
import RegulaCore.Edition

/-!
# The shell of the checker

The checker of a finished build, which the `lint` executable runs (`Regula.LintMain`), Lake's lint
driver for a project that sets `lintDriver := "regula/lint"`. It has three effects: it loads the
finished build (`Regula.Load.loadBundle`), it prints its report, and it sets its exit code. It
writes no file and removes no file (`Regula.Effects.check`). Lake's own load of the workspace runs
Git in the environment of the caller. It builds nothing: the project's gate
builds the claimed targets with `lake build --wfail` before it runs the checker, and a module
without its `.olean` makes the run `incomplete`.

The verdict is that of `Regula.Closed.run` (the specification's `gateRecord`): `pass` (exit 0)
when the input has the closed form and no rule reports a subject, `fail` (exit 1) when a rule
reports one, and `incomplete` (exit 2) when the build cannot be loaded or the input does not have
the closed form (RG2001).

The allowlists of RG2006 and RG2007 are the closed lists of `Regula.Allowlist` (`allowlists`).
-/

namespace Regula.Shell

open Lean Regula.Closed

/-- The allowlists the checker runs with: the closed lists of `Regula.Allowlist`. -/
def allowlists : Allowlists :=
  { options := Regula.Allowlist.admitsOption, extensions := Regula.Allowlist.admitsExtension }

/-- The address of a rule's page in the edition of the installed Regula (`Regula.helpUrl`): a
release's own page (`helpUrl_release`), and the development page exactly for an unreleased build
(`helpUrl_dev_iff`). -/
def page (rule : RuleId) : String := Regula.helpUrl rule

/-- The line of one finding, of the form `Regula.Closed.findingForm`. -/
def line (f : Finding) : String :=
  let place := match f.module with
    | some m => if m == f.subject then "" else s!" (module {m})"
    | none => ""
  s!"{f.rule.spelling} {f.subject}{place}: {f.detail} {page f.rule}"

/-- Print the findings and the verdict, and give the verdict's exit code (`Verdict.exitCode`). -/
def report (verdict : Verdict) (findings : List Finding) (why : Option String) : IO UInt32 := do
  for f in findings do
    IO.println (line f)
  match verdict, why with
  | .pass, _ => IO.println s!"regula: {verdict.label}"
  | .fail, _ => IO.println s!"regula: {verdict.label}, {findings.length} findings"
  | .incomplete, why =>
    IO.println s!"regula: {verdict.label} ({(page .environment)}): {why.getD "no reason"}"
  return verdict.exitCode

/-- What a run read: its environments, the modules of the root package, and the constants of
claimed modules in each environment. -/
def coverage (b : Bundle) : String :=
  let modules := (b.envs.head?.map (·.modules.length)).getD 0
  let claimed := b.envs.map fun i =>
    let table := i.claimTable
    (i.decls.filter fun d => !((table.find? d.module).getD []).isEmpty).length
  s!"regula: read {b.envs.length} environments, {modules} modules of the root package, and \
    {claimed} constants of claimed modules in each environment"

/-- Run the checker on the explicitly named workspace, or on the current directory only when
it is the workspace Lake dispatched. A different implicit workspace is incomplete. -/
unsafe def run (args : List String) : IO UInt32 := do
  let selection ← match args with
    | [] => pure Regula.Load.WorkspaceSelection.dispatched
    | [dir] => pure (Regula.Load.WorkspaceSelection.named dir)
    | _ => do
      IO.eprintln "usage: lint [WORKSPACE]"
      return 2
  match ← (Regula.Load.loadBundle selection).toBaseIO with
  | .error e => report .incomplete [] (some (toString e))
  | .ok bundle =>
    let (verdict, findings, why) := Regula.Closed.run allowlists bundle
    IO.println (coverage bundle)
    report verdict findings why

/-- Why this process has no Lean task manager, or `none` when it has one. It runs one task of
priority `Task.Priority.dedicated` and compares the thread the task ran on with the thread of the
caller: the same thread means that Lean has no task manager, as under `LEAN_NUM_THREADS=0`.

Assumes: Lean 4.35.0 gives `Task.Priority.dedicated` the value 9 (`src/Init/Core.lean:677`), above
`LEAN_MAX_PRIO`, and the task manager runs a task of such a priority on a new thread
(`src/runtime/object.cpp:792-795`, `:868-877`). Without a task manager, Lean runs the task on the
caller's thread before it returns (`lean_task_spawn_core`, `src/runtime/object.cpp:1184-1190`). Two
threads that run at once have different identifiers (`lean_io_get_tid`,
`src/runtime/process.cpp:340-352`). -/
def taskManagerMissing : IO (Option String) := do
  let caller ← IO.getTID
  let thread ← IO.ofExcept (← IO.wait (← IO.asTask (prio := .dedicated) IO.getTID))
  return if thread == caller then
    some "Lean's task manager is not running in this process (Lean starts none when \
      LEAN_NUM_THREADS is 0)"
  else none

/-- `run`, or the verdict `incomplete` in a process without Lean's task manager: there, Lake's load
of a workspace can end the process with a panic, whose exit code 1 is that of the verdict `fail`,
which no completed run established (issue 393). -/
unsafe def start (args : List String) : IO UInt32 := do
  if let some reason ← taskManagerMissing then
    report .incomplete [] (some reason)
  else run args

end Regula.Shell
