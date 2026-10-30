import Regula.Shell
import Regula.Removal
import Regula.TaskManagerCheck

/-! # The `lint` executable

The root of the `lint` executable, Lake's lint driver for a project that sets
`lintDriver := "regula/lint"`: `Regula.Shell.run` on the command-line arguments, started through
the guard of Lean's task manager and of Git's environment (`Regula.TaskManager.guard`). Lake's load
of the workspace runs Git, and the guard runs the checker in an environment that isolates Git from
the caller's Git variables (`Regula.GitIsolation`). -/

/-- The refusal of a run without Lean's task manager, or whose Git environment cannot be isolated:
the guard has printed the reason, and the exit code is that of the verdict `incomplete`. -/
def refuseLint (_reason : String) (_args : List String) : IO UInt32 :=
  pure Regula.Closed.Verdict.incomplete.exitCode

/-- The `lint` executable. -/
unsafe def main : List String → IO UInt32 :=
  Regula.TaskManager.guard "lint" refuseLint Regula.Shell.run

-- The removals and the writes that the compiled code of the program reaches from its roots
-- (`Regula.Removal.rawRemovals`) are those of the filesystem observer and those that
-- `Regula.Removal.sharedPairs` lists: the build of this module fails otherwise
-- (`Regula.Removal.checkProgram`). The program elaborates Lake's configuration of the workspace
-- that it loads, so its check states it.
run_cmd Regula.Removal.checkProgram (elaborates := true)

-- A program that needs Lean's task manager starts through its guard (`Regula.TaskManager.guard`),
-- and its refusal needs none: the build of this module fails otherwise
-- (`Regula.TaskManagerCheck.checkProgram`).
run_cmd Regula.TaskManagerCheck.checkProgram
