import Regula.Removal
import Regula.TaskManagerCheck
import Regula.Checker.Lint

/-! # Lint executable root

User-facing `lint` executable root, the Lake lint driver. -/

/-- The `lint` executable: `Regula.Checker.Lint.run` on the command-line arguments. A process
without Lean's task manager is refused before the run starts, with the exit code of an incomplete
run (`Regula.TaskManager.guard`). -/
unsafe def main : List String → IO UInt32 :=
  Regula.TaskManager.guard "lint" Regula.Checker.Lint.Outcome.incomplete.exitCode
    Regula.Checker.Lint.run

-- The removals that the compiled code of `main`, and of the initializers of the modules it links,
-- reaches are the filesystem observer's and those that `Regula.Removal.libraryRemovals` lists: the
-- build of this module fails otherwise (`Regula.Removal.checkProgram`).
run_cmd Regula.Removal.checkProgram

-- A program that needs Lean's task manager starts through its guard (`Regula.TaskManager.guard`):
-- the build of this module fails otherwise (`Regula.TaskManagerCheck.checkProgram`).
run_cmd Regula.TaskManagerCheck.checkProgram
