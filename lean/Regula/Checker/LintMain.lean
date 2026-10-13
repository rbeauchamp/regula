import Regula.Removal
import Regula.TaskManagerCheck
import Regula.Checker.Lint

/-! # Lint executable root

User-facing `lint` executable root, the Lake lint driver. -/

/-- The `lint` executable: `Regula.Checker.Lint.run` on the command-line arguments. A process
without Lean's task manager is refused before the run starts: each result destination that the
arguments name is marked incomplete with the reason, and the exit code is that of an incomplete run
(`Regula.TaskManager.guard`, `Lint.refuseWithoutTaskManager`). -/
unsafe def main : List String → IO UInt32 :=
  Regula.TaskManager.guard "lint" Regula.Checker.Lint.refuseWithoutTaskManager
    Regula.Checker.Lint.run

-- The removals and the writes that the compiled code of `main`, and of the initializers of the
-- modules it links, reaches are those of the filesystem observer and those that
-- `Regula.Removal.sharedPairs` lists: the build of this module fails otherwise
-- (`Regula.Removal.checkProgram`). The program elaborates Lean source, so its check states it.
run_cmd Regula.Removal.checkProgram (elaborates := true)

-- A program that needs Lean's task manager starts through its guard (`Regula.TaskManager.guard`),
-- and its refusal needs none: the build of this module fails otherwise
-- (`Regula.TaskManagerCheck.checkProgram`).
run_cmd Regula.TaskManagerCheck.checkProgram
