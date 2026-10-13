import Regula.Removal
import Regula.TaskManagerCheck
import Regula.Checker.AxiomGate

/-! # Axiom gate executable root

User-facing `axiomGate` executable root. Its only behavior is
`AxiomGate.entry`; it never installs injected Git facts. -/

/-- Runs `Regula.Checker.AxiomGate.entry` on the command-line arguments and returns its exit
code. A process without Lean's task manager is refused before the audit starts: each destination
that the arguments name is marked incomplete with the reason, and the exit code is that of an
incomplete audit (`Regula.TaskManager.guard`, `AxiomGate.refuseWithoutTaskManager`). -/
unsafe def main : List String → IO UInt32 :=
  Regula.TaskManager.guard "axiomGate" Regula.Checker.AxiomGate.refuseWithoutTaskManager
    Regula.Checker.AxiomGate.entry

-- The removals and the writes that the compiled code of `main`, and of the initializers of the
-- modules it links, reaches are those of the filesystem observer and those that
-- `Regula.Removal.sharedPairs` lists: the build of this module fails otherwise
-- (`Regula.Removal.checkProgram`). The program elaborates Lean source, so its check states it.
run_cmd Regula.Removal.checkProgram (elaborates := true)

-- A program that needs Lean's task manager starts through its guard (`Regula.TaskManager.guard`),
-- and its refusal needs none: the build of this module fails otherwise
-- (`Regula.TaskManagerCheck.checkProgram`).
run_cmd Regula.TaskManagerCheck.checkProgram
