import Regula.Removal
import Regula.Checker.AxiomGate

/-! # Axiom gate executable root

User-facing `axiomGate` executable root. Its only behavior is
`AxiomGate.entry`; it never installs injected Git facts. -/

/-- Runs `Regula.Checker.AxiomGate.entry` on the command-line arguments and returns its exit
code. -/
unsafe def main (args : List String) : IO UInt32 :=
  Regula.Checker.AxiomGate.entry args

-- The removals that the compiled code of `main`, and of the initializers of the modules it links,
-- reaches are the filesystem observer's and those that `Regula.Removal.libraryRemovals` lists: the
-- build of this module fails otherwise (`Regula.Removal.checkProgram`).
run_cmd Regula.Removal.checkProgram
