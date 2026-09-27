import Regula.Checker.AxiomGate

/-! # Axiom gate executable root

User-facing `axiomGate` executable root. Its only behavior is
`AxiomGate.entry`; it never installs injected Git facts. -/

/-- Runs `Regula.Checker.AxiomGate.entry` on the command-line arguments and returns its exit
code. -/
unsafe def main (args : List String) : IO UInt32 :=
  Regula.Checker.AxiomGate.entry args
