import Regula.Checker.AxiomGate

/-! # Axiom gate executable root

User-facing `axiomGate` executable root. Its only behavior is
`AxiomGate.entry`; it never installs injected Git facts. -/

unsafe def main (args : List String) : IO UInt32 :=
  Regula.Checker.AxiomGate.entry args
