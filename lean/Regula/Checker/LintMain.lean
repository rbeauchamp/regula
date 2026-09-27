import Regula.Checker.Lint

/-! # Lint executable root

User-facing `lint` executable root, the Lake lint driver. -/

/-- The `lint` executable: `Regula.Checker.Lint.run` on the command-line arguments. -/
unsafe def main (args : List String) : IO UInt32 :=
  Regula.Checker.Lint.run args
