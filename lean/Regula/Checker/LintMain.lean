import Regula.Removal
import Regula.Checker.Lint

/-! # Lint executable root

User-facing `lint` executable root, the Lake lint driver. -/

/-- The `lint` executable: `Regula.Checker.Lint.run` on the command-line arguments. -/
unsafe def main (args : List String) : IO UInt32 :=
  Regula.Checker.Lint.run args

-- The removals that the compiled code of `main`, and of the initializers of the modules it links,
-- reaches are the filesystem observer's and those that `Regula.Removal.libraryRemovals` lists: the
-- build of this module fails otherwise (`Regula.Removal.checkProgram`).
run_cmd Regula.Removal.checkProgram
