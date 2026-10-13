import Regula.DiagnosticsGate
import Regula.Removal
import Regula.Filesystem

/-! # The removal check and the presence read of the diagnostics gate

`lean --run lean/Regula/DiagnosticsGate.lean` runs the diagnostics gate before the package is
built, so it imports only Lean and does not run the check itself. This module imports it, and its
build fails when the compiled code of the program reaches a removal outside the filesystem
observer (`Regula.Removal.checkProgram`).

It also proves the program's own presence read, which the program defines because it cannot import
`Regula.Filesystem`, equal to the filesystem observer's (`isPresent_eq`). -/

run_cmd Regula.Removal.checkProgram

/-- The presence read of the program is the filesystem observer's (`Regula.Filesystem.isPresent`,
whose match form `Regula.Filesystem.isPresent_eq_match` states). -/
theorem Regula.ProgramCheck.DiagnosticsGate.isPresent_eq :
    Regula.DiagnosticsGate.isPresent = Regula.Filesystem.isPresent :=
  Regula.Filesystem.isPresent_eq_match.symm
