import Regula.DiagnosticsGate
import Regula.Removal

/-! # The removal check of the diagnostics gate

`lean --run lean/Regula/DiagnosticsGate.lean` runs the diagnostics gate before the package is
built, so it imports only Lean and does not run the check itself. This module imports it, and its
build fails when the compiled code of the program reaches a removal outside the filesystem
observer (`Regula.Removal.checkProgram`). -/

run_cmd Regula.Removal.checkProgram (named :=
  Regula.Removal.bootstrap `Regula.DiagnosticsGate.Process)
