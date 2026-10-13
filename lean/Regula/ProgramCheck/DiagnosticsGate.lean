import Regula.DiagnosticsGate
import Regula.Removal

/-! # The observer reach check of the diagnostics gate

`lean --run lean/Regula/DiagnosticsGate.lean` runs the diagnostics gate before the package is
built, so it imports only the toolchain and does not run the check itself. This module imports it,
and its build fails when the compiled code of the program reaches a primitive that the check
refuses (`Regula.Removal.checkProgram`), other than the bootstrap pairs of its process source
(`Regula.Removal.bootstrap`). -/

run_cmd Regula.Removal.checkProgram (named :=
  Regula.Removal.bootstrap `Regula.DiagnosticsGate.Process)
