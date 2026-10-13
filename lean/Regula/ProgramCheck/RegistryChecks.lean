import Regula.RegistryChecks
import Regula.Removal

/-! # The observer reach check of the registry checks

The first acceptance step runs `lean/Regula/RegistryChecks.lean` under `lake env` with the
toolchain's `lean --run`, which elaborates the module at each run, so the check runs here, once
when this module is built. Its build fails when the compiled code of the program reaches a
primitive that the check refuses (`Regula.Removal.checkProgram`). -/

run_cmd Regula.Removal.checkProgram
