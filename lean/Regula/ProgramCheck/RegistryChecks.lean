import Regula.RegistryChecks
import Regula.Removal

/-! # The removal and write check of the registry checks

The first acceptance step runs `lean/Regula/RegistryChecks.lean` with `lake env lean --run`, which
elaborates the module at each run, so the check runs here, once when this module is built. Its
build fails when the compiled code of the program reaches a removal or a write outside the
filesystem observer and the places that `Regula.Removal.sharedPairs` lists
(`Regula.Removal.checkProgram`). -/

run_cmd Regula.Removal.checkProgram
