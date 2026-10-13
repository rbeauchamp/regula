import Regula.RegistryChecks
import Regula.Removal

/-! # The removal and write check of the registry checks

The first acceptance step runs `lean/Regula/RegistryChecks.lean` with `lake env lean --run`, which
elaborates the module at each run, so the check runs here, once when this module is built. Its
build fails when the compiled code of the program reaches a removal or a write outside the
filesystem observer and the places that `Regula.Removal.sharedPairs` lists
(`Regula.Removal.checkProgram`). The program's modules link Regula's frontend
(`Regula.Checker.Frontend`) and Lake's loader of a configuration
(`Regula.Checker.Workspace.withRootWorkspace`), whose compiled code reaches Lean's elaborator, so
its check states that it elaborates: the class is conservative reachability from every compiled
declaration of its modules (`Regula.Removal.programRoots`). -/

run_cmd Regula.Removal.checkProgram (elaborates := true)
