import Regula.Site.Deployment
import Regula.Removal

/-! # The observer reach check of the deployment check of the site

`lean --run lean/Regula/Site/Deployment.lean` runs the deployment check of the site, which imports
only the toolchain and does not run the check itself. This module imports it, and its build fails
when the compiled code of the program reaches a primitive that the check refuses
(`Regula.Removal.checkProgram`), other than the bootstrap pairs of its process source
(`Regula.Removal.bootstrap`). -/

run_cmd Regula.Removal.checkProgram (named :=
  Regula.Removal.bootstrap `Regula.Site.Deployment.Process)
