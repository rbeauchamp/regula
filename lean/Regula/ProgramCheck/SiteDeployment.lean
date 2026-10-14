import Regula.Site.Deployment
import Regula.Removal

/-! # The removal and write check of the deployment check of the site

`lean --run lean/Regula/Site/Deployment.lean` runs the deployment check of the site, which imports
only Lean and does not run the check itself. This module imports it, and its build fails when the
compiled code of the program reaches a removal or a write outside the filesystem
observer and the places that `Regula.Removal.sharedPairs` lists
(`Regula.Removal.checkProgram`). -/

run_cmd Regula.Removal.checkProgram
