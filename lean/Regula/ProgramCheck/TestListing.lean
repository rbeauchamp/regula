import Regula.TestListing
import Regula.Removal

/-! # The removal and write check of the test listing

The validation pipeline runs the listing of the tests that Lake knows for the package,
`lean/Regula/TestListing.lean`, with `lean --run` before the package is built, so the listing
imports only Lake and does not run the check itself.
This module imports it, and its build fails when the compiled code of the program reaches a removal
or a write outside the filesystem observer and the places that `Regula.Removal.sharedPairs` lists
(`Regula.Removal.checkProgram`). The program elaborates the package's Lake configuration
(`Lake.loadPackage`), so its check states that it elaborates. -/

run_cmd Regula.Removal.checkProgram (elaborates := true)
