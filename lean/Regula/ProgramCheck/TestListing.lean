import Regula.TestListing
import Regula.Removal
import Lake.CLI.Main

/-! # The removal and write check and the load configuration of the test listing

The validation pipeline runs the listing of the tests that Lake knows for the package,
`lean/Regula/TestListing.lean`, with `lean --run` before the package is built, so the listing
imports only Lake and does not run the check itself.
This module imports it, and its build fails when the compiled code of the program reaches a removal
or a write outside the filesystem observer and the places that `Regula.Removal.sharedPairs` lists
(`Regula.Removal.checkProgram`). The program elaborates the package's Lake configuration
(`Lake.loadPackage`), so its check states that it elaborates.

The listing makes its load configuration itself (`Regula.TestListing.loadConfig`), not with
`Lake.LakeOptions.mkLoadConfig`, whose module links the code of every command of Lake
(`Regula.TestListing`, "How it reads the package"). This module proves the two configurations
equal (`loadConfig_eq`). It imports `Lake.CLI.Main` for that, and the program does not link it:
the check follows the modules that the program's root module imports (`Regula.Removal.linked`),
and no module imports this one. -/

run_cmd Regula.Removal.checkProgram (elaborates := true)

/-- The load configuration of the listing is the one that Lake's commands make from the options
that hold only the installations that the listing found, with the same failures in the same order:
`Lake.LakeOptions.mkLoadConfig`, which `lake check-test` runs (`Lake/CLI/Main.lean:131-145`,
`:1094-1097`). The options of `lake check-test` also hold its arguments, which only the load of a
workspace reads (`Regula.TestListing`, "How it reads the package"). -/
theorem Regula.ProgramCheck.TestListing.loadConfig_eq (elanInstall? : Option Lake.ElanInstall)
    (leanInstall? : Option Lake.LeanInstall) (lakeInstall? : Option Lake.LakeInstall) :
    Regula.TestListing.loadConfig elanInstall? leanInstall? lakeInstall? =
      Lake.LakeOptions.mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? } := by
  cases leanInstall? <;> cases lakeInstall? <;> rfl
