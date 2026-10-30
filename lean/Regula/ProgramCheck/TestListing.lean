import Regula.TestListing
import Lake.CLI.Main

/-! # The load configuration of the test listing

The validation pipeline runs the listing of the tests that Lake knows for the package,
`lean/Regula/TestListing.lean`, with `lean --run` before the package is built, so the listing
imports only Lake. The listing makes its load configuration itself
(`Regula.TestListing.loadConfig`), not with `Lake.LakeOptions.mkLoadConfig`, whose module links the
code of every command of Lake. This module proves the two configurations equal (`loadConfig_eq`). -/

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
