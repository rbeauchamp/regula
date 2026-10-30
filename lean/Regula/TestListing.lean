import Lake.CLI.Error
import Lake.Load.Package
import Lake.Util.IO

/-! # The listing of the tests that Lake knows for Regula's package

The validation pipeline's settings in `.no-mistakes.yaml` run this program from the repository
root as the listing of Regula's tests, on macOS:

```text
lake env lean --load-dynlib=libLake_shared.dylib --run lean/Regula/TestListing.lean
```

It prints the test driver that Lake reports for the package there on one line, and prints nothing
when Lake reports none. It exits with status 1 when Lake cannot load the package, after Lake's
messages on standard error, and when the driver is not a text that it can print as one line
(`listing`). So an empty listing with status 0 means that Lake loaded the package and reported no
test driver.

The program needs Lake's own compiled library, which `--load-dynlib` loads before the program
runs. `lake env` puts the toolchain's library directory first on the search path of shared
libraries (`Lake.Workspace.augmentedEnvVars`, `Lake/Config/Workspace.lean:409-431`,
`Lake/CLI/Main.lean:1260-1269`). Without that library, `lean --run` stopped in the load of every
`lakefile.lean` tried, at code that Lean's interpreter could not run, and exited with status 1
(observed with Lean v4.34.1, and with Lean v4.35.0 on this repository's `lakefile.lean`). A
`lakefile.toml` loaded without it. The file name of the library is
macOS's. On another system the command fails, so its listing blocks rather than passes.

## What Lake knows as a test

Lake v4.35.0 knows one test of a package: its test driver, `Lake.Package.testDriver`, which
`lake test` runs when the package is the root of the workspace (`Lake/CLI/Actions.lean:71-85`).
The driver is the package's `testDriver` setting, or the one script, executable or library tagged
`@[test_driver]`. A package with both, or with two tagged, does not load
(`Lake/Load/Lean/Eval.lean:145-161`). `lake check-test` reports the driver only by its exit
status. That status is 1 for an empty driver and also for a package that does not load
(`Lake/CLI/Main.lean:178-181`, `:1094-1097`, `Lake/Util/MainM.lean:72-75`, `:80-82`), so this
program reads the driver itself.

## How it reads the package

It makes the calls that `lake check-test` makes when no option is given
(`Lake/CLI/Main.lean:172-181`, `:1094-1097`):
- Lake's search for the Lean and Lake installations (`Lake.findInstall?`);
- the load configuration of the working directory, which `loadConfig` makes as
  `Lake.LakeOptions.mkLoadConfig` makes it from the options that hold only those installations
  (`Main.lean:131-145`), as `Regula.ProgramCheck.TestListing.loadConfig_eq` proves;
- the load of the package alone (`Lake.loadPackage`, `Lake/Load/Package.lean:135-139`).

The program does not call `mkLoadConfig`. The module that declares it, `Lake.CLI.Main`, imports
the code of every command of Lake. This module imports only Lake's load of a package
(`Lake.Load.Package`), the path operations that it uses too (`Lake.Util.IO`) and the errors of
Lake's commands (`Lake.CLI.Error`).

It runs the load with Lake's default log configuration, which is the command's when no option is
given (`Lake/CLI/Main.lean:100-107`, `:178-179`, `Lake/Util/Log.lean:125-128`, `:597-612`).
Lake's messages go to standard error, and an error, or an entry of the error level in the log,
fails the load (`Lake.LogIO.toBaseIO`, `Lake/Util/Log.lean:630-638`). The command passes its
arguments to the load configuration (`lakeArgs?`), which only the load of a workspace reads
(`Lake/Load/Workspace.lean:44`), not `Lake.loadPackage`. The load elaborates `lakefile.lean`, which
runs its compiler guard, and writes the compiled configuration below `.lake/config`, as
`lake check-test` does. It builds no target. When the configuration file is there, `lake env`
first loads the workspace itself and fails when Lake cannot load it
(`Lake/CLI/Main.lean:1260-1269`).

## Boundaries

Lake's choice of the configuration file, its elaboration of that file and the value of
`testDriver` that it gives are trusted at the pinned Lean, as `lake test` trusts them. What this
module proves is about the text that the program prints (`listing_ok_iff`). The pipeline reads each
line of standard output, with the white space at its ends removed, as one test identifier, and
skips a blank line. A printed driver is not empty, and its characters are between U+0021 and
U+007E. None of those is a line break or white space, so the pipeline reads the line as exactly
the driver. -/

namespace Regula.TestListing

/-- A character that the listing prints: one of the printable ASCII characters other than space,
U+0021 to U+007E. -/
def Printable (c : Char) : Prop := 0x21 ≤ c.toNat ∧ c.toNat ≤ 0x7E

/-- The test that `listing` runs on each character of the driver (`printable_iff`). -/
def printable (c : Char) : Bool := 0x21 ≤ c.toNat && c.toNat ≤ 0x7E

/-- The executed test accepts exactly the printable characters. -/
theorem printable_iff (c : Char) : printable c = true ↔ Printable c := by
  simp [printable, Printable]

/-- The lines that the listing prints for a package whose test driver is `driver`: none for the
empty driver, which is Lake's report of no test driver, and the driver itself when each of its
characters is printable. Any other driver is refused with a reason, because the pipeline would not
read a line of it as the driver. -/
def listing (driver : String) : Except String (List String) :=
  if driver.isEmpty then .ok []
  else if driver.all printable then .ok [driver]
  else .error s!"Lake reports the test driver {driver.quote}, which has a character outside \
    U+0021 to U+007E, so this listing cannot print it as one test identifier"

/-- The listing prints exactly Lake's report. It prints no line when the driver is empty and only
then, and it prints the driver as its one line when the driver is not empty and each of its
characters is printable. Every other driver is refused. -/
theorem listing_ok_iff (driver : String) (lines : List String) :
    listing driver = .ok lines ↔
      (driver = "" ∧ lines = []) ∨
        (driver ≠ "" ∧ (∀ c ∈ driver.toList, Printable c) ∧ lines = [driver]) := by
  have all_iff : driver.all printable = true ↔ ∀ c ∈ driver.toList, Printable c := by
    simp only [String.all_bool_eq, List.all_eq_true, printable_iff]
  unfold listing
  by_cases empty : driver = ""
  · subst empty
    have isEmpty : "".isEmpty = true := rfl
    simp only [isEmpty, ite_true, Except.ok.injEq, ne_eq, not_true_eq_false, false_and, or_false,
      true_and]
    exact ⟨Eq.symm, Eq.symm⟩
  · have notEmpty : driver.isEmpty = false := String.isEmpty_eq_false_iff.mpr empty
    by_cases allPrintable : driver.all printable = true
    · simp only [notEmpty, allPrintable, Bool.false_eq_true, ite_false, ite_true, Except.ok.injEq,
        empty, false_and, false_or, ne_eq, not_false_eq_true, true_and]
      exact ⟨fun printed => ⟨all_iff.mp allPrintable, printed.symm⟩,
        fun listed => listed.2.symm⟩
    · simp only [notEmpty, allPrintable, Bool.false_eq_true, ite_false, reduceCtorEq, empty,
        false_and, false_or, ne_eq, not_false_eq_true, true_and, false_iff, not_and]
      exact fun each => absurd (all_iff.mpr each) allPrintable

/-- The load configuration of the working directory, with the installations `elanInstall?`,
`leanInstall?` and `lakeInstall?`: the one that `Lake.LakeOptions.mkLoadConfig` makes from the
options that hold only these installations, with the same failures in the same order
(`Regula.ProgramCheck.TestListing.loadConfig_eq`). It fails when the working directory does not
resolve, then when the Lake installation is missing, then when the Lean installation is missing,
and then when Lake cannot compute its environment from them. -/
def loadConfig (elanInstall? : Option Lake.ElanInstall) (leanInstall? : Option Lake.LeanInstall)
    (lakeInstall? : Option Lake.LakeInstall) : EIO Lake.CliError Lake.LoadConfig := do
  let some wsDir ← Lake.resolvePath? "."
    | throw <| .missingRootDir "."
  let lake ← match lakeInstall? with
    | none => throw .unknownLakeInstall
    | some lake => pure lake
  let lean ← match leanInstall? with
    | none => throw .unknownLeanInstall
    | some lean => pure lean
  let lakeEnv ← Lake.Env.compute lake lean elanInstall? none |>.adapt fun msg => .invalidEnv msg
  return {
    lakeArgs? := some #[]
    lakeEnv
    wsDir
    relConfigFile := Lake.defaultConfigFile
    packageOverrides := #[]
    lakeOpts := {}
    leanOpts := Lean.Options.empty
    reconfigure := false
    updateDeps := false
    updateToolchain := true
  }

end Regula.TestListing

open Regula.TestListing in
/-- Print the test driver that Lake reports for the package of the working directory, or nothing
when it reports none. Exit with status 1 when Lake cannot load the package or the driver cannot be
printed as one line (`listing`), and with status 0 otherwise. -/
def main : IO UInt32 := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← Lake.findInstall?
  match ← (loadConfig elanInstall? leanInstall? lakeInstall?).toBaseIO with
  | .error error =>
      IO.eprintln s!"error: {error}"
      return 1
  | .ok config =>
      let some package ← (Lake.loadPackage config).toBaseIO | return 1
      match listing package.testDriver with
      | .ok lines =>
          lines.forM IO.println
          return 0
      | .error reason =>
          IO.eprintln s!"error: {reason}"
          return 1
