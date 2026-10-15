import RegulaCore.Toolchain
import Regula.Process
import Regula.Filesystem

/-! # Selected compiler identity

Resolve an Elan toolchain selector to its `lean` executable and read its version, commit and
origin-checked Core capability. `regula doctor` uses this observation. A selector is resolved only to a toolchain `elan toolchain list` names, spelled exactly as
the selector (`installedName?`), and only that listed name is run, without
Elan's `--install`: a selector naming none is refused, and no channel is resolved and nothing
is installed. Elan's listing, that it runs a listed toolchain without installing, process
execution and the compiler's self-report are trusted; a compiler built
from a tree with uncommitted changes reports that tree's commit, with no marker for them. -/

namespace Regula.Toolchain
open System

/-- The inherited variables that would redirect a selected compiler or its Lake, cleared. -/
def compilerEnv : Array (String × Option String) :=
  #["LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LEAN", "LEAN_AR", "LEAN_CC", "LEAN_GITHASH",
    "LAKE", "LAKE_HOME", "LAKE_OVERRIDE_LEAN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"].map
      (fun name => (name, none))

/-- The `elan` the doctor runs: `bin/elan` of the Elan installation at `home`, by its absolute path.
No PATH entry is read or searched, so a workspace package's binary directory, which Lake puts first
in the `PATH` of `lake exe` and `lake env`, supplies no `elan`.
Assumes: Lean v4.34.1 `Lake/Config/InstallPath.lean:30-35` places Elan's executables in its home's
`bin`. Elan v4.1.2 `src/elan/toolchain.rs` (`create_command`, `set_env`) runs an absolute command
as given and sets `ELAN_HOME` and `ELAN_TOOLCHAIN` for it. The installed Elan, its listing and its
toolchains are trusted. -/
def elanExecutable (home : FilePath) : IO FilePath := do
  let elan := (home / "bin" / "elan").addExtension FilePath.exeExtension
  unless ← Regula.Filesystem.isPresent elan do
    throw <| IO.userError s!"cannot find elan at {elan}, the Elan installation's binary directory"
  return elan

/-- The `lean` executable of the installed toolchain `selector` names (`installedName?` over
`elan toolchain list`), from directory `root`. Each Elan command runs the doctor's `elan`
(`elanExecutable`) of the Elan home `Regula.Process.elanHome` by its path, with that home. Only that
listed name is given to `elan run`, without `--install`. -/
def selectedLean (root : FilePath) (selector : String) : IO FilePath := do
  let home := (← Regula.Process.elanHome).val
  let elan ← elanExecutable home
  let env := compilerEnv.push ("ELAN_HOME", some home.toString)
  let listed ← Regula.Process.output (.stated elan "Elan lists the explicitly selected installed compilers") {
    cmd := elan.toString, args := #["toolchain", "list"], cwd := some root, env }
  unless listed.exitCode == 0 do
    throw <| IO.userError s!"cannot list installed toolchains with {elan}: {listed.stderr.trimAscii}"
  let some name := installedName? (listedToolchains listed.stdout) selector
    | throw <| IO.userError
        s!"cannot resolve selected compiler: Elan lists no installed toolchain named exactly \
          '{selector}'"
  let out ← Regula.Process.output (.stated elan "Elan resolves a listed installed compiler without installing") {
    cmd := elan.toString, args := #["run", name, elan.toString, "which", "lean"]
    cwd := some root, env }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"cannot resolve selected compiler: {out.stderr.trimAscii}"
  let selected ← IO.ofExcept (Regula.Process.absolute out.stdout.trimAscii.toString)
  return (← IO.ofExcept (Regula.Process.absolute (← IO.FS.realPath selected.val))).val

/-- The environment of a command of the selected compiler: `compilerEnv`, the selector, and the
compiler's own binary directory first in `PATH`. -/
def selectedEnv (selector : String) (lean : FilePath) : IO
    (Array (String × Option String)) := do
  let some bin := lean.parent | throw <| IO.userError "compiler has no binary directory"
  let inherited := System.SearchPath.parse ((← Regula.Process.readEnv "PATH").getD "")
  return compilerEnv ++ #[("ELAN_TOOLCHAIN", some selector),
    ("PATH", some (System.SearchPath.toString (bin :: inherited)))]

/-- The selected compiler's identity and isolated Core capability, admitted by `parseIdentity`.
The embedded observer is also the collector's source; Lake tracks it as a library input.
It runs as a standalone program in an automatically removed temporary directory. -/
def probe (root : FilePath) (selector : String) : IO Identity := do
  let lean ← selectedLean root selector
  Regula.Filesystem.withOwnTempDir fun scratch => do
    let source := scratch / "Identity.lean"
    IO.FS.writeFile source ((include_str "CompilerObservation.lean") ++ "\n\
      def main : IO Unit := do\n\
      \x20 let capability ← Regula.CompilerObservation.legacyPresent \
        (← Lean.getLibDir (← Lean.getBuildDir))\n\
      \x20 IO.println Lean.versionString\n\
      \x20 IO.println Lean.githash\n\
      \x20 IO.println (if capability then \"present\" else \"absent\")\n")
    let out ← Regula.Process.output (.stated lean "The doctor intentionally observes this separately selected installed compiler") {
      cmd := lean.toString, args := #["--run", source.toString], cwd := some root
      env := ← selectedEnv selector lean }
    unless out.exitCode == 0 do
      throw <| IO.userError s!"compiler probe failed: {out.stdout}{out.stderr}"
    IO.ofExcept (parseIdentity out.stdout)

end Regula.Toolchain
