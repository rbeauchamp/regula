import RegulaCore.Toolchain

/-! # Selected compiler identity

Resolve an Elan toolchain selector to its `lean` executable and read its version, commit and
origin-checked Core capability. The development toolchain driver and `regula doctor` share
this. A selector is resolved only to a toolchain `elan toolchain list` names, spelled as the
selector or as its release name (`installedName?`), and only that listed name is run, without
Elan's `--install`: a selector naming none is refused, and no channel is resolved and nothing
is installed. Elan's listing, that it runs a listed toolchain without installing, its naming of
release selectors, process execution and the compiler's self-report are trusted; a compiler built
from a tree with uncommitted changes reports that tree's commit, with no marker for them. -/

namespace Regula.Toolchain
open System

/-- The inherited variables that would redirect a selected compiler or its Lake, cleared. -/
def compilerEnv : Array (String × Option String) :=
  #["LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LEAN", "LEAN_AR", "LEAN_CC", "LEAN_GITHASH",
    "LAKE", "LAKE_HOME", "LAKE_OVERRIDE_LEAN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"].map
      (fun name => (name, none))

/-- The `lean` executable of the installed toolchain `selector` names (`installedName?` over
`elan toolchain list`), from directory `root`. Only that listed name is given to `elan run`, without
`--install`. -/
def selectedLean (root : FilePath) (selector : String) : IO FilePath := do
  let listed ← IO.Process.output {
    cmd := "elan", args := #["toolchain", "list"], cwd := some root, env := compilerEnv }
  unless listed.exitCode == 0 do
    throw <| IO.userError s!"cannot list installed toolchains: {listed.stderr.trimAscii}"
  let some name := installedName? (listedToolchains listed.stdout) selector
    | throw <| IO.userError
        s!"cannot resolve selected compiler: Elan lists no installed toolchain for '{selector}'"
  let out ← IO.Process.output {
    cmd := "elan", args := #["run", name, "elan", "which", "lean"]
    cwd := some root, env := compilerEnv }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"cannot resolve selected compiler: {out.stderr.trimAscii}"
  IO.FS.realPath out.stdout.trimAscii.toString

/-- The environment of a command of the selected compiler: `compilerEnv`, the selector, and the
compiler's own binary directory first in `PATH`. -/
def selectedEnv (selector : String) (lean : FilePath) : IO
    (Array (String × Option String)) := do
  let some bin := lean.parent | throw <| IO.userError "compiler has no binary directory"
  let inherited := System.SearchPath.parse ((← IO.getEnv "PATH").getD "")
  return compilerEnv ++ #[("ELAN_TOOLCHAIN", some selector),
    ("PATH", some (System.SearchPath.toString (bin :: inherited)))]

/-- The selected compiler's identity and isolated Core capability, admitted by `parseIdentity`.
The embedded observer is also the collector's source; Lake tracks it as a library input.
It runs as a standalone program in an automatically removed temporary directory. -/
def probe (root : FilePath) (selector : String) : IO Identity := do
  let lean ← selectedLean root selector
  IO.FS.withTempDir fun scratch => do
    let source := scratch / "Identity.lean"
    IO.FS.writeFile source ((include_str "CompilerObservation.lean") ++ "\n\
      def main : IO Unit := do\n\
      \x20 let capability ← Regula.CompilerObservation.legacyPresent \
        (← Lean.getLibDir (← Lean.getBuildDir))\n\
      \x20 IO.println Lean.versionString\n\
      \x20 IO.println Lean.githash\n\
      \x20 IO.println (if capability then \"present\" else \"absent\")\n")
    let out ← IO.Process.output {
      cmd := lean.toString, args := #["--run", source.toString], cwd := some root
      env := ← selectedEnv selector lean }
    unless out.exitCode == 0 do
      throw <| IO.userError s!"compiler probe failed: {out.stdout}{out.stderr}"
    IO.ofExcept (parseIdentity out.stdout)

end Regula.Toolchain
