import RegulaCore.Toolchain

/-! # Selected compiler identity

Resolve an Elan toolchain selector to its `lean` executable and read its version, commit and
origin-checked Core capability. The development toolchain driver and `regula doctor` share
this. `elan run` installs a known release that is missing, so a selector is first resolved to
a toolchain `elan toolchain list` names, and only that name is run: a selector naming none is
refused, and a release channel such as `stable` names none. Elan's listing, that it runs a
toolchain it lists without installing, its naming of release selectors, process execution and
the compiler's self-report are trusted; a compiler built from a tree with uncommitted changes
reports that tree's commit, with no marker for them. -/

namespace Regula.Toolchain
open System

/-- The inherited variables that would redirect a selected compiler or its Lake, cleared. -/
def compilerEnv : Array (String × Option String) :=
  #["LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LEAN", "LEAN_AR", "LEAN_CC", "LEAN_GITHASH",
    "LAKE", "LAKE_HOME", "LAKE_OVERRIDE_LEAN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"].map
      (fun name => (name, none))

/-- The `lean` executable of the installed toolchain `selector` names (`installedName?` over
`elan toolchain list`), from directory `root`. Only that listed name is given to `elan run`,
which would install any other known release. -/
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
The embedded observer is also the collector's source; Lake tracks it as a library input. -/
def probe (root : FilePath) (selector : String) : IO Identity := do
  let lean ← selectedLean root selector
  let out ← IO.Process.output {
    cmd := lean.toString, args := #["--stdin"], cwd := some root
    env := ← selectedEnv selector lean }
    (some ((include_str "CompilerObservation.lean") ++ "\n\
      #eval do\n\
      \x20 let capability ← Regula.CompilerObservation.legacyPresent \
        (← Lean.getLibDir (← Lean.getBuildDir))\n\
      \x20 IO.println Lean.versionString\n\
      \x20 IO.println Lean.githash\n\
      \x20 IO.println (if capability then \"present\" else \"absent\")\n"))
  unless out.exitCode == 0 do
    throw <| IO.userError s!"compiler probe failed: {out.stdout}{out.stderr}"
  IO.ofExcept (parseIdentity out.stdout)

end Regula.Toolchain
