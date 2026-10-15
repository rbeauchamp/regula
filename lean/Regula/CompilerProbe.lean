import RegulaCore.Toolchain
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

/-- The `lean` executable of the installed toolchain `selector` names (`installedName?` over
`elan toolchain list`), from directory `root`. Only that listed name is given to `elan run`, without
`--install`. The path that `elan which lean` prints is read exactly
(`Regula.Filesystem.Construction.printedPath?`: only the final newline is removed), and output that
is not one absolute path printed as a line is thrown.

Assumes: Elan 4.2.4 `elan which` prints the path of the binary with `println!` and `Path::display`
(`src/elan-cli/elan_mode.rs:290-302`): `bin/lean` below the toolchain's directory
(`src/elan/toolchain.rs:595-620`), which is the directory of its name in the `toolchains` directory
of Elan's home (`src/elan/toolchain.rs:390-399`, `src/elan/config.rs:74-80`). The toolchain is the
one that `ELAN_TOOLCHAIN` names (`src/elan/config.rs:135-141`, `:156-166`), which `elan run` sets
for the inner `elan`, with `ELAN_HOME` (`src/elan/toolchain.rs:544-551`). The inner `elan` reads its
home as that `ELAN_HOME` joined to its current directory (`src/elan-utils/src/utils.rs:438-445`),
so the path is absolute. `Path::display` prints a byte that is not UTF-8 changed, so a path that is
not UTF-8 is outside this protocol. -/
def selectedLean (root : FilePath) (selector : String) : IO FilePath := do
  let listed ← IO.Process.output {
    cmd := "elan", args := #["toolchain", "list"], cwd := some root, env := compilerEnv }
  unless listed.exitCode == 0 do
    throw <| IO.userError s!"cannot list installed toolchains: {listed.stderr.trimAscii}"
  let some name := installedName? (listedToolchains listed.stdout) selector
    | throw <| IO.userError
        s!"cannot resolve selected compiler: Elan lists no installed toolchain named exactly \
          '{selector}'"
  let out ← IO.Process.output {
    cmd := "elan", args := #["run", name, "elan", "which", "lean"]
    cwd := some root, env := compilerEnv }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"cannot resolve selected compiler: {out.stderr.trimAscii}"
  let some lean := Regula.Filesystem.Construction.printedPath? out.stdout
    | throw <| IO.userError s!"cannot resolve selected compiler: `elan which lean` printed \
        {out.stdout.quote}, not one absolute path"
  IO.FS.realPath lean

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
  Regula.Filesystem.withOwnTempDir fun scratch => do
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
