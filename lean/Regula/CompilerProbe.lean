import RegulaCore.Toolchain

/-! # Selected compiler identity

Resolve an Elan toolchain selector to its `lean` executable and read the version and commit
that compiler reports about itself. The development toolchain driver and `regula doctor` share
this. Nothing is installed: `elan run` refuses a toolchain that is not installed. Elan
resolution, process execution and the compiler's self-report are trusted; a compiler built
from a tree with uncommitted changes reports that tree's commit, with no marker for them. -/

namespace Regula.Toolchain
open System

/-- The inherited variables that would redirect a selected compiler or its Lake, cleared. -/
def compilerEnv : Array (String × Option String) :=
  #["LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LEAN", "LEAN_AR", "LEAN_CC", "LEAN_GITHASH",
    "LAKE", "LAKE_HOME", "LAKE_OVERRIDE_LEAN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"].map
      (fun name => (name, none))

/-- The `lean` executable Elan resolves `selector` to, from directory `root`. -/
def selectedLean (root : FilePath) (selector : String) : IO FilePath := do
  let out ← IO.Process.output {
    cmd := "elan", args := #["run", selector, "elan", "which", "lean"]
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

/-- The identity the compiler that `selector` resolves to reports, admitted by `parseIdentity`. -/
def probe (root : FilePath) (selector : String) : IO Identity := do
  let lean ← selectedLean root selector
  let out ← IO.Process.output {
    cmd := lean.toString, args := #["--stdin"], cwd := some root
    env := ← selectedEnv selector lean }
    (some "#eval IO.println Lean.versionString\n#eval IO.println Lean.githash\n")
  unless out.exitCode == 0 do
    throw <| IO.userError s!"compiler probe failed: {out.stdout}{out.stderr}"
  IO.ofExcept (parseIdentity out.stdout)

end Regula.Toolchain
