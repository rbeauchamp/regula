module

public import Regula.Process
public import RegulaPolicy.Compiler

/-! # The toolchain's programs

`freshChecker` runs the toolchain's `lake` and `leanchecker` by their paths in the toolchain's
installation directory, not by a bare name that `PATH` resolves. `lake env` puts the binary
directory of every package of a workspace before the toolchain's on the `PATH` of the program it
starts (`Lake.Workspace.augmentedPath`), so a bare name could run a program of the project or of one
of its dependencies instead. `Regula.Process.identified` selects the installation without PATH
and accepts it once its Lean reports the identity of the compiler that built this program.
Its other programs are trusted to be that
installation's; no program reports more of its identity than `lean` does.
-/

public section

namespace Regula.Toolchain
open System

/-- The identity-checked installation directory, retained by the process observer's cache. -/
def sysroot : IO FilePath := Regula.Process.sysroot

/-- The path of the closed tool selection in the binary directory of the toolchain's installation
directory (`sysroot`), with the platform's executable extension added. Throws when that
installation has no file there. -/
def program (tool : Regula.Process.Tool) : IO FilePath := Regula.Process.toolPath tool

end Regula.Toolchain
