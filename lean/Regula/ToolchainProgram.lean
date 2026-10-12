module

public import Regula.CompilerObservation
public import RegulaPolicy.Compiler

/-! # The toolchain's programs

`freshChecker` runs the toolchain's `lake` and `leanchecker` by their paths in the toolchain's
installation directory, not by a bare name that `PATH` resolves. `lake env` puts the binary
directory of every package of a workspace before the toolchain's on the `PATH` of the program it
starts (`Lake.Workspace.augmentedPath`), so a bare name could run a program of the project or of one
of its dependencies instead. The installation directory is `Regula.CompilerObservation.toolchainRoot`,
accepted once its `lean` reports the identity of the compiler this Regula build pins
(`Regula.CompilerObservation.identifiedRoot`). Its other programs are trusted to be that
installation's; no program reports more of its identity than `lean` does.
-/

public section

namespace Regula.Toolchain
open System

private initialize identified : IO.Ref (Option FilePath) ← IO.mkRef none

/-- The installation directory of the Lean toolchain, found once for the process:
`Regula.CompilerObservation.identifiedRoot` for the version and commit of the compiler this Regula
build pins (`RegulaPolicy.Compiler.version` and `commit`). -/
def sysroot : IO FilePath := do
  if let some root ← identified.get then return root
  let root ← Regula.CompilerObservation.identifiedRoot RegulaPolicy.Compiler.version
    RegulaPolicy.Compiler.commit
  identified.set (some root)
  return root

/-- The path of the program `name` in the binary directory of the toolchain's installation
directory (`sysroot`), with the platform's executable extension added. Throws when that
installation has no file there. -/
def program (name : String) : IO FilePath := do
  let path := (← sysroot) / "bin" / name |>.addExtension FilePath.exeExtension
  unless ← path.pathExists do
    throw <| IO.userError s!"the Lean toolchain has no program {name} at {path}"
  return path

end Regula.Toolchain
