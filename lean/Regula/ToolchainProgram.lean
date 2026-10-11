module

public import Regula.CompilerObservation
public import RegulaPolicy.Compiler

/-! # The toolchain's programs

Regula runs a program of the Lean toolchain, such as `lean`, `lake` or `leanchecker`, by its path
in the toolchain's installation directory, never by a bare name that `PATH` resolves. Lake puts the
binary directory of every package of a workspace before the toolchain's on the `PATH` of the
programs it starts (`Lake.Workspace.augmentedPath`, used by `lake env`, `lake exe` and `lake lint`),
so a bare name could run a program of the project or of one of its dependencies instead. The
installation directory is the canonical path of the absolute `LEAN_SYSROOT` that Lake sets
(`Regula.CompilerObservation.toolchainRoot`), accepted once its `lean` reports the identity of the
compiler this Regula build pins (`Regula.CompilerObservation.identifiedRoot`). Its other programs
are trusted to be that installation's; no program reports more of its identity than `lean` does.
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

/-- The bare names of the programs in the binary directory of the pinned toolchain's installation
on the supported platforms, as its release archives lay them out. -/
def programNames : List String :=
  ["cadical", "clang", "lake", "ld.lld", "ld64.lld", "lean", "leanc", "leanchecker", "leanir",
    "leanmake", "leantar", "llvm-ar"]

/-- The toolchain program name (`programNames`) that a process started as `cmd` with `args` holds
bare, if any: `cmd` itself, or else, when `cmd` is a `lake`, its first argument that is such a
name, in whatever position. Lake's own option parsing is not modelled: an argument of a `lake` that
spells a toolchain program's name is refused wherever it stands. -/
def bareName? (cmd : String) (args : Array String) : Option String :=
  if programNames.contains cmd then some cmd
  else if (FilePath.mk cmd).fileName == some "lake" then args.find? programNames.contains
  else none

/-- `bareName?` admits a process exactly when its command is not a toolchain program's bare name
and, when the command is a `lake`, none of its arguments is one. -/
theorem bareName?_eq_none_iff {cmd : String} {args : Array String} :
    bareName? cmd args = none ↔ cmd ∉ programNames ∧
      ((FilePath.mk cmd).fileName = some "lake" →
        ∀ argument ∈ args, argument ∉ programNames) := by
  unfold bareName?
  simp only [List.contains_iff_mem, beq_iff_eq]
  split
  · rename_i named
    simp [named]
  · rename_i unnamed
    split
    · rename_i lake
      simp [unnamed, lake, Array.find?_eq_none]
    · rename_i other
      simp [unnamed, other]

/-- Throws when a process started as `cmd` with `args` holds a toolchain program's bare name in a
place `bareName?` reads: as its command, or as any argument of a `lake`. -/
def refuseBareName (cmd : String) (args : Array String) : IO Unit := do
  if let some name := bareName? cmd args then
    throw <| IO.userError s!"the toolchain's {name} runs by its path (Regula.Toolchain.program), \
      not by a bare name that PATH resolves"

end Regula.Toolchain
