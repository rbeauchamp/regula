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

/-- Whether `text` spells the program `name` as a process start or a filesystem lookup can resolve
it: equal to it, or to it with the platform's executable suffix (`FilePath.exeExtension`), ignoring
the case of ASCII letters, since the default file systems of macOS and Windows ignore it. -/
def spells (name text : String) : Bool :=
  text.toLower == name ||
    (!FilePath.exeExtension.isEmpty && text.toLower == name ++ "." ++ FilePath.exeExtension)

/-- Whether `text` spells one of the toolchain's programs (`programNames`, `spells`). -/
def spellsProgram (text : String) : Bool := programNames.any (spells · text)

/-- Whether the file name of `cmd` spells `lake` (`spells`): a `lake` by a bare name or a path. -/
def isLake (cmd : String) : Bool := (FilePath.mk cmd).fileName.any (spells "lake")

/-- The text that spells a toolchain program (`spellsProgram`) which a process started as `cmd`
with `args` holds bare, if any: `cmd` itself, or else, when `cmd` is a `lake` (`isLake`), its first
argument that spells one, in whatever position. Lake's own option parsing is not modelled: an
argument of a `lake` that spells a toolchain program is refused wherever it stands. -/
def bareName? (cmd : String) (args : Array String) : Option String :=
  if spellsProgram cmd then some cmd
  else if isLake cmd then args.find? spellsProgram
  else none

/-- `spells` is false exactly when the lowercase text is neither the name nor, on a platform with
an executable suffix, the name with it. -/
theorem spells_eq_false {name text : String} :
    spells name text = false ↔ text.toLower ≠ name ∧
      (FilePath.exeExtension ≠ "" → text.toLower ≠ name ++ "." ++ FilePath.exeExtension) := by
  simp [spells]

/-- `spellsProgram` is false exactly when the text spells no name of `programNames`. -/
theorem spellsProgram_eq_false {text : String} :
    spellsProgram text = false ↔ ∀ name ∈ programNames, text.toLower ≠ name ∧
      (FilePath.exeExtension ≠ "" → text.toLower ≠ name ++ "." ++ FilePath.exeExtension) := by
  simp only [spellsProgram, List.any_eq_false, ← spells_eq_false, Bool.not_eq_true]

/-- `isLake` holds exactly when the command's file name, in lowercase, is `lake` or, on a platform
with an executable suffix, `lake` with it. -/
theorem isLake_iff {cmd : String} :
    isLake cmd = true ↔ ∃ file, (FilePath.mk cmd).fileName = some file ∧
      (file.toLower = "lake" ∨
        (FilePath.exeExtension ≠ "" ∧ file.toLower = "lake." ++ FilePath.exeExtension)) := by
  simp [isLake, spells, Option.any_eq_true]

/-- `bareName?` admits a process exactly when its command, in lowercase, is no toolchain program's
name, with or without the platform's executable suffix, and, when the command's file name is
`lake` in the same sense, none of its arguments is either. -/
theorem bareName?_eq_none_iff {cmd : String} {args : Array String} :
    bareName? cmd args = none ↔
      (∀ name ∈ programNames, cmd.toLower ≠ name ∧
        (FilePath.exeExtension ≠ "" → cmd.toLower ≠ name ++ "." ++ FilePath.exeExtension)) ∧
      ((∃ file, (FilePath.mk cmd).fileName = some file ∧ (file.toLower = "lake" ∨
          (FilePath.exeExtension ≠ "" ∧ file.toLower = "lake." ++ FilePath.exeExtension))) →
        ∀ argument ∈ args, ∀ name ∈ programNames, argument.toLower ≠ name ∧
          (FilePath.exeExtension ≠ "" →
            argument.toLower ≠ name ++ "." ++ FilePath.exeExtension)) := by
  rw [← spellsProgram_eq_false, ← isLake_iff]
  simp only [← spellsProgram_eq_false]
  unfold bareName?
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

/-- The environment variables through which Lake's `LeanInstall.get`
(`Lake/Config/InstallPath.lean:272` of Lean v4.34.1) chooses a program for the builds it runs:
`LEAN_AR` and `LEAN_CC`, and `AR` and `CC` where the installation bundles no `llvm-ar` or `clang`.
Lake runs the value of each as it is, so a bare name is one that `PATH` resolves. -/
def programOverrides : List String := ["LEAN_AR", "AR", "LEAN_CC", "CC"]

/-- Throws when a variable of `programOverrides`, as a process started with the environment changes
`env` sees it, is set to a path that is not absolute. That value is its last change in `env`, else
this process's own. An absolute value is accepted whatever it names. -/
def refuseRelativeOverrides (env : Array (String × Option String) := #[]) : IO Unit := do
  for name in programOverrides do
    let value ← match (env.filter (·.1 == name)).back? with
      | some (_, value) => pure value
      | none => IO.getEnv name
    if let some value := value then
      unless (FilePath.mk value).isAbsolute do
        throw <| IO.userError s!"the toolchain program override {name}={value} is not an \
          absolute path, so PATH could resolve it; unset it or give an absolute path"

end Regula.Toolchain
