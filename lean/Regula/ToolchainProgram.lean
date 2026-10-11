module

public import Regula.CompilerObservation
public import RegulaPolicy.Compiler

/-! # The toolchain's programs

Regula runs a program of the Lean toolchain, such as `lean`, `lake` or `leanchecker`, by its path
in the toolchain's installation directory, never by a bare name that `PATH` resolves. Lake puts the
binary directory of every package of a workspace before the toolchain's on the `PATH` of the
programs it starts (`Lake.Workspace.augmentedPath`, used by `lake env`, `lake exe` and `lake lint`),
so a bare name could run a program of the project or of one of its dependencies instead. The
installation directory is the canonical path of the absolute `LEAN_SYSROOT` that Lake sets, or in a
`lean` without it that `lean`'s own installation (`Regula.CompilerObservation.toolchainRoot`),
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

/-- The arguments of a `lake` that can name the program `lake env` starts: each argument that
follows an argument `env`, so also after Lake's global options, as in `lake -d <dir> env lean`.
Other arguments, such as a target or a module named `Lean`, are not programs. -/
def envPrograms (args : Array String) : List String :=
  (List.range args.size).filterMap fun i => if args[i]? = some "env" then args[i + 1]? else none

/-- The text that spells a toolchain program (`spellsProgram`) which a process started as `cmd`
with `args` holds bare, if any: `cmd` itself, or else, when `cmd` is a `lake` (`isLake`), the first
of its arguments that can name the program `lake env` starts (`envPrograms`) that spells one. -/
def bareName? (cmd : String) (args : Array String) : Option String :=
  if spellsProgram cmd then some cmd
  else if isLake cmd then (envPrograms args).find? spellsProgram
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

/-- A text is in `envPrograms` exactly when it is the argument at the position after one that
holds `env`. -/
theorem mem_envPrograms {args : Array String} {program : String} :
    program ∈ envPrograms args ↔ ∃ i, args[i]? = some "env" ∧ args[i + 1]? = some program := by
  simp only [envPrograms, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨i, -, found⟩
    split at found
    · exact ⟨i, by assumption, found⟩
    · cases found
  · rintro ⟨i, env, next⟩
    exact ⟨i, (Array.getElem?_eq_some_iff.mp env).1, by simp [env, next]⟩

/-- `bareName?` admits a process exactly when its command, in lowercase, is no toolchain program's
name, with or without the platform's executable suffix, and, when the command's file name is
`lake` in the same sense, no argument at the position after an argument `env` is either. -/
theorem bareName?_eq_none_iff {cmd : String} {args : Array String} :
    bareName? cmd args = none ↔
      (∀ name ∈ programNames, cmd.toLower ≠ name ∧
        (FilePath.exeExtension ≠ "" → cmd.toLower ≠ name ++ "." ++ FilePath.exeExtension)) ∧
      ((∃ file, (FilePath.mk cmd).fileName = some file ∧ (file.toLower = "lake" ∨
          (FilePath.exeExtension ≠ "" ∧ file.toLower = "lake." ++ FilePath.exeExtension))) →
        ∀ i program, args[i]? = some "env" → args[i + 1]? = some program →
          ∀ name ∈ programNames, program.toLower ≠ name ∧
            (FilePath.exeExtension ≠ "" →
              program.toLower ≠ name ++ "." ++ FilePath.exeExtension)) := by
  rw [← spellsProgram_eq_false, ← isLake_iff]
  simp only [← spellsProgram_eq_false]
  unfold bareName?
  split
  · rename_i named
    simp [named]
  · rename_i unnamed
    split
    · rename_i lake
      simp only [unnamed, lake, List.find?_eq_none, Bool.not_eq_true, true_and, forall_const]
      exact ⟨fun none i program env next => none program (mem_envPrograms.mpr ⟨i, env, next⟩),
        fun none program named => let ⟨i, env, next⟩ := mem_envPrograms.mp named
          none i program env next⟩
    · rename_i other
      simp [unnamed, other]

/-- Throws when a process started as `cmd` with `args` holds a toolchain program's bare name in a
place `bareName?` reads: as its command, or, for a `lake`, as the program `lake env` starts. -/
def refuseBareName (cmd : String) (args : Array String) : IO Unit := do
  if let some name := bareName? cmd args then
    throw <| IO.userError s!"the toolchain's {name} runs by its path (Regula.Toolchain.program), \
      not by a bare name that PATH resolves"

/-- The environment variables through which Lake's `LeanInstall.get`
(`Lake/Config/InstallPath.lean:272` of Lean v4.34.1) can choose a program for the builds it runs
(`overridesRead`). Lake runs the value it reads as it is, so a bare name is one that `PATH`
resolves. -/
def programOverrides : List String := ["LEAN_AR", "AR", "LEAN_CC", "CC"]

/-- The variable, with its value under `lookup`, from which Lake takes a program: `preferred` when
it is set, else, when the installation bundles no such program (`bundled` false), `fallback` when
it is set. -/
def override? (lookup : String → Option String) (preferred fallback : String) (bundled : Bool) :
    Option (String × String) :=
  match lookup preferred with
  | some value => some (preferred, value)
  | none => if bundled then none else (lookup fallback).map (fallback, ·)

/-- The variables, with their values under `lookup`, that Lake's `LeanInstall.get` reads to choose
its archiver (`findAr`, `Lake/Config/InstallPath.lean:289` of Lean v4.34.1: `LEAN_AR`, else `AR`
when the installation has no `bin/llvm-ar`, `bundledAr`) and its C compiler (`setCc`, line 300:
`LEAN_CC`, else `CC` when it has no `bin/clang`, `bundledCc`). -/
def overridesRead (lookup : String → Option String) (bundledAr bundledCc : Bool) :
    List (String × String) :=
  (override? lookup "LEAN_AR" "AR" bundledAr).toList ++
    (override? lookup "LEAN_CC" "CC" bundledCc).toList

/-- The variables of `overridesRead` whose value is not an absolute path. -/
def relativeOverrides (lookup : String → Option String) (bundledAr bundledCc : Bool) :
    List (String × String) :=
  (overridesRead lookup bundledAr bundledCc).filter fun (_, value) =>
    !(FilePath.mk value).isAbsolute

/-- `override?` gives a variable exactly when it is `preferred` and set, or it is `fallback`, set,
with `preferred` unset and no bundled program. -/
theorem override?_eq_some_iff {lookup : String → Option String} {preferred fallback : String}
    {bundled : Bool} {name value : String} :
    override? lookup preferred fallback bundled = some (name, value) ↔
      (name = preferred ∧ lookup preferred = some value) ∨
      (name = fallback ∧ lookup preferred = none ∧ bundled = false ∧
        lookup fallback = some value) := by
  unfold override?
  split
  · rename_i set
    simp [set, eq_comm]
  · rename_i unset
    cases bundled <;> simp [unset, eq_comm]
    exact And.comm

/-- `relativeOverrides` holds a variable exactly when Lake's `findAr` or `setCc` reads it, as
`overridesRead` states their order, and its value is not an absolute path. -/
theorem mem_relativeOverrides {lookup : String → Option String} {bundledAr bundledCc : Bool}
    {name value : String} :
    (name, value) ∈ relativeOverrides lookup bundledAr bundledCc ↔
      ((name = "LEAN_AR" ∧ lookup "LEAN_AR" = some value) ∨
        (name = "AR" ∧ lookup "LEAN_AR" = none ∧ bundledAr = false ∧ lookup "AR" = some value) ∨
        (name = "LEAN_CC" ∧ lookup "LEAN_CC" = some value) ∨
        (name = "CC" ∧ lookup "LEAN_CC" = none ∧ bundledCc = false ∧ lookup "CC" = some value)) ∧
      (FilePath.mk value).isAbsolute = false := by
  simp only [relativeOverrides, overridesRead, List.mem_filter, List.mem_append,
    Option.mem_toList, override?_eq_some_iff, Bool.not_eq_true', or_assoc]

/-- Throws when the Lake of the toolchain's installation (`sysroot`), started with the environment
changes `env`, would run a program override that is not an absolute path (`relativeOverrides`).
The value of a variable is its last change in `env`, else this process's own; whether the
installation bundles `llvm-ar` and `clang` is whether its `bin` directory has them. An absolute
value is accepted whatever it names. -/
def refuseRelativeOverrides (env : Array (String × Option String) := #[]) : IO Unit := do
  let mut values : List (String × String) := []
  for name in programOverrides do
    let value ← match (env.filter (·.1 == name)).back? with
      | some (_, value) => pure value
      | none => IO.getEnv name
    if let some value := value then values := (name, value) :: values
  let bin := (← sysroot) / "bin"
  let bundled (name : String) := (bin / name |>.addExtension FilePath.exeExtension).pathExists
  let lookup := fun name => List.lookup name values
  let relative := relativeOverrides lookup (← bundled "llvm-ar") (← bundled "clang")
  if let (name, value) :: _ := relative then
    throw <| IO.userError s!"the toolchain program override {name}={value}, which Lake runs, is \
      not an absolute path, so PATH could resolve it; unset it or give an absolute path"

/-- The environment changes that each Lake process Regula starts gets: `LEAN_SYSROOT` is the
identity-checked installation (`sysroot`) and `LAKE_OVERRIDE_LEAN` is unset. A toolchain `lake`
beside its `lean` then takes its own installation (`Lake.findLakeLeanJointHome?`), and
`Lake.findInstall?` does not run `Lake.findLeanInstall?`, which starts a `lean --print-prefix` that
`PATH` resolves when `LEAN_SYSROOT` and `LEAN` are unset. A caller puts these changes before its
own, so a control's deliberate `LEAN_SYSROOT` stays. -/
def lakeChildEnv : IO (Array (String × Option String)) := do
  return #[("LEAN_SYSROOT", some (← sysroot).toString), ("LAKE_OVERRIDE_LEAN", none)]

end Regula.Toolchain
