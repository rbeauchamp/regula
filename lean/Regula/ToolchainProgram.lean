module

public import Lean.Util.Path
public import RegulaPolicy.Compiler

/-! # The toolchain's programs

Regula runs a program of the Lean toolchain, such as `lean`, `lake` or `leanchecker`, by its path
in the toolchain's installation directory, never by a bare name that `PATH` resolves. Lake puts the
binary directory of every package of a workspace before the toolchain's on the `PATH` of the
programs it starts (`Lake.Workspace.augmentedPath`, used by `lake env`, `lake exe` and `lake lint`),
so a bare name could run a program of the project or of one of its dependencies instead. The
installation directory is the one whose `lean` reports the identity of the compiler this Regula
build pins. Its other programs are trusted to be that installation's; no program reports more of
its identity than `lean` does. `Regula.Collect.compilerCapability` makes the same check of the same
`lean` for itself: it is in the import closure of the force-loaded probe, which admits only policy
and infrastructure modules (`RegulaPolicy.infrastructureModuleNames`), so it does not import this
module. -/

public section

namespace Regula.Toolchain
open System

private initialize identified : IO.Ref (Option FilePath) ← IO.mkRef none

/-- The installation directory of the Lean toolchain, found once for the process:
`Lean.findSysroot` (`LEAN_SYSROOT`, which Lake sets for the programs it starts, else the prefix
that the `lean` on `PATH` prints), accepted only once its `bin/lean`, run without the inherited
`LEAN_PATH`, `LEAN_SRC_PATH` and `LEAN_SYSROOT`, prints the version and commit of the compiler this
Regula build pins (`RegulaPolicy.Compiler.version` and `commit`). A program that prints them is
taken to be that compiler; process execution and the installation's contents are trusted. -/
def sysroot : IO FilePath := do
  if let some root ← identified.get then return root
  let root ← Lean.findSysroot
  let output ← IO.Process.output {
    cmd := (root / "bin" / "lean").toString, args := #["--stdin"]
    env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none), ("LEAN_SYSROOT", none)] }
    (some "#eval IO.println Lean.versionString\n#eval IO.println Lean.githash\n")
  unless output.exitCode == 0 && output.stdout ==
      s!"{RegulaPolicy.Compiler.version}\n{RegulaPolicy.Compiler.commit}\n" do
    throw <| IO.userError
      "compiler capability: resolved compiler identity differs from this Regula build"
  identified.set (some root)
  return root

/-- The path of the program `name` in the binary directory of the toolchain's installation
directory (`sysroot`), with the platform's executable extension. Throws when that installation has
no file there. -/
def program (name : String) : IO FilePath := do
  let path := (← sysroot) / "bin" / name |>.withExtension FilePath.exeExtension
  unless ← path.pathExists do
    throw <| IO.userError s!"the Lean toolchain has no program {name} at {path}"
  return path

/-- The bare names of the programs in the binary directory of the pinned toolchain's installation
on the supported platforms, as its release archives lay them out. -/
def programNames : List String :=
  ["cadical", "clang", "lake", "ld.lld", "ld64.lld", "lean", "leanc", "leanchecker", "leanir",
    "leanmake", "leantar", "llvm-ar"]

/-- The bare toolchain program name (`programNames`) that a process started as `cmd` with `args`
would look up on `PATH`, if any: `cmd` itself, or else, when `cmd` is a `lake` and `args` start
with `env`, the program that `lake env` starts. -/
def bareName? (cmd : String) (args : Array String) : Option String :=
  if programNames.contains cmd then some cmd
  else if (FilePath.mk cmd).fileName == some "lake" && args[0]? == some "env" then
    args[1]?.filter programNames.contains
  else none

/-- A process that `bareName?` admits names no toolchain program bare: neither as the command
nor, for a `lake env`, as the program that `lake env` starts. -/
theorem bareName?_eq_none {cmd : String} {args : Array String} (h : bareName? cmd args = none) :
    cmd ∉ programNames ∧ ((FilePath.mk cmd).fileName = some "lake" → args[0]? = some "env" →
      ∀ name ∈ args[1]?, name ∉ programNames) := by
  unfold bareName? at h
  simp only [List.contains_iff_mem, beq_iff_eq, Bool.and_eq_true] at h
  split at h
  · simp at h
  · rename_i hc
    refine ⟨hc, fun lake env name named mem => ?_⟩
    simp [lake, env, Option.mem_def.mp named, Option.filter, mem] at h

/-- Throws when a process started as `cmd` with `args` would run a toolchain program by its bare
name (`bareName?`), instead of by its path (`program`). -/
def refuseBareName (cmd : String) (args : Array String) : IO Unit := do
  if let some name := bareName? cmd args then
    throw <| IO.userError s!"the toolchain's {name} runs by its path (Regula.Toolchain.program), \
      not by a bare name that PATH resolves"

end Regula.Toolchain
