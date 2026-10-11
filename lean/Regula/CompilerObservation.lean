module

public import Lean.Environment
public import Lean.Util.Path
import Lake.Config.InstallPath

/-! # Isolated compiler capability observation

This operational collector imports only the selected compiler's Core into a separate
environment with extension loading disabled. It never inspects the audited environment
or changes the global search path. Every resolved Core dependency must come from the
compiler's own library directory. The preparation driver executes this same source
with the selected compiler; no compiled Regula dependency is required. -/

public section

namespace Regula.CompilerObservation
open Lean

private def equality (type left right : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [.succ .zero]) type left right

private def reductionAxiomType (typeName reducer : Name) : Expr :=
  let type := mkConst typeName
  .forallE `a type (.forallE `b type
    (.forallE `h (equality type (mkApp (mkConst reducer) (.bvar 1)) (.bvar 0))
      (equality type (.bvar 2) (.bvar 1)) .default) .default) .default

/-- Observe the complete legacy family (`true`) or its complete absence (`false`).
Partial presence, a wrong declaration shape or an origin outside the selected compiler
is an error. Canonical-path resolution and compiler import are trusted IO observations. -/
def legacyPresent (library : System.FilePath) : IO Bool := do
  let env ← importModules #[{ module := `Init.Core }] {} (loadExts := false)
  for name in env.header.moduleNames do
    let actual ← IO.FS.realPath (← findOLean name)
    let expected ← IO.FS.realPath (modToFilePath library name "olean")
    unless actual == expected do
      throw <| IO.userError s!"compiler capability: foreign Core dependency {name}"
  let expected := #[
    (`Lean.trustCompiler, mkConst ``True),
    (`Lean.ofReduceBool, reductionAxiomType ``Bool `Lean.reduceBool),
    (`Lean.ofReduceNat, reductionAxiomType ``Nat `Lean.reduceNat)]
  let mut present := 0
  for (name, type) in expected do
    match env.find? name with
    | none => pure ()
    | some (.axiomInfo value) =>
      let some owner := env.getModuleIdxFor? name
        | throw <| IO.userError s!"compiler capability: missing owner for {name}"
      unless env.header.moduleNames[(owner : Nat)]? == some `Init.Core &&
          !value.isUnsafe && value.levelParams.isEmpty && value.type.eqv type do
        throw <| IO.userError s!"compiler capability: unexpected legacy axiom {name}"
      present := present + 1
    | some _ => throw <| IO.userError s!"compiler capability: legacy name is not an axiom: {name}"
  if present == 0 then return false
  if present == expected.size then return true
  throw <| IO.userError "compiler capability: incomplete legacy axiom family"

/-- The installation directory of the Lean toolchain, by its canonical path: the value of
`LEAN_SYSROOT`, which must be an absolute path; or, when it is unset and the running program is a
`lean` (the file stem of `IO.appPath`), that `lean`'s own installation (`Lean.getBuildDir`, the
parent of the canonical directory of the running `lean`); or, when it is unset in any other
program, the Elan toolchain that `ELAN_TOOLCHAIN` names, in the `toolchains` directory of the Elan
home that `ELAN_HOME` gives (`Lake.findElanInstall?`, `Lake/Config/InstallPath.lean:217`, and
`Lake.ElanInstall.toolchainDir`, line 54, which names it by `Lake.toolchain2Dir`, line 38). Throws
when `LEAN_SYSROOT` or `ELAN_HOME` is relative, when `ELAN_TOOLCHAIN` is needed and unset, or when
Elan's home is unknown; no `lean` is run to find the directory, so no program that `PATH`
resolves takes part.
Assumes: Lake sets `LEAN_SYSROOT` for each program it starts (`lake exe`, `lake env`, `lake lint`)
to the installation it detected (`Lake.Env.baseVars`, `Lake/Config/Env.lean:302` of Lean v4.34.1).
For a toolchain `lake` beside its `lean`, without `LAKE_OVERRIDE_LEAN` set to true, that is the
parent of the directory of the running `lake` (`Lake.findLakeLeanJointHome?`,
`Lake/Config/InstallPath.lean:334`), an absolute path. With that override, Lake detects the
installation instead from the inherited `LEAN_SYSROOT`, or else from the `lean` that `LEAN` or
`PATH` names (`Lake.findInstall?` and `Lake.findLeanInstall?`, `InstallPath.lean:371`); that
choice is the caller's, and `identifiedRoot` refuses one whose `lean` is another compiler.
Assumes: Lake never sets a variable of its own environment. It adds `LEAN_SYSROOT` only to the
environment it gives a child (`Lake.Env.baseVars`, read by `Lake.Workspace.augmentedEnvVars`,
`Lake/Config/Workspace.lean:417`), so a process that a target of `lake build` starts with
`IO.Process.output` and no `env` inherits Lake's own environment. Lake adds no `LEAN_SYSROOT` to
the `lean` it starts to compile a module either: `Lake.compileLeanModule` adds only `LEAN_PATH`
(its `rawProc`, `Lake/Build/Actions.lean:59`). So such a process has `LEAN_SYSROOT` only when Lake
itself has it, such as when Regula's `runLake` started Lake (`Regula.Toolchain.lakeChildEnv`) or the
user exported it. Otherwise a `lean` takes its own installation, whose `bin/lean` Lake ran by its
path, and another program takes the Elan toolchain.
Assumes: Elan's proxy sets `ELAN_TOOLCHAIN` to the toolchain it resolved and `ELAN_HOME` to its
home for the program it starts (`Toolchain::set_env`, `src/elan/toolchain.rs:353` of Elan 4.1.2),
so a Lake that Elan's `lake` proxy started, and each process that inherits its environment, names
the toolchain whose `lake` runs. `identifiedRoot` refuses one whose `lean` is another compiler. The
filesystem's resolution of the path is trusted. -/
def toolchainRoot : IO System.FilePath := do
  if let some root ← IO.getEnv "LEAN_SYSROOT" then
    let root := System.FilePath.mk root
    unless root.isAbsolute do
      throw <| IO.userError s!"the Lean toolchain is unknown: LEAN_SYSROOT is the relative path \
        {root}, not an absolute one"
    return ← IO.FS.realPath root
  if (← IO.appPath).fileStem == some "lean" then
    return ← IO.FS.realPath (← Lean.getBuildDir)
  let some toolchain ← IO.getEnv "ELAN_TOOLCHAIN"
    | throw <| IO.userError "the Lean toolchain is unknown: neither LEAN_SYSROOT nor \
        ELAN_TOOLCHAIN is set, and this program is not a `lean`; run it through Lake (lake exe, \
        lake env or lake lint), which sets LEAN_SYSROOT, or under a Lake that Elan started, \
        which sets ELAN_TOOLCHAIN"
  let some elan ← Lake.findElanInstall?
    | throw <| IO.userError s!"the Lean toolchain is unknown: LEAN_SYSROOT is unset and \
        ELAN_TOOLCHAIN is {toolchain}, but Elan's home is unknown: ELAN_HOME is unset, or ELAN \
        is empty"
  unless elan.home.isAbsolute do
    throw <| IO.userError s!"the Lean toolchain is unknown: ELAN_HOME is the relative path \
      {elan.home}, not an absolute one"
  IO.FS.realPath (elan.toolchainDir toolchain)

/-- `toolchainRoot`, accepted only once its `bin/lean`, run by that path without the inherited
`LEAN_PATH`, `LEAN_SRC_PATH` and `LEAN_SYSROOT`, prints exactly `version` and `commit` on their
own lines. A program that prints them is taken to be that compiler; process execution and the
installation's contents are trusted. -/
def identifiedRoot (version commit : String) : IO System.FilePath := do
  let root ← toolchainRoot
  let output ← IO.Process.output {
    cmd := (root / "bin" / "lean").toString, args := #["--stdin"]
    env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none), ("LEAN_SYSROOT", none)] }
    (some "#eval IO.println Lean.versionString\n#eval IO.println Lean.githash\n")
  unless output.exitCode == 0 && output.stdout == s!"{version}\n{commit}\n" do
    throw <| IO.userError
      "compiler capability: resolved compiler identity differs from this Regula build"
  return root

end Regula.CompilerObservation
