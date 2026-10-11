module

public import Lean.Environment
public import Lean.Util.Path

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
`LEAN_SYSROOT`, which must be an absolute path. Throws when `LEAN_SYSROOT` is unset or relative;
no `lean` is run to find the directory, so no program that `PATH` resolves takes part.
Assumes: Lake sets `LEAN_SYSROOT` for each program it starts (`lake exe`, `lake env`, `lake lint`)
to the installation it detected (`Lake.Env.baseVars`, `Lake/Config/Env.lean:302` of Lean v4.34.1),
which for a toolchain `lake` beside its `lean` is the parent of the directory of the running `lake`
(`Lake.findLakeLeanJointHome?`, `Lake/Config/InstallPath.lean:334`), an absolute path. The
filesystem's resolution of that path is trusted. -/
def toolchainRoot : IO System.FilePath := do
  let some root ← IO.getEnv "LEAN_SYSROOT"
    | throw <| IO.userError "the Lean toolchain is unknown: LEAN_SYSROOT is unset; run this \
        program through Lake (lake exe, lake env or lake lint), which sets it"
  let root := System.FilePath.mk root
  unless root.isAbsolute do
    throw <| IO.userError s!"the Lean toolchain is unknown: LEAN_SYSROOT is the relative path \
      {root}, not an absolute one"
  IO.FS.realPath root

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
