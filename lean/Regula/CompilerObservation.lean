module

public import Lean.Environment
public import Lean.Util.Path

/-! # Isolated compiler capability observation

This operational collector imports only the selected compiler's Core into a separate
environment with extension loading disabled. It never inspects the audited environment
or changes the global search path. Every resolved Core dependency must come from the
compiler's own library directory. The preparation driver executes this same source
with the selected compiler; no compiled Regula dependency is required. It also names the
toolchain's installation directory (`toolchainRoot`), accepted only once its `lean` reports a
given version and commit (`identifiedRoot`). -/

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
is an error. Canonical-path resolution and compiler import are trusted IO observations. Each origin
is the file that the search path finds after the import, under the hypotheses of
`Regula.Probe.loadedModuleOrigins`: nothing that the lookup reads changes in between. -/
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

/-- The one line that `text` prints, as it is spelled: `text` less its final newline, when that line
is not empty and has no newline, carriage return or NUL. This is the same function as
`Regula.Filesystem.Construction.printedLine?` (`printedLine?_eq_printedLine?` in
`Regula.Checker.Common`): this source runs alone, with Lean's library only, so it holds its own copy
of the decoder. -/
@[expose] def printedLine? (text : String) : Option String :=
  match text.toList.reverse with
  | '\n' :: reversed =>
    if reversed ≠ [] ∧ ∀ c ∈ reversed, c ≠ '\n' ∧ c ≠ '\r' ∧ c ≠ '\x00' then
      some (String.ofList reversed.reverse)
    else none
  | _ => none

/-- The installation directory that `text`, the output of `lean --print-prefix`, prints: the line
that `printedLine?` reads, when it is an absolute path. This is the same function as
`Regula.Filesystem.Construction.printedPath?` (`printedPrefix?_eq_printedPath?`). -/
@[expose] def printedPrefix? (text : String) : Option System.FilePath :=
  match printedLine? text with
  | some line => if (System.FilePath.mk line).isAbsolute then some ⟨line⟩ else none
  | none => none

/-- The installation directory that the program `lean` prints for `--print-prefix`, read exactly:
`Lean.findSysroot`'s run of that program, with `IO.Process.run`, which throws its failure, and with
the printed prefix read by `printedPrefix?` (only the final newline is removed) in place of
`Lean.findSysroot`'s removal of the whitespace at its ends. Output that is not one absolute path
printed as a line is thrown.

Assumes: Lean v4.35.0 `lean --print-prefix` prints `getBuildDir` with `IO.println` and exits with 0
(`Lean/Shell.lean:471-473`): the parent of the real path of the directory of its executable
(`Lean/Util/Path.lean:85-86`, `Init/System/IO.lean:1305-1309`), an absolute path. -/
def printedSysroot (lean : String) : IO System.FilePath := do
  let out ← IO.Process.run { cmd := lean, args := #["--print-prefix"] }
  let some root := printedPrefix? out
    | throw <| IO.userError s!"{lean} --print-prefix printed {out.quote}, not one absolute path"
  return root

/-- The installation directory of the Lean toolchain, as `Lean.findSysroot` finds it, with the
printed prefix read exactly: the value of `LEAN_SYSROOT` as it is when it is set, else the prefix
that the `lean` which `PATH` resolves prints (`printedSysroot`). `Lean.findSysroot` removes the
whitespace at the ends of that prefix (`Lean/Util/Path.lean:180-187` of Lean v4.35.0), so an
installation directory whose name ends in a space would be read as another one. -/
def findSysroot : IO System.FilePath := do
  if let some root ← IO.getEnv "LEAN_SYSROOT" then return root
  printedSysroot "lean"

/-- The installation directory of the Lean toolchain, by its canonical path: `findSysroot`, the
value of `LEAN_SYSROOT` when it is set, else the prefix that the `lean` which `PATH` resolves
prints. A process that Lake starts (`lake exe`, `lake env`, `lake lint`) has `LEAN_SYSROOT` set, so
for it no program that `PATH` resolves takes part.
Assumes: Lake sets `LEAN_SYSROOT` for each program it starts to the absolute installation directory
it detected (`Lake.Env.baseVars`, `Lake/Config/Env.lean:302` of Lean v4.35.0). `identifiedRoot`
refuses an installation whose `lean` is another compiler. The filesystem's resolution of the path
is trusted. -/
def toolchainRoot : IO System.FilePath := do
  IO.FS.realPath (← findSysroot)

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
