import Regula.Checker.Common
import RegulaPolicy.Domain

/-!
# Compiler-path coverage qualification

Public-entrypoint qualification of compiler-derived execution coverage. Each
single-edge mutation gets independent imported source, compiled artifacts,
positive and fresh restored controls. The emitted-C check is a diagnostic of
reachable code on the pin, not proof of compiler or external-code correctness.
-/

namespace Regula.Checker.CompilerPaths

open Lean System

private structure Case where
  name : String
  body : String
  before : String
  after : String
  expected : Array String
  reason : String := "execution-trusted-boundary"
  project : Bool := false
  moduleSystem : Bool := false
  emittedSymbol : Option String := none
  importLean : Bool := false
  extraImports : Array String := #[]
  supportModule : String := "Support"
  positiveExpected : Array String := #[]
  absent : Array String := #[]

private def externalAttribute := "@[extern \"compiler_path_external\"] "

private def cases : Array Case := #[
  { name := "init-module-origin"
    supportModule := "Init.Adopter"
    body := "/-- The identity. -/\ndef target (n : Nat) := n\n/-- The successor, through `target`. \
      -/\ndef entry (n : Nat) := target n + 1\n"
    before := "def target", after := externalAttribute ++ "def target"
    expected := #["CompilerPath.target [external]", "module Init.Adopter"]
    positiveExpected := #["Nat.add [native-runtime]"]
    project := true },
  { name := "lean-module-origin"
    supportModule := "Lean.Adopter"
    extraImports := #["Std.Sync.Mutex", "Lean.Data.Name"]
    body := "/-- The identity, doubled. -/\ndef other (n : Nat) := n + n\n/-- The identity. -/\n" ++
      "def target (n : Nat) := n\n/-- Under a fresh lock, prints the length of `target`'s " ++
      "decimal spelling and a name and syntax comparison. -/\n" ++
      "def entry (n : Nat) : IO Unit := do\n  let mutex ← Std.BaseMutex.new\n  mutex.lock\n" ++
      "  IO.println (← #[toString (target n)].foldlM (fun acc s => pure (acc + s.length)) 0)\n" ++
      "  IO.println (Lean.Name.quickCmp `a `b == .lt && Lean.Syntax.structEq .missing .missing)\n"
    before := "def target", after := "@[implemented_by other] def target"
    expected := #["CompilerPath.target [runtime-replacement]", "module Lean.Adopter"]
    -- Real toolchain boundaries of `Init`, `Std` and `Lean` (the last resolved through the
    -- lookalike's symlinked `Lean` prefix): replacements, an unsafe implementation, an extern
    -- and a partial definition, each attributed to the toolchain.
    positiveExpected := #["Nat.repr [runtime-replacement] correspondence=trusted " ++
      "replacement=Nat.reprFast toolchain",
      "Array.foldlMUnsafe [unsafe-computation] correspondence=trusted toolchain",
      "Std.BaseMutex.lock [native-runtime] correspondence=trusted toolchain " ++
        "(module Std.Sync.Mutex)",
      "Lean.Name.quickCmp [runtime-replacement] correspondence=trusted " ++
        "replacement=_private.Lean.Data.Name.0.Lean.Name.quickCmpImpl toolchain " ++
        "(module Lean.Data.Name)",
      "Lean.Syntax.structEq [partial-computation] correspondence=trusted toolchain " ++
        "(module Init.Meta.Defs)",
      "Array.foldlMUnsafe.fold [unsafe-computation] correspondence=trusted toolchain"]
    -- `Array.foldlMUnsafe.fold`, reached above, passes the proof placeholder `lcProof`, an
    -- `unsafe axiom` of `Init.Prelude`. Whether a constant's type is a proposition is Lean's
    -- `Meta.isProp` observation, an external elaborator boundary: this qualifies it on the pin
    -- (without the probe's erasure guard, `lcProof` is a toolchain unsafe-computation boundary),
    -- and is not a proof that every proof-typed constant is erased.
    absent := #["boundary lcProof ["]
    project := true },
  { name := "imported"
    body := "/-- The identity. -/\ndef target (n : Nat) := n\n" ++
      "/-- The identity, compiled as `target`. -/\ndef reference (n : Nat) := n\n" ++
      "@[csimp] theorem optimize : reference = target := rfl\n" ++
      "/-- Runs `reference`. -/\ndef entry (n : Nat) := reference n\n"
    before := "def target", after := externalAttribute ++ "def target"
    expected := #["CompilerPath.target [external]", "compiler-callers="]
    project := true, emittedSymbol := some "compiler_path_external" },
  { name := "module-system"
    body := "/-- The identity. -/\ndef target (n : Nat) := n\n" ++
      "/-- The identity, compiled as `target`. -/\ndef reference (n : Nat) := n\n" ++
      "@[csimp] theorem optimize : reference = target := rfl\n" ++
      "/-- Runs `reference`. -/\ndef entry (n : Nat) := reference n\n"
    before := "def target", after := externalAttribute ++ "def target"
    expected := #["CompilerPath.target [external]", "compiler-callers="]
    project := true, moduleSystem := true },
  { name := "chained"
    body := "def target (n : Nat) := n\ndef middle (n : Nat) := target n\n" ++
      "@[csimp] theorem middle_eq : middle = target := rfl\n" ++
      "def reference (n : Nat) := middle n\n" ++
      "@[csimp] theorem reference_eq : reference = middle := rfl\n" ++
      "def entry (n : Nat) := reference n\n"
    before := "def target", after := externalAttribute ++ "def target"
    expected := #["replacement=CompilerPath.middle", "replacement=CompilerPath.target",
      "CompilerPath.target [external]"] },
  { name := "csimp-implemented-by"
    body := "def target (n : Nat) := n\n" ++
      "@[implemented_by target] def replacement (n : Nat) := n\n" ++
      "def reference (n : Nat) := n\n" ++
      "@[csimp] theorem optimize : reference = replacement := rfl\n" ++
      "def entry (n : Nat) := reference n\n"
    before := "def target", after := externalAttribute ++ "def target"
    expected := #["compiler-simplification", "runtime-replacement",
      "CompilerPath.target [external]"] },
  { name := "implemented-by-csimp"
    body := "def target (n : Nat) := n\ndef logical (n : Nat) := n\n" ++
      "@[csimp] theorem optimize : logical = target := rfl\n" ++
      "def replacement (n : Nat) := logical n\n" ++
      "@[implemented_by replacement] def reference (n : Nat) := n\n" ++
      "def entry (n : Nat) := reference n\n"
    before := "def target", after := externalAttribute ++ "def target"
    expected := #["compiler-simplification", "runtime-replacement",
      "CompilerPath.target [external]"] },
  { name := "partial-target"
    body := externalAttribute ++ "def ffi (n : Nat) := n\n" ++
      "partial def dangerous (n : Nat) : Nat := if n == 0 then ffi n else dangerous (n - 1)\n" ++
      "def safe (n : Nat) := n\n@[implemented_by safe] def replacement (n : Nat) := n\n" ++
      "def reference (n : Nat) := n\n" ++
      "@[csimp] theorem optimize : reference = replacement := rfl\n" ++
      "def entry (n : Nat) := reference n\n"
    before := "implemented_by safe", after := "implemented_by dangerous"
    expected := #["partial-computation", "CompilerPath.ffi [external]"] },
  -- The next two cases qualify the collector's record of a constant compiled to a `partial`
  -- definition, an observation of the compiler and environment that no theorem covers: the
  -- finding of the constant's boundary names the definition, which has no finding and no
  -- boundary line of its own (`RegulaPolicy.executionFindings`).
  { name := "partial-helper"
    body := "def loop (n : Nat) : Nat := n\ndef entry (n : Nat) := loop n\n"
    before := "def loop (n : Nat) : Nat := n"
    after := "partial def loop (n : Nat) : Nat := if n == 0 then 0 else loop (n - 1)"
    expected := #["reaches CompilerPath.loop (partial-computation), with its implementation " ++
        "CompilerPath.loop._unsafe_rec (partial-computation)",
      "implementation CompilerPath.loop._unsafe_rec [partial-computation]"]
    absent := #["reaches CompilerPath.loop._unsafe_rec",
      "boundary CompilerPath.loop._unsafe_rec ["] },
  -- The registration is written after Mathlib's `compile_inductive%`: a `partial` copy of the
  -- reference, and a `partial` constant of the equality's type as its `csimp` lemma. It is a
  -- copy of that construction, not a run of Mathlib's command. A second constant of the same
  -- type gives the reference a second record of the same trusted boundary, which is reported
  -- with the first: one finding and one counted boundary for the three records.
  { name := "csimp-partial-implementation"
    body := "def reference (n : Nat) := n\n-- registration\ndef entry (n : Nat) := reference n\n"
    before := "-- registration"
    after := "open Lean Elab Command in\nrun_cmd liftCoreM do\n" ++
      "  let reference ← getConstInfoDefn ``CompilerPath.reference\n" ++
      "  addAndCompile <| .mutualDefnDecl [{ reference with\n" ++
      "    name := `CompilerPath.implementation, hints := .opaque, safety := .partial,\n" ++
      "    all := [`CompilerPath.implementation] }]\n" ++
      "  for name in [`CompilerPath.registered, `CompilerPath.registeredAgain] do\n" ++
      "    addDecl <| .mutualDefnDecl [{\n" ++
      "      name, levelParams := [],\n" ++
      "      type := mkApp3 (mkConst ``Eq [.one]) reference.type\n" ++
      "        (mkConst ``CompilerPath.reference) (mkConst `CompilerPath.implementation),\n" ++
      "      value := mkConst name, hints := .opaque, safety := .partial, all := [name] }]\n" ++
      "  Compiler.CSimp.add `CompilerPath.registered .global"
    expected := #["reaches CompilerPath.reference (compiler-simplification), with its " ++
        "implementation CompilerPath.implementation (partial-computation)",
      "implementation CompilerPath.implementation [partial-computation]",
      "restated CompilerPath.reference [compiler-simplification]",
      "1 boundary(ies) (0 checked, 1 trusted)",
      "file audit: FAIL (1 violation(s), 0 incomplete finding(s))"]
    absent := #["reaches CompilerPath.implementation",
      "boundary CompilerPath.implementation ["]
    importLean := true },
  { name := "unsafe-target"
    body := externalAttribute ++ "def ffi (n : Nat) := n\n" ++
      "unsafe def dangerous (n : Nat) : Nat := ffi n\n" ++
      "def safe (n : Nat) := n\n@[implemented_by safe] def replacement (n : Nat) := n\n" ++
      "def reference (n : Nat) := n\n" ++
      "@[csimp] theorem optimize : reference = replacement := rfl\n" ++
      "def entry (n : Nat) := reference n\n"
    before := "implemented_by safe", after := "implemented_by dangerous"
    expected := #["unsafe-computation", "CompilerPath.ffi [external]"] },
  { name := "local-csimp"
    body := "def target (n : Nat) := n\ndef reference (n : Nat) := n\n" ++
      "theorem optimize : reference = target := rfl\nsection\n" ++
      "attribute [local csimp] optimize\ndef entry (n : Nat) := reference n\nend\n"
    before := "def target", after := externalAttribute ++ "def target"
    expected := #["CompilerPath.target [external]"] },
  { name := "overwritten-csimp"
    body := "def target (n : Nat) := n\ndef other (n : Nat) := n\n" ++
      "def reference (n : Nat) := n\n" ++
      "@[csimp] theorem optimize : reference = target := rfl\n" ++
      "def entry (n : Nat) := reference n\n" ++
      "@[csimp] theorem later : reference = other := rfl\n"
    before := "def target", after := externalAttribute ++ "def target"
    expected := #["replacement=CompilerPath.target", "CompilerPath.target [external]"] },
  { name := "proof-valued-csimp"
    body := "def target (n : Nat) := n + 1\ndef reference (n : Nat) := 1 + n\n" ++
      "set_option linter.defProp false in\n" ++
      "@[csimp] def optimize : reference = target := funext fun n => Nat.add_comm 1 n\n" ++
      "def entry (n : Nat) := reference n\n"
    before := "def target", after := externalAttribute ++ "def target"
    expected := #["proved: CompilerPath.optimize", "CompilerPath.target [external]"] },
  { name := "overwritten-inlined-implementation"
    body := "@[inline] unsafe def old (n : Nat) := n + 1\ndef safe (n : Nat) := n\n" ++
      "@[implemented_by safe] def reference (n : Nat) := n\n" ++
      "def entry (n : Nat) := reference n\n" ++
      "attribute [implemented_by safe] reference\n"
    before := "@[implemented_by safe]", after := "@[implemented_by old]"
    expected := #["replacement=CompilerPath.old", "CompilerPath.old [unsafe-computation]"] },
  { name := "replacement-cycle"
    body := "def left (n : Nat) := n\ndef right (n : Nat) := n\n" ++
      "@[csimp] theorem forward : left = right := rfl\n" ++
      "theorem backward : right = left := rfl\n" ++
      "-- reverse registration\ndef entry (n : Nat) := left n\n"
    before := "-- reverse registration", after := "attribute [csimp] backward"
    expected := #["replacement-only cycle"], reason := "execution-unresolved" },
  { name := "unsupported-history-evaluator"
    body := "def safe (n : Nat) := n\n@[implemented_by safe] def reference (n : Nat) := n\n" ++
      "-- source metaprogram\ndef entry (n : Nat) := reference n\n"
    before := "-- source metaprogram", after := "run_cmd pure ()"
    expected := #["unsupported replacement-history evaluators"], reason := "execution-unresolved"
    importLean := true }
]

private def reasons (output : String) : Array String := Id.run do
  let mut found := #[]
  for line in outputLines output do
    if let _ :: suffix :: _ := line.splitOn "VIOLATION[" then
      if let some reason := (suffix.splitOn "]").head? then
        if !found.contains reason then found := found.push reason
    else
      let line := line.trimAscii.toString
      if line.startsWith "[" && !line.startsWith "[OK]" then
        let reason := ((line.drop 1).toString.splitOn "]").headD ""
        if !found.contains reason then found := found.push reason
  return found

/-- Number of independent mutation/restoration cases in this qualification. -/
def caseCount : Nat := cases.size

/-- One fresh phase. `Support` is imported rather than owned by the file audit;
its unrelated unsafe declarations cannot mask the intended execution failure. -/
private def phase (repo scratch : FilePath) (test : Case) (negative : Bool) : IO
    (Array String) := do
  let body := if negative then test.body.replace test.before test.after else test.body
  if negative && body == test.body then return #[s!"{test.name}: mutation anchor missing"]
  let header := (if test.moduleSystem then "module\npublic import Init\n"
    else if test.importLean then "import Lean\n" else "import Init\n") ++
    String.join (test.extraImports.toList.map fun name => s!"import {name}\n")
  let supportName := test.supportModule.toName
  let supportPath := Lean.modToFilePath scratch supportName "lean"
  if let some parent := supportPath.parent then IO.FS.createDirAll parent
  -- The module docstring is the first command after the imports (RG5001).
  IO.FS.writeFile supportPath (header ++
    "/-! Imported execution-path qualification support. -/\n" ++
    (if test.moduleSystem then "@[expose] public section\n" else "") ++
    "namespace CompilerPath\n" ++ body ++ "end CompilerPath\n")
  IO.FS.writeFile (scratch / "Wrapper.lean")
    s!"import {test.supportModule}\n/-! Execution-path qualification consumer. -/\n/-- Runs the \
      imported entry. -/\ndef callsImported (n : Nat) := CompilerPath.entry n\n"
  IO.FS.writeFile (scratch / "lean-toolchain") (← IO.FS.readFile (repo / "lean-toolchain"))
  -- `linter.missingDocs` goes on each claimed library (RG2006): the support library is
  -- claimed only in the project cases.
  let supportOptions := if test.project then "leanOptions.linter.missingDocs = true\n" else ""
  IO.FS.writeFile (scratch / "lakefile.toml")
    s!"name = \"compiler_path_control\"\n[leanOptions]\nautoImplicit = false\nrelaxedAutoImplicit \
      = false\n[[lean_lib]]\nname = \"{test.supportModule}\"\n{supportOptions}[[lean_lib]]\nname = \
      \"Wrapper\"\nleanOptions.linter.missingDocs = true\n"
  -- Resolve configuration before the checker captures its immutable source
  -- binding. A later first Lake invocation would otherwise create the manifest
  -- inside the checked interval, correctly invalidating that binding.
  let configured ← runProcess scratch "lake" #["update"]
  if !configured.succeeded then
    return #[s!"{test.name}: configuration setup failed:\n{configured.output}"]
  -- Lean resolves an entire module prefix from one search directory. Supply the unchanged
  -- toolchain artifacts of the lookalike's root (`Init` or `Lean`) by symlink alongside the
  -- isolated adopter module; never write into the actual toolchain. Each phase starts in a
  -- new scratch tree, including the restored control.
  let lookalikeRoot := supportName.getRoot
  let lookalike := decide (RegulaPolicy.ToolchainRoot lookalikeRoot)
  if lookalike then
    let toolchainLib ← Lean.getLibDir (← Lean.findSysroot)
    let output := scratch / ".lake" / "build" / "lib" / "lean"
    let prefixDirectory := lookalikeRoot.toString
    IO.FS.createDirAll (output / prefixDirectory)
    -- One `ln` per directory links every source under its own file name.
    let link (sources : Array FilePath) (directory : FilePath) := do
      unless sources.isEmpty do
        let result ← runProcess scratch "ln"
          (#["-s"] ++ sources.map (·.toString) ++ #[directory.toString])
        if !result.succeeded then
          throw <| IO.userError s!"could not expose toolchain control: {result.output}"
    link (((← toolchainLib.readDir).filter
      (·.fileName.startsWith s!"{prefixDirectory}.")).map (·.path)) output
    link ((← (toolchainLib / prefixDirectory).readDir).map (·.path)) (output / prefixDirectory)
  IO.FS.writeFile (scratch / "foundation_manifest.json")
    ("{\"schema-version\":2,\"surfaces\":[{\"library\":\"Wrapper\",\"claim\":\"standard-logical\","
        ++
      "\"execution\":\"checked\",\"rationale\":\"imported compiler control\"}]," ++
      "\"excluded-libraries\":[{\"library\":\"" ++ test.supportModule ++
          "\",\"rationale\":\"isolated imported control\"}]," ++
      "\"excluded-executables\":[]}")
  let binary := (repo / ".lake" / "build" / "bin" / "axiomGate").toString
  let check (result : ProcessResult) : Array String := Id.run do
    if negative then
      if result.succeeded || reasons result.output != #[test.reason] then
        return #[s!"{test.name}: expected only {test.reason}:\n{result.output}"]
      if let some missing := test.expected.find? (!result.output.contains ·) then
        return #[s!"{test.name}: missing {missing}:\n{result.output}"]
    else
      if !result.succeeded then return #[s!"{test.name}: positive failed:\n{result.output}"]
      if let some missing := test.positiveExpected.find? (!result.output.contains ·) then
        return #[s!"{test.name}: positive missing {missing}:\n{result.output}"]
    if let some present := test.absent.find? (result.output.contains ·) then
      return #[s!"{test.name}: unexpectedly reported {present}:\n{result.output}"]
    return #[]
  let mut failures := check
      (← runProcess scratch binary
          #["--file", "Wrapper.lean", "--execution", "checked", "--verbose"])
  if negative then
    if let some symbol := test.emittedSymbol then
      let cFile := scratch / "wrapper.c"
      let compiled ← runProcess scratch "lake"
          #["env", "lean", "-c", cFile.toString, "Wrapper.lean"]
      if !compiled.succeeded then
        failures :=
            failures.push s!"{test.name}: C diagnostic compilation failed:\n{compiled.output}"
      else if !(← IO.FS.readFile cFile).contains symbol then
        failures := failures.push s!"{test.name}: emitted C omitted diagnostic symbol {symbol}"
  if test.project then
    IO.FS.writeFile (scratch / "foundation_manifest.json")
      ("{\"schema-version\":2,\"surfaces\":[{\"library\":\"" ++ test.supportModule ++
          "\",\"claim\":\"standard-logical\"," ++
        (if lookalike then "\"execution\":\"checked\"," else "") ++
        "\"rationale\":\"reported \
          support\"},{\"library\":\"Wrapper\",\"claim\":\"standard-logical\"," ++
        "\"execution\":\"checked\",\"rationale\":\"checked consumer\"}]," ++
        "\"excluded-libraries\":[],\"excluded-executables\":[]}")
    -- Preserve the toolchain-only symlink overlay in this case. The claimed
    -- adopter sources are still built afresh in each independent phase.
    -- Boundary evidence lines are printed only in verbose mode.
    let args := (if lookalike then #["--incremental"] else #[]) ++ #["--verbose"]
    failures := failures ++ check (← runProcess scratch binary args)
  return failures

/-- One case: a positive, one mutation, and a separately rebuilt restoration, each in a scratch
tree of its own below `scratch`. -/
private def qualifyCase (repo scratch : FilePath) (test : Case) : IO (Array String) := do
  let mut failures := #[]
  for (name, negative) in [("positive", false), ("negative", true), ("restored", false)] do
    let result ← withScratch scratch s!"{test.name}-{name}" fun isolated =>
      phase repo isolated test negative
    failures := failures ++ result
  IO.println
      s!"self-test compiler paths: {test.name} completed (positive/mutation/fresh restoration)"
  (← IO.getStdout).flush
  return failures

/-- Every case's qualification, named after the case. Each writes only below its own scratch
trees and reads only the checker's built output in `repo`, so a caller may run them in any
order or concurrently. The enclosing caller owns and removes all scratch artifacts. -/
def qualifications (repo scratch : FilePath) : Array (String × IO (Array String)) :=
  cases.map fun test => (test.name, qualifyCase repo scratch test)

/-- Every case pays for a positive, one mutation, and a separately rebuilt
restoration. The enclosing caller owns and removes all scratch artifacts. -/
def qualify (repo scratch : FilePath) : IO (Array String) := do
  let mut failures := #[]
  for (_, run) in qualifications repo scratch do
    failures := failures ++ (← run)
  return failures

end Regula.Checker.CompilerPaths
