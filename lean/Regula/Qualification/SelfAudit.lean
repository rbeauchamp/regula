import Regula.Checker.Admission
import Regula.Checker.Lake
import Regula.Collect
import Regula.Linter.Documentation
import RegulaPolicy.Operational

/-! # Checker library self-audit

Operational self-audit of the checker's own excluded `Regula` library
(`./scripts/verify.sh diagnostics self-audit`; docs/guides/contributing.md).

The library is not a conforming proof surface, so the project audit excludes it. This
campaign applies the rules that do hold for operational code, per module of the library as
Lake discovers it: completed kernel admission of every owned safe declaration (RG2005), the
executed `RegulaPolicy.checked_operationalFailure` decision (RG1001–RG1005, RG1007) on the
observations the live linter's shared collector (`Regula.Collect.declaration`) constructs, and
the live linter's module-header (RG5001: docstring present and first, no repeated import) and
material-documentation presence predicates
(`Regula.Linter.Documentation`, RG5001–RG5003). Authored `unsafe`/`partial` declarations and
the pinned toolchain's Lake axioms that in-process Lake APIs reach are reported, never failed.

Each module is imported alone, because several executable roots of the library each define
`main` and cannot share one environment. Warning-free elaboration (RG2003) is the preceding
`lake build Regula` step of the same campaign. Trusted, not verified: Lean's import, kernel
replay and pretty-printer, the collector's observations, and the olean paths that identify a
toolchain module. -/
namespace Regula.Qualification.SelfAudit

open Lean System RegulaPolicy

/-- The excluded operational library this campaign audits. -/
def library : String := "Regula"

/-- The report claim label: the operational decision, never a conforming profile. -/
def claim : String := "operational"

/-- Observations of one module in its own imported environment. -/
structure ModuleObservation where
  /-- The observed module. -/
  «module» : Name
  /-- The collected record of every constant the module owns, in `ownedConstants` order. -/
  declarations : Array RegulaPolicy.Declaration
  /-- Owned declarations of this module that kernel replay admitted. -/
  admitted : Nat
  /-- Axioms reached from this module that a toolchain `Lake` module declares. -/
  toolchain : Array Name
  /-- The module's RG5001 header observation, read from its Lake source file. -/
  header : RegulaPolicy.ModuleHeader.Observation
  /-- Each public `@[regula_material]` declaration the module owns, with its RG5002/RG5003
  documentation failure, or `none` when its docstring passes. -/
  material : Array (Name × Option MaterialDocumentationFailure)

/-- Whether `owner`'s artifact is the pinned toolchain's own `Lake` module. -/
private def toolchainLakeModule (toolchainLib : FilePath) (owner : Name) : IO Bool := do
  unless owner.getRoot == `Lake do return false
  let expected := modToFilePath toolchainLib owner "olean"
  unless ← expected.pathExists do return false
  return (← IO.FS.realPath (← findOLean owner)) == (← IO.FS.realPath expected)

/-- Import one module, kernel-admit its owned declarations and collect its observations. -/
private unsafe def observe (toolchainLib : FilePath) (moduleName : Name) (source : FilePath) :
    IO (Except String ModuleObservation) := do
  Lean.enableInitializersExecution
  let env ← importModules #[{ module := moduleName, importAll := true }] {} 0
    (loadExts := true) (level := .private)
  let receipt ← match ← Checker.Admission.validate env #[moduleName] with
    | .ok receipt => pure receipt
    | .error failure => return .error failure.detail
  let admitted := (receipt.admitted.filter (·.1 == moduleName)).size
  let own := Regula.Probe.ownedConstants env [moduleName]
  let ctx : Elab.Command.Context := {
    fileName := "<operational-self-audit>", fileMap := FileMap.ofString "",
    snap? := none, cancelTk? := none }
  let collected ← EIO.toIO' <|
    (show Elab.Command.CommandElabM (Array RegulaPolicy.Declaration) from
      own.mapM fun (name, _) => Regula.Collect.declaration name .snapshot).run ctx
      |>.run (Elab.Command.mkState env)
  let declarations : Array RegulaPolicy.Declaration ← match collected with
    | .ok (declarations, _) => pure declarations
    | .error ex => return .error (← ex.toMessageData.toString)
  let mut toolchain : Array Name := #[]
  for d in declarations do
    for name in d.axioms do
      if standardLogicalAxiom name || toolchain.contains name then continue
      let some idx := env.getModuleIdxFor? name | continue
      let some owner := env.header.modules[idx.toNat]? | continue
      if ← toolchainLakeModule toolchainLib owner.module then
        toolchain := toolchain.push name
  let header ← Linter.Documentation.moduleObservation env moduleName
    (← IO.FS.readFile source) source.toString
  let mut material := #[]
  for (name, _) in own do
    if Linter.Documentation.selected env name then
      material := material.push (name, ← Linter.Documentation.declarationFailure env name)
  return .ok { «module» := moduleName, declarations, admitted, toolchain, header, material }

/-- Text of one violation finding at the declaration's module. -/
private def declarationText (id : RuleId) (name : Name) (detail : String) (moduleName : Name) :
    Except String String := do
  let ⟨_, finding⟩ ← Findings.declarationFinding id name detail (.module moduleName)
    .incrementalProject (some claim)
  return finding.text

/-- One module's region-free verdict, transported from its worker process as JSON. -/
structure ModuleResult where
  /-- The audited module's name. -/
  «module» : String
  /-- How many constants the module owns. -/
  declarations : Nat
  /-- How many of its owned declarations kernel replay admitted. -/
  admitted : Nat
  /-- How many of its declarations carry an executable-contract registration. -/
  contracts : Nat
  /-- The rendered text of every finding: module documentation, material documentation and
  declarations that `RegulaPolicy.operationalFailure` rejects. -/
  violations : Array String
  /-- Declarations that are `unsafe` or `partial` and have no unsafe-recursion base, reported
  rather than failed. -/
  unsafeDeclarations : Array String
  /-- The opaque bases of the module's `partial def`s, reported rather than failed. -/
  partialDefinitions : Array String
  /-- The admitted axioms, outside Standard-Logical, that a toolchain `Lake` module declares. -/
  toolchainAxioms : Array String
  /-- Non-proposition declarations whose axioms include one of those toolchain axioms. -/
  toolchainDependents : Array String
  deriving ToJson, FromJson

/-- Decide one module's observations with the axioms its own environment attributes to the
toolchain; every retained value is a freshly rendered string. -/
private def decide (o : ModuleObservation) : Except String ModuleResult := do
  let toolchain ← admitToolchainAxioms o.toolchain
  let mut violations : Array String := #[]
  for ⟨_, finding⟩ in ← Linter.Documentation.moduleFindings o.module o.header
      .incrementalProject (some claim) do
    violations := violations.push finding.text
  for (name, failure?) in o.material do
    if let some failure := failure? then
      violations := violations.push (← declarationText
        (ruleForMaterialDocumentation failure) name (materialDocumentationDetail failure) o.module)
  let mut unsafeDeclarations := #[]
  let mut partialDefinitions := #[]
  let mut dependents := #[]
  let mut contracts := 0
  for d in o.declarations do
    if d.executableContract.isSome then contracts := contracts + 1
    match d.unsafeRecBase with
    | none => if d.isUnsafe || d.isPartial then unsafeDeclarations :=
                                                 unsafeDeclarations.push d.name.toString
    | some base =>
      -- A `partial def` compiles to an opaque base implemented by this helper; safe
      -- structural or well-founded recursion keeps a definition base.
      if o.declarations.any (fun r => r.name == base && r.kind == .«opaque») then
        partialDefinitions := partialDefinitions.push base.toString
    if !d.isProp && d.axioms.any toolchain.names.contains then
      dependents := dependents.push d.name.toString
    if let some failure := checked_operationalFailure.run toolchain d then
      let id := ruleForFailure failure
      let extra := d.axioms.filter fun n => !standardLogicalAxiom n
      let detail := (descriptor id).applicability ++
        (if extra.isEmpty then "" else s!" (axioms outside Standard-Logical: {extra.toList})")
      violations := violations.push (← declarationText id d.name detail o.module)
  return ⟨o.module.toString, o.declarations.size, o.admitted, contracts, violations,
      unsafeDeclarations,
    partialDefinitions,
    toolchain.names.map toString, dependents⟩

/-- Worker: observe and decide exactly one module, printing only its JSON result. -/
unsafe def worker (moduleName source : String) : IO Unit := do
  Checker.initializeLeanSearchPath
  let observation ← IO.ofExcept (← observe (← getLibDir (← findSysroot)) moduleName.toName source)
  IO.println (toJson (← IO.ofExcept (decide observation))).compress

/-- Run the campaign: one fresh worker process per Lake-discovered module of the library.
Any violation or incomplete module refuses after the full report. -/
def check (jobs : Nat := 4) : IO Unit := do
  let repo ← Checker.repoRoot
  let inventory ← Checker.Lake.surfaceInventory repo
  let some info := inventory.libraries.find? (·.library == library)
    | throw <| IO.userError s!"self-audit: Lake discovered no root library {library}"
  if info.modules.isEmpty then
    throw <| IO.userError s!"self-audit: Lake discovered no modules of {library}"
  let self := (← IO.appPath).toString
  let outcomes ← Checker.mapWorkQueue jobs info.modules fun moduleName =>
    show IO (Except String ModuleResult) from do
    let result ← Checker.runProcess repo self
      #["--under-deadline", "self-audit-module", moduleName.toString,
        ((info.sources.find? (·.«module» == moduleName)).map (·.source.toString)).getD ""]
    if result.exitCode != 0 then
      return .error s!"{moduleName}: worker exit {result.exitCode}: {result.stderr.trimAscii}"
    match Json.parse result.stdout >>= fromJson? (α := ModuleResult) with
    | .ok r =>
      if r.module == moduleName.toString then return .ok r
      return .error s!"{moduleName}: worker answered for {r.module}"
    | .error e => return .error s!"{moduleName}: unreadable worker result: {e}"
  let results := outcomes.filterMap fun | .ok r => some r | .error _ => none
  let incomplete := outcomes.filterMap fun | .ok _ => none | .error e => some e
  let union (field : ModuleResult → Array String) : Array String :=
    (results.foldl (fun acc r => (field r).foldl
      (fun acc n => if acc.contains n then acc else acc.push n) acc) #[]).qsort (· < ·)
  let violations := results.flatMap (·.violations)
  for line in violations do IO.println line
  for line in incomplete do IO.println s!"INCOMPLETE {line}"
  let declarations := results.foldl (· + ·.declarations) 0
  let admitted := results.foldl (· + ·.admitted) 0
  let contracts := results.foldl (· + ·.contracts) 0
  let unsafeDeclarations := union (·.unsafeDeclarations)
  let partialDefinitions := union (·.partialDefinitions)
  let dependents := union (·.toolchainDependents)
  IO.println s!"operational self-audit of library {library}: {results.size}/{info.modules.size} \
    module(s), {declarations} declaration(s) inspected, {admitted} (every one neither unsafe nor \
    partial) kernel-admitted, {contracts} executable contract registration(s)"
  IO.println s!"reported, not failed: {unsafeDeclarations.size} unsafe \
    declaration(s): {unsafeDeclarations.toList}"
  IO.println s!"reported, not failed: {partialDefinitions.size} partial \
    definition(s): {partialDefinitions.toList}"
  IO.println s!"reported, not failed: {dependents.size} definition(s) reach toolchain Lake \
    axiom(s) {(union (·.toolchainAxioms)).toList}: {dependents.toList}"
  IO.println "trusted, not verified: Lean import and kernel replay, the collector's observations, \
    the toolchain artifact paths, worker processes and JSON transport, and every execution path \
    (the library's executables make no execution claim)"
  unless violations.isEmpty && incomplete.isEmpty do
    throw <| IO.userError s!"operational self-audit: FAIL ({violations.size} \
      violation(s), {incomplete.size} incomplete module(s))"
  IO.println "operational self-audit: PASS (operational claim only; not a conforming proof surface)"

end Regula.Qualification.SelfAudit
