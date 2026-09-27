module

public meta import Regula.MaterialClaim
public meta import Regula.Findings
public meta import Lean.DocString
public meta import Lean.Elab.Import
public meta import RegulaPolicy.ModuleHeader

/-! # Documentation presence checks

Module-doc presence and position and header imports (RG5001), and explicitly selected
declaration-doc presence, using both of Lean's documentation formats, and presence of a
nonempty Intent section in each selected declaration's docstring. Presence is distinct from
adequacy and registration completeness, which remain semantic review obligations. -/

public meta section

namespace Regula.Linter.Documentation
open Lean

/-- Read current or imported metadata. Callers establish completed elaboration
and load imported server data before treating absence as a completed observation. -/
def modulePresent (env : Environment) (moduleName : Name) : Except String Bool := do
  if moduleName == env.mainModule then
    return !(Lean.getMainModuleDoc env).isEmpty ||
      !(Lean.getMainVersoModuleDocs env).snippets.isEmpty
  let some markdown := Lean.getModuleDoc? env moduleName
    | throw s!"module documentation ownership is unavailable: {moduleName}"
  let some verso := Lean.getVersoModuleDoc? env moduleName
    | throw s!"Verso module documentation ownership is unavailable: {moduleName}"
  return !markdown.isEmpty || !verso.isEmpty

/-- Selector uses actual persistent registration and Lean's private-name convention. -/
def selected (env : Environment) (name : Name) : Bool :=
  materialClaimAttribute.hasTag env name && !Lean.isPrivateName name

/-- The executed material-documentation classification of a declaration. An inherited or
Verso docstring counts according to Lean's own lookup (`findDocString?`); the proved
`RegulaPolicy.materialDocumentationFailure` decides the missing docstring (RG5002) or a
docstring without a nonempty Intent section (RG5003). -/
def declarationFailure (env : Environment) (name : Name) :
    IO (Option RegulaPolicy.MaterialDocumentationFailure) := do
  return RegulaPolicy.materialDocumentationFailure (← Lean.findDocString? env name)

/-- The header facts RG5001 decides, read from a module's source text with Lean's own parser:
whether the first command after the header is a module docstring, and the header's imports in
source order (`HeaderSyntax.imports` without Lean's implicit `Init`). The first command is parsed
once, with the parser tables of `env`, which contains every syntax the module's imports declare;
a first command that does not parse is not a module docstring. -/
def headerFacts (env : Environment) (source fileName : String) :
    IO (Bool × List RegulaPolicy.ModuleHeader.ImportSpec) := do
  let inputCtx := Parser.mkInputContext source fileName
  let (header, state, messages) ← Parser.parseHeader inputCtx
  if messages.hasErrors then
    throw <| IO.userError s!"module-header: the header of {fileName} does not parse"
  let imports := (Elab.HeaderSyntax.imports header (includeInit := false)).toList.map
    fun i => (⟨i.module, i.importAll, i.isExported, i.isMeta⟩ : RegulaPolicy.ModuleHeader.ImportSpec)
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  let first := (Parser.andthenFn Parser.whitespace Parser.topLevelCommandParserFn).run inputCtx
    pmctx (Parser.getTokenTable env)
    { cache := Parser.initCacheForInput source, pos := state.pos }
  let documentationFirst := first.errorMsg.isNone && !first.stxStack.isEmpty &&
    first.stxStack.back.isOfKind ``Parser.Command.moduleDoc
  return (documentationFirst, imports)

/-- The RG5001 observation of one module: the module documentation Lean recorded and the header
facts of the module's source. -/
def moduleObservation (env : Environment) (moduleName : Name) (source fileName : String) :
    IO RegulaPolicy.ModuleHeader.Observation := do
  let documented ← IO.ofExcept <| modulePresent env moduleName
  let (documentationFirst, imports) ← headerFacts env source fileName
  return { documented, documentationFirst, imports }

/-- The finding detail of one RG5001 failure. -/
def failureDetail : RegulaPolicy.ModuleHeader.Failure → String
  | .missingDocumentation =>
    "module-documentation: add a module doc comment describing this module"
  | .misplacedDocumentation =>
    "module-documentation: make the module docstring the first command after the imports, " ++
      "before any `public section`"
  | .repeatedImport spec =>
    s!"module-documentation: remove the repeated import of `{spec.module}` with the same modifiers"

/-- The module's findings: one for each failure the proved decision
`RegulaPolicy.ModuleHeader.failures` reports, attributed to the module. -/
def moduleFindings (moduleName : Name) (observation : RegulaPolicy.ModuleHeader.Observation)
    (mode : EvidenceMode) (claim : Option String) : Except String (Array Finding) :=
  (RegulaPolicy.ModuleHeader.failures observation).toArray.mapM fun failure => do
    return ⟨.moduleDocumentation, ← makeDiagnostic .moduleDocumentation
      ⟨moduleName.toString, failureDetail failure⟩ (.module moduleName) mode claim .violation⟩

/-- Only explicitly registered public declarations receive these obligations. -/
def declarationFinding (env : Environment) (decl : RegulaPolicy.Declaration)
    (snapshot : Option SourceSnapshot) (mode : EvidenceMode) : IO (Option Finding) := do
  if !selected env decl.name then return none
  let some failure ← declarationFailure env decl.name | return none
  let location ← IO.ofExcept <| Findings.declarationLocation decl snapshot
  return some (← IO.ofExcept <| Findings.declarationFinding (ruleForMaterialDocumentation failure)
    decl.name (materialDocumentationDetail failure) location mode none)

end Regula.Linter.Documentation
