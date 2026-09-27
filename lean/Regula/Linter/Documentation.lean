module

public meta import Regula.MaterialClaim
public meta import Regula.Findings
public meta import Lean.DocString

/-! # Documentation presence checks

Module-doc and explicitly selected declaration-doc presence, using both of
Lean's documentation formats, and presence of a nonempty Intent section in each selected
declaration's docstring. Presence is distinct from adequacy and registration
completeness, which remain semantic review obligations. -/

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

/-- The source-free module condition carries honest module attribution. -/
def moduleFinding (env : Environment) (moduleName : Name) (mode : EvidenceMode) :
    Except String (Option Finding) := do
  if ← modulePresent env moduleName then return none
  return some ⟨.moduleDocumentation, ← makeDiagnostic .moduleDocumentation
    ⟨moduleName.toString, "module-documentation: add a module doc comment describing this module"⟩
    (.module moduleName) mode none .violation⟩

/-- Only explicitly registered public declarations receive these obligations. -/
def declarationFinding (env : Environment) (decl : RegulaPolicy.Declaration)
    (snapshot : Option SourceSnapshot) (mode : EvidenceMode) : IO (Option Finding) := do
  if !selected env decl.name then return none
  let some failure ← declarationFailure env decl.name | return none
  let location ← IO.ofExcept <| Findings.declarationLocation decl snapshot
  return some (← IO.ofExcept <| Findings.declarationFinding (ruleForMaterialDocumentation failure)
    decl.name (materialDocumentationDetail failure) location mode none)

end Regula.Linter.Documentation
