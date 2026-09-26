import VersoManual
import RegulaStandard
import RegulaCore.Standard

/-! Renders the standard alone. Rendering resolves every cross-reference and checklist-row
anchor, so a successful run is the standard's cross-reference check; the published copy is
rendered with the rest of the site by `regula-site`. Before rendering, every section the rule
registry cites (`Regula.Clause`) must be a part of the elaborated standard with the clause's tag
and exactly its heading, inside the chapter whose `file` is the clause's chapter. -/

open Verso.Doc Verso.Genre Manual

/-- `part` and every part below it. -/
def parts : Part Manual → List (Part Manual)
  | part@(.mk _ _ _ _ subParts) =>
    part :: subParts.toList.attach.flatMap fun ⟨sub, _⟩ => parts sub
decreasing_by
  have := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp ‹sub ∈ subParts.toList›)
  simp_wf
  omega

/-- The cited sections the elaborated standard `doc` does not contain as tagged and titled. -/
def missingClauses (doc : Part Manual) : List Regula.Clause :=
  Regula.Clause.all.filter fun c => !(parts doc).any fun chapter =>
    chapter.metadata.bind (·.file) == some c.chapter && (parts chapter).any fun cited =>
      cited.metadata.bind (·.tag) == some c.anchor && cited.titleString == c.heading

def main (args : List String) : IO UInt32 := do
  let missing := missingClauses (%doc RegulaStandard)
  unless missing.isEmpty do
    IO.eprintln s!"cited sections missing from the standard with their tag, heading and chapter: {missing.map (·.heading)}"
    return 1
  manualMain (%doc RegulaStandard) (options := args) (config := {
    emitTeX := false, emitHtmlSingle := .no, emitHtmlMulti := .immediately, htmlDepth := 1 })
