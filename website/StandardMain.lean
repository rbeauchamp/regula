import VersoManual
import RegulaRender
import RegulaStandard
import Regula.TaskManagerCheck
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

/-- The configuration of the standard's render, before its command-line options. -/
def standardConfig : RenderConfig :=
  { emitTeX := false, emitHtmlSingle := .no, emitHtmlMulti := .immediately, htmlDepth := 1 }

/-- Render the standard alone on Verso's command-line options `args` and the configuration
`standardConfig`, which its refusals read them with too (`refuseStandard`), after requiring every
cited section (`missingClauses`). When a cited section is missing, it refuses the run before Verso
starts: it prints the missing sections, moves aside each destination that the arguments name for a
render with `standardConfig` (`RegulaRender.refuse`), and returns 1. -/
def renderStandard (args : List String) : IO UInt32 := do
  let missing := missingClauses (%doc RegulaStandard)
  unless missing.isEmpty do
    IO.eprintln s!"cited sections missing from the standard with their tag, heading and chapter: {missing.map (·.heading)}"
    return (← RegulaRender.refuse "regula-standard" standardConfig args)
  manualMain (%doc RegulaStandard) (options := args) (config := standardConfig)

/-- The refusal of the renderer in a process without Lean's task manager
(`Regula.TaskManager.guard`): it moves aside each destination that the arguments name for a render
with `standardConfig` (`RegulaRender.refuse`), and returns 1. For the reason that the guard gives
before each run (`Regula.TaskManager.startedReason`), it moves nothing and returns 1: a run that
Verso starts keeps Verso's write behaviour, and a resumed render reads the saved state of an earlier
one. -/
def refuseStandard (reason : String) (args : List String) : IO UInt32 :=
  if reason == Regula.TaskManager.startedReason then pure 1
  else RegulaRender.refuse "regula-standard" standardConfig args

/-- `renderStandard` on the command-line arguments. A process without Lean's task manager is
refused before rendering starts (`Regula.TaskManager.guard`), and so is a standard that lacks a
cited section (`renderStandard`): each refusal moves aside the destinations that the arguments name
(`RegulaRender.refuse`) and returns 1. -/
def main : List String → IO UInt32 :=
  Regula.TaskManager.guard "regula-standard" refuseStandard renderStandard

-- A program that needs Lean's task manager starts through its guard (`Regula.TaskManager.guard`),
-- and its refusal needs none: the build of this module fails otherwise
-- (`Regula.TaskManagerCheck.checkProgram`).
run_cmd Regula.TaskManagerCheck.checkProgram
