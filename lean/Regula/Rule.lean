module

public import Regula.Tables
public import Regula.Verdict

public section

namespace Regula.Closed

open Lean (Name)

def logicalAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

def compilerAxioms : List Name := []

def nativeProofAxiom : Name → Bool
  | .str (.str (.str _ "_native") _) _ => true
  | _ => false

def loopConstructs : List Name := [``Lean.Loop.mk, ``repeatM]

inductive Subject where
  | constant (name module : Name)
  | module (name : Name)

def Subject.name : Subject → Name
  | .constant name _ => name
  | .module name => name

structure Guidance where
  text : String
  nonblank : text.toList.head?.any (!·.isWhitespace) = true

namespace Guidance

theorem text_ne_empty (g : Guidance) : g.text ≠ "" := by
  intro h
  have hn := g.nonblank
  rw [h] at hn
  simp at hn

theorem exists_nonwhitespace (g : Guidance) : ∃ c ∈ g.text.toList, c.isWhitespace = false := by
  have hn := g.nonblank
  cases hl : g.text.toList with
  | nil => simp [hl] at hn
  | cons c cs =>
    rw [hl] at hn
    simp only [List.head?_cons, Option.any_some, Bool.not_eq_true'] at hn
    exact ⟨c, by simp, hn⟩

end Guidance

structure Violation where
  subject : Subject
  detail : String
  guidance : Guidance

def violation (d : Decl) (detail : String) (guidance : Guidance) : Violation :=
  { subject := .constant d.name d.module, detail, guidance }

structure Rule where
  spelling : String
  check : ∀ {i : Input}, Tables i → List Violation

structure Finding where
  rule : String
  subject : Subject
  detail : String
  guidance : Guidance

def Finding.of (r : Rule) (v : Violation) : Finding :=
  { rule := r.spelling, subject := v.subject, detail := v.detail, guidance := v.guidance }

namespace Tables

variable {i : Input} (t : Tables i)

def known (a : Name) : Bool :=
  logicalAxioms.contains a && (t.index[a]?).any (·.inToolchain)

def admits : Profile → Name → Bool
  | .kernelOnly, _ => false
  | .choiceFree, a => t.known a && (a == ``propext || a == ``Quot.sound)
  | .standardLogical, a => t.known a

def ctorIdxPair (ind : Name) (defDecl implDecl : Decl) : Bool :=
  let defName := Name.str ind "ctorIdx"
  let implName := Name.str defName "_impl"
  (t.index[`getObjTagNat]?).any (·.inToolchain) &&
  (t.index[ind]?).any (fun indDecl =>
    indDecl.kind == .inductive &&
    indDecl.safety == .safe &&
    indDecl.module == defDecl.module) &&
  defDecl.name == defName &&
  defDecl.kind == .definition &&
  defDecl.safety == .safe &&
  defDecl.ctorIdxForm == .defn ind &&
  defDecl.implementedBy == some implName &&
  !defDecl.isExtern &&
  defDecl.initFn.isNone &&
  implDecl.name == implName &&
  implDecl.module == defDecl.module &&
  implDecl.kind == .definition &&
  implDecl.safety == .unsafe &&
  implDecl.ctorIdxForm == .impl ind &&
  implDecl.implementedBy.isNone &&
  !implDecl.isExtern &&
  implDecl.initFn.isNone

def ctorIdxDef (d : Decl) : Bool :=
  match d.ctorIdxForm with
  | .defn ind => (t.index[Name.str d.name "_impl"]?).any (t.ctorIdxPair ind d ·)
  | _ => false

def ctorIdxImpl (d : Decl) : Bool :=
  match d.ctorIdxForm with
  | .impl ind => (t.index[Name.str ind "ctorIdx"]?).any (t.ctorIdxPair ind · d)
  | _ => false

end Tables

inductive Report where
  | pass
  | fail (first : Finding) (rest : List Finding)
  | incomplete (why : String)

namespace Report

@[expose] def verdict : Report → Verdict
  | .pass => .pass
  | .fail _ _ => .fail
  | .incomplete _ => .incomplete

@[expose] def findings : Report → List Finding
  | .pass => []
  | .fail first rest => first :: rest
  | .incomplete _ => []

end Report

end Regula.Closed
