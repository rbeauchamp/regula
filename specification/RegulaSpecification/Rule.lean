module

public import Regula.Rule
public import RegulaSpecification.Witnesses
public import RegulaSpecification.Proofs.Tables
import all Regula.Rule

/-!
# What the statement of every rule shares

Each rule's statement is a module of its own below {lit}`Rules/`, which imports this module, the rule's own
check in the checker's package, and no other rule. A rule enters the specification's registry
({lit}`Rules.lean`) as a value of {lit}`Proved`: the rule that the checker runs, its violation predicate,
the proof that its check reports exactly the violations, its cases, and the proof of the kind of subject that
its violations carry. So no rule is registered without its statement, its proofs and its cases.

The lemmas here are the ones that more than one rule's proof uses.
-/

@[expose] public section

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

/-- A rule of the checker with its statement: the violation predicate over the specification's input, the
proof that the rule's check reports exactly its violations on every input and every value of its tables, the
cases that the rule's record needs, and the proof of the kind of subject that its violations carry. -/
structure Proved where
  /-- The rule that the checker runs. -/
  rule : Regula.Closed.Rule
  /-- What a violation of the rule is. -/
  Violates : Input → Name → Prop
  /-- The check reports exactly the violations. -/
  exact : ∀ {i : Regula.Closed.Input} (t : Regula.Closed.Tables i) (s : Name),
    s ∈ (rule.check t).map (·.subject.name) ↔ Violates (Link.toSpec i) s
  /-- The case that the rule must refuse, and the case that it must admit. -/
  cases : Witnessed Violates
  /-- Every violation of RG1013 has a module subject for a claimed module. Every violation of RG1011 has a
  constant subject carrying the name and the module of a declaration of a claimed module or, for its
  {attr}`@[csimp]` clause, the theorem of a claimed module's exported {attr}`@[csimp]` entry that no claimed
  module declares, with that claimed module. Every violation of another rule has a constant subject carrying
  the declaration's own name and module. -/
  subject : ∀ {i : Regula.Closed.Input} (t : Regula.Closed.Tables i), ∀ v ∈ rule.check t,
    (rule.spelling ∉ ["RG1011", "RG1013"] ∧ ∃ d ∈ i.decls, v.subject = .constant d.name d.module) ∨
      (rule.spelling = "RG1013" ∧ ∃ m ∈ i.modules, v.subject = .module m) ∨
      (rule.spelling = "RG1011" ∧
        ((∃ d ∈ i.decls, d.module ∈ i.modules ∧ v.subject = .constant d.name d.module) ∨
          ∃ e ∈ i.csimps, e.module ∈ i.modules ∧ e.thm ∉ i.claimedConstants ∧
            v.subject = .constant e.thm e.module))

namespace Proved

open Link

variable (p : Proved)

/-- The rule's check over the specification's input. -/
def checker : Checker Input Name := fun s =>
  (p.rule.check (ofAdmitted s).tables).map (·.subject.name)

theorem meets (rule : String) : (ruleRecord rule p.Violates).Meets p.checker := by
  refine (meets_iff _).mpr fun s c => ?_
  have := p.exact (ofAdmitted s).tables c
  rwa [toSpec_ofAdmitted] at this

/-- The rule's own check reports the case it must refuse and does not report the case it must admit. So a
function that reports nothing, or everything, cannot be the one that runs. -/
theorem cases_hold :
    p.cases.bad ∈ p.checker ⟨p.cases.refused, p.cases.refused_wf⟩ ∧
      p.cases.fine ∉ p.checker ⟨p.cases.admitted, p.cases.admitted_wf⟩ := by
  have hf := (meets_iff _).mp (p.meets "")
  exact ⟨(hf _ _).mpr p.cases.bad_violates, fun h => p.cases.fine_admitted ((hf _ _).mp h)⟩

end Proved

namespace Link

variable {i : Regula.Closed.Input} (t : Regula.Closed.Tables i)

theorem mem_report {α : Type} {l : List α} {c : α → Bool} {g : α → Regula.Closed.Violation}
    {sub : α → Name} (hg : ∀ a, (g a).subject.name = sub a) (s : Name) :
    s ∈ (l.filterMap fun a => if c a then some (g a) else none).map (·.subject.name) ↔
      ∃ a ∈ l, c a = true ∧ sub a = s := by
  simp only [List.mem_map, List.mem_filterMap]
  constructor
  · rintro ⟨f, ⟨a, ha, hf⟩, rfl⟩
    split at hf
    · rename_i hc
      simp only [Option.some.injEq] at hf
      exact ⟨a, ha, hc, by rw [← hf, hg]⟩
    · simp at hf
  · rintro ⟨a, ha, hc, rfl⟩
    exact ⟨g a, ⟨a, ha, by simp [hc]⟩, hg a⟩

theorem mem_report_violation {α : Type} {l : List α} {c : α → Bool} {g : α → Regula.Closed.Violation}
    {v : Regula.Closed.Violation}
    (hv : v ∈ l.filterMap fun a => if c a then some (g a) else none) :
    ∃ a ∈ l, c a = true ∧ g a = v := by
  obtain ⟨a, ha, hf⟩ := List.mem_filterMap.mp hv
  split at hf
  · exact ⟨a, ha, ‹_›, Option.some.inj hf⟩
  · cases hf

theorem filter_nonempty {α : Type} {l : List α} {p : α → Bool} :
    (!(l.filter p).isEmpty) = true ↔ ∃ a ∈ l, p a = true := by
  simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem, List.mem_filter]

theorem nil_iff_no_subject (vs : List Regula.Closed.Violation) :
    vs = [] ↔ ∀ s, s ∉ vs.map (·.subject.name) := by
  cases vs with
  | nil => simp
  | cons v vs =>
    constructor
    · intro h
      cases h
    · intro h
      exact absurd (List.mem_cons_self ..) (h v.subject.name)

theorem known_iff (a : Name) :
    t.known a = true ↔ (toSpec i).Known a := by
  unfold Regula.Closed.Tables.known
  rw [Bool.and_eq_true, any_index_iff t]
  have hl : (Regula.Closed.logicalAxioms.contains a = true) ↔ a ∈ logicalAxioms := by
    simp [Regula.Closed.logicalAxioms, logicalAxioms]
  rw [hl]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨d, hd, hn, ht⟩
    exact ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, hn, ht⟩
  · rintro ⟨x, hx, hn, ht⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    exact ⟨d, hd, hn, ht⟩

theorem native_iff (a : Name) : Regula.Closed.nativeProofAxiom a = true ↔ NativeProofAxiom a := by
  constructor
  · intro h
    unfold Regula.Closed.nativeProofAxiom at h
    split at h
    · exact ⟨_, _, _, rfl⟩
    · simp at h
  · rintro ⟨p, t, s, rfl⟩
    simp [Regula.Closed.nativeProofAxiom]

theorem compiler_contains (a : Name) : Regula.Closed.compilerAxioms.contains a = false := by
  simp [Regula.Closed.compilerAxioms]

theorem not_mem_compiler (a : Name) : a ∉ compilerAxioms := by simp [compilerAxioms]

theorem kindDef_iff (b : Regula.Closed.Decl) :
    b.kind = .definition ↔ (decl b).kind = .definition := by
  cases hd : b.kind <;> simp [decl, constKind, hd]

theorem kindInd_iff (b : Regula.Closed.Decl) :
    b.kind = .inductive ↔ (decl b).kind = .inductive := by
  cases hd : b.kind <;> simp [decl, constKind, hd]

theorem safety_iff (b : Regula.Closed.Decl) (v : Regula.Closed.Safety) :
    b.safety = v ↔ (decl b).safety = safety v := by
  cases hd : b.safety <;> cases v <;> simp [decl, safety, hd]

theorem ctorIdxForm_iff (b : Regula.Closed.Decl) (v : Regula.Closed.CtorIdxForm) :
    b.ctorIdxForm = v ↔ (decl b).ctorIdxForm = ctorIdxForm v := by
  cases hd : b.ctorIdxForm <;> cases v <;> simp [decl, ctorIdxForm, hd]

theorem ctorIdxPair_iff (ind : Name) (defDecl implDecl : Regula.Closed.Decl) :
    t.ctorIdxPair ind defDecl implDecl = true ↔
      (toSpec i).CtorIdxPair ind (decl defDecl) (decl implDecl) := by
  unfold Regula.Closed.Tables.ctorIdxPair Input.CtorIdxPair
  have htag : (t.index[`getObjTagNat]?).any (·.inToolchain) = true ↔
      (∃ g ∈ (toSpec i).decls, g.name = `getObjTagNat ∧ g.inToolchain = true) := by
    rw [any_index_iff t]
    exact ⟨by rintro ⟨g, hg, hn, ht⟩; exact ⟨decl g, mem_decls.mpr ⟨g, hg, rfl⟩, hn, ht⟩,
     by rintro ⟨x, hx, hn, ht⟩; obtain ⟨g, hg, rfl⟩ := mem_decls.mp hx; exact ⟨g, hg, hn, ht⟩⟩
  have hind : (t.index[ind]?).any (fun indDecl =>
      indDecl.kind == .inductive && indDecl.safety == .safe && indDecl.module == defDecl.module) = true ↔
      (∃ indDecl ∈ (toSpec i).decls, indDecl.name = ind ∧ indDecl.kind = .inductive ∧
        indDecl.safety = .safe ∧ indDecl.module = (decl defDecl).module) := by
    rw [any_index_iff t]
    constructor
    · rintro ⟨x, hx, hn, hp⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      exact ⟨decl x, mem_decls.mpr ⟨x, hx, rfl⟩, hn, (kindInd_iff x).mp hp.1.1,
        (safety_iff x .safe).mp hp.1.2, hp.2⟩
    · rintro ⟨x, hx, hn, hk, hs, hm⟩
      obtain ⟨y, hy, rfl⟩ := mem_decls.mp hx
      refine ⟨y, hy, hn, ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨(kindInd_iff y).mpr hk, (safety_iff y .safe).mpr hs⟩, hm⟩
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, Option.isNone_iff_eq_none,
    htag, hind, kindDef_iff, safety_iff, ctorIdxForm_iff, and_assoc]
  rfl

theorem ctorIdxDef_iff (d : Regula.Closed.Decl) :
    t.ctorIdxDef d = true ↔ (toSpec i).CtorIdxDef (decl d) := by
  unfold Regula.Closed.Tables.ctorIdxDef Input.CtorIdxDef
  cases hf : d.ctorIdxForm with
  | none =>
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro ind implDecl _ hp
    obtain ⟨_, _, _, _, _, hcf, _⟩ := hp
    simp [decl, ctorIdxForm, hf] at hcf
  | impl ind =>
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro ind' implDecl _ hp
    obtain ⟨_, _, _, _, _, hcf, _⟩ := hp
    simp [decl, ctorIdxForm, hf] at hcf
  | defn ind =>
    rw [any_index_iff t]
    constructor
    · rintro ⟨implDecl, himpl, _, hpair⟩
      exact ⟨ind, decl implDecl, mem_decls.mpr ⟨implDecl, himpl, rfl⟩,
        (ctorIdxPair_iff t ind d implDecl).mp hpair⟩
    · rintro ⟨ind', implSpec, himplSpec, hpair⟩
      obtain ⟨_, _, hdname, _, _, hcf, _, _, _, hiname, _⟩ := id hpair
      have hind : ind = ind' := by
        simp [decl, ctorIdxForm, hf] at hcf
        exact hcf
      subst hind
      obtain ⟨implDecl, himpl, rfl⟩ := mem_decls.mp himplSpec
      have hname : implDecl.name = Name.str d.name "_impl" := by
        change implDecl.name = Name.str (Name.str ind "ctorIdx") "_impl" at hiname
        change d.name = Name.str ind "ctorIdx" at hdname
        rw [hiname, hdname]
      exact ⟨implDecl, himpl, hname, (ctorIdxPair_iff t ind d implDecl).mpr hpair⟩

theorem ctorIdxImpl_iff (d : Regula.Closed.Decl) :
    t.ctorIdxImpl d = true ↔ (toSpec i).CtorIdxImpl (decl d) := by
  unfold Regula.Closed.Tables.ctorIdxImpl Input.CtorIdxImpl
  cases hf : d.ctorIdxForm with
  | none =>
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro ind defDecl _ hp
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hcf, _⟩ := hp
    simp [decl, ctorIdxForm, hf] at hcf
  | defn ind =>
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro ind' defDecl _ hp
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hcf, _⟩ := hp
    simp [decl, ctorIdxForm, hf] at hcf
  | impl ind =>
    rw [any_index_iff t]
    constructor
    · rintro ⟨defDecl, hdef, _, hpair⟩
      exact ⟨ind, decl defDecl, mem_decls.mpr ⟨defDecl, hdef, rfl⟩,
        (ctorIdxPair_iff t ind defDecl d).mp hpair⟩
    · rintro ⟨ind', defSpec, hdefSpec, hpair⟩
      obtain ⟨_, _, hdname, _, _, _, _, _, _, _, _, _, _, hcf, _⟩ := id hpair
      have hind : ind = ind' := by
        simp [decl, ctorIdxForm, hf] at hcf
        exact hcf
      subst hind
      obtain ⟨defDecl, hdef, rfl⟩ := mem_decls.mp hdefSpec
      exact ⟨defDecl, hdef, hdname, (ctorIdxPair_iff t ind defDecl d).mpr hpair⟩

end Link

end RegulaSpecification
