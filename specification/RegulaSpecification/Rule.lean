import Regula.Rule
import RegulaSpecification.Witnesses
import RegulaSpecification.Proofs.Tables

/-!
# What the statement of every rule shares

Each rule's statement is a module of its own below {lit}`Rules/`, which imports this module, the rule's own
check in the checker's package, and no other rule. A rule enters the specification's registry
({lit}`Rules.lean`) as a value of {lit}`Proved`: the rule that the checker runs, its violation predicate,
the proof that its check reports exactly the violations, and its cases. So no rule is registered without its
statement, its proof and its cases.

The lemmas here are the ones that more than one rule's proof uses.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

/-- A rule of the checker with its statement: the violation predicate over the specification's input, the
proof that the rule's check reports exactly its violations on every input and every value of its tables, and the
cases that the rule's record needs. -/
structure Proved where
  /-- The rule that the checker runs. -/
  rule : Regula.Closed.Rule
  /-- What a violation of the rule is. -/
  Violates : Input → Name → Prop
  /-- The check reports exactly the violations. -/
  exact : ∀ {i : Regula.Closed.Input} (t : Regula.Closed.Tables i) (s : Name),
    s ∈ (rule.check t).map (·.subject) ↔ Violates (Link.toSpec i) s
  /-- The case that the rule must refuse, and the case that it must admit. -/
  cases : Witnessed Violates

namespace Proved

open Link

variable (p : Proved)

/-- The rule's check over the specification's input. -/
def checker : Checker Input Name := fun s =>
  (p.rule.check (ofAdmitted s).tables).map (·.subject)

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
    {sub : α → Name} (hg : ∀ a, (g a).subject = sub a) (s : Name) :
    s ∈ (l.filterMap fun a => if c a then some (g a) else none).map (·.subject) ↔
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

theorem filter_nonempty {α : Type} {l : List α} {p : α → Bool} :
    (!(l.filter p).isEmpty) = true ↔ ∃ a ∈ l, p a = true := by
  simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem, List.mem_filter]

theorem nil_iff_no_subject (vs : List Regula.Closed.Violation) :
    vs = [] ↔ ∀ s, s ∉ vs.map (·.subject) := by
  cases vs with
  | nil => simp
  | cons v vs =>
    constructor
    · intro h
      cases h
    · intro h
      exact absurd (List.mem_cons_self ..) (h v.subject)

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

end Link

end RegulaSpecification
