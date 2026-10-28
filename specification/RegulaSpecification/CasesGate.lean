import RegulaSpecification.CasesExecution

/-!
# lean-intent's obligations for the verdict

The record of the verdict meets O2, O2 before a run, O3 and O4, and O5 with equality
(`gate_o5`): it determines the verdict of each input. The checker that always passes and the
checker that is always incomplete each fail it. A bundle with no environment, or with a claim of
no target, is refused (`no_claim_refused`).
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Witnesses

/-- An input the admission refuses: two constants with one name. -/
def duplicated : Input := withDecls [plain `Good.t `Good .theorem []]

theorem not_wf_duplicated : ¬ duplicated.WellFormed := by
  intro h
  have := h.unique
  simp [duplicated, withDecls, base, baseDecls, plain, toolchain, helperDecl] at this

/-- The compliant project, loaded in one environment. -/
def baseBundle : Bundle := ⟨[base]⟩

theorem wf_baseBundle : baseBundle.WellFormed where
  nonempty := by simp [baseBundle]
  each i hi := by
    simp only [baseBundle, List.mem_singleton] at hi
    subst hi
    exact wf_base
  oneProject i hi j hj := by
    simp only [baseBundle, List.mem_singleton] at hi hj
    subst hi hj
    exact ⟨rfl, rfl, rfl⟩
  covered i hi t ht m hm := by
    simp only [baseBundle, List.mem_singleton] at hi
    subst hi
    refine ⟨base, by simp [baseBundle], ?_⟩
    simp only [base, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp at hm <;> simp [base, hm]
  claims := ⟨base, by simp [baseBundle], `Good, .choiceFree, .report, by simp [base]⟩

/-- A bundle with an environment that the admission refuses. -/
def duplicatedBundle : Bundle := ⟨[duplicated]⟩

theorem not_wf_duplicatedBundle : ¬ duplicatedBundle.WellFormed :=
  fun h => not_wf_duplicated (h.each duplicated (by simp [duplicatedBundle]))

/-- A project whose claim excludes each target is refused, so an empty claim is no pass. -/
theorem no_claim_refused :
    ¬ (⟨[{ base with manifest := [⟨`Good, .excluded⟩, ⟨`app, .excluded⟩] }]⟩ : Bundle).WellFormed := by
  rintro ⟨-, -, -, -, i, hi, t, p, e, he⟩
  simp only [List.mem_singleton] at hi
  subst hi
  simp at he

open Classical in
/-- A verdict function that meets the record. -/
noncomputable def verdictOf (a : Allowlists) : Option Bundle → Verdict
  | none => .incomplete
  | some b => if b.WellFormed then (if b.AllHold a then .pass else .fail) else .incomplete

theorem verdictOf_meets (a : Allowlists) : (gateRecord a).Meets (verdictOf a) := by
  rw [gate_meets_iff]
  refine ⟨rfl, fun b hb => by simp [verdictOf, hb], fun b hb => ?_⟩
  by_cases hall : b.AllHold a <;> simp [verdictOf, hb, hall]

/-- The checker that always passes misses the build that Lean could not load. -/
theorem always_pass_fails (a : Allowlists) : ¬ (gateRecord a).Meets (fun _ => .pass) := by
  rw [gate_meets_iff]
  exact fun h => absurd h.1 (by decide)

/-- The checker that is always incomplete refuses each well-formed input. -/
theorem always_incomplete_fails (a : Allowlists) :
    ¬ (gateRecord a).Meets (fun _ => .incomplete) := by
  rw [gate_meets_iff]
  exact fun h => (h.2.2 baseBundle wf_baseBundle).1 rfl

theorem gate_adequate (a : Allowlists) :
    O2 (gateRecord a) ∧ O2Run (gateRecord a) ∧ O3 (gateRecord a) ∧ O4 (gateRecord a) ∧
      O5 (gateRecord a) .eq := by
  refine ⟨?_, o2Run_of_meets (verdictOf_meets a), ?_, gate_o4 a, gate_o5 a⟩
  · rw [o2_correct]
    refine ⟨⟨verdictOf a, by simp [gateRecord]⟩, ?_⟩
    intro p hp
    simp only [gateRecord, List.mem_singleton] at hp
    subst hp
    exact ⟨baseBundle, wf_baseBundle⟩
  · rw [o3_correct]
    intro p hp
    simp only [gateRecord, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨fun _ => .pass, by decide⟩
    · exact ⟨fun _ => .pass,
        fun h => absurd (h duplicatedBundle not_wf_duplicatedBundle) (by decide)⟩
    · exact ⟨fun _ => .incomplete, fun h => (h baseBundle wf_baseBundle).1 rfl⟩

end Witnesses

end RegulaSpecification
