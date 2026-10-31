import RegulaSpecification.CasesFoundation

/-!
# Lean-intent's obligations for the verdict

The record of the verdict meets O2, O2 before a run, O3 and O4, and O5 with equality (`gate_o5`): it
determines the verdict of each input. The checker that always passes and the checker that is always
incomplete each fail it. An input with a claim of no module is refused (`no_claim_refused`).
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
  simp [duplicated, withDecls, base, baseDecls, plain, toolchain, helperDecl, fDecl] at this

/-- A project that claims no module is refused, so an empty claim is no pass. -/
theorem no_claim_refused : ¬ ({ base with modules := [] } : Input).WellFormed :=
  fun h => h.claims rfl

/-- A project with a claimed module that the environment does not load is refused. -/
theorem unloaded_refused : ¬ ({ base with loads := [] } : Input).WellFormed := by
  intro h
  have := h.loaded `Good (by simp [base])
  simp at this

open Classical in
/-- A verdict function that meets the record. -/
noncomputable def verdictOf : Option Input → Verdict
  | none => .incomplete
  | some i => if i.WellFormed then (if AllHold i then .pass else .fail) else .incomplete

theorem verdictOf_meets : gateRecord.Meets verdictOf := by
  rw [gate_meets_iff]
  refine ⟨rfl, fun i hi => by simp [verdictOf, hi], fun i hi => ?_⟩
  by_cases hall : AllHold i <;> simp [verdictOf, hi, hall]

/-- The checker that always passes misses the build that Lean could not load. -/
theorem always_pass_fails : ¬ gateRecord.Meets (fun _ => .pass) := by
  rw [gate_meets_iff]
  exact fun h => absurd h.1 (by decide)

/-- The checker that is always incomplete refuses each well-formed input. -/
theorem always_incomplete_fails : ¬ gateRecord.Meets (fun _ => .incomplete) := by
  rw [gate_meets_iff]
  exact fun h => (h.2.2 base wf_base).1 rfl

theorem gate_adequate :
    O2 gateRecord ∧ O2Run gateRecord ∧ O3 gateRecord ∧ O4 gateRecord ∧ O5 gateRecord .eq := by
  refine ⟨?_, o2Run_of_meets verdictOf_meets, ?_, gate_o4, gate_o5⟩
  · rw [o2_correct]
    refine ⟨⟨verdictOf, by simp [gateRecord]⟩, ?_⟩
    intro p hp
    simp only [gateRecord, List.mem_singleton] at hp
    subst hp
    exact ⟨base, wf_base⟩
  · rw [o3_correct]
    intro p hp
    simp only [gateRecord, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨fun _ => .pass, by decide⟩
    · exact ⟨fun _ => .pass, fun h => absurd (h duplicated not_wf_duplicated) (by decide)⟩
    · exact ⟨fun _ => .incomplete, fun h => (h base wf_base).1 rfl⟩

end Witnesses

end RegulaSpecification
