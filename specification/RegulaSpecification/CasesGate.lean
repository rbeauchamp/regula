/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.CasesFoundation

/-!
# Lean-intent's obligations for the verdict

The record of the verdict meets O2, O2 before a run, O3 and O4, and O5 with equality (`gate_o5`): it
determines the verdict of each input. The checker that always passes and the checker that is always
incomplete each fail it. An input with a claim of no module is refused (`no_claim_refused`), and so
is one that mentions a constant it does not hold (`open_mention_refused`).
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Witnesses

/-- An input the admission refuses: it claims no module. -/
def unclaimed : Input := { base with modules := [] }

/-- A project that claims no module is refused, so an empty claim is no pass. -/
theorem no_claim_refused : ¬ unclaimed.WellFormed :=
  fun h => h.claims rfl

/-- A constant that mentions a constant that the input does not hold. -/
def openDecl : Decl := plain `Good.o `Good .theorem [`Gone.x]

/-- A project whose constant mentions a constant that it does not hold is refused, so an axiom that
the input cannot show is no pass. -/
theorem open_mention_refused :
    ¬ (withDecls [openDecl]
      (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, openDecl])).WellFormed := by
  intro h
  obtain ⟨d, hd, hn⟩ := h.closed openDecl (by simp [withDecls]) `Gone.x (by simp [openDecl, plain])
  simp only [withDecls, base, baseDecls, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    at hd
  rcases hd with (rfl | rfl | rfl | rfl) | rfl <;>
    simp [plain, toolchain, helperDecl, fDecl, openDecl] at hn

open Classical in
/-- A verdict function that meets the record. -/
noncomputable def verdictOf : Option Input → Verdict
  | none => .incomplete
  | some i => if i.WellFormed then (if AllHold i then .pass else .fail) else .incomplete

/-- `verdictOf` meets the record, so the record has a model. -/
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

/-- Every obligation lean-intent states, discharged for the record of the verdict. -/
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
    · exact ⟨fun _ => .pass, fun h => absurd (h unclaimed no_claim_refused) (by decide)⟩
    · exact ⟨fun _ => .incomplete, fun h => (h base wf_base).1 rfl⟩

end Witnesses

end RegulaSpecification
