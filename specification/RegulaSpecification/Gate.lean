module

public import RegulaSpecification.Rules

@[expose] public section

namespace RegulaSpecification

open LeanIntent

inductive Verdict where
  | pass
  | fail
  | incomplete
  deriving DecidableEq, Repr

def gateRecord : IntentRecord (Option Input → Verdict) where
  shape := .function (Option Input) (fun _ => Verdict)
  dom := []
  props := [
    ⟨"RG2001: a build that Lean could not load is incomplete", fun g => g none = .incomplete⟩,
    ⟨"an input the admission refuses is incomplete",
      fun g => ∀ i : Input, ¬ i.WellFormed → g (some i) = .incomplete⟩,
    ⟨"a well-formed input is complete, and passes exactly when every rule holds",
      fun g => ∀ i : Input, i.WellFormed →
        g (some i) ≠ .incomplete ∧ (g (some i) = .pass ↔ AllHold i)⟩]
  vocab := [⟨"well-formed input", Input, Input.WellFormed⟩]

theorem gate_meets_iff (g : Option Input → Verdict) :
    gateRecord.Meets g ↔ g none = .incomplete ∧
      (∀ i : Input, ¬ i.WellFormed → g (some i) = .incomplete) ∧
      ∀ i : Input, i.WellFormed →
        g (some i) ≠ .incomplete ∧ (g (some i) = .pass ↔ AllHold i) := by
  simp [IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props, gateRecord]

theorem gate_o5 : O5 gateRecord .eq := by
  rw [o5_correct]
  intro u v hu hv
  have hu' := (gate_meets_iff u).mp ⟨hu.1, hu.2⟩
  have hv' := (gate_meets_iff v).mp ⟨hv.1, hv.2⟩
  funext o
  cases o with
  | none => rw [hu'.1, hv'.1]
  | some i =>
    by_cases hi : i.WellFormed
    · obtain ⟨hun, hup⟩ := hu'.2.2 i hi
      obtain ⟨hvn, hvp⟩ := hv'.2.2 i hi
      by_cases hall : AllHold i
      · rw [hup.mpr hall, hvp.mpr hall]
      · have h1 : u (some i) ≠ .pass := fun h => hall (hup.mp h)
        have h2 : v (some i) ≠ .pass := fun h => hall (hvp.mp h)
        cases hx : u (some i) <;> cases hy : v (some i) <;> simp_all
    · rw [hu'.2.1 i hi, hv'.2.1 i hi]

theorem gate_o4 : O4 gateRecord := o4_function _ rfl

end RegulaSpecification
