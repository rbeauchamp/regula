/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Safety

/-!
# The verdict of a run, and RG2001

Regula's verdict is a closed type with three values. A build that Lean could not load, or an input
that the admission refuses, is `incomplete` (RG2001), never read as absent; a claim of no module is
refused too. A well-formed input passes exactly when RG1001 to RG1006 hold of it. `gate_o5` proves
the record determinate: any two verdict functions that meet it are equal, so the record leaves
nothing unsaid about the verdict.
-/

namespace RegulaSpecification

open LeanIntent

/-- Every rule that reads the input holds of it. -/
def AllHold (i : Input) : Prop :=
  (∀ c, ¬ Violates1001 i c) ∧ (∀ c, ¬ Violates1002 i c) ∧ (∀ c, ¬ Violates1003 i c) ∧
    (∀ c, ¬ Violates1004 i c) ∧ (∀ c, ¬ Violates1005 i c) ∧ (∀ c, ¬ Violates1006 i c)

/-- The verdict of a run. -/
inductive Verdict where
  /-- The input has the closed form, and every rule holds. -/
  | pass
  /-- The input has the closed form, and a rule does not hold. -/
  | fail
  /-- The build could not be loaded, or the input does not have the closed form. -/
  | incomplete
  deriving DecidableEq, Repr

/-- The intent record of the verdict. `none` is a build Lean could not load. -/
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

/-- What it means to meet the record of the verdict, with the record's fields unfolded. -/
theorem gate_meets_iff (g : Option Input → Verdict) :
    gateRecord.Meets g ↔ g none = .incomplete ∧
      (∀ i : Input, ¬ i.WellFormed → g (some i) = .incomplete) ∧
      ∀ i : Input, i.WellFormed →
        g (some i) ≠ .incomplete ∧ (g (some i) = .pass ↔ AllHold i) := by
  simp [IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props, gateRecord]

/-- The verdict is determinate: two verdict functions that meet the record are equal. -/
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

/-- O4: the verdict function is total. -/
theorem gate_o4 : O4 gateRecord := o4_function _ rfl

end RegulaSpecification
