import RegulaSpecification.Foundation
import RegulaSpecification.Execution
import RegulaSpecification.Contracts
import RegulaSpecification.Project
import RegulaSpecification.Intent

/-!
# The verdict of a run, and RG2001

Regula's verdict is a closed type with three values. A build that Lean could not load, or an input
that the admission refuses, is `incomplete` (RG2001), never read as absent; a well-formed input
passes exactly when every kept and new rule holds of it. `gate_o5` proves the record determinate:
any two verdict functions that meet it are equal, so the record leaves nothing unsaid about the
verdict.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

/-- The two allowlists the closed subset uses, fixed by #484. -/
structure Allowlists where
  /-- The option names a claimed target may set (RG2006). -/
  options : Name → Prop
  /-- The environment extensions a claimed module may have entries of (RG2007). -/
  extensions : Name → Prop

/-- Every kept and new rule holds of the input. -/
def AllHold (a : Allowlists) (i : Input) : Prop :=
  (∀ c, ¬ Violates1001 i c) ∧ (∀ c, ¬ Violates1002 i c) ∧ (∀ c, ¬ Violates1003 i c) ∧
    (∀ c, ¬ Violates1004 i c) ∧ (∀ c, ¬ Violates1005 i c) ∧ (∀ c, ¬ Violates1006 i c) ∧
    (∀ c, ¬ Violates1007 i c) ∧ (∀ c, ¬ Violates1008 i c) ∧ (∀ c, ¬ Violates1009 i c) ∧
    (∀ t, ¬ Violates2002 i t) ∧ (∀ m, ¬ Violates2004 i m) ∧ (∀ t, ¬ Violates2006 a.options i t) ∧
    (∀ m, ¬ Violates2007 a.extensions i m) ∧ (∀ c, ¬ Violates3001 i c) ∧
    (∀ c, ¬ Violates3002 i c) ∧ (∀ s, ¬ Violates6001 i s)

/-- The verdict of a run. -/
inductive Verdict where
  | pass
  | fail
  | incomplete
  deriving DecidableEq, Repr

/-- The intent record of the verdict. `none` is a build Lean could not load. -/
def gateRecord (a : Allowlists) : IntentRecord (Option Input → Verdict) where
  shape := .function (Option Input) (fun _ => Verdict)
  dom := []
  props := [
    ⟨"RG2001: a build that Lean could not load is incomplete", fun g => g none = .incomplete⟩,
    ⟨"an input the admission refuses is incomplete",
      fun g => ∀ i : Input, ¬ i.WellFormed → g (some i) = .incomplete⟩,
    ⟨"a well-formed input is complete, and passes exactly when every rule holds",
      fun g => ∀ i : Input, i.WellFormed → g (some i) ≠ .incomplete ∧ (g (some i) = .pass ↔ AllHold a i)⟩]
  vocab := [⟨"well-formed input", Input, Input.WellFormed⟩]

theorem gate_meets_iff (a : Allowlists) (g : Option Input → Verdict) :
    (gateRecord a).Meets g ↔ g none = .incomplete ∧
      (∀ i : Input, ¬ i.WellFormed → g (some i) = .incomplete) ∧
      ∀ i : Input, i.WellFormed → g (some i) ≠ .incomplete ∧ (g (some i) = .pass ↔ AllHold a i) := by
  simp [IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props, gateRecord]

/-- The verdict is determinate: two verdict functions that meet the record are equal. -/
theorem gate_o5 (a : Allowlists) : O5 (gateRecord a) .eq := by
  rw [o5_correct]
  intro u v hu hv
  have hu' := (gate_meets_iff a u).mp ⟨hu.1, hu.2⟩
  have hv' := (gate_meets_iff a v).mp ⟨hv.1, hv.2⟩
  funext o
  cases o with
  | none => rw [hu'.1, hv'.1]
  | some i =>
    by_cases hi : i.WellFormed
    · obtain ⟨hun, hup⟩ := hu'.2.2 i hi
      obtain ⟨hvn, hvp⟩ := hv'.2.2 i hi
      by_cases hall : AllHold a i
      · rw [hup.mpr hall, hvp.mpr hall]
      · have h1 : u (some i) ≠ .pass := fun h => hall (hup.mp h)
        have h2 : v (some i) ≠ .pass := fun h => hall (hvp.mp h)
        cases hx : u (some i) <;> cases hy : v (some i) <;> simp_all
    · rw [hu'.2.1 i hi, hv'.2.1 i hi]

/-- O4: the verdict function is total. -/
theorem gate_o4 (a : Allowlists) : O4 (gateRecord a) := o4_function _ rfl

end RegulaSpecification
