/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import LeanIntent.Record
import LeanIntent.Obligations
import LeanIntent.Progress
import RegulaSpecification.Input

/-!
# The intent record of a rule

Each rule is a pure function from the well-formed closed input to the list of constants it reports.
A rule's function takes the proof of the form with the input (`Checker`), so it has no case for an
input the admission refuses. Its intent record (`LeanIntent.IntentRecord`) has that function as its
subject and one property: the function reports a subject exactly when the subject violates the rule
(`ruleRecord`). The rule's meaning is therefore all in its violation predicate, which each rule
module defines and documents. The class `Admission` gives the well-formedness of the input.

The theorems below discharge lean-intent's obligations for such a record from two witnesses that
each rule supplies (`Witnessed`): a well-formed input on which a subject violates the rule, and a
well-formed input with a subject that does not. They give O2 at confirmation and before running,
O3, O4, and O5 with the freedom `SameReports`, which is what the record leaves unsaid: the order
and repetition of reported subjects.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

/-- The admission of a rule's input: what the shell refuses, as incomplete, before any rule runs. -/
class Admission (α : Type) where
  /-- The input has the closed form. -/
  WellFormed : α → Prop

instance : Admission Input := ⟨Input.WellFormed⟩

/-- An input of the form that the admission gives, with the proof of that form. -/
abbrev Admitted (α : Type) [Admission α] : Type := { i : α // Admission.WellFormed i }

/-- A rule's checker: from the well-formed closed input to the subjects it reports. -/
abbrev Checker (α S : Type) [Admission α] : Type := Admitted α → List S

variable {α S : Type} [Admission α]

/-- The one property of a rule's record: the checker reports a subject exactly when the subject
violates the rule. -/
def reportsExactly (rule : String) (V : α → S → Prop) : Clause (Checker α S) :=
  ⟨rule ++ ": reports exactly the violations of each well-formed input",
    fun f => ∀ i s, s ∈ f i ↔ V i.1 s⟩

/-- The intent record of a rule whose violations `V` states. Its vocabulary is the admission and
the violation predicate. -/
def ruleRecord (rule : String) (V : α → S → Prop) : IntentRecord (Checker α S) where
  shape := .function (Admitted α) (fun _ => List S)
  dom := []
  props := [reportsExactly rule V]
  vocab := [⟨"well-formed input", α, Admission.WellFormed⟩,
    ⟨rule ++ " violation", α × S, fun p => V p.1 p.2⟩]

/-- Two checkers report the same subjects on every well-formed input. -/
def SameReports (f g : Checker α S) : Prop :=
  ∀ i s, s ∈ f i ↔ s ∈ g i

/-- The witnesses a rule's record needs: a well-formed input on which `bad` violates the rule, a
well-formed input on which `fine` does not, and a finite list of the candidates of each input. -/
structure Witnessed (V : α → S → Prop) where
  /-- The candidates of an input: every subject that can violate the rule there. -/
  support : α → List S
  /-- Each subject that violates the rule is a candidate. -/
  support_complete : ∀ i s, V i s → s ∈ support i
  /-- The case the rule must rule out. -/
  refused : α
  /-- The refused case is well-formed. -/
  refused_wf : Admission.WellFormed refused
  /-- The subject of the refused case that violates the rule. -/
  bad : S
  /-- It violates the rule. -/
  bad_violates : V refused bad
  /-- The case the rule must admit. -/
  admitted : α
  /-- The admitted case is well-formed. -/
  admitted_wf : Admission.WellFormed admitted
  /-- The subject of the admitted case that does not violate the rule. -/
  fine : S
  /-- It does not violate the rule. -/
  fine_admitted : ¬ V admitted fine

/-- The checker that reports every candidate of a rule's witnesses. -/
def Witnessed.candidates {V : α → S → Prop} (w : Witnessed V) : Checker α S :=
  fun i => w.support i.1

variable {rule : String} {V : α → S → Prop}

/-- What it means to meet a rule's record, with the record's fields unfolded. -/
theorem meets_iff (f : Checker α S) :
    (ruleRecord rule V).Meets f ↔ ∀ i s, s ∈ f i ↔ V i.1 s := by
  simp [IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props, ruleRecord, reportsExactly]

/-- The checker that reports nothing does not meet the record: it misses the refused case. -/
theorem silent_fails (w : Witnessed V) : ¬ (ruleRecord rule V).Meets (fun _ => []) := by
  rw [meets_iff]
  intro h
  exact absurd ((h ⟨w.refused, w.refused_wf⟩ w.bad).mpr w.bad_violates) (by simp)

/-- The checker that reports every candidate does not meet the record: it refuses the admitted
case. -/
theorem noisy_fails (w : Witnessed V) (hfine : w.fine ∈ w.support w.admitted) :
    ¬ (ruleRecord rule V).Meets w.candidates := by
  rw [meets_iff]
  intro h
  exact w.fine_admitted ((h ⟨w.admitted, w.admitted_wf⟩ w.fine).mp hfine)

open Classical in
/-- A checker that meets the record: the candidates that violate the rule. -/
noncomputable def exact (w : Witnessed V) : Checker α S :=
  fun i => (w.support i.1).filter fun s => decide (V i.1 s)

/-- `exact` meets the record, so the record has a model. -/
theorem exact_meets (w : Witnessed V) : (ruleRecord rule V).Meets (exact w) := by
  rw [meets_iff]
  intro i s
  simp only [exact, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨w.support_complete i.1 s h, h⟩⟩

/-- O2 at confirmation: the domain hypotheses have a model and each vocabulary predicate has an
instance. -/
theorem o2 (w : Witnessed V) : O2 (ruleRecord rule V) := by
  rw [o2_correct]
  refine ⟨⟨fun _ => [], by simp [ruleRecord]⟩, ?_⟩
  intro p hp
  simp only [ruleRecord, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨w.admitted, w.admitted_wf⟩
  · exact ⟨(w.refused, w.bad), w.bad_violates⟩

/-- O2 before running: the record has a model. -/
theorem o2Run (w : Witnessed V) : O2Run (ruleRecord rule V) := o2Run_of_meets (exact_meets w)

/-- O3: the property can fail. -/
theorem o3 (w : Witnessed V) : O3 (ruleRecord rule V) := by
  rw [o3_correct]
  intro p hp
  simp only [ruleRecord, List.mem_singleton] at hp
  subst hp
  refine ⟨fun _ => [], fun h => ?_⟩
  exact absurd ((h ⟨w.refused, w.refused_wf⟩ w.bad).mpr w.bad_violates) List.not_mem_nil

/-- O4: the subject is a function, which Lean makes total. -/
theorem o4 : O4 (ruleRecord rule V) := o4_function _ rfl

/-- O5 with the freedom `SameReports`: any two checkers that meet the record report the same
subjects on each well-formed input. -/
theorem o5 : O5 (ruleRecord rule V) (.rel SameReports) := by
  rw [o5_correct]
  intro u v hu hv i s
  have hu' := (meets_iff (rule := rule) u).mp ⟨hu.1, hu.2⟩ i s
  have hv' := (meets_iff (rule := rule) v).mp ⟨hv.1, hv.2⟩ i s
  exact hu'.trans hv'.symm

/-- Every obligation lean-intent states, discharged for a witnessed rule. -/
theorem adequate (w : Witnessed V) :
    O2 (ruleRecord rule V) ∧ O2Run (ruleRecord rule V) ∧ O3 (ruleRecord rule V) ∧
      O4 (ruleRecord rule V) ∧ O5 (ruleRecord rule V) (.rel SameReports) :=
  ⟨o2 w, o2Run w, o3 w, o4, o5⟩

end RegulaSpecification
