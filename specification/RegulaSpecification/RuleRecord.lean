import LeanIntent.Record
import LeanIntent.Obligations
import LeanIntent.Progress
import RegulaSpecification.Input

/-!
# The intent record of a rule

Each kept or new rule is a pure function from the closed input to the list of subjects it reports
(declarations, modules, targets or deliverables). Its intent record (`LeanIntent.IntentRecord`)
has that function as its subject and one property: on every well-formed input, the function
reports a subject exactly when the subject violates the rule (`ruleRecord`). The rule's meaning
is therefore all in its violation predicate, which each rule module defines and documents. A rule
reads one environment (`Input`), or the bundle of every environment of a run (`Bundle`); the
class `Admission` gives the well-formedness of each.

The theorems below discharge lean-intent's obligations for such a record from two witnesses that
each rule supplies (`Witnessed`): a well-formed input on which a subject violates the rule, and a
well-formed input with a subject that does not. They give O2 at confirmation and before running,
O3, O4, and O5 with the freedom `SameReports`, which is what the record leaves unsaid: the order
and repetition of reported subjects, and what the function does on an input the admission refuses.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

/-- The admission of a rule's input: what the shell refuses, as incomplete, before any rule runs. -/
class Admission (α : Type) where
  /-- The input has the closed form. -/
  WellFormed : α → Prop

instance : Admission Input := ⟨Input.WellFormed⟩

/-- A rule's checker: from the closed input to the subjects it reports. -/
abbrev Checker (α S : Type) : Type := α → List S

variable {α S : Type} [Admission α]

/-- The one property of a rule's record: on each well-formed input, the checker reports a subject
exactly when the subject violates the rule. -/
def reportsExactly (rule : String) (V : α → S → Prop) : Clause (Checker α S) :=
  ⟨rule ++ ": reports exactly the violations of each well-formed input",
    fun f => ∀ i, Admission.WellFormed i → ∀ s, s ∈ f i ↔ V i s⟩

/-- The intent record of a rule whose violations `V` states. Its vocabulary is the admission and
the violation predicate. -/
def ruleRecord (rule : String) (V : α → S → Prop) : IntentRecord (Checker α S) where
  shape := .function α (fun _ => List S)
  dom := []
  props := [reportsExactly rule V]
  vocab := [⟨"well-formed input", α, Admission.WellFormed⟩,
    ⟨rule ++ " violation", α × S, fun p => V p.1 p.2⟩]

/-- Two checkers report the same subjects on every well-formed input. -/
def SameReports (f g : Checker α S) : Prop :=
  ∀ i, Admission.WellFormed i → ∀ s, s ∈ f i ↔ s ∈ g i

/-- The witnesses a rule's record needs: a well-formed input on which `bad` violates the rule, a
well-formed input on which `fine` does not, and a finite list of the candidates of each input. -/
structure Witnessed (V : α → S → Prop) where
  /-- The candidates of an input: every subject that can violate the rule there. -/
  support : α → List S
  support_complete : ∀ i s, V i s → s ∈ support i
  /-- The case the rule must rule out. -/
  refused : α
  refused_wf : Admission.WellFormed refused
  bad : S
  bad_violates : V refused bad
  /-- The case the rule must admit. -/
  admitted : α
  admitted_wf : Admission.WellFormed admitted
  fine : S
  fine_admitted : ¬ V admitted fine

variable {rule : String} {V : α → S → Prop}

theorem meets_iff (f : Checker α S) :
    (ruleRecord rule V).Meets f ↔ ∀ i, Admission.WellFormed i → ∀ s, s ∈ f i ↔ V i s := by
  simp [IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props, ruleRecord, reportsExactly]

/-- The checker that reports nothing does not meet the record: it misses the refused case. -/
theorem silent_fails (w : Witnessed V) : ¬ (ruleRecord rule V).Meets (fun _ => []) := by
  rw [meets_iff]
  intro h
  exact absurd ((h w.refused w.refused_wf w.bad).mpr w.bad_violates) (by simp)

/-- The checker that reports every candidate does not meet the record: it refuses the admitted
case. -/
theorem noisy_fails (w : Witnessed V) (hfine : w.fine ∈ w.support w.admitted) :
    ¬ (ruleRecord rule V).Meets w.support := by
  rw [meets_iff]
  intro h
  exact w.fine_admitted ((h w.admitted w.admitted_wf w.fine).mp hfine)

open Classical in
/-- A checker that meets the record: the candidates that violate the rule. -/
noncomputable def exact (w : Witnessed V) : Checker α S :=
  fun i => (w.support i).filter fun s => decide (V i s)

theorem exact_meets (w : Witnessed V) : (ruleRecord rule V).Meets (exact w) := by
  rw [meets_iff]
  intro i _ s
  simp only [exact, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨w.support_complete i s h, h⟩⟩

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
  exact absurd ((h w.refused w.refused_wf w.bad).mpr w.bad_violates) List.not_mem_nil

/-- O4: the subject is a function, which Lean makes total. -/
theorem o4 : O4 (ruleRecord rule V) := o4_function _ rfl

/-- O5 with the freedom `SameReports`: any two checkers that meet the record report the same
subjects on each well-formed input. -/
theorem o5 : O5 (ruleRecord rule V) (.rel SameReports) := by
  rw [o5_correct]
  intro u v hu hv i hi s
  have hu' := (meets_iff (rule := rule) u).mp ⟨hu.1, hu.2⟩ i hi s
  have hv' := (meets_iff (rule := rule) v).mp ⟨hv.1, hv.2⟩ i hi s
  exact hu'.trans hv'.symm

/-- Every obligation lean-intent states, discharged for a witnessed rule. -/
theorem adequate (w : Witnessed V) :
    O2 (ruleRecord rule V) ∧ O2Run (ruleRecord rule V) ∧ O3 (ruleRecord rule V) ∧
      O4 (ruleRecord rule V) ∧ O5 (ruleRecord rule V) (.rel SameReports) :=
  ⟨o2 w, o2Run w, o3 w, o4, o5⟩

end RegulaSpecification
