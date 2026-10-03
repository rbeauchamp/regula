import Regula.Contract
import RegulaPolicy.Guards
import RegulaPolicy.Traversal
import Lean.Data.Json

/-! # Qualification assertions

Pure qualification assertions. `evaluate` accepts exactly a list whose assertions
are all true, and otherwise identifies its first false assertion. This is a contract
about supplied observations, not the truth of compiler, filesystem, or process effects.
The operational adapters call the registered, proof-requiring entrypoint. -/

namespace RegulaQualification

/-- A labeled executable assertion about an observation. Labels explain refusal;
the Boolean is the exact predicate being checked, not evidence about external IO. -/
structure Check where
  /-- The text `evaluate` returns when this assertion is the first false one. -/
  label : String
  /-- Whether the assertion is true of the supplied observation. -/
  holds : Bool
  deriving Repr, DecidableEq

/-- Conjunction of all supplied assertions, including the empty conjunction. -/
def Satisfied (checks : List Check) : Prop :=
  ∀ check ∈ checks, check.holds = true

/-- Stop at the first false assertion; never turn an unknown observation into success. -/
def evaluate : List Check → Except String Unit
  | [] => .ok ()
  | check :: rest => if check.holds then evaluate rest else .error check.label

/-- One assertion as a pure `Except` step: its label is the refusal. -/
def Check.step (check : Check) : Except String Unit :=
  if check.holds then .ok () else .error check.label

/-- The evaluator is exactly the standard traversal of `Check.step`; its recursion is
retained as the executed definition. -/
theorem evaluate_eq_forM (checks : List Check) : evaluate checks = checks.forM Check.step := by
  induction checks with
  | nil => rfl
  | cons check rest ih =>
    change _ = (check.step >>= fun _ => rest.forM Check.step)
    cases h : check.holds <;> rw [evaluate, Check.step, h]
    · rfl
    · exact ih

/-- Success is equivalent to every supplied assertion holding. No assumptions about
list size, labels, or observations; in particular an always-refusing implementation
cannot satisfy this equivalence. -/
theorem evaluate_success (checks : List Check) :
    evaluate checks = .ok () ↔ Satisfied checks := by
  rw [evaluate_eq_forM, RegulaPolicy.Guards.listForM_eq_ok]
  refine forall₂_congr fun check _ => ?_
  cases h : check.holds <;> simp [Check.step, h]

/-- Refusal reports exactly the first false assertion, with a satisfied prefix and
an arbitrary unevaluated suffix. Duplicate labels do not affect the statement. -/
theorem evaluate_error (checks : List Check) (label : String) :
    evaluate checks = .error label ↔
      ∃ before check after, checks = before ++ check :: after ∧
        Satisfied before ∧ check.holds = false ∧ check.label = label := by
  rw [evaluate_eq_forM, RegulaPolicy.forM_eq_error]
  refine exists_congr fun before => exists_congr fun check => exists_congr fun after =>
    and_congr_right fun _ => and_congr ?_ ?_
  · refine forall₂_congr fun b _ => ?_
    cases hb : b.holds <;> simp [Check.step, hb]
  · cases hc : check.holds <;> simp [Check.step, hc]

/-- Composition runs the suffix only after prefix success and retains the exact
first error otherwise. This describes pure `Except`, not rollback of external IO. -/
theorem evaluate_append (xs ys : List Check) :
    evaluate (xs ++ ys) = (evaluate xs).bind (fun _ => evaluate ys) := by
  induction xs with
  | nil => rfl
  | cons check rest ih =>
    cases h : check.holds <;> simp [evaluate, h, ih, Except.bind]

/-- Required success, refusal, and composition behavior of the actual evaluator. -/
def EvaluationContract (run : List Check → Except String Unit) : Prop :=
  (∀ checks, run checks = .ok () ↔ Satisfied checks) ∧
  (∀ checks label, run checks = .error label ↔
    ∃ before check after, checks = before ++ check :: after ∧
      Satisfied before ∧ check.holds = false ∧ check.label = label) ∧
  (∀ xs ys, run (xs ++ ys) = (run xs).bind (fun _ => run ys))

/-- The IO adapters invoke this contract's `run`, which is definitionally `evaluate`. -/
theorem checked_evaluation : Regula.ExecutableContract evaluate EvaluationContract :=
  ⟨evaluate_success, evaluate_error, evaluate_append⟩

/-- `evaluate` accepts exactly the lists whose every assertion holds (`evaluate_success`): it
accepts the empty list and refuses one false assertion. `checked_evaluation` registers the
larger requirement, which also fixes the refusal's label and composition; this registration
states the accepted set as a two-way decision. -/
theorem checked_evaluate : Regula.ExecutableContract evaluate
    (Regula.Decides (· = .ok ()) Satisfied) :=
  ⟨.of_iff evaluate_success ⟨[], rfl⟩ ⟨[⟨"reject", false⟩], by simp [evaluate]⟩⟩

/-- Non-vacuity: a genuine true assertion succeeds. -/
theorem positive_control : evaluate [⟨"positive", true⟩] = .ok () := rfl

/-- A false assertion refuses even when surrounded by successful assertions. -/
theorem negative_control :
    evaluate [⟨"before", true⟩, ⟨"defect", false⟩, ⟨"after", true⟩] = .error "defect" := rfl

end RegulaQualification
