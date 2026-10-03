/-
Positive control for RG1008 (`@[regula_decision]`). Each function below is registered as a
decision and must be accepted: one with a two-way decision contract, one with a one-way contract,
one of two arguments decided through `Function.uncurry`, one whose result type is `Decidable _`,
one whose result type unfolds to it, and a `DecidablePred` instance. Each must be recorded with
its result form (`decision-result=other` or `decision-result=decidable`). A function that is not
registered has no such requirement and no such record, whether or not a contract decides it.
-/
import Regula.Contract
import Regula.Decision

@[regula_decision] def positive (n : Nat) : Bool := decide (0 < n)

theorem positive_decides :
    Regula.ExecutableContract positive (Regula.Decides (· = true) fun n => 0 < n) :=
  ⟨{ sound := fun _ accepted => of_decide_eq_true accepted
     accepted := ⟨1, by decide⟩
     complete := fun _ holds => decide_eq_true holds
     refused := ⟨0, by decide⟩ }⟩

/-- Accepts only even numbers below four: sound for evenness, and it refuses the even `4`. -/
@[regula_decision] def smallEven (n : Nat) : Bool := decide (n % 2 = 0) && decide (n < 4)

theorem smallEven_decidesSoundly :
    Regula.ExecutableContract smallEven (Regula.DecidesSoundly (· = true) fun n => n % 2 = 0) :=
  ⟨{ sound := fun n accepted => by
       simp only [smallEven, Bool.and_eq_true, decide_eq_true_eq] at accepted
       exact accepted.1
     accepted := ⟨0, by decide⟩ }⟩

@[regula_decision] def within (limit n : Nat) : Bool := decide (n < limit)

theorem within_decides :
    Regula.ExecutableContract within (fun check =>
      Regula.Decides (· = true) (fun input : Nat × Nat => input.2 < input.1)
        (Function.uncurry check)) :=
  ⟨{ sound := fun _ accepted => of_decide_eq_true accepted
     accepted := ⟨(1, 0), by decide⟩
     complete := fun _ holds => decide_eq_true holds
     refused := ⟨(0, 0), by decide⟩ }⟩

/-- Both directions by construction: no contract is registered. -/
@[regula_decision] def positiveEvidence (n : Nat) : Decidable (0 < n) := inferInstance

/-- An alias Lean's reduction unfolds to `Decidable`. -/
def Verdict (p : Prop) : Type := Decidable p

@[regula_decision] def positiveVerdict (n : Nat) : Verdict (0 < n) :=
  inferInstanceAs (Decidable (0 < n))

@[regula_decision] instance positivePredicate : DecidablePred fun n : Nat => 0 < n :=
  fun _ => inferInstance

/-- Not registered: no decision requirement applies, and no contract is needed. -/
def unregistered (n : Nat) : Bool := decide (n < 3)

/-- Whether `a` and `b` are equal, by counting both down together. Lean defines it by
well-founded recursion through `equalCount._unary`. The registration is applied after
compilation, so Lean does not copy it to that definition, which carries no decision record. -/
@[regula_decision] def equalCount (a b : Nat) : Bool :=
  if a = 0 then decide (b = 0) else if b = 0 then false else equalCount (a - 1) (b - 1)
termination_by a

/-- An accepted pair whose first number is zero has a zero second number; `equalCount` is not
claimed to accept every such pair. -/
theorem equalCount_decidesSoundly :
    Regula.ExecutableContract equalCount (fun check =>
      Regula.DecidesSoundly (· = true) (fun input : Nat × Nat => input.1 = 0 → input.2 = 0)
        (Function.uncurry check)) :=
  ⟨{ sound := fun ⟨a, b⟩ accepted zero => by
       have zero : a = 0 := zero
       subst zero
       simp only [Function.uncurry] at accepted
       rw [equalCount] at accepted
       simpa using accepted
     accepted := ⟨(0, 0), by simp [Function.uncurry, equalCount]⟩ }⟩
