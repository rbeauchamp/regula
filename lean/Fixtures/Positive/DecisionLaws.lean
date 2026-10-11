/-
Positive control for the law observer (`Regula.DecisionEquivalence` and the reports of the decision
carriers). Each registration below must be accepted, each with the law observer's report of it: a
law about the implementation itself and one through `Function.uncurry`, each linked with its two
laws and no outcome; a sound kind, linked with its law and its two outcomes; a law about a field
application, which the observer does not read (`unsupported`); and a law about another function
(`mismatch`). The last two are reported without a linkage conclusion, and neither is refused: an
equivalence is an ordinary requirement under RG1007. The closing theorems state that a law alone
gives no outcome.
-/
import Regula.Contract

/-- Whether `n` is even. -/
def even (n : Nat) : Bool := n % 2 == 0

theorem even_law :
    Regula.ExecutableContract even (Regula.DecisionEquivalence (· = true) fun n => n % 2 = 0) :=
  ⟨⟨fun n => by simp [even]⟩⟩

/-- Whether `n` is below `limit`. -/
def within (limit n : Nat) : Bool := decide (n < limit)

theorem within_law :
    Regula.ExecutableContract within (fun check =>
      Regula.DecisionEquivalence (· = true) (fun input : Nat × Nat => input.2 < input.1)
        (Function.uncurry check)) :=
  ⟨⟨fun _ => decide_eq_true_iff⟩⟩

/-- Accepts only even numbers below four: sound for evenness, and it refuses the even `4`. -/
def smallEven (n : Nat) : Bool := decide (n % 2 = 0) && decide (n < 4)

theorem smallEven_decidesSoundly :
    Regula.ExecutableContract smallEven (Regula.DecidesSoundly (· = true) fun n => n % 2 = 0) :=
  ⟨{ sound := fun n accepted => by
       simp only [smallEven, Bool.and_eq_true, decide_eq_true_eq] at accepted
       exact accepted.1
     accepted := ⟨0, by decide⟩ }⟩

/-- Whether `n` is above `floor`. -/
def above (floor n : Nat) : Bool := decide (floor < n)

/-- A law about `above` applied to the fields of a pair, a form the law observer does not read. -/
theorem above_fields :
    Regula.ExecutableContract above (fun check =>
      Regula.DecisionEquivalence (· = true) (fun input : Nat × Nat => input.1 < input.2)
        (fun input => check input.1 input.2)) :=
  ⟨⟨fun _ => decide_eq_true_iff⟩⟩

/-- A copy of `even` under another name. -/
def evenCopy (n : Nat) : Bool := n % 2 == 0

/-- A registration of `even` whose law is about `evenCopy`: the requirement holds, and the law
observer reports that the function it is about is not the implementation. -/
theorem even_otherLaw :
    Regula.ExecutableContract even (fun _ =>
      Regula.DecisionEquivalence (· = true) (fun n => n % 2 = 0) evenCopy) :=
  ⟨⟨fun n => by simp [evenCopy]⟩⟩

/-- A law on an empty domain holds, and its function neither accepts nor refuses an input. -/
theorem law_without_outcome :
    Regula.DecisionEquivalence (fun b : Bool => b = true) (fun _ => True)
        (Empty.elim : Empty → Bool) ∧
      ¬ (∃ x, (Empty.elim x : Bool) = true) ∧ ¬ ∃ x, ¬ (Empty.elim x : Bool) = true :=
  Regula.DecisionEquivalence.of_empty Empty.elim
