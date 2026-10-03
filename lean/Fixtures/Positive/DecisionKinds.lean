/-
Positive control for decision kinds (`Regula.DecidesSoundly`, `Regula.DecidesCompletely`,
`Regula.Decides`). Each registration below must be accepted and recorded with the kind its
requirement states: a two-way kind, each one-way kind, a kind reached only through an alias, a
two-argument function decided through `Function.uncurry`, and a failure-returning function whose
acceptance is `= none`. A registration with an ordinary requirement must be recorded with no
kind. The closing theorems state, for every specification, what the witness fields exclude: the
function that refuses every input has no `accepted` witness and so no sound kind, and it is not
complete for a specification some input satisfies.
-/
import Regula.Contract

def positive (n : Nat) : Bool := decide (0 < n)

theorem positive_decides :
    Regula.ExecutableContract positive (Regula.Decides (· = true) fun n => 0 < n) :=
  ⟨{ sound := fun _ accepted => of_decide_eq_true accepted
     accepted := ⟨1, by decide⟩
     complete := fun _ holds => decide_eq_true holds
     refused := ⟨0, by decide⟩ }⟩

/-- Accepts only even numbers below four: sound for evenness, and it refuses the even `4`. -/
def smallEven (n : Nat) : Bool := decide (n % 2 = 0) && decide (n < 4)

theorem smallEven_decidesSoundly :
    Regula.ExecutableContract smallEven (Regula.DecidesSoundly (· = true) fun n => n % 2 = 0) :=
  ⟨{ sound := fun n accepted => by
       simp only [smallEven, Bool.and_eq_true, decide_eq_true_eq] at accepted
       exact accepted.1
     accepted := ⟨0, by decide⟩ }⟩

/-- Accepts every number below ten: complete for "below four", and it accepts `5`. -/
def belowTen (n : Nat) : Bool := decide (n < 10)

theorem belowTen_decidesCompletely :
    Regula.ExecutableContract belowTen (Regula.DecidesCompletely (· = true) fun n => n < 4) :=
  ⟨{ complete := fun n holds => decide_eq_true (Nat.lt_trans holds (by decide))
     refused := ⟨10, by decide⟩ }⟩

def within (limit n : Nat) : Bool := decide (n < limit)

/-- A kind reached through an alias, about a two-argument function on the product of its
arguments. -/
def WithinContract (check : Nat → Nat → Bool) : Prop :=
  Regula.Decides (· = true) (fun input : Nat × Nat => input.2 < input.1) (Function.uncurry check)

theorem within_decides : Regula.ExecutableContract within WithinContract :=
  ⟨{ sound := fun _ accepted => of_decide_eq_true accepted
     accepted := ⟨(1, 0), by decide⟩
     complete := fun _ holds => decide_eq_true holds
     refused := ⟨(0, 0), by decide⟩ }⟩

/-- Reports why a number is not positive; `none` accepts. -/
def positiveFailure (n : Nat) : Option String := if 0 < n then none else some "not positive"

theorem positiveFailure_decides :
    Regula.ExecutableContract positiveFailure (Regula.Decides (· = none) fun n => 0 < n) :=
  ⟨Regula.Decides.of_iff (fun n => by simp [positiveFailure, Nat.pos_iff_ne_zero])
    ⟨1, by decide⟩ ⟨0, by decide⟩⟩

theorem positive_plain :
    Regula.ExecutableContract positive (fun check => ∀ n, check n = decide (0 < n)) :=
  ⟨fun _ => rfl⟩

/-- The standard's always-rejecting parser (§3.7): it satisfies its refined return type. -/
def rejectAll : Nat → Option {n : Nat // 0 < n} := fun _ => none

theorem rejectAll_refuses (n : Nat) : ¬ (rejectAll n).isSome = true := by simp [rejectAll]

/-- `rejectAll` has no `accepted` witness. -/
theorem rejectAll_not_accepted : ¬ ∃ n, (rejectAll n).isSome = true :=
  fun ⟨n, accepted⟩ => rejectAll_refuses n accepted

/-- So it has no sound kind, whatever the specification. -/
theorem rejectAll_not_decidesSoundly (spec : Nat → Prop) :
    ¬ Regula.DecidesSoundly (·.isSome = true) spec rejectAll :=
  Regula.DecidesSoundly.not_of_refuses_all rejectAll_refuses

/-- It is not complete for positivity, which `1` satisfies. -/
theorem rejectAll_not_decidesCompletely :
    ¬ Regula.DecidesCompletely (·.isSome = true) (fun n => 0 < n) rejectAll :=
  Regula.DecidesCompletely.not_of_refuses_all rejectAll_refuses ⟨1, by decide⟩
