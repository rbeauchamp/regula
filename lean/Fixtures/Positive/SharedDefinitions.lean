/-
Controls for the functions that the two sides of a decision registration share, where no
registration is refused. A registration is refused for a shared function with a result of `Bool`
or `BEq` (`Fixtures.Mutations.SharedTests` has those controls). Each registration below shares
no such function, so each must be accepted. The record of each must name the functions of the
other class that its specification reaches first and that its implementation or its acceptance
predicate reaches too (`RegulaPolicy.SharedNames`):

* `apart_decides`: the specification states a proposition, and the function decides it with a
  test of Lean's library. No function is named.
* `library_decides`: the specification and the function both call a test of Lean's library.
  A function of that library is not counted, so no function is named.
* `decided_decides`: the remedy with a theorem. The specification names a proposition, and the
  function decides it with a `Decidable` instance that runs a helper with a result of `Bool`.
  The specification's side does not read the value of the instance, so the helper is not shared.
* `copy_decides`: a limit of the search. The specification calls a helper with a result of
  `Bool`, and the function calls a second helper with the same text. They are two constants, so
  no function is named.
* `noEven_decides`: the form of `marks` in issue 249. A helper prepares the input of the two
  sides, and its result is a list. The helper is named in the class `other`.
* `below_decides`: the two sides share a definition of a proposition, its `Decidable` instance
  and a constant. No function is named.
* `knownSign_decides`: the two sides share a closed list whose value has a function
  abstraction. The list takes no argument, so it is no function and is not named.
* `firstBefore_decides`: the two sides share a record of one function, with no argument. Its
  type has a field that takes an argument, so it is a function, named in the class `other`. The
  test is a function abstraction inside the record and no constant, so the search has no
  function with a result of `Bool` to name.
-/
import Regula.Contract

/-- Whether `n` is below four. -/
def apart (n : Nat) : Bool := decide (n < 4)

theorem apart_decides :
    Regula.ExecutableContract apart (Regula.Decides (· = true) fun n => n < 4) :=
  ⟨.of_iff (fun n => by simp [apart]) ⟨0, by decide⟩ ⟨4, by decide⟩⟩

/-- Whether `n` is at most three, by a test of Lean's library. -/
def library (n : Nat) : Bool := Nat.ble n 3

theorem library_decides :
    Regula.ExecutableContract library (Regula.Decides (· = true) fun n => Nat.ble n 3 = true) :=
  ⟨.of_iff (fun _ => Iff.rfl) ⟨0, by decide⟩ ⟨4, by decide⟩⟩

/-- A helper with a result of `Bool`. -/
def small (n : Nat) : Bool := decide (n < 4)

/-- The statement that `small` decides, with no test. -/
def Small (n : Nat) : Prop := n < 4

/-- The helper decides the statement. -/
theorem small_iff (n : Nat) : small n = true ↔ Small n := by
  simp [small, Small]

instance (n : Nat) : Decidable (Small n) := decidable_of_iff _ (small_iff n)

/-- Decides `Small` with its instance, which runs `small`. -/
def decided (n : Nat) : Bool := decide (Small n)

theorem decided_decides :
    Regula.ExecutableContract decided (Regula.Decides (· = true) Small) :=
  ⟨.of_iff (fun n => by simp [decided]) ⟨0, by decide⟩ ⟨4, by decide⟩⟩

/-- A second helper with the text of `small`: a different constant. -/
def smallCopy (n : Nat) : Bool := decide (n < 4)

/-- Whether `n` is below four: it calls `small`. -/
def copy (n : Nat) : Bool := small n

theorem copy_decides :
    Regula.ExecutableContract copy (Regula.Decides (· = true) fun n => smallCopy n = true) :=
  ⟨.of_iff (fun _ => Iff.rfl) ⟨0, by decide⟩ ⟨4, by decide⟩⟩

/-- A step that prepares the input: the even numbers of a list. -/
def evens (numbers : List Nat) : List Nat := numbers.filter fun n => n % 2 = 0

/-- Whether a list has no even number: it calls `evens`. -/
def noEven (numbers : List Nat) : Bool := (evens numbers).isEmpty

theorem noEven_decides :
    Regula.ExecutableContract noEven
      (Regula.Decides (· = true) fun numbers => evens numbers = []) :=
  ⟨.of_iff (fun numbers => by simp [noEven]) ⟨[1], by decide⟩ ⟨[2], by decide⟩⟩

/-- A constant. -/
def limit : Nat := 4

/-- A statement that names the constant `limit`. -/
def Below (n : Nat) : Prop := n < limit

instance (n : Nat) : Decidable (Below n) := by
  unfold Below
  infer_instance

/-- Decides `Below` with its instance. -/
def below (n : Nat) : Bool := decide (Below n)

theorem below_decides :
    Regula.ExecutableContract below (Regula.Decides (· = true) Below) :=
  ⟨.of_iff (fun n => by simp [below]) ⟨0, by decide⟩ ⟨4, by decide⟩⟩

/-- A closed list. Its value has a function abstraction and it takes no argument. -/
def signs : List (String × Nat) := ["a", "bb"].map fun sign => (sign, sign.length)

/-- Whether `sign` is one of `signs`. -/
def knownSign (sign : String) : Bool := decide (∃ pair ∈ signs, pair.1 = sign)

theorem knownSign_decides :
    Regula.ExecutableContract knownSign
      (Regula.Decides (· = true) fun sign => ∃ pair ∈ signs, pair.1 = sign) :=
  ⟨.of_iff (fun sign => by simp [knownSign]) ⟨"a", by decide⟩ ⟨"c", by decide⟩⟩

/-- An order, as a record of one function. -/
structure Order where
  /-- Whether the first number is before the second. -/
  before : Nat → Nat → Bool

/-- The order of the larger number first. It takes no argument. -/
def descending : Order := ⟨fun a b => decide (b < a)⟩

/-- Whether `a` is before `b` in `descending`. -/
def firstBefore (a b : Nat) : Bool := descending.before a b

theorem firstBefore_decides :
    Regula.ExecutableContract firstBefore (fun run =>
      Regula.Decides (· = true)
        (fun input : Nat × Nat => descending.before input.1 input.2 = true)
        (Function.uncurry run)) :=
  ⟨.of_iff (fun _ => Iff.rfl) ⟨(1, 0), by decide⟩ ⟨(0, 1), by decide⟩⟩
