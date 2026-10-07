/-
Controls for the functions that the two sides of a decision registration share. The collector
refuses no registration for a shared function, so each registration below must be accepted. The
record of each registration must name the functions that its specification reaches first and
that its implementation or its acceptance predicate reaches too, by class
(`RegulaPolicy.SharedNames`):

* `apart_decides`: the specification states a proposition, and the function decides it with a
  test of Lean's library. No function is named.
* `smallEven_decides`: the specification and the function both call a helper with a result of
  `Bool`. The helper is named in the class `boolean`.
* `throughStatement_decides`: the specification reaches a helper through a definition of a
  proposition, and the function decides that proposition with `decide`. The instance that the
  function runs calls the helper, so the helper is named in the class `boolean`.
* `sameItem_decides`: the specification and the function both use a derived `BEq`. The instance
  is named in the class `boolean`.
* `noEven_decides`: the form of `marks` in issue 249. A helper prepares the input of the two
  sides, and its result is a list. The helper is named in the class `other`.
* `below_decides`: the two sides share a definition of a proposition, its `Decidable` instance
  and a constant. No function is named.
* `knownSign_decides`: the two sides share a closed list whose value has a function
  abstraction. The list takes no argument, so it is no function and is not named.
* `sameNat_decides`: the two sides share a `BEq` record that is a name for an instance of
  Lean's library, with no argument and no function abstraction in its value. It is named in the
  class `boolean`.
* `littleCheck_decides`: the two sides share a function whose result is `Box Prop`. The field
  of `Box` is read at the argument `Prop`, so the function is a statement and is not named, and
  the search reads its value: the helper with a result of `Bool` inside the statement is named.
* `same_decides`: the function does not use the helper. The acceptance predicate and the
  specification do, and the helper is named in the class `boolean`.
* `unchanged_decides`: the function does not use the helper. The acceptance predicate is a
  named definition of a proposition that is stated with the helper. The search reads the value
  of that definition, so the helper is named in the class `boolean`.
* `firstBefore_decides`: the two sides share a record of one function, with no argument. Its
  type has a field that takes an argument, so it is a function, named in the class `other`.
* `noOdd_decides`: the two sides share a helper of the class `other` that calls a helper of
  this file with a result of `Bool`. The search stops at the first helper: it is named, and the
  helper below it is not, so the list of the class `boolean` is empty.
-/
import Regula.Contract

/-- Whether `n` is below four. -/
def apart (n : Nat) : Bool := decide (n < 4)

theorem apart_decides :
    Regula.ExecutableContract apart (Regula.Decides (· = true) fun n => n < 4) :=
  ⟨.of_iff (fun n => by simp [apart]) ⟨0, by decide⟩ ⟨4, by decide⟩⟩

/-- A helper with a result of `Bool`. -/
def small (n : Nat) : Bool := decide (n < 4)

/-- Whether `n` is an even number below four: it calls `small`. -/
def smallEven (n : Nat) : Bool := small n && decide (n % 2 = 0)

theorem smallEven_decides :
    Regula.ExecutableContract smallEven
      (Regula.Decides (· = true) fun n => small n = true ∧ n % 2 = 0) :=
  ⟨.of_iff (fun n => by simp [smallEven]) ⟨0, by decide⟩ ⟨1, by decide⟩⟩

/-- A second helper with a result of `Bool`. -/
def tiny (n : Nat) : Bool := decide (n < 2)

/-- A statement that is stated with the helper `tiny`. -/
def Tiny (n : Nat) : Prop := tiny n = true

instance (n : Nat) : Decidable (Tiny n) := by
  unfold Tiny
  infer_instance

/-- Decides `Tiny` with its instance, which calls `tiny`. -/
def throughStatement (n : Nat) : Bool := decide (Tiny n)

theorem throughStatement_decides :
    Regula.ExecutableContract throughStatement (Regula.Decides (· = true) Tiny) :=
  ⟨.of_iff (fun n => by simp [throughStatement]) ⟨0, by decide⟩ ⟨2, by decide⟩⟩

/-- A record with a derived `BEq`. -/
structure Item where
  /-- The number of the item. -/
  id : Nat
  deriving BEq

/-- Whether two items are the same by the derived `BEq`. -/
def sameItem (a b : Item) : Bool := a == b

theorem sameItem_decides :
    Regula.ExecutableContract sameItem (fun run =>
      Regula.Decides (· = true) (fun input : Item × Item => (input.1 == input.2) = true)
        (Function.uncurry run)) :=
  ⟨.of_iff (fun _ => Iff.rfl) ⟨(⟨0⟩, ⟨0⟩), by decide⟩ ⟨(⟨0⟩, ⟨1⟩), by decide⟩⟩

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

/-- A `BEq` record that is a name for an instance of Lean's library. -/
@[instance_reducible] def eqForNat : BEq Nat := inferInstance

/-- Whether two numbers are the same by `eqForNat`. -/
def sameNat (a b : Nat) : Bool := eqForNat.beq a b

theorem sameNat_decides :
    Regula.ExecutableContract sameNat (fun run =>
      Regula.Decides (· = true) (fun input : Nat × Nat => eqForNat.beq input.1 input.2 = true)
        (Function.uncurry run)) :=
  ⟨.of_iff (fun _ => Iff.rfl) ⟨(0, 0), by decide⟩ ⟨(0, 1), by decide⟩⟩

/-- A record of one value of any type. -/
structure Box (α : Type) where
  /-- The value. -/
  value : α

/-- A third helper with a result of `Bool`. -/
def little (n : Nat) : Bool := decide (n < 3)

/-- A statement in a record: the result type is `Box Prop`. -/
def boxed (n : Nat) : Box Prop := ⟨little n = true⟩

instance (n : Nat) : Decidable (boxed n).value := by
  unfold boxed
  infer_instance

/-- Decides the statement of `boxed` with its instance, which calls `little`. -/
def littleCheck (n : Nat) : Bool := decide (boxed n).value

theorem littleCheck_decides :
    Regula.ExecutableContract littleCheck
      (Regula.Decides (· = true) fun n => (boxed n).value) :=
  ⟨.of_iff (fun n => by simp [littleCheck]) ⟨0, by decide⟩ ⟨3, by decide⟩⟩

/-- Returns its argument: it calls no helper. -/
def same (n : Nat) : Nat := n

theorem same_decides :
    Regula.ExecutableContract same
      (Regula.Decides (fun result => small result = true) fun n => small n = true) :=
  ⟨.of_iff (fun _ => Iff.rfl) ⟨0, by decide⟩ ⟨4, by decide⟩⟩

/-- A statement that is stated with the helper `small`. -/
def Small (n : Nat) : Prop := small n = true

/-- Returns its argument: it calls no helper. -/
def unchanged (n : Nat) : Nat := n

theorem unchanged_decides :
    Regula.ExecutableContract unchanged (Regula.Decides Small fun n => small n = true) :=
  ⟨.of_iff (fun _ => Iff.rfl) ⟨0, (by decide : small 0 = true)⟩
    ⟨4, (by decide : ¬ small 4 = true)⟩⟩

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

/-- A fourth helper with a result of `Bool`. -/
def odd (n : Nat) : Bool := decide (n % 2 = 1)

/-- A step that prepares the input with the helper `odd`: the odd numbers of a list. -/
def odds (numbers : List Nat) : List Nat := numbers.filter odd

/-- Whether a list has no odd number: it calls `odds`. -/
def noOdd (numbers : List Nat) : Bool := (odds numbers).isEmpty

theorem noOdd_decides :
    Regula.ExecutableContract noOdd
      (Regula.Decides (· = true) fun numbers => odds numbers = []) :=
  ⟨.of_iff (fun numbers => by simp [noOdd]) ⟨[2], by decide⟩ ⟨[1], by decide⟩⟩
