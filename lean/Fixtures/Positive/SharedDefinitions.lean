/-
Controls for the functions that the two sides of a decision registration share. The collector
refuses no registration for a shared function, so each registration below must be accepted. The
record of each registration must name the functions that its specification reaches first and
that its implementation reaches too, by class (`RegulaPolicy.SharedNames`):

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
