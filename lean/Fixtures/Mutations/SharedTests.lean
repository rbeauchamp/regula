/-
Controls for the shared-test rule: each decision registration below shares a function with a
result of `Bool` or `BEq` between its specification and its implementation or its acceptance
predicate, so each must be refused, and the finding must name the function
(`RegulaPolicy.SharedNames.booleans`). `Fixtures.Positive.SharedDefinitions` has the accepted
controls.

* `smallEven_decides`: the specification and the function both call a helper with a result of
  `Bool`.
* `throughStatement_decides`: the specification reaches a helper through a definition of a
  proposition that is stated with the helper, and the function decides that proposition with
  `decide`. The instance that the function runs calls the helper.
* `sameItem_decides`: the specification and the function both use a derived `BEq`. The instance
  and the comparison function that Lean derived for it are named.
* `sameNat_decides`: the two sides share a `BEq` record that is a name for an instance of
  Lean's library, with no argument and no function abstraction in its value.
* `littleCheck_decides`: the two sides share a function whose result is `Box Prop`. The field
  of `Box` is read at the argument `Prop`, so the function is a statement, and the search reads
  its value: the helper with a result of `Bool` inside the statement is named.
* `same_decides`: the function does not use the helper. The acceptance predicate and the
  specification do.
* `unchanged_decides`: the function does not use the helper. The acceptance predicate is a
  named definition of a proposition that is stated with the helper, and the search reads the
  value of that definition.
* `noOdd_decides`: the wrapper. The two sides share a helper of the other class, which
  returns a list, and that helper calls a helper with a result of `Bool`. The search for a
  function with a result of `Bool` reads below the first helper, so the second is named, with
  the first in the class `other`.
* `deepOdd_decides`: the wrapper at a second level. The helper with a result of `Bool` is two
  shared functions of the other class below the specification.
-/
import Regula.Contract

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

/-- A second step around the first: the odd numbers of a list, in the other order. -/
def oddsLast (numbers : List Nat) : List Nat := (odds numbers).reverse

/-- Whether a list has no odd number: it calls `oddsLast`. -/
def deepOdd (numbers : List Nat) : Bool := (oddsLast numbers).isEmpty

theorem deepOdd_decides :
    Regula.ExecutableContract deepOdd
      (Regula.Decides (· = true) fun numbers => oddsLast numbers = []) :=
  ⟨.of_iff (fun numbers => by simp [deepOdd]) ⟨[2], by decide⟩ ⟨[1], by decide⟩⟩
