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
* `admit_named_decides`, `admit_through_decides` and `admit_every_decides`: the input holds a
  panel, which holds a meter whose invariant is stated with the test `settled`, and the function
  runs `settled`. The first specification names `settled` itself. The second names a definition
  of a proposition that is stated with `settled`, and the search reads its value. The third states
  a property of every meter, so it is about the values of the meter type, and the search reads
  the declaration of that type, whose invariant names `settled`.
* `admitAt_decides`: a limit of the search. The specification reads a meter of an array of the
  input by its index. The instance of `GetElem` for an array takes the meter type as an
  argument, and the search reads the arguments of every function that is no projection of a
  field, so it reads the declaration of the meter type.
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

/-- A fifth helper with a result of `Bool`. -/
def settled (n : Nat) : Bool := decide (n < 10)

/-- A meter whose invariant is stated with the test `settled`. -/
structure Meter where
  /-- The reading. -/
  level : Nat
  /-- The reading is settled. -/
  settled_level : settled level = true

/-- A panel that holds a meter. -/
structure Panel where
  /-- The meter. -/
  meter : Meter

/-- The arguments of `admit`, in order. -/
structure AdmitInput where
  /-- The panel. -/
  panel : Panel
  /-- The requested amount. -/
  amount : Nat

/-- Whether the amount is below the reading of the meter. It runs the test `settled`. -/
def admit (panel : Panel) (amount : Nat) : Bool :=
  settled panel.meter.level && decide (amount < panel.meter.level)

/-- The function accepts exactly an amount below the reading: the invariant gives `settled`. -/
theorem admit_iff (panel : Panel) (amount : Nat) :
    admit panel amount = true ↔ amount < panel.meter.level := by
  simp [admit, panel.meter.settled_level]

theorem admit_named_decides : Regula.ExecutableContract admit (fun run =>
    Regula.Decides (· = true)
      (fun input : AdmitInput =>
        settled input.panel.meter.level = true ∧ input.amount < input.panel.meter.level)
      (fun input : AdmitInput => run input.panel input.amount)) :=
  ⟨.of_iff (fun input => by simp [admit_iff, input.panel.meter.settled_level])
    ⟨⟨⟨⟨5, by decide⟩⟩, 1⟩, by decide⟩ ⟨⟨⟨⟨5, by decide⟩⟩, 7⟩, by decide⟩⟩

/-- A statement that is stated with the helper `settled`. -/
def Settled (meter : Meter) : Prop := settled meter.level = true

theorem admit_through_decides : Regula.ExecutableContract admit (fun run =>
    Regula.Decides (· = true)
      (fun input : AdmitInput => Settled input.panel.meter ∧ input.amount < input.panel.meter.level)
      (fun input : AdmitInput => run input.panel input.amount)) :=
  ⟨.of_iff (fun input => by simp [admit_iff, Settled, input.panel.meter.settled_level])
    ⟨⟨⟨⟨5, by decide⟩⟩, 1⟩, by decide⟩ ⟨⟨⟨⟨5, by decide⟩⟩, 7⟩, by decide⟩⟩

theorem admit_every_decides : Regula.ExecutableContract admit (fun run =>
    Regula.Decides (· = true)
      (fun input : AdmitInput =>
        input.amount < input.panel.meter.level ∧ ∀ meter : Meter, meter.level < 10)
      (fun input : AdmitInput => run input.panel input.amount)) :=
  ⟨.of_iff (fun input => by
      rw [admit_iff]
      exact ⟨fun below => ⟨below, fun meter => by simpa [settled] using meter.settled_level⟩,
        And.left⟩)
    ⟨⟨⟨⟨5, by decide⟩⟩, 1⟩, (admit_iff _ _).mpr (by decide)⟩
    ⟨⟨⟨⟨5, by decide⟩⟩, 7⟩, fun accepted => absurd ((admit_iff _ _).mp accepted) (by decide)⟩⟩

/-- An array of meters with the index of one of them. -/
structure Bank where
  /-- The meters. -/
  meters : Array Meter
  /-- The index of a meter. -/
  index : Fin meters.size

/-- Whether the amount is below the reading of the meter at the index. It runs `settled`. -/
def admitAt (bank : Bank) (amount : Nat) : Bool := admit ⟨bank.meters[bank.index]⟩ amount

/-- The arguments of `admitAt`, in order. -/
structure AtInput where
  /-- The bank. -/
  bank : Bank
  /-- The requested amount. -/
  amount : Nat

theorem admitAt_decides : Regula.ExecutableContract admitAt (fun run =>
    Regula.Decides (· = true)
      (fun input : AtInput => input.amount < input.bank.meters[input.bank.index].level)
      (fun input : AtInput => run input.bank input.amount)) :=
  ⟨.of_iff (fun input => admit_iff _ _)
    ⟨⟨⟨#[⟨5, by decide⟩], ⟨0, by decide⟩⟩, 1⟩, by decide⟩
    ⟨⟨⟨#[⟨5, by decide⟩], ⟨0, by decide⟩⟩, 7⟩, by decide⟩⟩
