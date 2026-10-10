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
* `admit_named_decides`, `admit_through_decides` and `admit_every_decides`: the form of issue
  270, with the function of `Fixtures.Positive.SharedDefinitions`. The input holds a panel, which
  holds a meter whose invariant is stated with the test `settled`, and the function runs
  `settled`. The first specification names `settled` itself. The second names a definition of a
  proposition that is stated with `settled`, and the search reads its value. The third states a
  property of every meter, so it names the meter type as the binder of `∀`, and the search reads
  the declaration of that type, whose invariant names `settled`.
* `zeroTest_decides`: the specification reads the value of an opaque constant whose result type
  is a subtype stated with the test `isZero`. The search reads the type of an opaque constant, so
  it reaches `isZero`, and the specification is exactly `isZero n = true` on the input type `Nat`.
* `zeroAlways_decides`: the specification passes `always n` as the parameter of a structure to
  its projection function. The search reads the parameters of a projection, so it reaches the
  test `always` that the specification names.
* `admitBelow_decides`: a limit of the search. The specification reads the reading of the meter,
  a field of a field of the input. The type of that field is a structure that the search enters
  through the projection, and its invariant names `settled`.
* `admitPair_decides`: a limit of the search. The input is a pair, and its projections take the
  meter type as a parameter. The specification names the meter type there, and the search reads
  its declaration.
* `admitAt_decides`: a limit of the search. The specification reads a meter of an array of the
  input by its index. The instance of `GetElem` for an array takes the meter type as an
  argument, and the search reads the declaration of the meter type.
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
  /-- The limit of the amount. -/
  limit : Nat

/-- Whether the amount is below the limit. It runs the test `settled` on the meter. -/
def admit (panel : Panel) (amount limit : Nat) : Bool :=
  settled panel.meter.level && decide (amount < limit)

/-- The function accepts exactly an amount below the limit: the invariant gives `settled`. -/
theorem admit_iff (panel : Panel) (amount limit : Nat) :
    admit panel amount limit = true ↔ amount < limit := by
  simp [admit, panel.meter.settled_level]

theorem admit_named_decides : Regula.ExecutableContract admit (fun run =>
    Regula.Decides (· = true)
      (fun input : AdmitInput =>
        settled input.panel.meter.level = true ∧ input.amount < input.limit)
      (fun input : AdmitInput => run input.panel input.amount input.limit)) :=
  ⟨.of_iff (fun input => by simp [admit_iff, input.panel.meter.settled_level])
    ⟨⟨⟨⟨5, by decide⟩⟩, 1, 3⟩, by decide⟩ ⟨⟨⟨⟨5, by decide⟩⟩, 7, 3⟩, by decide⟩⟩

/-- A statement that is stated with the helper `settled`. -/
def Settled (meter : Meter) : Prop := settled meter.level = true

theorem admit_through_decides : Regula.ExecutableContract admit (fun run =>
    Regula.Decides (· = true)
      (fun input : AdmitInput => Settled input.panel.meter ∧ input.amount < input.limit)
      (fun input : AdmitInput => run input.panel input.amount input.limit)) :=
  ⟨.of_iff (fun input => by simp [admit_iff, Settled, input.panel.meter.settled_level])
    ⟨⟨⟨⟨5, by decide⟩⟩, 1, 3⟩, by decide⟩ ⟨⟨⟨⟨5, by decide⟩⟩, 7, 3⟩, by decide⟩⟩

theorem admit_every_decides : Regula.ExecutableContract admit (fun run =>
    Regula.Decides (· = true)
      (fun input : AdmitInput => input.amount < input.limit ∧ ∀ meter : Meter, meter.level < 10)
      (fun input : AdmitInput => run input.panel input.amount input.limit)) :=
  ⟨.of_iff (fun input => by
      rw [admit_iff]
      exact ⟨fun below => ⟨below, fun meter => by simpa [settled] using meter.settled_level⟩,
        And.left⟩)
    ⟨⟨⟨⟨5, by decide⟩⟩, 1, 3⟩, (admit_iff _ _ _).mpr (by decide)⟩
    ⟨⟨⟨⟨5, by decide⟩⟩, 7, 3⟩, fun accepted => absurd ((admit_iff _ _ _).mp accepted) (by decide)⟩⟩

/-- A sixth helper with a result of `Bool`. -/
def isZero (n : Nat) : Bool := decide (n = 0)

/-- An opaque value whose type states that it is `isZero n`. -/
opaque witness (n : Nat) : {b : Bool // b = isZero n} := ⟨isZero n, rfl⟩

/-- Whether `n` is zero: it calls `isZero`. -/
def zeroTest (n : Nat) : Bool := isZero n

theorem zeroTest_decides : Regula.ExecutableContract zeroTest
    (Regula.Decides (· = true) fun n => (witness n).val = true) :=
  ⟨.of_iff (fun n => by rw [(witness n).property]; rfl) ⟨0, by decide⟩ ⟨1, by decide⟩⟩

/-- A record of a number, indexed by a flag. -/
structure Tag (flag : Bool) where
  /-- The number. -/
  value : Nat

/-- The tag of zero, at the flag `true`. -/
def zeroTag : Tag true := ⟨0⟩

/-- A seventh helper with a result of `Bool`: it accepts each number. -/
def always (_ : Nat) : Bool := true

/-- Whether `n` is zero: it calls `always`. -/
def zeroAlways (n : Nat) : Bool := always n && decide (n = 0)

theorem zeroAlways_decides : Regula.ExecutableContract zeroAlways
    (Regula.Decides (· = true) fun n => @Tag.value (always n) zeroTag = 0 ∧ n = 0) :=
  ⟨.of_iff (fun n => by simp [zeroAlways, always, zeroTag]) ⟨0, by decide⟩ ⟨1, by decide⟩⟩

/-- The arguments of `admitBelow`, in order. -/
structure BelowInput where
  /-- The panel. -/
  panel : Panel
  /-- The requested amount. -/
  amount : Nat

/-- Whether the amount is below the reading of the meter. It runs `settled`. -/
def admitBelow (panel : Panel) (amount : Nat) : Bool :=
  settled panel.meter.level && decide (amount < panel.meter.level)

theorem admitBelow_decides : Regula.ExecutableContract admitBelow (fun run =>
    Regula.Decides (· = true)
      (fun input : BelowInput => input.amount < input.panel.meter.level)
      (fun input : BelowInput => run input.panel input.amount)) :=
  ⟨.of_iff (fun input => by simp [admitBelow, input.panel.meter.settled_level])
    ⟨⟨⟨⟨5, by decide⟩⟩, 1⟩, by decide⟩ ⟨⟨⟨⟨5, by decide⟩⟩, 7⟩, by decide⟩⟩

/-- Whether the amount is below the reading of a meter, with the input as a pair. -/
def admitPair (meter : Meter) (amount : Nat) : Bool :=
  settled meter.level && decide (amount < meter.level)

theorem admitPair_decides : Regula.ExecutableContract admitPair (fun run =>
    Regula.Decides (· = true) (fun input : Meter × Nat => input.2 < input.1.level)
      (Function.uncurry run)) :=
  ⟨.of_iff (fun input => by simp [Function.uncurry, admitPair, input.1.settled_level])
    ⟨(⟨5, by decide⟩, 1), by decide⟩ ⟨(⟨5, by decide⟩, 7), by decide⟩⟩

/-- An array of meters with the index of one of them. -/
structure Bank where
  /-- The meters. -/
  meters : Array Meter
  /-- The index of a meter. -/
  index : Fin meters.size

/-- The arguments of `admitAt`, in order. -/
structure AtInput where
  /-- The bank. -/
  bank : Bank
  /-- The requested amount. -/
  amount : Nat

/-- Whether the amount is below the reading of the meter at the index. It runs `settled`. -/
def admitAt (bank : Bank) (amount : Nat) : Bool :=
  admitBelow ⟨bank.meters[bank.index]⟩ amount

theorem admitAt_decides : Regula.ExecutableContract admitAt (fun run =>
    Regula.Decides (· = true)
      (fun input : AtInput => input.amount < input.bank.meters[input.bank.index].level)
      (fun input : AtInput => run input.bank input.amount)) :=
  ⟨.of_iff (fun input => by
      simp only [admitAt, admitBelow, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨And.right, fun below => ⟨Meter.settled_level _, below⟩⟩)
    ⟨⟨⟨#[⟨5, by decide⟩], ⟨0, by decide⟩⟩, 1⟩, by decide⟩
    ⟨⟨⟨#[⟨5, by decide⟩], ⟨0, by decide⟩⟩, 7⟩, by decide⟩⟩
