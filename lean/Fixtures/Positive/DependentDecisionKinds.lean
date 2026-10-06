/-
Positive control for decision kinds about functions with dependent or polymorphic types, at the
toolchain boundary: the collector reads each erasure and each field application from the term
Lean elaborates. Each registration below must be accepted and recorded with the kind its
requirement states: a two-way kind and each one-way kind about `Regula.Dependent.isSome` of a
function whose result type depends on its argument; a kind about `Regula.Dependent.val` of a
function that returns a value with a proof; a kind about a function with an argument whose type
depends on an earlier one, on a dependent pair; a kind about a function with a type argument at
its own universe parameter; a kind about a function with a proof argument, on a subtype;
`Function.uncurry` over the fields of a pair; and a kind reached only through an alias, about
`Regula.Dependent.isOk` of a three-argument function on a structure declared for its arguments.
Each function is registered with `@[regula_decision]`, so RG1008 must accept every one of them
through its contract. The closing theorem is the control of the second review's first finding:
a function that refuses every input has no two-way kind, whatever the acceptance predicate and
the specification.
-/
import Regula.Contract
import Regula.Decision

universe u

/-- The number itself, with a proof that it is positive, or nothing. -/
@[regula_decision] def positive? (n : Nat) : Option {m : Nat // m = n ∧ 0 < m} :=
  if h : 0 < n then some ⟨n, rfl, h⟩ else none

theorem positive?_isSome (n : Nat) : Regula.Dependent.isSome positive? n = true ↔ 0 < n := by
  unfold Regula.Dependent.isSome positive?
  split <;> simp_all

theorem positive?_decides :
    Regula.ExecutableContract positive? (fun parse =>
      Regula.Decides (· = true) (fun n => 0 < n) (Regula.Dependent.isSome parse)) :=
  ⟨.of_iff positive?_isSome ⟨1, (positive?_isSome 1).mpr (by decide)⟩
    ⟨0, fun accepted => absurd ((positive?_isSome 0).mp accepted) (by decide)⟩⟩

/-- An even number below four, with a proof that it is even: sound for evenness, and it refuses
the even `4`. -/
@[regula_decision] def smallEven? (n : Nat) : Option {m : Nat // m = n ∧ m % 2 = 0} :=
  if h : n % 2 = 0 ∧ n < 4 then some ⟨n, rfl, h.1⟩ else none

theorem smallEven?_decidesSoundly :
    Regula.ExecutableContract smallEven? (fun parse =>
      Regula.DecidesSoundly (· = true) (fun n => n % 2 = 0) (Regula.Dependent.isSome parse)) :=
  ⟨{ sound := fun n accepted => by
       unfold Regula.Dependent.isSome smallEven? at accepted
       split at accepted
       next h => exact h.1
       next => cases accepted
     accepted := ⟨0, by simp [Regula.Dependent.isSome, smallEven?]⟩ }⟩

/-- A number below ten, with that proof: complete for "below four", and it accepts `5`. -/
@[regula_decision] def belowTen? (n : Nat) : Option {m : Nat // m = n ∧ m < 10} :=
  if h : n < 10 then some ⟨n, rfl, h⟩ else none

theorem belowTen?_decidesCompletely :
    Regula.ExecutableContract belowTen? (fun parse =>
      Regula.DecidesCompletely (· = true) (fun n => n < 4) (Regula.Dependent.isSome parse)) :=
  ⟨{ complete := fun n holds => by
       have below : n < 10 := Nat.lt_trans holds (by decide)
       simp [Regula.Dependent.isSome, belowTen?, below]
     refused := ⟨10, by simp [Regula.Dependent.isSome, belowTen?]⟩ }⟩

/-- Whether a number is positive, with the proof that the flag says so. -/
@[regula_decision] def positiveFlag (n : Nat) : {flag : Bool // flag = true ↔ 0 < n} :=
  ⟨decide (0 < n), decide_eq_true_iff⟩

theorem positiveFlag_decides :
    Regula.ExecutableContract positiveFlag (fun check =>
      Regula.Decides (· = true) (fun n => 0 < n) (Regula.Dependent.val check)) :=
  ⟨.of_iff (Regula.Dependent.val_property positiveFlag) ⟨1, by decide⟩ ⟨0, by decide⟩⟩

/-- Whether an index below `limit + 1` is below three. The type of the second argument depends
on the first, and the result type on neither. -/
@[regula_decision] def low (limit : Nat) (index : Fin (limit + 1)) : Bool :=
  decide (index.val < 3)

theorem low_decides :
    Regula.ExecutableContract low (fun check =>
      Regula.Decides (· = true) (fun input => input.2.val < 3)
        (fun input : (limit : Nat) ×' Fin (limit + 1) => check input.1 input.2)) :=
  ⟨{ sound := fun _ accepted => of_decide_eq_true accepted
     accepted := ⟨⟨0, 0⟩, by decide⟩
     complete := fun _ holds => decide_eq_true holds
     refused := ⟨⟨3, 3⟩, by decide⟩ }⟩

/-- Whether a list of any element type has a member. -/
@[regula_decision] def inhabited {α : Type u} (items : List α) : Bool := !items.isEmpty

theorem inhabited_decides :
    Regula.ExecutableContract @inhabited.{u} (fun check =>
      Regula.Decides (· = true) (fun input => input.2 ≠ [])
        (fun input : (α : Type u) × List α => @check input.1 input.2)) :=
  ⟨.of_iff (fun input => by cases input.2 <;> simp [inhabited])
    ⟨⟨PUnit, [PUnit.unit]⟩, rfl⟩ ⟨⟨PUnit, []⟩, by simp [inhabited]⟩⟩

/-- Whether half of an even number is below three. The second argument is a proof about the
first. -/
@[regula_decision] def halfLow (n : Nat) (_even : n % 2 = 0) : Bool := decide (n / 2 < 3)

theorem halfLow_decides :
    Regula.ExecutableContract halfLow (fun check =>
      Regula.Decides (· = true) (fun input => input.val < 6)
        (fun input : {n : Nat // n % 2 = 0} => check input.1 input.2)) :=
  ⟨.of_iff (fun input => by simp only [halfLow, decide_eq_true_eq]; omega)
    ⟨⟨0, rfl⟩, by decide⟩ ⟨⟨6, rfl⟩, by decide⟩⟩

/-- Whether an index below `limit + 1` is below three, or is anything when `any`. -/
@[regula_decision] def lowOrAny (limit : Nat) (index : Fin (limit + 1)) (any : Bool) : Bool :=
  any || decide (index.val < 3)

/-- `Function.uncurry` over the fields of a dependent pair: the first two arguments form the
pair, and the third does not depend on them. -/
theorem lowOrAny_decides :
    Regula.ExecutableContract lowOrAny (fun check =>
      Regula.Decides (· = true) (fun input => input.2 = true ∨ input.1.2.val < 3)
        (Function.uncurry
          (fun input : (limit : Nat) ×' Fin (limit + 1) => check input.1 input.2))) :=
  ⟨.of_iff (fun input => by simp [Function.uncurry, lowOrAny])
    ⟨(⟨0, 0⟩, false), by decide⟩ ⟨(⟨3, 3⟩, false), by decide⟩⟩

/-- An index below `limit + 1` that is below three, or below four when `wide`, with a proof that
it is the supplied index. The result type depends on the first two arguments. -/
@[regula_decision] def lowIndex (limit : Nat) (index : Fin (limit + 1)) (wide : Bool) :
    Except String {found : Fin (limit + 1) // found = index} :=
  if index.val < (if wide then 4 else 3) then .ok ⟨index, rfl⟩ else .error "not low"

/-- The arguments of `lowIndex`, as the fields of one structure. -/
structure LowIndexInput where
  /-- The bound of the index. -/
  limit : Nat
  /-- The index, below `limit + 1`. -/
  index : Fin (limit + 1)
  /-- Whether the wider bound applies. -/
  wide : Bool

/-- A kind reached through an alias, about whether a three-argument function succeeds, on the
structure of its arguments. -/
def LowIndexContract
    (admit : (limit : Nat) → (index : Fin (limit + 1)) → Bool →
      Except String {found : Fin (limit + 1) // found = index}) : Prop :=
  Regula.Decides (· = true)
    (fun input : LowIndexInput => input.index.val < (if input.wide then 4 else 3))
    (Regula.Dependent.isOk fun input => admit input.limit input.index input.wide)

theorem lowIndex_decides : Regula.ExecutableContract lowIndex LowIndexContract :=
  ⟨.of_iff (fun input => by
      by_cases low : input.index.val < (if input.wide then 4 else 3) <;>
        simp [Regula.Dependent.isOk, lowIndex, low, Except.isOk, Except.toBool])
    ⟨⟨0, 0, false⟩, by decide⟩ ⟨⟨3, 3, false⟩, by decide⟩⟩

/-- The function of the second review's first finding: it refuses every input. -/
def never (_ : Bool) : Bool := false

/-- `never` has no two-way kind, whatever the acceptance predicate and the specification. -/
theorem never_not_decides (accepts : Bool → Prop) (spec : Bool → Prop) :
    ¬ Regula.Decides accepts spec never :=
  Regula.Decides.not_of_constant false
