import Lean.Data.Json
import Std.Data.TreeMap.Raw.AdditionalOperations
import RegulaPolicy.Guards
import Regula.Contract
import Regula.Decision

/-! # Agreement of a JSON value with an encoding

A decoder that fails closed compares its input with the canonical encoding of what it decoded,
so an unknown member and a stale redundant member are refused. Lean's own `Json` equality is
`partial`: no proof unfolds it, so no theorem says what a decoder that runs it accepts. `agrees`
is the comparison that those decoders run in its place. It is the procedure of that equality,
written as a total function by structural recursion: the same constructor, equal Booleans,
numbers and strings, array elements that agree in order, and for two objects the same number of
members, with each member of the first looked up by its name in the second. `agrees_iff` proves
that it answers `true` exactly for the pairs that `Agree` relates, and `Agree` states that
procedure with one constructor for each case.

The comparison is not symmetric in its two objects. It reads each member of the first tree, node
by node, and it looks the name up in the second tree. So the first value can be an object tree
that is not a search tree: no lookup reads it. Such a tree can give one name twice and lack
another name (https://github.com/rbeauchamp/regula/issues/269). A decoder therefore runs
`conforms`, which also requires each object tree of its input to be a search tree (`Regular`,
decided by `regular`, `regular_iff`). `canonical` is that decoder, for each reader and each
encoder.

**Not claimed.** That `agrees` returns what Lean's runtime equality returns: that function is
`partial`, so no theorem mentions it. The two have the same cases, read from the two
definitions (`Lean.Json.beq'` in `Lean/Data/Json/Basic.lean`), and a comparison of the two over
pairs of values is evidence for those pairs only. The relation is about `Json` values: what a
text parser returns for a text is outside it.

The module also has what a decoder needs to state the form of an encoded value without an
encoder. `Shaped` says that an object is a search tree, which members it has and what the value
of each is. `Shaped.of_members` proves it for an object that an encoder builds,
`Shaped.agree_of_members` proves that a value of the form agrees with such an object,
`Shaped.regular` proves that it has search trees, and `Shaped.of_agree` proves the converse for
a value whose object trees are search trees. `get?_of_mem` is the lemma about Lean's lookup
that these use: in a search tree, each member is found by its name.

The module is in the claimed library `RegulaCore`, so claimed code can run `conforms` too.
`Fields` and `Cases`, the induction over a value and the object trees inside it, are here for the
same reason. `regula init` runs `conforms` on the starter manifest (`Regula.Cli.Setup`). -/
namespace Regula.JsonAgreement
open Lean
open Std.DTreeMap.Internal (Impl)

/-- The fields of a JSON object, as `Json.obj` stores them. -/
abbrev Fields := Impl String (fun _ => Json)

private theorem sizeOf_lt_arr {value : Json} {elems : Array Json} (h : value ∈ elems) :
    sizeOf value < sizeOf (Json.arr elems) := by
  have := Array.sizeOf_lt_of_mem h
  simp only [Json.arr.sizeOf_spec]
  omega

/-- The cases of an induction over a JSON value and the object trees inside it. -/
structure Cases (motive : Json → Prop) (fieldsMotive : Fields → Prop) : Prop where
  /-- `null`. -/
  null : motive .null
  /-- A boolean. -/
  bool : ∀ b, motive (.bool b)
  /-- A number. -/
  num : ∀ n, motive (.num n)
  /-- A string. -/
  str : ∀ s, motive (.str s)
  /-- An array whose elements have the property. -/
  arr : ∀ elems : Array Json, (∀ value ∈ elems, motive value) → motive (.arr elems)
  /-- An object whose fields have the property. -/
  obj : ∀ fields : Fields, fieldsMotive fields → motive (.obj ⟨⟨fields⟩⟩)
  /-- The empty tree. -/
  leaf : fieldsMotive .leaf
  /-- A tree node whose value and subtrees have the property. -/
  inner : ∀ size key value left right, motive value → fieldsMotive left → fieldsMotive right →
    fieldsMotive (.inner size key value left right)

mutual
/-- Induction over a JSON value, through the object trees inside it. -/
theorem Cases.value {motive : Json → Prop} {fieldsMotive : Fields → Prop}
    (cases : Cases motive fieldsMotive) : ∀ value : Json, motive value
  | .null => cases.null
  | .bool b => cases.bool b
  | .num n => cases.num n
  | .str s => cases.str s
  | .arr elems => cases.arr elems fun value _ => cases.value value
  | .obj ⟨⟨fields⟩⟩ => cases.obj fields (cases.fields fields)
termination_by value => sizeOf value
decreasing_by
  · exact sizeOf_lt_arr ‹_›
  · simp only [Json.obj.sizeOf_spec, Std.TreeMap.Raw.mk.sizeOf_spec,
      Std.DTreeMap.Raw.mk.sizeOf_spec]
    omega
/-- Induction over an object tree, through the JSON values inside it. -/
theorem Cases.fields {motive : Json → Prop} {fieldsMotive : Fields → Prop}
    (cases : Cases motive fieldsMotive) : ∀ fields : Fields, fieldsMotive fields
  | .leaf => cases.leaf
  | .inner size key value left right =>
      cases.inner size key value left right (cases.value value) (cases.fields left)
        (cases.fields right)
termination_by fields => sizeOf fields
end

/-- The members of an object tree in the order of the tree: the left subtree, the node, the right
subtree. It is Std's `Impl.toListModel`, with each dependent pair written as a pair. -/
def members (fields : Fields) : List (String × Json) :=
  fields.toListModel.map fun member => (member.1, member.2)

@[simp] theorem members_leaf : members .leaf = [] := rfl

@[simp] theorem members_inner (size : Nat) (key : String) (value : Json) (left right : Fields) :
    members (.inner size key value left right) =
      members left ++ (key, value) :: members right := by
  simp [members]

/-- The number of the members of an object tree: one for each node. The size that a node records
is not read. -/
def count : Fields → Nat
  | .leaf => 0
  | .inner _ _ _ left right => count left + 1 + count right

/-- The number of the members is the length of their list. -/
theorem count_eq_length (fields : Fields) : count fields = (members fields).length := by
  induction fields with
  | leaf => rfl
  | inner size key value left right leftStep rightStep =>
    simp only [count, members_inner, List.length_append, List.length_cons, leftStep, rightStep]
    omega

/-! ### Search trees, decided -/

/-- The names of the members go up in the order of the tree: the tree is a search tree. It is
Std's `Impl.Ordered` (`ordered_iff`). -/
def Ordered (fields : Fields) : Prop := fields.Ordered

/-- `Ordered` over `members`: the names go up in the order of the tree. -/
theorem ordered_iff (fields : Fields) :
    Ordered fields ↔
      (members fields).Pairwise fun earlier later => compare earlier.1 later.1 = .lt := by
  simp [Ordered, Std.DTreeMap.Internal.Impl.Ordered, members, List.pairwise_map]

/-- Each object tree in the value, at each depth, is a search tree: the names of its members go
up in the order of the tree. -/
inductive Regular : Json → Prop
  /-- `null` has no object. -/
  | null : Regular .null
  /-- A Boolean has no object. -/
  | bool (value : Bool) : Regular (.bool value)
  /-- A number has no object. -/
  | num (value : JsonNumber) : Regular (.num value)
  /-- A string has no object. -/
  | str (value : String) : Regular (.str value)
  /-- An array of values with this property. -/
  | arr {elements : Array Json} : (∀ value ∈ elements, Regular value) → Regular (.arr elements)
  /-- A search tree whose members have values with this property. -/
  | obj {fields : Fields} : Ordered fields → (∀ member ∈ members fields, Regular member.2) →
      Regular (.obj ⟨⟨fields⟩⟩)

/-- Whether each name of the list comes before the name after it (`ascending_iff`). -/
def ascending : List String → Bool
  | first :: second :: rest => compare first second == .lt && ascending (second :: rest)
  | _ => true

/-- Each name comes before the name after it exactly when each name comes before every later
name: the order of strings is transitive. -/
theorem ascending_iff (names : List String) :
    ascending names = true ↔ names.Pairwise fun earlier later => compare earlier later = .lt := by
  induction names with
  | nil => simp [ascending]
  | cons first rest step =>
    cases rest with
    | nil => simp [ascending]
    | cons second more =>
      simp only [ascending, Bool.and_eq_true, beq_iff_eq, step, List.pairwise_cons]
      constructor
      · rintro ⟨less, laterAll, tail⟩
        refine ⟨fun name present => ?_, laterAll, tail⟩
        rcases List.mem_cons.mp present with rfl | inMore
        · exact less
        · exact Std.TransCmp.lt_trans less (laterAll name inMore)
      · rintro ⟨firstAll, laterAll, tail⟩
        exact ⟨firstAll second List.mem_cons_self, laterAll, tail⟩

mutual
/-- Whether each object tree in the value, at each depth, is a search tree (`Regular`, by
`regular_iff`): the names of the members of each object go up in the order of its tree. -/
def regular (j : Json) : Bool :=
  match j with
  | .arr ⟨elements⟩ => regularAll elements
  | .obj ⟨⟨fields⟩⟩ => ascending ((members fields).map (·.1)) && regularFields fields
  | _ => true
termination_by structural j
/-- `regular` on each element of a list. -/
def regularAll (elements : List Json) : Bool :=
  match elements with
  | [] => true
  | head :: rest => regular head && regularAll rest
termination_by structural elements
/-- `regular` on the value of each member of an object tree. -/
def regularFields (fields : Fields) : Bool :=
  match fields with
  | .leaf => true
  | .inner _ _ value left right => regular value && regularFields left && regularFields right
termination_by structural fields
end

theorem regular_registered : Regula.RegisteredDecision @regular := ⟨⟩

/-- **`regular` answers `true` exactly for the values whose object trees are search trees.** -/
theorem regular_iff (j : Json) : regular j = true ↔ Regular j := by
  refine Cases.value (motive := fun j => regular j = true ↔ Regular j)
    (fieldsMotive := fun fields =>
      regularFields fields = true ↔ ∀ member ∈ members fields, Regular member.2) ?_ j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun _ => .null, fun _ => by simp [regular]⟩
  · exact fun value => ⟨fun _ => .bool value, fun _ => by simp [regular]⟩
  · exact fun value => ⟨fun _ => .num value, fun _ => by simp [regular]⟩
  · exact fun value => ⟨fun _ => .str value, fun _ => by simp [regular]⟩
  · intro elems elements
    obtain ⟨elems⟩ := elems
    have all : ∀ items : List Json, (∀ value ∈ items, value ∈ elems) →
        (regularAll items = true ↔ ∀ value ∈ items, Regular value) := by
      intro items
      induction items with
      | nil => exact fun _ => ⟨(fun _ _ member => nomatch member), fun _ => by simp [regularAll]⟩
      | cons head rest step =>
        intro inside
        have heads := elements head (Array.mem_def.mpr (inside head List.mem_cons_self))
        have rests := step fun value member => inside value (List.mem_cons_of_mem _ member)
        simp only [regularAll, Bool.and_eq_true, heads, rests, List.forall_mem_cons]
    simp only [regular, all elems fun _ member => member]
    constructor
    · exact fun each => .arr fun value member => each value (Array.mem_def.mp member)
    · intro h
      cases h with
      | arr each => exact fun value member => each value (Array.mem_def.mpr member)
  · intro fields step
    simp only [regular, Bool.and_eq_true, ascending_iff, List.pairwise_map, step]
    constructor
    · exact fun ⟨ordered, values⟩ => .obj ((ordered_iff _).mpr ordered) values
    · intro h
      cases h with
      | obj ordered values => exact ⟨(ordered_iff _).mp ordered, values⟩
  · exact ⟨(fun _ _ member => nomatch member), fun _ => by simp [regularFields]⟩
  · intro size key value left right valueStep leftStep rightStep
    simp only [regularFields, Bool.and_eq_true, valueStep, leftStep, rightStep, members_inner,
      List.mem_append, List.mem_cons]
    constructor
    · rintro ⟨⟨here, lefts⟩, rights⟩ member (inLeft | rfl | inRight)
      · exact lefts member inLeft
      · exact here
      · exact rights member inRight
    · intro all
      exact ⟨⟨all _ (.inr (.inl rfl)), fun member present => all member (.inl present)⟩,
        fun member present => all member (.inr (.inr present))⟩

/-- `regular` is a sound and complete decision of `Regular` (`regular_iff`): it accepts `null`,
and it refuses an object of two members whose names do not go up in the order of its tree. The
specification is a relation with one constructor for each case of a value. -/
theorem checked_regular : Regula.ExecutableContract regular (fun test =>
    Regula.Decides (· = true) Regular test) :=
  ⟨Regula.Decides.of_iff regular_iff ⟨.null, by decide⟩
    ⟨.obj ⟨⟨.inner 2 "a" .null (.inner 1 "b" .null .leaf .leaf) .leaf⟩⟩, by decide⟩⟩

/-- `regular` decides `Regular`, so a check can state the proposition and run `decide`, whose
instance runs `regular`. -/
instance (j : Json) : Decidable (Regular j) := decidable_of_iff _ (regular_iff j)

/-- An object is a value with search trees when its members in the order of its tree are
`written`, the names go up, and the value of each member is a value with search trees. -/
theorem Regular.obj_of_members (fields : Std.TreeMap.Raw String Json compare)
    (written : List (String × Json)) (sorted : members fields.inner.inner = written)
    (each : ∀ member ∈ written, Regular member.2)
    (increasing : (written.map (·.1)).Pairwise fun earlier later => compare earlier later = .lt) :
    Regular (.obj fields) := by
  obtain ⟨⟨tree⟩⟩ := fields
  refine .obj ?_ fun member present => each member (sorted ▸ present)
  rw [ordered_iff, sorted]
  exact List.pairwise_map.mp increasing

mutual
/-- Whether the first JSON value agrees with the second: the same constructor, equal Booleans,
numbers and strings, array elements that agree in order, and for two objects the same number of
members, with each member of the first found by its name in the second with a value that it
agrees with (`Agree`, by `agrees_iff`). -/
def agrees (a b : Json) : Bool :=
  match a, b with
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => a == b
  | .str a, .str b => a == b
  | .arr ⟨a⟩, .arr ⟨b⟩ => agreesAll a b
  | .obj ⟨⟨a⟩⟩, .obj b => count a == count b.inner.inner && agreesFields a b
  | _, _ => false
termination_by structural a
/-- `agrees` on the elements of two arrays, in order. -/
def agreesAll (a b : List Json) : Bool :=
  match a, b with
  | [], [] => true
  | head :: rest, other :: others => agrees head other && agreesAll rest others
  | _, _ => false
termination_by structural a
/-- Whether each member of the tree `a` is found by its name in the object `b`, with a value that
it agrees with. -/
def agreesFields (a : Fields) (b : Std.TreeMap.Raw String Json compare) : Bool :=
  match a with
  | .leaf => true
  | .inner _ key value left right =>
      (match b.get? key with
       | some other => agrees value other
       | none => false) && agreesFields left b && agreesFields right b
termination_by structural a
end

theorem agrees_registered : Regula.RegisteredDecision @agrees := ⟨⟩

mutual
/-- The first JSON value agrees with the second: one constructor for each case of `agrees`. -/
inductive Agree : Json → Json → Prop
  /-- `null` agrees with `null`. -/
  | null : Agree .null .null
  /-- A Boolean agrees with the same Boolean. -/
  | bool (value : Bool) : Agree (.bool value) (.bool value)
  /-- A number agrees with the same number: the same mantissa and the same exponent. -/
  | num (value : JsonNumber) : Agree (.num value) (.num value)
  /-- A string agrees with the same string. -/
  | str (value : String) : Agree (.str value) (.str value)
  /-- An array agrees with an array when their elements agree in order. -/
  | arr {a b : List Json} : AgreeAll a b → Agree (.arr ⟨a⟩) (.arr ⟨b⟩)
  /-- An object agrees with an object of the same number of members in which each of its members
  is found. -/
  | obj {a : Fields} {b : Std.TreeMap.Raw String Json compare} :
      count a = count b.inner.inner → AgreeFields a b → Agree (.obj ⟨⟨a⟩⟩) (.obj b)
/-- Two lists of JSON values have the same length, and each element of the first agrees with the
element of the second at its place. -/
inductive AgreeAll : List Json → List Json → Prop
  /-- The empty lists. -/
  | nil : AgreeAll [] []
  /-- A head that agrees with a head, before a tail that agrees with a tail. -/
  | cons {head other : Json} {rest others : List Json} :
      Agree head other → AgreeAll rest others → AgreeAll (head :: rest) (other :: others)
/-- Each member of an object tree is found by its name in an object, with a value that it agrees
with. -/
inductive AgreeFields : Fields → Std.TreeMap.Raw String Json compare → Prop
  /-- The empty tree has no member. -/
  | leaf (b : Std.TreeMap.Raw String Json compare) : AgreeFields .leaf b
  /-- The member of a node is found, and so is each member of the two subtrees. -/
  | inner {size : Nat} {key : String} {value other : Json} {left right : Fields}
      {b : Std.TreeMap.Raw String Json compare} :
      b.get? key = some other → Agree value other → AgreeFields left b → AgreeFields right b →
        AgreeFields (.inner size key value left right) b
end

private theorem agreesAll_iff {a : List Json}
    (elements : ∀ value ∈ a, ∀ other, agrees value other = true ↔ Agree value other) :
    ∀ b, agreesAll a b = true ↔ AgreeAll a b := by
  induction a with
  | nil =>
    intro b
    cases b with
    | nil => exact ⟨fun _ => .nil, fun _ => by simp [agreesAll]⟩
    | cons other others =>
      exact ⟨fun h => by simp [agreesAll] at h, fun h => nomatch h⟩
  | cons head rest step =>
    intro b
    cases b with
    | nil => exact ⟨fun h => by simp [agreesAll] at h, fun h => nomatch h⟩
    | cons other others =>
      have rests := step (fun value member => elements value (List.mem_cons_of_mem _ member))
        others
      have heads := elements head List.mem_cons_self other
      simp only [agreesAll, Bool.and_eq_true, heads, rests]
      constructor
      · rintro ⟨first, more⟩
        exact .cons first more
      · intro h
        cases h with
        | cons first more => exact ⟨first, more⟩

/-- **`agrees` answers `true` exactly for the pairs that `Agree` relates.** -/
theorem agrees_iff (a b : Json) : agrees a b = true ↔ Agree a b := by
  revert b
  refine Cases.value (motive := fun a => ∀ b, agrees a b = true ↔ Agree a b)
    (fieldsMotive := fun fields => ∀ b, agreesFields fields b = true ↔ AgreeFields fields b) ?_ a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    cases b <;> simp [agrees] <;> first | exact .null | exact fun h => nomatch h
  · intro value b
    cases b <;> simp [agrees]
    all_goals first
      | exact fun h => nomatch h
      | exact ⟨fun same => same ▸ .bool _, fun h => by cases h; rfl⟩
  · intro value b
    cases b <;> simp [agrees]
    all_goals first
      | exact fun h => nomatch h
      | exact ⟨fun same => same ▸ .num _, fun h => by cases h; rfl⟩
  · intro value b
    cases b <;> simp [agrees]
    all_goals first
      | exact fun h => nomatch h
      | exact ⟨fun same => same ▸ .str _, fun h => by cases h; rfl⟩
  · intro elems elements b
    obtain ⟨elems⟩ := elems
    cases b with
    | arr other =>
      obtain ⟨other⟩ := other
      have lists := agreesAll_iff
        (fun value member => elements value (Array.mem_def.mpr member)) other
      simp only [agrees, lists]
      exact ⟨fun h => .arr h, fun h => by cases h; assumption⟩
    | _ => exact ⟨fun h => by simp [agrees] at h, fun h => nomatch h⟩
  · intro fields step b
    cases b with
    | obj other =>
      simp only [agrees, Bool.and_eq_true, beq_iff_eq, step other]
      exact ⟨fun ⟨size, all⟩ => .obj size all, fun h => by cases h; exact ⟨‹_›, ‹_›⟩⟩
    | _ => exact ⟨fun h => by simp [agrees] at h, fun h => nomatch h⟩
  · intro b
    exact ⟨fun _ => .leaf b, fun _ => by simp [agreesFields]⟩
  · intro size key value left right valueStep leftStep rightStep b
    simp only [agreesFields, Bool.and_eq_true, leftStep b, rightStep b]
    constructor
    · rintro ⟨⟨found, lefts⟩, rights⟩
      split at found
      · rename_i other present
        exact .inner present ((valueStep other).mp found) lefts rights
      · exact absurd found Bool.false_ne_true
    · intro h
      cases h with
      | inner present values lefts rights =>
        rw [present]
        exact ⟨⟨(valueStep _).mpr values, lefts⟩, rights⟩

/-- Each member of a tree is found exactly when each member of its list is found: the reading of
`AgreeFields` over the members in the order of the tree. -/
theorem agreeFields_iff (a : Fields) (b : Std.TreeMap.Raw String Json compare) :
    AgreeFields a b ↔
      ∀ member ∈ members a, ∃ other, b.get? member.1 = some other ∧ Agree member.2 other := by
  induction a with
  | leaf => exact ⟨fun _ _ member => (nomatch member), fun _ => .leaf b⟩
  | inner size key value left right leftStep rightStep =>
    constructor
    · intro h member present
      cases h with
      | inner found values lefts rights =>
        simp only [members_inner, List.mem_append, List.mem_cons] at present
        rcases present with inLeft | rfl | inRight
        · exact leftStep.mp lefts member inLeft
        · exact ⟨_, found, values⟩
        · exact rightStep.mp rights member inRight
    · intro all
      obtain ⟨other, found, values⟩ := all (key, value) (by simp [members_inner])
      exact .inner found values
        (leftStep.mpr fun member present => all member (by simp [members_inner, present]))
        (rightStep.mpr fun member present => all member (by simp [members_inner, present]))

/-- `agrees` is a sound and complete decision of `Agree` on pairs of JSON values
(`agrees_iff`): it accepts `null` with `null`, and it refuses `null` with a Boolean. The
specification is a relation with one constructor for each case of the comparison. It does not
say that the two values are equal, and it does not mention Lean's runtime equality of `Json`. -/
theorem checked_agrees : Regula.ExecutableContract agrees (fun test =>
    Regula.Decides (· = true) (fun values : Json × Json => Agree values.1 values.2)
      (Function.uncurry test)) :=
  ⟨Regula.Decides.of_iff (fun values => agrees_iff values.1 values.2)
    ⟨(.null, .null), rfl⟩ ⟨(.null, .bool true), by decide⟩⟩

/-- Whether the first JSON value has search trees as its object trees and agrees with the second
(`conforms_iff`). This is the comparison of an input with an encoding: `agrees` alone looks each
name of the input up in the encoding and never a name of the encoding in the input, so it also
accepts an input object tree that is not a search tree, which can give one name twice and lack
another name. -/
def conforms (a b : Json) : Bool := regular a && agrees a b

theorem conforms_registered : Regula.RegisteredDecision @conforms := ⟨⟩

/-- `conforms` answers `true` exactly when the first value is a value with search trees that
agrees with the second. -/
theorem conforms_iff (a b : Json) : conforms a b = true ↔ Regular a ∧ Agree a b := by
  simp only [conforms, Bool.and_eq_true, regular_iff, agrees_iff]

/-- The first value has search trees, and it agrees with the second. `conforms` decides it, so a
check can state this proposition and run `decide`, whose instance runs `conforms`. -/
def Conforms (a b : Json) : Prop := Regular a ∧ Agree a b

instance (a b : Json) : Decidable (Conforms a b) := decidable_of_iff _ (conforms_iff a b)

/-- `conforms` is a sound and complete decision (`conforms_iff`): it accepts `null` with `null`,
and it refuses `null` with a Boolean. The specification names the relations `Regular` and
`Agree`, not the two Boolean functions. -/
theorem checked_conforms : Regula.ExecutableContract conforms (fun test =>
    Regula.Decides (· = true)
      (fun values : Json × Json => Regular values.1 ∧ Agree values.1 values.2)
      (Function.uncurry test)) :=
  ⟨Regula.Decides.of_iff (fun values => conforms_iff values.1 values.2)
    ⟨(.null, .null), rfl⟩ ⟨(.null, .bool true), by decide⟩⟩

/-! ### Decoders that fail closed -/

/-- The decoder that accepts what `decode` returns only when the input has search trees as its
object trees and agrees with the encoding of that value (`conforms`), and that refuses with
`refusal` otherwise: `canonical_eq_ok_iff`. -/
def canonical {α : Type} (decode : Json → Except String α) (encode : α → Json)
    (refusal : String) (j : Json) : Except String α := do
  let value ← decode j
  unless conforms j (encode value) do throw refusal
  return value

theorem canonical_registered : Regula.RegisteredDecision @canonical := ⟨⟩

/-- A canonical decoder returns a value exactly when `decode` returns it, the object trees of the
input are search trees, and the input agrees with the encoding of that value. -/
theorem canonical_eq_ok_iff {α : Type} (decode : Json → Except String α) (encode : α → Json)
    (refusal : String) (j : Json) (value : α) :
    canonical decode encode refusal j = .ok value ↔
      decode j = .ok value ∧ Regular j ∧ Agree j (encode value) := by
  unfold canonical
  cases decoded : decode j with
  | error message =>
    simp only [bind, Except.bind]
    constructor
    · intro h
      cases h
    · rintro ⟨h, _⟩
      cases h
  | ok found =>
    by_cases test : conforms j (encode found) = true
    · simp only [bind, Except.bind, test, pure, Except.pure, Except.ok.injEq, ↓reduceIte]
      constructor
      · rintro rfl
        exact ⟨rfl, (conforms_iff _ _).mp test⟩
      · rintro ⟨same, _⟩
        exact same
    · simp only [bind, Except.bind, test, throw, throwThe, MonadExceptOf.throw, ↓reduceIte,
        Bool.false_eq_true]
      constructor
      · intro h
        cases h
      · rintro ⟨same, conforming⟩
        obtain rfl : found = value := Except.ok.inj same
        exact absurd ((conforms_iff _ _).mpr conforming) test

/-- What a call of `canonical` gives: the type of a decoded value, the reader, the encoder, the
text of the refusal and the input. -/
structure Decoding where
  /-- The type of a decoded value. -/
  payload : Type
  /-- The reader of the members of the input. -/
  decode : Json → Except String payload
  /-- The encoder of a decoded value. -/
  encode : payload → Json
  /-- The text of the refusal. -/
  refusal : String
  /-- The input. -/
  input : Json

/-- `canonical` is a sound and complete decision, for each reader and each encoder
(`canonical_eq_ok_iff`): it accepts exactly an input whose object trees are search trees and
that the reader reads to a value whose encoding the input agrees with. It accepts `null` for the
reader of the one value of `Unit` with the encoder to `null`, and it refuses each input for a
reader that refuses each input. The result type depends on the type of the decoded value, so
the decision is of whether the result is a success (`Regula.Dependent.isOk`). The reader and the
encoder are arguments: the kind says nothing about a particular reader or encoder. -/
theorem checked_canonical : Regula.ExecutableContract (@canonical) (fun run :
      {α : Type} → (Json → Except String α) → (α → Json) → String → Json → Except String α =>
    Regula.Decides (· = true)
      (fun call : Decoding => ∃ value, call.decode call.input = .ok value ∧
        Regular call.input ∧ Agree call.input (call.encode value))
      (Regula.Dependent.isOk fun call : Decoding =>
        run call.decode call.encode call.refusal call.input)) :=
  ⟨Regula.Decides.of_iff
    (fun call => by
      rw [Regula.Dependent.isOk_eq_true_iff]
      exact exists_congr fun value =>
        canonical_eq_ok_iff call.decode call.encode call.refusal call.input value)
    ⟨⟨Unit, fun _ => .ok (), fun _ => .null, "", .null⟩, by
      rw [Regula.Dependent.isOk_eq_true_iff]
      exact ⟨(), (canonical_eq_ok_iff _ _ _ _ _).mpr ⟨rfl, .null, .null⟩⟩⟩
    ⟨⟨Unit, fun _ => .error "", fun _ => .null, "", .null⟩, by
      rw [Regula.Dependent.isOk_eq_true_iff]
      rintro ⟨value, accepted⟩
      exact nomatch ((canonical_eq_ok_iff _ _ _ _ _).mp accepted).1⟩⟩

/-! ### Search trees -/

/-- The names of a list of members go up. A list with literal names has this property by
`decide`, after `List.map` is unfolded: the lemmas below prove it so, as a default argument. -/
abbrev Increasing (written : List (String × Json)) : Prop :=
  (written.map (·.1)).Pairwise fun earlier later => compare earlier later = .lt

/-- A tree whose members in the order of the tree have names that go up is a search tree. -/
theorem Ordered.of_members {fields : Fields} {written : List (String × Json)}
    (sorted : members fields = written) (increasing : Increasing written) : Ordered fields := by
  rw [ordered_iff, sorted]
  exact List.pairwise_map.mp increasing

/-- **In a search tree, each member is found by its name.** -/
theorem get?_of_mem {fields : Fields} (ordered : Ordered fields) {member : String × Json}
    (present : member ∈ members fields) :
    (⟨⟨fields⟩⟩ : Std.TreeMap.Raw String Json compare).get? member.1 = some member.2 := by
  induction fields with
  | leaf => exact nomatch present
  | inner size key value left right leftStep rightStep =>
    have unfolded : (⟨⟨.inner size key value left right⟩⟩ :
        Std.TreeMap.Raw String Json compare).get? member.1 =
          match compare member.1 key with
          | .lt => (⟨⟨left⟩⟩ : Std.TreeMap.Raw String Json compare).get? member.1
          | .gt => (⟨⟨right⟩⟩ : Std.TreeMap.Raw String Json compare).get? member.1
          | .eq => some value := rfl
    rw [unfolded]
    rw [ordered_iff] at ordered
    simp only [members_inner, List.pairwise_append, List.pairwise_cons] at ordered
    obtain ⟨lefts, ⟨after, rights⟩, across⟩ := ordered
    simp only [members_inner, List.mem_append, List.mem_cons] at present
    rcases present with inLeft | rfl | inRight
    · rw [across member inLeft (key, value) List.mem_cons_self]
      exact leftStep ((ordered_iff _).mpr lefts) inLeft
    · rw [Std.ReflCmp.compare_self (cmp := (compare : String → String → Ordering))]
    · rw [Std.OrientedCmp.gt_of_lt (after member inRight)]
      exact rightStep ((ordered_iff _).mpr rights) inRight

/-! ### The members of an object, by their names

The form of an encoded value is stated with `Shaped`: which members an object has, and what the
value of each is. The statement does not mention an encoder. -/

/-- A name of a member of an object, with what the value of that member is. -/
structure Entry where
  /-- The name of the member. -/
  name : String
  /-- What the value of the member is. -/
  meaning : Json → Prop

/-- The value is an object with the members of `schema` and no other. Its tree is a search tree
(`Ordered`), and it has as many members as the schema has names. Each name of the schema is
found, with a value of its meaning. Each member has a name of the schema, with a value of the
meaning of that name. -/
def Shaped (schema : List Entry) (j : Json) : Prop :=
  ∃ fields : Std.TreeMap.Raw String Json compare, j = .obj fields ∧
    Ordered fields.inner.inner ∧ count fields.inner.inner = schema.length ∧
    (∀ entry ∈ schema, ∃ value, fields.get? entry.name = some value ∧ entry.meaning value) ∧
    (∀ member ∈ members fields.inner.inner,
      ∃ entry ∈ schema, entry.name = member.1 ∧ entry.meaning member.2)

/-- Two lists have the same length, and their elements are related one by one. -/
inductive Aligned {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  /-- The empty lists. -/
  | nil : Aligned R [] []
  /-- Two related heads before two tails that are related one by one. -/
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → Aligned R as bs → Aligned R (a :: as) (b :: bs)

theorem aligned_left {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (all : Aligned R as bs) : ∀ a ∈ as, ∃ b ∈ bs, R a b := by
  induction all with
  | nil => exact fun _ member => nomatch member
  | cons head _ step =>
    intro a member
    rcases List.mem_cons.mp member with rfl | inTail
    · exact ⟨_, List.mem_cons_self, head⟩
    · obtain ⟨b, present, related⟩ := step a inTail
      exact ⟨b, List.mem_cons_of_mem _ present, related⟩

private theorem aligned_right {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (all : Aligned R as bs) : ∀ b ∈ bs, ∃ a ∈ as, R a b := by
  induction all with
  | nil => exact fun _ member => nomatch member
  | cons head _ step =>
    intro b member
    rcases List.mem_cons.mp member with rfl | inTail
    · exact ⟨_, List.mem_cons_self, head⟩
    · obtain ⟨a, present, related⟩ := step b inTail
      exact ⟨a, List.mem_cons_of_mem _ present, related⟩

private theorem aligned_length {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (all : Aligned R as bs) : as.length = bs.length := by
  induction all with
  | nil => rfl
  | cons _ _ step => simp [step]

/-- An object has the members of a schema when its members in the order of its tree are
`written`, the names go up, and the members have the names and the meanings of the schema, one by
one. Each member is then found by its name (`get?_of_mem`). -/
theorem Shaped.of_members {schema : List Entry} (fields : Std.TreeMap.Raw String Json compare)
    (written : List (String × Json)) (sorted : members fields.inner.inner = written)
    (meanings : Aligned
      (fun member entry => member.1 = entry.name ∧ entry.meaning member.2) written schema)
    (increasing : Increasing written) :
    Shaped schema (.obj fields) := by
  obtain ⟨⟨tree⟩⟩ := fields
  have found : ∀ member ∈ written,
      (⟨⟨tree⟩⟩ : Std.TreeMap.Raw String Json compare).get? member.1 = some member.2 :=
    fun member present => get?_of_mem (.of_members sorted increasing) (sorted ▸ present)
  refine ⟨⟨⟨tree⟩⟩, rfl, .of_members sorted increasing, ?_, ?_, ?_⟩
  · rw [count_eq_length, sorted, aligned_length meanings]
  · intro entry present
    obtain ⟨member, inWritten, same, meaning⟩ := aligned_right meanings entry present
    exact ⟨member.2, same ▸ found member inWritten, meaning⟩
  · intro member present
    obtain ⟨entry, inSchema, same, meaning⟩ := aligned_left meanings member (sorted ▸ present)
    exact ⟨entry, inSchema, same.symm, meaning⟩

/-- An object with the members of a schema agrees with an object of the same number of members
that has, for each name of the schema, a value that each value of that meaning agrees with. -/
theorem Shaped.agree {schema : List Entry} {j : Json} (shaped : Shaped schema j)
    (canonical : Std.TreeMap.Raw String Json compare)
    (size : count canonical.inner.inner = schema.length)
    (each : ∀ entry ∈ schema, ∃ value, canonical.get? entry.name = some value ∧
      ∀ found, entry.meaning found → Agree found value) :
    Agree j (.obj canonical) := by
  obtain ⟨⟨⟨fields⟩⟩, rfl, -, length, -, all⟩ := shaped
  refine .obj (length.trans size.symm) ((agreeFields_iff _ _).mpr fun member present => ?_)
  obtain ⟨entry, inSchema, same, meaning⟩ := all member present
  obtain ⟨value, found, agree⟩ := each entry inSchema
  exact ⟨value, same ▸ found, agree _ meaning⟩

/-- As `Shaped.agree`, for an object whose members in the order of its tree are `written`. -/
theorem Shaped.agree_of_members {schema : List Entry} {j : Json} (shaped : Shaped schema j)
    (canonical : Std.TreeMap.Raw String Json compare) (written : List (String × Json))
    (sorted : members canonical.inner.inner = written)
    (meanings : Aligned (fun member entry => member.1 = entry.name ∧
      ∀ value, entry.meaning value → Agree value member.2) written schema)
    (increasing : Increasing written) :
    Agree j (.obj canonical) := by
  obtain ⟨⟨tree⟩⟩ := canonical
  have found : ∀ member ∈ written,
      (⟨⟨tree⟩⟩ : Std.TreeMap.Raw String Json compare).get? member.1 = some member.2 :=
    fun member present => get?_of_mem (.of_members sorted increasing) (sorted ▸ present)
  refine shaped.agree ⟨⟨tree⟩⟩ ?_ fun entry present => ?_
  · rw [count_eq_length, sorted, aligned_length meanings]
  · obtain ⟨member, inWritten, same, agree⟩ := aligned_right meanings entry present
    exact ⟨member.2, same ▸ found member inWritten, agree⟩

/-- The member of a name of the schema, as `Json.getObjVal?` reads it. -/
theorem Shaped.member {schema : List Entry} {j : Json} (shaped : Shaped schema j)
    {entry : Entry} (present : entry ∈ schema) :
    ∃ value, j.getObjVal? entry.name = .ok value ∧ entry.meaning value := by
  obtain ⟨fields, rfl, -, -, lookups, -⟩ := shaped
  obtain ⟨value, found, meaning⟩ := lookups entry present
  refine ⟨value, ?_, meaning⟩
  -- `delta`, not `Json.getObjVal?` in the simp set, which would realize here copies of its
  -- equation lemmas.
  delta Json.getObjVal?
  simp only [found]
  rfl

/-- A value of the form of a schema is a value with search trees, when each value of the meaning
of each name of the schema is. -/
theorem Shaped.regular {schema : List Entry} {j : Json} (shaped : Shaped schema j)
    (each : ∀ entry ∈ schema, ∀ value, entry.meaning value → Regular value) : Regular j := by
  obtain ⟨⟨⟨fields⟩⟩, rfl, ordered, -, -, all⟩ := shaped
  refine .obj ordered fun member present => ?_
  obtain ⟨entry, inSchema, -, meaning⟩ := all member present
  exact each entry inSchema _ meaning

/-- An object agrees with itself when its members in the order of its tree are `written`, the
names go up, and the value of each member agrees with itself. -/
theorem Agree.obj_self (fields : Std.TreeMap.Raw String Json compare)
    (written : List (String × Json)) (sorted : members fields.inner.inner = written)
    (each : ∀ member ∈ written, Agree member.2 member.2)
    (increasing : Increasing written) :
    Agree (.obj fields) (.obj fields) := by
  obtain ⟨⟨tree⟩⟩ := fields
  refine .obj rfl ((agreeFields_iff _ _).mpr fun member present => ?_)
  exact ⟨member.2, get?_of_mem (.of_members sorted increasing) present,
    each member (sorted ▸ present)⟩

/-- A list of values each of which agrees with itself agrees with itself. -/
theorem agreeAll_self {elements : List Json} (each : ∀ value ∈ elements, Agree value value) :
    AgreeAll elements elements := by
  induction elements with
  | nil => exact .nil
  | cons head rest step =>
    exact .cons (each head (by simp)) (step fun value inside => each value (by simp [inside]))

/-- **A value whose object trees are search trees agrees with itself**: each member of each of
its trees is found by its name (`get?_of_mem`). -/
theorem Regular.agree_self {j : Json} (regular : Regular j) : Agree j j := by
  induction regular with
  | null => exact .null
  | bool value => exact .bool value
  | num value => exact .num value
  | str value => exact .str value
  | @arr elements _ step =>
    obtain ⟨elements⟩ := elements
    exact .arr (agreeAll_self fun value inside => step value (Array.mem_def.mpr inside))
  | @obj fields ordered _ step =>
    exact .obj rfl ((agreeFields_iff _ _).mpr fun member present =>
      ⟨member.2, get?_of_mem ordered present, step member present⟩)

/-! ### From an agreement to the members

`Shaped.of_agree` is the converse of `Shaped.agree_of_members`, for a value whose object trees
are search trees (`Regular`). An object tree that is not a search tree can agree with an
encoding and not have the members of the schema: it can give one name twice in the place of
another name, or have a member that no lookup finds. `conforms` refuses such an input. -/

/-- A name that is found in an object tree is the name of a member of the tree, with the value
that the lookup returns. -/
theorem mem_of_get? {fields : Fields} {name : String} {value : Json}
    (found : (⟨⟨fields⟩⟩ : Std.TreeMap.Raw String Json compare).get? name = some value) :
    (name, value) ∈ members fields := by
  induction fields with
  | leaf => exact nomatch found
  | inner size key other left right leftStep rightStep =>
    have unfolded : (⟨⟨.inner size key other left right⟩⟩ :
        Std.TreeMap.Raw String Json compare).get? name =
          match compare name key with
          | .lt => (⟨⟨left⟩⟩ : Std.TreeMap.Raw String Json compare).get? name
          | .gt => (⟨⟨right⟩⟩ : Std.TreeMap.Raw String Json compare).get? name
          | .eq => some other := rfl
    rw [unfolded] at found
    simp only [members_inner, List.mem_append, List.mem_cons]
    split at found
    · exact .inl (leftStep found)
    · exact .inr (.inr (rightStep found))
    · rename_i same
      obtain rfl : name = key := Std.LawfulEqCmp.eq_of_compare same
      obtain rfl : other = value := Option.some.inj found
      exact .inr (.inl rfl)

/-- A value that agrees with a string is that string. -/
theorem Agree.eq_str {value : Json} {text : String} (agree : Agree value (.str text)) :
    value = .str text := by
  cases agree
  rfl

/-- A value that agrees with a number is that number. -/
theorem Agree.eq_num {value : Json} {number : JsonNumber} (agree : Agree value (.num number)) :
    value = .num number := by
  cases agree
  rfl

/-- A value that agrees with `null` is `null`. -/
theorem Agree.eq_null {value : Json} (agree : Agree value .null) : value = .null := by
  cases agree
  rfl

/-- A value conforms to a number exactly when it is that number: the same mantissa and the same
exponent. So comparing a value with a number through `conforms` decides equality to it. -/
theorem conforms_num_iff (value : Json) (number : JsonNumber) :
    conforms value (.num number) = true ↔ value = .num number := by
  rw [conforms_iff]
  constructor
  · exact fun ⟨_, agree⟩ => agree.eq_num
  · rintro rfl
    exact ⟨.num number, .num number⟩

private theorem nodup_of_increasing {names : List String}
    (increasing : names.Pairwise fun earlier later => compare earlier later = .lt) :
    names.Nodup :=
  increasing.imp fun {earlier later} less same => by
    rw [same, Std.ReflCmp.compare_self (cmp := (compare : String → String → Ordering))] at less
    exact nomatch less

private theorem aligned_names {schema : List Entry} {written : List (String × Json)}
    {P : String × Json → Entry → Prop}
    (aligned : Aligned (fun member entry => member.1 = entry.name ∧ P member entry) written
      schema) : written.map (·.1) = schema.map (·.name) := by
  induction aligned with
  | nil => rfl
  | cons head _ step => simp only [List.map_cons, head.1, step]

private theorem entry_of_name {schema : List Entry} (distinct : (schema.map (·.name)).Nodup)
    {first second : Entry} (inFirst : first ∈ schema) (inSecond : second ∈ schema)
    (same : first.name = second.name) : first = second := by
  induction schema with
  | nil => exact nomatch inFirst
  | cons head rest step =>
    obtain ⟨absent, others⟩ := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp inFirst with rfl | firstRest <;>
      rcases List.mem_cons.mp inSecond with rfl | secondRest
    · rfl
    · exact absurd (List.mem_map.mpr ⟨second, secondRest, same.symm⟩) absent
    · exact absurd (List.mem_map.mpr ⟨first, firstRest, same⟩) absent
    · exact step others firstRest secondRest

/-- **A value whose object trees are search trees, and that agrees with an object, has the
members of a schema** when the members of that object in the order of its tree are `written`,
their names go up, and each value that agrees with the value of a written member has the meaning
of the schema for that name. -/
theorem Shaped.of_agree {schema : List Entry} {j : Json}
    {canonical : Std.TreeMap.Raw String Json compare} (written : List (String × Json))
    (regular : Regular j) (agree : Agree j (.obj canonical))
    (sorted : members canonical.inner.inner = written)
    (meanings : Aligned (fun member entry => member.1 = entry.name ∧
      ∀ value, Regular value → Agree value member.2 → entry.meaning value) written schema)
    (increasing : Increasing written) :
    Shaped schema j := by
  obtain ⟨⟨target⟩⟩ := canonical
  cases agree with
  | obj size fields =>
    rename_i tree
    cases regular with
    | obj ordered values =>
      have each := (agreeFields_iff _ _).mp fields
      have traversal : ∀ member ∈ members tree,
          ∃ entry ∈ schema, entry.name = member.1 ∧ entry.meaning member.2 := by
        intro member present
        obtain ⟨other, found, agrees⟩ := each member present
        have listed : (member.1, other) ∈ written := sorted ▸ mem_of_get? found
        obtain ⟨entry, inSchema, same, meaning⟩ := aligned_left meanings _ listed
        exact ⟨entry, inSchema, same.symm, meaning _ (values member present) agrees⟩
      have length : count tree = schema.length := by
        rw [size, count_eq_length, sorted, aligned_length meanings]
      refine ⟨⟨⟨tree⟩⟩, rfl, ordered, length, ?_, traversal⟩
      intro entry present
      have treeNames : ((members tree).map (·.1)).Nodup :=
        nodup_of_increasing (List.pairwise_map.mpr ((ordered_iff _).mp ordered))
      have schemaNames : (schema.map (·.name)).Nodup := by
        rw [← aligned_names meanings]
        exact nodup_of_increasing increasing
      have same : (schema.map (·.name)).Perm ((members tree).map (·.1)) :=
        RegulaPolicy.Guards.perm_of_length_of_mem treeNames
          (by rw [List.length_map, List.length_map, ← length, count_eq_length])
          fun name inTree => by
            obtain ⟨member, memberPresent, rfl⟩ := List.mem_map.mp inTree
            obtain ⟨found, inSchema, sameName, -⟩ := traversal member memberPresent
            exact List.mem_map.mpr ⟨found, inSchema, sameName⟩
      obtain ⟨member, memberPresent, sameName⟩ :=
        List.mem_map.mp (same.mem_iff.mp (List.mem_map.mpr ⟨entry, present, rfl⟩))
      obtain ⟨found, inSchema, foundName, meaning⟩ := traversal member memberPresent
      obtain rfl : found = entry :=
        entry_of_name schemaNames inSchema present (foundName.trans sameName)
      exact ⟨member.2, sameName ▸ get?_of_mem ordered memberPresent, meaning⟩

end Regula.JsonAgreement
