import Regula.SourceTexts
import Regula.Contract
import Regula.Decision

/-! # Agreement of two JSON values

A decoder that fails closed compares its input with the canonical encoding of what it decoded,
so an unknown member and a stale redundant member are refused. Lean's own `Json` equality is
`partial`: no proof unfolds it, so no theorem says what such a decoder accepts. `agrees` is the
comparison those decoders run instead. It is a pure, total function of two `Json` values, and
`agrees_iff` proves that it answers `true` exactly for the pairs that `Agree` relates.

`Agree` relates two values of the same constructor: equal Booleans, numbers and strings, arrays
whose elements agree in order, and objects whose members, read in the order of each tree
(`members`), have the same names in the same sequence and values that agree. The relation does
not compare the shape of two object trees, so two objects with the same members that were built
by different sequences of insertions agree where `SharedExecution.same`, which decides `=`,
refuses them.

**Not claimed.** That `agrees` returns what Lean's runtime equality returns: that function is
`partial`, so no theorem mentions it. For two objects whose trees are search trees the two have
the same answer, because the members of a search tree in tree order are its members in the order
of the names. That is read from the two definitions, not proved. The relation is about `Json`
values: what a text parser returns for a text is outside it. -/
namespace Regula.JsonAgreement
open Lean
open Regula.SourceTexts (Fields Cases)

/-- The members of an object tree in the order of the tree: the left subtree, the node, the right
subtree. -/
def members : Fields → List (String × Json)
  | .leaf => []
  | .inner _ key value left right => members left ++ (key, value) :: members right

mutual
/-- Whether two JSON values agree: the same constructor, equal Booleans, numbers and strings,
array elements that agree in order, and object members that have the same names in the order of
each tree with values that agree (`Agree`, by `agrees_iff`). -/
@[regula_decision]
def agrees (a b : Json) : Bool :=
  match a, b with
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => a == b
  | .str a, .str b => a == b
  | .arr ⟨a⟩, .arr ⟨b⟩ => agreesAll a b
  | .obj ⟨⟨a⟩⟩, .obj ⟨⟨b⟩⟩ =>
      match agreesFields a (members b) with
      | some [] => true
      | _ => false
  | _, _ => false
termination_by sizeOf a
/-- `agrees` on the elements of two arrays, in order. -/
def agreesAll (a b : List Json) : Bool :=
  match a, b with
  | [], [] => true
  | head :: rest, other :: others => agrees head other && agreesAll rest others
  | _, _ => false
termination_by sizeOf a
/-- Read the members of the tree `a` in the order of the tree against the start of `pending`:
the members that stay after the last member of `a`, or `none` when a member of `a` has no
partner with its name and an agreeing value. -/
def agreesFields (a : Fields) (pending : List (String × Json)) :
    Option (List (String × Json)) :=
  match a with
  | .leaf => some pending
  | .inner _ key value left right =>
      match agreesFields left pending with
      | some ((name, other) :: pending) =>
          if key == name && agrees value other then agreesFields right pending else none
      | _ => none
termination_by sizeOf a
end

mutual
/-- Two JSON values agree: one constructor for each constructor of `Json`. -/
inductive Agree : Json → Json → Prop
  /-- `null` agrees with `null`. -/
  | null : Agree .null .null
  /-- A Boolean agrees with the same Boolean. -/
  | bool (value : Bool) : Agree (.bool value) (.bool value)
  /-- A number agrees with the same number: the same mantissa and the same exponent. -/
  | num (value : JsonNumber) : Agree (.num value) (.num value)
  /-- A string agrees with the same string. -/
  | str (value : String) : Agree (.str value) (.str value)
  /-- Two arrays agree when their elements agree in order. -/
  | arr {a b : List Json} : AgreeAll a b → Agree (.arr ⟨a⟩) (.arr ⟨b⟩)
  /-- Two objects agree when their members agree in the order of each tree. -/
  | obj {a b : Fields} : AgreeMembers (members a) (members b) → Agree (.obj ⟨⟨a⟩⟩) (.obj ⟨⟨b⟩⟩)
/-- Two lists of JSON values have the same length and agree element by element. -/
inductive AgreeAll : List Json → List Json → Prop
  /-- The empty lists. -/
  | nil : AgreeAll [] []
  /-- Two heads that agree before two tails that agree. -/
  | cons {head other : Json} {rest others : List Json} :
      Agree head other → AgreeAll rest others → AgreeAll (head :: rest) (other :: others)
/-- Two lists of members have the same length and agree member by member: the same name and
values that agree. -/
inductive AgreeMembers : List (String × Json) → List (String × Json) → Prop
  /-- The empty lists. -/
  | nil : AgreeMembers [] []
  /-- Two members of one name with values that agree, before two tails that agree. -/
  | cons (name : String) {value other : Json} {rest others : List (String × Json)} :
      Agree value other → AgreeMembers rest others →
        AgreeMembers ((name, value) :: rest) ((name, other) :: others)
end

/-- Two member lists that agree, each before one of two more that agree, agree. -/
theorem AgreeMembers.append {first others : List (String × Json)} :
    ∀ {second more : List (String × Json)}, AgreeMembers first second →
      AgreeMembers others more → AgreeMembers (first ++ others) (second ++ more) := by
  induction first with
  | nil =>
    intro second more firsts rests
    cases firsts
    exact rests
  | cons head rest step =>
    intro second more firsts rests
    cases firsts with
    | cons name values tails => exact .cons name values (step tails rests)

/-- A list that agrees with an append is an append of two lists that agree with the parts. -/
theorem AgreeMembers.split {first others : List (String × Json)} :
    ∀ {whole : List (String × Json)}, AgreeMembers (first ++ others) whole →
      ∃ second more, whole = second ++ more ∧ AgreeMembers first second ∧
        AgreeMembers others more := by
  induction first with
  | nil =>
    intro whole agree
    exact ⟨[], whole, rfl, .nil, agree⟩
  | cons head rest step =>
    intro whole agree
    cases agree with
    | cons name values tails =>
      obtain ⟨second, more, rfl, seconds, mores⟩ := step tails
      exact ⟨_ :: second, more, rfl, .cons name values seconds, mores⟩

private theorem agreesAll_sound {a : List Json}
    (elements : ∀ value ∈ a, ∀ other, agrees value other = true → Agree value other) :
    ∀ b, agreesAll a b = true → AgreeAll a b := by
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => exact .nil
    | cons other others => simp [agreesAll] at h
  | cons head rest step =>
    intro b h
    cases b with
    | nil => simp [agreesAll] at h
    | cons other others =>
      simp only [agreesAll, Bool.and_eq_true] at h
      exact .cons (elements head List.mem_cons_self other h.1)
        (step (fun value member => elements value (List.mem_cons_of_mem _ member)) others h.2)

private theorem agreesAll_complete {a : List Json}
    (elements : ∀ value ∈ a, ∀ other, Agree value other → agrees value other = true) :
    ∀ b, AgreeAll a b → agreesAll a b = true := by
  induction a with
  | nil =>
    intro b h
    cases h
    simp [agreesAll]
  | cons head rest step =>
    intro b h
    cases h with
    | cons heads tails =>
      simp only [agreesAll, Bool.and_eq_true]
      exact ⟨elements head List.mem_cons_self _ heads,
        step (fun value member => elements value (List.mem_cons_of_mem _ member)) _ tails⟩

/-- **`agrees` answers `true` only for values that agree.** -/
theorem agrees_sound (a b : Json) (h : agrees a b = true) : Agree a b := by
  revert b
  refine Cases.value (motive := fun a => ∀ b, agrees a b = true → Agree a b)
    (fieldsMotive := fun fields => ∀ pending rest, agreesFields fields pending = some rest →
      ∃ front, pending = front ++ rest ∧ AgreeMembers (members fields) front) ?_ a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b h
    cases b <;> simp_all [agrees]
    exact .null
  · intro value b h
    cases b <;> simp_all [agrees]
    exact .bool _
  · intro value b h
    cases b <;> simp_all [agrees]
    exact .num _
  · intro value b h
    cases b <;> simp_all [agrees]
    exact .str _
  · intro elems elements b h
    obtain ⟨elems⟩ := elems
    cases b with
    | arr other =>
      obtain ⟨other⟩ := other
      simp only [agrees] at h
      exact .arr (agreesAll_sound
        (fun value member => elements value (Array.mem_def.mpr member)) other h)
    | _ => simp [agrees] at h
  · intro fields step b h
    cases b with
    | obj other =>
      obtain ⟨⟨other⟩⟩ := other
      simp only [agrees] at h
      split at h
      · rename_i found
        obtain ⟨front, whole, agree⟩ := step _ _ found
        rw [List.append_nil] at whole
        exact .obj (whole ▸ agree)
      · exact absurd h Bool.false_ne_true
    | _ => simp [agrees] at h
  · intro pending rest h
    simp only [agreesFields, Option.some.injEq] at h
    exact ⟨[], h ▸ rfl, .nil⟩
  · intro size key value left right valueStep leftStep rightStep pending rest h
    simp only [agreesFields] at h
    split at h
    · rename_i name other pending' found
      split at h
      · rename_i test
        simp only [Bool.and_eq_true, beq_iff_eq] at test
        obtain ⟨rfl, values⟩ := test
        obtain ⟨before, whole, lefts⟩ := leftStep _ _ found
        obtain ⟨after, tail, rights⟩ := rightStep _ _ h
        refine ⟨before ++ (key, other) :: after, ?_, ?_⟩
        · rw [whole, tail, List.append_assoc, List.cons_append]
        · exact lefts.append (.cons key (valueStep other values) rights)
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- **`agrees` answers `true` for all values that agree.** -/
theorem agrees_complete (a b : Json) (h : Agree a b) : agrees a b = true := by
  revert b
  refine Cases.value (motive := fun a => ∀ b, Agree a b → agrees a b = true)
    (fieldsMotive := fun fields => ∀ front rest, AgreeMembers (members fields) front →
      agreesFields fields (front ++ rest) = some rest) ?_ a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b h
    cases h
    simp [agrees]
  · intro value b h
    cases h
    simp [agrees]
  · intro value b h
    cases h
    simp [agrees]
  · intro value b h
    cases h
    simp [agrees]
  · intro elems elements b h
    obtain ⟨elems⟩ := elems
    cases h with
    | arr all =>
      simp only [agrees]
      exact agreesAll_complete
        (fun value member => elements value (Array.mem_def.mpr member)) _ all
  · intro fields step b h
    cases h with
    | obj all =>
      have found := step _ [] all
      rw [List.append_nil] at found
      simp only [agrees, found]
  · intro front rest h
    simp only [members] at h
    cases h
    simp [agreesFields]
  · intro size key value left right valueStep leftStep rightStep front rest h
    simp only [members] at h
    obtain ⟨before, tail, rfl, lefts, tails⟩ := h.split
    cases tails with
    | cons name values rights =>
      simp only [agreesFields]
      rw [List.append_assoc, leftStep before _ lefts]
      simp only [List.cons_append, beq_self_eq_true, valueStep _ values, Bool.and_self,
        ite_true]
      exact rightStep _ rest rights

/-- `agrees` answers `true` exactly for the values that `Agree` relates. -/
theorem agrees_iff (a b : Json) : agrees a b = true ↔ Agree a b :=
  ⟨agrees_sound a b, agrees_complete a b⟩

/-- Each JSON value agrees with itself, for each shape of its object trees. -/
theorem Agree.refl (a : Json) : Agree a a := by
  refine Cases.value (motive := fun a => Agree a a)
    (fieldsMotive := fun fields => AgreeMembers (members fields) (members fields)) ?_ a
  refine ⟨.null, .bool, .num, .str, ?_, ?_, .nil, ?_⟩
  · intro elems elements
    obtain ⟨elems⟩ := elems
    refine .arr ?_
    have all : ∀ value ∈ elems, Agree value value :=
      fun value member => elements value (Array.mem_def.mpr member)
    clear elements
    induction elems with
    | nil => exact .nil
    | cons head rest step =>
      exact .cons (all head List.mem_cons_self)
        (step fun value member => all value (List.mem_cons_of_mem _ member))
  · intro fields step
    exact .obj step
  · intro size key value left right valueStep leftStep rightStep
    exact leftStep.append (.cons key valueStep rightStep)

/-- `agrees` accepts each value with itself. -/
theorem agrees_self (a : Json) : agrees a a = true :=
  agrees_complete a a (.refl a)

/-- `agrees` is a sound and complete decision of `Agree` on pairs of JSON values
(`agrees_iff`): it accepts `null` with `null`, and it refuses `null` with a Boolean. The
specification is a relation with one constructor for each constructor of `Json`. It does not say
that the two values are equal, and it does not mention Lean's runtime equality of `Json`. -/
theorem checked_agrees : Regula.ExecutableContract agrees (fun test =>
    Regula.Decides (· = true) (fun values : Json × Json => Agree values.1 values.2)
      (Function.uncurry test)) :=
  ⟨Regula.Decides.of_iff (fun values => agrees_iff values.1 values.2)
    ⟨(.null, .null), by simp [Function.uncurry, agrees]⟩
    ⟨(.null, .bool true), by simp [Function.uncurry, agrees]⟩⟩

/-! ### Decoders that fail closed -/

/-- The decoder that accepts what `decode` returns only when the input agrees with the encoding
of that value, and that refuses with `refusal` otherwise. An input with a member that `encode`
does not write, or with a redundant member whose value is not the one that `encode` writes, is
refused: `canonical_eq_ok_iff`. -/
@[regula_decision]
def canonical {α : Type} (decode : Json → Except String α) (encode : α → Json)
    (refusal : String) (j : Json) : Except String α := do
  let value ← decode j
  unless agrees j (encode value) do throw refusal
  return value

/-- A canonical decoder returns a value exactly when `decode` returns it and the input agrees
with the encoding of that value. -/
theorem canonical_eq_ok_iff {α : Type} (decode : Json → Except String α) (encode : α → Json)
    (refusal : String) (j : Json) (value : α) :
    canonical decode encode refusal j = .ok value ↔
      decode j = .ok value ∧ Agree j (encode value) := by
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
    by_cases test : agrees j (encode found) = true
    · simp only [bind, Except.bind, test, pure, Except.pure, Except.ok.injEq, ↓reduceIte]
      constructor
      · rintro rfl
        exact ⟨rfl, agrees_sound _ _ test⟩
      · rintro ⟨same, _⟩
        exact same
    · simp only [bind, Except.bind, test, throw, throwThe, MonadExceptOf.throw, ↓reduceIte,
        Bool.false_eq_true]
      constructor
      · intro h
        cases h
      · rintro ⟨same, agree⟩
        obtain rfl : found = value := Except.ok.inj same
        exact absurd (agrees_complete _ _ agree) test

/-- A canonical decoder accepts an encoding that `decode` reads back to its value. -/
theorem canonical_encode {α : Type} {decode : Json → Except String α} {encode : α → Json}
    (refusal : String) {value : α} (roundtrip : decode (encode value) = .ok value) :
    canonical decode encode refusal (encode value) = .ok value :=
  (canonical_eq_ok_iff decode encode refusal (encode value) value).mpr
    ⟨roundtrip, .refl (encode value)⟩

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
(`canonical_eq_ok_iff`): it accepts exactly an input that the reader reads to a value whose
encoding the input agrees with. It accepts `null` for the reader of the one value of `Unit` with
the encoder to `null`, and it refuses each input for a reader that refuses each input. The
result type depends on the type of the decoded value, so the decision is of whether the result
is a success (`Regula.Dependent.isOk`). The reader and the encoder are arguments: the kind says
nothing about a particular reader or encoder. -/
theorem checked_canonical : Regula.ExecutableContract (@canonical) (fun run :
      {α : Type} → (Json → Except String α) → (α → Json) → String → Json → Except String α =>
    Regula.Decides (· = true)
      (fun call : Decoding => ∃ value, call.decode call.input = .ok value ∧
        Agree call.input (call.encode value))
      (Regula.Dependent.isOk fun call : Decoding =>
        run call.decode call.encode call.refusal call.input)) :=
  ⟨Regula.Decides.of_iff
    (fun call => by
      rw [Regula.Dependent.isOk_eq_true_iff]
      exact exists_congr fun value =>
        canonical_eq_ok_iff call.decode call.encode call.refusal call.input value)
    ⟨⟨Unit, fun _ => .ok (), fun _ => .null, "", .null⟩, by
      rw [Regula.Dependent.isOk_eq_true_iff]
      exact ⟨(), (canonical_eq_ok_iff _ _ _ _ _).mpr ⟨rfl, .null⟩⟩⟩
    ⟨⟨Unit, fun _ => .error "", fun _ => .null, "", .null⟩, by
      rw [Regula.Dependent.isOk_eq_true_iff]
      rintro ⟨value, accepted⟩
      exact nomatch ((canonical_eq_ok_iff _ _ _ _ _).mp accepted).1⟩⟩

end Regula.JsonAgreement
