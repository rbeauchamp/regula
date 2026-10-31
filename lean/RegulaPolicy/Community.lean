module

import all Init.Meta.Defs

/-! # The required options of a claimed target

The options `regula init` writes and `regula doctor` reads (`RegulaCore.Setup`): `required`, the
options every claimed target sets, with the additional options of a target that imports Mathlib;
`valuesOf` and `sets`, what a target's resolved `leanOptions` give an option, under either spelling
(`optionOf`), as Lean reads a value (`OptionValue.readsAs`); and `argumentSettings`, each option
that a target's extra `lean` arguments can set with `-D`.

The checker does not read this module for its verdict: it decides RG2006 with
`Regula.Closed.Input.optionFindings` and `Regula.Allowlist.options`.

`argumentSettings` models `lean`'s reading of `-D` as a superset: a `-D` it parses starts at the
first `D` of an argument that begins with a single `-`, and its value follows the `D` or is the next
argument. That correspondence with the command-line parser of the Lean executable is assumed, read
from Lean's `Lean.Shell` source and its getopt handling; it is neither proved nor observed.
`mem_argumentSettings_iff` states what the model reads. -/

@[expose] public section

namespace RegulaPolicy.Community

open Lean (Name)

/-- A Lean option value, as Lake records it in `leanOptions` (`Lean.LeanOptionValue`). -/
inductive OptionValue where
  /-- A string value. -/
  | string (s : String)
  /-- A Boolean value. -/
  | bool (b : Bool)
  /-- A natural-number value. -/
  | nat (n : Nat)
  deriving DecidableEq, Repr

/-- Lean reads `v` as `r` for an option declared with the type of `r`: a string as it parses a
command-line or string option value, any other value only when it is `r`. This is the relation,
as a proposition; `OptionValue.readsAs` decides it (`OptionValue.readsAs_iff`). -/
def OptionValue.ReadsAs : OptionValue → OptionValue → Prop
  | .string s, .bool b => s = toString b
  | .string s, .nat n => s.toNat? = some n
  | v, r => v = r

/-- The executed comparison: whether Lean reads `v` as `r` (`OptionValue.ReadsAs`). -/
def OptionValue.readsAs : OptionValue → OptionValue → Bool
  | .string s, .bool b => s == toString b
  | .string s, .nat n => s.toNat? == some n
  | v, r => v == r

/-- The executed comparison accepts exactly the values that Lean reads as the required one. -/
theorem OptionValue.readsAs_iff (v r : OptionValue) : v.readsAs r = true ↔ v.ReadsAs r := by
  cases v <;> cases r <;> simp [OptionValue.readsAs, OptionValue.ReadsAs]

/-- The options Lake builds one target's modules with. -/
structure BuildOptions where
  /-- Lake's resolved `leanOptions`: build type, package, then target, a later entry for the
  same key replacing an earlier one, so each key occurs once. -/
  options : List (Name × OptionValue)
  deriving DecidableEq, Repr

/-- The option a `leanOptions` key sets: the key without a leading `weak.` component, removed by
the call Lean makes (`Lean.Language.Lean.reparseOptions`). -/
def optionOf (name : Name) : Name :=
  name.replacePrefix `weak .anonymous

/-- `optionOf` is Lean's own removal of a leading `weak.` component from an option name. -/
theorem optionOf_eq_replacePrefix (name : Name) :
    optionOf name = name.replacePrefix `weak .anonymous := rfl

/-- The characters after the first `D`, when there is one. -/
def afterD : List Char → Option (List Char)
  | [] => none
  | c :: rest => if c = 'D' then some rest else afterD rest

/-- The characters after the first `D` of an argument that begins with a single `-`: a `-D`
value, or empty when the value is the next argument. `lean` reads `-D` alone or after flags, as
in `-qD`; an argument whose first `D` is not a `-D` still gives a candidate. -/
def defineText? (argument : String) : Option (List Char) :=
  match argument.toList with
  | c :: d :: rest => if c = '-' ∧ d ≠ '-' then afterD (d :: rest) else none
  | _ => none

/-- The characters before and after the first `=`, when there is one. -/
def splitAtEq : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
    if c = '=' then some ([], rest) else (splitAtEq rest).map fun p => (c :: p.1, p.2)

/-- A `-D` value `name=value`, split at its first `=` as `lean` does: the name and value texts. -/
def settingText? (text : List Char) : Option (String × String) :=
  (splitAtEq text).map fun p => (String.ofList p.1, String.ofList p.2)

/-- The `-D` setting that `argument`, followed by the arguments `rest`, can make. -/
def argumentText? (argument : String) (rest : List String) : Option (String × String) :=
  match defineText? argument with
  | some [] => rest.head?.bind fun next => settingText? next.toList
  | some text => settingText? text
  | none => none

/-- The name and value texts of every `-D` setting the extra `lean` arguments can make, in
argument order. -/
def argumentTexts : List String → List (String × String)
  | [] => []
  | argument :: rest => (argumentText? argument rest).toList ++ argumentTexts rest

/-- Every option setting the extra `lean` arguments can make with `-D`, in argument order: each
name read as `lean` reads it (`String.toName`), each value a string. -/
def argumentSettings (arguments : List String) : List (Name × OptionValue) :=
  (argumentTexts arguments).map fun t => (t.1.toName, .string t.2)

/-- `argument` is a `-D` form with `text` after its `D`: a single `-`, then flags without a `D`
(as the `q` of `-qD`), then `D`. -/
def DefineForm (argument : String) (text : List Char) : Prop :=
  ∃ flags, argument.toList = '-' :: flags ++ 'D' :: text ∧ 'D' ∉ flags ∧ flags.head? ≠ some '-'

/-- `text` is `name=value`, with no `=` in `name`. -/
def SettingForm (text : List Char) (name value : String) : Prop :=
  ∃ n v, text = n ++ '=' :: v ∧ '=' ∉ n ∧ name = String.ofList n ∧ value = String.ofList v

/-- `argument`, followed by the arguments `rest`, sets the option text `name` to `value` with
`-D`: `name=value` follows its `D`, or, when nothing follows the `D`, is the next argument. -/
def DefinesHere (argument : String) (rest : List String) (name value : String) : Prop :=
  ∃ text, DefineForm argument text ∧
    ((text ≠ [] ∧ SettingForm text name value) ∨
      (text = [] ∧ ∃ next more, rest = next :: more ∧ SettingForm next.toList name value))

/-- Some argument of `arguments` sets the option text `name` to `value` with `-D`. -/
def Defines (arguments : List String) (name value : String) : Prop :=
  ∃ pre argument rest, arguments = pre ++ argument :: rest ∧ DefinesHere argument rest name value

/-- `afterD` finds exactly the characters after the first `D`. -/
theorem afterD_eq_some_iff (chars text : List Char) :
    afterD chars = some text ↔ ∃ flags, chars = flags ++ 'D' :: text ∧ 'D' ∉ flags := by
  induction chars with
  | nil => simp [afterD]
  | cons c rest ih =>
    by_cases hc : c = 'D'
    · subst hc
      simp only [afterD, ↓reduceIte, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨[], rfl, by simp⟩
      · rintro ⟨_ | ⟨f, flags⟩, h, hD⟩
        · simpa using h
        · simp_all
    · simp only [afterD, hc, ↓reduceIte, ih]
      constructor
      · rintro ⟨flags, rfl, hD⟩
        exact ⟨c :: flags, rfl, by simp [Ne.symm hc, hD]⟩
      · rintro ⟨_ | ⟨f, flags⟩, h, hD⟩
        · simp_all
        · simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨flags, rfl, fun h => hD (List.mem_cons_of_mem _ h)⟩

/-- `defineText?` recognizes exactly the `-D` forms. -/
theorem defineText?_eq_some_iff (argument : String) (text : List Char) :
    defineText? argument = some text ↔ DefineForm argument text := by
  unfold defineText? DefineForm
  generalize argument.toList = chars
  match chars with
  | [] => simp
  | [c] => simp
  | c :: d :: rest =>
    by_cases h : c = '-' ∧ d ≠ '-'
    · obtain ⟨rfl, hd⟩ := h
      simp only [hd, ne_eq, not_false_eq_true, and_self, ↓reduceIte, afterD_eq_some_iff]
      constructor
      · rintro ⟨flags, heq, hD⟩
        refine ⟨flags, by simp [heq], hD, ?_⟩
        cases flags with
        | nil => simp
        | cons f fs =>
          simp only [List.cons_append, List.cons.injEq] at heq
          simp [← heq.1, hd]
      · rintro ⟨flags, heq, hD, -⟩
        exact ⟨flags, by simpa using heq, hD⟩
    · simp only [h, ↓reduceIte, reduceCtorEq, false_iff, not_exists, not_and]
      intro flags heq hD hh
      apply h
      simp only [List.cons_append, List.cons.injEq] at heq
      refine ⟨heq.1, ?_⟩
      cases flags with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        rw [heq.2.1]
        decide
      | cons f fs =>
        simp only [List.cons_append, List.cons.injEq] at heq
        rw [heq.2.1]
        simpa using hh

/-- `splitAtEq` splits exactly at the first `=`. -/
theorem splitAtEq_eq_some_iff (chars name value : List Char) :
    splitAtEq chars = some (name, value) ↔ chars = name ++ '=' :: value ∧ '=' ∉ name := by
  induction chars generalizing name with
  | nil => simp [splitAtEq]
  | cons c rest ih =>
    by_cases hc : c = '='
    · subst hc
      simp only [splitAtEq, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩
        simp
      · rintro ⟨h, hn⟩
        cases name with
        | nil => simpa [eq_comm] using h
        | cons n ns => simp_all
    · simp only [splitAtEq, hc, ↓reduceIte, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq]
      constructor
      · rintro ⟨n, v, hs, rfl, rfl⟩
        obtain ⟨rfl, hn⟩ := (ih n).1 hs
        exact ⟨rfl, by simp [Ne.symm hc, hn]⟩
      · rintro ⟨h, hn⟩
        cases name with
        | nil => simp_all
        | cons n ns =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨ns, value, (ih ns).2 ⟨rfl, fun h => hn (List.mem_cons_of_mem _ h)⟩, rfl, rfl⟩

/-- `settingText?` reads exactly the `name=value` texts. -/
theorem settingText?_eq_some_iff (text : List Char) (name value : String) :
    settingText? text = some (name, value) ↔ SettingForm text name value := by
  simp only [settingText?, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq, SettingForm,
    splitAtEq_eq_some_iff]
  constructor
  · rintro ⟨n, v, ⟨h, hn⟩, rfl, rfl⟩
    exact ⟨n, v, h, hn, rfl, rfl⟩
  · rintro ⟨n, v, h, hn, rfl, rfl⟩
    exact ⟨n, v, ⟨h, hn⟩, rfl, rfl⟩

/-- `argumentText?` reads exactly the `-D` setting one argument makes. -/
theorem argumentText?_eq_some_iff (argument : String) (rest : List String) (name value : String) :
    argumentText? argument rest = some (name, value) ↔ DefinesHere argument rest name value := by
  unfold argumentText? DefinesHere
  cases h : defineText? argument with
  | none =>
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro text hform
    rw [← defineText?_eq_some_iff, h] at hform
    exact absurd hform (by simp)
  | some text =>
    have hform : ∀ t, DefineForm argument t ↔ t = text := fun t => by
      rw [← defineText?_eq_some_iff, h, Option.some.injEq, eq_comm]
    simp only [hform, exists_eq_left]
    cases text with
    | nil =>
      cases rest with
      | nil => simp
      | cons next more => simp [settingText?_eq_some_iff]
    | cons c cs => simp [settingText?_eq_some_iff]

/-- `argumentTexts` reads exactly the `-D` settings of the arguments. -/
theorem mem_argumentTexts_iff (arguments : List String) (name value : String) :
    (name, value) ∈ argumentTexts arguments ↔ Defines arguments name value := by
  induction arguments with
  | nil => simp [argumentTexts, Defines]
  | cons argument rest ih =>
    simp only [argumentTexts, List.mem_append, Option.mem_toList, argumentText?_eq_some_iff, ih]
    constructor
    · rintro (h | ⟨pre, b, more, rfl, h⟩)
      · exact ⟨[], argument, rest, rfl, h⟩
      · exact ⟨argument :: pre, b, more, rfl, h⟩
    · rintro ⟨pre, b, more, heq, h⟩
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact .inl h
      | cons p pre =>
        simp only [List.cons_append, List.cons.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact .inr ⟨pre, b, more, rfl, h⟩

/-- `argumentSettings` holds exactly the `-D` settings, each name read by `String.toName`. -/
theorem mem_argumentSettings_iff (arguments : List String) (n : Name) (v : OptionValue) :
    (n, v) ∈ argumentSettings arguments ↔
      ∃ name value, Defines arguments name value ∧ n = name.toName ∧ v = .string value := by
  simp only [argumentSettings, List.mem_map, Prod.exists, Prod.mk.injEq, mem_argumentTexts_iff]
  constructor
  · rintro ⟨name, value, hd, rfl, rfl⟩
    exact ⟨name, value, hd, rfl, rfl⟩
  · rintro ⟨name, value, hd, rfl, rfl⟩
    exact ⟨name, value, hd, rfl, rfl⟩

/-- The options every claimed target sets: no automatic implicits (standard §7.1), and Lean's
linter that reports each public declaration without a docstring (standard §6.7). -/
def baseline : List (Name × OptionValue) :=
  [(`autoImplicit, .bool false), (`relaxedAutoImplicit, .bool false),
    (`linter.missingDocs, .bool true)]

/-- Mathlib's standard linter set with its three Mathlib-repository exclusions (standard §6.7),
set by a claimed target whose modules import Mathlib. -/
def mathlibBaseline : List (Name × OptionValue) :=
  [(`linter.mathlibStandardSet, .bool true), (`linter.style.header, .bool false),
    (`linter.hashCommand, .bool false), (`linter.style.longFile, .nat 0)]

/-- The options a claimed target sets, with their values. -/
def required (mathlib : Bool) : List (Name × OptionValue) :=
  baseline ++ if mathlib then mathlibBaseline else []

/-- The values the options give option `name`, under either spelling. -/
def valuesOf (o : BuildOptions) (name : Name) : List OptionValue :=
  o.options.filterMap fun entry => if optionOf entry.1 = name then some entry.2 else none

/-- The options set `name` to `value`: at least once, and never to another value. -/
def sets (o : BuildOptions) (name : Name) (value : OptionValue) : Bool :=
  !(valuesOf o name).isEmpty && (valuesOf o name).all (·.readsAs value)

/-- Each option is required at most once. -/
theorem required_unique (mathlib : Bool) :
    ∀ r ∈ required mathlib, ∀ r' ∈ required mathlib, r.1 = r'.1 → r = r' := by
  cases mathlib <;> decide

end RegulaPolicy.Community
