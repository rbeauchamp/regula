module

/-! # Community build configuration decision

The decision behind RG2006 for one claimed Lake target (standard §7.1, §6.7 and §6.2): the
options Lake builds its modules with turn automatic implicits off, enable Lean's
`linter.missingDocs`, keep every linter on except the three Mathlib-repository linters §6.7
excludes, and, when the target imports Mathlib, enable Mathlib's standard linter set with exactly
those exclusions. Of these, Mathlib's header linter may instead stay on when the target configures
its license line (`linter.style.header.license`). The target sets these options in Lake's
`leanOptions`, where the audit reads them, and no `-D` among its extra `lean` arguments gives one of
them a value the requirement does not admit or turns off another linter.

## Main declarations

- `BuildOptions`: Lake's resolved `leanOptions` and extra `lean` arguments for one target.
- `OptionValue.readsAs`: the value Lean reads an option value as.
- `argumentSettings`: the options the extra `lean` arguments can set with `-D`.
- `required`: the options every claimed target sets, and the additional Mathlib options.
- `licensed`, `admits`, `meets`: the target configures the header linter's license line; the values
  the requirement admits for a required option, which are its required value and, for the header
  linter, `true` with a configured license.
- `meets_of_sets`: options that set a required option to its required value (`sets`) meet the
  requirement on it.
- `failures`: the executed decision, every failure of one target in a fixed order.
- `failures_eq_nil_iff`: no failure exactly when `Conforming` holds.
- `conforming_of_mathlib`: the Mathlib requirement strengthens the core-only one.
- `conforming_header`, `header_on_unlicensed_fails`, `admits_header_iff`, `admits_of_ne`: what a
  conforming Mathlib target gives the header linter, that a target with the header linter on and no
  license line fails, and that every other required option admits only its required value.
- `Licensed`, `licensed_iff`, `admits_iff`: the license line counts as configured only when the
  options give it, and every value that the options or any `-D` candidate give it is a nonempty
  string; `licensed` and `admits` decide exactly that and what the requirement admits.
- `licensed_header_passes`, `unlicensed_header_fails`: a Mathlib target with the header linter on
  and Acorn's MIT license line has no failure; without the license line it fails with exactly the
  header linter.
- `conforming_autoImplicit`, `conforming_missingDocs`: what a conforming target gives the
  automatic-implicit options and `linter.missingDocs`.
- `missingDocs_unset_fails`: a core-only target (`mathlib = false`) with only the
  automatic-implicit options and no extra `lean` arguments fails with exactly the missing
  `linter.missingDocs`.
- `mem_argumentTexts_iff`: the `-D` reading holds exactly the settings of `Defines`, stated over
  the characters of the arguments.
- `leanArgument_mem_failures_iff`: a `-D` argument fails exactly when some `-D` form sets a
  checked option to a contradicting value.
- `autoImplicit_argument_fails`, `maxHeartbeats_argument_passes`, `linter_argument_fails`,
  `excluded_linter_argument_passes`, `plugin_argument_passes`: fixed argument lists.

## Option names and values

Lake and Lean accept an option key with a leading `weak.` component, which sets the option
after it when that option is declared and is otherwise ignored; `optionOf` reads the option a key
sets. When a target sets one option under both spellings, every value given must be the required
one, except that the header linter may be `true` when the license line is configured: the license
option is given at least once in `leanOptions`, and every value that `leanOptions` or any `-D`
candidate gives it is a nonempty string. Lean parses a string value by the option's declared type
(`Lean.Language.Lean.setOption`): `"true"` and `"false"` for a Boolean option and a numeral for a
natural-number one, so `readsAs` compares a string with a required value that way. A linter
option is an option whose first component is `linter`; turning one off means giving it a value
Lean reads as `false`.

## Boundaries

The decision reads the configuration Lake resolves: its build-type, package and target options,
merged with later entries taking precedence, and its `weakLeanArgs` and `moreLeanArgs`. Of the
extra arguments it reads only their `-D` settings, and any other argument is allowed, including
one that loads a plugin or a setup file. `argumentSettings` models the `lean` command line: every
`-D` it parses starts at the first `D` of an argument that begins with a single `-`, and its
value follows the `D` or is the next argument, so the model reads a superset of the `-D`
settings and can reject a candidate `lean` does not read as one. That correspondence with the
command-line parser of the Lean executable is assumed, read from Lean's `Lean.Shell` source and
its getopt handling; it is neither proved nor observed. That reading only rejects: a `-D` never
configures the license line, which only `leanOptions` does. That Mathlib's header linter at the
pinned release compares the second header line with `linter.style.header.license` is likewise read
from its source (`Mathlib/Tactic/Linter/Header.lean`) and assumed. The decision does not read
`set_option` commands in source, which review checks (`DECL-01`), nor options given to `lake` on
its command line. Which targets are claimed and whether a target imports Mathlib are supplied by the
operational adapter. That `linter.missingDocs` is on establishes only that Lean runs the linter;
its reports are build warnings, which RG2003 rejects. -/

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
command-line or string option value, any other value only when it is `r`. -/
def OptionValue.readsAs : OptionValue → OptionValue → Bool
  | .string s, .bool b => s == toString b
  | .string s, .nat n => s.toNat? == some n
  | v, r => v == r

/-- The options Lake builds one target's modules with. -/
structure BuildOptions where
  /-- Lake's resolved `leanOptions`: build type, package, then target, a later entry for the
  same key replacing an earlier one, so each key occurs once. -/
  options : List (Name × OptionValue)
  /-- Lake's extra `lean` arguments: `weakLeanArgs` and `moreLeanArgs` of the package and the
  target. -/
  arguments : List String
  deriving DecidableEq, Repr

/-- The option a `leanOptions` key sets: the key without a leading `weak.` component. -/
def optionOf : Name → Name
  | .str .anonymous "weak" => .anonymous
  | .str p s => .str (optionOf p) s
  | .num p k => .num (optionOf p) k
  | .anonymous => .anonymous

/-- The first component of a name, when it is a string. -/
def rootOf : Name → Option String
  | .anonymous => none
  | .str p s => some ((rootOf p).getD s)
  | .num p _ => rootOf p

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

/-- The linters a claimed target may turn off for all its modules: exactly the §6.7 exclusions. -/
def exclusions : List Name := [`linter.style.header, `linter.hashCommand, `linter.style.longFile]

/-- The values the options give option `name`, under either spelling. -/
def valuesOf (o : BuildOptions) (name : Name) : List OptionValue :=
  o.options.filterMap fun entry => if optionOf entry.1 = name then some entry.2 else none

/-- The options set `name` to `value`: at least once, and never to another value. -/
def sets (o : BuildOptions) (name : Name) (value : OptionValue) : Bool :=
  !(valuesOf o name).isEmpty && (valuesOf o name).all (·.readsAs value)

/-- Mathlib's header linter, which a Mathlib target turns off or, with its license configured,
may leave on (standard §6.7). -/
def headerLinter : Name := `linter.style.header

/-- The option that gives the license line Mathlib's header linter expects (`String`-valued). -/
def licenseOption : Name := `linter.style.header.license

/-- Lean reads the value as a license line: a nonempty string. -/
def OptionValue.isLicense : OptionValue → Bool
  | .string s => !s.isEmpty
  | _ => false

/-- The values that the target's options and every `-D` candidate of its extra `lean` arguments
give the license option. -/
def licenseValues (o : BuildOptions) : List OptionValue :=
  valuesOf o licenseOption ++
    ((argumentSettings o.arguments).filterMap fun s =>
      if optionOf s.1 = licenseOption then some s.2 else none)

/-- The target configures the license line: its options give the license option at least once,
and every value that its options and every `-D` candidate give it is a nonempty string. -/
def licensed (o : BuildOptions) : Bool :=
  !(valuesOf o licenseOption).isEmpty && (licenseValues o).all OptionValue.isLicense

/-- The target configures the license line, stated without the executed decisions: its options
give the license option a value, and every value that its options and every `-D` candidate of
`argumentSettings` give it is a nonempty string. -/
def Licensed (o : BuildOptions) : Prop :=
  valuesOf o licenseOption ≠ [] ∧
  (∀ v ∈ valuesOf o licenseOption, ∃ t, v = .string t ∧ t ≠ "") ∧
  ∀ s ∈ argumentSettings o.arguments, optionOf s.1 = licenseOption →
    ∃ t, s.2 = .string t ∧ t ≠ ""

/-- `licensed` decides exactly `Licensed`: only the options configure the license line, and a
`-D` candidate can only make it fail. -/
theorem licensed_iff (o : BuildOptions) : licensed o = true ↔ Licensed o := by
  have hl : ∀ v : OptionValue, v.isLicense = true ↔ ∃ t, v = .string t ∧ t ≠ "" := by
    intro v
    cases v <;> simp [OptionValue.isLicense]
  simp [licensed, licenseValues, Licensed, hl, -List.all_filterMap]
  exact fun _ _ => ⟨fun h a b => h b a, fun h b a => h a b⟩

/-- The target gives the required option `r` the value `v` that the requirement admits: the value
Lean reads as the required one, or, for the header linter, Lean's reading of `true` when the
target configures the license line. -/
def admits (o : BuildOptions) (r : Name × OptionValue) (v : OptionValue) : Bool :=
  v.readsAs r.2 || (r.1 == headerLinter && v.readsAs (.bool true) && licensed o)

/-- `admits` decides exactly what the requirement admits, stated without the executed decisions. -/
theorem admits_iff (o : BuildOptions) (r : Name × OptionValue) (v : OptionValue) :
    admits o r v = true ↔
      v.readsAs r.2 = true ∨ (r.1 = headerLinter ∧ v.readsAs (.bool true) = true ∧ Licensed o) := by
  simp [admits, licensed_iff, and_assoc]

/-- The options give the required option `r` a value, and only values that the requirement
admits. -/
def meets (o : BuildOptions) (r : Name × OptionValue) : Bool :=
  !(valuesOf o r.1).isEmpty && (valuesOf o r.1).all (admits o r)

/-- Options that set a required option to its required value meet the requirement on it. -/
theorem meets_of_sets (o : BuildOptions) (r : Name × OptionValue) (h : sets o r.1 r.2 = true) :
    meets o r = true := by
  simp only [sets, meets, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun v hv => by simp [admits, h.2 v hv]⟩

/-- Setting `name` to `value` turns off a linter outside the §6.7 exclusions (§6.2). -/
def disables (name : Name) (value : OptionValue) : Bool :=
  rootOf name == some "linter" && value.readsAs (.bool false) && !exclusions.contains name

/-- The `-D` setting of `name` to `value` gives a required option a value the requirement does
not admit or turns off a linter outside the §6.7 exclusions. -/
def contradicts (o : BuildOptions) (mathlib : Bool) (name : Name) (value : OptionValue) : Bool :=
  (required mathlib).any (fun r => optionOf name == r.1 && !admits o r value) ||
    disables (optionOf name) value

/-- One way a target's build options fail RG2006. -/
inductive Failure where
  /-- A required option is not given, or is given a value the requirement does not admit; `given`
  lists the values the options give. -/
  | option (name : Name) (value : OptionValue) (given : List OptionValue)
  /-- A linter outside the §6.7 exclusions is turned off for every module of the target. -/
  | disabledLinter (name : Name)
  /-- An extra `lean` argument sets `name` to `value` with `-D` against the requirement. -/
  | leanArgument (name : Name) (value : OptionValue)
  deriving DecidableEq, Repr

/-- Every failure of one target's build options: required options in the order of `required`,
then each turned-off linter in option order, then each contradicting `-D` in argument order. -/
def failures (o : BuildOptions) (mathlib : Bool) : List Failure :=
  (required mathlib).filterMap (fun r =>
      if meets o r then none else some (.option r.1 r.2 (valuesOf o r.1))) ++
    o.options.filterMap (fun entry =>
      if disables (optionOf entry.1) entry.2 then some (.disabledLinter (optionOf entry.1))
      else none) ++
    (argumentSettings o.arguments).filterMap fun s =>
      if contradicts o mathlib s.1 s.2 then some (.leanArgument s.1 s.2) else none

/-- An option value as written in `lakefile.lean`. -/
def OptionValue.text : OptionValue → String
  | .string s => s.quote
  | .bool b => toString b
  | .nat n => toString n

/-- What a failure of the option `name` adds to its finding detail: the header linter may also be
`true` in `leanOptions`, with the license line configured there. -/
def licenseHint (name : Name) : String :=
  if optionOf name = headerLinter then
    s!", or set it to true and `{licenseOption}` to your license line, both in `leanOptions`"
  else ""

/-- One failure as a finding detail. -/
def Failure.text : Failure → String
  | .option name value [] => s!"`{name}` is not set; set it to {value.text}" ++ licenseHint name
  | .option name value given =>
    s!"`{name}` is {", ".intercalate (given.map OptionValue.text)}; set it to {value.text}" ++
      licenseHint name
  | .disabledLinter name =>
    s!"`{name}` is off for every module; only the standard §6.7 exclusions may be"
  | .leanArgument name value =>
    s!"an extra `lean` argument sets `{name}` to {value.text}; remove it" ++ licenseHint name

/-- The finding detail of a target's failures. -/
def detail (failures : List Failure) : String :=
  "community-configuration: " ++ "; ".intercalate (failures.map Failure.text)

/-- The RG2006 obligation of one target, stated without the executed Boolean decisions: every
required option is given, and only values that the requirement admits: what Lean reads as its
required value, and for Mathlib's header linter also `true` when the target configures the license
line (`Licensed`); no option turns off a linter outside the §6.7 exclusions; and no `-D` among the
extra `lean` arguments gives a required option a value the requirement does not admit or turns off
such a linter. -/
def Conforming (o : BuildOptions) (mathlib : Bool) : Prop :=
  (∀ r ∈ required mathlib, valuesOf o r.1 ≠ [] ∧ ∀ v ∈ valuesOf o r.1,
    v.readsAs r.2 = true ∨ (r.1 = headerLinter ∧ v.readsAs (.bool true) = true ∧ Licensed o)) ∧
  (∀ entry ∈ o.options, rootOf (optionOf entry.1) = some "linter" →
    entry.2.readsAs (.bool false) = true → optionOf entry.1 ∈ exclusions) ∧
  ∀ s ∈ argumentSettings o.arguments,
    (∀ r ∈ required mathlib, optionOf s.1 = r.1 → s.2.readsAs r.2 = true ∨
      (r.1 = headerLinter ∧ s.2.readsAs (.bool true) = true ∧ Licensed o)) ∧
    (rootOf (optionOf s.1) = some "linter" → s.2.readsAs (.bool false) = true →
      optionOf s.1 ∈ exclusions)

/-- `meets` decides exactly the first conjunct's condition for one option. -/
theorem meets_iff (o : BuildOptions) (r : Name × OptionValue) :
    meets o r = true ↔
      valuesOf o r.1 ≠ [] ∧ ∀ v ∈ valuesOf o r.1, admits o r v = true := by
  simp [meets]

/-- `disables` decides exactly the negation of the second conjunct's condition. -/
theorem disables_iff (name : Name) (value : OptionValue) :
    disables name value = true ↔
      rootOf name = some "linter" ∧ value.readsAs (.bool false) = true ∧ name ∉ exclusions := by
  simp [disables, and_assoc]

/-- `contradicts` decides exactly the negation of the third conjunct's condition. -/
theorem contradicts_eq_false_iff (o : BuildOptions) (mathlib : Bool) (name : Name)
    (value : OptionValue) :
    contradicts o mathlib name value = false ↔
      (∀ r ∈ required mathlib, optionOf name = r.1 → admits o r value = true) ∧
      (rootOf (optionOf name) = some "linter" → value.readsAs (.bool false) = true →
        optionOf name ∈ exclusions) := by
  have := disables_iff (optionOf name) value
  cases h : disables (optionOf name) value <;> simp_all [contradicts]

/-- The decision reports no failure exactly when the target meets its RG2006 obligation. -/
theorem failures_eq_nil_iff (o : BuildOptions) (mathlib : Bool) :
    failures o mathlib = [] ↔ Conforming o mathlib := by
  simp only [failures, Conforming, ← admits_iff, List.append_eq_nil_iff,
    List.filterMap_eq_nil_iff, and_assoc]
  refine and_congr (forall₂_congr fun r _ => ?_)
    (and_congr (forall₂_congr fun e _ => ?_) (forall₂_congr fun s _ => ?_))
  · rw [← meets_iff]
    cases meets o r <;> simp
  · have := disables_iff (optionOf e.1) e.2
    cases h : disables (optionOf e.1) e.2 <;> simp_all
  · rw [← contradicts_eq_false_iff]
    cases contradicts o mathlib s.1 s.2 <;> simp

/-- A target that meets the Mathlib requirement meets the core-only one: `required false` is a
prefix of `required true`, and the linter conditions do not depend on Mathlib. -/
theorem conforming_of_mathlib (o : BuildOptions) (h : Conforming o true) : Conforming o false :=
  ⟨fun r hr => h.1 r (by simp_all [required]), h.2.1,
    fun s hs => ⟨fun r hr => (h.2.2 s hs).1 r (by simp_all [required]), (h.2.2 s hs).2⟩⟩

/-- For an option other than the header linter the requirement admits exactly what Lean reads as
the required value. -/
theorem admits_of_ne (o : BuildOptions) (r : Name × OptionValue) (h : r.1 ≠ headerLinter)
    (v : OptionValue) : admits o r v = v.readsAs r.2 := by
  cases hb : (r.1 == headerLinter)
  · simp [admits, hb]
  · exact absurd (beq_iff_eq.1 hb) h

/-- Every conforming target gives `autoImplicit` and `relaxedAutoImplicit` only values Lean reads
as `false`, in its options and in its `-D` arguments. -/
theorem conforming_autoImplicit (o : BuildOptions) (mathlib : Bool) (h : Conforming o mathlib) :
    ∀ name ∈ [`autoImplicit, `relaxedAutoImplicit],
      (∀ v ∈ valuesOf o name, v.readsAs (.bool false) = true) ∧
      ∀ s ∈ argumentSettings o.arguments, optionOf s.1 = name →
        s.2.readsAs (.bool false) = true := by
  intro name hname
  have hr : (name, OptionValue.bool false) ∈ required mathlib := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
    rcases hname with rfl | rfl <;> simp [required, baseline]
  have hne : name ≠ headerLinter := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
    rcases hname with rfl | rfl <;> simp [headerLinter]
  exact ⟨fun v hv => ((h.1 _ hr).2 v hv).resolve_right fun h' => hne h'.1,
    fun s hs hs' => ((h.2.2 s hs).1 _ hr hs').resolve_right fun h' => hne h'.1⟩

/-- Every conforming target enables `linter.missingDocs`: its options give the option at least
once and only values Lean reads as `true`, and no `-D` among its extra `lean` arguments gives it
another value. -/
theorem conforming_missingDocs (o : BuildOptions) (mathlib : Bool) (h : Conforming o mathlib) :
    valuesOf o `linter.missingDocs ≠ [] ∧
      (∀ v ∈ valuesOf o `linter.missingDocs, v.readsAs (.bool true) = true) ∧
      ∀ s ∈ argumentSettings o.arguments, optionOf s.1 = `linter.missingDocs →
        s.2.readsAs (.bool true) = true := by
  have hr : (`linter.missingDocs, OptionValue.bool true) ∈ required mathlib := by
    simp [required, baseline]
  have hne : (`linter.missingDocs : Name) ≠ headerLinter := by simp [headerLinter]
  exact ⟨(h.1 _ hr).1, fun v hv => ((h.1 _ hr).2 v hv).resolve_right fun h' => hne h'.1,
    fun s hs hs' => ((h.2.2 s hs).1 _ hr hs').resolve_right fun h' => hne h'.1⟩

/-- A core-only target (`mathlib = false`) that turns automatic implicits off, sets no other
option and has no extra `lean` arguments fails with exactly one failure: `linter.missingDocs` is
not set. -/
theorem missingDocs_unset_fails :
    failures ⟨[(`autoImplicit, .bool false), (`relaxedAutoImplicit, .bool false)], []⟩ false =
      [.option `linter.missingDocs (.bool true) []] := by
  simp [failures, required, baseline, meets, admits, valuesOf, optionOf, disables, rootOf,
    exclusions, argumentSettings, argumentTexts, OptionValue.readsAs]

/-- A `-D` string value contradicts the requirement exactly when it is a value the requirement does
not admit for a required option (`admits`), or it is `"false"` for a linter outside the §6.7
exclusions. -/
theorem contradicts_string_eq_true_iff (o : BuildOptions) (mathlib : Bool) (n : Name)
    (value : String) :
    contradicts o mathlib n (.string value) = true ↔
      (∃ r ∈ required mathlib, optionOf n = r.1 ∧ admits o r (.string value) = false) ∨
      (rootOf (optionOf n) = some "linter" ∧ value = "false" ∧ optionOf n ∉ exclusions) := by
  have hfalse : (OptionValue.string value).readsAs (.bool false) = true ↔ value = "false" := by
    simp only [OptionValue.readsAs, beq_iff_eq]
    rfl
  rw [contradicts, Bool.or_eq_true, List.any_eq_true, disables_iff, hfalse]
  simp

/-- The decision reports a `-D` argument exactly when some argument sets a checked option to a
value that contradicts the requirement: `-Dname=value`, also after flags as in `-qD`, or `-D`
followed by `name=value` as the next argument. The name is read as `lean` reads it
(`String.toName`), and a linter is turned off by the string `"false"`. -/
theorem leanArgument_mem_failures_iff (o : BuildOptions) (mathlib : Bool) (n : Name)
    (v : OptionValue) :
    Failure.leanArgument n v ∈ failures o mathlib ↔
      ∃ name value, Defines o.arguments name value ∧ n = name.toName ∧ v = .string value ∧
        ((∃ r ∈ required mathlib, optionOf n = r.1 ∧ admits o r (.string value) = false) ∨
          (rootOf (optionOf n) = some "linter" ∧ value = "false" ∧ optionOf n ∉ exclusions)) := by
  have hmem : Failure.leanArgument n v ∈ failures o mathlib ↔
      (n, v) ∈ argumentSettings o.arguments ∧ contradicts o mathlib n v = true := by
    simp only [failures, List.mem_append, List.mem_filterMap]
    constructor
    · rintro ((⟨r, -, h⟩ | ⟨e, -, h⟩) | ⟨s, hs, h⟩)
      · split at h <;> simp at h
      · split at h <;> simp at h
      · split at h
        · simp only [Option.some.injEq, Failure.leanArgument.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hs, by assumption⟩
        · simp at h
    · rintro ⟨hs, hc⟩
      exact .inr ⟨(n, v), hs, by simp [hc]⟩
  rw [hmem, mem_argumentSettings_iff]
  constructor
  · rintro ⟨⟨name, value, hd, rfl, rfl⟩, hc⟩
    exact ⟨name, value, hd, rfl, rfl, (contradicts_string_eq_true_iff _ _ _ _).1 hc⟩
  · rintro ⟨name, value, hd, rfl, rfl, hc⟩
    exact ⟨⟨name, value, hd, rfl, rfl⟩, (contradicts_string_eq_true_iff _ _ _ _).2 hc⟩

/-! The cases below fix the extra `lean` arguments and hold for every `leanOptions`. Lean's
`String.toName` is `partial`, so the kernel cannot evaluate it: a case whose argument names an
option takes the name `lean` reads as a hypothesis. -/

/-- `-DautoImplicit=true` gives a required option another value, so the target fails. -/
theorem autoImplicit_argument_fails (options : List (Name × OptionValue)) (mathlib : Bool)
    (h : "autoImplicit".toName = `autoImplicit) :
    Failure.leanArgument `autoImplicit (.string "true") ∈
      failures ⟨options, ["-DautoImplicit=true"]⟩ mathlib := by
  rw [leanArgument_mem_failures_iff]
  refine ⟨"autoImplicit", "true", (mem_argumentTexts_iff ["-DautoImplicit=true"] _ _).1 (by decide),
    h.symm, rfl,
    .inl ⟨(`autoImplicit, .bool false), by simp [required, baseline], rfl,
      by rw [admits_of_ne _ _ (by simp [headerLinter])]; decide⟩⟩

/-- `-DmaxHeartbeats=400000` sets no checked option, so it adds no failure. -/
theorem maxHeartbeats_argument_passes (options : List (Name × OptionValue)) (mathlib : Bool)
    (h : "maxHeartbeats".toName = `maxHeartbeats) (n : Name) (v : OptionValue) :
    Failure.leanArgument n v ∉ failures ⟨options, ["-DmaxHeartbeats=400000"]⟩ mathlib := by
  rw [leanArgument_mem_failures_iff]
  rintro ⟨name, value, hd, rfl, rfl, hc⟩
  have ht : argumentTexts ["-DmaxHeartbeats=400000"] = [("maxHeartbeats", "400000")] := by
    decide
  rw [← mem_argumentTexts_iff, ht, List.mem_singleton, Prod.mk.injEq] at hd
  obtain ⟨rfl, rfl⟩ := hd
  have ho : optionOf "maxHeartbeats".toName = `maxHeartbeats := by rw [h]; rfl
  rw [ho] at hc
  cases mathlib <;> simp [required, baseline, mathlibBaseline, rootOf, admits] at hc

/-- `-qD` followed by `weak.linter.unusedVariables=false` turns off a linter outside the §6.7
exclusions, so the target fails. -/
theorem linter_argument_fails (options : List (Name × OptionValue)) (mathlib : Bool)
    (h : "weak.linter.unusedVariables".toName = `weak.linter.unusedVariables) :
    Failure.leanArgument `weak.linter.unusedVariables (.string "false") ∈
      failures ⟨options, ["-qD", "weak.linter.unusedVariables=false"]⟩ mathlib := by
  rw [leanArgument_mem_failures_iff]
  refine ⟨"weak.linter.unusedVariables", "false",
    (mem_argumentTexts_iff ["-qD", "weak.linter.unusedVariables=false"] _ _).1 (by decide),
    h.symm, rfl, .inr ⟨rfl, rfl, ?_⟩⟩
  have ho : optionOf `weak.linter.unusedVariables = `linter.unusedVariables := rfl
  rw [ho]
  simp [exclusions]

/-- `-Dweak.linter.hashCommand=false` turns off a §6.7 exclusion, which a Mathlib target sets to
`false` itself, so it adds no failure. -/
theorem excluded_linter_argument_passes (options : List (Name × OptionValue))
    (h : "weak.linter.hashCommand".toName = `weak.linter.hashCommand) (n : Name)
    (v : OptionValue) :
    Failure.leanArgument n v ∉ failures ⟨options, ["-Dweak.linter.hashCommand=false"]⟩ true := by
  rw [leanArgument_mem_failures_iff]
  rintro ⟨name, value, hd, rfl, rfl, hc⟩
  have ht : argumentTexts ["-Dweak.linter.hashCommand=false"] =
      [("weak.linter.hashCommand", "false")] := by
    decide
  rw [← mem_argumentTexts_iff, ht, List.mem_singleton, Prod.mk.injEq] at hd
  obtain ⟨rfl, rfl⟩ := hd
  have ho : optionOf "weak.linter.hashCommand".toName = `linter.hashCommand := by rw [h]; rfl
  have hr : (OptionValue.string "false").readsAs (.bool false) = true := by decide
  rw [ho] at hc
  simp [required, baseline, mathlibBaseline, exclusions, admits, hr] at hc

/-- Arguments that are not `-D`, such as `--plugin` and `--tstack`, add no failure. -/
theorem plugin_argument_passes (options : List (Name × OptionValue)) (mathlib : Bool) (n : Name)
    (v : OptionValue) :
    Failure.leanArgument n v ∉
      failures ⟨options, ["--plugin=libDemo.dylib", "--tstack=100000"]⟩ mathlib := by
  rw [leanArgument_mem_failures_iff]
  rintro ⟨name, value, hd, -⟩
  have ht : argumentTexts ["--plugin=libDemo.dylib", "--tstack=100000"] = [] := by decide
  rw [← mem_argumentTexts_iff, ht] at hd
  simp at hd

/-! ## Mathlib's header linter

A Mathlib target may leave `linter.style.header` on when it configures the linter's license line,
`linter.style.header.license`; otherwise the requirement is unchanged. -/

/-- No value is read as both `true` and `false`. -/
theorem readsAs_true_false (v : OptionValue) (ht : v.readsAs (.bool true) = true)
    (hf : v.readsAs (.bool false) = true) : False := by
  cases v with
  | string s =>
    simp only [OptionValue.readsAs, beq_iff_eq] at ht hf
    rw [hf] at ht
    exact absurd ht (by decide)
  | bool b => cases b <;> first | exact absurd ht (by decide) | exact absurd hf (by decide)
  | nat n => simp [OptionValue.readsAs] at ht

/-- The header linter, set to `false`, is required of every Mathlib target. -/
theorem header_mem_required : (headerLinter, OptionValue.bool false) ∈ required true := by
  simp [required, mathlibBaseline, headerLinter]

/-- The requirement on the header linter admits `false`, as Lean reads it, and `true` exactly when
the target configures the license line. -/
theorem admits_header_iff (o : BuildOptions) (v : OptionValue) :
    admits o (headerLinter, .bool false) v = true ↔
      v.readsAs (.bool false) = true ∨ (v.readsAs (.bool true) = true ∧ Licensed o) := by
  simp [admits_iff]

/-- A conforming Mathlib target gives the header linter, in its options and in its `-D`
arguments, only values Lean reads as `false`, or reads as `true` while the target configures the
license line; its options give the header linter a value. -/
theorem conforming_header (o : BuildOptions) (h : Conforming o true) :
    valuesOf o headerLinter ≠ [] ∧
      (∀ v ∈ valuesOf o headerLinter,
        v.readsAs (.bool false) = true ∨ (v.readsAs (.bool true) = true ∧ Licensed o)) ∧
      ∀ s ∈ argumentSettings o.arguments, optionOf s.1 = headerLinter →
        s.2.readsAs (.bool false) = true ∨ (s.2.readsAs (.bool true) = true ∧ Licensed o) :=
  ⟨(h.1 _ header_mem_required).1,
    fun v hv => ((h.1 _ header_mem_required).2 v hv).imp_right And.right,
    fun s hs hs' => ((h.2.2 s hs).1 _ header_mem_required hs').imp_right And.right⟩

/-- A Mathlib target that leaves the header linter on and configures no license line fails: the
header linter's `true`, in a value its options give or in a `-D` argument, is not admitted. -/
theorem header_on_unlicensed_fails (o : BuildOptions) (hl : ¬ Licensed o) :
    (∀ v ∈ valuesOf o headerLinter, v.readsAs (.bool true) = true → ¬ Conforming o true) ∧
    (∀ s ∈ argumentSettings o.arguments, optionOf s.1 = headerLinter →
      s.2.readsAs (.bool true) = true → ¬ Conforming o true) := by
  refine ⟨fun v hv ht hc => ?_, fun s hs hs' ht hc => ?_⟩
  · rcases (conforming_header o hc).2.1 v hv with hf | ⟨-, hl'⟩
    · exact readsAs_true_false v ht hf
    · exact hl hl'
  · rcases (conforming_header o hc).2.2 s hs hs' with hf | ⟨-, hl'⟩
    · exact readsAs_true_false s.2 ht hf
    · exact hl hl'

/-- A Mathlib target that turns the header linter on and sets its license line to Acorn's MIT
line, with the other §6.7 options, has no failure. -/
theorem licensed_header_passes :
    failures ⟨[(`autoImplicit, .bool false), (`relaxedAutoImplicit, .bool false),
      (`linter.missingDocs, .bool true), (`linter.mathlibStandardSet, .bool true),
      (`linter.style.header, .bool true),
      (`linter.style.header.license,
        .string "Released under the MIT license as described in the repository LICENSE."),
      (`linter.hashCommand, .bool false), (`linter.style.longFile, .nat 0)], []⟩ true = [] := by
  simp +decide [failures, required, baseline, mathlibBaseline, meets, admits, licensed,
    licenseValues, valuesOf, optionOf, disables, exclusions, argumentSettings, argumentTexts,
    headerLinter, licenseOption, OptionValue.readsAs, OptionValue.isLicense]

/-- The same target without the license line fails with exactly the header linter, set to
`true`, where `false` is required. -/
theorem unlicensed_header_fails :
    failures ⟨[(`autoImplicit, .bool false), (`relaxedAutoImplicit, .bool false),
      (`linter.missingDocs, .bool true), (`linter.mathlibStandardSet, .bool true),
      (`linter.style.header, .bool true),
      (`linter.hashCommand, .bool false), (`linter.style.longFile, .nat 0)], []⟩ true =
      [.option `linter.style.header (.bool false) [.bool true]] := by
  simp [failures, required, baseline, mathlibBaseline, meets, admits, licensed,
    licenseValues, valuesOf, optionOf, disables, rootOf, exclusions, argumentSettings,
    argumentTexts, headerLinter, licenseOption, OptionValue.readsAs]

end RegulaPolicy.Community
