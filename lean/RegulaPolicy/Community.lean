module

import all Init.Meta.Defs
public import RegulaPolicy.Compiler
public import RegulaPolicy.Domain
meta import Regula.Decision

/-! # Community build configuration decision

The decision behind RG2006 for one claimed Lake target (standard §7.1, §6.7 and §6.2): the
options Lake builds its modules with turn automatic implicits off, enable Lean's
`linter.missingDocs` and, when the target imports Mathlib, enable Mathlib's standard linter set
with the three Mathlib-repository linters §6.7 excludes turned off. Of these, Mathlib's header
linter may instead stay on when the target configures its license line
(`linter.style.header.license`). Every other option the target sets for all its modules, in
Lake's `leanOptions` or with a `-D` among its extra `lean` arguments, must be in RG2006's closed
accepted set (`Accepted`) at an accepted value; any other option, at any value, fails, whether
Lean declares it or not. So no target-wide option can stop a warning that Lean reports by default,
except a raised `exponentiation.threshold`, unless one of the arguments for the accepted set below
is wrong.

## Main declarations

- `BuildOptions`: Lake's resolved `leanOptions` and extra `lean` arguments for one target.
- `OptionValue.readsAs`: the value Lean reads an option value as.
- `argumentSettings`: the options the extra `lean` arguments can set with `-D`.
- `required`: the options every claimed target sets, and the additional Mathlib options.
- `Accepted`, `accepts`, `accepts_iff`: the closed accepted set for every other option, and its
  executed decision.
- `warningSettings`, `printSettings`: each `linter.`, `warn.` and `pp.` option that Lean or the
  pinned Mathlib registers, with its accepted value and the file and line of its registration.
- `acceptedRelease_eq`: the arguments for the accepted set were read for the supported Lean
  release, so moving to another release fails the build until they are read again.
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
- `leanArgument_mem_failures_iff`, `unaccepted_mem_failures_iff`: a `-D` argument fails exactly
  when some `-D` form sets a required option to a value it does not admit or another option
  outside the accepted set; an option of `leanOptions` fails exactly when it is no required option
  and outside the accepted set.
- `warn_sorry_option_fails`, `docVersoSuggestions_option_fails`: `leanOptions` that set
  `warn.sorry` or `doc.verso.suggestions` to `false` fail.
- `unlisted_linter_option_fails`, `analyzeTactics_option_fails`: `leanOptions` that set an
  unlisted `linter.` option, or `linter.unusedVariables.analyzeTactics`, to `true` fail.
- `ppUnicode_option_fails`, `ppOneline_option_fails`: `leanOptions` that set `pp.unicode` to
  `false` or `pp.oneline` to `true` fail.
- `accepted_families_pass`: one option of each accepted family adds no failure.
- `autoImplicit_argument_fails`, `linter_argument_fails`, `warn_argument_fails`,
  `undeclared_weak_argument_fails`, `maxHeartbeats_argument_passes`,
  `excluded_linter_argument_passes`, `plugin_argument_passes`: fixed argument lists.
- `optionOf_eq_replacePrefix`: `optionOf` is the call by which Lean removes a leading `weak.`.

## Option names and values

Lake and Lean accept an option key with a leading `weak.` component, which sets the option
after it when that option is declared and is otherwise ignored; `optionOf` reads the option a key
sets, as Lean reads it (`optionOf_eq_replacePrefix`). When a target sets one option under both
spellings, every value given must be the required one, except that the header linter may be
`true` when the license line is configured: the license option is given at least once in
`leanOptions`, and every value that `leanOptions` or any `-D` candidate gives it is a nonempty
string. Lean parses a string value by the option's declared type
(`Lean.Language.Lean.setOption`): `"true"` and `"false"` for a Boolean option and a numeral for a
natural-number one, so `readsAs` compares a string with a required value that way. The name
alone decides: whether Lean applies a `weak.` entry depends on which imported modules declare the
option, so a `weak.` entry for an option that no module declares is refused although Lean ignores
it, and its correction is to delete it.

## The accepted set

`Accepted` admits, besides the required options at the values the requirement admits: the §6.7
exclusions at their prescribed values (`exclusionSettings`), the standard's own choice; the
header linter's license line at a nonempty string, which selects which header the header linter
accepts and silences no other warning; each `linter.` and `warn.` option registered by Lean
`acceptedRelease` (`leanWarningSettings`) or by Mathlib `acceptedMathlib` and its pinned Batteries
(`mathlibWarningSettings`), at the one value that silences nothing its registered default reports;
`warningAsError` and `debugAssertions` at `true` (`checkSwitches`), which add checks; the resource
limits `maxHeartbeats`, `synthInstance.maxHeartbeats`, `maxRecDepth`, `maxSynthPendingDepth`,
`synthInstance.maxSize` and
`exponentiation.threshold` at any natural number (`resourceLimits`); and each `pp.` option
registered by Lean, Mathlib or Qq at its registered default (`printSettings`). Raising a positive
resource limit lets Lean do work it would otherwise stop, and lowering one only stops that work
sooner; `0` means no limit for `maxHeartbeats`, `synthInstance.maxHeartbeats` and `maxRecDepth`
(`Lean/CoreM.lean:487`, `Lean/Exception.lean:248`), so Lean does all the work and hides no
warning. The exception is `exponentiation.threshold`: raising it stops the warning that a power
was not evaluated (`Lean/Util/SafeExponentiation.lean:29`), because Lean evaluates the power
instead. A pretty-printer option changes the text some linters compare, so only its default is
accepted. A `linter.`, `warn.` or `pp.` option not listed, or at another value, is refused. Each
listed value was read from its registration's description or docstring at those revisions and is
not proved. `acceptedRelease_eq` fails the build when the supported Lean release moves; nothing
checked ties `acceptedMathlib` to the Mathlib pin.

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
from its source (`Mathlib/Tactic/Linter/Header.lean`) and assumed. The options a claimed
module's source sets are decided by `sourceFailures`, from the record of Regula's elaboration
observer; the decision does not read options given to `lake` on its command line. A
project that wants a resource limit fixed checks it itself. Which targets are claimed and
whether a target imports Mathlib are supplied by the operational adapter. That
`linter.missingDocs` is on establishes only that Lean runs the linter; its reports are build
warnings, which RG2003 rejects. -/

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

instance (v r : OptionValue) : Decidable (v.ReadsAs r) :=
  decidable_of_iff _ (v.readsAs_iff r)

/-- The options Lake builds one target's modules with. -/
structure BuildOptions where
  /-- Lake's resolved `leanOptions`: build type, package, then target, a later entry for the
  same key replacing an earlier one, so each key occurs once. -/
  options : List (Name × OptionValue)
  /-- Lake's extra `lean` arguments: `weakLeanArgs` and `moreLeanArgs` of the package and the
  target. -/
  arguments : List String
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
      v.ReadsAs r.2 ∨ (r.1 = headerLinter ∧ v.ReadsAs (.bool true) ∧ Licensed o) := by
  simp [admits, licensed_iff, OptionValue.readsAs_iff, and_assoc]

/-- The options give the required option `r` a value, and only values that the requirement
admits. -/
def meets (o : BuildOptions) (r : Name × OptionValue) : Bool :=
  !(valuesOf o r.1).isEmpty && (valuesOf o r.1).all (admits o r)

/-- Options that set a required option to its required value meet the requirement on it. -/
theorem meets_of_sets (o : BuildOptions) (r : Name × OptionValue) (h : sets o r.1 r.2 = true) :
    meets o r = true := by
  simp only [sets, meets, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun v hv => by simp [admits, h.2 v hv]⟩

/-- The Mathlib revision whose option registrations `mathlibWarningSettings` was read from: the one
`integration/mathlib/lakefile.lean` pins, read with the Batteries revision of its manifest. -/
def acceptedMathlib : String := "d13f23b723b8a846827a245b89c10fc7d3f11612"

/-- Each `linter.` and `warn.` option that Lean `acceptedRelease` registers with
`register_builtin_option` or `register_option`, cited by file and line under `src/lean/` of the
toolchain, at the one value that silences nothing its registered default reports: `true` where
its description says `true` turns a warning on or extends it, and its default where `true` narrows
one. Two narrow. `linter.extra.dupNamespace.consecutiveOnly` at `true`, its default, warns only on
consecutive duplicated namespaces. `linter.unusedVariables.analyzeTactics` at `true` counts a
parameter as used when any intermediate tactic state mentions it (`Lean/Linter/UnusedVariables.lean`
line 400), so it is accepted only at its default `false`. `linter.all` at `true` only makes `true`
the default of each linter that `Lean.Linter.getLinterValue` reads (`Lean/Linter/Init.lean:130`);
neither narrowing option is read that way. -/
def leanWarningSettings : List (Name × OptionValue) := [
  -- Lean/AddDecl.lean:71
  (`warn.sorry, .bool true),
  -- Lean/DeprecatedModule.lean:20
  (`linter.deprecated.module, .bool true),
  -- Lean/Elab/DeclModifiers.lean:17
  (`linter.redundantVisibility, .bool true),
  -- Lean/Elab/DeprecatedArg.lean:18
  (`linter.deprecated.arg, .bool true),
  -- Lean/Elab/DeprecatedSyntax.lean:17
  (`linter.deprecated.syntax, .bool true),
  -- Lean/Elab/DocString/Builtin/Postponed.lean:20
  (`linter.doc.deferred, .bool true),
  -- Lean/Elab/MutualDef.lean:497, 1180, 1185, 1190
  (`linter.unusedSectionVars, .bool true),
  (`warn.classDefReducibility, .bool true),
  (`warn.exposeOnPrivate, .bool true),
  (`warn.redundantExpose, .bool true),
  -- Lean/Elab/SetOption.lean:15
  (`linter.deprecated.options, .bool true),
  -- Lean/Elab/Tactic/Lets.lean:25
  (`linter.tactic.unusedName, .bool true),
  -- Lean/Elab/Tactic/RCases.lean:23
  (`linter.unusedRCasesPattern, .bool true),
  -- Lean/Elab/Tactic/Simp.lean:675
  (`linter.unusedSimpArgs, .bool true),
  -- Lean/Elab/Tactic/Simpa.lean:21
  (`linter.unnecessarySimpa, .bool true),
  -- Lean/Linter/AmbiguousOpen.lean:16
  (`linter.ambiguousOpen, .bool true),
  -- Lean/Linter/Builtin.lean:16
  (`linter.suspiciousUnexpanderPatterns, .bool true),
  -- Lean/Linter/CheckUnivs.lean:29
  (`linter.checkUnivs, .bool true),
  -- Lean/Linter/Coe.lean:23
  (`linter.deprecatedCoercions, .bool true),
  -- Lean/Linter/ConstructorAsVariable.lean:25
  (`linter.constructorNameAsVariable, .bool true),
  -- Lean/Linter/DefProp.lean:26
  (`linter.defProp, .bool true),
  -- Lean/Linter/Deprecated.lean:19
  (`linter.deprecated, .bool true),
  -- Lean/Linter/DocsOnAlt.lean:21
  (`linter.tactic.docsOnAlt, .bool true),
  -- Lean/Linter/Extra/DupNamespace.lean:30, 35
  (`linter.extra.dupNamespace, .bool true),
  (`linter.extra.dupNamespace.consecutiveOnly, .bool true),
  -- Lean/Linter/Extra/UnnecessarySeqFocus.lean:44
  (`linter.extra.unnecessarySeqFocus, .bool true),
  -- Lean/Linter/Extra/UnreachableTactic.lean:32
  (`linter.extra.unreachableTactic, .bool true),
  -- Lean/Linter/Extra/UnusedDecidableInType.lean:120
  (`linter.extra.unusedDecidableInType, .bool true),
  -- Lean/Linter/Init.lean:101, 106, 112
  (`linter.all, .bool true),
  (`linter.extra, .bool true),
  (`linter.coreInternal, .bool true),
  -- Lean/Linter/InternalModule.lean:30
  (`linter.coreInternal.internalModule, .bool true),
  -- Lean/Linter/List.lean:31, 40
  (`linter.indexVariables, .bool true),
  (`linter.listVariables, .bool true),
  -- Lean/Linter/MissingDocs.lean:20
  (`linter.missingDocs, .bool true),
  -- Lean/Linter/Omit.lean:17
  (`linter.omit, .bool true),
  -- Lean/Linter/TacticTypeCheck.lean:24
  (`linter.tacticCheckInstances, .bool true),
  -- Lean/Linter/UnusedVariables.lean:84, 89, 94, 99
  (`linter.unusedVariables, .bool true),
  (`linter.unusedVariables.funArgs, .bool true),
  (`linter.unusedVariables.patternVars, .bool true),
  (`linter.unusedVariables.analyzeTactics, .bool false),
  -- Lean/Meta/Tactic/Simp/LoopProtection.lean:17
  (`linter.loopingSimpArgs, .bool true)
]

/-- Each `linter.` and `warn.` option that Mathlib `acceptedMathlib` registers with `register_option`
or `register_linter_set`, or the Batteries revision it pins registers, cited by file and line in
each repository, at the one value that silences nothing its registered default reports: `true`
where its description or docstring says `true` turns a warning, report or linter set on or extends
it, and its default otherwise. The exceptions: `linter.haveLet` at `2`, which its description calls
always active; the bounds `linter.style.longFile`, `linter.style.longFileDefValue` and
`linter.style.longLine.maxLineLength` and the sampling divisor
`linter.tacticAnalysis.tryAtEachStep.fraction` at their defaults, since raising one reports less;
`linter.countHeartbeatsApprox`, which rounds a reported count, and `linter.tacticAnalysis.dummy`, a
test option, at their default `false`. `linter.style.header.license`, a string, has its own entry
in `Accepted`. Options registered only under `scripts/` or `MathlibTest/`, which no Mathlib module
imports, are not listed. -/
def mathlibWarningSettings : List (Name × OptionValue) := [
  -- Mathlib/Init.lean:85, 119, 127
  (`linter.mathlibStandardSet, .bool true),
  (`linter.nightlyRegressionSet, .bool true),
  (`linter.weeklyLintSet, .bool true),
  -- Mathlib/Tactic/CategoryTheory/Coherence.lean:159
  (`warn.refl_coherence, .bool true),
  -- Mathlib/Tactic/FastInstance.lean:23
  (`linter.fast_instance_existing, .bool true),
  -- Mathlib/Tactic/Linter/AuxLemma.lean:56
  (`linter.auxLemma, .bool true),
  -- Mathlib/Tactic/Linter/CommandRanges.lean:41
  (`linter.commandRanges, .bool true),
  -- Mathlib/Tactic/Linter/DeprecatedSyntaxLinter.lean:53, 63, 73, 80, 91, 98, 109
  (`linter.style.refine, .bool true),
  (`linter.style.cases, .bool true),
  (`linter.style.induction, .bool true),
  (`linter.style.admit, .bool true),
  (`linter.style.native, .bool true),
  (`linter.style.nativeDecide, .bool true),
  (`linter.style.maxHeartbeats, .bool true),
  -- Mathlib/Tactic/Linter/DirectoryDependency.lean:70
  (`linter.directoryDependency, .bool true),
  -- Mathlib/Tactic/Linter/DocPrime.lean:37
  (`linter.docPrime, .bool true),
  -- Mathlib/Tactic/Linter/DocString.lean:30, 38, 48
  (`linter.style.docString, .bool true),
  (`linter.style.docString.empty, .bool true),
  (`linter.style.docStringVerso, .bool true),
  -- Mathlib/Tactic/Linter/EmptyLine.lean:79
  (`linter.style.emptyLine, .bool true),
  -- Mathlib/Tactic/Linter/FlexibleLinter.lean:108
  (`linter.flexible, .bool true),
  -- Mathlib/Tactic/Linter/GlobalAttributeIn.lean:90
  (`linter.globalAttributeIn, .bool true),
  -- Mathlib/Tactic/Linter/HashCommandLinter.lean:36
  (`linter.hashCommand, .bool true),
  -- Mathlib/Tactic/Linter/HaveILetI.lean:44
  (`linter.style.haveILetI, .bool true),
  -- Mathlib/Tactic/Linter/HaveLetLinter.lean:44
  (`linter.haveLet, .nat 2),
  -- Mathlib/Tactic/Linter/Header.lean:225
  (`linter.style.header, .bool true),
  -- Mathlib/Tactic/Linter/InternalConstructor.lean:51
  (`linter.internalConstructors, .bool true),
  -- Mathlib/Tactic/Linter/Lint.lean:79
  (`linter.dupNamespace, .bool true),
  -- Mathlib/Tactic/Linter/MinImports.lean:74, 83
  (`linter.minImports, .bool true),
  (`linter.minImports.increases, .bool true),
  -- Mathlib/Tactic/Linter/Multigoal.lean:50
  (`linter.style.multiGoal, .bool true),
  -- Mathlib/Tactic/Linter/OldObtain.lean:70
  (`linter.oldObtain, .bool true),
  -- Mathlib/Tactic/Linter/OverlappingInstances.lean:139
  (`linter.overlappingInstances, .bool true),
  -- Mathlib/Tactic/Linter/PPRoundtrip.lean:32
  (`linter.ppRoundtrip, .bool true),
  -- Mathlib/Tactic/Linter/PrivateModule.lean:65
  (`linter.privateModule, .bool true),
  -- Mathlib/Tactic/Linter/Style.lean:61, 142, 191, 257, 300, 347, 353, 425, 433, 493, 578, 629
  (`linter.style.setOption, .bool true),
  (`linter.style.missingEnd, .bool true),
  (`linter.style.cdot, .bool true),
  (`linter.style.dollarSyntax, .bool true),
  (`linter.style.lambdaSyntax, .bool true),
  (`linter.style.longFile, .nat 0),
  (`linter.style.longFileDefValue, .nat 1500),
  (`linter.style.longLine, .bool true),
  (`linter.style.longLine.maxLineLength, .nat 100),
  (`linter.style.nameCheck, .bool true),
  (`linter.style.openClassical, .bool true),
  (`linter.style.show, .bool true),
  -- Mathlib/Tactic/Linter/TextBased.lean:278, 298, 314, 401, 506, 558, 587
  (`linter.adaptationNote, .bool true),
  (`linter.trailingWhitespace, .bool true),
  (`linter.whitespaceBeforeSemicolon, .bool true),
  (`linter.unicodeLinter, .bool true),
  (`linter.pythonStyle, .bool true),
  (`linter.modulesUpperCamelCase, .bool true),
  (`linter.modulesForbiddenWindows, .bool true),
  -- Mathlib/Tactic/Linter/UnusedInstancesInType.lean:315, 356
  (`linter.unusedDecidableInType, .bool true),
  (`linter.unusedFintypeInType, .bool true),
  -- Mathlib/Tactic/Linter/UnusedTactic.lean:64
  (`linter.unusedTactic, .bool true),
  -- Mathlib/Tactic/Linter/UpstreamableDecl.lean:65, 77, 85
  (`linter.upstreamableDecl, .bool true),
  (`linter.upstreamableDecl.defs, .bool true),
  (`linter.upstreamableDecl.private, .bool true),
  -- Mathlib/Tactic/Linter/Whitespace.lean:40, 47
  (`linter.style.whitespace, .bool true),
  (`linter.style.whitespace.verbose, .bool true),
  -- Mathlib/Tactic/SetNotationForOrder.lean:115
  (`linter.setNotationForOrder, .bool true),
  -- Mathlib/Tactic/Simps/Basic.lean:267, 272
  (`linter.simpsNoConstructor, .bool true),
  (`linter.simpsUnusedCustomDeclarations, .bool true),
  -- Mathlib/Tactic/TacticAnalysis.lean:47, 375
  (`linter.tacticAnalysis, .bool true),
  (`linter.tacticAnalysis.dummy, .bool false),
  -- Mathlib/Tactic/TacticAnalysis/Declarations.lean:184, 199, 207, 217, 227, 245, 271, 299, 366,
  --   376, 387, 507, 516, 525, 537, 546, 559, 593, 704, 715, 726
  (`linter.tacticAnalysis.regressions.linarithToGrind, .bool true),
  (`linter.tacticAnalysis.regressions.ringToGrind, .bool true),
  (`linter.tacticAnalysis.regressions.omegaToLia, .bool true),
  (`linter.tacticAnalysis.omegaToLia, .bool true),
  (`linter.tacticAnalysis.rwaSuggestion, .bool true),
  (`linter.tacticAnalysis.rwMerge, .bool true),
  (`linter.tacticAnalysis.mergeWithGrind, .bool true),
  (`linter.tacticAnalysis.terminalToGrind, .bool true),
  (`linter.tacticAnalysis.tryAtEachStep.fraction, .nat 1),
  (`linter.tacticAnalysis.tryAtEachStep.showTiming, .bool true),
  (`linter.tacticAnalysis.tryAtEachStep.selfReplacements, .bool true),
  (`linter.tacticAnalysis.tryAtEachStepGrind, .bool true),
  (`linter.tacticAnalysis.tryAtEachStepSimpAll, .bool true),
  (`linter.tacticAnalysis.tryAtEachStepAesop, .bool true),
  (`linter.tacticAnalysis.tryAtEachStepGrindSuggestions, .bool true),
  (`linter.tacticAnalysis.tryAtEachStepSimpAllSuggestions, .bool true),
  (`linter.tacticAnalysis.tryAtEachStepFromEnv, .bool true),
  (`linter.tacticAnalysis.introMerge, .bool true),
  (`linter.tacticAnalysis.verifyGrind, .bool true),
  (`linter.tacticAnalysis.verifyGrindSuggestions, .bool true),
  (`linter.tacticAnalysis.verifyGrindOnly, .bool true),
  -- Mathlib/Tactic/Tauto.lean:239, 249
  (`linter.tacticAnalysis.tautoToGrind, .bool true),
  (`linter.tacticAnalysis.regressions.tautoToGrind, .bool true),
  -- Mathlib/Tactic/Translate/Core.lean:126, 133, 140, 147, 154, 160, 165, 171
  (`linter.existingAttributeWarning, .bool true),
  (`linter.translateGenerateName, .bool true),
  (`linter.translateExisting, .bool true),
  (`linter.translateReorder, .bool true),
  (`linter.translateRelevantArg, .bool true),
  (`linter.translateOverwrite, .bool true),
  (`linter.translateRedundant, .bool true),
  (`linter.translate.warnInvalid, .bool true),
  -- Mathlib/Util/CountHeartbeats.lean:252, 263
  (`linter.countHeartbeats, .bool true),
  (`linter.countHeartbeatsApprox, .bool false),
  -- Batteries/Linter/UnnecessarySeqFocus.lean:40
  (`linter.unnecessarySeqFocus, .bool true),
  -- Batteries/Linter/UnreachableTactic.lean:28
  (`linter.unreachableTactic, .bool true),
  -- Batteries/Tactic/Lint/Simp.lean:69
  (`linter.simpNF.respectTransparency, .bool true)
]

/-- The listed `linter.` and `warn.` options with their accepted values. -/
def warningSettings : List (Name × OptionValue) := leanWarningSettings ++ mathlibWarningSettings

/-- Each `pp.` option that Lean `acceptedRelease` registers, or Mathlib `acceptedMathlib` or the Qq
revision it pins registers, cited by file and line, at its registered default. A pretty-printer
option changes the text that some linters compare: with `pp.unicode` at `false` Mathlib's
whitespace linter stops at the first mismatch, `→` printed as `->`, before the missing space it
would report (`Mathlib/Tactic/Linter/Whitespace.lean:203`), and `pp.oneline` at `true` truncates
the text it compares. So each is accepted only at its default; a different printing belongs in an
editor or user setting, not in a target's options. -/
def printSettings : List (Name × OptionValue) := [
  -- Lean/Elab/Util.lean:65
  (`pp.macroStack, .bool false),
  -- Lean/Hygiene.lean:70
  (`pp.sanitizeNames, .bool true),
  -- Lean/Meta/PPGoal.lean:15, 20, 25, 30, 35, 40
  (`pp.auxDecls, .bool false),
  (`pp.implementationDetailHyps, .bool false),
  (`pp.inaccessibleNames, .bool true),
  (`pp.showLetValues, .bool false),
  (`pp.showLetValues.threshold, .nat 0),
  (`pp.showLetValues.tactic.threshold, .nat 255),
  -- Lean/PrettyPrinter.lean:32
  (`pp.exprSizes, .bool false),
  -- Lean/PrettyPrinter/Delaborator/Options.lean:15, 19, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60,
  --   64, 68, 72, 76, 81, 85, 89, 93, 97, 101, 105, 109, 114, 119, 125, 129, 133, 138, 142, 147,
  --   151, 155, 159, 163, 167, 171, 175, 179, 183, 187, 191, 195, 199, 203, 207, 211, 215
  (`pp.maxSteps, .nat 5000),
  (`pp.all, .bool false),
  (`pp.notation, .bool true),
  (`pp.parens, .bool false),
  (`pp.unicode, .bool true),
  (`pp.unicode.fun, .bool false),
  (`pp.match, .bool true),
  (`pp.sorrySource, .bool false),
  (`pp.coercions, .bool true),
  (`pp.coercions.types, .bool false),
  (`pp.universes, .bool false),
  (`pp.fullNames, .bool false),
  (`pp.privateNames, .bool false),
  (`pp.funBinderTypes, .bool false),
  (`pp.piBinderTypes, .bool true),
  (`pp.piBinderNames, .bool false),
  (`pp.piBinderNames.hygienic, .bool false),
  (`pp.foralls, .bool true),
  (`pp.letVarTypes, .bool false),
  (`pp.natLit, .bool false),
  (`pp.numericTypes, .bool false),
  (`pp.mdata, .bool false),
  (`pp.instantiateMVars, .bool true),
  (`pp.mvars, .bool true),
  (`pp.mvars.levels, .bool true),
  (`pp.mvars.anonymous, .bool true),
  (`pp.mvars.withType, .bool false),
  (`pp.mvars.delayed, .bool false),
  (`pp.fvars.anonymous, .bool true),
  (`pp.beta, .bool false),
  (`pp.structureInstances, .bool true),
  (`pp.structureInstances.flatten, .bool true),
  (`pp.structureInstances.defaults, .bool false),
  (`pp.fieldNotation, .bool true),
  (`pp.fieldNotation.generalized, .bool true),
  (`pp.explicit, .bool false),
  (`pp.structureInstanceTypes, .bool false),
  (`pp.safeShadowing, .bool true),
  (`pp.tagAppFns, .bool false),
  (`pp.proofs, .bool false),
  (`pp.proofs.withType, .bool false),
  (`pp.proofs.threshold, .nat 0),
  (`pp.instances, .bool true),
  (`pp.instanceTypes, .bool false),
  (`pp.deepTerms, .bool false),
  (`pp.deepTerms.threshold, .nat 50),
  (`pp.motives.pi, .bool true),
  (`pp.motives.nonConst, .bool false),
  (`pp.motives.all, .bool false),
  -- Lean/PrettyPrinter/Delaborator/TopDownAnalyze.lean:32, 37, 46, 51, 56, 61, 67, 72, 77, 82, 87,
  --   92
  (`pp.analyze, .bool false),
  (`pp.analyze.checkInstances, .bool false),
  (`pp.analyze.typeAscriptions, .bool true),
  (`pp.analyze.trustSubst, .bool false),
  (`pp.analyze.trustOfNat, .bool true),
  (`pp.analyze.trustOfScientific, .bool true),
  (`pp.analyze.trustSubtypeMk, .bool true),
  (`pp.analyze.trustId, .bool true),
  (`pp.analyze.trustKnownFOType2TypeHOFuns, .bool true),
  (`pp.analyze.omitMax, .bool true),
  (`pp.analyze.knowsType, .bool true),
  (`pp.analyze.explicitHoles, .bool false),
  -- Lean/PrettyPrinter/Formatter.lean:597
  (`pp.oneline, .bool false),
  -- Lean/Util/PPExt.lean:15, 19, 23, 27
  (`pp.raw, .bool false),
  (`pp.raw.showInfo, .bool false),
  (`pp.raw.maxDepth, .nat 32),
  (`pp.rawOnError, .bool false),
  -- Mathlib/Data/Prod/Basic.lean:312
  (`pp.numericProj.prod, .bool true),
  -- Mathlib/Util/PPOptions.lean:24
  (`pp.mathlib.binderPredicates, .bool true),
  -- Qq/Delab.lean:17
  (`pp.qq, .bool true)
]

/-- The §6.7 exclusions at the values the standard prescribes for them: Mathlib's header linter
off, `linter.hashCommand` off and no `linter.style.longFile` limit. -/
def exclusionSettings : List (Name × OptionValue) :=
  [(headerLinter, .bool false), (`linter.hashCommand, .bool false),
    (`linter.style.longFile, .nat 0)]

/-- Options that add checks at `true`: `warningAsError` makes Lean report each warning as an
error (`Lean/Log.lean`), and `debugAssertions`, which Lake's `debug` build type sets
(`Lake/Config/LeanConfig.lean`), keeps run-time assertions in compiled code. Neither removes a
message at `true`. -/
def checkSwitches : List Name := [`warningAsError, `debugAssertions]

/-- Resource limits: raising one lets Lean do work that it would otherwise stop with an error
(`maxHeartbeats`, `synthInstance.maxHeartbeats`, `maxRecDepth`, `maxSynthPendingDepth`), keep a
type-class answer that it would otherwise discard and fail without (`synthInstance.maxSize`,
`Lean/Meta/SynthInstance.lean` lines 25 and 467), or skip with a warning
(`exponentiation.threshold`, whose warning reports a power it did not evaluate, so raising it
stops that warning while Lean evaluates the power). Lowering a positive limit only stops that work
sooner; `0` means no limit for `maxHeartbeats` and `synthInstance.maxHeartbeats`
(`Lean/CoreM.lean:487`) and for `maxRecDepth` (`Lean/Exception.lean:248`), so Lean does all the
work and hides no warning. -/
def resourceLimits : List Name :=
  [`maxHeartbeats, `synthInstance.maxHeartbeats, `maxRecDepth, `maxSynthPendingDepth,
    `synthInstance.maxSize, `exponentiation.threshold]

/-- The Lean release whose source the arguments for the accepted options were read from. -/
def acceptedRelease : String := "4.34.1"

/-- The arguments for the accepted options were read for the release this source revision
supports, so a move to another release fails the build until they are read again. -/
theorem acceptedRelease_eq : acceptedRelease = RegulaPolicy.Compiler.version := rfl

/-- Lean reads `v` as a natural number. -/
def OptionValue.readsNat : OptionValue → Bool
  | .nat _ => true
  | .string s => s.toNat?.isSome
  | .bool _ => false

/-- `readsNat` holds exactly for the values Lean reads as some natural number. -/
theorem OptionValue.readsNat_iff (v : OptionValue) :
    v.readsNat = true ↔ ∃ n, v.ReadsAs (.nat n) := by
  cases v with
  | nat m => simp [OptionValue.readsNat, OptionValue.ReadsAs]
  | string s =>
    simp only [OptionValue.readsNat, OptionValue.ReadsAs, Option.isSome_iff_exists]
  | bool b => simp [OptionValue.readsNat, OptionValue.ReadsAs]

/-- `isLicense` holds exactly for the nonempty strings. -/
theorem OptionValue.isLicense_iff (v : OptionValue) :
    v.isLicense = true ↔ ∃ t, v = .string t ∧ t ≠ "" := by
  cases v <;> simp [OptionValue.isLicense]

/-- The option `name` at `value`, other than a required option, is in RG2006's accepted set: a §6.7
exclusion at its prescribed value; the header linter's license line at a nonempty string; a listed
`linter.` or `warn.` option at its listed value (`warningSettings`); one of `checkSwitches` at
`true`; one of `resourceLimits` at a natural number; or a listed `pp.` option at its registered
default (`printSettings`). Except for `exponentiation.threshold`, none can stop a warning that
Lean reports by default: an exclusion is the standard's own; the license string selects which
header the header linter accepts and silences no other warning; a listed value was read from the
option's registration as silencing nothing its default reports; a check switch adds checks; a
resource limit lets Lean do more work, and `0` removes the limit where it means none; a
pretty-printer option keeps the text linters compare at its default. Raising
`exponentiation.threshold` stops the warning that a power was not evaluated, because Lean
evaluates it. Every other `linter.`, `warn.` or `pp.` option, and a listed one at another value,
is refused. That the listed values silence nothing was read from the registrations' descriptions
at Lean `acceptedRelease` and Mathlib `acceptedMathlib`, and is not proved. The name alone
decides: whether Lean applies a `weak.` entry depends on which imported modules declare the
option, so a `weak.` entry is refused for its name even when no module declares it and Lean
ignores it. This is the relation, as a proposition, that `accepts`
decides (`accepts_iff`). -/
def Accepted (name : Name) (value : OptionValue) : Prop :=
  (∃ e ∈ exclusionSettings, e.1 = name ∧ value.ReadsAs e.2) ∨
  (name = licenseOption ∧ ∃ t, value = .string t ∧ t ≠ "") ∨
  (∃ e ∈ warningSettings, e.1 = name ∧ value.ReadsAs e.2) ∨
  (name ∈ checkSwitches ∧ value.ReadsAs (.bool true)) ∨
  (name ∈ resourceLimits ∧ ∃ n, value.ReadsAs (.nat n)) ∨
  ∃ e ∈ printSettings, e.1 = name ∧ value.ReadsAs e.2

/-- The executed decision of `Accepted`. -/
def accepts (name : Name) (value : OptionValue) : Bool :=
  exclusionSettings.any (fun e => e.1 == name && value.readsAs e.2) ||
  (name == licenseOption && value.isLicense) ||
  warningSettings.any (fun e => e.1 == name && value.readsAs e.2) ||
  (checkSwitches.contains name && value.readsAs (.bool true)) ||
  (resourceLimits.contains name && value.readsNat) ||
  printSettings.any (fun e => e.1 == name && value.readsAs e.2)

/-- `accepts` decides exactly `Accepted`. -/
theorem accepts_iff (name : Name) (value : OptionValue) :
    accepts name value = true ↔ Accepted name value := by
  have he : exclusionSettings.any (fun e => e.1 == name && value.readsAs e.2) = true ↔
      ∃ e ∈ exclusionSettings, e.1 = name ∧ value.ReadsAs e.2 := by
    simp [OptionValue.readsAs_iff]
  have hw : warningSettings.any (fun e => e.1 == name && value.readsAs e.2) = true ↔
      ∃ e ∈ warningSettings, e.1 = name ∧ value.ReadsAs e.2 := by
    simp [OptionValue.readsAs_iff]
  have hp : printSettings.any (fun e => e.1 == name && value.readsAs e.2) = true ↔
      ∃ e ∈ printSettings, e.1 = name ∧ value.ReadsAs e.2 := by
    simp [OptionValue.readsAs_iff]
  simp only [accepts, Accepted, Bool.or_eq_true, Bool.and_eq_true, he, hw, hp, beq_iff_eq,
    OptionValue.isLicense_iff, OptionValue.readsAs_iff, OptionValue.readsNat_iff,
    List.contains_iff_mem, or_assoc]

/-- The option `name`, set to `value` for every module, is not a required option and is not in the
accepted set. -/
def unaccepted (mathlib : Bool) (name : Name) (value : OptionValue) : Bool :=
  (required mathlib).all (fun r => r.1 != name) && !accepts name value

/-- `unaccepted` decides exactly that `name` is no required option and `Accepted` fails. -/
theorem unaccepted_iff (mathlib : Bool) (name : Name) (value : OptionValue) :
    unaccepted mathlib name value = true ↔
      (∀ r ∈ required mathlib, r.1 ≠ name) ∧ ¬Accepted name value := by
  rw [← accepts_iff]
  simp [unaccepted]

/-- `unaccepted` fails exactly when the option is required or `Accepted`. -/
theorem unaccepted_eq_false_iff (mathlib : Bool) (name : Name) (value : OptionValue) :
    unaccepted mathlib name value = false ↔
      ((∀ r ∈ required mathlib, r.1 ≠ name) → Accepted name value) := by
  have hall : (required mathlib).all (fun r => r.1 != name) = true ↔
      ∀ r ∈ required mathlib, r.1 ≠ name := by
    simp
  rw [← accepts_iff, ← hall, unaccepted]
  cases (required mathlib).all (fun r => r.1 != name) <;> cases accepts name value <;> simp

/-- The `-D` setting of `name` to `value` gives a required option a value the requirement does
not admit, or sets an option outside the accepted set. -/
def contradicts (o : BuildOptions) (mathlib : Bool) (name : Name) (value : OptionValue) : Bool :=
  (required mathlib).any (fun r => optionOf name == r.1 && !admits o r value) ||
    unaccepted mathlib (optionOf name) value

/-- One way a target's build options fail RG2006. -/
inductive Failure where
  /-- A required option is not given, or is given a value the requirement does not admit; `actual`
  lists the values the options give. -/
  | option (name : Name) (value : OptionValue) (actual : List OptionValue)
  /-- The options set `name`, no required option, to `value` outside the accepted set for every
  module of the target. -/
  | unaccepted (name : Name) (value : OptionValue)
  /-- An extra `lean` argument sets `name` to `value` with `-D` against the requirement. -/
  | leanArgument (name : Name) (value : OptionValue)
  deriving DecidableEq, Repr

/-- Every failure of one target's build options: required options in the order of `required`,
then each option outside the accepted set in option order, then each contradicting `-D` in
argument order. -/
@[regula_decision]
def failures (o : BuildOptions) (mathlib : Bool) : List Failure :=
  (required mathlib).filterMap (fun r =>
      if meets o r then none else some (.option r.1 r.2 (valuesOf o r.1))) ++
    o.options.filterMap (fun entry =>
      if unaccepted mathlib (optionOf entry.1) entry.2 then
        some (.unaccepted (optionOf entry.1) entry.2)
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
  | .unaccepted name value =>
    s!"`{name}` set to {value.text} is not in RG2006's accepted set; remove it"
  | .leanArgument name value =>
    s!"an extra `lean` argument sets `{name}` to {value.text}, which RG2006 does not accept; \
      remove it" ++ licenseHint name

/-- The finding detail of a target's failures. -/
def detail (failures : List Failure) : String :=
  "community-configuration: " ++ "; ".intercalate (failures.map Failure.text)

/-- The RG2006 obligation of one target, stated without the executed Boolean decisions: every
required option is given, and only values that the requirement admits: what Lean reads as its
required value, and for Mathlib's header linter also `true` when the target configures the license
line (`Licensed`); every other option the options set is `Accepted`; and each `-D` among the extra
`lean` arguments gives a required option only a value the requirement admits and sets any other
option only as `Accepted` allows. -/
def Conforming (o : BuildOptions) (mathlib : Bool) : Prop :=
  (∀ r ∈ required mathlib, valuesOf o r.1 ≠ [] ∧ ∀ v ∈ valuesOf o r.1,
    v.ReadsAs r.2 ∨ (r.1 = headerLinter ∧ v.ReadsAs (.bool true) ∧ Licensed o)) ∧
  (∀ entry ∈ o.options, (∀ r ∈ required mathlib, r.1 ≠ optionOf entry.1) →
    Accepted (optionOf entry.1) entry.2) ∧
  ∀ s ∈ argumentSettings o.arguments,
    (∀ r ∈ required mathlib, optionOf s.1 = r.1 → s.2.ReadsAs r.2 ∨
      (r.1 = headerLinter ∧ s.2.ReadsAs (.bool true) ∧ Licensed o)) ∧
    ((∀ r ∈ required mathlib, r.1 ≠ optionOf s.1) → Accepted (optionOf s.1) s.2)

/-- `meets` decides exactly the first conjunct's condition for one option. -/
theorem meets_iff (o : BuildOptions) (r : Name × OptionValue) :
    meets o r = true ↔
      valuesOf o r.1 ≠ [] ∧ ∀ v ∈ valuesOf o r.1, admits o r v = true := by
  simp [meets]

/-- `contradicts` decides exactly the negation of the third conjunct's condition. -/
theorem contradicts_eq_false_iff (o : BuildOptions) (mathlib : Bool) (name : Name)
    (value : OptionValue) :
    contradicts o mathlib name value = false ↔
      (∀ r ∈ required mathlib, optionOf name = r.1 → admits o r value = true) ∧
      ((∀ r ∈ required mathlib, r.1 ≠ optionOf name) → Accepted (optionOf name) value) := by
  rw [contradicts, Bool.or_eq_false_iff, unaccepted_eq_false_iff]
  simp

/-- The decision reports no failure exactly when the target meets its RG2006 obligation. -/
theorem failures_eq_nil_iff (o : BuildOptions) (mathlib : Bool) :
    failures o mathlib = [] ↔ Conforming o mathlib := by
  simp only [failures, Conforming, ← admits_iff, List.append_eq_nil_iff,
    List.filterMap_eq_nil_iff, and_assoc]
  refine and_congr (forall₂_congr fun r _ => ?_)
    (and_congr (forall₂_congr fun e _ => ?_) (forall₂_congr fun s _ => ?_))
  · rw [← meets_iff]
    cases meets o r <;> simp
  · rw [← unaccepted_eq_false_iff]
    cases unaccepted mathlib (optionOf e.1) e.2 <;> simp
  · rw [← contradicts_eq_false_iff]
    cases contradicts o mathlib s.1 s.2 <;> simp

/-- Each value the Mathlib requirement admits for one of Mathlib's options is `Accepted` without
it. -/
theorem accepted_of_mathlibBaseline (o : BuildOptions) (r : Name × OptionValue)
    (hr : r ∈ mathlibBaseline) (v : OptionValue)
    (hv : v.ReadsAs r.2 ∨ (r.1 = headerLinter ∧ v.ReadsAs (.bool true) ∧ Licensed o)) :
    Accepted r.1 v := by
  simp only [mathlibBaseline, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inr (.inr (.inl ⟨(`linter.mathlibStandardSet, .bool true), by decide, rfl,
      hv.elim id (fun h => absurd h.1 (by decide))⟩))
  · rcases hv with hf | ⟨-, ht, -⟩
    · exact .inl ⟨(headerLinter, .bool false), by simp [exclusionSettings], rfl, hf⟩
    · exact .inr (.inr (.inl ⟨(headerLinter, .bool true), by decide, rfl, ht⟩))
  · exact .inl ⟨(`linter.hashCommand, .bool false), by simp [exclusionSettings], rfl,
      hv.elim id (fun h => absurd h.1 (by decide))⟩
  · exact .inl ⟨(`linter.style.longFile, .nat 0), by simp [exclusionSettings], rfl,
      hv.elim id (fun h => absurd h.1 (by decide))⟩

/-- A target that meets the Mathlib requirement meets the core-only one: `required false` is a
prefix of `required true`, and a value the Mathlib requirement admits for one of Mathlib's options
is `Accepted` (`accepted_of_mathlibBaseline`). -/
theorem conforming_of_mathlib (o : BuildOptions) (h : Conforming o true) : Conforming o false := by
  have hreq : ∀ n, (∀ r ∈ required false, r.1 ≠ n) →
      (∀ r ∈ required true, r.1 ≠ n) ∨ ∃ r ∈ mathlibBaseline, r.1 = n := by
    intro n hn
    by_cases hm : ∃ r ∈ mathlibBaseline, r.1 = n
    · exact .inr hm
    · refine .inl fun r hr hrn => ?_
      simp only [required, ite_true, List.mem_append] at hr
      rcases hr with hb | hb
      · exact hn r (by simpa [required] using hb) hrn
      · exact hm ⟨r, hb, hrn⟩
  refine ⟨fun r hr => h.1 r (by simp_all [required]), fun e he hn => ?_,
    fun s hs => ⟨fun r hr => (h.2.2 s hs).1 r (by simp_all [required]), fun hn => ?_⟩⟩
  · rcases hreq _ hn with ht | ⟨r, hr, hre⟩
    · exact h.2.1 e he ht
    · have hm : r ∈ required true := by simp [required, hr]
      have hv : e.2 ∈ valuesOf o r.1 := by
        simp only [valuesOf, List.mem_filterMap]
        exact ⟨e, he, by simp [hre]⟩
      rw [← hre]
      exact accepted_of_mathlibBaseline o r hr e.2 ((h.1 r hm).2 e.2 hv)
  · rcases hreq _ hn with ht | ⟨r, hr, hre⟩
    · exact (h.2.2 s hs).2 ht
    · have hm : r ∈ required true := by simp [required, hr]
      rw [← hre]
      exact accepted_of_mathlibBaseline o r hr s.2 ((h.2.2 s hs).1 r hm hre.symm)


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
      (∀ v ∈ valuesOf o name, v.ReadsAs (.bool false)) ∧
      ∀ s ∈ argumentSettings o.arguments, optionOf s.1 = name →
        s.2.ReadsAs (.bool false) := by
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
      (∀ v ∈ valuesOf o `linter.missingDocs, v.ReadsAs (.bool true)) ∧
      ∀ s ∈ argumentSettings o.arguments, optionOf s.1 = `linter.missingDocs →
        s.2.ReadsAs (.bool true) := by
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
  decide

/-- A `-D` string value contradicts the requirement exactly when it is a value the requirement does
not admit for a required option (`admits`), or it sets another option outside the accepted set. -/
theorem contradicts_string_eq_true_iff (o : BuildOptions) (mathlib : Bool) (n : Name)
    (value : String) :
    contradicts o mathlib n (.string value) = true ↔
      (∃ r ∈ required mathlib, optionOf n = r.1 ∧ admits o r (.string value) = false) ∨
      ((∀ r ∈ required mathlib, r.1 ≠ optionOf n) ∧
        ¬Accepted (optionOf n) (.string value)) := by
  rw [contradicts, Bool.or_eq_true, List.any_eq_true, unaccepted_iff]
  simp

/-- The decision reports a `-D` argument exactly when some argument sets an option to a value that
contradicts the requirement: `-Dname=value`, also after flags as in `-qD`, or `-D` followed by
`name=value` as the next argument. The name is read as `lean` reads it (`String.toName`). -/
theorem leanArgument_mem_failures_iff (o : BuildOptions) (mathlib : Bool) (n : Name)
    (v : OptionValue) :
    Failure.leanArgument n v ∈ failures o mathlib ↔
      ∃ name value, Defines o.arguments name value ∧ n = name.toName ∧ v = .string value ∧
        ((∃ r ∈ required mathlib, optionOf n = r.1 ∧ admits o r (.string value) = false) ∨
          ((∀ r ∈ required mathlib, r.1 ≠ optionOf n) ∧
            ¬Accepted (optionOf n) (.string value))) := by
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

/-- The decision reports `n` at `v` as outside the accepted set exactly when one of the target's
options sets `n`, under either spelling, to `v`, `n` is no required option and `Accepted n v`
fails. -/
theorem unaccepted_mem_failures_iff (o : BuildOptions) (mathlib : Bool) (n : Name)
    (v : OptionValue) :
    Failure.unaccepted n v ∈ failures o mathlib ↔
      ∃ entry ∈ o.options, optionOf entry.1 = n ∧ entry.2 = v ∧
        (∀ r ∈ required mathlib, r.1 ≠ n) ∧ ¬Accepted n v := by
  simp only [failures, List.mem_append, List.mem_filterMap]
  constructor
  · rintro ((⟨r, -, h⟩ | ⟨e, he, h⟩) | ⟨s, -, h⟩)
    · split at h <;> simp at h
    · split at h
      · rename_i hd
        simp only [Option.some.injEq, Failure.unaccepted.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨e, he, rfl, rfl, (unaccepted_iff _ _ _).1 hd⟩
      · simp at h
    · split at h <;> simp at h
  · rintro ⟨e, he, rfl, rfl, hd⟩
    exact .inl (.inr ⟨e, he, by simp [(unaccepted_iff _ _ _).2 hd]⟩)

/-- An option that the options set for every module to a value `unaccepted` refuses is reported. -/
theorem unaccepted_option_fails (o : BuildOptions) (mathlib : Bool) (n : Name) (v : OptionValue)
    (h : (n, v) ∈ o.options) (hn : optionOf n = n) (hu : unaccepted mathlib n v = true) :
    Failure.unaccepted n v ∈ failures o mathlib :=
  (unaccepted_mem_failures_iff o mathlib n v).2 ⟨_, h, hn, rfl, (unaccepted_iff _ _ _).1 hu⟩

/-- `leanOptions` that set `warn.sorry` to `false` fail: Lean's warning for a declaration that
uses `sorry` is one of its default warnings, and `false` is not in the accepted set. -/
theorem warn_sorry_option_fails (o : BuildOptions) (mathlib : Bool)
    (h : (`warn.sorry, OptionValue.bool false) ∈ o.options) :
    Failure.unaccepted `warn.sorry (.bool false) ∈ failures o mathlib :=
  unaccepted_option_fails o mathlib _ _ h rfl (by cases mathlib <;> decide)

/-- `leanOptions` that set `doc.verso.suggestions` to `false` fail: the option is not in the
accepted set at any value, although no list of Lean's warning switches has to name it. -/
theorem docVersoSuggestions_option_fails (o : BuildOptions) (mathlib : Bool)
    (h : (`doc.verso.suggestions, OptionValue.bool false) ∈ o.options) :
    Failure.unaccepted `doc.verso.suggestions (.bool false) ∈ failures o mathlib :=
  unaccepted_option_fails o mathlib _ _ h rfl (by cases mathlib <;> decide)

/-- `leanOptions` that set an unlisted `linter.` option, even to `true`, fail: the accepted set lists
each `linter.` and `warn.` option by name, so one that no listed registration declares is refused. -/
theorem unlisted_linter_option_fails (o : BuildOptions) (mathlib : Bool)
    (h : (`linter.example, OptionValue.bool true) ∈ o.options) :
    Failure.unaccepted `linter.example (.bool true) ∈ failures o mathlib :=
  unaccepted_option_fails o mathlib _ _ h rfl (by cases mathlib <;> decide)

/-- `leanOptions` that set `linter.unusedVariables.analyzeTactics` to `true` fail: at `true` the
linter counts a parameter as used when an intermediate tactic state mentions it, so it can drop a
warning its default `false` reports. -/
theorem analyzeTactics_option_fails (o : BuildOptions) (mathlib : Bool)
    (h : (`linter.unusedVariables.analyzeTactics, OptionValue.bool true) ∈ o.options) :
    Failure.unaccepted `linter.unusedVariables.analyzeTactics (.bool true) ∈ failures o mathlib :=
  unaccepted_option_fails o mathlib _ _ h rfl (by cases mathlib <;> decide)

/-- `leanOptions` that set `pp.unicode` to `false` fail: Mathlib's whitespace linter compares the
printed text, so ASCII printing can stop it before a missing space it would report. -/
theorem ppUnicode_option_fails (o : BuildOptions) (mathlib : Bool)
    (h : (`pp.unicode, OptionValue.bool false) ∈ o.options) :
    Failure.unaccepted `pp.unicode (.bool false) ∈ failures o mathlib :=
  unaccepted_option_fails o mathlib _ _ h rfl (by cases mathlib <;> decide)

/-- `leanOptions` that set `pp.oneline` to `true` fail: it truncates the printed text a linter
compares. -/
theorem ppOneline_option_fails (o : BuildOptions) (mathlib : Bool)
    (h : (`pp.oneline, OptionValue.bool true) ∈ o.options) :
    Failure.unaccepted `pp.oneline (.bool true) ∈ failures o mathlib :=
  unaccepted_option_fails o mathlib _ _ h rfl (by cases mathlib <;> decide)

/-- A core-only target with the required options and one option of each accepted family in
`leanOptions` (a §6.7 exclusion at its value, the license line, listed `linter.` and `warn.`
options at their listed values, among them `linter.extra.dupNamespace.consecutiveOnly` at its
default `true` and `linter.haveLet` at `2`, both check switches, two resource limits, one at `0`,
which means no limit, and a printing option at its default) has no failure. -/
theorem accepted_families_pass :
    failures ⟨[(`autoImplicit, .bool false), (`relaxedAutoImplicit, .bool false),
      (`linter.missingDocs, .bool true), (`weak.linter.hashCommand, .bool false),
      (`linter.style.header.license, .string "MIT"), (`linter.unusedVariables, .bool true),
      (`linter.extra.dupNamespace.consecutiveOnly, .bool true), (`linter.haveLet, .nat 2),
      (`warn.sorry, .bool true), (`warningAsError, .bool true), (`debugAssertions, .bool true),
      (`maxHeartbeats, .nat 0), (`exponentiation.threshold, .nat 512),
      (`pp.unicode, .bool true)], []⟩ false = [] := by
  decide

/-! The cases below fix the extra `lean` arguments and hold for every `leanOptions`. Lean's
`String.toName` is `partial`, and the kernel does not evaluate `String.toNat?`: a case whose
argument names an option or gives a number takes what `lean` reads as a hypothesis. -/

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

/-- A `-D` setting of an option outside the required options that `accepts` refuses is
reported. -/
theorem unaccepted_argument_fails (options : List (Name × OptionValue)) (mathlib : Bool)
    (argument name value : String) (n : Name) (hd : Defines [argument] name value)
    (h : name.toName = n) (hu : unaccepted mathlib (optionOf n) (.string value) = true) :
    Failure.leanArgument n (.string value) ∈ failures ⟨options, [argument]⟩ mathlib := by
  rw [leanArgument_mem_failures_iff]
  exact ⟨name, value, hd, h.symm, rfl, .inr ((unaccepted_iff _ _ _).1 hu)⟩

/-- `-qD` followed by `weak.linter.unusedVariables=false` sets a linter to `false`, outside the
accepted set, so the target fails. -/
theorem linter_argument_fails (options : List (Name × OptionValue)) (mathlib : Bool)
    (h : "weak.linter.unusedVariables".toName = `weak.linter.unusedVariables) :
    Failure.leanArgument `weak.linter.unusedVariables (.string "false") ∈
      failures ⟨options, ["-qD", "weak.linter.unusedVariables=false"]⟩ mathlib := by
  rw [leanArgument_mem_failures_iff]
  exact ⟨"weak.linter.unusedVariables", "false",
    (mem_argumentTexts_iff ["-qD", "weak.linter.unusedVariables=false"] _ _).1 (by decide),
    h.symm, rfl, .inr ((unaccepted_iff _ _ _).1 (by cases mathlib <;> decide))⟩

/-- `-Dwarn.sorry=false` turns off one of Lean's own warnings, outside the accepted set, so the
target fails. -/
theorem warn_argument_fails (options : List (Name × OptionValue)) (mathlib : Bool)
    (h : "warn.sorry".toName = `warn.sorry) :
    Failure.leanArgument `warn.sorry (.string "false") ∈
      failures ⟨options, ["-Dwarn.sorry=false"]⟩ mathlib :=
  unaccepted_argument_fails options mathlib _ "warn.sorry" "false" _
    ((mem_argumentTexts_iff ["-Dwarn.sorry=false"] _ _).1 (by decide)) h
    (by cases mathlib <;> decide)

/-- `-Dweak.warn.example=false` is refused although no module declares `warn.example` and Lean
ignores the setting: a `weak.` entry is classified by its name alone. -/
theorem undeclared_weak_argument_fails (options : List (Name × OptionValue)) (mathlib : Bool)
    (h : "weak.warn.example".toName = `weak.warn.example) :
    Failure.leanArgument `weak.warn.example (.string "false") ∈
      failures ⟨options, ["-Dweak.warn.example=false"]⟩ mathlib :=
  unaccepted_argument_fails options mathlib _ "weak.warn.example" "false" _
    ((mem_argumentTexts_iff ["-Dweak.warn.example=false"] _ _).1 (by decide)) h
    (by cases mathlib <;> decide)

/-- `-DmaxHeartbeats=400000` raises a resource limit, which the accepted set admits at any natural
number, so it adds no failure. -/
theorem maxHeartbeats_argument_passes (options : List (Name × OptionValue)) (mathlib : Bool)
    (h : "maxHeartbeats".toName = `maxHeartbeats) (hn : "400000".toNat? = some 400000)
    (n : Name) (v : OptionValue) :
    Failure.leanArgument n v ∉ failures ⟨options, ["-DmaxHeartbeats=400000"]⟩ mathlib := by
  rw [leanArgument_mem_failures_iff]
  rintro ⟨name, value, hd, rfl, rfl, hc⟩
  have ht : argumentTexts ["-DmaxHeartbeats=400000"] = [("maxHeartbeats", "400000")] := by
    decide
  rw [← mem_argumentTexts_iff, ht, List.mem_singleton, Prod.mk.injEq] at hd
  obtain ⟨rfl, rfl⟩ := hd
  have ho : optionOf "maxHeartbeats".toName = `maxHeartbeats := by rw [h]; rfl
  rw [ho] at hc
  have ha : Accepted `maxHeartbeats (.string "400000") :=
    .inr (.inr (.inr (.inr (.inl ⟨by simp [resourceLimits], 400000, hn⟩))))
  cases mathlib <;> simp [required, baseline, mathlibBaseline, admits, ha] at hc

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
  simp [required, baseline, mathlibBaseline, admits, hr] at hc

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
theorem readsAs_true_false (v : OptionValue) (ht : v.ReadsAs (.bool true))
    (hf : v.ReadsAs (.bool false)) : False := by
  cases v with
  | string s =>
    simp only [OptionValue.ReadsAs] at ht hf
    rw [hf] at ht
    exact absurd ht (by decide)
  | bool b => cases b <;> first | exact absurd ht (by decide) | exact absurd hf (by decide)
  | nat n => simp [OptionValue.ReadsAs] at ht

/-- The header linter, set to `false`, is required of every Mathlib target. -/
theorem header_mem_required : (headerLinter, OptionValue.bool false) ∈ required true := by
  simp [required, mathlibBaseline, headerLinter]

/-- The requirement on the header linter admits `false`, as Lean reads it, and `true` exactly when
the target configures the license line. -/
theorem admits_header_iff (o : BuildOptions) (v : OptionValue) :
    admits o (headerLinter, .bool false) v = true ↔
      v.ReadsAs (.bool false) ∨ (v.ReadsAs (.bool true) ∧ Licensed o) := by
  simp [admits_iff]

/-- A conforming Mathlib target gives the header linter, in its options and in its `-D`
arguments, only values Lean reads as `false`, or reads as `true` while the target configures the
license line; its options give the header linter a value. -/
theorem conforming_header (o : BuildOptions) (h : Conforming o true) :
    valuesOf o headerLinter ≠ [] ∧
      (∀ v ∈ valuesOf o headerLinter,
        v.ReadsAs (.bool false) ∨ (v.ReadsAs (.bool true) ∧ Licensed o)) ∧
      ∀ s ∈ argumentSettings o.arguments, optionOf s.1 = headerLinter →
        s.2.ReadsAs (.bool false) ∨ (s.2.ReadsAs (.bool true) ∧ Licensed o) :=
  ⟨(h.1 _ header_mem_required).1,
    fun v hv => ((h.1 _ header_mem_required).2 v hv).imp_right And.right,
    fun s hs hs' => ((h.2.2 s hs).1 _ header_mem_required hs').imp_right And.right⟩

/-- A Mathlib target that leaves the header linter on and configures no license line fails: the
header linter's `true`, in a value its options give or in a `-D` argument, is not admitted. -/
theorem header_on_unlicensed_fails (o : BuildOptions) (hl : ¬ Licensed o) :
    (∀ v ∈ valuesOf o headerLinter, v.ReadsAs (.bool true) → ¬ Conforming o true) ∧
    (∀ s ∈ argumentSettings o.arguments, optionOf s.1 = headerLinter →
      s.2.ReadsAs (.bool true) → ¬ Conforming o true) := by
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
  decide

/-- The same target without the license line fails with exactly the header linter, set to
`true`, where `false` is required. -/
theorem unlicensed_header_fails :
    failures ⟨[(`autoImplicit, .bool false), (`relaxedAutoImplicit, .bool false),
      (`linter.missingDocs, .bool true), (`linter.mathlibStandardSet, .bool true),
      (`linter.style.header, .bool true),
      (`linter.hashCommand, .bool false), (`linter.style.longFile, .nat 0)], []⟩ true =
      [.option `linter.style.header (.bool false) [.bool true]] := by
  decide

/-! ## Options set in a claimed module's source

Regula's elaboration observer records each option that a claimed module's source sets through
Lean's `set_option` elaborator, with the value and form of its `set_option` syntax
(`RegulaObserver.Setting`). The same accepted set decides them as decides a target's options, with
the one permission that standard §6.2 gives: a community linter turned off for one declaration by
`set_option linter.NAME false in` before a declaration command (`declarationKind`). Lean's default
warnings, the `linter.` and `warn.` options Lean registers (`leanWarningSettings`) whose registered
default is not `false`, are never community linters, and neither are `linter.all` and
`linter.mathlibStandardSet`, which switch many linters at once. An option that a macro of the
pinned toolchain wrote, such as `smartUnfolding` in `rfl'`, is that macro's implementation and
passes, when the operational adapter authenticated the macro's module as the toolchain's own
artifact (`toolchain`); a module's name gives no such receipt. The source sets no `debug.` or
`trace.` option, since the accepted set lists none. An option that elaborator code changes without
`set_option` is not recorded: of Lean's builtin commands only `unlock_limits` also assigns the
options of the enclosing scope, and RG2006 accepts what it sets (`unlockLimits_accepted`); a
temporary change through `withScope`, as in a deriving handler or a `local notation`, is
elaborator code. -/


/-- How a claimed module's source set an option (`RegulaObserver.Form`). -/
inductive SourceForm where
  /-- `set_option name value` as a command. -/
  | command
  /-- `set_option name value in` before one command. -/
  | commandIn
  /-- `set_option name value in` inside a term. -/
  | term
  /-- `set_option name value in` inside a tactic block. -/
  | tactic
  /-- An option set without `set_option` syntax that the observer found. -/
  | elaborated
  deriving DecidableEq, Repr

/-- One option that a claimed module's source set, as Regula's elaboration observer recorded it. -/
structure SourceSetting where
  /-- The option. -/
  name : Name
  /-- The literal value its `set_option` syntax gives, or none when the observer read none. -/
  value : Option OptionValue
  /-- The option's registered default, or none when it is unknown or not a string, Boolean or
  natural number. -/
  registeredDefault : Option OptionValue
  /-- How the source set it. -/
  form : SourceForm
  /-- For the form before one command, the syntax kind of the command that `set_option … in`
  wraps, through each further `set_option … in`; none otherwise. -/
  wrapped : Option Name := none
  /-- The module that declares the macro whose expansion wrote the option's name, or none when the
  name is in the module's source text. -/
  origin : Option Name
  /-- The operational adapter's receipt that a module was loaded from its own `.olean` in the
  pinned toolchain's library directory (`admitToolchainOrigin`), when it gave one for `origin`;
  the module's name alone gives none. -/
  toolchain : Option ToolchainOrigin := none
  /-- Where the option's name is in the module, line and column, as Lean reports them; only the
  report reads it. -/
  location : Nat × Nat := (0, 0)
  deriving DecidableEq, Repr

/-- The syntax kind of a declaration command (`Lean.Parser.Command.declaration`): one `def`,
`theorem`, `instance`, `structure`, `inductive` or other declaration with its modifiers. -/
def declarationKind : Name := `Lean.Parser.Command.declaration

/-- The linter options that switch many linters at once: `linter.all` sets the default of every
linter Lean reads through `Lean.Linter.getLinterValue` (`Lean/Linter/Init.lean:130`), Lean's
default warnings among them, and `linter.mathlibStandardSet` turns Mathlib's standard set on. -/
def linterSwitches : List Name := [`linter.all, `linter.mathlibStandardSet]

/-- A default warning of Lean: a `linter.` or `warn.` option that Lean registers
(`leanWarningSettings`), unless its registered default is known to be `false`. -/
def defaultWarning (name : Name) (registeredDefault : Option OptionValue) : Bool :=
  leanWarningSettings.any (·.1 == name) &&
    !registeredDefault.any (·.readsAs (.bool false))

/-- `defaultWarning`, stated by quantifiers: Lean registers the option as one of its warnings, and
no known registered default reads as `false`. -/
def DefaultWarning (name : Name) (registeredDefault : Option OptionValue) : Prop :=
  (∃ e ∈ leanWarningSettings, e.1 = name) ∧
    ∀ d, registeredDefault = some d → ¬ d.ReadsAs (.bool false)

/-- `defaultWarning` decides exactly `DefaultWarning`. -/
theorem defaultWarning_iff (name : Name) (registeredDefault : Option OptionValue) :
    defaultWarning name registeredDefault = true ↔ DefaultWarning name registeredDefault := by
  cases registeredDefault <;>
    simp [defaultWarning, DefaultWarning, ← OptionValue.readsAs_iff]

/-- A community linter turned off for one declaration: `set_option linter.NAME false in` before a
declaration command, where `linter.NAME` is not a default warning of Lean and switches no set of
linters. -/
def communityDisable (s : SourceSetting) : Bool :=
  s.form == .commandIn && s.wrapped == some declarationKind && s.name.getRoot == `linter &&
    !linterSwitches.contains s.name && s.value.any (·.readsAs (.bool false)) &&
    !defaultWarning s.name s.registeredDefault

/-- `communityDisable`, stated by its parts: the form before one command, which wraps a declaration
command, an option under `linter`, outside `linterSwitches`, whose value reads as `false`, and not a
default warning of Lean. -/
def CommunityDisable (s : SourceSetting) : Prop :=
  s.form = .commandIn ∧ s.wrapped = some declarationKind ∧ s.name.getRoot = `linter ∧
    s.name ∉ linterSwitches ∧ (∃ v, s.value = some v ∧ v.ReadsAs (.bool false)) ∧
    ¬ DefaultWarning s.name s.registeredDefault

/-- `communityDisable` decides exactly `CommunityDisable`. -/
theorem communityDisable_iff (s : SourceSetting) :
    communityDisable s = true ↔ CommunityDisable s := by
  have hd := defaultWarning_iff s.name s.registeredDefault
  cases hv : s.value <;>
    simp [communityDisable, CommunityDisable, hv, ← hd, ← OptionValue.readsAs_iff, and_assoc]

/-- A macro that a module of the pinned toolchain declares wrote the option's name: the adapter
gave a receipt for the module `origin` names. -/
def toolchainWritten (s : SourceSetting) : Bool :=
  match s.origin, s.toolchain with
  | some m, some r => r.moduleName == m
  | _, _ => false

/-- `toolchainWritten`, stated by its receipt: some toolchain receipt names the macro's module. -/
def ToolchainWritten (s : SourceSetting) : Prop :=
  ∃ r, s.toolchain = some r ∧ s.origin = some r.moduleName

/-- `toolchainWritten` decides exactly `ToolchainWritten`. -/
theorem toolchainWritten_iff (s : SourceSetting) :
    toolchainWritten s = true ↔ ToolchainWritten s := by
  unfold toolchainWritten ToolchainWritten
  cases s.origin with
  | none => simp
  | some m =>
    cases s.toolchain with
    | none => simp
    | some r =>
      simp only [beq_iff_eq, Option.some.injEq, exists_eq_left']
      exact ⟨Eq.symm, Eq.symm⟩

/-- RG2006 accepts the option a claimed module's source set, for a target with options `o` that
imports Mathlib when `mathlib`: a toolchain macro wrote it, it turns a community linter off for
one command, or its value is one the requirement admits for a required option and otherwise one
`Accepted` admits. -/
def sourceAccepted (o : BuildOptions) (mathlib : Bool) (s : SourceSetting) : Bool :=
  toolchainWritten s || communityDisable s ||
    match s.value with
    | none => false
    | some v =>
      match (required mathlib).find? (·.1 == s.name) with
      | some r => admits o r v
      | none => accepts s.name v

/-- The relation `sourceAccepted` decides, stated without the executed decisions on the value. -/
def SourceAccepted (o : BuildOptions) (mathlib : Bool) (s : SourceSetting) : Prop :=
  ToolchainWritten s ∨ CommunityDisable s ∨
    ∃ v, s.value = some v ∧
      ((∃ r ∈ required mathlib, r.1 = s.name ∧
          (∀ r' ∈ required mathlib, r'.1 = s.name → r' = r) ∧
          (v.ReadsAs r.2 ∨ (r.1 = headerLinter ∧ v.ReadsAs (.bool true) ∧ Licensed o))) ∨
        ((∀ r ∈ required mathlib, r.1 ≠ s.name) ∧ Accepted s.name v))

/-- Each option is required at most once. -/
theorem required_unique (mathlib : Bool) :
    ∀ r ∈ required mathlib, ∀ r' ∈ required mathlib, r.1 = r'.1 → r = r' := by
  cases mathlib <;> decide

/-- `sourceAccepted` decides exactly `SourceAccepted`. -/
theorem sourceAccepted_iff (o : BuildOptions) (mathlib : Bool) (s : SourceSetting) :
    sourceAccepted o mathlib s = true ↔ SourceAccepted o mathlib s := by
  unfold sourceAccepted SourceAccepted
  simp only [Bool.or_eq_true, or_assoc]
  refine or_congr (toolchainWritten_iff s) (or_congr (communityDisable_iff s) ?_)
  cases hv : s.value with
  | none => simp
  | some v =>
    simp only [Option.some.injEq, exists_eq_left']
    cases hf : (required mathlib).find? (·.1 == s.name) with
    | some r =>
      have hr := List.mem_of_find?_eq_some hf
      have hn : r.1 = s.name := by simpa using List.find?_some hf
      have huniq : ∀ r' ∈ required mathlib, r'.1 = s.name → r' = r := fun r' hr' hn' =>
        required_unique mathlib r' hr' r hr (hn'.trans hn.symm)
      rw [admits_iff]
      constructor
      · intro h; exact .inl ⟨r, hr, hn, huniq, h⟩
      · rintro (⟨r', hr', hn', -, h⟩ | ⟨hnone, -⟩)
        · rwa [huniq r' hr' hn'] at h
        · exact absurd hn (hnone r hr)
    | none =>
      have hnone : ∀ r ∈ required mathlib, r.1 ≠ s.name := fun r hr hn => by
        simpa [hn] using List.find?_eq_none.mp hf r hr
      rw [accepts_iff]
      constructor
      · intro h; exact .inr ⟨hnone, h⟩
      · rintro (⟨r, hr, hn, -⟩ | ⟨-, h⟩)
        · exact absurd hn (hnone r hr)
        · exact h

/-- The options that a claimed module's source set and RG2006 does not accept, in source
order. -/
@[regula_decision]
def sourceFailures (o : BuildOptions) (mathlib : Bool) (settings : List SourceSetting) :
    List SourceSetting :=
  settings.filter (!sourceAccepted o mathlib ·)

/-- The decision reports no source option exactly when RG2006 accepts each. -/
theorem sourceFailures_eq_nil_iff (o : BuildOptions) (mathlib : Bool)
    (settings : List SourceSetting) :
    sourceFailures o mathlib settings = [] ↔ ∀ s ∈ settings, SourceAccepted o mathlib s := by
  simp [sourceFailures, List.filter_eq_nil_iff, sourceAccepted_iff]

/-- One option a module's source set that RG2006 does not accept, as the report names it: where
it is, in `module` (a module's name, or the file a standalone compilation compiled), the option,
its value, and the macro's module when a macro wrote it. -/
def SourceSetting.text (module : String) (s : SourceSetting) : String :=
  let value := match s.value with
    | some v => s!" {v.text}"
    | none => " (a value that is not a literal)"
  let origin := match s.origin with
    | some m => s!", written by a macro of {m}"
    | none => ""
  s!"{module}:{s.location.1}:{s.location.2}: set_option {s.name}{value}{origin}"

/-- The detail of the RG2006 finding for the source options `failures` of `module`. -/
def sourceDetail (module : String) (failures : List SourceSetting) : String :=
  "community-configuration: the source sets options that RG2006 does not accept: " ++
    "; ".intercalate (failures.map (SourceSetting.text module))

/-- A setting the source wrote, with value `v`, by command form `form`. -/
def written (name : Name) (v : OptionValue) (form : SourceForm) : SourceSetting :=
  { name, value := some v, registeredDefault := none, form, origin := none }

/-- `set_option autoImplicit true` in a claimed module fails, whatever the target sets. -/
theorem autoImplicit_source_fails (o : BuildOptions) (mathlib : Bool) :
    sourceAccepted o mathlib (written `autoImplicit (.bool true) .command) = false := by
  cases mathlib <;> rfl

/-- `set_option linter.missingDocs false` as a command fails: only the form before one command
turns a community linter off. -/
theorem missingDocs_command_fails (o : BuildOptions) (mathlib : Bool) :
    sourceAccepted o mathlib (written `linter.missingDocs (.bool false) .command) = false := by
  cases mathlib <;> rfl

/-- `set_option linter.missingDocs false in` before one declaration passes: `linter.missingDocs` is
a community linter (standard §6.2), Lean's default for it being `false`. -/
theorem missingDocs_in_passes (o : BuildOptions) (mathlib : Bool) :
    sourceAccepted o mathlib { written `linter.missingDocs (.bool false) .commandIn with
      registeredDefault := some (.bool false), wrapped := some declarationKind } = true := by
  cases mathlib <;> rfl

/-- `set_option linter.missingDocs false in` before a `section` fails: Lean's expansion of
`cmd in section …` closes the `section` it opens with the `end` that the source wrote for its own
`section`, so the setting reaches every declaration up to that `end`. -/
theorem missingDocs_in_section_fails (o : BuildOptions) (mathlib : Bool) :
    sourceAccepted o mathlib { written `linter.missingDocs (.bool false) .commandIn with
      registeredDefault := some (.bool false),
      wrapped := some `Lean.Parser.Command.section } = false := by
  cases mathlib <;> rfl


/-- `set_option linter.unusedVariables false in` fails: it turns one of Lean's default warnings
off. -/
theorem unusedVariables_in_fails (o : BuildOptions) (mathlib : Bool) :
    sourceAccepted o mathlib { written `linter.unusedVariables (.bool false) .commandIn with
      registeredDefault := some (.bool true) } = false := by
  cases mathlib <;> rfl

/-- `set_option linter.all false in` fails: it switches Lean's default warnings off. -/
theorem linterAll_in_fails (o : BuildOptions) (mathlib : Bool) :
    sourceAccepted o mathlib { written `linter.all (.bool false) .commandIn with
      registeredDefault := some (.bool false) } = false := by
  cases mathlib <;> rfl

/-- `set_option warn.sorry false in` fails: a `warn.` option is never a community linter. -/
theorem warnSorry_in_fails (o : BuildOptions) (mathlib : Bool) :
    sourceAccepted o mathlib { written `warn.sorry (.bool false) .commandIn with
      registeredDefault := some (.bool true) } = false := by
  cases mathlib <;> rfl

/-- `set_option maxHeartbeats 400000 in` passes, as a target option does. -/
theorem maxHeartbeats_in_passes (o : BuildOptions) (mathlib : Bool) :
    sourceAccepted o mathlib (written `maxHeartbeats (.nat 400000) .commandIn) = true := by
  cases mathlib <;> rfl

/-- `set_option debug.skipKernelTC true` and `set_option trace.Meta.synthInstance true in` fail. -/
theorem debug_trace_source_fail (o : BuildOptions) (mathlib : Bool) :
    sourceAccepted o mathlib (written `debug.skipKernelTC (.bool true) .command) = false ∧
      sourceAccepted o mathlib (written `trace.Meta.synthInstance (.bool true) .commandIn) =
        false := by
  cases mathlib <;> exact ⟨rfl, rfl⟩

/-- An option whose value the observer did not read fails, unless a toolchain macro wrote it. -/
theorem unread_source_fails (o : BuildOptions) (mathlib : Bool) (name : Name)
    (form : SourceForm) :
    sourceAccepted o mathlib
      { name, value := none, registeredDefault := none, form, origin := none } = false := by
  simp [sourceAccepted, toolchainWritten, communityDisable]

/-- `smartUnfolding` set to `false` by a macro that `Init.Tactics` declares, as `rfl'` does,
passes when the adapter gave a receipt for `Init.Tactics`. -/
theorem toolchain_macro_passes (o : BuildOptions) (mathlib : Bool) :
    sourceAccepted o mathlib { written `smartUnfolding (.bool false) .tactic with
      origin := some `Init.Tactics,
      toolchain := some ⟨`Init.Tactics, "Init/Tactics.olean", "Init/Tactics.olean",
        by decide, by decide, rfl⟩ } = true := by
  rfl

/-- `set_option autoImplicit true in`, written by a macro that a module named `Lean.Adopter`
declares, fails without a receipt for that module: a module's name does not make it the
toolchain's. -/
theorem nameOnly_macro_fails (o : BuildOptions) (mathlib : Bool) :
    sourceAccepted o mathlib { written `autoImplicit (.bool true) .commandIn with
      origin := some `Lean.Adopter, wrapped := some declarationKind } = false := by
  cases mathlib <;> rfl

/-- The options that `unlock_limits` sets, each to `0` (`Lean/Elab/BuiltinCommand.lean` lines 522
to 527), pass. -/
theorem unlockLimits_accepted (o : BuildOptions) (mathlib : Bool) :
    ∀ name ∈ [`maxHeartbeats, `maxRecDepth, `synthInstance.maxHeartbeats],
      sourceAccepted o mathlib (written name (.nat 0) .command) = true := by
  intro name h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> cases mathlib <;> rfl


end RegulaPolicy.Community
