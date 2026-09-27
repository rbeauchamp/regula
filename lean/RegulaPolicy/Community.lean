module

/-! # Community build configuration decision

The decision behind RG2006 for one claimed Lake target (standard §8.1, §6.7 and §6.2): the
options Lake builds its modules with turn automatic implicits off, keep every linter on except
the three Mathlib-repository linters §6.7 excludes, and, when the target imports Mathlib, enable
Mathlib's standard linter set with exactly those exclusions. The target passes Lean options only
through Lake's `leanOptions`, where the audit reads them.

## Main declarations

- `BuildOptions`: Lake's resolved `leanOptions` and extra `lean` arguments for one target.
- `required`: the options every claimed target sets, and the additional Mathlib options.
- `failures`: the executed decision, every failure of one target in a fixed order.
- `failures_eq_nil_iff`: no failure exactly when `Conforming` holds.
- `conforming_of_mathlib`: the Mathlib requirement strengthens the core-only one.

## Option names

Lake and Lean accept an option key with a leading `weak.` component, which sets the option
after it when that option is declared and is otherwise ignored; `optionOf` reads the option a key
sets. When a target sets one option under both spellings, every value given must be the required
one. A linter option is an option whose first component is `linter`; turning one off means
setting it to `false`.

## Boundaries

The decision reads the configuration Lake resolves: its build-type, package and target options,
merged with later entries taking precedence, and its `weakLeanArgs` and `moreLeanArgs`. It does
not read `set_option` commands in source, which review checks (`DECL-01`), nor options given to
`lake` on its command line. Which targets are claimed and whether a target imports Mathlib are
supplied by the operational adapter. The `linter.missingDocs` requirement of §6.7 is not part of
this decision yet. -/

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

/-- The options every claimed target sets (standard §8.1): no automatic implicits. -/
def baseline : List (Name × OptionValue) :=
  [(`autoImplicit, .bool false), (`relaxedAutoImplicit, .bool false)]

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
  !(valuesOf o name).isEmpty && (valuesOf o name).all (· == value)

/-- Setting `name` to `value` turns off a linter outside the §6.7 exclusions (§6.2). -/
def disables (name : Name) (value : OptionValue) : Bool :=
  rootOf name == some "linter" && value == .bool false && !exclusions.contains name

/-- One way a target's build options fail RG2006. -/
inductive Failure where
  /-- A required option is not set to its value; `given` lists the values the options give. -/
  | option (name : Name) (value : OptionValue) (given : List OptionValue)
  /-- A linter outside the §6.7 exclusions is turned off for every module of the target. -/
  | disabledLinter (name : Name)
  /-- The target passes extra arguments to `lean`, which can set options the audit does not
  read. -/
  | leanArguments (arguments : List String)
  deriving DecidableEq, Repr

/-- Every failure of one target's build options: required options in the order of `required`,
then each turned-off linter in option order, then the extra arguments. -/
def failures (o : BuildOptions) (mathlib : Bool) : List Failure :=
  (required mathlib).filterMap (fun r =>
      if sets o r.1 r.2 then none else some (.option r.1 r.2 (valuesOf o r.1))) ++
    o.options.filterMap (fun entry =>
      if disables (optionOf entry.1) entry.2 then some (.disabledLinter (optionOf entry.1))
      else none) ++
    if o.arguments.isEmpty then [] else [.leanArguments o.arguments]

/-- An option value as written in `lakefile.lean`. -/
def OptionValue.text : OptionValue → String
  | .string s => s.quote
  | .bool b => toString b
  | .nat n => toString n

/-- One failure as a finding detail. -/
def Failure.text : Failure → String
  | .option name value [] => s!"`{name}` is not set; set it to {value.text}"
  | .option name value given =>
    s!"`{name}` is {", ".intercalate (given.map OptionValue.text)}; set it to {value.text}"
  | .disabledLinter name =>
    s!"`{name}` is off for every module; only the standard §6.7 exclusions may be"
  | .leanArguments arguments =>
    s!"extra `lean` arguments {arguments}; set options in `leanOptions` instead"

/-- The finding detail of a target's failures. -/
def detail (failures : List Failure) : String :=
  "community-configuration: " ++ "; ".intercalate (failures.map Failure.text)

/-- The RG2006 obligation of one target, stated without the executed Boolean functions: every
required option is given, and only its required value; no option turns off a linter outside
the §6.7 exclusions; and there are no extra `lean` arguments. -/
def Conforming (o : BuildOptions) (mathlib : Bool) : Prop :=
  (∀ r ∈ required mathlib, valuesOf o r.1 ≠ [] ∧ ∀ v ∈ valuesOf o r.1, v = r.2) ∧
  (∀ entry ∈ o.options, rootOf (optionOf entry.1) = some "linter" → entry.2 = .bool false →
    optionOf entry.1 ∈ exclusions) ∧
  o.arguments = []

/-- `sets` decides exactly the first conjunct's condition for one option. -/
theorem sets_iff (o : BuildOptions) (name : Name) (value : OptionValue) :
    sets o name value = true ↔ valuesOf o name ≠ [] ∧ ∀ v ∈ valuesOf o name, v = value := by
  simp [sets]

/-- `disables` decides exactly the negation of the second conjunct's condition. -/
theorem disables_iff (name : Name) (value : OptionValue) :
    disables name value = true ↔
      rootOf name = some "linter" ∧ value = .bool false ∧ name ∉ exclusions := by
  simp [disables, and_assoc]

/-- The decision reports no failure exactly when the target meets its RG2006 obligation. -/
theorem failures_eq_nil_iff (o : BuildOptions) (mathlib : Bool) :
    failures o mathlib = [] ↔ Conforming o mathlib := by
  simp only [failures, Conforming, List.append_eq_nil_iff, List.filterMap_eq_nil_iff, and_assoc]
  refine and_congr (forall₂_congr fun r _ => ?_) (and_congr (forall₂_congr fun e _ => ?_) ?_)
  · rw [← sets_iff]
    cases sets o r.1 r.2 <;> simp
  · have := disables_iff (optionOf e.1) e.2
    cases h : disables (optionOf e.1) e.2 <;> simp_all
  · cases o.arguments <;> simp

/-- A target that meets the Mathlib requirement meets the core-only one: `required false` is a
prefix of `required true`, and the other two conditions do not depend on Mathlib. -/
theorem conforming_of_mathlib (o : BuildOptions) (h : Conforming o true) : Conforming o false :=
  ⟨fun r hr => h.1 r (by simp_all [required]), h.2⟩

/-- Every conforming target sets `autoImplicit` and `relaxedAutoImplicit` to `false`. -/
theorem conforming_autoImplicit (o : BuildOptions) (mathlib : Bool) (h : Conforming o mathlib) :
    (∀ v ∈ valuesOf o `autoImplicit, v = .bool false) ∧
      ∀ v ∈ valuesOf o `relaxedAutoImplicit, v = .bool false :=
  ⟨(h.1 (`autoImplicit, .bool false) (by simp [required, baseline])).2,
    (h.1 (`relaxedAutoImplicit, .bool false) (by simp [required, baseline])).2⟩

end RegulaPolicy.Community
