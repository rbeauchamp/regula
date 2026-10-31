/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# The closed input

The one input every rule of the checker reads: the constants Lean loads from the finished build, the
modules that the build claims, and the profile that the project states. It carries no source text,
message, compiled code, option or build log, so a rule cannot decide anything that is not here.

A value of `Input` has the closed form by its type: no name is that of two constants
(`Draft.unique`), each mentioned constant is held (`Input.closed`), and at least one module is
claimed (`Input.claims`). So a rule has no case for an input that lacks that form. The loader
constructs the first of these (`Regula.Load.Facts.input`), and `Draft.admit` is the one place that
reads the other two, and either refuses the reading or gives the proofs.

The types follow `specification/RegulaSpecification/Input.lean`, and `Draft.admit` decides that
module's admission (`Input.WellFormed`). `specification/RegulaSpecification/Proofs/` proves each
rule function of `Regula.Rules` against the specification's violation predicate, this admission
against its statement, and each field against the environment that `Regula.Load` reads it from.
That Lean's and Lake's interfaces report the build is what the specification's trusted base lists.
-/

public section

namespace Regula.Closed

open Lean (Name)

/-- The kind of a constant, one for each constructor of Lean's `ConstantInfo`. -/
inductive Kind where
  /-- `ConstantInfo.axiomInfo`. -/
  | «axiom»
  /-- `ConstantInfo.defnInfo`. -/
  | «definition»
  /-- `ConstantInfo.thmInfo`. -/
  | «theorem»
  /-- `ConstantInfo.opaqueInfo`. -/
  | «opaque»
  /-- `ConstantInfo.quotInfo`. -/
  | quotient
  /-- `ConstantInfo.inductInfo`. -/
  | «inductive»
  /-- `ConstantInfo.ctorInfo`. -/
  | constructor
  /-- `ConstantInfo.recInfo`. -/
  | recursor
  deriving DecidableEq, Repr

/-- The safety of a constant. Lean gives a definition one `DefinitionSafety` and each other constant
at most an unsafe flag, so this type states no constant that is both unsafe and partial. -/
inductive Safety where
  /-- Neither `ConstantInfo.isUnsafe` nor `ConstantInfo.isPartial`. -/
  | safe
  /-- `ConstantInfo.isUnsafe`. -/
  | «unsafe»
  /-- `ConstantInfo.isPartial`. -/
  | «partial»
  deriving DecidableEq, Repr

/-- One constant of a loaded environment, as Lean reports it from the build's `.olean` files. -/
structure Decl where
  /-- Its name. -/
  name : Name
  /-- The module whose `.olean` holds it (`Environment.getModuleIdxFor?`). -/
  module : Name
  /-- `axiom` when any loaded module's own data states an axiom of this name (Lean's import can drop
  it for a theorem), and otherwise the `ConstantInfo` constructor of the constant Lean keeps. -/
  kind : Kind
  /-- Whether it is safe, unsafe or partial. -/
  safety : Safety
  /-- The constants that the type and value mention, the fields that `Lean.collectAxioms` walks, of
  the constant Lean keeps and of each constant of this name that a loaded module's own data states
  (Lean's import can drop those). -/
  uses : List Name
  /-- The constants its value mentions, for a definition, theorem or opaque constant, and nothing
  for any other constant. -/
  valueUses : List Name
  /-- The constant `@[implemented_by]` names, if any (`Lean.Compiler.getImplementedBy?`). -/
  implementedBy : Option Name
  /-- Whether it is `@[extern]` (`Lean.isExtern`). -/
  isExtern : Bool
  /-- Whether its module belongs to the Lean toolchain's own library. -/
  inToolchain : Bool
  deriving Repr

/-- The foundation profiles a project can state. -/
inductive Profile where
  /-- No axiom. -/
  | kernelOnly
  /-- `propext` and `Quot.sound` only. -/
  | choiceFree
  /-- `propext`, `Quot.sound` and `Classical.choice`. -/
  | standardLogical
  deriving DecidableEq, Repr

namespace Profile

/-- The text by which a project states a profile in `lintDriverArgs`. -/
def spelling : Profile → String
  | .kernelOnly => "kernel-only"
  | .choiceFree => "choice-free"
  | .standardLogical => "standard-logical"

/-- Each profile once. -/
def all : List Profile := [.kernelOnly, .choiceFree, .standardLogical]

/-- `all` lists each profile. -/
theorem mem_all (p : Profile) : p ∈ all := by
  cases p <;> simp [all]

/-- Distinct profiles have distinct spellings. -/
theorem spelling_injective : Function.Injective spelling := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- The profile with the spelling `text`, if any. -/
def ofSpelling? (text : String) : Option Profile :=
  all.find? (·.spelling == text)

/-- `ofSpelling?` gives exactly the profile of a spelling. -/
theorem ofSpelling?_eq_some {text : String} {p : Profile} :
    ofSpelling? text = some p ↔ p.spelling = text := by
  constructor
  · intro h
    simpa using List.find?_some h
  · rintro rfl
    cases p <;> decide

end Profile

/-- What the loader reads of an environment, before the admission. No name is that of two constants:
the constants of an environment are the keys of a hash map, so the loader constructs this. -/
structure Draft where
  /-- The profile that the project states. -/
  profile : Profile
  /-- The claimed modules: each module of a default target of the root package, and each module of
  the root package that their imports reach. -/
  modules : List Name
  /-- The constants of the environment. -/
  decls : List Decl
  /-- Each name is the name of one constant. -/
  unique : (decls.map (·.name)).Nodup

/-- The closed input of one run: a reading that has the closed form. -/
structure Input extends Draft where
  /-- Each mentioned constant is held. -/
  closed : ∀ d ∈ decls, ∀ u ∈ d.uses, ∃ e ∈ decls, e.name = u
  /-- At least one module is claimed, so that a claim of nothing is not read as a pass. -/
  claims : modules ≠ []

/-- The names of `l`, for lookups. -/
def setOf (l : List Name) : Std.HashSet Name := l.foldl (·.insert ·) {}

/-- What folding the names of `l` into a set holds. -/
theorem mem_insertFold (l : List Name) (init : Std.HashSet Name) (x : Name) :
    (l.foldl (·.insert ·) init).contains x = true ↔ x ∈ l ∨ init.contains x = true := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq,
      List.mem_cons]
    constructor
    · rintro (h | rfl | h)
      · exact .inl (.inr h)
      · exact .inl (.inl rfl)
      · exact .inr h
    · rintro ((rfl | h) | h)
      · exact .inr (.inl rfl)
      · exact .inl h
      · exact .inr (.inr h)

/-- `setOf` holds exactly the names of its list. -/
theorem mem_setOf (l : List Name) (x : Name) : (setOf l).contains x = true ↔ x ∈ l := by
  rw [setOf, mem_insertFold]
  simp

namespace Draft

variable (d : Draft)

/-- The first constant that mentions a constant that the reading does not hold, with what it
mentions. -/
def openMention? : Option (Name × Name) :=
  let names := setOf (d.decls.map (·.name))
  d.decls.findSome? fun x => (x.uses.find? (!names.contains ·)).map (x.name, ·)

/-- There is no such constant exactly when each mentioned constant is held. -/
theorem openMention?_eq_none :
    d.openMention? = none ↔ ∀ x ∈ d.decls, ∀ u ∈ x.uses, ∃ e ∈ d.decls, e.name = u := by
  have hnames : ∀ u,
      (setOf (d.decls.map (·.name))).contains u = true ↔ ∃ e ∈ d.decls, e.name = u := by
    intro u
    rw [mem_setOf]
    simp
  simp only [openMention?, List.findSome?_eq_none_iff, Option.map_eq_none_iff, List.find?_eq_none]
  constructor
  · intro h x hx u hu
    exact (hnames u).mp (by simpa using h x hx u hu)
  · intro h x hx u hu
    simp [(hnames u).mpr (h x hx u hu)]

/-- The closed input of the reading, or why it does not have the closed form: a constant that
mentions a constant the reading does not hold, or a claim of no module. -/
def admit : Except String Input :=
  match h : d.openMention? with
  | some (n, u) => .error s!"the constant {n} mentions {u}, which the environment does not hold"
  | none =>
    match hm : d.modules with
    | [] => .error "the build claims no module, so nothing is checked"
    | _ :: _ =>
      .ok { toDraft := d, closed := d.openMention?_eq_none.mp h, claims := by simp [hm] }

end Draft

end Regula.Closed
