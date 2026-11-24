module

public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace Regula.Closed

open Lean (Name)

inductive Kind where
  | «axiom»
  | «definition»
  | «theorem»
  | «opaque»
  | quotient
  | «inductive»
  | constructor
  | recursor
  deriving DecidableEq, Repr

inductive Safety where
  | safe
  | «unsafe»
  | «partial»
  deriving DecidableEq, Repr

inductive CtorIdxForm where
  | none
  | defn (induct : Name)
  | impl (induct : Name)
  deriving DecidableEq, Repr

structure Decl where
  name : Name
  module : Name
  kind : Kind
  safety : Safety
  uses : List Name
  valueUses : List Name
  implementedBy : Option Name
  isExtern : Bool
  initFn : Option Name
  inToolchain : Bool
  ctorIdxForm : CtorIdxForm
  deriving Repr

inductive Profile where
  | kernelOnly
  | choiceFree
  | standardLogical
  deriving DecidableEq, Repr

namespace Profile

def spelling : Profile → String
  | .kernelOnly => "kernel-only"
  | .choiceFree => "choice-free"
  | .standardLogical => "standard-logical"

def all : List Profile := [.kernelOnly, .choiceFree, .standardLogical]

theorem mem_all (p : Profile) : p ∈ all := by
  cases p <;> simp [all]

theorem spelling_injective : Function.Injective spelling := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

def ofSpelling? (text : String) : Option Profile :=
  all.find? (·.spelling == text)

theorem ofSpelling?_eq_some {text : String} {p : Profile} :
    ofSpelling? text = some p ↔ p.spelling = text := by
  constructor
  · intro h
    simpa using List.find?_some h
  · rintro rfl
    cases p <;> decide

end Profile

structure CSimpEntry where
  module : Name
  thm : Name
  deriving DecidableEq, Repr

structure Draft where
  profile : Profile
  modules : List Name
  moduleFiles : List Name
  claimedConstants : List Name
  csimps : List CSimpEntry
  decls : List Decl
  unique : (decls.map (·.name)).Nodup

structure Input extends Draft where
  closed : ∀ d ∈ decls, ∀ u ∈ d.uses, ∃ e ∈ decls, e.name = u
  claims : modules ≠ []

def setOf (l : List Name) : Std.HashSet Name := l.foldl (·.insert ·) {}

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

theorem mem_setOf (l : List Name) (x : Name) : (setOf l).contains x = true ↔ x ∈ l := by
  rw [setOf, mem_insertFold]
  simp

namespace Draft

variable (d : Draft)

def openMention? : Option (Name × Name) :=
  let names := setOf (d.decls.map (·.name))
  d.decls.findSome? fun x => (x.uses.find? (!names.contains ·)).map (x.name, ·)

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
