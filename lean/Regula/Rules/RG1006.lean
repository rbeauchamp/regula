module

public import Regula.Rule
import Lean.Compiler.Old

/-!
# RG1006: `unsafe`, `partial`, loop and `partial_fixpoint` declarations

A claimed module holds a constant that is unsafe, partial or named as a recursion helper, without the
exempted form, a constant whose value mentions a loop construct of Lean, or a definition or opaque
constant whose value directly mentions `Lean.Order.fix`, which `partial_fixpoint` elaborates to
(`Lean/Elab/PreDefinition/PartialFixpoint/Main.lean:103-111,191,220`, `Lean/Meta/Order.lean:52-58`,
`Init/Internal/Order/Basic.lean:486` at v4.35.0). Theorems (such as realized dependency `.eq_def`
lemmas) and `Lean.Order.lfp_monotone` (`inductive_fixpoint`, `coinductive_fixpoint`, `coinductive`)
are not refused.
`specification/RegulaSpecification/Rules/RG1006.lean` states the rule and proves this check against it.
-/

public section

namespace Regula.Rules.RG1006

open Lean (Name)
open Regula.Closed

/-- Whether the value of `d` mentions a loop construct. -/
def mentionsLoop (d : Decl) : Bool := loopConstructs.any d.valueUses.contains

/-- Whether `d` is a definition or an opaque constant. -/
def hasRunValue (d : Decl) : Bool := d.kind == .definition || d.kind == .opaque

/-- Whether `d` is a definition or an opaque constant whose value directly mentions `Lean.Order.fix`. -/
def mentionsOrderFix (d : Decl) : Bool := hasRunValue d && d.valueUses.contains ``Lean.Order.fix

/-- Whether the compiler reads the name of `d` as a recursion helper's. This is its own test,
whatever the kind or flags of the constant. -/
def namedAsHelper (d : Decl) : Bool := (Lean.Compiler.isUnsafeRecName? d.name).isSome

variable {i : Input} (t : Tables i)

/-- `d` has the name of a recursion helper, and its base is a safe, total definition in its module.
The name is read with the compiler's own test, `Lean.Compiler.isUnsafeRecName?`. The base is a
definition: the base of a `partial def` is an opaque constant, so its helper is no exception. -/
def helperBaseFits (d : Decl) : Bool :=
  match Lean.Compiler.isUnsafeRecName? d.name with
  | some base => t.index[base]?.any fun b =>
      b.kind == .definition && b.module == d.module && b.safety == .safe &&
        b.implementedBy.isNone && !b.isExtern
  | none => false

/-- `d` has the exempted form, beside a safe definition in the same module, which names no origin. -/
def helperForm (d : Decl) : Bool :=
  d.safety == .partial && d.implementedBy.isNone && !d.isExtern && helperBaseFits t d

/-- What RG1006 prints of a constant that it reports. -/
def escapeDetail (d : Decl) : String :=
  if mentionsLoop d then "mentions a loop construct of Lean"
  else if mentionsOrderFix d then "its value mentions Lean.Order.fix, which partial_fixpoint elaborates to"
  else
    match d.safety with
    | .unsafe => "is unsafe"
    | .partial => "is partial"
    | .safe => "has the name of a recursion helper, and is not partial"

/-- The constants of claimed modules that are unsafe, partial or named as a recursion helper, without
the exempted form, whose value mentions a loop construct of Lean, or that are definitions or opaque
constants whose value directly mentions `Lean.Order.fix`. -/
def check : List Violation :=
  t.claimed.filterMap fun d =>
    if ((d.safety != .safe || namedAsHelper d) && !helperForm t d) ||
        mentionsLoop d || mentionsOrderFix d then
      some (violation d (escapeDetail d))
    else none

/-- RG1006, for the registry. Its body is exposed so that the registry reads its spelling (`Regula.Closed.spellings_nodup`). -/
@[expose] def rule : Rule := { spelling := "RG1006", check := check }

end Regula.Rules.RG1006
