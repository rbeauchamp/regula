module

public import Regula.Rule
import Lean.Compiler.Old

/-!
# RG1006: `unsafe`, `partial`, loop and `partial_fixpoint` declarations

A claimed module holds a constant that is unsafe, partial or named as a recursion helper, without the
exempted form, a constant whose value mentions a loop construct of Lean, or a definition or opaque
constant whose value directly mentions `Lean.Order.fix`, which `partial_fixpoint` elaborates to
(`Lean/Elab/PreDefinition/PartialFixpoint/Main.lean:103-111,191,220`, `Lean/Meta/Order.lean:52-58`,
`Init/Internal/Order/Basic.lean:486` at v4.35.0). That last clause reads no theorem (such as a
realized dependency `.eq_def` lemma) and not `Lean.Order.lfp_monotone` (`inductive_fixpoint`,
`coinductive_fixpoint`, `coinductive`). The other clauses read every claimed constant, and the
exempted form exempts a constant only from the first.
`specification/RegulaSpecification/Rules/RG1006.lean` states the rule and proves this check against it.
-/

public section

namespace Regula.Rules.RG1006

open Lean (Name)
open Regula.Closed

/-- Whether the value of `d` mentions a loop construct. -/
def mentionsLoop (d : Decl) : Bool := loopConstructs.any d.valueUses.contains

/-- Whether `d` is a definition or an opaque constant whose value directly mentions `Lean.Order.fix`. -/
def mentionsOrderFix (d : Decl) : Bool :=
  (d.kind == .definition || d.kind == .opaque) && d.valueUses.contains ``Lean.Order.fix

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

/-- Fix guidance for loop constructs (`while`/`repeat`). -/
def loopGuidance : Guidance :=
  { text := "replace while/repeat loops with finite for iteration, structural recursion, or total \
      recursion using termination_by/decreasing_by or a derived fuel bound"
    nonblank := by simp [Char.isWhitespace] }

/-- Fix guidance for `Lean.Order.fix` (`partial_fixpoint`). -/
def orderFixGuidance : Guidance :=
  { text := "replace partial_fixpoint / Lean.Order.fix with structural recursion, \
      termination_by/decreasing_by, or a derived fuel bound"
    nonblank := by simp [Char.isWhitespace] }

/-- Fix guidance for `unsafe` declarations. -/
def unsafeGuidance : Guidance :=
  { text := "remove unsafe and rewrite as safe total code (structural recursion, \
      termination_by/decreasing_by, or a derived fuel bound); isolate unavoidable runtime entry points \
      outside claimed modules"
    nonblank := by simp [Char.isWhitespace] }

/-- Fix guidance for `partial` declarations. -/
def partialGuidance : Guidance :=
  { text := "remove partial and prove termination via structural recursion, \
      termination_by/decreasing_by, or a derived fuel bound, or change the claimed function to \
      accept and check a supplied witness with a small total checker (any producer kept in \
      claimed code still needs its own termination proof; do not use partial_fixpoint)"
    nonblank := by simp [Char.isWhitespace] }

/-- Fix guidance for a safe declaration forged with a `._unsafe_rec` helper name. -/
def forgedHelperGuidance : Guidance :=
  { text := "do not declare names ending in ._unsafe_rec; rename the declaration so Lean's compiler \
      does not substitute it for the base definition"
    nonblank := by simp [Char.isWhitespace] }

/-- What RG1006 prints of a constant that it reports: its detail text paired with its fix guidance. -/
def escapeReport (d : Decl) : String × Guidance :=
  if mentionsLoop d then
    ("mentions a loop construct of Lean", loopGuidance)
  else if mentionsOrderFix d then
    ("its value mentions Lean.Order.fix, which partial_fixpoint elaborates to", orderFixGuidance)
  else
    match d.safety with
    | .unsafe => ("is unsafe", unsafeGuidance)
    | .partial => ("is partial", partialGuidance)
    | .safe => ("has the name of a recursion helper, and is not partial", forgedHelperGuidance)

/-- The constants of claimed modules that are unsafe, partial or named as a recursion helper, without
the exempted form, whose value mentions a loop construct of Lean, or that are definitions or opaque
constants whose value directly mentions `Lean.Order.fix`. -/
def check : List Violation :=
  t.claimed.filterMap fun d =>
    if ((d.safety != .safe || namedAsHelper d) && !helperForm t d) ||
        mentionsLoop d || mentionsOrderFix d then
      some (let report := escapeReport d; violation d report.1 report.2)
    else none

/-- RG1006, for the registry. Its body is exposed so that the registry reads its spelling (`Regula.Closed.spellings_nodup`). -/
@[expose] def rule : Rule := { spelling := "RG1006", check := check }

end Regula.Rules.RG1006
