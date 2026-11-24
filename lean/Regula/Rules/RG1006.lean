module

public import Regula.Rule
import Lean.Compiler.Old

public section

namespace Regula.Rules.RG1006

open Lean (Name)
open Regula.Closed

def mentionsLoop (d : Decl) : Bool := loopConstructs.any d.valueUses.contains

def mentionsOrderFix (d : Decl) : Bool :=
  (d.kind == .definition || d.kind == .opaque) && d.valueUses.contains ``Lean.Order.fix

def namedAsHelper (d : Decl) : Bool := (Lean.Compiler.isUnsafeRecName? d.name).isSome

variable {i : Input} (t : Tables i)

def helperBaseFits (d : Decl) : Bool :=
  match Lean.Compiler.isUnsafeRecName? d.name with
  | some base => t.index[base]?.any fun b =>
      b.kind == .definition && b.module == d.module && b.safety == .safe &&
        b.implementedBy.isNone && !b.isExtern
  | none => false

def helperForm (d : Decl) : Bool :=
  d.safety == .partial && d.implementedBy.isNone && !d.isExtern && helperBaseFits t d

def loopGuidance : Guidance :=
  { text := "replace while/repeat loops with finite for iteration, structural recursion, or total \
      recursion using termination_by/decreasing_by or a derived fuel bound"
    nonblank := by simp [Char.isWhitespace] }

def orderFixGuidance : Guidance :=
  { text := "replace partial_fixpoint / Lean.Order.fix with structural recursion, \
      termination_by/decreasing_by, or a derived fuel bound"
    nonblank := by simp [Char.isWhitespace] }

def unsafeGuidance : Guidance :=
  { text := "remove unsafe and rewrite as safe total code (structural recursion, \
      termination_by/decreasing_by, or a derived fuel bound); isolate unavoidable runtime entry points \
      outside claimed modules"
    nonblank := by simp [Char.isWhitespace] }

def partialGuidance : Guidance :=
  { text := "remove partial and prove termination via structural recursion, \
      termination_by/decreasing_by, or a derived fuel bound, or change the claimed function to \
      accept and check a supplied witness with a small total checker (any producer kept in \
      claimed code still needs its own termination proof; do not use partial_fixpoint)"
    nonblank := by simp [Char.isWhitespace] }

def forgedHelperGuidance : Guidance :=
  { text := "do not declare names ending in ._unsafe_rec; rename the declaration so Lean's compiler \
      does not substitute it for the base definition"
    nonblank := by simp [Char.isWhitespace] }

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

def check : List Violation :=
  t.claimed.filterMap fun d =>
    if ((d.safety != .safe || namedAsHelper d) && !helperForm t d && !t.ctorIdxImpl d) ||
        mentionsLoop d || mentionsOrderFix d then
      some (let report := escapeReport d; violation d report.1 report.2)
    else none

@[expose] def rule : Rule := { spelling := "RG1006", check := check }

end Regula.Rules.RG1006
