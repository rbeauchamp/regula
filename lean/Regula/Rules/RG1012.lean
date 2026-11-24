module

public import Regula.Rule

public section

namespace Regula.Rules.RG1012

open Lean (Name)
open Regula.Closed

def panicFunctions : List Name := [``panicCore, ``panic, ``panicWithPos, ``panicWithPosWithDecl]

def lastString? : Name → Option String
  | .str _ s => some s
  | .num p _ => lastString? p
  | .anonymous => none

def bangNamed (n : Name) : Bool := (lastString? n.eraseMacroScopes).any (·.contains '!')

variable {i : Input} (t : Tables i)

def panicForm (u : Name) : Bool :=
  panicFunctions.contains u || (bangNamed u && !(t.index[u]?).any (·.kind == .theorem))

def hasRunValue (d : Decl) : Bool := d.kind == .definition || d.kind == .opaque

def panicFnGuidance : Guidance :=
  { text := "replace panic!/unreachable!/assert! with intrinsic typing (narrowed input types or \
      impossible-case proofs via nomatch/contradiction) or explicit Option/Except; avoid masking \
      failures with silent default/getD unless part of the specification"
    nonblank := by simp [Char.isWhitespace] }

def bangOpGuidance : Guidance :=
  { text := "replace !-operations with intrinsic typing (Fin, xs[i]'h, or narrowed input types) or \
      explicit Option/Except (such as xs[i]?); avoid masking failures with silent default/getD unless \
      part of the specification"
    nonblank := by simp [Char.isWhitespace] }

def panicGuidance (u : Name) : Guidance :=
  if panicFunctions.contains u then panicFnGuidance else bangOpGuidance

def check : List Violation :=
  t.claimed.filterMap fun d =>
    if hasRunValue d then
      (d.valueUses.find? (panicForm t)).map fun u =>
        violation d s!"its value mentions {u}, a panic form: one of Lean's four panic functions, or a \
          constant that is no theorem and whose name's last string component, with its macro scopes erased, \
          contains `!`, Lean's naming for an operation that panics when it fails"
          (panicGuidance u)
    else none

@[expose] def rule : Rule := { spelling := "RG1012", check := check }

end Regula.Rules.RG1012
