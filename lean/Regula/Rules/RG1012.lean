module

public import Regula.Rule

/-!
# RG1012: hidden panics

A definition or opaque constant of a claimed module whose value mentions a panic form: one of Lean's four
panic functions, or a constant that is no theorem and whose name's last string component, with its macro
scopes erased, contains `!`, Lean's naming for an operation that panics when it fails. `panicCore` is
`default` in Lean's logic (`Init/Prelude.lean:3849` at v4.35.0), and its compiled code prints the message and
returns that default unless the variable `LEAN_ABORT_ON_PANIC` is set or the program asked to exit on a panic
(`lean_panic_impl` and `lean_panic_fn`, `src/runtime/object.cpp:176-207` at v4.35.0), so a proved function can
go on with a value that its proofs never considered. Mentions are read directly, with no closure through other
constants, and a theorem is not read, because a proof is never run.
`specification/RegulaSpecification/Rules/RG1012.lean` states the rule and proves this check against it.
-/

public section

namespace Regula.Rules.RG1012

open Lean (Name)
open Regula.Closed

/-- Lean's four panic functions (`Init/Prelude.lean:3849` and `:3863`, `Init/Util.lean:59` and `:81` at
v4.35.0). `panic!`, `unreachable!` and `assert!` elaborate to `panicWithPosWithDecl`. -/
def panicFunctions : List Name := [``panicCore, ``panic, ``panicWithPos, ``panicWithPosWithDecl]

/-- The last string component of a name, past the numeric components that follow it. -/
def lastString? : Name → Option String
  | .str _ s => some s
  | .num p _ => lastString? p
  | .anonymous => none

/-- Whether the last string component of `n`, with its macro scopes erased (`Lean.Name.eraseMacroScopes`),
contains `!`. -/
def bangNamed (n : Name) : Bool := (lastString? n.eraseMacroScopes).any (·.contains '!')

variable {i : Input} (t : Tables i)

/-- Whether `u` is a panic form: one of Lean's four panic functions, or a name that `bangNamed` admits and
that the input does not hold as a theorem. A name that the input does not hold counts. -/
def panicForm (u : Name) : Bool :=
  panicFunctions.contains u || (bangNamed u && !(t.index[u]?).any (·.kind == .theorem))

/-- Whether `d` is a definition or an opaque constant. -/
def hasRunValue (d : Decl) : Bool := d.kind == .definition || d.kind == .opaque

/-- What RG1012 prints of a constant that it reports: the first panic form that its value mentions. -/
def panicDetail (d : Decl) : String :=
  match d.valueUses.find? (panicForm t) with
  | some u => s!"its value mentions {u}, which can panic and then returns a default value"
  | none => "its value mentions a panic form"

/-- The definitions and opaque constants of claimed modules whose value mentions a panic form. -/
def check : List Violation :=
  t.claimed.filterMap fun d =>
    if hasRunValue d && d.valueUses.any (panicForm t) then some (violation d (panicDetail t d))
    else none

/-- RG1012, for the registry. Its body is exposed so that the registry reads its spelling (`Regula.Closed.spellings_nodup`). -/
@[expose] def rule : Rule := { spelling := "RG1012", check := check }

end Regula.Rules.RG1012
