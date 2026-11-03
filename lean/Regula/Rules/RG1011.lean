module

public import Regula.Rule

/-!
# RG1011: replaced compiled code

A constant of a claimed module has `@[implemented_by]` or `@[extern]`, so a compiled program runs
other code in its place than the definition that its proofs are about. The loader reads both with
`Lean.Compiler.getImplementedBy?` and `Lean.isExtern`, the queries by which Lean's compiler decides
what it compiles for a constant (`shouldGenerateCode`, `Lean/Compiler/LCNF/Main.lean:34` and `:40` at
v4.35.0). `specification/RegulaSpecification/Rules/RG1011.lean` states the rule and proves this check
against it.
-/

public section

namespace Regula.Rules.RG1011

open Regula.Closed

/-- What runs in place of the definition of `d`, when its check reports it. -/
def replacement (d : Decl) : String :=
  match d.implementedBy, d.isExtern with
  | some impl, true => s!"@[implemented_by {impl}] and @[extern]"
  | some impl, false => s!"@[implemented_by {impl}]"
  | none, _ => "@[extern]"

/-- The constants of claimed modules that have `@[implemented_by]` or `@[extern]`. -/
def check {i : Input} (t : Tables i) : List Violation :=
  t.claimed.filterMap fun d =>
    if d.implementedBy.isSome || d.isExtern then
      some (violation d s!"has {replacement d}, so compiled code runs in place of its definition")
    else none

/-- RG1011, for the registry. Its body is exposed so that the registry reads its spelling (`Regula.Closed.spellings_nodup`). -/
@[expose] def rule : Rule := { spelling := "RG1011", check := check }

end Regula.Rules.RG1011
