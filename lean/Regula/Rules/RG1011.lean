module

public import Regula.Rule

/-!
# RG1011: replaced compiled code

A constant of a claimed module has `@[implemented_by]` or `@[extern]`, or is a definition for which
`@[init]` or `@[builtin_init]` names an initialization function, so a compiled program runs other code
in its place than the definition that its proofs are about. The loader reads the three with
`Lean.Compiler.getImplementedBy?`, `Lean.isExtern` and `Lean.getInitFnNameFor?`, the queries by which
Lean's compiler decides what it compiles for a constant (`shouldGenerateCode`,
`Lean/Compiler/LCNF/Main.lean:34` and `:40`, and `toDecl`, `Lean/Compiler/LCNF/ToDecl.lean:72`, at
v4.35.0). `specification/RegulaSpecification/Rules/RG1011.lean` states the rule and proves this check
against it.
-/

public section

namespace Regula.Rules.RG1011

open Regula.Closed

/-- Whether `d` is a definition for which `@[init]` or `@[builtin_init]` names an initialization
function. An opaque constant with one, which `initialize` declares, is not read: Lean's logic states
nothing of its value. -/
def initialized (d : Decl) : Bool := d.kind == .definition && d.initFn.isSome

/-- What runs in place of the definition of `d`, when its check reports it. -/
def replacement (d : Decl) : String :=
  " and ".intercalate
    ((d.implementedBy.map fun impl => s!"@[implemented_by {impl}]").toList ++
      (if d.isExtern then ["@[extern]"] else []) ++
      (if d.kind == .definition then
        (d.initFn.map fun fn => s!"the initialization function {fn} of @[init] or @[builtin_init]").toList
      else []))

/-- The constants of claimed modules that have `@[implemented_by]` or `@[extern]`, and the definitions
of claimed modules that have an initialization function. -/
def check {i : Input} (t : Tables i) : List Violation :=
  t.claimed.filterMap fun d =>
    if d.implementedBy.isSome || d.isExtern || initialized d then
      some (violation d s!"has {replacement d}, so compiled code runs in place of its definition")
    else none

/-- RG1011, for the registry. Its body is exposed so that the registry reads its spelling (`Regula.Closed.spellings_nodup`). -/
@[expose] def rule : Rule := { spelling := "RG1011", check := check }

end Regula.Rules.RG1011
