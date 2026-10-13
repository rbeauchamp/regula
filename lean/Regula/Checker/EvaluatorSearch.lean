import Lean.Elab.Command
import Lean.Elab.Tactic.Basic
import Lean.Compiler.ImplementedByAttr

/-! # Lean's builtin elaborators that evaluate project code

The search that gives `RegulaPolicy.Community.evaluators`: the builtin elaborators of the running
Lean whose compiled code can evaluate code the project supplies. RG2006 counts an option as written
by the toolchain only when none of them is above it (`RegulaPolicy.Community.toolchainWritten`),
since such an elaborator may have elaborated syntax that the project's code built. The registry
checks run the search and refuse unless its result is that list, so the list follows the pinned
toolchain.

The search reads the static call edges of Lean's compiled code as the environment of the module
`Lean` records them: the constants each definition's or opaque constant's value uses, and its
`implemented_by` target. An edge through a closure that an attribute table or a reference holds is
not among them, so the search does not follow Lean's dispatch from one elaborator to another. Its
targets are Lean's evaluators of a term or expression the project supplies:
`Lean.Elab.Term.evalTerm`, `Lean.Meta.evalExprCore` (under `evalExpr` and `evalExpr'`) and the
`#eval` core `Lean.Elab.Command.elabEvalCoreUnsafe`. Lean's constant evaluator
`Lean.Environment.evalConst` is not one: it evaluates a named declaration, and Lean's attribute and
configuration code reaches it from `elabSetOption` and `elabDeclaration` too. -/

namespace Regula.Checker.EvaluatorSearch

open Lean

/-- Lean's evaluators of a term or expression the project supplies. -/
def targets : List Name :=
  [`Lean.Elab.Term.evalTerm, `Lean.Meta.evalExprCore, `Lean.Elab.Command.elabEvalCoreUnsafe]

/-- The constants that the value of `c` uses, with its `implemented_by` target. -/
def edges (env : Environment) (c : ConstantInfo) : Array Name :=
  let used := match c with
    | .defnInfo d => d.value.getUsedConstants
    | .opaqueInfo o => o.value.getUsedConstants
    | _ => #[]
  match Compiler.getImplementedBy? env c.name with
  | some impl => used.push impl
  | none => used

/-- The constants of `env` from which an edge path (`edges`) reaches one of `targets`. -/
def reaching (env : Environment) : NameSet := Id.run do
  let mut callers : Std.HashMap Name (Array Name) := {}
  for (name, c) in env.constants.toList do
    for used in edges env c do
      callers := callers.insert used ((callers.getD used #[]).push name)
  let mut reached : NameSet := {}
  let mut queue := (targets.filter env.contains).toArray
  for t in queue do reached := reached.insert t
  let mut i := 0
  while h : i < queue.size do
    let n := queue[i]
    i := i + 1
    for caller in callers.getD n #[] do
      unless reached.contains caller do
        reached := reached.insert caller
        queue := queue.push caller
  return reached

/-- The declarations of the builtin entries of the keyed elaborator table `attr`. -/
unsafe def builtinEntries {γ : Type} (attr : KeyedDeclsAttribute γ) : IO (Array Name) := do
  let table ← attr.tableRef.get
  return table.fold (init := #[]) fun acc _ entries =>
    entries.foldl (fun acc e => if e.isBuiltin then acc.push e.declName else acc) acc

/-- The builtin command, term and tactic elaborators and macros of the running Lean whose code
reaches one of `targets` in the environment of the module `Lean` of the toolchain whose library is
on the search path, sorted by name. -/
private unsafe def searchImpl : IO (List Name) := do
  enableInitializersExecution
  let env ← importModules (loadExts := true) #[{ module := `Lean }] {}
  let reached := reaching env
  let builtins := (← builtinEntries Elab.Command.commandElabAttribute) ++
    (← builtinEntries Elab.Term.termElabAttribute) ++
    (← builtinEntries Elab.Tactic.tacticElabAttribute) ++ (← builtinEntries Elab.macroAttribute)
  return (builtins.filter reached.contains).toList.eraseDups.mergeSort (·.toString ≤ ·.toString)

/-- `searchImpl`: it imports a second environment and reads Lean's elaborator tables, which a
safe definition cannot do. -/
@[implemented_by searchImpl]
opaque search : IO (List Name)

end Regula.Checker.EvaluatorSearch
