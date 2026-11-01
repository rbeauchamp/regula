/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import Lean.AuxRecursor
import Lean.Elab.Command
import Lean.ProjFns
import RegulaSpecification.Proofs.Domain

/-!
# No premise of an owed pass applies a decision of the checker

The audit of `a399fbe9` found `Answers.start` requiring two of the checker's own tests to return the wanted Booleans, so that the theorem that a
pass is owed had a false premise on a run that the checker wrongly refused. This module keeps that class from coming back. The build of the specification walks
what each statement of `premises` mentions, through the definitions of the specification, and fails on a constant of the checker's own program that is not a
type, a constructor, a field or one of `data`, which hold data and decide nothing. Each other constant of the program is a function that a premise
would apply to an answer. So a new premise that names `Regula.Load.below`, or that reaches it through a definition, stops the build.

This is a check and no theorem: it reads what Lean's `Expr.getUsedConstants` lists. It says nothing of what a premise means, and a statement left out of
`premises` is not read: the list is the owed-pass theorems' own premises, by name.
-/

namespace RegulaSpecification.Premises

open Lean

/-- The premises of `domain_owed`, `plain_owed`, `full_owed`, `run_plain_owed` and `run_full_owed`, other than the record they are theorems of, which
states the program: `RunMeets` names the decision that the program must have made, and is no premise about what a system answered. -/
def premises : List Name :=
  [``Effects.DomainRun, ``Effects.Answers, ``Domain.Project.InDomain, ``Effects.PlainOwed, ``Effects.FullOwed]

/-- The constants of the program that hold data and decide nothing: the tables of the closed language, the pinned text, what `Resp` gives each operation, and what
Lean generates for a type of the program. -/
def data : List Name :=
  [``Regula.Language.derivingClasses, ``Regula.Language.configItems, ``Regula.Language.simpleAttributes, ``Regula.Language.kinds, ``Regula.Language.atoms,
    ``Regula.Language.leafKinds, ``Regula.Language.options, ``Regula.Language.configKeys, ``Regula.Language.leanToolchain, ``Regula.Effect.Resp,
    ``Regula.Effect.Op.ctorIdx]

/-- What a constant mentions: its type, its value, and the constructors of an inductive type. -/
def mentionsOf (info : ConstantInfo) : Array Name :=
  match info with
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray
  | .ctorInfo v => v.type.getUsedConstants
  | .axiomInfo v => v.type.getUsedConstants
  | .quotInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants

/-- Whether a constant is the checker's own. -/
def ownProgram (n : Name) : Bool :=
  n.getRoot == `Regula

/-- Whether a constant of the program is a type, a constructor, a recursor or a structure's field: it decides nothing itself, and the walk goes on through what it mentions,
so a proof field that holds a function of the program is still found. -/
def structural (env : Environment) (n : Name) : Bool :=
  env.isProjectionFn n || isAuxRecursor env n ||
    match env.find? n with
    | some (.inductInfo _) | some (.ctorInfo _) | some (.recInfo _) => true
    | _ => false

/-- The constants of the program that a walk from `todo` reaches and that are neither structural nor data, stopping at what is neither the specification's nor the program's. `fuel`
bounds the constants visited, and running out is a failure. -/
def walk (env : Environment) : Nat → List Name → NameSet → List Name → Except String (List Name)
  | _, [], _, found => .ok found
  | 0, _ :: _, _, _ => .error "the walk over the premises reached too many constants"
  | fuel + 1, n :: rest, seen, found =>
    if seen.contains n || data.contains n then
      walk env fuel rest seen found
    else if ownProgram n && !structural env n then
      walk env fuel rest (seen.insert n) (n :: found)
    else if ownProgram n || n.getRoot == `RegulaSpecification then
      let next := ((env.find? n).map mentionsOf).getD #[]
      walk env fuel (next.toList ++ rest) (seen.insert n) found
    else
      walk env fuel rest (seen.insert n) found

-- The check.
run_cmd do
  match walk (← getEnv) 1000000 premises {} [] with
  | .error why => throwError why
  | .ok [] => pure ()
  | .ok found => throwError "a premise of an owed pass reaches these functions of the checker's own program: {found}"

end RegulaSpecification.Premises
