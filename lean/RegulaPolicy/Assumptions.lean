module

public import RegulaPolicy.KernelAxioms
public import RegulaPolicy.External
meta import Regula.Decision

/-! # The assumptions a claim rests on

A claim is a theorem about a definition that Regula's code runs. When the definition acts on an
external system, the theorem is stated over every model of that system that satisfies the
assumptions it needs, so it uses each one (`RegulaPolicy.External`). This module reads them as
`#print axioms` reads axioms: the assumptions and the checked operations among the constants that
the claim uses, directly or through the constants it uses.

## What a claim uses

A step from a constant goes to every constant that its type and its value use
(`KernelAxioms.successors`), proofs included, with the constructors of an inductive type and the
inductive types of a recursor: the walk of the axiom table. So a theorem whose proof applies a
lemma that has an assumption as a hypothesis rests on that assumption, even when the theorem states
the hypothesis by its unfolded text instead of by the assumption's name. A hypothesis that is
written out and that no constant of the walk names is outside the report: the walk matches
constants, not definitional equality. A theorem whose proof proves an assumption for a particular
model also lists it.

`table` computes, for every claim at once, the declarations with a role (`leaf`) that each one
reaches, from one forward search from all the claims (`KernelAxioms.searchEdges`), the one that
`KernelAxioms.axiomTable` reads too, with one backward search from each such declaration
(`KernelAxioms.leafTable`). `table_some` states that each claim's entry holds exactly the
declarations with a role that it reaches (`RestsOn`).

## Boundaries

The constants are the ones Lean's kernel holds for the environment of the claims; that the
observing pass supplies those constants is trusted, as for the axioms of a declaration. A role is
what an attribute wrote (`Regula.Assumption`); that a predicate with the role `assumption` states
the property its docstring and sources describe is review. -/

@[expose] public section

namespace RegulaPolicy.Assumptions

open Lean KernelAxioms External

/-- The claim `claim` rests on the declaration `d`: `d` has a role that is an assumption or a
checked operation, and the walk of the constants that `claim` uses reaches `d`. -/
def RestsOn (find : Name → Option ConstantInfo) (role : Name → Option Role) (claim d : Name) :
    Prop :=
  Reach (successors find) claim d ∧
    ((∃ system sources, role d = some (.assumption system sources)) ∨
      ∃ system contract sources, role d = some (.checked system contract sources))

/-- Whether a role is one a claim rests on: an assumption or a checked operation. An observer is
IO code, not a property. -/
def restable : Role → Bool
  | .assumption .. | .checked .. => true
  | .observer _ => false

/-- The declarations a walk stops at: those with a role that `restable` accepts. -/
def leaf (role : Name → Option Role) (d : Name) : Bool :=
  match role d with
  | some r => restable r
  | none => false

/-- `leaf` accepts exactly the declarations with an assumption or a checked operation as role. -/
theorem leaf_iff (role : Name → Option Role) (d : Name) :
    leaf role d = true ↔
      (∃ system sources, role d = some (.assumption system sources)) ∨
        ∃ system contract sources, role d = some (.checked system contract sources) := by
  unfold leaf
  cases h : role d with
  | none => simp
  | some r => cases r <;> simp [restable]

/-- For every claim of the forward search `forward`, the assumptions and checked operations it
rests on, under its name: the `leafTable` of the search, with those declarations as its leaves.
`forward` is the walk of the constants that the claims use (`table_some`). `none` when a search back
runs out of `fuel`. -/
def table (role : Name → Option Role) (fuel : Nat)
    (forward : Std.HashSet Name × List (Name × Array Name)) :
    Option (Std.HashMap Name (Array Name)) :=
  leafTable (leaf role) fuel forward

/-- **`table` of the walk of the constants that `claims` use holds every claim, and gives each
claim exactly the declarations it rests on** (`RestsOn`). -/
theorem table_some {find : Name → Option ConstantInfo} {role : Name → Option Role} {fuel : Nat}
    {claims : Array Name} {forward : Std.HashSet Name × List (Name × Array Name)}
    {result : Std.HashMap Name (Array Name)}
    (hs : searchEdges (successors find) fuel claims.toList = some forward)
    (h : table role fuel forward = some result) :
    (∀ claim ∈ claims, ∃ rested, result[claim]? = some rested) ∧
      ∀ claim rested, result[claim]? = some rested →
        ∀ d, d ∈ rested ↔ RestsOn find role claim d :=
  have ⟨holds, exact⟩ := leafTable_some hs h
  ⟨holds, fun claim rested found d => (exact claim rested found d).trans
    ⟨fun ⟨reach, isLeaf⟩ => ⟨reach, (leaf_iff role d).mp isLeaf⟩,
      fun ⟨reach, rests⟩ => ⟨reach, (leaf_iff role d).mpr rests⟩⟩⟩

end RegulaPolicy.Assumptions
