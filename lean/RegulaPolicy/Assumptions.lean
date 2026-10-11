module

public import RegulaPolicy.KernelAxioms
public import RegulaPolicy.External
meta import Regula.Decision

/-! # The assumptions a claim rests on

A claim is a theorem about a definition that Regula's code runs. When the definition acts on an
external system, the theorem is stated over every model of that system that satisfies the
assumptions it needs, so its statement names each one (`RegulaPolicy.External`). This module reads
them from the statement, as `#print axioms` reads axioms from a proof: the assumptions and the
checked operations that the claim's statement reaches.

## What a statement reaches

A step from a constant goes to the constants that the meaning of its statement uses
(`statementSuccessors`): the type of a theorem, and the type and the value of each other constant,
with the constructors of an inductive type and the inductive types of a recursor
(`KernelAxioms.successorsOf`). A proof is not part of what a statement means, so a step does not
enter the value of a theorem: the statement of a theorem whose proof uses a lemma with a
hypothesis has that hypothesis itself, or the proof would not be accepted. A step enters the value
of a definition, so a property that a definition bundles is reached through it, and a checked
operation that the claimed definition runs is reached through the claimed definition's value.

`table` computes, for every claim at once, the declarations with a role (`leaf`) that each one
reaches, with one forward search from all the claims and one backward search from each such
declaration (`KernelAxioms.leafTable`). `table_some` states that each claim's entry holds exactly
the declarations with a role that it reaches (`RestsOn`).

## Boundaries

The constants are the ones Lean's kernel holds for the environment of the claims; that the
observing pass supplies those constants is trusted, as for the axioms of a declaration. A role is
what an attribute wrote (`Regula.Assumption`); that a predicate with the role `assumption` states
the property its docstring and sources describe is review. -/

@[expose] public section

namespace RegulaPolicy.Assumptions

open Lean KernelAxioms External

/-- The constants that the meaning of a constant's statement uses: the type of a theorem, and for
each other constant the constants of `KernelAxioms.successorsOf`, which are those of its type and
value, the constructors of an inductive type and the inductive types of a recursor. -/
def statementSuccessorsOf : ConstantInfo → Array Name
  | .thmInfo value => Std.TreeSet.toArray value.type.getUsedConstantsAsSet
  | info => successorsOf info

/-- The constants after `n` in a walk of statements: those `statementSuccessorsOf` gives for the
constant `find` holds under `n`, or none when it holds none. -/
def statementSuccessors (find : Name → Option ConstantInfo) (n : Name) : Array Name :=
  match find n with
  | some info => statementSuccessorsOf info
  | none => #[]

/-- The claim `claim` rests on the declaration `d`: `d` has a role that is an assumption or a
checked operation, and the walk of statements reaches `d` from `claim`. -/
def RestsOn (find : Name → Option ConstantInfo) (role : Name → Option Role) (claim d : Name) :
    Prop :=
  Reach (statementSuccessors find) claim d ∧
    ((∃ system sources, role d = some (.assumption system sources)) ∨
      ∃ system contract sources, role d = some (.checked system contract sources))

/-- Whether a role is one a claim rests on: an assumption or a checked operation. An observer is
IO code, which no statement names as a property. -/
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

/-- For every claim of `claims`, the assumptions and checked operations it rests on, under its name:
the `leafTable` of the walk of statements with those declarations as its leaves. `none` when a
search runs out of `fuel`. -/
def table (find : Name → Option ConstantInfo) (role : Name → Option Role) (fuel : Nat)
    (claims : Array Name) : Option (Std.HashMap Name (Array Name)) :=
  leafTable (statementSuccessors find) (leaf role) fuel claims

/-- **`table` holds every claim, and gives each claim exactly the declarations it rests on**
(`RestsOn`). -/
theorem table_some {find : Name → Option ConstantInfo} {role : Name → Option Role} {fuel : Nat}
    {claims : Array Name} {result : Std.HashMap Name (Array Name)}
    (h : table find role fuel claims = some result) :
    (∀ claim ∈ claims, ∃ rested, result[claim]? = some rested) ∧
      ∀ claim rested, result[claim]? = some rested →
        ∀ d, d ∈ rested ↔ RestsOn find role claim d :=
  have ⟨holds, exact⟩ := leafTable_some h
  ⟨holds, fun claim rested found d => (exact claim rested found d).trans
    ⟨fun ⟨reach, isLeaf⟩ => ⟨reach, (leaf_iff role d).mp isLeaf⟩,
      fun ⟨reach, rests⟩ => ⟨reach, (leaf_iff role d).mpr rests⟩⟩⟩

end RegulaPolicy.Assumptions
