module

public import Lean.Declaration
import all Lean.Declaration
import all Lean.Environment

/-! # Theorems that two modules share

Lean realizes some constants in the module that first needs them (equation, unfolding and
match-equation lemmas, functional induction and case principles, congruence and injectivity
lemmas), so two modules that do not import each other can each contain the same one. Lean's
import keeps one copy of such a name when the two copies pass its private `subsumesInfo` test in
one of the two directions. `sameTheorem` is that test restricted to two theorems, and
`sameTheorem_iff_subsumesInfo` proves the correspondence against Lean's own definition, which
`import all Lean.Environment` makes available. Kernel admission (`Admission.checkDuplicates`)
admits a shared name only under `sameTheorem`. -/

namespace Regula.Checker.Admission

open Lean

/-- Whether two constants of one name are theorems that Lean's import accepts together: the same
name, universe parameters and mutual block, and types that `Expr.eqv` (alpha-equivalence,
binder annotations ignored) equates in either direction. Their proofs may differ. -/
@[expose] public def sameTheorem : ConstantInfo → ConstantInfo → Bool
  | .thmInfo a, .thmInfo b =>
      a.name == b.name && (a.type == b.type || b.type == a.type) &&
        a.levelParams == b.levelParams && a.all == b.all
  | _, _ => false

/-- On two theorems, `sameTheorem` is Lean's private `subsumesInfo` in either direction, for any
constant map; on any other pair it is false. Read from the pinned `Lean.finalizeImport` source,
not modeled here: it accepts a second constant of one name beside an earlier one exactly when
`subsumesInfo` holds in one of the two directions, so `sameTheorem` is its condition for two
theorems, and every other pair it accepts involves an axiom. Private because its statement names
Lean's private definition. -/
private theorem sameTheorem_iff_subsumesInfo (constants : Std.HashMap Name ConstantInfo)
    (a b : ConstantInfo) :
    sameTheorem a b = true ↔ a.isTheorem = true ∧ b.isTheorem = true ∧
      (subsumesInfo constants a b || subsumesInfo constants b a) = true := by
  cases a <;> cases b <;>
    simp [sameTheorem, subsumesInfo, ConstantInfo.isTheorem, ConstantInfo.name,
      ConstantInfo.type, ConstantInfo.levelParams, ConstantInfo.toConstantVal]
  grind

end Regula.Checker.Admission
