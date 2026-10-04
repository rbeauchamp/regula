import Mathlib.Algebra.Group.Even

/-!
# Basic positive controls over Mathlib

Mathlib integration control. Small positive controls: `Audit.smoke` proves only
`1 + 1 = 2`; `Audit.EvenVal` is the canonical subtype of even naturals, stated with
Mathlib's `Even`; and `Audit.four` inhabits it with underlying value `4`. These
declarations assume only their imported Core and Mathlib definitions. Successful
elaboration makes no broader claim about the toolchain or other files.
-/

namespace Audit

/-- The natural-number expression `1 + 1` reduces to `2`. -/
theorem smoke : 1 + 1 = 2 := rfl

/-- Even natural numbers, reusing Lean's canonical `Subtype` and `Even`
predicate rather than wrapping either concept in a duplicate structure. -/
abbrev EvenVal := {n : Nat // Even n}

/-- Inhabitance witness for the constrained type (module 0 non-vacuity). -/
def four : EvenVal := ⟨4, ⟨2, rfl⟩⟩

/-- The witness really carries the value it claims. -/
example : four.val = 4 := rfl

end Audit
