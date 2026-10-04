/-!
# Basic positive controls

Small positive controls: `Audit.smoke` proves only `1 + 1 = 2`; `Audit.EvenVal`
is the canonical subtype of even naturals; and `Audit.four` inhabits it with
underlying value `4`. These declarations assume only Lean's core definitions.
Successful elaboration makes no broader claim about the toolchain or other files.
-/

namespace Audit

/-- The natural-number expression `1 + 1` reduces to `2`. -/
theorem smoke : 1 + 1 = 2 := rfl

/-- Even natural numbers, reusing Lean's canonical `Subtype` and core's divisibility
relation (`2 ∣ n` is `∃ c, n = 2 * c`) rather than wrapping either concept in a
duplicate structure. -/
abbrev EvenVal := {n : Nat // 2 ∣ n}

/-- Inhabitance witness for the constrained type (module 0 non-vacuity). -/
def four : EvenVal := ⟨4, ⟨2, rfl⟩⟩

/-- The witness really carries the value it claims. -/
example : four.val = 4 := rfl

end Audit
