import AuditApp.Limiter

/-!
# Limiter demonstration script

The fixed update script used by the `auditApp` executable, together with
contracts for both interpretations. `demo_final` describes the retained total
`run` API, which continues after a refused grant. `demo_checked_error` describes
the strict `runChecked` interpreter called by the shell: at the default capacity 2, it
stops at the third grant and retains the first two grants' state. Admission facts describe the
scripted initial capacity. Nothing here claims a property of the IO boundary.
`demo_checked_error` is a material claim registered with `@[regula_material]`, so RG5002/RG5003
require its Intent section.
-/

namespace AuditApp

/-- The fixed demonstration script: two grants, a third grant that a
capacity-2 limiter must refuse, one release, one final grant. -/
def demoScript : List Op := [.grant, .grant, .grant, .release, .grant]

/-- The demonstration's initial state: capacity 2 with no slots in use,
satisfying the invariant proof field directly. -/
def demoInitial : Limiter := ⟨2, 0, Nat.zero_le 2⟩

/-- The scripted capacity passes the admission boundary. -/
theorem demo_admitted : (admit 2).isSome = true := by decide

/-- Capacity zero does not pass the admission boundary. -/
theorem demo_rejected : admit 0 = none := admit_none rfl

/-- The demonstration run stays within its capacity. The proof is the
composition theorem `run_bounded` instantiated to the scripted run; the
statement reads the capacity of the final state, which the kernel identifies
with `demoInitial.capacity` by unfolding the closed run. -/
theorem demo_bounded :
    (run demoScript demoInitial).inUse ≤ (run demoScript demoInitial).capacity :=
  run_bounded demoInitial demoScript

/-- The exact end state of the scripted run on the actual executable
definitions: two slots of the capacity-2 limiter are in use, because the
third grant is refused. Kernel-checked by decision. -/
theorem demo_final : (run demoScript demoInitial).inUse = 2 := by decide

/-- The strict demonstration stops at the third grant. This instance of the
universal error contract identifies the retained successful prefix; unlike
`run`, it never processes the subsequent release and grant.

# Intent
At the default capacity 2, the demonstration script the executable runs must stop at
its third grant, keeping the two slots already granted, rather than continuing past the
refusal. Other command-line capacities are outside this claim. -/
@[regula_material]
theorem demo_checked_error :
    runChecked demoScript demoInitial =
      (.error (), run [.grant, .grant] demoInitial) := by
  apply (runChecked_error _ _ _).mpr
  exact ⟨[.grant, .grant], [.release, .grant], rfl, by simp only [Fits]; decide, rfl, by decide⟩

end AuditApp
