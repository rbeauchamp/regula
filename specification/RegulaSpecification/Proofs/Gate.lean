/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import Regula.DiagnosticsGate

/-!
# The local gate, at `IO`

The gate program is the merge gate, and a defect in it that let a broken change pass would be serious. `runSteps_io` and
`runIn_zero` prove, of the definitions at `IO`, from any state of the world, that it gives 0 only when each step of
`localSteps` gave 0. `runLocal` is `runIn` between making and removing the checker's copy, in a `try ... finally`, which is
read from the code and has no theorem here. `BaseIO` and `IO` are state monads in Lean's own definition (`Init/System/ST.lean`), so
no assumption about the order of effects is needed for this. A defect that only stops the gate visibly, such as a failed
copy or removal, which `IO` turns into a nonzero exit, is accepted risk.
-/

namespace RegulaSpecification.GateProgram

open Regula.DiagnosticsGate

/-- A step of `IO`'s bind on success, by its definition. -/
theorem io_bind_ok {α β : Type} {x : IO α} {f : α → IO β} {w w₁ : Void IO.RealWorld} {a : α}
    (h : x w = .ok a w₁) : (x >>= f) w = f a w₁ := by
  show EST.bind x f w = _
  simp [EST.bind, h]

/-- A step of `IO`'s bind on failure, by its definition. -/
theorem io_bind_error {α β : Type} {x : IO α} {f : α → IO β} {w w₁ : Void IO.RealWorld} {e : IO.Error}
    (h : x w = .error e w₁) : (x >>= f) w = .error e w₁ := by
  show EST.bind x f w = _
  simp [EST.bind, h]

/-- `runSteps` at `IO`: a run that reports no step asked each step, and each gave 0. -/
theorem runSteps_io (run : Step → IO UInt32) (steps : List Step) (w w' : Void IO.RealWorld)
    (h : runSteps run steps w = .ok none w') :
    ∀ s ∈ steps, ∃ w₁ w₂, run s w₁ = .ok 0 w₂ := by
  induction steps generalizing w with
  | nil => simp
  | cons step rest ih =>
    intro s hs
    rw [runSteps] at h
    cases hrun : run step w with
    | error e w₁ =>
      rw [io_bind_error hrun] at h
      cases h
    | ok code w₁ =>
      rw [io_bind_ok hrun] at h
      split at h
      · rename_i hc
        have hzero : code = 0 := by simpa using hc
        subst hzero
        rcases List.mem_cons.mp hs with rfl | hs
        · exact ⟨w, w₁, hrun⟩
        · exact ih w₁ h s hs
      · cases h

/-- `runIn` gives 0 only when each step gave 0. -/
theorem runIn_zero (target root : String) (w w' : Void IO.RealWorld)
    (h : runIn target root w = .ok 0 w') :
    ∀ s ∈ localSteps target root, ∃ w₁ w₂, runStep s w₁ = .ok 0 w₂ := by
  unfold runIn at h
  cases hr : runSteps runStep (localSteps target root) w with
  | error e w₁ =>
    rw [io_bind_error hr] at h
    cases h
  | ok r w₁ =>
    rw [io_bind_ok hr] at h
    cases hs : sayResult (localSteps target root) r w₁ with
    | error e w₂ =>
      rw [io_bind_error hs] at h
      cases h
    | ok u w₂ =>
      rw [io_bind_ok hs] at h
      have hc : exitOf r = 0 := EST.Out.ok.inj h |>.1
      have hn := (exitOf_eq_zero_iff r).mp hc
      subst hn
      exact runSteps_io _ _ _ _ hr

/-- The gate's `localSteps` hold the steps it must run, in this order: the full gate, the build, the checker on its own
build, and the specification's build, replay and checker. -/
theorem localSteps_eq (checker root : String) :
    (localSteps checker root).map (·.arguments) =
      [["clean"], ["build", "lint"], ["exe", "lint", "standard-logical", "full", root], ["build", "--wfail"],
        ["build", "--wfail", "Regula", "lint"], ["lint"], ["build", "--wfail"],
        ["check", "--inadvisably-no-sandbox"], ["lint"]] := rfl

end RegulaSpecification.GateProgram
