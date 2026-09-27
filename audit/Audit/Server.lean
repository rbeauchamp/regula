/-!
# Proof-bearing service state

Proof-bearing service state for modules 1 and 3. Admission checks raw natural
counts; initialization and every update establish `served ≤ cap`. The public
constructor also requires that proof. The finite-prefix theorem relates the
result to the starting capacity, not to an external service or a latest-state
discipline. These definitions use only Lean's prelude and ordinary total recursion.
-/

namespace Glossary

/-- An immutable admitted value; the bound is required even by direct construction. -/
structure Server where
  /-- The number of requests served so far. -/
  served : Nat
  /-- The maximum number of requests the server may serve. -/
  cap : Nat
  /-- Proof that the served count is within the capacity. -/
  bounded : served ≤ cap

/-- Dynamic admission of raw counts using computable natural-number comparison. -/
def Server.validate (served cap : Nat) : Option Server :=
  if h : served ≤ cap then some ⟨served, cap, h⟩ else none

/-- Every successful admission retains exactly the input counts. The result's
`bounded` field supplies the statically usable invariant. -/
theorem Server.validate_some {served cap : Nat} {s : Server}
    (h : validate served cap = some s) : s.served = served ∧ s.cap = cap := by
  unfold validate at h
  split at h
  next =>
    injection h with hs
    subst hs
    exact ⟨rfl, rfl⟩
  next => nomatch h

/-- Admission rejects exactly the count pairs violating the bound. -/
theorem Server.validate_none (served cap : Nat) :
    validate served cap = none ↔ ¬ served ≤ cap := by
  unfold validate
  split <;> simp_all

/-- No valid value is lost when its fields are validated again. -/
theorem Server.validate_roundtrip (s : Server) :
    validate s.served s.cap = some s := by
  unfold validate
  rw [dite_eq_left s.bounded]

/-- Initialization is possible for every capacity, including zero. -/
def Server.init (cap : Nat) : Server := ⟨0, cap, Nat.zero_le _⟩

/-- Serve one request when capacity remains; otherwise retain the same value. -/
def Server.step (s : Server) : Server :=
  if h : s.served < s.cap then
    { s with served := s.served + 1, bounded := h }
  else s

/-- Exact update behavior, including the full-capacity branch. -/
theorem Server.step_served (s : Server) :
    s.step.served = if s.served < s.cap then s.served + 1 else s.served := by
  unfold step
  split <;> rfl

/-- Every step retains capacity. -/
theorem Server.step_cap (s : Server) : s.step.cap = s.cap := by
  unfold step
  split <;> rfl

/-- An arbitrary finite prefix of the actual `step` definition: the prelude's
`Nat.repeat`, reused rather than redeclared. -/
def Server.run (n : Nat) (s : Server) : Server := Nat.repeat step n s

/-- Every finite prefix retains the initial capacity. -/
theorem Server.run_cap (n : Nat) (s : Server) : (run n s).cap = s.cap := by
  induction n with
  | zero => rfl
  | succ k ih => exact (step_cap (run k s)).trans ih

/-- Safety relative to the starting capacity, for all prefix lengths and all
admitted states. This proves neither liveness nor latest-state use. -/
theorem Server.run_bounded (n : Nat) (s : Server) : (run n s).served ≤ s.cap := by
  rw [← run_cap n s]
  exact (run n s).bounded

end Glossary
