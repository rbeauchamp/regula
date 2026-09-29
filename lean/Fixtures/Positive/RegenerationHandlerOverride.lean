/-
Positive control (issue #125): genuine recursive definitions followed by macros
that make fail every tactic and term the well-founded regeneration would
otherwise dispatch: the `sorry`, `exact`, `all_goals` and `clean_wf` tactics
and the `sorry` term. The regeneration uses only the syntax handlers built into
the Lean executable, so the module's own handlers never run there and the
helpers are still admitted.
-/

def fixtures_override_walk (bytes : ByteArray) (start : Nat) : Nat :=
  if start < bytes.size then fixtures_override_walk bytes (start + 1) else start
termination_by bytes.size - start

def fixtures_override_countdown (n : Nat) : Nat :=
  if h : n = 0 then 0 else fixtures_override_countdown (n - 1) + 1
termination_by n
decreasing_by omega

macro_rules | `(tactic| sorry) => `(tactic| fail "overridden sorry")
macro_rules | `(tactic| exact $_) => `(tactic| fail "overridden exact")
macro_rules | `(tactic| all_goals $_) => `(tactic| fail "overridden all_goals")
macro_rules | `(tactic| clean_wf) => `(tactic| fail "overridden clean_wf")
macro_rules | `(sorry) => `((0 : Nat))
