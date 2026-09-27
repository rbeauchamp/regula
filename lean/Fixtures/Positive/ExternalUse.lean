/-
External-consumer control (AC-08): a small fixture that only imports the
published `AuditApp` library and reasons about its declarations. The public
checker classifies the declarations introduced here and reports the exact
foundation labels — without adopting any general software process.

`#print axioms` confirms what the checker reports: `ext_admitted_fresh` depends on
no axiom (Kernel-only), and `ext_requested_default` depends on `propext`,
`Classical.choice` and `Quot.sound` (Standard-Logical), because Lean's `String`
parser behind `AuditApp.requestedCapacity` uses them.
-/
import AuditApp

theorem ext_admitted_fresh (capacity : Nat) (l : AuditApp.Limiter)
    (h : AuditApp.admit capacity = some l) : 0 < l.capacity ∧ l.inUse = 0 :=
  AuditApp.admit_sound h

theorem ext_requested_default (arg : String) (rest : List String) :
    AuditApp.requestedCapacity (arg :: rest) = arg.toNat?.getD 2 :=
  AuditApp.requestedCapacity_exact (arg :: rest)
