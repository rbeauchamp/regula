/-
Mutation of `Fixtures.Positive.DecisionRegistration`: the file registers `Nat.ble`, a function of
an imported module, as a decision. Lean accepts the attribute, because a module of the function's
own inventory may write its registration. This file's inventory does not declare `Nat.ble`, so
the audit records no declaration to decide the requirement for: it must stop without a verdict
and name the registration.
-/
import Regula.Decision

attribute [regula_decision] Nat.ble
