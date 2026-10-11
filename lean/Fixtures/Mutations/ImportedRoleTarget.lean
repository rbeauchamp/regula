/-
Intended failure: a role given to a constant that an imported module declares. `Nat.le` is a
predicate, so it could be an assumption, but a role is given only in the module that declares the
constant, so that no import carries a second role for it.
-/
import Regula.Assumption

namespace Fixtures.ImportedRoleTarget

attribute [regula_assumption filesystem (trusted "control: an imported predicate")] Nat.le

end Fixtures.ImportedRoleTarget
