/-
Intended failure: an assumption on a structure whose type is `Type 1`, not `Prop`. A theorem cannot
take a value of the structure as a hypothesis that states a property, so `@[regula_assumption]`
refuses it.
-/
import Regula.Assumption

namespace Fixtures.NonPredicateAssumption

@[regula_assumption filesystem (trusted "control: no property")]
structure Model where
  World : Type

end Fixtures.NonPredicateAssumption
