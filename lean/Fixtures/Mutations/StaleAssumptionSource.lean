/-
Intended failure: an assumption whose source is pinned to a Lean release other than the one that
elaborates the module. `@[regula_assumption]` refuses it where it is written, so the module does
not elaborate until the source is read again at the current release.
-/
import Regula.Assumption

namespace Fixtures.StaleAssumptionSource

@[regula_assumption filesystem (lean "v4.33.0" "Init/System/IO.lean#L1330-L1342")]
def Removes : Prop := True

end Fixtures.StaleAssumptionSource
