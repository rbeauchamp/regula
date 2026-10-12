module

public import Regula.Assumption
public import Fixtures.ModuleObserver
meta import Regula.Assumption

/-! # A role cannot be assigned by another module

The full-view correction applies only after the ownership guard. This fixture attempts to assign
an environment role to another module's public observer and must fail at that guard. -/

attribute [regula_observer environment] Fixtures.ModuleObserver.observe
