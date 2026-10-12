module

public import Regula.Assumption
meta import Regula.Assumption

/-! # Module visibility at the attribute boundary

Public definitions have hidden bodies in the exporting view. Attribute validation must read the
body owned by this module, rather than classify that public declaration as an axiom. This fixture
checks the compiler/attribute boundary; it starts no process and establishes no native IO fact. -/

namespace Fixtures.ModuleObserver

/-- A module-system public observer accepted from its locally owned definition. -/
@[regula_observer process]
public def observe : IO Unit := pure ()

/-- A module-system public predicate accepted as a sourced assumption. -/
@[regula_assumption process (trusted "control of module visibility, not a runtime fact")]
public def Observed : Prop := True

end Fixtures.ModuleObserver
