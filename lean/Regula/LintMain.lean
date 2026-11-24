module

import Lean.ImportingFlag
import Regula.Shell
import Regula.Workspace

public unsafe def main (args : List String) : IO UInt32 :=
  (Regula.Effect.Prog.interpret
    (Regula.Effect.table Lean.enableInitializersExecution Regula.Load.lakeCalls)
    (Regula.Shell.run args)).toIO
