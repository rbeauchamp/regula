/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

import Lean.ImportingFlag
import Regula.Shell
import Regula.Workspace

/-! # The `lint` executable

The root of the `lint` executable, Lake's lint driver for a project that sets
`lintDriver := "regula/lint"`: the interpretation of `Regula.Shell.run` on the command-line arguments, through
the one table of effects (`Regula.Effect.table`) with the calls of Lake (`Regula.Load.lakeCalls`). It holds no
logic. It is `unsafe` because Lean's `enableInitializersExecution` is, which lets Lean's own parsers load for each
file that the reader parses. -/

/-- The `lint` executable. -/
public unsafe def main (args : List String) : IO UInt32 :=
  (Regula.Effect.Prog.interpret
    (Regula.Effect.table Lean.enableInitializersExecution Regula.Load.lakeCalls)
    (Regula.Shell.run args)).toIO
