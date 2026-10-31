/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

import Regula.Shell
import Regula.Workspace

/-! # The `lint` executable

The root of the `lint` executable, Lake's lint driver for a project that sets
`lintDriver := "regula/lint"`: `Regula.Shell.run` on the command-line arguments, with Lake's load of
the workspace (`Regula.Load.loadInput`). -/

/-- The `lint` executable. -/
public def main : List String → IO UInt32 :=
  Regula.Shell.run Regula.Load.loadInput
