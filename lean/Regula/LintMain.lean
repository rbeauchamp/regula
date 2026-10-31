/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

import Lean.ImportingFlag
import Regula.Reader
import Regula.Shell
import Regula.Workspace

/-! # The `lint` executable

The root of the `lint` executable, Lake's lint driver for a project that sets
`lintDriver := "regula/lint"`: `Regula.Shell.run` on the command-line arguments, with Lake's load of
the workspace (`Regula.Load.loadInput`) and the language check's reader (`Regula.Reader`). It is `unsafe`
because Lean's `enableInitializersExecution` is, which lets Lean's own parsers load for each file that the
reader parses. -/

/-- The `lint` executable. -/
public unsafe def main : List String → IO UInt32 :=
  Regula.Shell.run Regula.Load.loadInput (fun dir => Regula.Load.loadInputAt dir)
    (Regula.Reader.read Lean.enableInitializersExecution) Regula.Reader.buildAndReplay
