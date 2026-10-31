import Regula.Shell
import Regula.Workspace
import Regula.Effects

/-! # The `lint` executable

The root of the `lint` executable, Lake's lint driver for a project that sets
`lintDriver := "regula/lint"`: `Regula.Shell.start` on the command-line arguments. It gives the shell
Lake's load of the workspace (`Regula.Load.loadBundle`) and `Environment.freeRegions`, the one
`unsafe` call of the checker, so that the claimed loader and shell hold neither. The bundle frees an
environment after it has copied the input out of its data, and no reference to that data remains
(`Regula.Load.copyInput`). -/

/-- The `lint` executable. -/
unsafe def main : List String → IO UInt32 :=
  Regula.Shell.start (Regula.Load.loadBundle Lean.Environment.freeRegions)


-- The program loads the finished build, prints its report and sets its exit code: the build of
-- this module fails when the compiled code of a module outside the toolchain that it links starts a
-- process, writes or removes a file, or makes or moves an entry, or calls a declaration of the
-- toolchain that reaches one (`Regula.Effects.check`). The two of `Regula.Effects.lakeLoad` are
-- Lake's load of the workspace, whose own Git, Lean and `.lake/config` effects are Lake's.
run_cmd Regula.Effects.check
