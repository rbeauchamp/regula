import Regula.Shell
import Regula.Effects

/-! # The `lint` executable

The root of the `lint` executable, Lake's lint driver for a project that sets
`lintDriver := "regula/lint"`: `Regula.Shell.start` on the command-line arguments. -/

/-- The `lint` executable. -/
unsafe def main : List String → IO UInt32 :=
  Regula.Shell.start


-- The program loads the finished build, prints its report and sets its exit code: the build of
-- this module fails when the compiled code of a module outside the toolchain that it links starts a
-- process, writes or removes a file, or makes or moves an entry, or calls a declaration of the
-- toolchain that reaches one (`Regula.Effects.check`). The two of `Regula.Effects.lakeLoad` are
-- Lake's load of the workspace, whose own Git, Lean and `.lake/config` effects are Lake's.
run_cmd Regula.Effects.check
