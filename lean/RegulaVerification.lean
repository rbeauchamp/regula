import Lean.Util.Path

/-! # Launcher of the cold verification driver

`scripts/verify.sh` runs this file with `lean --run` before the package is built. The driver is the
module `RegulaVerification.Driver` of the claimed library `RegulaVerification`, and it declares no
`main`. `lake check` imports every module of the default targets into one environment
(`Lake/CLI/Main.lean:1218-1226` at v4.35.0), and Lean refuses two imported modules that declare one
name with different values (`Lean/Environment.lean:2336-2344`), so a library module with a
top-level `main` beside the `main` of `auditApp` would stop `lake check` of this package. This file
is in no Lake target, so no build compiles it and no load of the build reads it.

It hands the driver's source, which it embeds when Lean elaborates it, to the `lean` that runs it
(`Lean.getBuildDir`, never a program that a search of `PATH` finds), with `main` bound to
`RegulaVerification.entry`, and exits with the driver's exit status. Its effects are that one
child process and the write of the child's standard input.

Assumes: `lean --stdin --run FILE ARGS` elaborates its standard input as the file `FILE`, so the
driver's `include_str` reads relative to `FILE`, and runs its `main` with `ARGS`
(`Lean/Shell.lean:498-561` and `Lean/Elab/BuiltinTerm.lean:437-445` at v4.35.0). The child stays
in this process's process group, so the deadline of `scripts/verify.sh` reaches it. -/

/-- The source of the driver, read when Lean elaborates this file. -/
def driverSource : String := include_str "RegulaVerification/Driver.lean"

/-- Run the driver with `args`, from the root of the repository, and give its exit status. -/
def main (args : List String) : IO UInt32 := do
  let child ← IO.Process.spawn {
    cmd := ((← Lean.getBuildDir) / "bin" / "lean").toString
    args := #["--stdin", "--run", "lean/RegulaVerification/Driver.lean"] ++ args.toArray
    stdin := .piped }
  let (input, child) ← child.takeStdin
  input.putStr (driverSource ++ "\n/-- The driver's entry point. -/\n" ++
    "def main := RegulaVerification.entry\n")
  input.flush
  child.wait
