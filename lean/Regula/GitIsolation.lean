import RegulaCore.GitIsolation

/-! # Starting a program under Git isolation

Lake v4.34.1 starts each of its Git commands with no environment of its own
(`Regula.Filesystem.Construction.processEnvironment`), when it materializes a dependency, when it
builds a module of a dependency package and looks up a prebuilt archive, and in its command line
tools. So a Git command that Lake runs for Regula, in Regula's own process or in a Lake child, has
the environment of the program that started it. `enter` gives every compiled Regula program the
environment `processEnvironment` describes before the program runs: when its environment lacks
an entry, it starts the same executable again with the same arguments, the same standard input,
output and error and the same working directory, under that environment, and returns the child's
exit status. Everything the program then does in its own process inherits that environment, and
so does every process it starts, unless that start changes a variable that the isolation names.

`Regula.TaskManager.guard` runs `enter`, and `Regula.TaskManagerCheck.checkProgram` requires the
guard in every compiled program that can start a process. `enter` starts a program again only when
the running executable is the file that Lake builds for that program (`runsAs`). When isolation is
missing in any other process, such as one that the Lean frontend runs (`lean --run`), a plugin of
`lean` or a renamed copy of the executable, `enter` refuses before `run` and names the variables to
unset or set. `requireIsolated` is the refusal of Lake's in-process loader
(`Regula.Checker.Workspace`) in a process whose environment lacks an entry, which a caller that no
guard runs can reach.

## What stays trusted

The kernel proves the decisions (`Regula.GitIsolation.unisolated_eq_empty_iff`,
`Regula.GitIsolation.processEnvironment_isolated`). That the child receives the environment Lean's
spawn describes, that `IO.appPath` names the running executable, process creation itself, and
signal delivery are the runtime's and the operating system's. A child that a signal ends returns
`128 + n` from Lean's wait (`runtime/process.cpp:354-367`), which the parent returns as its own
exit status; the parent does not end by that signal. A signal sent to the parent's process ID
alone is not passed on to the child; one sent to the process group reaches both, as the child stays
in the parent's group. Git environment variables outside Git's repository-local list, such as
`GIT_TEMPLATE_DIR`, `GIT_EXEC_PATH` or `GIT_SSH_COMMAND`, stay inherited, as they do for the Git
commands Regula starts itself. -/

namespace Regula.GitIsolation

/-- The leading argument with which `enter` starts its program again. `strip` removes it, so the
program never reads it. It marks only that a restart happened: whether the environment is isolated
is decided from the environment, never from this argument. -/
def restarted : String := "--regula-git-isolation-restart"

/-- Whether `args` begins with `restarted`, and `args` without it. -/
def strip : List String → Bool × List String
  | first :: rest => if first == restarted then (true, rest) else (false, first :: rest)
  | [] => (false, [])

/-- The isolation of this process's Git (`Regula.Filesystem.Construction.isolationEnvironment`)
and the entries of it whose value this process's environment does not have (`unisolated`, over a
reading of each named variable). -/
def observe : IO (Array (String × Option String) × Array (String × Option String)) := do
  let isolation ← Regula.Filesystem.Construction.isolationEnvironment
  let values ← isolation.mapM fun (name, _) => do return (name, ← IO.getEnv name)
  let read (name : String) : Option String := (values.find? (·.1 == name)).bind (·.2)
  return (isolation, unisolated read isolation)

/-- What a caller sets or removes so that its environment has the entries `entries`, without the
values it has now. -/
def describe (entries : Array (String × Option String)) : String :=
  ", ".intercalate <| entries.toList.map fun
    | (name, none) => s!"unset {name}"
    | (name, some value) => s!"{name}={value}"

/-- The file name of the executable that Lake builds for the `lean_exe` whose executable name is
`program`: `program` with the platform's executable extension.

Assumes: Lake v4.34.1 names the file of an executable by its `exeName` and
`System.FilePath.exeExtension` (`Lake/Config/LeanExe.lean:66-69`). -/
def executableFile (program : String) : String :=
  ((System.FilePath.mk program).addExtension System.FilePath.exeExtension).toString

/-- Whether the running executable is the file that Lake builds for `program`
(`executableFile`), by the file name of `IO.appPath`. Under the Lean frontend (`lean --run`), in a
plugin of `lean` or in a renamed copy of the executable, it is not.

The file name is not evidence of how the process was entered, so this is a diagnostic with a
stated limit. `lake exe qualify observers` refuses a program of the package whose name is that of
a program of the toolchain, such as `lean`. A frontend started under the file name of a Regula
executable, such as a hard link to `lean`, still passes. Then `restart` starts that frontend with
`restarted` as its first argument, and it exits with a code other than 0 (observed: v4.34.1 `lean`
prints `unrecognized option` and exits with 1). Neither process runs the program, so nothing runs
without isolation, and that exit status is the result.

Assumes: Lean v4.34.1 `Init/System/IO.lean:952-955` (`IO.appPath`) names the running
executable. -/
def runsAs (program : String) : IO Bool := do
  return (← IO.appPath).fileName == some (executableFile program)

/-- Start this executable again on `args` under `isolation`, after `restarted`, with the inherited
standard streams and working directory, and return the exit status that Lean's wait gives for it.

Assumes: Lean v4.34.1 `Init/System/IO.lean:952-955` (`IO.appPath`) names the running executable;
`Init/System/IO.lean:1420-1450` inherits the three streams, the working directory and the
environment by default and applies `env` left to right (`runtime/process.cpp:436-515`);
`runtime/process.cpp:354-367` returns the exit code, or `128 + n` for a child that signal `n`
ended. -/
def restart (isolation : Array (String × Option String)) (args : List String) : IO UInt32 := do
  let child ← IO.Process.spawn {
    cmd := (← IO.appPath).toString, args := (restarted :: args).toArray, env := isolation }
  child.wait

/-- Run `run` on `args` in an isolated environment, for the program whose Lake executable name is
`program`. When this process's environment has every entry of the isolation, `run` runs here.
Otherwise, when the running executable is the one that Lake builds for `program` (`runsAs`) and
this is its first start, the program starts again under the isolation (`restart`) and its exit
status is the result; `run` does not run here. In each other case the result is the reason for a
refusal, which names the variables still to unset or set, and `run` does not run: when the
running executable is another one, such as `lean` under `lean --run` or a renamed copy; on a
second start (`again`) whose environment still lacks an entry; or when Git's list, the running
executable or the restart is unavailable. An exception of `run` itself is not caught. -/
def enter (program : String) (again : Bool) (run : List String → IO UInt32)
    (args : List String) : IO (Except String UInt32) := do
  let (isolation, missing) ← match ← observe.toBaseIO with
    | .ok observed => pure observed
    | .error error => return .error s!"Git isolation is unavailable: {error}"
  if missing.isEmpty then return .ok (← run args)
  match ← (runsAs program).toBaseIO with
  | .ok true => pure ()
  | .ok false =>
    return .error s!"Git isolation is missing, and this process is not the \
      `{executableFile program}` executable that Lake builds, so it cannot start again under it; \
      start it with: {describe missing}"
  | .error error =>
    return .error s!"Git isolation is missing, and the running executable is unknown ({error}); \
      start it with: {describe missing}"
  if again then
    return .error s!"Git isolation did not take effect after one restart; still to set: \
      {describe missing}"
  match ← (restart isolation args).toBaseIO with
  | .ok status => return .ok status
  | .error error => return .error s!"could not start again under Git isolation: {error}"

/-- Refuse, with `prefix` and what to set, unless this process's environment has every entry of
the isolation. The refusal tells an interpreted caller, which no guard starts again, which
variables to unset or set before it starts. -/
def requireIsolated (pfx : String) : IO Unit := do
  let (_, missing) ← match ← observe.toBaseIO with
    | .ok observed => pure observed
    | .error error => throw <| IO.userError s!"{pfx}: Git isolation is unavailable: {error}"
  unless missing.isEmpty do
    throw <| IO.userError s!"{pfx}: Lake's own Git commands would inherit this process's Git \
      environment, which is not isolated. Start this program from a compiled Regula program, \
      which isolates its environment before it runs, or start it with: {describe missing}"

end Regula.GitIsolation
