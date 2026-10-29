import Regula.GitIsolation

/-! # The refusal of a program without Lean's task manager, and its start under Git isolation

A Lean program runs its tasks on the threads of Lean's task manager. A compiled program starts the
task manager after the initializers of its modules and before `main`, with the number of threads
that `LEAN_NUM_THREADS` gives, and none when it is `0`. Without a task manager, Lean runs a task on
the thread that starts it, a call of `IO.Promise.new` ends the process with a panic, which exits
with code 1 or, when `LEAN_ABORT_ON_PANIC` is set, aborts, and a wait for any of several tasks
reads no task manager. So a run of a program that needs one can end with the exit code of a verdict
that no completed run established (issue 393).

`taskManagerMissing` observes whether the process has a task manager, through Lean's
own scheduling of a task. `guard` runs a program only when it has one. Otherwise it refuses before
the program starts: it prints one reason line and runs the program's own refusal, which marks each
result destination that the arguments name incomplete, with the reason, and returns the program's
exit code of a run that established no result.

With a task manager, `guard` starts the program under Git isolation (`Regula.GitIsolation.enter`):
it runs here when its environment is isolated. When isolation is missing and the running executable
is the file that Lake builds for the program, it starts again once under the isolation, which the
Git commands of Lake in this process and in every process it starts inherit. When isolation is
missing in any other process, such as one that the Lean frontend runs (`lean --run`), a plugin of
`lean` or a renamed copy of the executable, or when isolation is unavailable or does not take
effect, `guard` refuses the same way, with that reason. Each compiled program of the package whose
code reaches a function of the runtime that needs the task manager, or that starts a process,
starts through `guard`, and its refusal does neither (`Regula.TaskManagerCheck.checkProgram`).

A run that has a task manager can stop early too, before it writes or marks a destination. So
`guard` runs the refusal before every run as well, with the reason that the run has not completed
(`startedReason`), before it enters the isolation: no code of the program runs before each
destination is marked, and an earlier completed result does not remain at a destination that a run
which stopped early marked (issue 423). A destination that the writer refuses
(`Regula.Destination`), such as a symbolic link, keeps what it holds, and a reader that follows the
link still reads its target, which may hold an earlier completed result. A program that starts
again under the isolation marks them again in the same way. The renderers of the website are the
exception: their refusals move nothing for `startedReason`, since a run that Verso starts keeps
Verso's write behaviour and a resumed render reads the saved state of an earlier one. -/

namespace Regula.TaskManager

/-- The reason that `taskManagerMissing` gives for a process without Lean's task manager. -/
def taskManagerMissingReason : String :=
  "Lean's task manager is not running in this process: a task of priority \
    `Task.Priority.dedicated` ran on the thread that started it (Lean starts none when \
    LEAN_NUM_THREADS is 0)"

/-- Why this process has no Lean task manager, or `none` when it has one. It runs one task of
priority `Task.Priority.dedicated` and compares the thread the task ran on with the thread of the
caller: the same thread means that Lean has no task manager. It observes Lean's own scheduling of a
task, not the value of `LEAN_NUM_THREADS`, and it needs no task manager itself. The guard of each
program of the package (`guard`) uses it. The observation of the process is a trusted boundary, and
nothing here proves it.

Assumes: Lean 4.35.0 gives `Task.Priority.dedicated` the value 9 (`src/Init/Core.lean:677`), above
`LEAN_MAX_PRIO`, 8, and below `LEAN_SYNC_PRIO`, the largest `unsigned`
(`src/runtime/object.cpp:71-72`); the task manager runs a task of such a priority on a new thread
that it starts for that task (`enqueue_core` and `spawn_dedicated_worker`,
`src/runtime/object.cpp:792-795` and `868-877`), while `LEAN_SYNC_PRIO` would run it on the
caller's thread (`788-791`). Without a task manager, Lean runs the task on the caller's thread
before it returns (`lean_task_spawn_core`, `src/runtime/object.cpp:1184-1190`), which `IO.asTask`
calls (`lean_io_as_task`, `src/runtime/io.cpp:1551-1554`). Assumes: two threads that run at once
have different identifiers (`lean_io_get_tid`, `src/runtime/process.cpp:340-352`,
`pthread_threadid_np` on macOS and `gettid` on Linux); the caller's thread runs until the task has
ended, because it waits for it. -/
def taskManagerMissing : IO (Option String) := do
  let caller ← IO.getTID
  let thread ← IO.ofExcept (← IO.wait (← IO.asTask (prio := .dedicated) IO.getTID))
  return if thread == caller then some taskManagerMissingReason else none

/-- The line that `guard` prints for the program `program` refused for `reason`. -/
def refusalLine (program reason : String) : String :=
  s!"{program}: INCOMPLETE: {reason}; no run started, so there is no result"

/-- The reason that each result destination of a run records from the start of the run until the
run writes it: `guard` marks each destination with it before the run starts. -/
def startedReason : String := "the run has not completed"

/-- The program `program` on the arguments `args`, refused before it starts when this process has
no task manager (`taskManagerMissing`): `guard` then prints the reason on one line
to standard error (`refusalLine`) and returns what `refuse` returns on the reason and `args`.
`refuse` is the program's refusal: it marks each result destination of `args` incomplete, with the
reason, and returns the program's exit code of a run that established no result. Otherwise `guard`
runs `refuse` on `startedReason` and `args`, and discards the exit code that it returns, so each
result destination of `args` that its writer admits (`Regula.Destination`) is marked incomplete
before any code of the program runs. Two refusals are the exception: those of the website's
renderers, `regula-site` and `regula-standard`, move nothing for `startedReason`, so an earlier
render's output stays until Verso writes over it. Then it
runs `run` on `args` under Git isolation (`Regula.GitIsolation.enter`), with `program` as the Lake
executable name of the program: it returns what `run` returns when it runs here, or the exit status
of the program started again under the isolation. When isolation is missing and the running
executable is not the one that Lake builds for `program`, such as under the Lean frontend
(`lean --run`), or when isolation is unavailable or did not take effect, it returns the same
refusal with that reason. A leading `Regula.GitIsolation.restarted` is removed from `args` first
(`Regula.GitIsolation.strip`), so neither `run` nor `refuse` reads it. A run that stops before it
writes a destination that `refuse` marked, whatever stops it, thus leaves it marked incomplete,
and a refusal, an early stop and a completed run take each destination from one reading, the
refusal's, and mark it through one writer.

`Regula.TaskManagerCheck.checkProgram` requires a compiled program that needs the task manager or
starts a process to define `main` as `guard` applied to a string literal and two constants, and its
refusal to need no task manager and to start no process. The qualification of the package's
programs (`Regula.Qualification.Observers`) requires that literal to be the executable name that
Lake's loaded workspace declares for the program's root.

Assumes: Lean 4.35.0's compiled `main` runs the initializer of the program's root module, which
runs those of the modules it imports, then `lean_io_mark_end_initialization` and only then
`lean_init_task_manager`, in every run, whatever `LEAN_NUM_THREADS` says
(`src/Lean/Compiler/LCNF/EmitC.lean:1127-1131`). So no initializer runs with a task manager, and
what one does without it is the same in every run: a task that it starts runs on the
initializer's thread before the call returns (`lean_task_spawn_core`,
`src/runtime/object.cpp:1184-1190`), and a promise that it creates ends the process with a panic
(`lean_promise_new`, `src/runtime/object.cpp:1305-1310`).
`guard` runs after every initializer, so the runs that it refuses are those whose initialization
completed, and `LEAN_NUM_THREADS` changes nothing that runs before it. -/
def guard (program : String) (refuse : String → List String → IO UInt32)
    (run : List String → IO UInt32) (args : List String) : IO UInt32 := do
  let (again, args) := Regula.GitIsolation.strip args
  if let some reason ← taskManagerMissing then
    IO.eprintln (refusalLine program reason)
    refuse reason args
  else
    discard <| refuse startedReason args
    match ← Regula.GitIsolation.enter program again run args with
    | .ok status => return status
    | .error reason =>
      IO.eprintln (refusalLine program reason)
      refuse reason args

end Regula.TaskManager
