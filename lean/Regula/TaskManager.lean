import Regula.Probe

/-! # The refusal of a program without Lean's task manager

A Lean program runs its tasks on the threads of Lean's task manager. A compiled program starts the
task manager after the initializers of its modules and before `main`, with the number of threads
that `LEAN_NUM_THREADS` gives, and none when it is `0`. Without a task manager, Lean runs a task on
the thread that starts it, a call of `IO.Promise.new` ends the process with a panic, which exits
with code 1 or, when `LEAN_ABORT_ON_PANIC` is set, aborts, and a wait for any of several tasks
reads no task manager. So a run of a program that needs one can end with the exit code of a verdict
that no completed run established (issue 393).

`Regula.Probe.taskManagerMissing` observes whether the process has a task manager, through Lean's
own scheduling of a task. `guard` runs a program only when it has one. Otherwise it refuses before
the program starts: it prints one reason line and runs the program's own refusal, which marks each
result destination that the arguments name incomplete, with the reason, and returns the program's
exit code of a run that established no result. Each compiled program of the package whose code
reaches a function of the runtime that needs the task manager starts through `guard`, and its
refusal needs no task manager (`Regula.TaskManagerCheck.checkProgram`).

A run that has a task manager can stop early too, before it writes or marks a destination. So
`guard` runs the refusal before every run as well, with the reason that the run has not completed
(`startedReason`): no code of the program runs before each destination is marked, and an earlier
completed result never remains where a run that stopped early names one (issue 423). The
renderers of the website are the exception: their refusals move nothing for `startedReason`, since
a run that Verso starts keeps Verso's write behaviour and a resumed render reads the saved state of
an earlier one. -/

namespace Regula.TaskManager

/-- The line that `guard` prints for the program `program` refused for `reason`. -/
def refusalLine (program reason : String) : String :=
  s!"{program}: INCOMPLETE: {reason}; no run started, so there is no result"

/-- The reason that each result destination of a run records from the start of the run until the
run writes it: `guard` marks each destination with it before the run starts. -/
def startedReason : String := "the run has not completed"

/-- The program `program` on the arguments `args`, refused before it starts when this process has
no task manager (`Regula.Probe.taskManagerMissing`): `guard` then prints the reason on one line
to standard error (`refusalLine`) and returns what `refuse` returns on the reason and `args`.
`refuse` is the program's refusal: it marks each result destination of `args` incomplete, with the
reason, and returns the program's exit code of a run that established no result. Otherwise `guard`
runs `refuse` on `startedReason` and `args`, and discards the exit code that it returns, so each
result destination of `args` is marked incomplete before any code of the program runs. Then it
returns what `run` returns on `args`. A run that stops before it writes a destination, whatever
stops it, thus leaves that destination marked incomplete, and a refusal, an early stop and a
completed run take each destination from one reading, the refusal's, and mark it through one
writer.

`Regula.TaskManagerCheck.checkProgram` requires a compiled program that needs the task manager to
define `main` as `guard` applied to a string literal and two constants, and its refusal to need no
task manager.

Assumes: Lean 4.34.1's compiled `main` runs the initializer of the program's root module, which
runs those of the modules it imports, then `lean_io_mark_end_initialization` and only then
`lean_init_task_manager`, in every run, whatever `LEAN_NUM_THREADS` says
(`src/Lean/Compiler/LCNF/EmitC.lean:1127-1131`). So no initializer runs with a task manager, and
what one does without it is the same in every run: a task that it starts runs on the
initializer's thread before the call returns (`lean_task_spawn_core`,
`src/runtime/object.cpp:1200-1206`), and a promise that it creates ends the process with a panic
(`lean_promise_new`, `src/runtime/object.cpp:1321-1326`).
`guard` runs after every initializer, so the runs that it refuses are those whose initialization
completed, and `LEAN_NUM_THREADS` changes nothing that runs before it. -/
def guard (program : String) (refuse : String → List String → IO UInt32)
    (run : List String → IO UInt32) (args : List String) : IO UInt32 := do
  if let some reason ← Regula.Probe.taskManagerMissing then
    IO.eprintln (refusalLine program reason)
    refuse reason args
  else
    discard <| refuse startedReason args
    run args

end Regula.TaskManager
