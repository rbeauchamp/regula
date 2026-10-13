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
refusal needs no task manager (`Regula.TaskManagerCheck.checkProgram`). -/

namespace Regula.TaskManager

/-- The line that `guard` prints for the program `program` refused for `reason`. -/
def refusalLine (program reason : String) : String :=
  s!"{program}: INCOMPLETE: {reason}; no run started, so there is no result"

/-- The program `program` on the arguments `args`, refused before it starts when this process has
no task manager (`Regula.Probe.taskManagerMissing`): `guard` then prints the reason on one line
to standard error (`refusalLine`) and returns what `refuse` returns on the reason and `args`.
`refuse` is the program's refusal: it marks each result destination of `args` incomplete, with the
reason, and returns the program's exit code of a run that established no result. Otherwise `guard`
returns what `run` returns on `args`.

`Regula.TaskManagerCheck.checkProgram` requires a compiled program that needs the task manager to
define `main` as `guard` applied to a string literal and two constants, and its refusal to need no
task manager.

Assumes: Lean 4.34.1's compiled `main` runs the initializer of the program's root module, which
runs those of the modules it imports, then `lean_io_mark_end_initialization` and only then
`lean_init_task_manager`, in every run, whatever `LEAN_NUM_THREADS` says
(`src/Lean/Compiler/LCNF/EmitC.lean:1127-1131`). So `guard` runs after every initializer, and an
initializer that needs the task manager stops every run of its program, with a task manager to come
or not: that is a defect of the program in every environment, outside the runs that `guard`
refuses, which are those whose initialization completed. -/
def guard (program : String) (refuse : String → List String → IO UInt32)
    (run : List String → IO UInt32) (args : List String) : IO UInt32 := do
  if let some reason ← Regula.Probe.taskManagerMissing then
    IO.eprintln (refusalLine program reason)
    refuse reason args
  else
    run args

end Regula.TaskManager
