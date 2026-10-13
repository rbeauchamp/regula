import RegulaPolicy.TaskManager

/-! # The refusal of a program without Lean's task manager

A Lean program runs its tasks on the threads of Lean's task manager. A compiled program starts the
task manager after the initializers of its modules and before `main`, with the number of threads
that `LEAN_NUM_THREADS` gives, and none when it is `0`. Without a task manager, Lean runs a task on
the thread that starts it, a call of `IO.Promise.new` ends the process with a panic and exit code 1,
and a wait for any of several tasks reads no task manager. So a run of a program that needs one
can end with the exit code of a verdict that no completed run established (issue 393).

`RegulaPolicy.TaskManager.missing` observes whether the process has a task manager, through Lean's
own scheduling of a task. `guard` runs a program only when it has one, and otherwise refuses before
the program starts: it prints one reason line and returns the program's exit code of a run that
established no result. Each compiled program of the package whose code reaches a function of the
runtime that needs the task manager starts through `guard` (`Regula.TaskManagerCheck.checkProgram`). -/

namespace Regula.TaskManager

open RegulaPolicy.TaskManager

/-- The line that `guard` prints for the program `program` refused for `reason`. -/
def refusalLine (program reason : String) : String :=
  s!"{program}: INCOMPLETE: {reason}; no run started, so there is no result"

/-- The program `program` on the arguments `args`, refused before it starts when this process has
no task manager (`RegulaPolicy.TaskManager.missing`): `guard` then prints the reason on one line
to standard error (`refusalLine`) and returns `incomplete`, the program's exit code of a run that
established no result. Otherwise it returns what `run` returns on `args`.

`Regula.TaskManagerCheck.checkProgram` requires a compiled program that needs the task manager to
define `main` as an application of `guard`. -/
def guard (program : String) (incomplete : UInt32) (run : List String → IO UInt32)
    (args : List String) : IO UInt32 := do
  if let some reason ← missing then
    IO.eprintln (refusalLine program reason)
    return incomplete
  run args

end Regula.TaskManager
