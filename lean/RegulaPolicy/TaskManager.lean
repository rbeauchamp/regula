module

public import Init

/-! # Whether a process has Lean's task manager

A Lean program runs its tasks on the threads of Lean's task manager, and a compiled program starts
none when `LEAN_NUM_THREADS` is `0`. `missing` observes whether this process has one, through
Lean's own scheduling of a task, not through a read of that variable. The probe of an audit
(`Regula.Probe.requireDedicatedThreads`) and the guard of each program of the package
(`Regula.TaskManager.guard`) use it. It is here, in a library that the probe may import, because
the probe is loaded into every audited environment. The observation of the process is a trusted
boundary, and nothing here proves it. -/

@[expose] public section

namespace RegulaPolicy.TaskManager

/-- The reason that `missing` gives for a process without a task manager. -/
def missingReason : String :=
  "Lean's task manager is not running in this process: a task of priority \
    `Task.Priority.dedicated` ran on the thread that started it (Lean starts none when \
    LEAN_NUM_THREADS is 0)"

/-- Why this process has no task manager, or `none` when it has one. It runs one task of priority
`Task.Priority.dedicated` and compares the thread the task ran on with the thread of the caller:
the same thread means that Lean has no task manager.

Assumes: Lean 4.34.1 runs a task of priority above `LEAN_MAX_PRIO`, as `Task.Priority.dedicated`
is, on a new thread that the task manager starts for it (`enqueue_core` and
`spawn_dedicated_worker`, `src/runtime/object.cpp:805-808` and `884-893`), and without a task
manager runs it on the caller's thread before it returns (`lean_task_spawn_core`,
`src/runtime/object.cpp:1200-1206`), which `IO.asTask` calls (`lean_io_as_task`,
`src/runtime/io.cpp:1553-1556`). Assumes: two threads that run at once have different
identifiers (`lean_io_get_tid`, `src/runtime/process.cpp:340-352`, `pthread_threadid_np` on macOS
and `gettid` on Linux); the caller's thread runs until the task has ended, because it waits for
it. -/
def missing : IO (Option String) := do
  let caller ← IO.getTID
  let thread ← IO.ofExcept (← IO.wait (← IO.asTask (prio := .dedicated) IO.getTID))
  return if thread == caller then some missingReason else none

end RegulaPolicy.TaskManager

end
