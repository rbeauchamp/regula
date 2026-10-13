import Lean.Compiler.IR.EmitUtil
import Lean.Elab.Command
import Regula.TaskManager
import Regula.Removal

/-! # The check that each compiled program needing the task manager starts through the guard

A compiled program starts Lean's task manager only after the initializers of its modules, and with
no thread when `LEAN_NUM_THREADS` is `0` (`Regula.TaskManager`). `checkProgram` follows the
compiled code of the program whose `main` the environment declares. When that code reaches a
function of the runtime that needs the task manager (`symbols`, `uvPrefix`), it requires `main` to
have the closed form of the guard (`closedForm`): `Regula.TaskManager.guard` applied to a string
literal, the program's refusal and the program itself, each of the two a constant. Lean evaluates
the arguments of an application before the call, and none of these three runs code of the program
when it is evaluated. The refusal, which the guard runs in a process without a task manager, must
reach none of those functions. The program then refuses to start without a task manager, with its
exit code of a run that established no result and its result destinations marked incomplete,
instead of running its tasks on one thread, ending with a panic or reading no task manager. A
program whose compiled code reaches none of those functions passes without the guard, as
`auditApp` does. The initializers of the modules that a program links run before the task manager
starts in every run, so no guard can give them one: the check refuses a program when the code of an
initializer outside Lean's toolchain reaches a function of the runtime that stops the process
without one (`stopSymbols`, `initializerReach`), with the initializers of the removal check's
inventory (`Regula.Removal.initializersOf`).

Each compiled program of the package runs this check at the end of its root module, which fails to
build when the check refuses, and the module records the program (`checked`). `lake exe qualify
observers` refuses a compiled program of the root package that no module records, and checks
itself the one root that no library module can import, `auditApp`'s `Main`
(`Regula.Qualification.Observers`). The executables of the `website` and `markdown` packages run
the check in their root modules too, outside that inventory.

## What it does not cover

A program run with `lean --run`, such as the verification and provisioning drivers, needs no
guard. The `lean` executable starts its task manager before it elaborates the file, with the number
of threads that `-j` gives and otherwise as many as the hardware has, whatever `LEAN_NUM_THREADS`
says. Without threads, its own elaboration of the file creates a promise and ends with a panic
before `main` runs.

The initializers that the modules of Lean's toolchain declare are not followed, and code outside
the toolchain is followed from an initializer only up to a declaration of the toolchain: a call of
one bound to a C function that stops the process without a task manager is found, but one of
another function of the toolchain that reaches such a C function is not, as for
`IO.CancelToken.new` (`initializerReach`). Followed through the toolchain, the initializers of
every program of this package reach one, `IO.Promise.resolve`, through the attributes that its
modules register, though they complete in a run without a task manager: the self-test's control
observes the guard's refusal after them, for this build. The check reads the compiled code that the
environment holds, and a reached declaration whose compiled code it does not hold counts as one
that needs the task manager. The C functions of the runtime are not followed: `symbols` and
`uvPrefix` name the ones that need the task manager. As for the removal check
(`Regula.Removal`), the criterion is honest code: a hand-written `extern` bound to another C
function of the runtime that reads the task manager, or a `main` whose compiled code another
declaration replaces, is outside it. -/

namespace Regula.TaskManagerCheck

open Lean IR

/-- The C functions of the Lean 4.34.1 runtime that need the task manager, each as the `extern`
attribute of Lean's library names it: the functions of `src/runtime/object.cpp` and
`src/runtime/io.cpp` that read the task manager (`g_task_manager`) or start a task or a promise
through a function that reads it (`lean_task_spawn_core`, `lean_task_map_core`,
`lean_task_bind_core`, `lean_promise_new`).

Assumes: Lean 4.34.1, by a search of `src/runtime` for `g_task_manager`, `lean_task_spawn_core`,
`lean_task_map_core`, `lean_task_bind_core`, `lean_promise_new` and `lean_io_promise_new`:
`Task.spawn`, `Task.map`
and `Task.bind` are bound to `lean_task_spawn`, `lean_task_map` and `lean_task_bind`
(`src/Init/Core.lean:686`, `701` and `717`), which call the functions of the same name with
`_core` (`src/include/lean/lean.h:1438-1446`); the `IO` operations on tasks and promises are bound
to the other names (`src/Init/System/IO.lean:244`, `257`, `271`, `505`, `511`, `555` and `573`,
`src/Init/System/Promise.lean:40`, `48` and `54`), whose C functions read the task manager or
call one that does (`src/runtime/io.cpp:1553-1601`, `src/runtime/object.cpp:1200-1365`); and no
C function of the runtime outside `src/runtime/object.cpp`, `src/runtime/io.cpp`,
`src/runtime/uv` and the wrappers of `lean.h` above calls one of them. -/
def symbols : List String :=
  ["lean_task_spawn", "lean_task_map", "lean_task_bind", "lean_io_as_task", "lean_io_map_task",
    "lean_io_bind_task", "lean_io_check_canceled", "lean_io_cancel", "lean_io_get_task_state",
    "lean_io_wait_any", "lean_io_promise_new", "lean_io_promise_resolve",
    "lean_io_promise_result_opt"]

/-- The prefix of the C functions of the runtime's asynchronous input and output, each of which
counts as one that needs the task manager.

Assumes: in Lean 4.34.1, the functions of `src/runtime/uv` that start an operation return a
promise (`lean_promise_new` or `lean_io_promise_new`, for example `lean_uv_timer_next` and
`lean_uv_tcp_connect`, `src/runtime/uv/timer.cpp:114-124` and `src/runtime/uv/tcp.cpp:124-140`);
the prefix counts all of them, which can only add programs that need the guard. -/
def uvPrefix : String := "lean_uv_"

/-- Whether the entry of an `extern` attribute calls a C function that needs the task manager
(`symbols`, `uvPrefix`): by its name, or in the C text of an inline entry. -/
def needsTaskManager : ExternEntry → Bool
  | .standard _ fn => symbols.contains fn || fn.startsWith uvPrefix
  | .inline _ pattern => (uvPrefix :: symbols).any fun symbol => (pattern.splitOn symbol).length > 1
  | _ => false

/-- The C functions of the Lean 4.34.1 runtime that stop the process when they are called without
a task manager, as initializers are called, each as the `extern` attribute of Lean's library names
it: `lean_io_promise_new` ends with Lean's internal panic, `lean_io_promise_resolve` and
`lean_io_wait_any` dereference the absent task manager, and each function of `src/runtime/uv`
listed creates a promise. The other functions of `symbols` do not stop there: a task is started,
mapped or bound by running it on the caller's thread, so each task is finished, and cancelling a
finished task, reading its state or checking for cancellation outside a task reads no task
manager.

Assumes: Lean 4.34.1. `lean_promise_new` calls `lean_internal_panic` without a task manager
(`src/runtime/object.cpp:1321-1327`), which prints and calls `std::exit(1)` (`object.cpp:92-96`),
and `lean_io_promise_new` calls it (`object.cpp:1348-1351`); `lean_promise_resolve` and
`lean_io_wait_any_core` call a method of `g_task_manager` (`object.cpp:1344-1346`, `1317-1319`),
which `lean_io_promise_resolve` and `lean_io_wait_any` call (`object.cpp:1353-1356`,
`src/runtime/io.cpp:1599-1600`); `lean_task_spawn_core`, `lean_task_map_core` and
`lean_task_bind_core` run the task on the caller's thread when `g_task_manager` is null
(`object.cpp:1200-1207`, `1222-1231`, `1284-1293`); `lean_io_cancel_core` returns for a finished
task, `lean_io_get_task_state_core` reads a finished task without the task manager and
`lean_io_check_canceled_core` reads it only inside a task (`object.cpp:1295-1315`); and the
functions of `src/runtime/uv` that call `lean_promise_new` or `lean_io_promise_new` are those
listed (`dns.cpp:36-53`, `128-134`, `signal.cpp:137-220`, `system.cpp:425-431`,
`tcp.cpp:124-140`, `183-230`, `278-292`, `353-363`, `520-530`, `622-640`, `timer.cpp:114-118`,
`udp.cpp:135-167`, `252-264`, `336-347`). -/
def stopSymbols : List String :=
  ["lean_io_promise_new", "lean_io_promise_resolve", "lean_io_wait_any", "lean_uv_dns_get_info",
    "lean_uv_dns_get_name", "lean_uv_signal_next", "lean_uv_random", "lean_uv_tcp_connect",
    "lean_uv_tcp_send", "lean_uv_tcp_recv", "lean_uv_tcp_wait_readable", "lean_uv_tcp_accept",
    "lean_uv_tcp_shutdown", "lean_uv_timer_next", "lean_uv_udp_send", "lean_uv_udp_recv",
    "lean_uv_udp_wait_readable"]

/-- Whether the entry of an `extern` attribute calls a C function that stops the process without a
task manager (`stopSymbols`): by its name, or in the C text of an inline entry. -/
def stopsWithoutTaskManager : ExternEntry → Bool
  | .standard _ fn => stopSymbols.contains fn
  | .inline _ pattern => stopSymbols.any fun symbol => (pattern.splitOn symbol).length > 1
  | _ => false

/-- Whether `name` is an `extern` declaration of `env` with an entry that `flagged` flags, by default
one bound to a C function that needs the task manager (`needsTaskManager`), whatever its name. -/
def boundToTaskManager (env : Environment) (name : Name)
    (flagged : ExternEntry → Bool := needsTaskManager) : Bool :=
  match findEnvDecl env name with
  | some (.extern _ _ _ data) => data.entries.any flagged
  | _ => false

/-- The bound on the number of declarations that `reached?` reads. -/
def maxDeclarations : Nat := 10_000_000

/-- What the compiled code of a program reaches that needs the task manager. -/
inductive Reached where
  /-- A call of `primitive`, bound to a C function that needs the task manager, in the compiled
  code of `caller`; `caller` is `primitive` when the declaration is itself a root. -/
  | primitive (caller primitive : Name)
  /-- A reached declaration whose compiled code the environment does not hold, so what it calls
  is unknown. -/
  | unknown (name : Name)
  deriving BEq, Repr

/-- The first declaration bound to a C function that needs the task manager
(`boundToTaskManager`) that the compiled code of `roots` reaches, with its caller, or the first
reached declaration whose compiled code `env` does not hold; `none` when it reaches neither. Every
compiled declaration that `descend` admits is followed, by default each of this package, of Lean's
library and of each other package; a call of a bound declaration is found in the code of each
followed one, whatever `descend` says of the bound declaration, and a C function of the runtime is
not followed. -/
def reached? (env : Environment) (roots : Array Name) (descend : Name → Bool := fun _ => true)
    (flagged : ExternEntry → Bool := needsTaskManager) : Option Reached := Id.run do
  let mut seen : Std.HashSet Name := {}
  for root in roots do seen := seen.insert root
  let mut work := roots
  -- Each declaration is added to `work` at most once; a declaration left in `work` at the bound
  -- is unknown, so the check fails closed.
  for _ in [:maxDeclarations] do
    let some name := work.back? | return none
    work := work.pop
    match findEnvDecl env name with
    | some decl@(.fdecl ..) =>
      for used in collectUsedDecls env [decl] do
        if used == name then continue
        if boundToTaskManager env used flagged then return some (.primitive name used)
        if !seen.contains used && descend used then
          seen := seen.insert used
          work := work.push used
    | some (.extern _ _ _ data) =>
      if data.entries.any flagged then return some (.primitive name name)
      if data.entries.any (· matches .opaque) then return some (.unknown name)
    | none => return some (.unknown name)
  return work.back?.map .unknown

/-- The roots of the module names of Lean's toolchain: `Init`, `Std`, `Lean` and `Lake`. -/
def toolchainRoots : List Name := [`Init, `Std, `Lean, `Lake]

/-- Whether `name` is declared by a module of Lean's toolchain (`toolchainRoots`); a declaration of
the module being elaborated is not. -/
def toolchain (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | some index => env.header.moduleNames[index.toNat]?.any (toolchainRoots.contains ·.getRoot)
  | none => false

/-- What the initializers of the modules that the program of `root` links reach that stops the
process without a task manager (`reached?`, `stopsWithoutTaskManager`). The roots are the
initializers of the inventory of the removal check (`Regula.Removal.initializersOf`) that no module
of the toolchain declares, and only code outside the toolchain is followed, so a call of a
declaration bound to a C function that stops the process is found in that code, whatever module
declares the bound one.

Assumes: an initializer outside the toolchain that calls a function of Lean's toolchain whose code
reaches a C function that stops the process without a task manager, such as `IO.CancelToken.new`,
which creates a promise, is not seen, since the toolchain's code is not followed. Followed through
it, the initializers of each program of this package reach one: `IO.Promise.resolve`, from
`Lean.Environment.PromiseCheckedResult.commitChecked`, through the attributes that its modules
register. Observed for this build, not established by the check: each program that the self-test
runs with `LEAN_NUM_THREADS=0` (`axiomGate`, `lint`, `docFenceAudit`, `qualify` and
`checkerSelftest`) prints its guard's refusal, which runs after all its initializers. -/
def initializerReach (env : Environment) (root : Name) : Option Reached :=
  let outside := fun name => !toolchain env name
  reached? env ((Regula.Removal.initializersOf env (Regula.Removal.linked env root)).filter outside)
    outside stopsWithoutTaskManager

/-- `value` without its metadata. -/
def stripData : Lean.Expr → Lean.Expr
  | .mdata _ value => stripData value
  | value => value

/-- The refusal and the program of an application of the guard to a string literal and two
constants: `Regula.TaskManager.guard "name" refuse run`. -/
def guardOf (value : Lean.Expr) : Option (Name × Name) :=
  match value.getAppFn, value.getAppArgs.map stripData with
  | .const ``Regula.TaskManager.guard _, #[.lit (.strVal _), .const refuse _, .const run _] =>
    some (refuse, run)
  | _, _ => none

/-- The refusal and the program of the definition `value` of `main` when it has the closed form of
the guard: `Regula.TaskManager.guard "name" refuse run`, or that application to the one argument
of `fun args => …` (`guardOf`); `none` otherwise. The guard is then the first code of `main` that
runs.

Assumes: in compiled Lean 4.34.1 code, evaluating a string literal or a constant of function type
runs no code of the program: it gives the literal, a closure of the constant, or the value that the
constant's initializer computed before `main`. The compiler gives a definition of function type a
parameter for each argument of its type, so it does not evaluate the definition when it initializes
its module (observed for `def run : List String → IO UInt32 := other`). The initializers are
checked apart (`initializerReach`). -/
def closedForm (value : Lean.Expr) : Option (Name × Name) :=
  match stripData value with
  | .lam _ _ body _ =>
    match stripData body with
    | .app function argument =>
      if stripData argument == .bvar 0 then guardOf (stripData function) else none
    | _ => none
  | value => guardOf value

/-- The refusal and the program of `main` in `env` when its definition has the closed form of the
guard (`closedForm`). -/
def guarded (env : Environment) : Option (Name × Name) :=
  (env.find? `main |>.bind (·.value? (allowOpaque := true))).bind closedForm

/-- Why the check refuses the program whose `main` the environment `env` declares in the module
`root`; `none` otherwise. When `main` has the closed form of the guard (`guarded`), the check
refuses a refusal whose compiled code reaches a function that needs the task manager or a
declaration whose compiled code is unknown (`reached?`). Otherwise it refuses the program when the
compiled code of `main` reaches one of them. Before both, it refuses the program when an initializer
of a module that it links outside the toolchain reaches a function that stops the process without a
task manager or a declaration whose compiled code is unknown (`initializerReach`), since
initializers run before the task manager starts, in every run. -/
def refusal (env : Environment) (root : Name) : Option String :=
  match initializerReach env root with
  | some (.primitive caller primitive) =>
    some s!"an initializer of a module that the program of {root} links stops the process without \
      Lean's task manager ({caller} calls {primitive}), and initializers run before it starts, in \
      every run"
  | some (.unknown name) =>
    some s!"an initializer of a module that the program of {root} links reaches {name}, whose \
      compiled code is not available, so whether it stops the process without Lean's task manager \
      is unknown"
  | none =>
    match guarded env with
    | some (refuse, _) =>
      match reached? env #[refuse] with
      | none => none
      | some (.primitive caller primitive) =>
        some s!"the refusal {refuse} of the program of {root} needs Lean's task manager \
          ({caller} calls {primitive}), and the guard runs it in a process without one"
      | some (.unknown name) =>
        some s!"the refusal {refuse} of the program of {root} reaches {name}, whose compiled code \
          is not available, so whether it needs Lean's task manager is unknown"
    | none => match reached? env #[`main] with
      | none => none
      | some (.primitive caller primitive) =>
        some s!"the program of {root} needs Lean's task manager ({caller} calls {primitive}), and \
          its `main` is not `Regula.TaskManager.guard` applied to a string literal, its refusal and \
          its program, each a constant"
      | some (.unknown name) =>
        some s!"the program of {root} reaches {name}, whose compiled code is not available, so \
          whether it needs Lean's task manager is unknown, and its `main` is not \
          `Regula.TaskManager.guard` applied to a string literal, its refusal and its program, each \
          a constant"

/-- The check accepts a program exactly when the initializers of the modules that it links outside
the toolchain reach neither a function that stops the process without a task manager nor a
declaration whose compiled code is unknown (`initializerReach`), and its `main` has the closed form
of the guard with a refusal whose compiled code reaches neither a function that needs the task
manager nor such a declaration, or its `main` has another form and its compiled code reaches
neither. -/
theorem refusal_eq_none_iff (env : Environment) (root : Name) :
    refusal env root = none ↔ initializerReach env root = none ∧
      ((∃ refuse run, guarded env = some (refuse, run) ∧ reached? env #[refuse] = none) ∨
      (guarded env = none ∧ reached? env #[`main] = none)) := by
  unfold refusal
  cases hInit : initializerReach env root with
  | some found => cases found <;> simp
  | none =>
    simp only [true_and]
    cases hGuarded : guarded env with
    | none =>
      cases hReached : reached? env #[`main] with
      | none => simp
      | some found => cases found <;> simp
    | some pair =>
      obtain ⟨refuse, run⟩ := pair
      cases hReached : reached? env #[refuse] with
      | none => simp [hReached]
      | some found => cases found <;> simp [hReached]

/-- The prefix of the marker that `checkProgram` adds for each program that it checked: the
definition `checked ++ root` of type `Unit`, where `root` is the program's root module. `lake exe
qualify observers` reads the markers from the module data of the package's modules. -/
def checked : Name := `Regula.TaskManagerCheck.checked

/-- Check the program whose `main` the environment declares: fail with the refusal of the program
(`refusal`) when there is one, and otherwise record the program (`checked`). -/
def checkProgram : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  unless env.contains `main do
    throwError "no `main` is declared here, so there is no program to check"
  let root := match env.getModuleIdxFor? `main with
    | some index => env.header.moduleNames[index.toNat]!
    | none => env.mainModule
  if let some refused := refusal env root then throwError refused
  Elab.Command.liftCoreM <| addDecl (.defnDecl {
    name := checked ++ root, levelParams := [], type := mkConst ``Unit,
    value := mkConst ``Unit.unit, hints := .abbrev, safety := .safe })

end Regula.TaskManagerCheck
