import Lean.Compiler.IR.EmitUtil
import Lean.Elab.Command
import Regula.Removal
import Regula.TaskManager

/-! # The check that each compiled program needing the task manager or a process uses the guard

A compiled program starts Lean's task manager only after the initializers of its modules, and with
no thread when `LEAN_NUM_THREADS` is `0` (`Regula.TaskManager`). `checkProgram` follows the
compiled code of the program whose `main` the environment declares. When that code reaches a
function of the runtime that needs the task manager (`symbols`, `uvPrefix`) or that starts a
process (`processSymbol`), it requires `main` to have the closed form of the guard (`closedForm`):
`Regula.TaskManager.guard` applied to a string literal, the program's refusal and the program
itself, each of the two a constant. Lean evaluates the arguments of an application before the call,
and none of these three runs code of the program when it is evaluated. The refusal, which the guard
runs in a process without a task manager or without Git isolation, must reach none of those
functions. The program then refuses to start without a task manager, with its exit code of a run
that established no result and its result destinations marked incomplete, instead of running its
tasks on one thread, ending with a panic or reading no task manager. And it runs only in an
environment under Git isolation (`Regula.GitIsolation.enter`), so the Git commands that Lake
starts for it, in its own process or in a process it starts, inherit that isolation. A program
whose compiled code reaches none of those functions passes without the guard, as `auditApp` does.

The code that initializes the modules that a program links runs before `main`, so before the
guard: the actions of `[init]` declarations and the values of declarations with no parameter
(`Regula.Removal.initializersOf`). The check refuses a program, whatever `main` is, when that code
can start a process (`initializersReached?`). A declaration whose evaluation runs only full
applications and C functions that compute a value (`valueExterns`) builds its value and applies
none of its closures, so it starts no process itself (`evaluatesValue`). Each other declaration is
followed through every declaration it refers to, closures included. Four registrations of Lean's
builtin `bv_decide` tactics, named exactly, also store their closures in a reference
(`registrations`).

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

The initializers of a compiled program are not followed for the functions that need the task
manager. They run before the task manager starts in every run, whatever `LEAN_NUM_THREADS` says,
so none of them runs with one, the same in every run, and no guard runs before them (the
`Assumes:` entry of `Regula.TaskManager.guard`). The
check reads the compiled code that the environment holds, and a reached declaration whose compiled
code it does not hold counts as one that needs the task manager. The C functions of the runtime
are not followed: `symbols` and `uvPrefix` name the ones that need the task manager. As for the
removal check (`Regula.Removal`), the criterion is honest code: a hand-written `extern` bound to
another C function of the runtime that reads the task manager, or a `main` whose compiled code
another declaration replaces, is outside it. -/

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

/-- The C function of the runtime that starts a process, as the `extern` attribute of
`IO.Process.spawn` names it. `IO.Process.output` and `IO.Process.run` start their processes
through `IO.Process.spawn`, and so do Lake's `captureProc`, `proc` and `testProc`, which run every
Git command of Lake.

Assumes: Lean 4.34.1 binds `IO.Process.spawn` to `lean_io_process_spawn`
(`src/Init/System/IO.lean:1489`), and no other `extern` declaration of Lean's library outside
`src/runtime/uv` (`uvPrefix`) is bound to a C function that starts a process, by a search of
`src` for the `extern` attributes whose names hold `spawn`, `process`, `exec`, `fork` or
`system`. -/
def processSymbol : String := "lean_io_process_spawn"

/-- Whether the entry of an `extern` attribute calls the C function that starts a process
(`processSymbol`): by its name, or in the C text of an inline entry. -/
def startsProcess : ExternEntry → Bool
  | .standard _ fn => fn == processSymbol
  | .inline _ pattern => (pattern.splitOn processSymbol).length > 1
  | _ => false

/-- Whether the entry of an `extern` attribute calls a C function that only a program started
through the guard may call: one that needs the task manager (`needsTaskManager`) or that starts a
process (`startsProcess`). -/
def needsGuard (entry : ExternEntry) : Bool :=
  needsTaskManager entry || startsProcess entry

/-- Whether `name` is an `extern` declaration of `env` bound to a C function for which `bound`
holds (`needsGuard`, `startsProcess`), whatever its name. -/
def boundBy (env : Environment) (bound : ExternEntry → Bool) (name : Name) : Bool :=
  match findEnvDecl env name with
  | some (.extern _ _ _ data) => data.entries.any bound
  | _ => false

/-- The C functions of the Lean 4.34.1 runtime, each by the declaration bound to it, that compute a
value from their arguments: arithmetic, comparison and conversion of natural numbers and of
fixed-width integers, hashing and comparison of strings and names, the reads of an array and the
update of an array that the caller holds, the address of an object, and whether the platform is
Windows. None of them applies an argument, writes a reference or starts a process. A C function
outside this list counts as one that can do more (`evaluatesValue`); the list holds those that
the initialization code of the package's programs needs.

Assumes: each is bound to the C function of the same role that `include/lean/lean.h` of the
toolchain declares at lines 1009-1139 (arrays), 1387-1390 (strings), 1520-1661 (natural numbers),
2151-2222 (`UInt64` and `USize`) and 3120-3123 (`lean_ptr_addr`, `lean_name_eq`), or to
`lean_system_platform_windows` (`src/Init/System/Platform.lean:22`); each computes its result from
its arguments, and an update copies a shared array before it writes. -/
def valueExterns : List Name :=
  [``Nat.add, ``Nat.mul, ``Nat.div, ``Nat.decEq, ``Nat.decLt, ``Nat.decLe,
    ``UInt64.ofNatLT, ``UInt64.toUSize, ``UInt64.xor, ``UInt64.shiftRight, ``UInt64.decEq,
    ``UInt64.decLt, ``USize.ofNat, ``USize.toNat, ``USize.add, ``USize.sub, ``USize.mul,
    ``USize.land, ``USize.shiftRight, ``USize.decEq, ``USize.decLe, ``mixHash, ``String.hash,
    ``String.compare, ``Lean.Name.beq, ``Array.mkEmpty, ``Array.replicate, ``Array.size,
    ``Array.getInternal, ``Array.getInternalBorrowed, ``Array.get!InternalBorrowed,
    ``Array.ugetBorrowed, ``Array.set, ``Array.uset, ``Array.push, ``ptrAddrUnsafe,
    ``System.Platform.getIsWindows]

/-- The C functions that write a reference, by the declarations bound to them, which
`ST.Prim.Ref.modifyUnsafe` calls: only `registrations` may call them.

Assumes: Lean 4.34.1 binds them to `lean_st_ref_take` and `lean_st_ref_set`
(`src/Init/System/ST.lean:190-195`, `:199-202`), which read or store their argument in the
reference and apply nothing. -/
def referenceExterns : List Name := [``ST.Prim.Ref.take, ``ST.Prim.Ref.set]

/-- The initializers, by their full names, that register the elaborators of Lean's builtin
`bv_decide` and `bv_trace` tactics and of their `grind` forms. Each applies `addBuiltin` to the
tactic table, the key, the name and the elaborator (`src/Lean/KeyedDeclsAttribute.lean:146-148`),
which stores the elaborator, a closure, in the table's reference (`:104-105`). The elaborators
reach `Lean.Meta.Tactic.BVDecide.External.runInterruptible`, which starts the SAT solver
(`src/Lean/Meta/Tactic/BVDecide/External.lean:98-100`; `src/Lean/Elab/Tactic/BVDecide.lean:189-204`,
`src/Lean/Elab/Tactic/Grind/BVDecide.lean:28-40`). The check admits one of these initializers when
its evaluation calls only `valueExterns` and `referenceExterns` and applies no closure
(`evaluatesValue`); it follows every other initializer that reaches the same runner.

Assumes: no code that initializes a module of a program of the package elaborates one of these
tactics, so none applies these elaborators before `main`. The removal check admits the removals of
the same tactics on the same assumption (`Regula.Removal.libraryRemovals`). -/
def registrations : List Name :=
  let bv := `Lean.Elab.Tactic.BVDecide
  let grind := `Lean.Elab.Tactic.Grind.BVDecide
  [mkPrivateNameCore bv (`Lean.Elab.Tactic.BVDecide.evalBvDecide ++ `_regBuiltin ++
      `Lean.Elab.Tactic.BVDecide.evalBvDecide_1),
    mkPrivateNameCore bv (`Lean.Elab.Tactic.BVDecide.evalBvTraceTactic ++ `_regBuiltin ++
      `Lean.Elab.Tactic.BVDecide.evalBvTraceTactic_1),
    mkPrivateNameCore grind (`Lean.Elab.Tactic.Grind.evalBvDecide ++ `_regBuiltin ++
      mkPrivateNameCore grind `Lean.Elab.Tactic.Grind.evalBvDecide_1),
    mkPrivateNameCore grind (`Lean.Elab.Tactic.Grind.evalBvTrace ++ `_regBuiltin ++
      mkPrivateNameCore grind `Lean.Elab.Tactic.Grind.evalBvTrace_1)]

/-- The bound on the number of declarations that `reached?` reads. -/
def maxDeclarations : Nat := 10_000_000

/-- What the compiled code of a program reaches that needs the guard. -/
inductive Reached where
  /-- A call of `primitive`, bound to a C function that needs the task manager or starts a
  process, in the compiled
  code of `caller`; `caller` is `primitive` when the declaration is itself a root. -/
  | primitive (caller primitive : Name)
  /-- A reached declaration whose compiled code the environment does not hold, so what it calls
  is unknown. -/
  | unknown (name : Name)
  deriving BEq, Repr

/-- The first call of a declaration bound to a C function for which `bound` holds (`boundBy`) that
the compiled code of `roots` reaches, with its caller, or the first reached declaration whose
compiled code `env` does not hold; `none` when it reaches neither. Every compiled declaration is
followed, of this package, of Lean's library and of each other package, closures included; a C
function of the runtime is not. -/
def reached? (env : Environment) (roots : Array Name) (bound : ExternEntry → Bool := needsGuard) :
    Option Reached := Id.run do
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
        if boundBy env bound used then return some (.primitive name used)
        if !seen.contains used then
          seen := seen.insert used
          work := work.push used
    | some (.extern _ _ _ data) =>
      if data.entries.any bound then return some (.primitive name name)
      if data.entries.any (· matches .opaque) then return some (.unknown name)
    | none => return some (.unknown name)
  return work.back?.map .unknown

/-- The declarations that `body` applies fully (`Lean.IR.Expr.fap`), pushed onto `acc.1`, and
whether it applies a closure (`Lean.IR.Expr.ap`), or-ed into `acc.2`. A partial application
(`Lean.IR.Expr.pap`) builds a closure and runs nothing, so it adds nothing. -/
partial def applications : FnBody → Array Name × Bool → Array Name × Bool
  | .vdecl _ _ value rest, acc =>
    let acc := match value with
      | .fap function _ => (acc.1.push function, acc.2)
      | .ap .. => (acc.1, true)
      | _ => acc
    applications rest acc
  | .jdecl _ _ joined rest, acc => applications rest (applications joined acc)
  | .case _ _ _ alternatives, acc =>
    alternatives.foldl (fun acc alternative => applications alternative.body acc) acc
  | body, acc => if body.isTerminal then acc else applications body.body acc

/-- What `doesMore` finds: the declarations whose evaluation can do more than build a value, and
whether its two traversals finished within their bound. -/
structure Propagation where
  /-- The declarations found to do more than build a value. -/
  found : Std.HashSet Name
  /-- Whether the forward and the backward traversal each finished with no work left. -/
  complete : Bool

/-- Whether the declaration `name` is to be inspected after `propagation`: each declaration is
when a traversal stopped at its bound with work left, since what it reaches is then unknown;
otherwise those found. So no root is dropped by a traversal that did not finish. -/
def Propagation.inspects (propagation : Propagation) (name : Name) : Bool :=
  !propagation.complete || propagation.found.contains name

/-- The declarations among the code that the evaluation of `roots` runs whose evaluation can do
more than build a value: each declaration of that code that applies a closure, each C function of
it outside `allowed`, each declaration of it whose compiled code `env` does not hold, and each
declaration that applies one of them. The code that the evaluation of a declaration runs is its
compiled body and, through each full application, the code of the declaration applied; a partial
application builds a closure, whose code it does not run. Each traversal reads at most `bound`
declarations; when one stops there with work left, the result is incomplete, and every
declaration, each root among them, is to be inspected (`Propagation.inspects`).

Assumes: in Lean 4.34.1's compiled code a full application (`Lean.IR.Expr.fap`) runs the code of
the declaration applied, a partial application (`Lean.IR.Expr.pap`) builds a closure only, and the
application of a closure (`Lean.IR.Expr.ap`) runs that closure
(`src/Lean/Compiler/IR/Basic.lean:192-197`). -/
def doesMore (env : Environment) (roots : Array Name) (allowed : List Name)
    (bound : Nat := maxDeclarations) : Propagation := Id.run do
  let mut seen : Std.HashSet Name := {}
  for root in roots do seen := seen.insert root
  let mut work := roots
  let mut callers : Std.HashMap Name (Array Name) := {}
  let mut found : Array Name := #[]
  -- Each declaration is added to `work` at most once.
  for _ in [:bound] do
    let some name := work.back? | break
    work := work.pop
    match findEnvDecl env name with
    | some (.fdecl _ _ _ body _) =>
      let (applied, appliesClosure) := applications body (#[], false)
      if appliesClosure then found := found.push name
      for used in applied do
        callers := callers.insert used ((callers.getD used #[]).push name)
        unless seen.contains used do
          seen := seen.insert used
          work := work.push used
    | some (.extern ..) => unless allowed.contains name do found := found.push name
    | none => found := found.push name
  let forward := work.isEmpty
  let mut result : Std.HashSet Name := {}
  for name in found do result := result.insert name
  let mut back := found
  for _ in [:bound] do
    let some name := back.back? | break
    back := back.pop
    for caller in callers.getD name #[] do
      unless result.contains caller do
        result := result.insert caller
        back := back.push caller
  return { found := result, complete := forward && back.isEmpty }

/-- Whether the evaluation of `root` only builds a value: the code that it runs calls no C function
outside `allowed`, applies no closure and is known, and `doesMore` finished
(`Propagation.inspects`). Such an evaluation starts no process, since the only C function that does
is not in `valueExterns` or `referenceExterns`. -/
def evaluatesValue (env : Environment) (allowed : List Name) (root : Name) : Bool :=
  !(doesMore env #[root] allowed).inspects root

/-- What the code that initializes the modules that the program whose `main` is in the module
`root` links can reach (`Regula.Removal.linked`, `Regula.Removal.initializersOf`): the first call
of a declaration bound to the C function that starts a process (`startsProcess`), or the first
declaration whose compiled code `env` does not hold (`reached?`), from each of its declarations
that `doesMore` leaves to inspect (`Propagation.inspects`, `valueExterns`), each of them when its
traversal stopped at the bound, other than `registrations` whose evaluation builds a value and
writes references only.

A declaration that is not followed builds its value and applies none of its closures. Code that
applies a closure is followed through every declaration that it refers to, so through the values
whose closures it can read; and code that stores a closure in a reference calls a C function
outside `valueExterns`, so it is followed too, except `registrations`. -/
def initializersReached? (env : Environment) (root : Name) : Option Reached :=
  let roots := Regula.Removal.initializersOf env (Regula.Removal.linked env root)
  let more := doesMore env roots valueExterns
  reached? env (roots.filter fun declaration => more.inspects declaration &&
      !(registrations.contains declaration &&
        evaluatesValue env (valueExterns ++ referenceExterns) declaration))
    startsProcess

/-- `value` without its metadata. -/
def stripData : Lean.Expr → Lean.Expr
  | .mdata _ value => stripData value
  | value => value

/-- The Lake executable name, the refusal and the program of an application of the guard to a
string literal and two constants: `Regula.TaskManager.guard "name" refuse run`. -/
def guardOf (value : Lean.Expr) : Option (String × Name × Name) :=
  match value.getAppFn, value.getAppArgs.map stripData with
  | .const ``Regula.TaskManager.guard _, #[.lit (.strVal program), .const refuse _, .const run _] =>
    some (program, refuse, run)
  | _, _ => none

/-- The Lake executable name, the refusal and the program of the definition `value` of `main` when
it has the closed form of the guard: `Regula.TaskManager.guard "name" refuse run`, or that
application to the one argument of `fun args => …` (`guardOf`); `none` otherwise. The guard is then
the first code of `main` that runs.

Assumes: in compiled Lean 4.34.1 code, evaluating a string literal or a constant of function type
runs no code of the program: it gives the literal, a closure of the constant, or the value that the
constant's initializer computed before `main`. The compiler gives a definition of function type a
parameter for each argument of its type, so it does not evaluate the definition when it initializes
its module (observed for `def run : List String → IO UInt32 := other`). The code that initializes
the modules is checked on its own (`initializersReached?`). -/
def closedForm (value : Lean.Expr) : Option (String × Name × Name) :=
  match stripData value with
  | .lam _ _ body _ =>
    match stripData body with
    | .app function argument =>
      if stripData argument == .bvar 0 then guardOf (stripData function) else none
    | _ => none
  | value => guardOf value

/-- The Lake executable name, the refusal and the program of `main` in `env` when its definition has
the closed form of the guard (`closedForm`). -/
def guarded (env : Environment) : Option (String × Name × Name) :=
  (env.find? `main |>.bind (·.value? (allowOpaque := true))).bind closedForm

/-- Why the check refuses the program whose `main` the environment `env` declares in the module
`root`; `none` otherwise. The check refuses the program when the code that initializes the modules
that it links can start a process or reaches a declaration whose compiled code is unknown
(`initializersReached?`). When `main` has the closed form of the guard (`guarded`), the check
refuses a refusal whose compiled code reaches a function that needs the task manager or starts a
process, or a declaration whose compiled code is unknown (`reached?`). Otherwise it refuses the
program when the compiled code of `main` reaches one of them. -/
def refusal (env : Environment) (root : Name) : Option String :=
  match initializersReached? env root with
  | some (.primitive caller primitive) =>
    some s!"the code that initializes the modules of the program of {root} can start a process \
      ({caller} calls {primitive}), and it runs before `main`, so that process would not run under \
      the Git isolation of the guard"
  | some (.unknown name) =>
    some s!"the code that initializes the modules of the program of {root} reaches {name}, whose \
      compiled code is not available, so whether it starts a process before `main` is unknown"
  | none =>
  match guarded env with
  | some (_, refuse, _) =>
    match reached? env #[refuse] with
    | none => none
    | some (.primitive caller primitive) =>
      some s!"the refusal {refuse} of the program of {root} needs Lean's task manager or starts \
        a process ({caller} calls {primitive}), and the guard runs it in a process without a task \
        manager or without Git isolation"
    | some (.unknown name) =>
      some s!"the refusal {refuse} of the program of {root} reaches {name}, whose compiled code \
        is not available, so whether it needs Lean's task manager or starts a process is unknown"
  | none => match reached? env #[`main] with
    | none => none
    | some (.primitive caller primitive) =>
      some s!"the program of {root} needs Lean's task manager or starts a process \
        ({caller} calls {primitive}), and its `main` is not `Regula.TaskManager.guard` applied \
        to a string literal, its refusal and its program, each a constant"
    | some (.unknown name) =>
      some s!"the program of {root} reaches {name}, whose compiled code is not available, so \
        whether it needs Lean's task manager or starts a process is unknown, and its `main` is not \
        `Regula.TaskManager.guard` applied to a string literal, its refusal and its program, each \
        a constant"

/-- The check accepts a program exactly when the code that initializes the modules that it links
can reach neither a start of a process nor a declaration whose compiled code is unknown
(`initializersReached?`), and either its `main` has the closed form of the guard with a refusal
whose compiled code reaches neither a function that needs the task manager or starts a process
nor a declaration whose compiled code is unknown, or its `main` has another form and its compiled
code reaches neither. -/
theorem refusal_eq_none_iff (env : Environment) (root : Name) :
    refusal env root = none ↔ initializersReached? env root = none ∧
      ((∃ program refuse run, guarded env = some (program, refuse, run) ∧
          reached? env #[refuse] = none) ∨
        (guarded env = none ∧ reached? env #[`main] = none)) := by
  unfold refusal
  cases hInit : initializersReached? env root with
  | some found => cases found <;> simp
  | none =>
  simp only [true_and]
  cases hGuarded : guarded env with
  | none =>
    cases hReached : reached? env #[`main] with
    | none => simp
    | some found => cases found <;> simp
  | some pair =>
    obtain ⟨program, refuse, run⟩ := pair
    cases hReached : reached? env #[refuse] with
    | none => simp only [hReached]; simp; exact ⟨program, refuse, ⟨rfl, rfl⟩, hReached⟩
    | some found => cases found <;> simp [hReached]

/-- The prefix of the marker that `checkProgram` adds for each program that it checked: the
definition `checked ++ root` of type `Unit`, where `root` is the program's root module. `lake exe
qualify observers` reads the markers from the module data of the package's modules. -/
def checked : Name := `Regula.TaskManagerCheck.checked

/-- The prefix of the marker that `checkProgram` adds for each program whose `main` has the closed
form of the guard (`guarded`): the definition `named ++ root ++ program` of type `Unit`, where
`root` is the program's root module and `program` the string literal that `main` passes to the
guard, as one last component. `lake exe qualify observers` requires `program` to be the executable
name that Lake's loaded workspace declares for `root`, which is the name that
`Regula.GitIsolation.runsAs` compares with the running executable. -/
def named : Name := `Regula.TaskManagerCheck.named

/-- Add the marker definition `marker` of type `Unit`. -/
def mark (marker : Name) : Elab.Command.CommandElabM Unit :=
  Elab.Command.liftCoreM <| addDecl (.defnDecl {
    name := marker, levelParams := [], type := mkConst ``Unit,
    value := mkConst ``Unit.unit, hints := .abbrev, safety := .safe })

/-- Check the program whose `main` the environment declares: fail with the refusal of the program
(`refusal`) when there is one, and otherwise record the program (`checked`) and, when `main` has
the closed form of the guard, the executable name that it passes to the guard (`named`). -/
def checkProgram : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  unless env.contains `main do
    throwError "no `main` is declared here, so there is no program to check"
  let root := match env.getModuleIdxFor? `main with
    | some index => env.header.moduleNames[index.toNat]!
    | none => env.mainModule
  if let some refused := refusal env root then throwError refused
  mark (checked ++ root)
  if let some (program, _, _) := guarded env then mark (.str (named ++ root) program)

end Regula.TaskManagerCheck
