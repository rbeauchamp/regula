import Regula.Removal
import Regula.TaskManagerCheck

/-! # Controls of the check that each program runs

A planted program whose `main` calls a removal primitive fails the check that each program of the
package runs at the end of its root module or of a module that imports it
(`Regula.Removal.checkProgram`), and the same program with its removal made by the filesystem
observer passes it. A planted declaration of this module with the filesystem observer's role
admits nothing, and the check refuses a program while one is declared outside `Regula.Filesystem`
(`Regula.Removal.foreignObservers`).

A planted program whose `main` starts a task, creates a promise or captures a process's output
fails the check that a compiled program needing Lean's task manager starts through the guard
(`Regula.TaskManagerCheck.checkProgram`), and so do one that runs the guard and then starts a task
and one that calls a declaration of another name bound to a C function that needs the task
manager. So do a guard with an argument that starts a task before the call, a guard whose program
is not a constant and a guard whose refusal starts a task. The same task started through the
closed form of `Regula.TaskManager.guard` passes it, applied to `main`'s argument or not, and so
does a program that needs no task manager. A program that starts a process, directly or through
a declaration of another name bound to the C function that starts one, fails the check too, as
does a guard whose refusal starts one, and the same start through the guard passes it, so each
process that a compiled program starts inherits its Git isolation (`Regula.GitIsolation.enter`).
A guarded program fails it too when the code that initializes its modules starts a process,
which runs before the guard: an initializer that starts one, or an unreferenced `unsafe`
definition with no parameter whose value starts one. A definition with no parameter that only
holds a closure that starts a process passes it. A traversal that stops at its bound leaves every
root to inspect, also the one that starts a process that the cut-off would drop
(`Regula.TaskManagerCheck.doesMore`). Each planted declaration is added for its control
alone and removed after it, so this module declares no `main` and records no program. The
self-audit builds this module with the whole `Regula` library, and that build fails when a control
does not give the expected result. -/

namespace Regula.ProgramCheck.Controls

open Lean Elab Command

/-- The refusal of `checkProgram` for the program whose `main` is `value`, of type `IO Unit`, added
to the environment for this control alone after `setup`; `none` when it accepts the program. -/
def refusal (value : Expr) (setup : CommandElabM Unit := pure ()) : CommandElabM (Option String) :=
  withoutModifyingEnv do
    setup
    liftTermElabM do
      addAndCompile (.defnDecl {
        name := `main, levelParams := [], type := mkApp (mkConst ``IO) (mkConst ``Unit), value,
        hints := .opaque, safety := .safe })
    try
      Regula.Removal.checkProgram
      return none
    catch error => return some (← error.toMessageData.toString)

-- A `main` that removes a file with the library's primitive fails the check; one that removes it
-- with the observer passes it.
run_cmd do
  let path := mkStrLit "planted"
  let raw := mkApp (mkConst ``IO.FS.removeFile) (mkApp (mkConst ``System.FilePath.mk) path)
  if (← refusal raw).isNone then
    throwError "the check accepted a program whose main calls IO.FS.removeFile"
  let routed := mkApp2 (mkConst ``Regula.Filesystem.removePath) (mkConst ``Regula.Removal.Kind.file)
    (mkApp (mkConst ``System.FilePath.mk) path)
  if let some refused ← refusal routed then
    throwError "the check refused a program whose main removes with the observer: {refused}"

-- The filesystem observer's role, given in this module: a planted observer that calls the library's
-- primitive does not make its call admitted, and a planted observer that removes nothing makes the
-- check refuse the program that calls it.
run_cmd do
  let observer (name : Name) (body : Term) : CommandElabM Unit := do
    elabCommand (← `(command|
      @[regula_observer filesystem] def $(mkIdent name) : IO Unit := $body))
  let planted := mkConst ((← getCurrNamespace) ++ `plantedObserver)
  let raw ← refusal planted
    (observer `plantedObserver (← `(IO.FS.removeFile "planted")))
  unless raw.any (·.contains "plantedObserver calls IO.FS.removeFile") do
    throwError "a planted filesystem observer of another module made its removal admitted: {raw}"
  let foreign ← refusal planted (observer `plantedObserver (← `(pure ())))
  unless foreign.any (·.contains "the filesystem observer's role is given outside") do
    throwError "the check accepted a program while a filesystem observer is declared outside \
      Regula.Filesystem: {foreign}"


/-- The refusal of the check that a program needing Lean's task manager starts through the guard
(`Regula.TaskManagerCheck.checkProgram`) for the program that the command `program` declares,
added to the environment for this control alone; `none` when it accepts the program. -/
def taskRefusal (program : CommandElabM Unit) : CommandElabM (Option String) :=
  withoutModifyingEnv do
    program
    try
      Regula.TaskManagerCheck.checkProgram
      return none
    catch error => return some (← error.toMessageData.toString)

-- A `main` that starts a task, creates a promise or captures a process's output, which starts a
-- task, fails the task-manager check, and so does one that runs the guard and then starts a task
-- (here the guard's own start of a process can be the call the check names).
-- The guard in its closed form, applied to a string literal, a refusal and a program, each of the
-- two a constant, passes it, applied to `main`'s argument or not, and so does a `main` that needs
-- no task manager. A guard with an argument that Lean evaluates before the call and that starts a
-- task, with a program that is not a constant, or with a refusal that starts a task fails it.
run_cmd do
  let main := mkIdent `_root_.main
  let run := mkIdent `plantedRun
  let refuse := mkIdent `plantedRefuse
  let program : CommandElabM Unit := do
    elabCommand (← `(command|
      def $run (_ : List String) : IO UInt32 := do
        let _ ← IO.asTask (pure ())
        return 0))
    elabCommand (← `(command|
      def $refuse (_ : String) (_ : List String) : IO UInt32 := pure 3))
  let needs (refused : Option String) (call : String) : Bool :=
    refused.any (·.contains s!"calls {call}), and its `main` is not `Regula.TaskManager.guard` \
      applied")
  -- The guard itself starts a process when it starts its program again under Git isolation
  -- (`Regula.GitIsolation.restart`), so a `main` that calls it in another form is refused for
  -- whichever primitive the walk reaches first.
  let unguarded (refused : Option String) : Bool :=
    refused.any (·.contains "), and its `main` is not `Regula.TaskManager.guard` applied")
  let task ← taskRefusal (elabCommand (← `(command|
    def $main (_ : List String) : IO UInt32 := do
      let _ ← IO.asTask (pure ())
      return 0)))
  unless needs task "BaseIO.asTask" do
    throwError "the task-manager check accepted a program that starts a task: {task}"
  let promise ← taskRefusal (elabCommand (← `(command|
    def $main (_ : List String) : IO UInt32 := do
      let _ ← (IO.Promise.new : BaseIO (IO.Promise Nat))
      return 0)))
  unless needs promise "IO.Promise.new" do
    throwError "the task-manager check accepted a program that creates a promise: {promise}"
  let output ← taskRefusal (elabCommand (← `(command|
    def $main (_ : List String) : IO UInt32 := do
      let _ ← IO.Process.output { cmd := "true" }
      return 0)))
  unless needs output "BaseIO.asTask" || needs output "IO.Process.spawn" do
    throwError "the task-manager check accepted a program that captures a process's output: \
      {output}"
  let after ← taskRefusal do
    program
    elabCommand (← `(command|
      def $main (args : List String) : IO UInt32 := do
        let code ← Regula.TaskManager.guard "planted" $refuse (fun _ => pure 0) args
        let _ ← IO.asTask (pure ())
        return code))
  unless unguarded after do
    throwError "the task-manager check accepted a program that starts a task after the guard: \
      {after}"
  if let some refused ← taskRefusal do
      program
      elabCommand (← `(command|
        def $main : List String → IO UInt32 := Regula.TaskManager.guard "planted" $refuse $run))
    then
    throwError "the task-manager check refused a program that starts through the guard: {refused}"
  if let some refused ← taskRefusal do
      program
      elabCommand (← `(command|
        def $main (args : List String) : IO UInt32 :=
          Regula.TaskManager.guard "planted" $refuse $run args))
    then
    throwError "the task-manager check refused a program whose main applies the guard to its \
      argument: {refused}"
  if let some refused ← taskRefusal (elabCommand (← `(command|
      def $main (_ : List String) : IO UInt32 := do
        IO.println "planted"
        return 0))) then
    throwError "the task-manager check refused a program that needs no task manager: {refused}"
  -- Lean evaluates the program name before it calls the guard, so this task starts first.
  let eager ← taskRefusal do
    program
    elabCommand (← `(command|
      def $main (args : List String) : IO UInt32 :=
        Regula.TaskManager.guard (Task.spawn fun _ => String.intercalate "," args).get $refuse
          $run args))
  unless needs eager "Task.spawn" do
    throwError "the task-manager check accepted a guard with an argument that starts a task \
      before the call: {eager}"
  let lambda ← taskRefusal do
    program
    elabCommand (← `(command|
      def $main : List String → IO UInt32 :=
        Regula.TaskManager.guard "planted" $refuse fun args => $run ("planted" :: args)))
  unless unguarded lambda do
    throwError "the task-manager check accepted a guard whose program is not a constant: {lambda}"
  let refusing ← taskRefusal do
    program
    let refuseTask := mkIdent `plantedRefuseTask
    elabCommand (← `(command|
      def $refuseTask (_ : String) (_ : List String) : IO UInt32 := do
        let _ ← IO.asTask (pure ())
        return 3))
    elabCommand (← `(command|
      def $main : List String → IO UInt32 := Regula.TaskManager.guard "planted" $refuseTask $run))
  unless refusing.any (·.contains "plantedRefuseTask of the program of") &&
      refusing.any (·.contains "calls BaseIO.asTask), and the guard runs it in a process without \
        a task manager or without Git isolation") do
    throwError "the task-manager check accepted a refusal that starts a task: {refusing}"

-- A declaration of another name bound to a C function that needs the task manager is found by
-- its binding, not by its name.
run_cmd do
  let main := mkIdent `_root_.main
  let waitAny := mkIdent `plantedWaitAny
  let bound ← taskRefusal do
    elabCommand (← `(command|
      @[extern "lean_io_wait_any"]
      opaque $waitAny (tasks : @& List (Task Nat)) : BaseIO Nat))
    elabCommand (← `(command|
      def $main (_ : List String) : IO UInt32 := do
        let _ ← ($waitAny [Task.pure 0])
        return 0))
  unless bound.any (·.contains "plantedWaitAny), and its `main`") do
    throwError "the task-manager check accepted a program that calls a declaration bound to \
      lean_io_wait_any: {bound}"

-- A `main` that starts a process with no task, a declaration of another name bound to the C
-- function that starts a process, and a refusal that starts a process each fail the check, since
-- a process started outside the guard inherits a Git environment that is not isolated. The same
-- start through the guard passes it, and an initializer that starts one fails it under the guard.
run_cmd do
  let main := mkIdent `_root_.main
  let run := mkIdent `plantedStart
  let refuse := mkIdent `plantedRefuse
  let program : CommandElabM Unit := do
    elabCommand (← `(command|
      def $run (_ : List String) : IO UInt32 := do
        let child ← IO.Process.spawn { cmd := "true" }
        child.wait))
    elabCommand (← `(command|
      def $refuse (_ : String) (_ : List String) : IO UInt32 := pure 3))
  let starts (refused : Option String) (call : String) : Bool :=
    refused.any (·.contains "starts a process (") && refused.any (·.contains call) &&
      refused.any (·.contains "calls IO.Process.spawn), and its `main` is not \
        `Regula.TaskManager.guard` applied")
  let spawn ← taskRefusal do
    program
    elabCommand (← `(command|
      def $main (args : List String) : IO UInt32 := $run args))
  unless starts spawn "plantedStart" do
    throwError "the task-manager check accepted a program that starts a process: {spawn}"
  if let some refused ← taskRefusal do
      program
      elabCommand (← `(command|
        def $main : List String → IO UInt32 := Regula.TaskManager.guard "planted" $refuse $run))
    then
    throwError "the task-manager check refused a program that starts a process through the guard: \
      {refused}"
  let spawnAs := mkIdent `plantedSpawn
  let bound ← taskRefusal do
    elabCommand (← `(command|
      @[extern "lean_io_process_spawn"]
      opaque $spawnAs (args : IO.Process.SpawnArgs) : IO (IO.Process.Child args.toStdioConfig)))
    elabCommand (← `(command|
      def $main (_ : List String) : IO UInt32 := do
        let child ← ($spawnAs { cmd := "true" })
        child.wait))
  unless bound.any (·.contains "plantedSpawn), and its `main`") do
    throwError "the task-manager check accepted a program that calls a declaration bound to \
      lean_io_process_spawn: {bound}"
  let refusing ← taskRefusal do
    program
    let refuseStart := mkIdent `plantedRefuseStart
    elabCommand (← `(command|
      def $refuseStart (_ : String) (_ : List String) : IO UInt32 := do
        let child ← IO.Process.spawn { cmd := "true" }
        child.wait))
    elabCommand (← `(command|
      def $main : List String → IO UInt32 := Regula.TaskManager.guard "planted" $refuseStart $run))
  unless refusing.any (·.contains "plantedRefuseStart of the program of") &&
      refusing.any (·.contains "calls IO.Process.spawn), and the guard runs it in a process \
        without a task manager or without Git isolation") do
    throwError "the task-manager check accepted a refusal that starts a process: {refusing}"
  let initStart := mkIdent `plantedInitStart
  let initialized ← taskRefusal do
    program
    elabCommand (← `(command|
      def $initStart : IO Unit := do
        let child ← IO.Process.spawn { cmd := "true" }
        discard child.wait))
    elabCommand (← `(command| initialize $initStart:ident))
    elabCommand (← `(command|
      def $main : List String → IO UInt32 := Regula.TaskManager.guard "planted" $refuse $run))
  let before (refused : Option String) (caller : String) : Bool :=
    refused.any (·.contains "the code that initializes the modules of the program of") &&
      refused.any (·.contains caller) &&
      refused.any (·.contains "calls IO.Process.spawn), and it runs before `main`")
  unless before initialized "plantedInitStart" do
    throwError "the task-manager check accepted a guarded program with an initializer that \
      starts a process: {initialized}"
  let evaluated := mkIdent `plantedEvaluated
  let valued ← taskRefusal do
    program
    elabCommand (← `(command|
      unsafe def $evaluated : UInt32 :=
        match unsafeIO (IO.Process.spawn { cmd := "true" } >>= fun child => child.wait) with
        | .ok code => code
        | .error _ => 0))
    elabCommand (← `(command|
      def $main : List String → IO UInt32 := Regula.TaskManager.guard "planted" $refuse $run))
  unless before valued "plantedEvaluated" do
    throwError "the task-manager check accepted a guarded program with an unreferenced \
      definition with no parameter whose value starts a process: {valued}"
  let held := mkIdent `plantedHeld
  if let some refused ← taskRefusal do
      program
      elabCommand (← `(command|
        def $held : Nat × (List String → IO UInt32) := (0, $run)))
      elabCommand (← `(command|
        def $main : List String → IO UInt32 := Regula.TaskManager.guard "planted" $refuse $run))
    then
    throwError "the task-manager check refused a guarded program with a definition with no \
      parameter that only holds a closure that starts a process: {refused}"

-- A traversal of `Regula.TaskManagerCheck.doesMore` that stops at its bound leaves every root to
-- inspect. The roots are a declaration that applies thirty pure declarations and one that applies a
-- declaration that starts a process. At some bound the backward traversal stops before it reaches
-- the starting root, which a cut-off would drop. At each bound that root is still to inspect, and
-- with no bound the traversal finishes and leaves the pure root out.
run_cmd withoutModifyingEnv do
  let current ← getCurrNamespace
  let n := mkIdent `n
  let mut sum ← `(0)
  for index in [:30] do
    let leaf := mkIdent (Name.mkSimple s!"plantedLeaf{index}")
    elabCommand (← `(command|
      @[noinline] def $leaf ($n : Nat) : Nat := $n * $(Syntax.mkNumLit (toString (index + 2)))))
    sum ← `($sum + $leaf $n)
  let wide := mkIdent `plantedWide
  let spawning := mkIdent `plantedSpawning
  let start := mkIdent `plantedStarting
  elabCommand (← `(command| @[noinline] def $wide ($n : Nat) : Nat := $sum))
  elabCommand (← `(command|
    @[noinline] def $spawning (_ : Unit) : IO UInt32 := do
      let child ← IO.Process.spawn { cmd := "true" }
      child.wait))
  elabCommand (← `(command|
    @[noinline] def $start (unit : Unit) : IO UInt32 := $spawning unit))
  let env ← getEnv
  let pure := current ++ `plantedWide
  let starting := current ++ `plantedStarting
  let roots := #[pure, starting]
  let complete := Regula.TaskManagerCheck.doesMore env roots Regula.TaskManagerCheck.valueExterns
  unless complete.complete && complete.found.contains starting &&
      !complete.found.contains pure do
    throwError "the traversal with no bound did not finish, missed the root that starts a \
      process or kept the pure root"
  let mut dropped := false
  for bound in [1:100] do
    let cut := Regula.TaskManagerCheck.doesMore env roots Regula.TaskManagerCheck.valueExterns
      bound
    unless cut.inspects starting && cut.inspects pure == !cut.complete do
      throwError "at bound {bound} the traversal left the root that starts a process or kept the \
        pure root uninspected"
    dropped := dropped || (!cut.complete && !cut.found.contains starting)
  unless dropped do
    throwError "no bound stopped the traversal before it reached the root that starts a process, \
      so this control does not exercise the cut-off"

end Regula.ProgramCheck.Controls
