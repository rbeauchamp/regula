import Regula.Removal
import Regula.TaskManagerCheck
import Std.Tactic.BVDecide.LRAT.Parser

/-! # Controls of the check that each program runs

A planted program whose `main` calls a removal primitive fails the check that each program of the
package runs at the end of its root module or of a module that imports it
(`Regula.Removal.checkProgram`), and the same program with its removal made by the filesystem
observer passes it. A planted program that writes a file fails it too, and so does one that opens a
file to write it; one that opens a file to read it passes it. A planted declaration of this module
with the filesystem observer's role admits nothing, and the check refuses a program while one is
declared outside `Regula.Filesystem` (`Regula.Removal.foreignObservers`). A planted program whose
`main` refers to Lean's elaborator in its compiled code, without calling it, fails the check that
states that it does not elaborate, and passes the one that states that it does: the class is the
reachability of the compiled code, which a reference makes. A planted program whose `main` does
nothing and whose module's initializer calls a tactic's write
(`Std.Tactic.BVDecide.LRAT.dumpLRATProof`) is classified by that write in the same way, since the
check walks the initializers of the modules outside Lean's toolchain too
(`Regula.Removal.elaborationRoots`). Those modules are told apart by where Lean's search path found
each one (`Regula.Removal.toolchainModules`): among those of this build, the modules of Lean's
elaborator and of `bv_decide` are of the toolchain, and those of this package are not. A planted
program that does not elaborate fails the check that states that it does
(`Regula.Removal.elaborationRefusal`).

A planted program whose `main` starts a task, creates a promise or captures a process's output
fails the check that a compiled program needing Lean's task manager starts through the guard
(`Regula.TaskManagerCheck.checkProgram`), and so do one that runs the guard and then starts a task
and one that calls a declaration of another name bound to a C function that needs the task
manager. So do a guard with an argument that starts a task before the call, a guard whose program
is not a constant and a guard whose refusal starts a task. The same task started through the
closed form of `Regula.TaskManager.guard` passes it, applied to `main`'s argument or not, and so
does a program that needs no task manager. Each planted declaration is added for its control
alone and removed after it, so this module declares no `main` and records no program. The
self-audit builds this module with the whole `Regula` library, and that build fails when a control
does not give the expected result. -/

namespace Regula.ProgramCheck.Controls

open Lean Elab Command

/-- The refusal of `checkProgram` for the program whose `main` is `value`, of type `IO Unit`, added
to the environment for this control alone after `setup`; `none` when it accepts the program. -/
def refusal (value : Expr) (setup : CommandElabM Unit := pure ()) (elaborates : Bool := false) :
    CommandElabM (Option String) :=
  withoutModifyingEnv do
    setup
    liftTermElabM do
      addAndCompile (.defnDecl {
        name := `main, levelParams := [], type := mkApp (mkConst ``IO) (mkConst ``Unit), value,
        hints := .opaque, safety := .safe })
    try
      Regula.Removal.checkProgram (elaborates := elaborates)
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

-- A `main` that writes a file with the library's primitive fails the check, and so does one that
-- opens a file to write it; one that opens a file to read it passes it.
run_cmd do
  let plant (body : Term) : CommandElabM Unit := do
    elabCommand (← `(command| def $(mkIdent `plantedWrite) : IO Unit := $body))
  let planted := mkConst ((← getCurrNamespace) ++ `plantedWrite)
  for (body, primitive) in [((← `(IO.FS.writeFile "planted" "")), ``IO.FS.writeFile),
      ((← `(discard <| IO.FS.Handle.mk "planted" .write)), ``IO.FS.Handle.mk)] do
    let refused ← refusal planted (plant body)
    unless refused.any (·.contains s!"plantedWrite calls {primitive}") do
      throwError "the check accepted a program whose main calls {primitive} to write: {refused}"
  if let some refused ← refusal planted (plant (← `(discard <| IO.FS.Handle.mk "planted" .read)))
  then
    throwError "the check refused a program whose main opens a file to read it: {refused}"

-- A `main` whose compiled code refers to Lean's elaborator, storing it without calling it, fails the
-- check that states that it does not elaborate, and passes the one that states that it does: the
-- class is reachability in the compiled code, not a run of the elaborator. A `main` that does not
-- elaborate fails the check that states that it does.
run_cmd do
  let plant (body : Term) : CommandElabM Unit := do
    elabCommand (← `(command| def $(mkIdent `plantedElaboration) : IO Unit := $body))
  let planted := mkConst ((← getCurrNamespace) ++ `plantedElaboration)
  let elaborating ← `(discard <| IO.mkRef Lean.Elab.Command.elabCommand)
  let undeclared ← refusal planted (plant elaborating)
  unless undeclared.any (·.contains "reaches Lean's elaborator") do
    throwError "the check accepted a program that elaborates and states that it does not: \
      {undeclared}"
  if let some refused ← refusal planted (plant elaborating) (elaborates := true) then
    throwError "the check refused a program that elaborates and states that it does: {refused}"
  let idle ← refusal planted (plant (← `(pure ()))) (elaborates := true)
  unless idle.any (·.contains "reaches one of") do
    throwError "the check accepted a program that does not elaborate and states that it does: \
      {idle}"

-- The modules that Lean loaded from its toolchain's library, as the search path of this build finds
-- them, hold those of Lean's elaborator and of `bv_decide`, and none of this package.
run_cmd do
  let env ← getEnv
  let toolchain ← Regula.Removal.toolchainModules env (Regula.Removal.linked env env.mainModule)
  for module in [`Init.Prelude, `Lean.Elab.Command, `Std.Tactic.BVDecide.LRAT.Parser] do
    unless toolchain.contains module do
      throwError "{module} is not among the modules that Lean loaded from its toolchain's library"
  for module in [`Regula.Removal, `Regula.Filesystem, env.mainModule] do
    if toolchain.contains module then
      throwError "{module} is among the modules that Lean loaded from its toolchain's library"

-- A `main` that does nothing, in a module whose initializer calls a tactic's write, fails the check
-- that states that it does not elaborate, and passes the one that states that it does: the check
-- walks the initializers of the modules outside Lean's toolchain, where it finds the write.
run_cmd do
  let plant : CommandElabM Unit := do
    elabCommand (← `(command| def $(mkIdent `plantedIdle) : IO Unit := pure ()))
    elabCommand (← `(command|
      initialize Std.Tactic.BVDecide.LRAT.dumpLRATProof "planted" #[] true))
  let planted := mkConst ((← getCurrNamespace) ++ `plantedIdle)
  let undeclared ← refusal planted plant
  unless undeclared.any (·.contains "Std.Tactic.BVDecide.LRAT.dumpLRATProof") do
    throwError "the check accepted, as a program that does not elaborate, one whose initializer \
      calls a tactic's write: {undeclared}"
  if let some refused ← refusal planted plant (elaborates := true) then
    throwError "the check refused a program whose initializer calls a tactic's write and that \
      states that it elaborates: {refused}"

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
-- task, fails the task-manager check, and so does one that runs the guard and then starts a task.
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
  unless needs output "BaseIO.asTask" do
    throwError "the task-manager check accepted a program that captures a process's output: \
      {output}"
  let after ← taskRefusal do
    program
    elabCommand (← `(command|
      def $main (args : List String) : IO UInt32 := do
        let code ← Regula.TaskManager.guard "planted" $refuse (fun _ => pure 0) args
        let _ ← IO.asTask (pure ())
        return code))
  unless needs after "BaseIO.asTask" do
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
  unless needs lambda "BaseIO.asTask" do
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
        one") do
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

end Regula.ProgramCheck.Controls
