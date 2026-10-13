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
manager. The same task started through `Regula.TaskManager.guard` passes it, and so does a program
that needs no task manager. Each planted declaration is added for its control alone and
removed after it, so this module declares no `main` and records no program. The self-audit builds
this module with the whole `Regula` library, and that build fails when a control does not give the
expected result. -/

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
-- task, fails the task-manager check, and so does one that runs the guard and then starts a task;
-- the same task started through the guard passes it, and so does a `main` that needs no task
-- manager.
run_cmd do
  let main := mkIdent `_root_.main
  let needs (refused : Option String) (call : String) : Bool :=
    refused.any (·.contains s!"calls {call}), and its `main` is not an application")
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
  let after ← taskRefusal (elabCommand (← `(command|
    def $main (args : List String) : IO UInt32 := do
      let code ← Regula.TaskManager.guard "planted" 3 (fun _ => pure 0) args
      let _ ← IO.asTask (pure ())
      return code)))
  unless needs after "BaseIO.asTask" do
    throwError "the task-manager check accepted a program that starts a task after the guard: \
      {after}"
  if let some refused ← taskRefusal (elabCommand (← `(command|
      def $main : List String → IO UInt32 := Regula.TaskManager.guard "planted" 3 fun _ => do
        let _ ← IO.asTask (pure ())
        return 0))) then
    throwError "the task-manager check refused a program that starts through the guard: {refused}"
  if let some refused ← taskRefusal (elabCommand (← `(command|
      def $main (_ : List String) : IO UInt32 := do
        IO.println "planted"
        return 0))) then
    throwError "the task-manager check refused a program that needs no task manager: {refused}"

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
