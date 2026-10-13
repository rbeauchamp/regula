import Regula.Removal
import Regula.TaskManagerCheck
import Std.Async.Process
import Std.Async.System
import Std.Time.Zoned.Database.TZdb

/-! # Controls of the check that each program runs

A planted program whose `main` calls a removal primitive fails the check that each program of the
package runs at the end of its root module or of a module that imports it
(`Regula.Removal.checkProgram`), and the same program with its removal made by the filesystem
observer passes it. A planted declaration of this module with the filesystem observer's role
admits nothing, and the check refuses a program while one is declared outside `Regula.Filesystem`
(`Regula.Removal.foreignObservers`).

A planted program whose `main` starts a process or reads the environment outside `Regula.Process`
fails the same check: through `IO.Process.spawn`, a wrapper of `IO.Process.output`,
`IO.Process.run`, the PATH fallback of `Lean.findSysroot`, `IO.getEnv`, a public launcher of Lake
or Lean, a timezone read of `Std`, the public `Std` wrapper of each libuv environment binding, or
an `extern` of another name bound to the runtime's process start or to a libuv environment read.
So do such a read in a local module whose name starts with `Lake`, and a process observer's role
given in this module.
The same start through `Regula.Process.output` and the same read through `Regula.Process.readEnv`
pass it. These controls compile each program, and start no process and read no variable.

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
  unless foreign.any (·.contains "an observer's role is given outside its boundary module") do
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

/-- Compile this body as the planted global main, without executing it. These controls qualify
the compiler/reach boundary; they are not observations of a live spawned child. -/
def bodyRefusal (body : Term) (setup : CommandElabM Unit := pure ()) :
    CommandElabM (Option String) := withoutModifyingEnv do
  setup
  let value ← liftTermElabM do
    let value ← Term.elabTermEnsuringType body (mkApp (mkConst ``IO) (mkConst ``Unit))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars value
  refusal value

-- Each negative changes one route to the primitive. No child is executed by these compile-time
-- controls; the refusal must name the intended primitive, rather than merely fail compilation.
run_cmd do
  for (label, body, primitive) in [
      ("spawn", ← `(do discard <| IO.Process.spawn { cmd := "planted" }), "IO.Process.spawn"),
      ("output wrapper", ← `(do
        let wrapped := IO.Process.output
        discard <| wrapped { cmd := "planted" }), "IO.Process.output"),
      ("run", ← `(do discard <| IO.Process.run { cmd := "planted" }), "IO.Process.run"),
      ("findSysroot PATH fallback", ← `(do discard <| Lean.findSysroot), "IO.Process.run"),
      ("environment", ← `(do discard <| IO.getEnv "PLANTED"), "IO.getEnv")] do
    let refused ← bodyRefusal body
    unless refused.any (·.contains s!"calls {primitive}") do
      throwError "{label}: the reach check did not refuse the intended primitive: {refused}"
  let routed ← bodyRefusal (← `(do
    discard <| Regula.Process.output (.toolchain .lean) { cmd := "", args := #["--version"] }))
  if let some refused := routed then
    throwError "the reach check refused a process through the observer: {refused}"
  let read ← bodyRefusal (← `(do discard <| Regula.Process.readEnv "PLANTED"))
  if let some refused := read then
    throwError "the reach check refused an environment read through the observer: {refused}"

-- Each public `Std` wrapper of a libuv environment binding reaches that binding, inlined or
-- through the wrapper, and the refusal names the binding. No variable or directory is read or
-- changed by these compile-time controls.
run_cmd do
  for (label, body, binding) in [
      ("getEnvVar", ← `(do discard <| Std.Async.System.getEnvVar "PLANTED"), "osGetenv"),
      ("setEnvVar", ← `(Std.Async.System.setEnvVar "PLANTED" "planted"), "osSetenv"),
      ("unsetEnvVar", ← `(Std.Async.System.unsetEnvVar "PLANTED"), "osUnsetenv"),
      ("getEnv", ← `(do discard <| Std.Async.System.getEnv), "osEnviron"),
      ("getHomeDir", ← `(do discard <| Std.Async.System.getHomeDir), "osHomedir"),
      ("getTmpDir", ← `(do discard <| Std.Async.System.getTmpDir), "osTmpdir"),
      ("getCwd", ← `(do discard <| Std.IO.Process.getCwd), "cwd"),
      ("setCwd", ← `(Std.IO.Process.setCwd (System.FilePath.mk "planted")), "chdir"),
      ("getExecutablePath", ← `(do discard <| Std.IO.Process.getExecutablePath), "exePath")] do
    let refused ← bodyRefusal body
    unless refused.any (·.contains s!"calls Std.Internal.UV.System.{binding}") do
      throwError "{label}: the reach check did not refuse the intended libuv binding: {refused}"

-- Public library launch APIs are boundaries too: a project caller cannot borrow an exemption
-- for a library's own starts. These controls inspect compiled calls without running a child.
run_cmd do
  for (label, body, primitive) in [
      ("Lake.proc", ← `(do discard <| (Lake.proc { cmd := "planted" }).toBaseIO), "Lake.proc"),
      ("Lake.captureProc", ← `(do discard <| (Lake.captureProc { cmd := "planted" }).toBaseIO), "Lake.captureProc'"),
      ("Lean solver launcher", ← `(do
        let env ← Lean.mkEmptyEnvironment
        discard <| (Lean.Meta.Tactic.BVDecide.External.runInterruptible 1 { cmd := "planted" }).toIO'
          { fileName := "planted", fileMap := Lean.FileMap.ofString "" } { env }),
        "Lean.Meta.Tactic.BVDecide.External.runInterruptible"),
      ("Std timezone file", ← `(do
        discard <| Std.Time.Database.TZdb.resolveLocalPath #[]),
        "Std.Time.Database.TZdb.resolveLocalPath"),
      ("Std timezone directories", ← `(do
        discard <| Std.Time.Database.TZdb.resolveZonesPaths Std.Time.Database.TZdb.default),
        "Std.Time.Database.TZdb.resolveZonesPaths")] do
    let refused ← bodyRefusal body
    unless refused.any (·.contains s!"calls {primitive}") do
      throwError "{label}: a project call borrowed a library-launch exemption: {refused}"

-- A local module name rooted at Lake still receives no imported-library exemption.
run_cmd do
  let refused ← bodyRefusal (← `(do discard <| IO.getEnv "PLANTED")) do
    modifyEnv (·.setMainModule `Lake.PlantedControl)
  unless refused.any (·.contains "calls IO.getEnv") do
    throwError "a locally authored Lake-rooted module borrowed a library exemption: {refused}"

-- An arbitrary extern name bound to the process runtime symbol is detected as the same boundary.
run_cmd do
  let setup := elabCommand (← `(command|
    @[extern "lean_io_process_spawn"] opaque plantedSpawn (args : IO.Process.SpawnArgs) :
      IO (IO.Process.Child args.toStdioConfig)))
  let refused ← bodyRefusal (← `(do discard <| plantedSpawn { cmd := "planted" })) setup
  unless refused.any (·.contains "calls Regula.ProgramCheck.Controls.plantedSpawn") do
    throwError "a differently named process extern escaped the reach check: {refused}"

-- An arbitrary extern name bound to a libuv environment symbol is detected as the same boundary.
run_cmd do
  let setup := elabCommand (← `(command|
    @[extern "lean_uv_os_getenv"] opaque plantedGetenv (name : @& String) : IO (Option String)))
  let refused ← bodyRefusal (← `(do discard <| plantedGetenv "PLANTED")) setup
  unless refused.any (·.contains "calls Regula.ProgramCheck.Controls.plantedGetenv") do
    throwError "a differently named environment extern escaped the reach check: {refused}"

-- A process observer role belongs only to Regula.Process, even if a foreign declaration is pure.
run_cmd do
  let setup := elabCommand (← `(command|
    @[regula_observer process] def plantedProcessObserver : IO Unit := pure ()))
  let refused ← bodyRefusal (← `(plantedProcessObserver)) setup
  unless refused.any (·.contains "an observer's role is given outside its boundary module") do
    throwError "a foreign process observer escaped the reach check: {refused}"

end Regula.ProgramCheck.Controls
