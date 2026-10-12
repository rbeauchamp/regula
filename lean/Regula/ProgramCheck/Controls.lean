import Regula.Removal

/-! # Controls of the check that each program runs

A planted program whose `main` calls a removal primitive fails the check that each program of the
package runs at the end of its root module or of a module that imports it
(`Regula.Removal.checkProgram`), and the same program with its removal made by the filesystem
observer passes it. A planted declaration of this module with the filesystem observer's role
admits nothing, and the check refuses a program while one is declared outside `Regula.Filesystem`
(`Regula.Removal.foreignObservers`). Each planted declaration is added for its control alone and
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

end Regula.ProgramCheck.Controls
