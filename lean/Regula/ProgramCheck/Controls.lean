import Regula.Removal

/-! # Controls of the check that each program runs

A planted program whose `main` calls a removal primitive fails the check that each program of the
package runs at the end of its root module or of a module that imports it
(`Regula.Removal.checkProgram`), and the same program with its removal made by the filesystem
observer passes it. Each planted `main` is added for its control alone and removed after it, so
this module declares no `main` and records no program. The first acceptance step builds this
module, and its build fails when a control does not give the expected result. -/

namespace Regula.ProgramCheck.Controls

open Lean Elab Command

/-- Whether `checkProgram` accepts the program whose `main` is `value`, of type `IO Unit`, added
to the environment for this control alone. -/
def accepts (value : Expr) : CommandElabM Bool :=
  withoutModifyingEnv do
    liftTermElabM do
      addAndCompile (.defnDecl {
        name := `main, levelParams := [], type := mkApp (mkConst ``IO) (mkConst ``Unit), value,
        hints := .opaque, safety := .safe })
    try
      Regula.Removal.checkProgram
      return true
    catch _ => return false

-- A `main` that removes a file with the library's primitive fails the check; one that removes it
-- with the observer passes it.
run_cmd do
  let path := mkStrLit "planted"
  let raw := mkApp (mkConst ``IO.FS.removeFile) (mkApp (mkConst ``System.FilePath.mk) path)
  if ← accepts raw then
    throwError "the check accepted a program whose main calls IO.FS.removeFile"
  let routed := mkApp2 (mkConst ``Regula.Filesystem.removePath) (mkConst ``Regula.Removal.Kind.file)
    (mkApp (mkConst ``System.FilePath.mk) path)
  unless ← accepts routed do
    throwError "the check refused a program whose main removes with the observer"

end Regula.ProgramCheck.Controls
