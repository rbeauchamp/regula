import Lake.Util.Proc

/-! A standalone imported-module reach control. It executes no child or environment read. -/

namespace Regula.ProjectCaller

/-- An ordinary project module owns its environment action. -/
@[noinline] def read : IO Unit := do
  discard <| IO.getEnv "REGULA_PLANTED_LIBRARY"

/-- A project caller cannot borrow the imported library launcher's internal exemption. -/
@[noinline] def start : IO Unit := do
  discard <| (Lake.captureProc' { cmd := "planted" }).toBaseIO

end Regula.ProjectCaller

/-- An ordinary project's declaration name does not supply imported-library ownership. -/
@[noinline] def Std.Time.Database.TZdb.resolveLocalPath : IO Unit := do
  discard <| IO.getEnv "REGULA_PLANTED_LIBRARY"
