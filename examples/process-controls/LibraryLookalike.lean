import Lake.Util.Proc

/-! A standalone imported-module reach control. It executes no child or environment read. -/

namespace Lake.PlantedControl

/-- A project module under a library name still owns its environment action. -/
@[noinline] def read : IO Unit := do
  discard <| IO.getEnv "REGULA_PLANTED_LIBRARY"

/-- A project caller cannot borrow the imported library launcher's internal exemption. -/
@[noinline] def start : IO Unit := do
  discard <| (Lake.captureProc' { cmd := "planted" }).toBaseIO

end Lake.PlantedControl
