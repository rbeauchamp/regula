import Lake.Build.Actions
import Lake.Config.InstallPath

/-! Raw native-tool fallback control, outside claimed programs. Lake chooses and starts its tool.
The caller proves the planted cc/ar image ran with its marker; an unrelated failure is insufficient. -/

/-- Observe Lake's actual missing-bundle fallback, with all native overrides absent. -/
def main (args : List String) : IO UInt32 := do
  let [installation, operation, directory] := args
    | throw <| IO.userError "native fallback control requires installation, operation and directory"
  let installation ← Lake.LeanInstall.get installation (collocated := true)
  let directory := System.FilePath.mk directory
  unless operation == "cc" || operation == "ar" do
    throw <| IO.userError "unknown native fallback control"
  let action := if operation == "cc" then
    Lake.compileO (directory / "control.o") (directory / "control.c")
      (compiler := installation.cc)
    else Lake.compileStaticLib (directory / "control.a") #[] (ar := installation.ar)
  let result ← Lake.LogIO.toBaseIO action
  return if result.isSome then 0 else 1
