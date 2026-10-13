module

public import Lake
public meta import Lake
public import Lake.Load
public import Lake.CLI.Main
public import Lake.Util.MainM
public import Lake.Util.Cli
public import Lake.Util.IO
public import Lean.Elab.Frontend
public meta import Lean.Elab.Frontend
public meta import Lake.CLI.Main
meta import all Lake.CLI.Main
import all Lake.CLI.Main
open Lake DSL

/-! Tiny committed selection for the external Lake resolver control. -/

public section

package regula_selection_fixture where
  enableArtifactCache := false

require verso from "committed"

namespace Selection
run_cmd do
  let input := Lean.Parser.mkInputContext (include_str "LakeBuildConfig.inc")
    "Regula/LakeBuildConfig.inc"
  let result ← Lean.Elab.IO.processCommands input {} (← get)
  set result.commandState
run_cmd do
  let input := Lean.Parser.mkInputContext (include_str "RendererSelection.inc")
    "Regula/RendererSelection.inc"
  let result ← Lean.Elab.IO.processCommands input {} (← get)
  set result.commandState
end Selection

/-- External-loader baseline: record the package Lake actually selected before the guard. -/
target selectionBaseline pkg : Unit := do
  let workspace ← getWorkspace
  let some dependency := workspace.findPackageByName? `verso
    | error "selection baseline: Lake omitted verso"
  IO.FS.writeFile (pkg.dir / "selected-package") (← IO.FS.realPath dependency.dir).toString
  return Job.pure ()

/-- Use the actual build admission. Only a successful admission can write the action marker. -/
target selectionGuard pkg : Unit := do
  let workspace ← getWorkspace
  discard <| Selection.admitBuild (← Selection.buildConfig workspace) workspace
  IO.FS.writeFile (pkg.dir / "guard-entered") "guard entered"
  return Job.pure ()
