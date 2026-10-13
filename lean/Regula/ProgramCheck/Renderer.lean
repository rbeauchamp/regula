import Regula.Removal
import Regula.Checker.Workspace
import Lake.Load.Manifest

/-! # The renderer's committed dependency selection

The renderer runs the reach check only when its exempted library retains the committed manifest
selection. Lake resolves the manifest after its own selector inputs pass the shared refusal.
Build configuration, module naming and artifact loading remain trusted inputs. -/

namespace Regula.ProgramCheck.Renderer

open Lean System

/-- Require the renderer's sourced library to retain its committed manifest selection through
Lake's resolution. A workspace, LoadConfig or URL-map override makes the reach check incomplete.
Use the supplied actual build configuration; never manufacture empty override inputs.
Pass the resolved workspace to `action` only after selector admission.
Assumes: Lake v4.34.1 `Lake/Load/Manifest.lean:192-200,244-273` decodes the manifest and
`Lake/Load/Workspace.lean:62-67` resolves its packages. The committed build configuration,
package selection, module naming, artifact loading and pinned dependency contents remain trusted.
Lean v4.34.1 `Lean/Environment.lean:109-129,2225-2228` stores no compiled-as module identity. -/
def requireCommittedSelection (config : _root_.Lake.LoadConfig)
    (action : _root_.Lake.Workspace → IO Unit := fun _ => pure ()) : IO Unit := do
  try
    let manifestFile := config.wsDir / config.relManifestFile
    let before ← IO.FS.readFile manifestFile
    let some manifest ← _root_.Lake.Manifest.load? manifestFile
      | throw <| IO.userError "missing committed renderer manifest"
    let searchPath ← Lean.searchPathRef.get
    try
      Regula.Checker.Workspace.withManifestWorkspace config manifest #[`verso] action
      finally Lean.searchPathRef.set searchPath
    unless (← IO.FS.readFile manifestFile) == before do
      throw <| IO.userError "renderer manifest changed during resolution"
  catch error =>
    if (toString error).contains "observer reach check incomplete:" then throw error
    throw <| IO.userError s!"observer reach check incomplete: {error}"

/-- Check the renderer using the common reach/admission decision in its closed manifest case.
Assumes: Lean v4.34.1 `Lean/Elab/Command.lean:323-326` reports this command's source filename;
relative filenames use the compiler's working directory. Source location and directory stability
remain trusted compiler/filesystem observations. The committed Lake configuration runs the
selection target before renderer compilation; its generated record remains trusted build input.
A missing record, another workspace or changed manifest makes the check incomplete. -/
def check : Elab.Command.CommandElabM Unit := do
  let directory := (FilePath.mk (← getFileName)).parent.getD "."
  Elab.Command.liftIO do
    let file := Regula.Checker.Workspace.Selection.selectionFile directory
    let .ok text ← (IO.FS.readFile file).toBaseIO
      | throw <| IO.userError "observer reach check incomplete: actual Lake build selection is unavailable"
    let selection ← IO.ofExcept (Json.parse text >>= fromJson?)
    let selectedDirectory ← IO.FS.realPath
      (FilePath.mk (selection : Regula.Checker.Workspace.Selection.BuildSelection).directory)
    unless selectedDirectory == (← IO.FS.realPath directory) do
      throw <| IO.userError "observer reach check incomplete: build selection belongs to another workspace"
    let environment := (← Regula.Checker.Workspace.loadConfig directory false).lakeEnv
    let config := selection.configuration environment
    unless (← IO.FS.readFile (config.wsDir / config.relManifestFile)) == selection.manifestText do
      throw <| IO.userError "observer reach check incomplete: manifest differs from the admitted build selection"
    requireCommittedSelection config
  Regula.Removal.checkProgram

end Regula.ProgramCheck.Renderer
