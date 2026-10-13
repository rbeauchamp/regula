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
Pass the actual resolved workspace to `action` only after selector admission.
Assumes: Lake v4.34.1 `Lake/Load/Manifest.lean:192-200,244-273` decodes the manifest and
`Lake/Load/Workspace.lean:62-67` resolves its packages. The committed build configuration,
package selection, module naming, artifact loading and pinned dependency contents remain trusted.
Lean v4.34.1 `Lean/Environment.lean:109-129,2225-2228` stores no compiled-as module identity. -/
def requireCommittedSelection (directory : FilePath)
    (action : _root_.Lake.Workspace → IO Unit := fun _ => pure ()) : IO Unit := do
  try
    let manifestFile := directory / _root_.Lake.defaultManifestFile
    let before ← IO.FS.readFile manifestFile
    let some manifest ← _root_.Lake.Manifest.load? manifestFile
      | throw <| IO.userError "missing committed renderer manifest"
    let searchPath ← Lean.searchPathRef.get
    try
      Regula.Checker.Workspace.withManifestWorkspace directory manifest #[`verso] action
      finally Lean.searchPathRef.set searchPath
    unless (← IO.FS.readFile manifestFile) == before do
      throw <| IO.userError "renderer manifest changed during resolution"
  catch error =>
    if (toString error).contains "observer reach check incomplete:" then throw error
    throw <| IO.userError s!"observer reach check incomplete: {error}"

/-- Check the renderer using the common reach/admission decision in its closed manifest case.
Assumes: Lean v4.34.1 `Lean/Elab/Command.lean:323-326` reports this command's source filename;
relative filenames use the compiler's working directory. Source location and directory stability
remain trusted compiler/filesystem observations. -/
def check : Elab.Command.CommandElabM Unit := do
  let directory := (FilePath.mk (← getFileName)).parent.getD "."
  Elab.Command.liftIO <| requireCommittedSelection directory
  Regula.Removal.checkProgram

end Regula.ProgramCheck.Renderer
