import Lake
import Lake.Load
import Regula.Checker.Common

/-!
In-process Lake workspace loading for checker discovery. A checked project
loads through Lake's own elaborated package model, so `lakefile.lean` and
`lakefile.toml` projects take the same path; no custom Lake facets or
source-format guesses participate. Load failures fail closed.
-/

namespace Regula.Checker.Workspace

open Lean System

private def detectEnvironment : IO _root_.Lake.Env := do
  let (elan?, lean?, lake?) ← _root_.Lake.findInstall?
  let some lean := lean?
    | throw <| IO.userError "lake-workspace-load-failed: cannot detect a Lean install"
  let lake := lake?.getD (_root_.Lake.LakeInstall.ofLean lean)
  match ← EIO.toIO' (_root_.Lake.Env.compute lake lean elan?) with
  | .ok env => return env
  | .error error => throw <| IO.userError s!"lake-workspace-load-failed: {error}"

/-- Load the workspace rooted at `repo` with Lake's loader and pass it to
`action`. The action runs in the same process, so it must not retain mutable
workspace state beyond its return value. With `scrubSearchPath`, the inherited
`LEAN_PATH` and `LEAN_SRC_PATH` are ignored, as for `scrubbedLeanPathEnv`. -/
def withRootWorkspace {α : Type} (repo : FilePath) (action : _root_.Lake.Workspace → IO α)
    (scrubSearchPath := false) : IO α := do
  let lakeEnv ← detectEnvironment
  let lakeEnv := if scrubSearchPath then { lakeEnv with initLeanPath := [], initLeanSrcPath := [] }
    else lakeEnv
  let config : _root_.Lake.LoadConfig := { lakeEnv, wsDir := ← IO.FS.realPath repo }
  let (ws?, log) ← (_root_.Lake.loadWorkspace config).captureLog
  match ws? with
  | some ws => action ws
  | none =>
      let messages := log.entries.map (·.message)
      throw <| IO.userError <|
        s!"lake-workspace-load-failed: {"; ".intercalate messages.toList}"

end Regula.Checker.Workspace
