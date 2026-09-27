import Lean

/-! # Frontend rejection diagnostics

Completed frontend rejection with typed message boundaries. -/

namespace Regula.Checker.Diagnostics

open Lean

/-- Unlike `pathExists`, preserve permission and other setup errors. -/
private def metadata? (path : System.FilePath) : IO (Option IO.FS.Metadata) := do
  match ← path.metadata.toBaseIO with
  | .ok data => return some data
  | .error (.noFileOrDirectory ..) => return none
  | .error error => throw error

/-- Lean's first matching module-root resolution, with setup errors retained. -/
private def sourceImportPath? (name : Name) : IO (Option System.FilePath) := do
  let root := name.getRoot.toString (escape := false)
  for directory in ← searchPathRef.get do
    let rootData ← metadata? (directory / root)
    let hasRoot ← if rootData.any (·.type == .dir) then pure true
      else pure (← metadata? ((directory / root).addExtension "olean")).isSome
    if hasRoot then
      let path := Lean.modToFilePath directory name "olean"
      return if (← metadata? path).isSome then some path else none
  return none

private def errorStrings (messages : MessageLog) : IO (Array String) := do
  let mut errors := #[]
  for message in messages.toList do
    if message.severity == .error && !message.isSilent then
      errors := errors.push (← message.toString)
  return errors

/-- Return effective errors only after completed source processing. Header
syntax and direct import mistakes are source errors. Other failed imports or
header setup are incomplete, even when Lean renders their exceptions as errors.
Initializers execute only in the actual frontend import, never in preflight. -/
unsafe def errors (moduleName : Name) (source : System.FilePath) : IO (Array String) := do
  Lean.enableInitializersExecution
  let text ← IO.FS.readFile source
  let inputCtx := Parser.mkInputContext text source.toString
  -- Parse directly once to distinguish source syntax errors from the language
  -- processor's catch-all conversion of unexpected header exceptions.
  let (_, _, parseMessages) ← Parser.parseHeader inputCtx
  let result ← if parseMessages.hasErrors then errorStrings parseMessages else do
    let sourceHeaderError ← IO.mkRef false
    let opts := Lean.Elab.async.set {} false
    let snapshot ← Lean.Language.Lean.process (fun stx => do
      let reject (message : String) := do
        sourceHeaderError.set true
        let messages := MessageLog.empty.add {
          fileName := source.toString
          pos := inputCtx.fileMap.toPosition stx.startPos
          severity := .error
          data := message }
        return .error ({
          diagnostics := ← Language.Snapshot.Diagnostics.ofMessageLog messages
          result? := none, metaSnap := default } : Language.Lean.HeaderProcessedSnapshot)
      -- A missing implicit Init is an installation failure, not a source error.
      for imp in stx.imports (includeInit := false) do
        let some path ← sourceImportPath? imp.module
          | do
            let message ← try
              let path ← findOLean imp.module
              pure s!"object file '{path}' of module {imp.module} does not exist"
            catch error => pure error.toString
            return ← reject message
        if stx.isModule then
          let (data, _) ← readModuleData path
          if !data.isModule then
            return ← reject s!"cannot import non-`module` {imp.module} from `module`"
      return .ok {
        imports := stx.imports
        isModule := stx.isModule
        mainModuleName := moduleName
        opts
        trustLevel := 0
        plugins := #[] })
      none { inputCtx with }
    let snapshots := (Lean.Language.toSnapshotTree snapshot).getAll
    let some parsed := snapshot.result?
      | throw <| IO.userError "diagnostic header setup did not complete"
    -- Force header completion before reading the flag set by its callback.
    -- An IO lift inside a Boolean expression would run before that pure wait.
    if parsed.processedSnap.get.result?.isNone then
      if !(← sourceHeaderError.get) then
        throw <| IO.userError "diagnostic import setup did not complete"
    let mut errors := #[]
    for snap in snapshots do
      errors := errors ++ (← errorStrings snap.diagnostics.msgLog)
    pure errors
  if (← IO.FS.readFile source) != text then
    throw <| IO.userError "source changed during diagnostic collection"
  return result

end Regula.Checker.Diagnostics
