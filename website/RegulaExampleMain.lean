import SubVerso.Compat
import SubVerso.Highlighting

/-! # Example elaboration helper

`regula-example FILE` elaborates the Lean module in `FILE` exactly as written: its own header
selects the imported environment, which contains nothing else, and its commands are elaborated
there in this fresh process under `exampleOptions`. It prints one JSON object with every message
(severity, one-based line and zero-based column within `FILE`, text) and the SubVerso
highlighting of the whole module. The standard's `lean` code blocks (`RegulaExample`) run it
where each block is written, so a document never imports an example's modules and the site
executable never links them.
Process, filesystem and search-path effects are trusted; the caller decides what the reported
outcome must be. -/

open Lean Elab Frontend
open SubVerso Highlighting

/-- The options every example elaborates under: automatic implicits off, as standard §8.1
recommends, and Lean's `linter.missingDocs` on, as standard §6.7 requires of a claimed library;
`pp.tagAppFns` only tags the highlighting. -/
def exampleOptions (opts : Options) : Options :=
  opts.setBool `autoImplicit false
    |>.setBool `relaxedAutoImplicit false
    |>.setBool `linter.missingDocs true
    |>.setBool `pp.tagAppFns true

private def severity : MessageSeverity → String
  | .error => "error"
  | .warning => "warning"
  | .information => "information"

unsafe def run (path : System.FilePath) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let contents ← IO.FS.readFile path
  let ictx := Parser.mkInputContext contents path.toString
  let (header, parserState, headerMessages) ← Parser.parseHeader ictx
  enableInitializersExecution
  let env ← importModules (headerToImports header) {} (trustLevel := 1024) (loadExts := true)
  let env := env.setMainModule `RegulaExample
  let commandState : Command.State := { env, maxRecDepth := defaultMaxRecDepth, messages := headerMessages }
  let commandState := { commandState with scopes := match commandState.scopes with
    | sc :: rest => { sc with opts := exampleOptions sc.opts } :: rest
    | [] => [] }
  let pctx : Frontend.Context := { inputCtx := ictx }
  let state ← IO.mkRef { commandState, parserState, cmdPos := parserState.pos }
  let result ← Compat.Frontend.processCommands header pctx state
  let result := result.updateLeading contents
  let hls ← (Frontend.runCommandElabM <| Command.liftTermElabM <| highlightFrontendResult result) pctx state
  let messages := Compat.messageLogArray result.headerMessages ++
    result.items.flatMap (fun item => Compat.messageLogArray item.messages)
  let messages ← messages.filter (!·.isSilent) |>.mapM fun m => do
    return Json.mkObj [("severity", .str (severity m.severity)), ("line", toJson m.pos.line),
      ("column", toJson m.pos.column), ("text", .str (← m.data.toString))]
  let code : Highlighted := hls.foldl (· ++ ·) .empty
  IO.println (Json.mkObj [("messages", .arr messages), ("code", code.exportCode.toJson)]).compress
  return 0

unsafe def main : List String → IO UInt32
  | [path] => try run path catch e => do IO.eprintln s!"regula-example: {e}"; return 2
  | _ => do IO.eprintln "usage: regula-example FILE"; return 1
