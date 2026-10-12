import SubVerso.Compat
import SubVerso.Highlighting

/-! # Example elaboration helper

`regula-example FILE` elaborates the Lean module in `FILE` exactly as written: Lean's own header
processing (`processHeader`) imports the environment its header selects, at the visibility its
`module` keyword selects, which contains nothing else, and reports the header's diagnostics; its
commands are elaborated there in this fresh process under `exampleOptions`. As in Lean's own
frontend, a header error ends elaboration: the helper then reports the header's messages and the
unhighlighted text. It prints one JSON object with every message (severity, one-based line and
zero-based column within `FILE`, text) and the SubVerso highlighting of the whole module. The
standard's `lean` code blocks (`RegulaExample`) run it where each block is written, so a document
never imports an example's modules and the site executable never links them.
Process, filesystem and search-path effects are trusted, and so is the external SAT solver
`bv_decide` runs; the caller decides what the reported outcome must be. -/

open Lean Elab Frontend
open SubVerso Highlighting

/-- The options every example elaborates under: automatic implicits off, as standard §7.1
recommends, and Lean's `linter.missingDocs` on, as standard §6.7 requires of a claimed library;
`pp.tagAppFns` only tags the highlighting; `sat.solver` names `solver`, so `bv_decide` runs the
selected compiler's bundled CaDiCaL rather than one beside this helper or on `PATH`. An example's
own `set_option` still overrides each. -/
def exampleOptions (solver : System.FilePath) (opts : Options) : Options :=
  opts.setBool `autoImplicit false
    |>.setBool `relaxedAutoImplicit false
    |>.setBool `linter.missingDocs true
    |>.setBool `pp.tagAppFns true
    |>.set `sat.solver solver.toString

private def severity : MessageSeverity → String
  | .error => "error"
  | .warning => "warning"
  | .information => "information"

/-- Print the reported messages, without the silent ones, and the highlighting as one JSON
object. -/
private def report (messages : Array Message) (code : Highlighted) : IO Unit := do
  let messages ← messages.filter (!·.isSilent) |>.mapM fun m => do
    return Json.mkObj [("severity", .str (severity m.severity)), ("line", toJson m.pos.line),
      ("column", toJson m.pos.column), ("text", .str (← m.data.toString))]
  IO.println (Json.mkObj [("messages", .arr messages), ("code", code.exportCode.toJson)]).compress

unsafe def run (path : System.FilePath) : IO UInt32 := do
  let sysroot ← findSysroot
  initSearchPath sysroot
  let opts := exampleOptions
    (sysroot / "bin" / "cadical" |>.withExtension System.FilePath.exeExtension) {}
  let contents ← IO.FS.readFile path
  let ictx := Parser.mkInputContext contents path.toString
  let (header, parserState, headerMessages) ← Parser.parseHeader ictx
  if headerMessages.hasErrors then
    report (Compat.messageLogArray headerMessages) (.text contents)
    return 0
  enableInitializersExecution
  let (env, messages) ← processHeader header opts headerMessages ictx (trustLevel := 1024)
    (mainModule := `RegulaExample)
  if messages.hasErrors then
    report (Compat.messageLogArray messages) (.text contents)
    return 0
  let commandState := Command.mkState env messages opts
  let pctx : Frontend.Context := { inputCtx := ictx }
  let state ← IO.mkRef { commandState, parserState, cmdPos := parserState.pos }
  let result ← Compat.Frontend.processCommands header pctx state
  let result := result.updateLeading contents
  let hls ← (Frontend.runCommandElabM <| Command.liftTermElabM <| highlightFrontendResult result) pctx state
  report (Compat.messageLogArray result.headerMessages ++
      result.items.flatMap (fun item => Compat.messageLogArray item.messages))
    (hls.foldl (· ++ ·) .empty)
  return 0

unsafe def main : List String → IO UInt32
  | [path] => try run path catch e => do IO.eprintln s!"regula-example: {e}"; return 2
  | _ => do IO.eprintln "usage: regula-example FILE"; return 1
