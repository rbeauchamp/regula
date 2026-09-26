import VersoManual
import RegulaPolicy.Pattern

/-! # Checked Lean examples of the standard

Verso code blocks for the standard's Lean examples. A `lean` block is one complete Lean module,
printed exactly as it is elaborated. Where the block is written, while the document is
elaborated, the `regula-example` helper (`RegulaExampleMain`) elaborates it in a fresh process
whose environment is exactly the block's own `import` header: nothing of the document, of
another example or of this extension is visible to it, and the document never imports the
example's modules (so the site executable never links them).

- `lean`: a positive example; elaboration must report no error and no warning.
- `lean (fails := "PATTERN")`: an expected rejection; elaboration must report an error, and one
  error message must match `PATTERN` in the restricted diagnostic language of standard §8.7,
  decided by the proved `RegulaPolicy.matchesPattern` (`matchesPattern_iff`).
- `lean +trustedCompiler`: a teaching example of a compiler-trusting mechanism; elaboration
  must report no error and no warning.
- `leanSketch`: Lean-like text displayed with a notice that it is not elaborated, for
  multi-file or placeholder sketches; `sh`, `text` and `toml` display non-Lean text.

This extension decides elaboration outcomes and renders the helper's highlighting. The
declaration, kernel-admission and axiom classification of every `lean` block is the
documentation fence audit's (`lake exe docFenceAudit`), which reads the same blocks from this
package's sources. The helper process, its search path and the file system are trusted.

The roles `{repo "PATH"}[text]` (a repository link whose path must exist) and
`{checklistRow}[ID]` (a checklist row identifier that is also its anchor) complete the
standard's markup.
-/

open Lean Elab
open scoped Lean.Doc.Syntax
open Verso ArgParse Doc Elab Genre.Manual
open SubVerso.Highlighting

namespace RegulaExample

/-- What a `lean` block's elaboration must show. -/
inductive Expectation where
  | positive
  | rejected (pattern : String)
  | trustedCompiler
  deriving Repr

structure Config where
  fails : Option String
  trustedCompiler : Bool

instance : FromArgs Config DocElabM where
  fromArgs := Config.mk <$> .named `fails .string true <*> .flag `trustedCompiler false

private def Config.expectation : Config → DocElabM Expectation
  | { fails := none, trustedCompiler := false } => pure .positive
  | { fails := none, trustedCompiler := true } => pure .trustedCompiler
  | { fails := some pattern, trustedCompiler := false } => do
    unless decide (RegulaPolicy.PatternValid pattern) do
      throwError "invalid expected-diagnostic pattern {repr pattern}"
    pure (.rejected pattern)
  | { fails := some _, trustedCompiler := true } =>
    throwError "an example cannot both fail and demonstrate a trusted compiler mechanism"

/-- One message of an example's elaboration, as the helper reports it. -/
structure Reported where
  severity : String
  line : Nat
  column : Nat
  text : String
  deriving FromJson

/-- The helper executable, built by Lake before the standard's modules (`needs`). Lake runs
the document's elaboration in the website package directory. -/
def helperPath : IO System.FilePath := do
  let path := (← IO.currentDir) / ".lake" / "build" / "bin" / "regula-example"
  unless ← path.pathExists do
    throw <| IO.userError s!"example helper not built: {path}"
  return path

/-- Elaborate one example module in a fresh `regula-example` process: its messages and highlighting. -/
def runHelper (text : String) : IO (Array Reported × Json) := do
  let helper ← helperPath
  IO.FS.withTempFile fun handle path => do
    handle.putStr text
    handle.flush
    let out ← IO.Process.output { cmd := helper.toString, args := #[path.toString] }
    if out.exitCode != 0 then
      throw <| IO.userError s!"example helper failed ({out.exitCode}): {out.stderr}"
    let json ← IO.ofExcept (Json.parse out.stdout)
    return (← IO.ofExcept (json.getObjValAs? (Array Reported) "messages"), ← IO.ofExcept (json.getObjVal? "code"))

/-- Elaborate one example where it is written (see `runHelper`), check the outcome against
`expectation`, and render the helper's highlighting. -/
def elabExample (expectation : Expectation) (str : StrLit) : DocElabM Term := do
  let text := str.getString
  let (messages, code) ← runHelper text
  let some start := str.raw.getPos? | throwErrorAt str "example has no source position"
  let firstLine := (← getFileMap).toPosition start |>.line
  let describe (ms : Array Reported) : String :=
    "\n".intercalate (ms.toList.map fun m =>
      s!"line {firstLine + m.line - 1}, column {m.column}: {m.severity}: {m.text}")
  let errors := messages.filter (·.severity == "error")
  let warnings := messages.filter (·.severity == "warning")
  match expectation with
  | .positive | .trustedCompiler =>
    unless errors.isEmpty && warnings.isEmpty do
      throwErrorAt str "example did not elaborate cleanly:\n{describe (errors ++ warnings)}"
  | .rejected pattern =>
    if errors.isEmpty then
      throwErrorAt str "expected a rejection matching {repr pattern}, but the example elaborated"
    unless errors.any (RegulaPolicy.matchesPattern pattern ·.text) do
      throwErrorAt str "no error message matches {repr pattern}:\n{describe errors}"
  let range := Syntax.getRange? str |>.map (← getFileMap).utf8RangeToLspRange
  ``(Verso.Doc.Block.other
      (Verso.Genre.Manual.InlineLean.Block.lean (hlFromExport! $(quote code.compress)) (some $(quote (← getFileName))) $(quote range))
      #[Verso.Doc.Block.code $(quote text)])

/-- A checked Lean example of the standard; see the module documentation. -/
@[code_block]
def lean : CodeBlockExpanderOf Config
  | config, str => do elabExample (← config.expectation) str

/-- Lean-like text shown but not elaborated: a multi-file or placeholder sketch. The rendered
block says so. -/
@[code_block]
def leanSketch : CodeBlockExpanderOf Unit
  | (), str => ``(Verso.Doc.Block.concat #[
      Verso.Doc.Block.para #[Verso.Doc.Inline.emph #[Verso.Doc.Inline.text "Sketch, not elaborated as Lean:"]],
      Verso.Doc.Block.code $(quote str.getString)])

/-- Shell commands (not Lean). -/
@[code_block]
def sh : CodeBlockExpanderOf Unit
  | (), str => ``(Verso.Doc.Block.code $(quote str.getString))

/-- Plain text (not Lean). -/
@[code_block]
def text : CodeBlockExpanderOf Unit
  | (), str => ``(Verso.Doc.Block.code $(quote str.getString))

/-- Lake TOML configuration (not Lean). -/
@[code_block]
def toml : CodeBlockExpanderOf Unit
  | (), str => ``(Verso.Doc.Block.code $(quote str.getString))

end RegulaExample

namespace RegulaExample

/-- The repository root: the parent of the website package, where Lake runs elaboration. -/
def repositoryRoot : IO System.FilePath := do
  return (← IO.currentDir) / ".."

/- A link to a repository file or directory, at the revision the site is built from
(`REGULA_SOURCE_REVISION`, else `main`). -/
inline_extension Inline.repo (path fragment : String) (directory : Bool) where
  data := Json.arr #[.str path, .str fragment, .bool directory]
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun go _ data content => do
      let .arr #[.str path, .str fragment, .bool directory] := data
        | Verso.reportError s!"Expected repository link data, got {data}"; content.mapM go
      let revision := (← IO.getEnv "REGULA_SOURCE_REVISION").getD "main"
      let kind := if directory then "tree" else "blob"
      let href := s!"https://github.com/rbeauchamp/regula/{kind}/{revision}/{path}" ++
        (if fragment.isEmpty then "" else "#" ++ fragment)
      return {{<a href={{href}}>{{← content.mapM go}}</a>}}

structure RepoArgs where
  target : String

instance : FromArgs RepoArgs DocElabM where
  fromArgs := RepoArgs.mk <$> .positional `target .string

/-- `{repo "PATH#FRAGMENT"}[text]` links a repository file; the path must exist. -/
@[role]
def repo : RoleExpanderOf RepoArgs
  | { target }, content => do
    let (path, fragment) := match target.splitOn "#" with
      | [p] => (p, "")
      | [p, f] => (p, f)
      | _ => (target, "")
    let file := (← repositoryRoot) / path
    unless ← file.pathExists do
      throwError "repository path does not exist: {path}"
    let directory ← file.isDir
    let content ← content.mapM elabInline
    ``(Verso.Doc.Inline.other (Inline.repo $(quote path) $(quote fragment) $(quote directory)) #[$content,*])

/- A checklist row identifier; its text is also the row's anchor. Duplicate identifiers are
refused when the document is traversed. -/
inline_extension Inline.row (row : String) where
  data := Json.str row
  traverse id data _ := do
    let .str row := data
      | Verso.reportError s!"Expected a row identifier, got {data}"; pure none
    let path ← (·.path) <$> read
    discard <| Verso.Genre.Manual.providedTag id path row
    pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ id data _ => do
      let .str row := data
        | Verso.reportError s!"Expected a row identifier, got {data}"; pure .empty
      match (← Verso.Doc.Html.HtmlT.state).externalTags[id]? with
      -- A row identifier is never broken across lines.
      | some link => return {{<code id={{link.htmlId.toString}} style="white-space:nowrap">{{row}}</code>}}
      | none => Verso.reportError s!"Untagged checklist row {row}"; return {{<code>{{row}}</code>}}

/-- `{checklistRow}[ID]`: a checklist row identifier, displayed as code and used as its anchor. -/
@[role]
def checklistRow : RoleExpanderOf Unit
  | (), content => do
    let #[inl] := content | throwError "a checklist row takes exactly its identifier"
    let `(inline| $s:str) := inl | throwErrorAt inl "a checklist row takes exactly its identifier"
    let row := s.getString
    unless row.length > 0 && row.all (fun c => c.isUpper || c.isDigit || c == '-') do
      throwError "not a checklist row identifier: {row}"
    ``(Verso.Doc.Inline.other (Inline.row $(quote row)) #[])

end RegulaExample

namespace RegulaExample

/- An empty element carrying the enclosing part's HTML id. Verso links a part that is its own
page as `route/#id` but gives the page heading no `id`; this block supplies it, derived from
the part itself. -/
block_extension Block.pageAnchor where
  data := .null
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ _ _ => do
      -- The document root is not linked by fragment (the standard is the root only when it is
      -- rendered alone, for its cross-reference check).
      let some header := (← read).traverseContext.headers.back?
        | pure .empty
      let some id := header.metadata.bind (·.id)
        | Verso.reportError s!"page anchor in untagged part {header.titleString}"; pure .empty
      let some link := (← read).traverseState.externalTags[id]?
        | Verso.reportError s!"page anchor in part without HTML id {header.titleString}"; pure .empty
      return {{<span id={{link.htmlId.toString}}></span>}}

/-- `{pageAnchor}`: the `id` of the enclosing part, for a part rendered as its own page. -/
@[block_command]
def pageAnchor : BlockCommandOf Unit
  | () => ``(Verso.Doc.Block.other Block.pageAnchor #[])

end RegulaExample
