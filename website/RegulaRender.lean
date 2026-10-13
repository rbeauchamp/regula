import VersoManual
import Regula.Filesystem

/-! # The destinations of a render through Verso's `manualMain` (issue 424)

`regula-site` and `regula-standard` render through Verso's `manualMain`, which writes the places
that its options name: the pages below the output directory (`--output DIR`), the saved state of a
delayed render (`--delay-html-multi FILE`, `--delay-html-single FILE`) and the word count
(`--with-word-count FILE`). A run that stops before Verso writes them leaves an earlier run's files
in place, and a later reader accepts them: `--resume-html-multi FILE` renders from an earlier saved
state.

`begin` reads the options (`parse`) and invalidates each destination of that reading
(`destinations`) through Regula's filesystem observer (`Regula.Filesystem`). A run calls it before
anything that can fail and renders with the configuration that it returns, and the refusal of a
process without Lean's task manager (`refuse`) calls it in the run's place. So both take their
destinations from one reading and leave the same state: no saved state, no word count, and no pages
that the run writes.

Verso's own parser, `manualMain.opts`, is private to the module `VersoManual` at the revision that
`website/lake-manifest.json` pins (`cad4b633`): it is an auxiliary definition of `manualMain`
(`src/verso-manual/VersoManual.lean:994-1036`), and the module system makes it private, so code
outside that module cannot call it. `parse` is a copy of it, and the build of this module checks
the copy against Verso's parser on every short argument list (`checkParser`). -/

namespace RegulaRender

open System Verso.Genre.Manual

/-- The error of Verso's parser for an option `option` that needs a file name and has none. -/
private def missingFile (option : String) : IO.Error :=
  IO.userError s!"Missing filename for {option}"

/-- The error of Verso's parser for an option `option` whose file name `file` starts with `-`. -/
private def optionAsFile (option file : String) : IO.Error :=
  IO.userError s!"Expected filename after {option}, got option {file}"

/-- The configuration that the command-line options `args` give from `config`: a copy of Verso's
private parser `manualMain.opts`, clause for clause, which the build checks against it
(`checkParser`). An option that needs a file name refuses a missing one and one that starts with
`-`, and any other argument it does not know is refused.

Assumes: Verso `cad4b633`, `src/verso-manual/VersoManual.lean:994-1036` (`manualMain.opts`) and
`src/verso/Verso/CLI.lean:39-46` (`requireFilename`). -/
def parse (config : RenderConfig) : List String → IO RenderConfig
  | "--output" :: dir :: more => parse { config with destination := dir } more
  | "--depth" :: n :: more => parse { config with htmlDepth := n.toNat! } more
  | "--with-tex" :: more => parse { config with emitTeX := true } more
  | "--without-tex" :: more => parse { config with emitTeX := false } more
  | "--with-html-single" :: more => parse { config with emitHtmlSingle := .immediately } more
  | "--delay-html-single" :: [] => throw (missingFile "--delay-html-single")
  | "--delay-html-single" :: f :: more =>
    if f.startsWith "-" then throw (optionAsFile "--delay-html-single" f)
    else parse { config with emitHtmlSingle := .delay f } more
  | "--resume-html-single" :: [] => throw (missingFile "--resume-html-single")
  | "--resume-html-single" :: f :: more =>
    if f.startsWith "-" then throw (optionAsFile "--resume-html-single" f)
    else parse { config with emitHtmlSingle := .resumeFrom f } more
  | "--without-html-single" :: more => parse { config with emitHtmlSingle := .no } more
  | "--with-html-multi" :: more => parse { config with emitHtmlMulti := .immediately } more
  | "--delay-html-multi" :: [] => throw (missingFile "--delay-html-multi")
  | "--delay-html-multi" :: f :: more =>
    if f.startsWith "-" then throw (optionAsFile "--delay-html-multi" f)
    else parse { config with emitHtmlMulti := .delay f } more
  | "--resume-html-multi" :: [] => throw (missingFile "--resume-html-multi")
  | "--resume-html-multi" :: f :: more =>
    if f.startsWith "-" then throw (optionAsFile "--resume-html-multi" f)
    else parse { config with emitHtmlMulti := .resumeFrom f } more
  | "--without-html-multi" :: more => parse { config with emitHtmlMulti := .no } more
  | "--with-word-count" :: [] => throw (missingFile "--with-word-count")
  | "--with-word-count" :: file :: more =>
    if file.startsWith "-" then throw (optionAsFile "--with-word-count" file)
    else parse { config with wordCount := some file } more
  | "--without-word-count" :: more => parse { config with wordCount := none } more
  | "--draft" :: more => parse { config with draft := true } more
  | "--twoside" :: more => parse { config with twoside := true } more
  | "--verbose" :: more => parse { config with verbose := true } more
  | "--remote-config" :: [] => throw (missingFile "--remote-config")
  | "--remote-config" :: file :: more =>
    if file.startsWith "-" then throw (optionAsFile "--remote-config" file)
    else parse { config with remoteConfigFile := some file } more
  | other :: _ => throw (IO.userError s!"Unknown option {other}")
  | [] => pure config

/-- A place that a render writes. -/
inductive Destination where
  /-- A file that the render writes whole: the saved state of a delayed render or the word
  count. -/
  | file (path : FilePath)
  /-- A directory of pages below the output directory, with the paths that the render reads from
  it: the cross-reference table and the saved state of a delayed render that it resumes. -/
  | pages (path : FilePath) (reads : List FilePath)

/-- The places that a render with `config` writes, as Verso's `manualMain` writes them at the
revision that `website/lake-manifest.json` pins (`cad4b633`). Each mode of pages that is not `.no`
writes its own directory below `destination`; a delayed render also writes its saved state, and a
resumed one reads that state and the cross-reference table in its directory. With TeX, the render
writes the directory `tex`, and with a word count, that file.

The match on `OutputConfig` names each of its fields, and the match on `EmitHtml` each of its
constructors, so a revision of Verso that adds one fails the build of this module.

Assumes: Verso `cad4b633`, `src/verso-manual/VersoManual.lean`, at these lines.
- The pages of a mode are written below `destination` in `tex` (426), `html-single` (748) and
  `html-multi` (840), and `emitHtml` names the same two directories of pages (1062-1064).
- `.immediately` and `.delay` write the cross-reference table `xref.json` into that directory first
  (1071, 1077, through `emitXrefsJson`, 568-572); `.delay f` then writes its saved state to `f`
  (1078, through `SavedState.save`, 954-955).
- `.resumeFrom f` reads its saved state from `f` (1080, through `SavedState.load`, 957-958), and its
  pages read `xref.json` from their directory (795, 880) before they write it again.
- The word count is written to its file (1053-1056, through `wordCount`, 728).
- Every other file of a render is written below one of these directories: the extra files (874,
  876), the search index and the assets of the pages. The cache of remote cross-references
  (`src/multi-verso/MultiVerso.lean:580-597`) is written only when `--remote-config` or a
  `verso-sources.json` names one; it holds the data of other sites, which its own manifest dates,
  not a result of the render. -/
def destinations (config : RenderConfig) : List Destination :=
  match config.toOutputConfig with
  | ⟨root, tex, single, multi, wordCount, _draft, _verbose⟩ =>
    let pages (how : EmitHtml) (dir : String) : List Destination :=
      match how with
      | .no => []
      | .immediately => [.pages (root / dir) []]
      | .delay state => [.file state, .pages (root / dir) []]
      | .resumeFrom state => [.pages (root / dir) [root / dir / "xref.json", state]]
    (if tex then [.pages (root / "tex") []] else []) ++ pages single "html-single" ++
      pages multi "html-multi" ++ wordCount.toList.map .file

/-- Invalidate `destination` through Regula's filesystem observer: remove the file, and remove the
directory of pages or, when the render reads paths from it, each of its entries that is not one of
them and holds none of them. A relative path is taken below the real working directory, and a `.`
or `..` component or a symbolic link among the components of a path that it removes stops it
before it removes anything (`Regula.Filesystem.ownPath`). Each removal acts only on an entry at its
own place (`Regula.Filesystem.observer_removeOwn`, `observer_removeFound`), so it never follows a
link out of the path that the options name. A path that the render reads is compared as
`Regula.Filesystem.ownPath` gives it, or as written where that refuses it; a saved state in the
directory that the comparison does not find there is removed, and the resumed render then stops. -/
def Destination.invalidate : Destination → IO Unit
  | .file path => Regula.Filesystem.removePath .file path
  | .pages path [] => Regula.Filesystem.removePath .directory path
  | .pages path reads => do
    let path ← Regula.Filesystem.ownPath path
    Regula.Filesystem.requireOwnDirectory path
    unless ← path.isDir do return
    let reads ← reads.mapM fun read => do
      try return (← Regula.Filesystem.ownPath read).components catch _ => return read.components
    for entry in ← path.readDir do
      unless reads.any ((path / entry.fileName).components.isPrefixOf ·) do
        Regula.Filesystem.removeFound entry.path

/-- The configuration of a render of a program whose own configuration is `config`, on its
command-line options `args` (`parse`), after each destination of that configuration is
invalidated (`destinations`, `Destination.invalidate`). A run calls it before anything that can
fail and passes the result to `manualMain` with no options, which renders with exactly this
configuration. Options that `parse` refuses name no destination: it then throws before it removes
anything.

Assumes: Verso `cad4b633`, `src/verso-manual/VersoManual.lean`: `manualMain` renders with
`opts config options` (1043), and `opts` returns its configuration unchanged on no options (1036). -/
def begin (config : RenderConfig) (args : List String) : IO RenderConfig := do
  let config ← parse config args
  for destination in destinations config do destination.invalidate
  return config

/-- The refusal of the program `program`, whose configuration is `config`, in a process without
Lean's task manager (`Regula.TaskManager.guard`): it invalidates the destinations of `args` as a run
does first (`begin`), printing a line when it cannot, and returns 1. -/
def refuse (program : String) (config : RenderConfig) (args : List String) : IO UInt32 := do
  try discard <| begin config args
  catch error => IO.eprintln s!"{program}: could not invalidate the destinations of {args}: {error}"
  return 1

section Check

open Lean Elab Command

/-- The string literals in `e`. -/
private partial def stringLiterals : Expr → Array String
  | .lit (.strVal s) => #[s]
  | .app f a => stringLiterals f ++ stringLiterals a
  | .lam _ t b _ | .forallE _ t b _ => stringLiterals t ++ stringLiterals b
  | .letE _ t v b _ => stringLiterals t ++ stringLiterals v ++ stringLiterals b
  | .mdata _ e | .proj _ _ e => stringLiterals e
  | _ => #[]

/-- What a parser gives on `args` from `config`: the configuration, as `Config`'s JSON encoding,
or the text of the error that it throws. -/
private def outcome (parser : RenderConfig → List String → IO RenderConfig)
    (config : RenderConfig) (args : List String) : IO (Except String Json) := do
  try return .ok (toJson (← parser config args).toConfig)
  catch error => return .error (toString error)

/-- An outcome of `outcome`, as text. -/
private def describe : Except String Json → String
  | .ok config => config.compress
  | .error error => s!"the error {repr error}"

/-- A configuration that differs from the default one in every field that an option sets. -/
private def changedConfig : RenderConfig :=
  { destination := "start", htmlDepth := 7, emitTeX := true, emitHtmlSingle := .delay "single",
    emitHtmlMulti := .no, wordCount := some "count", draft := true, twoside := true,
    verbose := true, remoteConfigFile := some "remote" }

/-- Every list of at most `n` elements of `tokens`. -/
private def lists (tokens : List String) : Nat → List (List String)
  | 0 => [[]]
  | n + 1 => [] :: tokens.flatMap fun t => (lists tokens n).map (t :: ·)

/-- The check of `parse` against Verso's parser `manualMain.opts`, which the build of this module
runs: both must give the same configuration, or throw the same error, on every argument list of at
most three tokens, from the default configuration and from one that differs from it in every field
that an option sets. The tokens are each option of Verso's parser, the string literals that start
with `--` in its definition and the auxiliary definitions it uses, and two other arguments: `1`,
which is a file name and a number, and `-1`, which starts with `-`. A list in which `--depth` is
followed by an argument that is not a number is left out, since both parsers then stop with a panic
of `String.toNat!`. Verso's parser is found under its private name and run by Lean's evaluator.

It is a bounded check: it covers each option on its own, followed by every token, and every pair of
consecutive options with their arguments, not every longer list. -/
def checkParser : CommandElabM Unit := do
  let env ← getEnv
  let verso := mkPrivateNameCore `VersoManual ``manualMain ++ `opts
  let some info := env.find? verso
    | throwError "Verso's parser {verso} is not in the environment"
  let mut seen : NameSet := {}
  let mut pending := #[verso]
  let mut literals : Array String := #[]
  while h : pending.size > 0 do
    let name := pending.back
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some value := (env.find? name).bind (·.value?) | continue
    literals := literals ++ stringLiterals value
    pending := pending ++ value.getUsedConstants.filter (verso.isPrefixOf ·)
  let options := (literals.filter (·.startsWith "--")).toList.eraseDups
  if options.isEmpty then throwError "no option of Verso's parser {verso} was found"
  let versoParse ← liftTermElabM <|
    unsafe evalConst (RenderConfig → List String → IO RenderConfig) info.name
  let numeral (s : String) : Bool := !s.isEmpty && s.all Char.isDigit
  let mut count := 0
  for args in lists (options ++ ["1", "-1"]) 3 do
    if (args.zip args.tail).any fun (a, b) => a == "--depth" && !numeral b then continue
    for config in [({} : RenderConfig), changedConfig] do
      let ours ← outcome parse config args
      let theirs ← outcome versoParse config args
      let same := match ours, theirs with
        | .ok ours, .ok theirs => ours == theirs
        | .error ours, .error theirs => ours == theirs
        | _, _ => false
      unless same do
        throwError "RegulaRender.parse disagrees with Verso's parser on {args}: it gives \
          {describe ours}, and Verso's parser gives {describe theirs}"
      count := count + 1
  if count == 0 then throwError "the check of RegulaRender.parse compared no argument list"

end Check

run_cmd checkParser

end RegulaRender
