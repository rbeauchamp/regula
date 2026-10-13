import VersoManual
import RegulaRender.Options
import Regula.Filesystem

/-! # The destinations of a render through Verso's `manualMain` (issue 424)

`regula-site` and `regula-standard` render through Verso's `manualMain`, which writes the places
that its options name: the directories of pages below the output directory (`--output DIR`), the
saved state of a delayed render (`--delay-html-multi FILE`, `--delay-html-single FILE`) and the word
count (`--with-word-count FILE`). A run that stops before Verso writes them leaves an earlier run's
files in place, and a later reader accepts them: `--resume-html-multi FILE` renders from an earlier
saved state.

`begin` reads the options with Verso's own parser (`versoOptions`) and invalidates the destinations
of that reading (`Plan`) through Regula's filesystem observer (`Regula.Filesystem`). A run calls it
before anything that can fail and renders with the configuration that it returns, and the refusal
of a process without Lean's task manager (`refuse`) calls it in the run's place. So both take their
destinations from one parser and leave the same state: no saved state, no word count, and no
directory of pages, except the cross-reference table that a resumed render reads. -/

namespace RegulaRender

open System Verso.Genre.Manual

/-- The directories below the output directory where Verso writes TeX and pages.

Assumes: Verso `cad4b633`, `src/verso-manual/VersoManual.lean`: TeX is written in `tex` (426) and
the pages in `html-single` (748) and `html-multi` (840), and `emitHtml` names the same two
directories of pages (1062-1064). -/
def formatDirectories : List String := ["tex", "html-single", "html-multi"]

/-- The name of the cross-reference table in a directory of pages, which a resumed render reads.

Assumes: Verso `cad4b633`, `src/verso-manual/VersoManual.lean`: a render that is not resumed writes
`xref.json` into the directory of its pages before it writes them (1071, 1077, through
`emitXrefsJson`, 568-572), and the pages of every render read it there (795, 880), so a resumed
render reads the table that the delayed render left. -/
def crossReferences : String := "xref.json"

/-- What a render with a configuration writes and reads, besides the directories of pages. -/
structure Plan where
  /-- The output directory. -/
  root : FilePath
  /-- The files that the render writes whole: the saved states of delayed renders and the word
  count. -/
  files : List FilePath
  /-- The saved states that resumed renders read. -/
  inputs : List FilePath
  /-- The directories of pages, among `formatDirectories`, that resumed renders write and whose
  cross-reference table they read. -/
  resumed : List String

/-- What a render with `config` writes and reads, as Verso's `manualMain` does at the revision that
`website/lake-manifest.json` pins (`cad4b633`). A delayed mode of pages writes its saved state, a
resumed one reads its saved state and the cross-reference table of its directory, and a word count
is written to its file.

The match on `OutputConfig` names each of its fields, and the match on `EmitHtml` each of its
constructors, so a revision of Verso that adds one fails the build of this module.

Assumes: Verso `cad4b633`, `src/verso-manual/VersoManual.lean`: `.delay f` writes its saved state to
`f` (1078, through `SavedState.save`, 954-955), `.resumeFrom f` reads it from `f` (1080, through
`SavedState.load`, 957-958), and the word count is written to its file (1053-1056, through
`wordCount`, 728). -/
def plan (config : RenderConfig) : Plan :=
  match config.toOutputConfig with
  | ⟨root, _tex, single, multi, wordCount, _draft, _verbose⟩ =>
    let mode (how : EmitHtml) (dir : String) : List FilePath × List FilePath × List String :=
      match how with
      | .no | .immediately => ([], [], [])
      | .delay state => ([state], [], [])
      | .resumeFrom state => ([], [state], [dir])
    let (singleFiles, singleInputs, singleResumed) := mode single "html-single"
    let (multiFiles, multiInputs, multiResumed) := mode multi "html-multi"
    { root, files := singleFiles ++ multiFiles ++ wordCount.toList,
      inputs := singleInputs ++ multiInputs, resumed := singleResumed ++ multiResumed }

/-- Stop, with the reason, unless each file that a render with `config` writes outside the
directories of pages is outside its output directory, and each extra file that it copies is below
them. A saved state or a word count in the output directory, and a saved state that a resumed render
reads there, are refused: the render removes the directories of pages there before it renders, so
such a file could be removed, or kept with stale pages beside it. An extra file whose destination is
absolute or has a `..` component is refused, since Verso joins it to a directory of pages
(`System.FilePath.join` keeps an absolute path as it is). A path is compared as
`Regula.Filesystem.ownPath` gives it, so a path with a `.` or `..` component or a symbolic link
among its components also stops it.

Assumes: Verso `cad4b633`, `src/verso-manual/VersoManual.lean`: the extra files are copied to
`dir.join dest` below a directory of pages (450 and 452 for TeX, 805 and 807 for single-page HTML,
874 and 876 for multi-page HTML). Every other file of a render is written below a directory of
pages: the search index, the files of the document's blocks for TeX (454), and the assets of its
blocks and of Verso's features (`-verso-data`, `HtmlAssets.writeFiles` in
`src/verso-manual/VersoManual/Html/Features.lean:348-354`). The document's blocks and Verso's
features give those names, which are trusted to be relative. The cache of remote cross-references (`src/multi-verso/MultiVerso.lean:580-597`) is
written only when `--remote-config` or a `verso-sources.json` names one; it holds the data of other
sites, which its own manifest dates, not a result of the render. Regula's configurations name one
extra file, `regula.css` (`siteConfig` in `website/Main.lean`), and no remote configuration. -/
def requireConfined (config : RenderConfig) : IO Unit := do
  let p := plan config
  let root := (← Regula.Filesystem.ownPath p.root).components
  for path in p.files ++ p.inputs do
    if root.isPrefixOf (← Regula.Filesystem.ownPath path).components then
      throw <| IO.userError s!"{path} is in the output directory {p.root}: a saved state or a word \
        count there is refused, since the render removes the directories of pages there first"
  for (_, destination) in config.extraFiles ++ config.extraFilesHtml ++ config.extraFilesTeX do
    let destination := FilePath.mk destination
    if destination.isAbsolute || destination.components.contains ".." then
      throw <| IO.userError s!"the extra file {destination} is absolute or has a `..` component, so \
        Verso would write it outside the directories of pages"

/-- Remove the directory of pages `dir` below the output directory `root` through Regula's
filesystem observer, or, when a resumed render writes it (`resumed`), each of its entries but the
cross-reference table that the render reads (`crossReferences`). A relative path is taken below the
real working directory, and a `.` or `..` component or a symbolic link among the components of the
path stops it before it removes anything (`Regula.Filesystem.ownPath`). Each removal acts only on
an entry at its own place (`Regula.Filesystem.observer_removeOwn`, `observer_removeFound`), so it
never follows a link out of the output directory. -/
def invalidatePages (root : FilePath) (resumed : List String) (dir : String) : IO Unit := do
  unless resumed.contains dir do
    return ← Regula.Filesystem.removePath .directory (root / dir)
  let path ← Regula.Filesystem.ownPath (root / dir)
  Regula.Filesystem.requireOwnDirectory path
  unless ← path.isDir do return
  for entry in ← path.readDir do
    unless entry.fileName == crossReferences do
      Regula.Filesystem.removeFound entry.path

/-- The configuration of a render of a program whose own configuration is `config`, on its
command-line options `args`, read with Verso's own parser (`versoOptions`), after the destinations of
that configuration are invalidated: each of its `formatDirectories` below the output directory,
whichever modes the options select (`invalidatePages`), and each file that it writes whole
(`Plan.files`). It first requires them to be confined (`requireConfined`), so it removes nothing
when it refuses them. A run calls it before anything that can fail and passes the result to
`manualMain` with no options, which renders with exactly this configuration. Options that Verso's
parser refuses name no destination that the parser gives, and `manualMain` writes nothing for them:
it parses them before it writes anything.

Assumes: Verso `cad4b633`, `src/verso-manual/VersoManual.lean`: `manualMain` parses its options
(1043) before it writes anything, and its parser returns its configuration unchanged on no options
(1036). -/
def begin (config : RenderConfig) (args : List String) : IO RenderConfig := do
  let config ← versoOptions config args
  requireConfined config
  let p := plan config
  for dir in formatDirectories do invalidatePages p.root p.resumed dir
  for file in p.files do Regula.Filesystem.removePath .file file
  return config

/-- The refusal of the program `program`, whose configuration is `config`, in a process without
Lean's task manager (`Regula.TaskManager.guard`): it invalidates the destinations of `args` as a run
does first (`begin`), printing a line when it cannot, and returns 1. -/
def refuse (program : String) (config : RenderConfig) (args : List String) : IO UInt32 := do
  try discard <| begin config args
  catch error => IO.eprintln s!"{program}: could not invalidate the destinations of {args}: {error}"
  return 1

end RegulaRender
