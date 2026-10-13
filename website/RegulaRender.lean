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

`begin` reads the options with Verso's own parser (`versoOptions`). It resolves each path of that
reading once, through Regula's filesystem observer (`Regula.Filesystem`), into a `Plan` of resolved
paths (`resolvePlan`). It admits the plan with one pure function (`refusal`), and an admitted plan
removes nothing that the render reads (`removals_admitted`). Then it removes what the plan names
(`invalidate`), and gives the configuration that Verso renders with, which it builds from the plan
alone (`Plan.configure`). A run calls it before anything that can fail, and the refusal of a process
without Lean's task manager (`refuse`) calls it in the run's place. So both take their destinations
from one parser and leave the same state: no saved state, no word count, and no directory of pages,
except the cross-reference table that a resumed render reads. -/

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
`emitXrefsJson`, 568-572), and the pages of every render read it there (795, 880) and write it again
(`emitXrefsJson`, 881), so a resumed render reads and writes the table that the delayed render
left. -/
def crossReferences : String := "xref.json"

/-! ## The plan of a render -/

/-- A resolved path: the names of the components of an absolute path below the root of the
filesystem, so `["a", "b"]` is `/a/b`. `resolve` gives only names that are not empty, `.` or `..`,
and `invalidate` lists only such names, so a list that is a prefix of another names a directory
that contains the other, or the same entry. -/
abbrev Names := List String

/-- The absolute path that `names` gives: the root of the filesystem followed by each name. -/
def pathOf (names : Names) : FilePath :=
  if names.isEmpty then ⟨FilePath.pathSeparator.toString⟩
  else ⟨String.join (names.map (FilePath.pathSeparator.toString ++ ·))⟩

/-- What a mode of pages does with a saved state, as Verso's `EmitHtml` does, at a resolved path. -/
inductive Mode where
  /-- No pages are written. -/
  | no
  /-- The pages are written in the run. -/
  | immediately
  /-- The saved state of the run is written to the file, and no pages. -/
  | delay (state : Names)
  /-- The pages are written from the saved state that the file holds. -/
  | resumeFrom (state : Names)

/-- What a render writes and reads, at resolved paths (`resolvePlan`). -/
structure Plan where
  /-- The output directory. -/
  root : Names
  /-- The mode of single-page HTML. -/
  single : Mode
  /-- The mode of multi-page HTML. -/
  multi : Mode
  /-- The file of the word count, if any. -/
  wordCount : Option Names

namespace Plan

/-- Each mode of pages, with its directory among `formatDirectories`. -/
def modes (p : Plan) : List (String × Mode) := [("html-single", p.single), ("html-multi", p.multi)]

/-- The files that the render writes whole: the saved states of delayed modes and the word count.

Assumes: Verso `cad4b633`, `src/verso-manual/VersoManual.lean`: `.delay f` writes its saved state to
`f` (1078, through `SavedState.save`, 954-955), and the word count is written to its file
(1053-1056, through `wordCount`, 728). -/
def files (p : Plan) : List Names :=
  p.modes.filterMap (fun | (_, .delay state) => some state | _ => none) ++ p.wordCount.toList

/-- The saved states that resumed modes read.

Assumes: Verso `cad4b633`, `src/verso-manual/VersoManual.lean`: `.resumeFrom f` reads its saved
state from `f` (1080, through `SavedState.load`, 957-958). -/
def inputs (p : Plan) : List Names :=
  p.modes.filterMap fun | (_, .resumeFrom state) => some state | _ => none

/-- The directories of pages, among `formatDirectories`, of resumed modes. -/
def resumed (p : Plan) : List String :=
  p.modes.filterMap fun | (dir, .resumeFrom _) => some dir | _ => none

/-- The cross-reference table of each resumed mode, which `invalidate` keeps (`crossReferences`). -/
def kept (p : Plan) : List Names := p.resumed.map fun dir => p.root ++ [dir, crossReferences]

/-- What the render reads, which no removal may reach: its saved states and its kept
cross-reference tables. -/
def reads (p : Plan) : List Names := p.inputs ++ p.kept

/-- The configuration `config` with the output directory, the modes of pages and the word count of
the plan, each at its resolved path (`pathOf`). -/
def configure (p : Plan) (config : RenderConfig) : RenderConfig :=
  let emit : Mode → EmitHtml
    | .no => .no
    | .immediately => .immediately
    | .delay state => .delay (pathOf state)
    | .resumeFrom state => .resumeFrom (pathOf state)
  { config with
    destination := pathOf p.root, emitHtmlSingle := emit p.single, emitHtmlMulti := emit p.multi,
    wordCount := p.wordCount.map pathOf }

end Plan

/-- A removal that `invalidate` makes, at a resolved path. -/
inductive Removal where
  /-- A directory of pages, removed whole (`Regula.Filesystem.removeOwn`). -/
  | directory (names : Names)
  /-- An entry of the directory of pages of a resumed mode, removed whole
  (`Regula.Filesystem.removeFound`). -/
  | entry (names : Names)
  /-- A file that the render writes whole (`Regula.Filesystem.removeOwn`). -/
  | file (names : Names)

/-- The resolved path of a removal. -/
def Removal.names : Removal → Names
  | .directory names | .entry names | .file names => names

/-- The removals of the plan `p`, where `listing dir` gives the names of the entries of the
directory of pages `dir` of a resumed mode: each directory of pages of a mode that is not resumed,
also one of a mode that writes no pages (`tex`), each entry of the directory of a resumed mode but
its cross-reference table, and each file that the render writes whole. -/
def removals (p : Plan) (listing : String → List String) : List Removal :=
  formatDirectories.flatMap (fun dir =>
    if p.resumed.contains dir then
      ((listing dir).filter (· != crossReferences)).map fun name => .entry (p.root ++ [dir, name])
    else [.directory (p.root ++ [dir])]) ++
  p.files.map .file

/-- Why the plan `p` is refused, or `none` when it is admitted. A file that the render writes whole
or reads is refused in its output directory, since the render removes the directories of pages
there first, and when it contains the output directory. A file that it writes whole is refused when
it is, or contains, a saved state that it reads, since the render removes the file before Verso
reads the state. -/
def refusal (p : Plan) : Option String :=
  match (p.files ++ p.inputs).find? (fun path => p.root.isPrefixOf path || path.isPrefixOf p.root),
      p.files.find? (fun file => p.reads.any file.isPrefixOf) with
  | some path, _ => some s!"{pathOf path} is in the output directory {pathOf p.root}, or contains \
    it: a saved state or a word count there is refused, since the render removes the directories \
    of pages there first"
  | none, some file => some s!"{pathOf file}, which the render writes, is or contains a file that \
    it reads, which it would remove before Verso reads it"
  | none, none => none

/-- What an admitted plan gives: each file that the render writes whole or reads is outside its
output directory and does not contain it, and each file that it writes whole neither is nor
contains a file that it reads. -/
theorem refusal_eq_none {p : Plan} (admitted : refusal p = none) :
    (∀ path ∈ p.files ++ p.inputs, ¬ p.root <+: path ∧ ¬ path <+: p.root) ∧
    ∀ file ∈ p.files, ∀ read ∈ p.reads, ¬ file <+: read := by
  unfold refusal at admitted
  split at admitted
  · cases admitted
  · cases admitted
  · rename_i outside apart
    simp only [List.find?_eq_none, Bool.or_eq_true, List.isPrefixOf_iff_prefix, not_or,
      List.any_eq_true, not_exists, not_and] at outside apart
    exact ⟨outside, fun file h read r => apart file h read r⟩

/-- In an admitted plan, each removal, whatever entries the directories of resumed modes list, lies
in a directory of pages below the output directory or is a file that the render writes whole, and
neither is nor contains a saved state that the render reads or a cross-reference table that it
keeps. -/
theorem removals_admitted {p : Plan} (admitted : refusal p = none) (listing : String → List String)
    {removal : Removal} (listed : removal ∈ removals p listing) :
    ((∃ dir ∈ formatDirectories, p.root ++ [dir] <+: removal.names) ∨
        ∃ file ∈ p.files, removal = .file file) ∧
      ∀ read ∈ p.reads, ¬ removal.names <+: read := by
  have ⟨outside, apart⟩ := refusal_eq_none admitted
  have notInput : ∀ rest, ∀ input ∈ p.inputs, ¬ p.root ++ rest <+: input := fun rest input h below =>
    (outside input (List.mem_append_right _ h)).1 ((List.prefix_append _ _).trans below)
  simp only [removals, List.mem_append, List.mem_flatMap, List.mem_map] at listed
  rcases listed with ⟨dir, isFormat, listed⟩ | ⟨file, isFile, rfl⟩
  · split at listed
    · simp only [List.mem_map, List.mem_filter] at listed
      obtain ⟨name, ⟨_, other⟩, rfl⟩ := listed
      refine ⟨Or.inl ⟨dir, isFormat, ⟨[name], by simp [Removal.names]⟩⟩, fun read isRead => ?_⟩
      simp only [Plan.reads, List.mem_append, Plan.kept, List.mem_map] at isRead
      rcases isRead with isInput | ⟨_, _, rfl⟩
      · exact notInput _ read isInput
      · intro below
        simp only [Removal.names, List.prefix_append_right_inj, List.cons_prefix_cons] at below
        simp [below.2.1, crossReferences] at other
    · rename_i resumes
      simp only [List.mem_singleton] at listed
      subst listed
      refine ⟨Or.inl ⟨dir, isFormat, List.prefix_refl _⟩, fun read isRead => ?_⟩
      simp only [Plan.reads, List.mem_append, Plan.kept, List.mem_map] at isRead
      rcases isRead with isInput | ⟨_, _, rfl⟩
      · exact notInput _ read isInput
      · intro below
        simp only [Removal.names, List.prefix_append_right_inj, List.cons_prefix_cons] at below
        rw [below.1] at resumes
        simp_all
  · exact ⟨Or.inr ⟨file, isFile, rfl⟩, apart file isFile⟩

/-! ## Resolution and removal -/

/-- The resolved path of `path`, the `what` of a render, after `leaf` checks what is there. An empty
path stops it. Its empty components are dropped, so `a/` names `a` and `a//b` names `a/b`, and then
`Regula.Filesystem.ownPath` takes a relative path below the real working directory and drops its
leading `.` components. That refuses any other `.` or `..` component, and a symbolic link among the
components above the leaf. `leaf` then checks the leaf at the resolved path, by a read that follows
no link there (`Regula.Filesystem.requireOwnFile`, `Regula.Filesystem.requireOwnDirectory`). -/
def resolve (what : String) (leaf : FilePath → IO Unit) (path : FilePath) : IO Names := do
  if path.toString.isEmpty then
    throw <| IO.userError s!"the {what} is an empty path: nothing was removed or rendered"
  let names := path.components.filter (!·.isEmpty)
  let own ← Regula.Filesystem.ownPath (if path.isAbsolute then pathOf names else mkFilePath names)
  let resolved := own.components.filter (!·.isEmpty)
  leaf (pathOf resolved)
  return resolved

/-- The plan of a render with `config`, each path of which is resolved once (`resolve`). The output
directory is a directory at its own place or nothing, and each saved state, the word count and each
kept cross-reference table is a file at its own place or nothing: a symbolic link at one of them,
or an entry of another kind, stops it.

The match on `OutputConfig` names each of its fields, and the match on `EmitHtml` each of its
constructors, so a revision of Verso that adds one fails the build of this module. -/
def resolvePlan (config : RenderConfig) : IO Plan := do
  let file := resolve (leaf := Regula.Filesystem.requireOwnFile)
  let mode (what : String) : EmitHtml → IO Mode
    | .no => pure .no
    | .immediately => pure .immediately
    | .delay state => .delay <$> file s!"saved state of {what}" state
    | .resumeFrom state => .resumeFrom <$> file s!"saved state of {what}" state
  match config.toOutputConfig with
  | ⟨root, _tex, single, multi, wordCount, _draft, _verbose⟩ =>
    let root ← resolve "output directory" Regula.Filesystem.requireOwnDirectory root
    let single ← mode "single-page HTML" single
    let multi ← mode "multi-page HTML" multi
    let wordCount ← wordCount.mapM (file "word count")
    let p : Plan := { root, single, multi, wordCount }
    for table in p.kept do discard <| file "cross-reference table" (pathOf table)
    return p

/-- Stop unless each extra file that a render with `config` copies is below a directory of pages.
An extra file whose destination is absolute or has a `..` component is refused, since Verso joins
it to a directory of pages (`System.FilePath.join` keeps an absolute path as it is).

Assumes: Verso `cad4b633`, `src/verso-manual/VersoManual.lean`: the extra files are copied to
`dir.join dest` below a directory of pages (450 and 452 for TeX, 805 and 807 for single-page HTML,
874 and 876 for multi-page HTML). Every other file of a render is written below a directory of
pages: the search index, the files of the document's blocks for TeX (454), and the assets of its
blocks and of Verso's features (`-verso-data`, `HtmlAssets.writeFiles` in
`src/verso-manual/VersoManual/Html/Features.lean:348-354`). The document's blocks and Verso's
features give those names, which are trusted to be relative. The cache of remote cross-references
(`src/multi-verso/MultiVerso.lean:580-597`) is written only when `--remote-config` or a
`verso-sources.json` names one; it holds the data of other sites, which its own manifest dates, not
a result of the render. Regula's configurations name one extra file, `regula.css` (`siteConfig` in
`website/Main.lean`), and no remote configuration. -/
def requireExtraFilesBelow (config : RenderConfig) : IO Unit := do
  for (_, destination) in config.extraFiles ++ config.extraFilesHtml ++ config.extraFilesTeX do
    let destination := FilePath.mk destination
    if destination.isAbsolute || destination.components.contains ".." then
      throw <| IO.userError s!"the extra file {destination} is absolute or has a `..` component, so \
        Verso would write it outside the directories of pages: nothing was removed or rendered"

/-- The names of the entries of the directory `dir`, which is a directory at its own place or
nothing (`Regula.Filesystem.requireOwnDirectory`): none when nothing is there. A name that is
empty, `.` or `..`, or that has a separator, stops it, so each name is one component. -/
def entries (dir : FilePath) : IO (List String) := do
  let found ← tryCatch dir.readDir fun
    | .noFileOrDirectory .. => pure #[]
    | error => throw error
  let names := found.toList.map (·.fileName)
  if let some name := names.find? fun name =>
      name.isEmpty || name == "." || name == ".." || name.any (FilePath.pathSeparators.contains ·)
  then throw <| IO.userError s!"{dir} lists an entry that is not a name: {repr name}"
  return names

/-- Remove what the admitted plan `p` names (`removals`), through Regula's filesystem observer. It
first requires each directory of pages to be a directory at its own place or nothing, and lists the
entries of each of a resumed mode (`entries`), so it stops before it removes anything when one is
not. Each removal acts only on an entry at its own place (`Regula.Filesystem.observer_removeOwn`,
`observer_removeFound`), so it never follows a link out of the output directory, and it removes
nothing that the render reads (`removals_admitted`). -/
def invalidate (p : Plan) : IO Unit := do
  let mut listed : List (String × List String) := []
  for dir in formatDirectories do
    let path := pathOf (p.root ++ [dir])
    Regula.Filesystem.requireOwnDirectory path
    if p.resumed.contains dir then listed := (dir, ← entries path) :: listed
  for removal in removals p fun dir => (listed.lookup dir).getD [] do
    match removal with
    | .directory names => Regula.Filesystem.removeOwn .directory (pathOf names)
    | .entry names => Regula.Filesystem.removeFound (pathOf names)
    | .file names => Regula.Filesystem.removeOwn .file (pathOf names)

/-- The configuration of a render of a program whose own configuration is `config`, on its
command-line options `args`, read with Verso's own parser (`versoOptions`), after the destinations of
that configuration are invalidated. It requires the extra files to be below the directories of pages
(`requireExtraFilesBelow`), resolves the plan (`resolvePlan`) and admits it (`refusal`), so it
removes nothing when one of them refuses. Then it removes what the plan names (`invalidate`) and
gives the configuration of the plan (`Plan.configure`). A run calls it before anything that can fail
and passes the result to `manualMain` with no options, which renders with exactly this
configuration. Options that Verso's parser refuses name no destination that the parser gives, and
`manualMain` writes nothing for them: it parses them before it writes anything.

Assumes: Verso `cad4b633`, `src/verso-manual/VersoManual.lean`: `manualMain` parses its options
(1043) before it writes anything, and its parser returns its configuration unchanged on no options
(1036). -/
def begin (config : RenderConfig) (args : List String) : IO RenderConfig := do
  let config ← versoOptions config args
  requireExtraFilesBelow config
  let p ← resolvePlan config
  if let some reason := refusal p then
    throw <| IO.userError s!"{reason}: nothing was removed or rendered"
  invalidate p
  return p.configure config

/-- The refusal of the program `program`, whose configuration is `config`, in a process without
Lean's task manager (`Regula.TaskManager.guard`): it invalidates the destinations of `args` as a run
does first (`begin`), printing a line when it cannot, and returns 1. -/
def refuse (program : String) (config : RenderConfig) (args : List String) : IO UInt32 := do
  try discard <| begin config args
  catch error => IO.eprintln s!"{program}: could not invalidate the destinations of {args}: {error}"
  return 1

end RegulaRender
