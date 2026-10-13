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

`begin` reads the options with Verso's own parser (`versoOptions`). It resolves each path that the
configuration names one time, through Regula's filesystem observer (`Regula.Filesystem`), into a
`Plan` of resolved paths (`resolvePlan`). Then it observes the file at each removal and each read
by its identity (`Located`, `Regula.Filesystem.identities`), and admits the observation with one
pure function (`refusal`). An admitted observation removes no file that the render reads and no
real ancestor of one, by identity (`removals_admitted`), and writes no saved state or word count in
the output directory (`written_admitted`). Only then it removes what the plan names (`invalidate`),
and gives the configuration that Verso renders with, which it builds from the plan alone
(`Plan.configure`). A run calls it before anything that can fail, and the refusal of a process
without Lean's task manager (`refuse`) calls it in the run's place. So both take their destinations
from one parser and leave the same state: no saved state, no word count, and no directory of pages,
except the cross-reference table that a resumed render reads. -/

namespace RegulaRender

open System Verso.Genre.Manual
open Regula.Filesystem (FileId)

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
and `invalidate` lists only such names. -/
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
  /-- The files that Verso copies into each directory of pages, each with its destination there. -/
  extraFiles : List (Names × String)
  /-- The files that Verso copies into each directory of HTML pages, with their destinations. -/
  extraFilesHtml : List (Names × String)
  /-- The files that Verso copies into the directory of TeX, with their destinations. -/
  extraFilesTeX : List (Names × String)
  /-- The remote configuration that the options name, if any. -/
  remoteConfig : Option Names
  /-- When the options name no remote configuration: the file `verso-sources.json` in the working
  directory and in each of its ancestors, among which is the one that Verso reads, if any. -/
  defaultRemoteConfigs : List Names

namespace Plan

/-- Each mode of pages, with its directory among `formatDirectories`. -/
def modes (p : Plan) : List (String × Mode) := [("html-single", p.single), ("html-multi", p.multi)]

/-- The files that the render writes whole: the saved states of delayed modes and the word count.

Assumes: Verso `cad4b633`, `src/verso-manual/VersoManual.lean`: `.delay f` writes its saved state to
`f` (1078, through `SavedState.save`, 954-955), and the word count is written to its file
(1053-1056, through `wordCount`, 728). -/
def files (p : Plan) : List Names :=
  p.modes.filterMap (fun | (_, .delay state) => some state | _ => none) ++ p.wordCount.toList

/-- The saved states that resumed modes read. -/
def inputs (p : Plan) : List Names :=
  p.modes.filterMap fun | (_, .resumeFrom state) => some state | _ => none

/-- The directories of pages, among `formatDirectories`, of resumed modes. -/
def resumed (p : Plan) : List String :=
  p.modes.filterMap fun | (dir, .resumeFrom _) => some dir | _ => none

/-- The cross-reference table of each resumed mode, which `invalidate` keeps (`crossReferences`). -/
def kept (p : Plan) : List Names := p.resumed.map fun dir => p.root ++ [dir, crossReferences]

/-- The files that the render reads, which no removal may reach: the saved states of resumed modes,
their kept cross-reference tables, the copied files and the remote configuration.

Assumes: Verso `cad4b633`. These are the files that `manualMain` reads whose paths its
configuration gives. `src/verso-manual/VersoManual.lean`: `.resumeFrom f` reads its saved state
from `f` (1080, through `SavedState.load`, 957-958); a render reads the cross-reference table
(`crossReferences`); and the copied files are read at 450, 452, 805, 807, 874 and 876, through
`copyRecursively` (`src/verso/Verso/FS.lean:28-45`). `updateRemotes`
(`src/multi-verso/MultiVerso.lean:580-594`, called at 750 and 839) reads the remote configuration
that the options name, and otherwise `verso-sources.json` in the nearest ancestor of the working
directory that has a `lean-toolchain` (`findProject`, 384-395, and `defaultConfigFile`, 415).
`manualMain` also reads files whose paths its configuration does not give: the cache directory and
the files that the content of a remote configuration names (597-613 and 411). Regula's
configurations name no remote configuration, and the website package has no `verso-sources.json`.
The document and Verso's own assets are compiled into the program, and the files that the
elaboration of the document reads are read when it is compiled, not by `manualMain`. -/
def reads (p : Plan) : List Names :=
  p.inputs ++ p.kept ++ (p.extraFiles ++ p.extraFilesHtml ++ p.extraFilesTeX).map (·.1) ++
    p.remoteConfig.toList ++ p.defaultRemoteConfigs

/-- The configuration `config` with the output directory, the modes of pages, the word count, the
copied files and the remote configuration of the plan, each at its resolved path (`pathOf`). -/
def configure (p : Plan) (config : RenderConfig) : RenderConfig :=
  let emit : Mode → EmitHtml
    | .no => .no
    | .immediately => .immediately
    | .delay state => .delay (pathOf state)
    | .resumeFrom state => .resumeFrom (pathOf state)
  let copies (files : List (Names × String)) := files.map fun (source, dest) => (pathOf source, dest)
  { config with
    destination := pathOf p.root, emitHtmlSingle := emit p.single, emitHtmlMulti := emit p.multi,
    wordCount := p.wordCount.map pathOf, extraFiles := copies p.extraFiles,
    extraFilesHtml := copies p.extraFilesHtml, extraFilesTeX := copies p.extraFilesTeX,
    remoteConfigFile := p.remoteConfig.map pathOf }

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

/-- Each removal is in a directory of pages below the output directory, or is a file that the
render writes whole. -/
theorem removals_within (p : Plan) (listing : String → List String) {removal : Removal}
    (listed : removal ∈ removals p listing) :
    (∃ dir ∈ formatDirectories, p.root ++ [dir] <+: removal.names) ∨
      ∃ file ∈ p.files, removal = .file file := by
  simp only [removals, List.mem_append, List.mem_flatMap, List.mem_map] at listed
  rcases listed with ⟨dir, isFormat, listed⟩ | ⟨file, isFile, rfl⟩
  · split at listed
    · simp only [List.mem_map, List.mem_filter] at listed
      obtain ⟨name, _, rfl⟩ := listed
      exact Or.inl ⟨dir, isFormat, ⟨[name], by simp [Removal.names]⟩⟩
    · simp only [List.mem_singleton] at listed
      subst listed
      exact Or.inl ⟨dir, isFormat, List.prefix_refl _⟩
  · exact Or.inr ⟨file, isFile, rfl⟩

/-! ## Where a path is, by the identity of its files -/

/-- Where a resolved path is: the identity (`FileId`, the device and the number of a file on it) of
each of its prefixes that is present, and the names below them, which are absent. The prefixes of
a resolved path are present up to one of them and absent below it (`Regula.Filesystem.ownPath`),
and none that is present is a symbolic link, except the path itself when the check of its leaf
admits one. So the identities are those of the path's real ancestors. -/
structure Located where
  /-- The path, for a message. -/
  names : Names
  /-- The identity of each present prefix of the path: first the root of the filesystem, then the
  prefix with one more name each time. -/
  chain : List FileId
  /-- The names of the path below its last present prefix. -/
  rest : List String

/-- The identity of the last present prefix of a located path. -/
def Located.anchor (l : Located) : Option FileId := l.chain.getLast?

/-- The identity of the file at a located path, when it is present. -/
def Located.present (l : Located) : Option FileId := if l.rest.isEmpty then l.anchor else none

/-- Where the path `names` is, when `identity` gives the identity of each present path, and `none`
for an absent one (`identify`). -/
def locate (identity : Names → Option FileId) (names : Names) : Located :=
  let chain := (((List.range (names.length + 1)).map fun k => identity (names.take k)).takeWhile
    Option.isSome).filterMap id
  { names, chain, rest := names.drop (chain.length - 1) }

/-- Whether a volume could take the names `a` and `b` in one directory for one entry. For two ASCII
names, this is when they are equal ignoring ASCII case. For a name with another character, it is
always so, because a volume can ignore case or Unicode normalization. It compares the bytes of the
names, since the functions of Lean 4.34.1 on the characters of a string use `Classical.choice`.

Assumes: a volume takes two ASCII names in one directory for one entry only when they are equal
ignoring ASCII case. -/
def mayEqualName (a b : String) : Bool :=
  let ascii (s : String) := s.toUTF8.data.all (· < 128)
  let fold (s : String) :=
    s.toUTF8.data.map fun byte => if 65 ≤ byte && byte ≤ 90 then byte + 32 else byte
  if ascii a && ascii b then fold a == fold b else true

/-- Whether the located path `a` can be or contain the located path `b` after the render makes the
absent components of both. When `a` is present, that is when its identity is among those of the
present prefixes of `b`. When `a` is absent, `b` is absent too. Then `b` can be below `a` only when
the two have the last present prefix of one identity, and the absent names of `a` can be the first
absent names of `b` (`mayEqualName`). An unknown identity counts as possible. -/
def mayContain (a b : Located) : Bool :=
  match a.present with
  | some id => b.chain.contains id
  | none =>
    a.anchor.isNone || b.anchor.isNone ||
      (b.present.isNone && a.anchor == b.anchor && a.rest.length ≤ b.rest.length &&
        (a.rest.zip b.rest).all fun (x, y) => mayEqualName x y)

/-- What `mayContain a b = false` gives: when `a` is present, its identity is not that of `b` or of
a present prefix of `b`; when the two are absent with the last present prefix of one identity, the
absent names of `a` cannot be the first absent names of `b`. -/
theorem mayContain_eq_false {a b : Located} (apart : mayContain a b = false) :
    (∀ id, a.present = some id → id ∉ b.chain) ∧
      (a.present = none → b.present = none → a.anchor.isSome → a.anchor = b.anchor →
        ¬ (a.rest.length ≤ b.rest.length ∧ ∀ x ∈ a.rest.zip b.rest, mayEqualName x.1 x.2)) := by
  unfold mayContain at apart
  constructor
  · intro id present
    rw [present] at apart
    simpa [List.contains_iff_mem] using apart
  · intro absent absent' known same ⟨shorter, names⟩
    rw [absent] at apart
    have close : (b.present.isNone && a.anchor == b.anchor &&
        decide (a.rest.length ≤ b.rest.length) &&
        (a.rest.zip b.rest).all fun (x, y) => mayEqualName x y) = true := by
      simp only [absent', Option.isNone_none, same, beq_self_eq_true, decide_eq_true shorter,
        Bool.true_and, List.all_eq_true]
      exact fun x mem => names x mem
    simp [close] at apart

/-! ## Admission -/

/-- What `invalidate` observes before it removes anything: where the output directory, each file
that the render writes whole, each removal and each file that the render reads are. -/
structure Observation where
  /-- The output directory. -/
  root : Located
  /-- The files that the render writes whole (`Plan.files`). -/
  written : List Located
  /-- The removals (`removals`). -/
  removed : List Located
  /-- The files that the render reads (`Plan.reads`). -/
  reads : List Located

/-- The observation of the plan `p`, where `listing` gives the entries of the directories of pages
of resumed modes and `locate` where a path is. -/
def observation (p : Plan) (listing : String → List String) (locate : Names → Located) :
    Observation :=
  { root := locate p.root, written := p.files.map locate,
    removed := (removals p listing).map fun removal => locate removal.names,
    reads := p.reads.map locate }

/-- Why the observation `o` is refused, or `none` when it is admitted. A removal is refused when it
can be or contain a file that the render reads, or lie in one (`mayContain`). A saved state or a
word count is refused when it can be in the output directory or contain it. -/
def refusal (o : Observation) : Option String :=
  match o.removed.findSome? (fun r => (o.reads.find? fun q => mayContain r q || mayContain q r).map
      (r, ·)),
    o.written.find? (fun w => mayContain o.root w || mayContain w o.root) with
  | some (r, q), _ => some s!"{pathOf r.names}, which the render removes first, may be or contain \
    {pathOf q.names}, which it reads, or lie in it"
  | none, some w => some s!"{pathOf w.names}, a saved state or a word count, may be in the output \
    directory {pathOf o.root.names} or contain it, and the render removes the directories of pages \
    there first"
  | none, none => none

/-- What an admitted observation gives, by `mayContain`: no removal can be or contain a file that
the render reads, or lie in one, and no saved state or word count can be in the output directory
or contain it. -/
theorem refusal_eq_none {o : Observation} (admitted : refusal o = none) :
    (∀ r ∈ o.removed, ∀ q ∈ o.reads, mayContain r q = false ∧ mayContain q r = false) ∧
      ∀ w ∈ o.written, mayContain o.root w = false ∧ mayContain w o.root = false := by
  unfold refusal at admitted
  split at admitted
  · cases admitted
  · cases admitted
  · rename_i separate outside
    simp only [List.findSome?_eq_none_iff, Option.map_eq_none_iff, List.find?_eq_none,
      Bool.or_eq_true, not_or, Bool.not_eq_true] at separate outside
    exact ⟨separate, outside⟩

/-- In an admitted observation of the plan `p`, each removal is in a directory of pages below the
output directory or is a file that the render writes whole (`removals_within`). When it is present,
its identity is not that of a file that the render reads or of a present prefix of one. When such a
file is present, its identity is not that of the removal or of a present prefix of it. -/
theorem removals_admitted {p : Plan} {listing : String → List String} {locate : Names → Located}
    (admitted : refusal (observation p listing locate) = none) {removal : Removal}
    (listed : removal ∈ removals p listing) :
    ((∃ dir ∈ formatDirectories, p.root ++ [dir] <+: removal.names) ∨
        ∃ file ∈ p.files, removal = .file file) ∧
      ∀ read ∈ p.reads,
        (∀ id, (locate removal.names).present = some id → id ∉ (locate read).chain) ∧
          ∀ id, (locate read).present = some id → id ∉ (locate removal.names).chain := by
  refine ⟨removals_within p listing listed, fun read isRead => ?_⟩
  have ⟨apart, apart'⟩ := (refusal_eq_none admitted).1 (locate removal.names)
    (List.mem_map_of_mem listed) (locate read) (List.mem_map_of_mem isRead)
  exact ⟨(mayContain_eq_false apart).1, (mayContain_eq_false apart').1⟩

/-- In an admitted observation of the plan `p`, for each saved state or word count: when the output
directory is present, its identity is not that of the file or of a present prefix of it, and when
the file is present, its identity is not that of the output directory or of a present prefix of it.
When the two are absent below one present directory, the absent names of the output directory
cannot be the first absent names of the file. -/
theorem written_admitted {p : Plan} {listing : String → List String} {locate : Names → Located}
    (admitted : refusal (observation p listing locate) = none) {file : Names}
    (written : file ∈ p.files) :
    (∀ id, (locate p.root).present = some id → id ∉ (locate file).chain) ∧
      (∀ id, (locate file).present = some id → id ∉ (locate p.root).chain) ∧
      ((locate p.root).present = none → (locate file).present = none →
        (locate p.root).anchor.isSome → (locate p.root).anchor = (locate file).anchor →
        ¬ ((locate p.root).rest.length ≤ (locate file).rest.length ∧
          ∀ x ∈ (locate p.root).rest.zip (locate file).rest, mayEqualName x.1 x.2)) := by
  have ⟨inside, contains⟩ := (refusal_eq_none admitted).2 (locate file) (List.mem_map_of_mem written)
  exact ⟨(mayContain_eq_false inside).1, (mayContain_eq_false contains).1,
    (mayContain_eq_false inside).2⟩

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

/-- The plan of a render with `config`, each path of which is resolved one time (`resolve`). The
output directory is a directory at its own place or nothing. Each saved state, the word count, each
copied file, the remote configuration and each kept cross-reference table is a file at its own
place or nothing: a symbolic link at one of them, a directory or an entry of another kind stops it.
So Verso copies no directory, whose entries the plan does not resolve.

The match on `OutputConfig` names each of its fields, and the match on `EmitHtml` each of its
constructors, so a revision of Verso that adds one fails the build of this module. -/
def resolvePlan (config : RenderConfig) : IO Plan := do
  let file (what : String) (path : FilePath) := resolve what Regula.Filesystem.requireOwnFile path
  let mode (what : String) : EmitHtml → IO Mode
    | .no => pure .no
    | .immediately => pure .immediately
    | .delay state => .delay <$> file s!"saved state of {what}" state
    | .resumeFrom state => .resumeFrom <$> file s!"saved state of {what}" state
  let copies (files : List (FilePath × String)) : IO (List (Names × String)) :=
    files.mapM fun (source, dest) => return (← file "copied file" source, dest)
  match config.toOutputConfig with
  | ⟨root, _tex, single, multi, wordCount, _draft, _verbose⟩ =>
    let root ← resolve "output directory" Regula.Filesystem.requireOwnDirectory root
    let single ← mode "single-page HTML" single
    let multi ← mode "multi-page HTML" multi
    let wordCount ← wordCount.mapM (file "word count")
    let extraFiles ← copies config.extraFiles
    let extraFilesHtml ← copies config.extraFilesHtml
    let extraFilesTeX ← copies config.extraFilesTeX
    let remoteConfig ← config.remoteConfigFile.mapM (file "remote configuration")
    let defaultRemoteConfigs ← if remoteConfig.isSome then pure [] else do
      let working ← resolve "working directory" Regula.Filesystem.requireOwnDirectory "."
      (List.range (working.length + 1)).mapM fun k =>
        file "remote configuration" (pathOf (working.take k ++ ["verso-sources.json"]))
    let p : Plan :=
      { root, single, multi, wordCount, extraFiles, extraFilesHtml, extraFilesTeX, remoteConfig,
        defaultRemoteConfigs }
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
(`src/multi-verso/MultiVerso.lean:580-597`) is written only when a remote configuration exists; it
holds the data of other sites, which its own manifest dates, not a result of the render. -/
def requireExtraFilesBelow (config : RenderConfig) : IO Unit := do
  for (_, destination) in config.extraFiles ++ config.extraFilesHtml ++ config.extraFilesTeX do
    let destination := FilePath.mk destination
    if destination.isAbsolute || destination.components.contains ".." then
      throw <| IO.userError s!"the extra file {destination} is absolute or has a `..` component, so \
        Verso would write it outside the directories of pages: nothing was removed or rendered"

/-- The names of the entries of the directory `dir`, none when nothing is there. It first requires
`dir` to be nothing, or a directory at its own place whose entries are directories or files
(`Regula.Filesystem.requireNoLinkedEntries`). A name that is empty, `.` or `..`, or that has a
separator, stops it, so each name is one component. -/
def entries (dir : FilePath) : IO (List String) := do
  Regula.Filesystem.requireNoLinkedEntries dir
  let found ← tryCatch dir.readDir fun
    | .noFileOrDirectory .. => pure #[]
    | error => throw error
  let names := found.toList.map (·.fileName)
  if let some name := names.find? fun name =>
      name.isEmpty || name == "." || name == ".." || name.any (FilePath.pathSeparators.contains ·)
  then throw <| IO.userError s!"{dir} lists an entry that is not a name: {repr name}"
  return names

/-- The identity of each present prefix of each path of `paths`, by one read of
`Regula.Filesystem.identities`, as a function that gives `none` for an absent path. -/
def identify (paths : List Names) : IO (Names → Option FileId) := do
  let prefixes := (paths.flatMap fun names => (List.range (names.length + 1)).map names.take).eraseDups
  let table := prefixes.zip (← Regula.Filesystem.identities (prefixes.map pathOf))
  return fun names => (table.lookup names).join

/-- Remove what the plan `p` names (`removals`), through Regula's filesystem observer, after it
admits its observation (`refusal`). It first requires each directory of pages to be a directory at
its own place or nothing, lists the entries of each of a resumed mode (`entries`), and observes
the identity of each path that the observation names (`identify`, `locate`). So it stops before it
removes anything when one of these fails or the observation is refused. It removes exactly the
removals that it observed, so it removes no file that the render reads and no real ancestor of one
(`removals_admitted`). Each removal acts only on an entry at its own place
(`Regula.Filesystem.observer_removeOwn`, `observer_removeFound`), so it never follows a link out of
the output directory. -/
def invalidate (p : Plan) : IO Unit := do
  let mut listed : List (String × List String) := []
  for dir in formatDirectories do
    let path := pathOf (p.root ++ [dir])
    Regula.Filesystem.requireOwnDirectory path
    if p.resumed.contains dir then listed := (dir, ← entries path) :: listed
  let listing (dir : String) : List String := (listed.lookup dir).getD []
  let identity ← identify (p.root :: p.files ++ (removals p listing).map (·.names) ++ p.reads)
  if let some reason := refusal (observation p listing (locate identity)) then
    throw <| IO.userError s!"{reason}: nothing was removed or rendered"
  for removal in removals p listing do
    match removal with
    | .directory names => Regula.Filesystem.removeOwn .directory (pathOf names)
    | .entry names => Regula.Filesystem.removeFound (pathOf names)
    | .file names => Regula.Filesystem.removeOwn .file (pathOf names)

/-- The configuration of a render of a program whose own configuration is `config`, on its
command-line options `args`, read with Verso's own parser (`versoOptions`), after the destinations of
that configuration are invalidated. It requires the extra files to be below the directories of pages
(`requireExtraFilesBelow`), resolves the plan (`resolvePlan`), and then removes what the plan names
after it admits its observation (`invalidate`), so it removes nothing when one of them refuses. It
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
