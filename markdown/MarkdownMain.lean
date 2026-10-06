import RegulaMarkdown
import RegulaCore.ControlledProse

/-! Checks every Markdown document the repository tracks: for a rule ID in prose that is not a
link to its rule page (`Regula.Markdown.documentErrors`), and for the writing rules that a text
decides alone (`RegulaCore/ControlledProse.lean`, checks C1 to C9, with the baseline and its
ratchet). The documents are the files Git tracks below the repository root whose extension is
`md` or `markdown`, as `git ls-files` lists them; each is read from the working tree. The
documentation step of acceptance runs it (`lean/RegulaVerification.lean`).

Everything this program decides, it decides with a registered decision of `RegulaCore`: `parse`,
`untracked` and `adopt` for the vocabulary, `findings` (C1 to C8) through `tally` and `report`,
`Baseline.parse`, `gate` and `ratchet`. The rest is not proved: the list of tracked files and
the baseline of the base revision are Git's, the content of a file is the file system's, a
digest is `shasum`'s, and md4c's reading of a document is `Regula.Markdown.read`'s
(`RegulaMarkdown.lean`). -/

open Regula.Markdown Regula.Controlled

namespace Regula.Controlled.Run

/-- The file of the vocabulary, at the repository root. -/
def vocabularyFile : String := "CONTEXT.md"

/-- The file of the baseline, at the repository root. -/
def baselineFile : String := "prose-baseline.json"

/-- What the program was asked to do. -/
structure Options where
  /-- The repository root. -/
  root : System.FilePath
  /-- The `CONTEXT.md` of the package that the vocabulary names as shared. -/
  shared : Option System.FilePath := none
  /-- The revision whose merge base with `HEAD` is the base revision of the ratchet. -/
  base : String := "origin/main"
  /-- Write the baseline of the documents as they are instead of checking them. -/
  write : Bool := false
  /-- Print every finding of this document instead of checking the repository. -/
  list : Option String := none

/-- The options of the arguments `args`, if they are a root and known options. -/
def Options.parse : List String → Option Options
  | root :: rest =>
    let rec go (options : Options) : List String → Option Options
      | [] => some options
      | "--shared" :: path :: rest => go { options with shared := some path } rest
      | "--base" :: revision :: rest => go { options with base := revision } rest
      | "--write-baseline" :: rest => go { options with write := true } rest
      | "--list" :: path :: rest => go { options with list := some path } rest
      | _ => none
    if root.startsWith "--" then none else go { root } rest
  | [] => none

/-- Run `git` with `args` in `root`. -/
def git (root : System.FilePath) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd := "git", args, cwd := some root }

/-- The paths of the files Git tracks below `root`, relative to it. -/
def trackedFiles (root : System.FilePath) : IO (List String) := do
  let listed ← git root #["ls-files", "-z"]
  unless listed.exitCode == 0 do
    throw <| IO.userError s!"git ls-files failed in {root}: {listed.stderr}"
  return (listed.stdout.splitOn "\x00").filter (!·.isEmpty)

/-- One tracked Markdown document: its path, its text and md4c's reading of it. -/
structure Document where
  /-- The path, relative to the repository root. -/
  path : String
  /-- The text of the file in the working tree. -/
  source : String
  /-- md4c's reading of the text. -/
  reading : Reading

/-- The tracked Markdown documents among `tracked`, read from the working tree. -/
def documents (root : System.FilePath) (tracked : List String) : IO (List Document) :=
  (tracked.filter isMarkdown).mapM fun (path : String) => do
    let source ← IO.FS.readFile (root / path)
    return ⟨path, source, read source⟩

/-- A refusal of a vocabulary file as lines of output: the file, the line when there is one, the
check and the reason. -/
def vocabularyRefusals (file text : String) : List String :=
  (explain text).map fun (line, reason) =>
    match line with
    | some line => s!"{file}:{line}: C9: {reason}"
    | none => s!"{file}: C9: {reason}"

/-- The vocabulary of the repository: its `CONTEXT.md`, whose source paths are tracked files,
together with the `Shared` tables of the vocabulary it names, if it names one. -/
def loadVocabulary (options : Options) (tracked : List String) :
    IO (Except (List String) Vocabulary) := do
  unless tracked.contains vocabularyFile do
    return .error [s!"{vocabularyFile}: C9: Git tracks no {vocabularyFile} at the repository root"]
  let text ← IO.FS.readFile (options.root / vocabularyFile)
  let some own := parse text | return .error (vocabularyRefusals vocabularyFile text)
  let lines := text.splitOn "\n"
  let missing := (untracked tracked own).map fun path =>
    s!"{vocabularyFile}:{(lines.findIdx fun line => line.contains s!"`{path}`") + 1}: C9: the \
      source path `{path}` is not a tracked file"
  unless missing.isEmpty do return .error missing
  match own.draft.shared, options.shared with
  | none, none => return .ok own
  | none, some _ =>
    return .error [s!"{vocabularyFile}: C9: --shared was given, and the vocabulary names no \
      shared vocabulary"]
  | some package, none =>
    return .error [s!"{vocabularyFile}:5: C9: the vocabulary names the shared vocabulary \
      `{String.ofList package}`; give the {vocabularyFile} of that package with --shared"]
  | some _, some path =>
    let sharedText ← IO.FS.readFile path
    let some shared := parse sharedText
      | return .error (vocabularyRefusals path.toString sharedText)
    match adopt shared own with
    | some vocabulary => return .ok vocabulary
    | none =>
      return .error <|
        (if shared.draft.shared.isSome then
          [s!"{path}: C9: the shared vocabulary names a shared vocabulary itself"]
        else []) ++
        (shared.draft.adopt own.draft).defects.map fun (_, reason) =>
          s!"{vocabularyFile}: C9: together with the `Shared` tables of {path}: {reason}"

/-- A refusal of a baseline text as lines of output. -/
def baselineRefusals (file text : String) : List String :=
  (Baseline.explain text).map fun (line, reason) =>
    match line with
    | some line => s!"{file}:{line}: {reason}"
    | none => s!"{file}: {reason}"

/-- The baseline of the repository: its `prose-baseline.json`, or the baseline with no entry
when Git tracks no such file. -/
def loadBaseline (root : System.FilePath) (tracked : List String) :
    IO (Except (List String) Baseline) := do
  unless tracked.contains baselineFile do return .ok Baseline.empty
  let text ← IO.FS.readFile (root / baselineFile)
  match Baseline.parse text with
  | some baseline => return .ok baseline
  | none => return .error (baselineRefusals baselineFile text)

/-- The SHA-256 digest of the file at `path`, in lowercase hexadecimal digits, as the external
`shasum` tool computes it. -/
def digestOf (path : System.FilePath) : IO String := do
  let out ← IO.Process.output { cmd := "shasum", args := #["-a", "256", path.toString] }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"shasum -a 256 {path} failed: {out.stderr}"
  return ((out.stdout.splitOn " ").headD "")

/-- The vocabulary that the checks C6 and C7 use for the document at `path`: the vocabulary
file itself names each replaced name and each replaced word, so it is read with the vocabulary
that has no row. -/
def lexicon (vocabulary : Vocabulary) (path : String) : Vocabulary :=
  if path == vocabularyFile then Vocabulary.empty else vocabulary

/-- What the run observes of one document for `baseline`: its tally, unless its entry is frozen
or generated, and its digest, when its entry is frozen. -/
def observe (root : System.FilePath) (baseline : Baseline) (vocabulary : Vocabulary)
    (document : Document) : IO Observed := do
  match baseline.find document.path with
  | some (.frozen _) => return ⟨document.path, ← digestOf (root / document.path), []⟩
  | some (.generated _) => return ⟨document.path, "", []⟩
  | _ =>
    return ⟨document.path, "", tally (lexicon vocabulary document.path) document.reading⟩

/-- The base revision: the merge base of `HEAD` and the revision `options.base`, or that
revision itself when Git finds no merge base (in a shallow clone, where the history between the
two is not there). -/
def baseRevision (options : Options) : IO (Except String String) := do
  let merged ← git options.root #["merge-base", "HEAD", options.base]
  if merged.exitCode == 0 then return .ok merged.stdout.trimAscii.toString
  let tip ← git options.root #["rev-parse", "--verify", "--quiet", options.base ++ "^{commit}"]
  if tip.exitCode == 0 then return .ok tip.stdout.trimAscii.toString
  return .error s!"{baselineFile}: the base revision is not available: Git has no revision \
    {options.base}; fetch it, or give the revision that the change starts from with --base"

/-- The baseline of the base revision (`baseRevision`): its `prose-baseline.json`, `none` when
that commit has no such file. -/
def baseBaseline (options : Options) : IO (Except String (Option Baseline)) := do
  let commit ← match ← baseRevision options with
    | .ok commit => pure commit
    | .error reason => return .error reason
  let listed ← git options.root #["ls-tree", "--name-only", commit, "--", baselineFile]
  unless listed.exitCode == 0 do
    return .error s!"{baselineFile}: `git ls-tree {commit}` failed ({listed.stderr.trimAscii})"
  if listed.stdout.trimAscii.toString.isEmpty then return .ok none
  let shown ← git options.root #["show", s!"{commit}:./{baselineFile}"]
  unless shown.exitCode == 0 do
    return .error s!"{baselineFile}: `git show {commit}:./{baselineFile}` failed \
      ({shown.stderr.trimAscii})"
  match Baseline.parse shown.stdout with
  | some baseline => return .ok (some baseline)
  | none =>
    return .error s!"{baselineFile}: the {baselineFile} of the base revision {commit} is not \
      the print of a baseline"

/-- The number of rows of each table of a vocabulary, for the report of a run. -/
def rows (vocabulary : Vocabulary) : String :=
  let draft := vocabulary.draft
  s!"{draft.sharedNouns.length + draft.projectNouns.length} technical nouns, \
    {draft.sharedVerbs.length + draft.projectVerbs.length} technical verbs and \
    {draft.replaced.length} replaced words"

/-- Check the repository: the rule IDs of every tracked Markdown document, the vocabulary, the
checks C1 to C8 of every document with the baseline, and the baseline in relation to the base
revision. Exit code 0 when nothing is refused, and 1 otherwise, after printing each refusal. -/
def check (options : Options) : IO UInt32 := do
  let tracked ← trackedFiles options.root
  let documents ← documents options.root tracked
  if documents.isEmpty then
    IO.eprintln s!"FAIL: Git tracks no Markdown document below {options.root}"
    return 1
  let ruleIds := documents.flatMap fun d => documentErrors d.path d.source d.reading
  let vocabulary ← loadVocabulary options tracked
  let baseline ← loadBaseline options.root tracked
  let mut prose : List String := []
  let mut summary := ""
  match vocabulary, baseline with
  | .ok vocabulary, .ok baseline =>
    let observed ← documents.mapM (observe options.root baseline vocabulary)
    let found := documents.flatMap fun d =>
      if (baseline.find d.path).isNone then
        report (lexicon vocabulary d.path) d.path d.source d.reading
      else []
    let growth ← match ← baseBaseline options with
      | .ok base => pure (ratchet base baseline)
      | .error reason => pure [reason]
    prose := found ++ gate baseline observed ++ growth
    summary := s!"the vocabulary has {rows vocabulary}; {baseline.entries.length} of the \
      documents have an entry in the baseline"
  | vocabulary, baseline =>
    prose := (match vocabulary with | .error refusals => refusals | .ok _ => []) ++
      (match baseline with | .error refusals => refusals | .ok _ => [])
  unless ruleIds.isEmpty do
    IO.eprintln ("FAIL: tracked Markdown documents have a rule ID in prose that is not a link to \
      its rule page, or a construct the check does not read:\n" ++ "\n".intercalate ruleIds)
  unless prose.isEmpty do
    IO.eprintln ("FAIL: the vocabulary, the prose of the tracked Markdown documents or the \
      baseline is refused (docs/guides/writing.md gives each check):\n" ++
      "\n".intercalate prose)
  unless ruleIds.isEmpty && prose.isEmpty do return 1
  IO.println s!"Markdown documents: {documents.length} tracked documents read by md4c; every rule \
    ID in their prose links to its rule page; the checks C1 to C9 of their prose report nothing \
    that the baseline does not permit ({summary})"
  return 0

/-- Print every finding of the checks C1 to C8 in one tracked Markdown document. -/
def list (options : Options) (path : String) : IO UInt32 := do
  let tracked ← trackedFiles options.root
  let vocabulary ← match ← loadVocabulary options tracked with
    | .ok vocabulary => pure vocabulary
    | .error refusals =>
      IO.eprintln ("\n".intercalate refusals)
      return 1
  let source ← IO.FS.readFile (options.root / path)
  let found := report (lexicon vocabulary path) path source (read source)
  IO.println ("\n".intercalate found)
  IO.println s!"{path}: {found.length} findings"
  return 0

/-- The fields of the entry of a document with `tally`. -/
def countFields (path : String) (tally : List Nat) : List (List Char) :=
  path.toList :: tally.map fun count => (toString count).toList

/-- Write the baseline of the documents as they are: the frozen and generated entries of the
baseline as it is, and one entry of numbers for each other document with a finding. The ratchet
of the next check still refuses a new path and a larger number. -/
def writeBaseline (options : Options) : IO UInt32 := do
  let tracked ← trackedFiles options.root
  let documents ← documents options.root tracked
  let vocabulary ← match ← loadVocabulary options tracked with
    | .ok vocabulary => pure vocabulary
    | .error refusals =>
      IO.eprintln ("\n".intercalate refusals)
      return 1
  let baseline ← match ← loadBaseline options.root tracked with
    | .ok baseline => pure baseline
    | .error refusals =>
      IO.eprintln ("\n".intercalate refusals)
      return 1
  let kept := baseline.ledger.entries.filter fun fields =>
    match baseline.find (String.ofList (fields.headD [])) with
    | some (.frozen _) | some (.generated _) => true
    | _ => false
  let counted := documents.filterMap fun d =>
    match baseline.find d.path with
    | some (.frozen _) | some (.generated _) => none
    | _ =>
      let counts := tally (lexicon vocabulary d.path) d.reading
      if counts.all (· == 0) then none else some (countFields d.path counts)
  let entries := ((kept ++ counted).toArray.qsort fun left right =>
    left.headD [] < right.headD []).toList
  let text := String.ofList (Ledger.render ⟨entries⟩)
  match Baseline.parse text with
  | some written =>
    IO.FS.writeFile (options.root / baselineFile) text
    IO.println s!"{baselineFile}: {written.entries.length} entries written"
    return 0
  | none =>
    IO.eprintln ("\n".intercalate (baselineRefusals baselineFile text))
    return 1

/-! ## Controls

The files of `lean/Fixtures/ControlledProse` are controls of the decisions: for each check and
for each baseline decision, one text that the decision accepts and one or more that it refuses,
read by md4c as a document is. The run below refuses unless each control has the result that
`controls` gives, with the file, the line and the check in the message of each refusal, and
unless the directory holds these files and no other. -/

/-- What a control must give. -/
inductive Expect where
  /-- A document with no finding of any check. -/
  | clean
  /-- A document with a finding of `check` at `line`, in a message that starts with the file,
  the line and the check. -/
  | finding (check : String) (line : Nat)
  /-- A vocabulary that `parse` accepts, whose text is its print and whose source paths are
  files of the directory. -/
  | vocabulary
  /-- A text that `parse` refuses with a reason at `line`. -/
  | noVocabulary (line : Nat)
  /-- A vocabulary whose source path is not a file of the directory. -/
  | untrackedSource
  /-- A vocabulary that adopts the `Shared` tables of the accepted vocabulary. -/
  | adopts
  /-- A vocabulary that cannot adopt the `Shared` tables of the accepted vocabulary. -/
  | clashes
  /-- A baseline for which the gate accepts the document controls. -/
  | admits
  /-- A baseline for which the gate refuses the document controls, with `path` in a reason. -/
  | refusesDocument (path : String)
  /-- A baseline that the ratchet accepts in relation to the accepted baseline. -/
  | shrinks
  /-- A baseline that the ratchet refuses in relation to the accepted baseline, with `path` in a
  reason. -/
  | grows (path : String)
  /-- A text that `Baseline.parse` refuses with a reason at `line`. -/
  | noBaseline (line : Nat)

/-- The controls, by file name. -/
def controls : List (String × Expect) := [
  ("C1.accept.text", .clean), ("C1.refuse.text", .finding "C1" 5),
  ("C2.accept.text", .clean), ("C2.refuse.text", .finding "C2" 6),
  ("C3.accept.text", .clean), ("C3.refuse.text", .finding "C3" 3),
  ("C4.accept.text", .clean), ("C4.refuse.text", .finding "C4" 3),
  ("C5.accept.text", .clean), ("C5.refuse.text", .finding "C5" 3),
  ("C6.accept.text", .clean), ("C6.refuse.text", .finding "C6" 3),
  ("C7.accept.text", .clean), ("C7.refuse.text", .finding "C7" 3),
  ("C8.accept.text", .clean), ("C8.refuse.text", .finding "C8" 3),
  ("C9.accept.text", .vocabulary), ("C9.refuse.text", .noVocabulary 11),
  ("C9.untracked.text", .untrackedSource),
  ("C9.shared.text", .adopts), ("C9.clash.text", .clashes),
  ("gate.accept.json", .admits), ("gate.refuse.json", .refusesDocument "C3.refuse.text"),
  ("ratchet.accept.json", .shrinks), ("ratchet.refuse-path.json", .grows "C9.accept.text"),
  ("ratchet.refuse-number.json", .grows "C3.refuse.text"),
  ("baseline.refuse.json", .noBaseline 6)]

/-- Run the controls of `directory`. Exit code 0 when each control gives what `controls`
expects and the directory holds exactly these files, and 1 otherwise. -/
def runControls (directory : System.FilePath) : IO UInt32 := do
  let names := (← directory.readDir).toList.map (·.fileName)
  let read' (name : String) : IO String := IO.FS.readFile (directory / name)
  let some vocabulary := parse (← read' "C9.accept.text")
    | IO.eprintln "FAIL: C9.accept.text is not the print of a vocabulary"
      return 1
  let some baseline := Baseline.parse (← read' "gate.accept.json")
    | IO.eprintln "FAIL: gate.accept.json is not the print of a baseline"
      return 1
  -- The document controls, as the documents of a repository.
  let mut observed : List Observed := []
  for (name, expect) in controls do
    match expect with
    | .clean | .finding .. =>
      observed := observed ++ [⟨name, "", tally vocabulary (read (← read' name))⟩]
    | _ => pure ()
  let mut failures : List String := []
  for (name, expect) in controls do
    let text ← read' name
    let failure : Option String :=
      match expect with
      | .clean =>
        match report vocabulary name text (read text) with
        | [] => none
        | found => some s!"expected no finding, got: {found}"
      | .finding check line =>
        let found := report vocabulary name text (read text)
        if found.any (·.startsWith s!"{name}:{line}: {check}: ") then none
        else some s!"expected a message that starts with `{name}:{line}: {check}: `, got: {found}"
      | .vocabulary =>
        match parse text with
        | some parsed =>
          if write parsed != text then some "its print is another text"
          else
            match untracked names parsed with
            | [] => none
            | missing => some s!"source paths that are no file of the directory: {missing}"
        | none => some s!"refused: {vocabularyRefusals name text}"
      | .noVocabulary line =>
        if (parse text).isSome then some "accepted"
        else if (explain text).any (·.1 == some line) then none
        else some s!"expected a reason at line {line}, got: {vocabularyRefusals name text}"
      | .untrackedSource =>
        match parse text with
        | some parsed =>
          if (untracked names parsed).isEmpty then some "every source is a file" else none
        | none => some s!"refused: {vocabularyRefusals name text}"
      | .adopts =>
        match parse text with
        | some project => if (adopt vocabulary project).isSome then none else some "not adopted"
        | none => some s!"refused: {vocabularyRefusals name text}"
      | .clashes =>
        match parse text with
        | some project => if (adopt vocabulary project).isSome then some "adopted" else none
        | none => some s!"refused: {vocabularyRefusals name text}"
      | .admits =>
        match Baseline.parse text with
        | some parsed =>
          match gate parsed observed with
          | [] => none
          | refusals => some s!"the gate refuses: {refusals}"
        | none => some s!"refused: {baselineRefusals name text}"
      | .refusesDocument path =>
        match Baseline.parse text with
        | some parsed =>
          if (gate parsed observed).any (·.startsWith s!"{path}: ") then none
          else some s!"expected a refusal of {path}, got: {gate parsed observed}"
        | none => some s!"refused: {baselineRefusals name text}"
      | .shrinks =>
        match Baseline.parse text with
        | some head =>
          match ratchet (some baseline) head with
          | [] => none
          | refusals => some s!"the ratchet refuses: {refusals}"
        | none => some s!"refused: {baselineRefusals name text}"
      | .grows path =>
        match Baseline.parse text with
        | some head =>
          if (ratchet (some baseline) head).any (·.startsWith s!"{path}: ") then none
          else some s!"expected a refusal of {path}, got: {ratchet (some baseline) head}"
        | none => some s!"refused: {baselineRefusals name text}"
      | .noBaseline line =>
        if (Baseline.parse text).isSome then some "accepted"
        else if (Baseline.explain text).any (·.1 == some line) then none
        else some s!"expected a reason at line {line}, got: {baselineRefusals name text}"
    if let some reason := failure then failures := failures ++ [s!"{name}: {reason}"]
  let expected := controls.map (·.1)
  for name in names do
    unless expected.contains name do
      failures := failures ++ [s!"{name}: the directory has a file that is no control"]
  unless failures.isEmpty do
    IO.eprintln ("FAIL: controls of the checks of Markdown prose:\n" ++ "\n".intercalate failures)
    return 1
  IO.println s!"Controls of the checks of Markdown prose: {controls.length} controls in \
    {directory} gave the expected results (each refusal with its file, its line and its check)"
  return 0

end Regula.Controlled.Run

open Regula.Controlled.Run in
/-- Check the tracked Markdown documents of the repository at the directory given as the first
argument (see `Regula.Controlled.Run.check`), or do one of the other tasks of `usage`. -/
def main (args : List String) : IO UInt32 := do
  let usage := "usage: lake exe regula-markdown REPOSITORY [--shared CONTEXT.md] [--base \
    REVISION] [--write-baseline | --list DOCUMENT]\n       lake exe regula-markdown --controls \
    DIRECTORY"
  match args with
  | ["--controls", directory] => runControls directory
  | _ =>
    let some options := Options.parse args
      | IO.eprintln usage
        return 1
    match options.list with
    | some path => list options path
    | none => if options.write then writeBaseline options else check options
