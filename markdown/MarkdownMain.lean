import RegulaMarkdown
import RegulaCore.ProseBaseline

/-! Checks every Markdown document the repository tracks: for a rule ID in prose that is not a
link to its rule page (`Regula.Markdown.documentErrors`), and for the writing rules that a text
decides alone (checks C1 to C8, `RegulaCore/ControlledProse.lean`), with the baseline of the
documents that have findings (checks B1 and B2, `RegulaCore/ProseBaseline.lean`). It also checks
the vocabulary of the repository, its `CONTEXT.md` (check C9, `RegulaCore/Vocabulary.lean`). The
documents are the files Git tracks below the repository root whose extension is `md` or
`markdown`, as `git ls-files` lists them; each is read from the working tree. The documentation
step of acceptance runs it (`lean/RegulaVerification.lean`).

This program uses these registered decisions of `RegulaCore`: `documentErrors` for the rule IDs;
`parse`, `adopt` and `untracked` for the vocabulary; the eight checks of a document through
`tally` and `report`; `Baseline.parse`, `gate` and `ratchet` for the baseline. `vocabularyOf`
puts the three decisions of the vocabulary together, and `explain`, `clashes` and
`Baseline.explain` give the lines of a refusal (`explain_nil_iff`, `clashes_nil_iff`,
`Baseline.explain_nil_iff`). The other refusals of a repository have no registered decision and
no theorem: `vocabularyOf` refuses a vocabulary that names a shared vocabulary when it is given
none; `loadVocabulary` refuses when Git does not track `CONTEXT.md`, and when Git does not list
the files of the repository of the shared vocabulary; `baseBaseline` refuses when Git has no
base revision or does not give its baseline; and `check` refuses when Git does not list the
files of the repository, and when it lists no Markdown document. The rest is not proved: the
list of tracked files and the baseline of the base revision are Git's, the content of a file is
the file system's, a digest is `shasum`'s, and md4c's reading of a document is
`Regula.Markdown.read`'s (`RegulaMarkdown.lean`). -/

open Regula.Markdown Regula.Controlled

namespace Regula.Controlled.Run

/-- The file of the vocabulary, at the repository root. -/
def vocabularyFile : String := "CONTEXT.md"

/-- The file of the baseline, at the repository root. -/
def baselineFile : String := "prose-baseline.json"

/-- The name of the check of the vocabulary. -/
def vocabularyCheck : String := "C9"

/-- The name of the check of the findings that the baseline permits (`gate`), and of the form of
the baseline (`Baseline.parse`). -/
def gateCheck : String := "B1"

/-- The name of the check of the baseline in relation to the base revision (`ratchet`). -/
def ratchetCheck : String := "B2"

/-- One refusal as a line of output: the file, the line, the check and the reason. -/
def refusal (file : String) (line : Nat) (check reason : String) : String :=
  s!"{file}:{line}: {check}: {reason}"

/-- What the program was asked to do. -/
structure Options where
  /-- The repository root. -/
  root : System.FilePath
  /-- The `CONTEXT.md` of the package that the vocabulary names as shared. -/
  shared : Option System.FilePath := none
  /-- The revision whose merge base with `HEAD` is the base revision of check B2. -/
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

/-- Run `git` with `args` in `directory`. -/
def git (directory : System.FilePath) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd := "git", args, cwd := some directory }

/-- The paths of the files Git tracks below `directory`, relative to it, or the reason Git gives
none. -/
def trackedFiles (directory : System.FilePath) : IO (Except String (List String)) := do
  let listed ← git directory #["ls-files", "-z"]
  unless listed.exitCode == 0 do
    return .error s!"`git ls-files` failed in {directory}: {listed.stderr.trimAscii}"
  return .ok ((listed.stdout.splitOn "\x00").filter (!·.isEmpty))

/-! ## The vocabulary -/

/-- A vocabulary file as the program reads it. -/
structure Source where
  /-- The path of the file, as a refusal shows it. -/
  file : String
  /-- The text of the file. -/
  text : String
  /-- The paths of the tracked files of the repository of the file, relative to its root. -/
  tracked : List String

/-- What a row with an untracked source is refused for. -/
def untrackedReason (path : String) : String :=
  s!"the source path `{path}` is not a tracked file of the repository of this vocabulary"

/-- Check C9. The vocabulary of `own`: its text is the print of a vocabulary (`parse`); when it
names a shared vocabulary, `shared` is the print of one and the rows together are well formed
(`adopt`); and the source path of each row is a tracked file of the repository of the row
(`untracked`). Each refusal gives its file, its line, the check and the reason. -/
def vocabularyOf (own : Source) (shared : Option Source) : Except (List String) Vocabulary :=
  match parse own.text with
  | none =>
    .error ((explain own.text).map fun (line, reason) =>
      refusal own.file line vocabularyCheck reason)
  | some project =>
    match shared with
    | none =>
      match project.draft.shared with
      | some package =>
        .error [refusal own.file (project.draft.lineOf (sharedLabel ++ package)) vocabularyCheck
          s!"the vocabulary names the shared vocabulary `{String.ofList package}`; give the \
            {vocabularyFile} of that package with --shared"]
      | none =>
        match untracked own.tracked own.tracked project with
        | [] => .ok project
        | missing =>
          .error (missing.map fun (_, line, path) =>
            refusal own.file (project.draft.lineOf line) vocabularyCheck (untrackedReason path))
    | some shared =>
      match parse shared.text with
      | none =>
        .error ((explain shared.text).map fun (line, reason) =>
          refusal shared.file line vocabularyCheck reason)
      | some package =>
        match adopt package project with
        | none =>
          .error ((clashes package project).map fun (inShared, line, reason) =>
            refusal (if inShared then shared.file else own.file) line vocabularyCheck reason)
        | some vocabulary =>
          match untracked shared.tracked own.tracked vocabulary with
          | [] => .ok vocabulary
          | missing =>
            .error (missing.map fun (inShared, line, path) =>
              if inShared then
                refusal shared.file (package.draft.lineOf line) vocabularyCheck
                  (untrackedReason path)
              else
                refusal own.file (project.draft.lineOf line) vocabularyCheck
                  (untrackedReason path))

/-- The vocabulary of the repository at `options.root`, or its refusals: the result of
`vocabularyOf` for its `CONTEXT.md`, for the file given with `--shared`, and for the files that
Git tracks in the repository of each one. The repository of the shared file is the directory
that file is in, which must be a Git checkout. -/
def loadVocabulary (options : Options) (tracked : List String) :
    IO (Except (List String) Vocabulary) := do
  unless tracked.contains vocabularyFile do
    return .error [refusal vocabularyFile 1 vocabularyCheck
      s!"Git tracks no {vocabularyFile} at the repository root"]
  let own : Source :=
    ⟨vocabularyFile, ← IO.FS.readFile (options.root / vocabularyFile), tracked⟩
  match options.shared with
  | none => return vocabularyOf own none
  | some path =>
    let directory := path.parent.getD "."
    match ← trackedFiles directory with
    | .error reason =>
      return .error [refusal path.toString 1 vocabularyCheck
        s!"the tracked files of the repository of the shared vocabulary are not known: {reason}"]
    | .ok sharedTracked =>
      return vocabularyOf own (some ⟨path.toString, ← IO.FS.readFile path, sharedTracked⟩)

/-- The number of rows of each table of a vocabulary, for the report of a run. -/
def rows (vocabulary : Vocabulary) : String :=
  let draft := vocabulary.draft
  s!"{draft.sharedNouns.length + draft.projectNouns.length} technical nouns, \
    {draft.sharedVerbs.length + draft.projectVerbs.length} technical verbs and \
    {draft.replaced.length} replaced words"

/-! ## The documents and the baseline -/

/-- One Markdown document: its path, its text and md4c's reading of it. -/
structure Document where
  /-- The path, relative to the repository root. -/
  path : String
  /-- The text of the file. -/
  source : String
  /-- md4c's reading of the text. -/
  reading : Reading

/-- The vocabulary that the checks C6 and C7 use for the document at `path`: the vocabulary
file itself gives each replaced name and each replaced word, so it is read with the vocabulary
that has no row. -/
def lexicon (vocabulary : Vocabulary) (path : String) : Vocabulary :=
  if path == vocabularyFile then Vocabulary.empty else vocabulary

/-- The SHA-256 digest of the file at `path`, in lowercase hexadecimal digits, as the external
`shasum` tool computes it. -/
def digestOf (path : System.FilePath) : IO String := do
  let out ← IO.Process.output { cmd := "shasum", args := #["-a", "256", path.toString] }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"shasum -a 256 {path} failed: {out.stderr}"
  return ((out.stdout.splitOn " ").headD "")

/-- The entry of `baseline` for the document at `path`, if it has one. -/
def entryOf (baseline : Baseline) (path : String) : Option Entry :=
  baseline.entries.find? fun entry => entry.path == path.toList

/-- What the run observes of one document for `baseline`: its tally, unless its entry is frozen
or generated, and its digest, when its entry is frozen. -/
def observe (directory : System.FilePath) (baseline : Baseline) (vocabulary : Vocabulary)
    (document : Document) : IO Observed := do
  match (entryOf baseline document.path).map Entry.allowance with
  | some (.frozen _) => return ⟨document.path, ← digestOf (directory / document.path), []⟩
  | some (.generated _) => return ⟨document.path, "", []⟩
  | _ =>
    return ⟨document.path, "", tally (lexicon vocabulary document.path) document.reading⟩

/-- The refusals of the checks C1 to C8 and B1 for `documents` and `baseline`: each finding of a
document with no entry, with its file, its line and its check, and each document that the
baseline does not admit, with the line of the baseline. -/
def documentRefusals (file : String) (baseline : Baseline) (vocabulary : Vocabulary)
    (documents : List Document) (observed : List Observed) : List String :=
  (documents.flatMap fun d =>
    if (entryOf baseline d.path).isNone then
      report (lexicon vocabulary d.path) d.path d.source d.reading
    else []) ++
  (gate baseline observed).map fun (line, reason) => refusal file line gateCheck reason

/-- The refusals of check B2 for the baseline `head` of `file` in relation to `base`. -/
def ratchetRefusals (file : String) (base : Option Baseline) (head : Baseline)
    (tracked : List String) : List String :=
  (ratchet base head tracked).map fun (line, reason) => refusal file line ratchetCheck reason

/-- The baseline with the text `text` of `file`, or the refusals of its form. -/
def baselineOf (file text : String) : Except (List String) Baseline :=
  match Baseline.parse text with
  | some baseline => .ok baseline
  | none =>
    .error ((Baseline.explain text).map fun (line, reason) => refusal file line gateCheck reason)

/-- The baseline of the repository: its `prose-baseline.json`, or the baseline with no entry
when Git tracks no such file. -/
def loadBaseline (root : System.FilePath) (tracked : List String) :
    IO (Except (List String) Baseline) := do
  unless tracked.contains baselineFile do return .ok Baseline.empty
  return baselineOf baselineFile (← IO.FS.readFile (root / baselineFile))

/-- The base revision: the merge base of `HEAD` and the revision `options.base`, or that
revision itself when Git finds no merge base (in a shallow clone, where the history between the
two is not there). -/
def baseRevision (options : Options) : IO (Except String String) := do
  let merged ← git options.root #["merge-base", "HEAD", options.base]
  if merged.exitCode == 0 then return .ok merged.stdout.trimAscii.toString
  let tip ← git options.root #["rev-parse", "--verify", "--quiet", options.base ++ "^{commit}"]
  if tip.exitCode == 0 then return .ok tip.stdout.trimAscii.toString
  return .error s!"the base revision is not available: Git has no revision {options.base}; \
    fetch it, or give the revision that the change starts from with --base"

/-- The baseline of the base revision (`baseRevision`): its `prose-baseline.json`, `none` when
that commit has no such file. -/
def baseBaseline (options : Options) : IO (Except String (Option Baseline)) := do
  let commit ← match ← baseRevision options with
    | .ok commit => pure commit
    | .error reason => return .error reason
  let listed ← git options.root #["ls-tree", "--name-only", commit, "--", baselineFile]
  unless listed.exitCode == 0 do
    return .error s!"`git ls-tree {commit}` failed ({listed.stderr.trimAscii})"
  if listed.stdout.trimAscii.toString.isEmpty then return .ok none
  let shown ← git options.root #["show", s!"{commit}:./{baselineFile}"]
  unless shown.exitCode == 0 do
    return .error s!"`git show {commit}:./{baselineFile}` failed ({shown.stderr.trimAscii})"
  match Baseline.parse shown.stdout with
  | some baseline => return .ok (some baseline)
  | none =>
    return .error s!"the {baselineFile} of the base revision {commit} is not the print of a \
      baseline"

/-- The tracked Markdown documents among `tracked`, read from the working tree. -/
def documentsOf (root : System.FilePath) (tracked : List String) : IO (List Document) :=
  (tracked.filter isMarkdown).mapM fun (path : String) => do
    let source ← IO.FS.readFile (root / path)
    return ⟨path, source, read source⟩

/-- Check the repository: the rule IDs of every tracked Markdown document, the vocabulary, the
checks C1 to C8 of every document with the baseline, and the baseline in relation to the base
revision. Exit code 0 when there is at least one document and nothing is refused, and 1
otherwise, after printing each refusal. -/
def check (options : Options) : IO UInt32 := do
  let tracked ← match ← trackedFiles options.root with
    | .ok tracked => pure tracked
    | .error reason =>
      IO.eprintln s!"FAIL: {reason}"
      return 1
  let documents ← documentsOf options.root tracked
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
    let growth ← match ← baseBaseline options with
      | .ok base => pure (ratchetRefusals baselineFile base baseline (documents.map (·.path)))
      | .error reason => pure [refusal baselineFile 1 ratchetCheck reason]
    prose := documentRefusals baselineFile baseline vocabulary documents observed ++ growth
    summary := s!"{vocabularyFile} is the print of a vocabulary with {rows vocabulary}, and each \
      source path is a tracked file (check {vocabularyCheck}); the checks C1 to C8 of the prose \
      give no finding that the baseline does not permit ({baseline.entries.length} of the \
      documents have an entry in {baselineFile}, checks {gateCheck} and {ratchetCheck})"
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
  IO.println s!"Markdown documents: {documents.length} tracked documents read by md4c; every \
    rule ID in their prose links to its rule page; {summary}"
  return 0

/-- Print every finding of the checks C1 to C8 in one Markdown document of the repository. -/
def list (options : Options) (path : String) : IO UInt32 := do
  let tracked ← match ← trackedFiles options.root with
    | .ok tracked => pure tracked
    | .error reason =>
      IO.eprintln s!"FAIL: {reason}"
      return 1
  let vocabulary ← match ← loadVocabulary options tracked with
    | .ok vocabulary => pure vocabulary
    | .error refusals =>
      IO.eprintln ("\n".intercalate refusals)
      return 1
  let source ← IO.FS.readFile (options.root / path)
  let found := report (lexicon vocabulary path) path source (read source)
  unless found.isEmpty do IO.println ("\n".intercalate found)
  IO.println s!"{path}: {found.length} findings"
  return 0

/-- Write the baseline of the documents as they are: the frozen and generated entries of the
baseline as it is, and one entry of numbers for each other document with a finding. Check B2 of
the next run still refuses a new path and a larger number. -/
def writeBaseline (options : Options) : IO UInt32 := do
  let tracked ← match ← trackedFiles options.root with
    | .ok tracked => pure tracked
    | .error reason =>
      IO.eprintln s!"FAIL: {reason}"
      return 1
  let documents ← documentsOf options.root tracked
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
  let fixed (entry : Entry) : Bool :=
    match entry.allowance with
    | .counts _ => false
    | _ => true
  let kept := baseline.entries.filter fixed
  let counted := documents.filterMap fun d =>
    if ((entryOf baseline d.path).map fixed).getD false then none
    else
      let counts := tally (lexicon vocabulary d.path) d.reading
      if counts.all (· == 0) then none
      else some (⟨d.path.toList, .counts (counts.map fun n => (Nat.repr n).toList)⟩ : Entry)
  let entries := ((kept ++ counted).toArray.qsort fun left right =>
    left.path < right.path).toList
  let text := String.ofList (ledgerOf entries).render
  match baselineOf baselineFile text with
  | .ok written =>
    IO.FS.writeFile (options.root / baselineFile) text
    IO.println s!"{baselineFile}: {written.entries.length} entries written"
    return 0
  | .error refusals =>
    IO.eprintln ("\n".intercalate refusals)
    return 1

/-! ## Controls

The files of `lean/Fixtures/ControlledProse` are controls of the decisions: for each check, a
text that the check accepts and one or more texts that it refuses. A control of C9 is read as
`CONTEXT.md` is, by `vocabularyOf`. A control of C1 to C8 is a document, read by md4c as a
tracked document is, with the vocabulary of `C9.accept.text`. A control of B1 is a baseline for
the document controls, and a control of B2 is a baseline in relation to `B2.base.json`. The
names of the files of the directory are the tracked files. The run below refuses unless each
control has the result that `controls` gives, with the exact file, line and check at the start
of each refusal, and unless the directory holds these files and no other. A control is a text
of a grammar or a document, which has no place for a comment, so the comment of each control is
here. -/

/-- What a control must give. -/
inductive Expect where
  /-- The check accepts. -/
  | accepted
  /-- The check refuses, and each refusal starts with `file`, `line` and `check`. -/
  | refused (file : String) (line : Nat) (check : String)

/-- What a control is read as. -/
inductive Subject where
  /-- The file read as `CONTEXT.md`, and the file read as the `CONTEXT.md` of the shared package
  that it names, if any (check C9). -/
  | vocabulary (own : String) (shared : Option String := none)
  /-- The file read as one document (checks C1 to C8). -/
  | document (file : String)
  /-- The file read as the baseline of the document controls (check B1). -/
  | gate (file : String)
  /-- The file read as the baseline of a head revision in relation to the baseline `base` of the
  base revision (check B2). -/
  | ratchet (base file : String)

/-- The files of a subject. -/
def Subject.files : Subject → List String
  | .vocabulary own shared => own :: shared.toList
  | .document file | .gate file => [file]
  | .ratchet base file => [base, file]

/-- One control: what is read, and the result it must give. -/
structure Control where
  /-- What the control is read as. -/
  subject : Subject
  /-- The result that the control must give. -/
  expect : Expect

/-- The controls. -/
def controls : List Control := [
  -- `parse` accepts a vocabulary with each of the five tables, and `untracked` accepts its
  -- sources.
  ⟨.vocabulary "C9.accept.text", .accepted⟩,
  -- `parse` refuses rows that are not in the sequence of their terms.
  ⟨.vocabulary "C9.refuse-order.text", .refused "C9.refuse-order.text" 11 "C9"⟩,
  -- `parse` refuses one term in a table of nouns and in a table of verbs.
  ⟨.vocabulary "C9.refuse-term.text", .refused "C9.refuse-term.text" 16 "C9"⟩,
  -- `parse` refuses a definition of two sentences with a tab character between them.
  ⟨.vocabulary "C9.refuse-sentences.text", .refused "C9.refuse-sentences.text" 10 "C9"⟩,
  -- `parse` refuses a definition that is a period and has no word.
  ⟨.vocabulary "C9.refuse-no-word.text", .refused "C9.refuse-no-word.text" 10 "C9"⟩,
  -- `untracked` refuses a source path that is no tracked file.
  ⟨.vocabulary "C9.refuse-source.text", .refused "C9.refuse-source.text" 10 "C9"⟩,
  -- The branch of `vocabularyOf` that refuses a vocabulary that names a shared vocabulary when
  -- it is given none. This refusal is of no registered decision.
  ⟨.vocabulary "C9.project.accept.text", .refused "C9.project.accept.text" 5 "C9"⟩,
  -- `adopt` accepts a project vocabulary with the `Shared` tables of the vocabulary it names.
  ⟨.vocabulary "C9.project.accept.text" (some "C9.accept.text"), .accepted⟩,
  -- `adopt` refuses a row of a `Project` table that has the term of a row of a `Shared` table.
  ⟨.vocabulary "C9.project.refuse-term.text" (some "C9.accept.text"),
    .refused "C9.project.refuse-term.text" 11 "C9"⟩,
  -- `untracked` refuses a source path of a row of a `Shared` table that is no tracked file of
  -- the repository of the shared vocabulary.
  ⟨.vocabulary "C9.project.accept.text" (some "C9.package.refuse-source.text"),
    .refused "C9.package.refuse-source.text" 10 "C9"⟩,
  -- `longSentences` accepts sentences of 25 words in a paragraph, an item of an unordered list
  -- and a table cell, and refuses a sentence of 26 words.
  ⟨.document "C1.accept.text", .accepted⟩,
  ⟨.document "C1.refuse.text", .refused "C1.refuse.text" 3 "C1"⟩,
  -- `longSentences` counts a number with periods as its parts, when the number is not in code
  -- font: 24 words and such a number of three parts are 27 words.
  ⟨.document "C1.refuse-number.text", .refused "C1.refuse-number.text" 3 "C1"⟩,
  -- `longSteps` accepts sentences of 20 words in an item of an ordered list and after
  -- `WARNING:`, and refuses a sentence of 21 words in an item of an ordered list.
  ⟨.document "C2.accept.text", .accepted⟩,
  ⟨.document "C2.refuse.text", .refused "C2.refuse.text" 3 "C2"⟩,
  -- `longParagraphs` accepts a paragraph of six sentences and refuses one of seven.
  ⟨.document "C3.accept.text", .accepted⟩,
  ⟨.document "C3.refuse.text", .refused "C3.refuse.text" 3 "C3"⟩,
  -- `longParagraphs` counts the sentences in parentheses: one sentence with seven sentences in
  -- parentheses is refused.
  ⟨.document "C3.refuse-parentheses.text", .refused "C3.refuse-parentheses.text" 3 "C3"⟩,
  -- `semicolons` accepts a semicolon in code font and refuses one in prose.
  ⟨.document "C4.accept.text", .accepted⟩,
  ⟨.document "C4.refuse.text", .refused "C4.refuse.text" 3 "C4"⟩,
  -- `contractions` accepts a possessive form and a contraction in a quotation, and refuses a
  -- contraction in prose.
  ⟨.document "C5.accept.text", .accepted⟩,
  ⟨.document "C5.refuse.text", .refused "C5.refuse.text" 3 "C5"⟩,
  -- `replacedNames` accepts a replaced name that is a part of a longer term, and refuses the
  -- replaced name alone.
  ⟨.document "C6.accept.text", .accepted⟩,
  ⟨.document "C6.refuse.text", .refused "C6.refuse.text" 3 "C6"⟩,
  -- `replacedWords` accepts a replaced word in code font and refuses it in prose.
  ⟨.document "C7.accept.text", .accepted⟩,
  ⟨.document "C7.refuse.text", .refused "C7.refuse.text" 3 "C7"⟩,
  -- `abbreviations` accepts an abbreviation in code font and refuses it in prose.
  ⟨.document "C8.accept.text", .accepted⟩,
  ⟨.document "C8.refuse.text", .refused "C8.refuse.text" 3 "C8"⟩,
  -- `gate` accepts a baseline with the numbers of each document control that has findings, and
  -- with the digest of a frozen document.
  ⟨.gate "B1.accept.json", .accepted⟩,
  -- `gate` refuses an entry with another number than the document has.
  ⟨.gate "B1.refuse-number.json", .refused "B1.refuse-number.json" 7 "B1"⟩,
  -- `gate` refuses a document with findings and no entry, at the line where its entry would be.
  ⟨.gate "B1.refuse-entry.json", .refused "B1.refuse-entry.json" 15 "B1"⟩,
  -- `gate` refuses a frozen entry whose digest is not the digest of its document.
  ⟨.gate "B1.refuse-frozen.json", .refused "B1.refuse-frozen.json" 5 "B1"⟩,
  -- `Baseline.parse` refuses entries that are not in the sequence of their paths.
  ⟨.gate "B1.refuse-order.json", .refused "B1.refuse-order.json" 7 "B1"⟩,
  -- `ratchet` accepts a baseline with a smaller number, without an entry of numbers and with
  -- the frozen entry of the base revision.
  ⟨.ratchet "B2.base.json" "B2.accept.json", .accepted⟩,
  -- `ratchet` refuses an entry with a path that the base revision does not have.
  ⟨.ratchet "B2.base.json" "B2.refuse-path.json", .refused "B2.refuse-path.json" 6 "B2"⟩,
  -- `ratchet` refuses an entry with a larger number than the base revision has.
  ⟨.ratchet "B2.base.json" "B2.refuse-number.json", .refused "B2.refuse-number.json" 6 "B2"⟩,
  -- `ratchet` refuses a baseline without the frozen entry of the base revision, when the
  -- document of that entry is a tracked file.
  ⟨.ratchet "B2.base.json" "B2.refuse-frozen.json", .refused "B2.refuse-frozen.json" 5 "B2"⟩]

/-- Run the controls of `directory`. Exit code 0 when each control gives what `controls` expects
and the directory holds exactly the files of the controls, and 1 otherwise. -/
def runControls (directory : System.FilePath) : IO UInt32 := do
  let names := (← directory.readDir).toList.map (·.fileName)
  let text (name : String) : IO String := IO.FS.readFile (directory / name)
  let source (name : String) : IO Source := return ⟨name, ← text name, names⟩
  let some vocabulary := parse (← text "C9.accept.text")
    | IO.eprintln "FAIL: C9.accept.text is not the print of a vocabulary"
      return 1
  -- The document controls, as the documents of a repository.
  let mut documents : List Document := []
  for control in controls do
    if let .document file := control.subject then
      let content ← text file
      documents := documents ++ [⟨file, content, read content⟩]
  let mut failures : List String := []
  for control in controls do
    let (subject, result) ← match control.subject with
      | .vocabulary own shared =>
        let result := match vocabularyOf (← source own) (← shared.mapM source) with
          | .ok _ => []
          | .error refusals => refusals
        pure (s!"{own}{(shared.map fun name => s!" with {name}").getD ""}", result)
      | .document file =>
        let content ← text file
        pure (file, report vocabulary file content (read content))
      | .gate file =>
        match baselineOf file (← text file) with
        | .error refusals => pure (file, refusals)
        | .ok baseline =>
          let observed ← documents.mapM (observe directory baseline vocabulary)
          pure (file, (gate baseline observed).map fun (line, reason) =>
            refusal file line gateCheck reason)
      | .ratchet base file =>
        match baselineOf base (← text base), baselineOf file (← text file) with
        | .ok before, .ok head =>
          pure (s!"{file} in relation to {base}", ratchetRefusals file (some before) head names)
        | before, head =>
          pure (s!"{file} in relation to {base}",
            (match before with | .error refusals => refusals | .ok _ => []) ++
              (match head with | .error refusals => refusals | .ok _ => []))
    match control.expect, result with
    | .accepted, [] => pure ()
    | .accepted, refusals =>
      failures := failures ++ [s!"{subject}: expected no refusal, got: {refusals}"]
    | .refused .., [] =>
      failures := failures ++ [s!"{subject}: expected a refusal, got none"]
    | .refused file line check, refusals =>
      let start := refusal file line check ""
      unless refusals.all (·.startsWith start) do
        failures := failures ++
          [s!"{subject}: expected each refusal to start with `{start}`, got: {refusals}"]
  let expected := controls.flatMap (·.subject.files)
  for name in names do
    unless expected.contains name do
      failures := failures ++ [s!"{name}: the directory has a file that is no control"]
  unless failures.isEmpty do
    IO.eprintln ("FAIL: controls of the checks of Markdown prose:\n" ++ "\n".intercalate failures)
    return 1
  IO.println s!"Controls of the checks of Markdown prose: {controls.length} controls in \
    {directory} gave the expected results (each refusal starts with its file, its line and its \
    check)"
  return 0

end Regula.Controlled.Run

open Regula.Controlled.Run in
/-- Check the tracked Markdown documents, the vocabulary and the baseline of the repository at
the directory given as the first argument (see `Regula.Controlled.Run.check`), or do one of the
other tasks of the usage text. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--controls", directory] => runControls directory
  | _ =>
    let some options := Options.parse args
      | IO.eprintln "usage: lake exe regula-markdown REPOSITORY [--shared CONTEXT.md] [--base \
          REVISION] [--write-baseline | --list DOCUMENT]\n       lake exe regula-markdown \
          --controls DIRECTORY"
        return 1
    match options.list with
    | some path => list options path
    | none => if options.write then writeBaseline options else check options
