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
`tally` and `report`; `Baseline.parse`, `gate` and `ratchet` for the baseline; `baseOf` for the
base revision, with the start that `Start.read` reads. `vocabularyOf`
puts the three decisions of the vocabulary together, and `explain`, `clashes` and
`Baseline.explain` give the lines of a refusal (`explain_nil_iff`, `clashes_nil_iff`,
`Baseline.explain_nil_iff`). The other refusals of a repository have no registered decision and
no theorem: `vocabularyOf` refuses a vocabulary that names a shared vocabulary when it is given
none; `loadVocabulary` refuses when Git does not track `CONTEXT.md`, and when Git does not list
the files of the repository of the shared vocabulary; `baseReference` refuses when Git does not
give the baseline or the documents of the base revision; and `examine` refuses when Git does
not list the files of the repository, and when it lists no Markdown document. The rest is not
proved: the list of tracked files, the parents of the checked commit, the commit that a revision
names, the merge base, and the baseline and the documents of the base revision are Git's
(`historyOf`), the value that a workflow gives for its event is GitHub's, the content of a file
is the file system's, a digest is `shasum`'s, and md4c's reading of a document is
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

/-- The environment variable that gives the start of the check to check B2
(`Regula.Controlled.Start.read`): `before:` and the commit before the change, or `pull:` and the
head of a pull request. The workflow of CI sets it from the event that started the run
(`.github/workflows/ci.yml`). -/
def startVariable : String := "REGULA_PROSE_START"

/-- What the program was asked to do. -/
structure Options where
  /-- The repository root. -/
  root : System.FilePath
  /-- The `CONTEXT.md` of the package that the vocabulary names as shared. -/
  shared : Option System.FilePath := none
  /-- How the check was started, for the base revision of check B2: what the option `--target`
  and the variable `REGULA_PROSE_START` give (`Start.read`). -/
  start : Start := .target defaultTarget
  /-- Write the baseline of the documents as they are instead of checking them. -/
  write : Bool := false
  /-- Print every finding of this document instead of checking the repository. -/
  list : Option String := none

/-- The options of the arguments `args`, if they are a root and known options. `environment` is
the value of the environment variable `REGULA_PROSE_START`, if it is set. The start of the
check is what the option `--target` and that value give together (`Start.read`). -/
def Options.parse (environment : Option String) : List String → Option Options
  | root :: rest =>
    let rec go (options : Options) (target : Option String) : List String → Option Options
      | [] => some { options with start := Start.read target environment }
      | "--shared" :: path :: rest => go { options with shared := some path } target rest
      | "--target" :: revision :: rest => go options (some revision) rest
      | "--write-baseline" :: rest => go { options with write := true } target rest
      | "--list" :: path :: rest => go { options with list := some path } target rest
      | _ => none
    if root.startsWith "--" then none else go { root } none rest
  | [] => none

-- The arguments and the variable give the start through `Start.read`: a developer's run for
-- `origin/main` or for the revision of `--target`, the commit before the change, or the head of
-- a pull request. An empty variable, and the variable together with `--target`, give no base.
-- Compiled-evaluation observations at build time, not kernel-checked proofs.
#guard (Options.parse none ["r"]).map (·.start) == some (.target "origin/main")
#guard (Options.parse none ["r", "--target", "t"]).map (·.start) == some (.target "t")
#guard (Options.parse (some "before:c") ["r"]).map (·.start) == some (.before "c")
#guard (Options.parse (some "pull:h") ["r"]).map (·.start) == some (.pull "h")
#guard (Options.parse (some "") ["r"]).map (·.start) == some (.unknown "")
#guard (Options.parse (some "before:c") ["r", "--target", "t"]).map (·.start) ==
  some (.unknown "--target t together with `before:c`")

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

/-- The SHA-256 digest of `text`, in lowercase hexadecimal digits, as the external `shasum` tool
computes it from its standard input. -/
def digestOfText (text : String) : IO String := do
  let out ← IO.Process.output { cmd := "shasum", args := #["-a", "256"] } (some text)
  unless out.exitCode == 0 do
    throw <| IO.userError s!"shasum -a 256 failed: {out.stderr}"
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

/-- The refusals of check B2 for the baseline `head` of `file`, if the revision has one, in
relation to the reference of the base revision. -/
def ratchetRefusals (file : String) (reference : Reference) (head : Option Baseline)
    (tracked : List String) : List String :=
  (ratchet reference head tracked).map fun (line, reason) =>
    refusal file line ratchetCheck reason

/-- What the checks observe of one document of a base revision that has no baseline, with the
text `source`: its tally, and its digest when `head` has a frozen entry for its path. -/
def measureOne (head : Baseline) (vocabulary : Vocabulary) (path source : String) :
    IO Observed := do
  let digest ← match (entryOf head path).map Entry.allowance with
    | some (.frozen _) => digestOfText source
    | _ => pure ""
  return ⟨path, digest, tally (lexicon vocabulary path) (read source)⟩

/-- The baseline with the text `text` of `file`, or the refusals of its form. -/
def baselineOf (file text : String) : Except (List String) Baseline :=
  match Baseline.parse text with
  | some baseline => .ok baseline
  | none =>
    .error ((Baseline.explain text).map fun (line, reason) => refusal file line gateCheck reason)

/-- The baseline of the repository: its `prose-baseline.json`, or `none` when Git tracks no such
file. -/
def loadBaseline (root : System.FilePath) (tracked : List String) :
    IO (Except (List String) (Option Baseline)) := do
  unless tracked.contains baselineFile do return .ok none
  return (baselineOf baselineFile (← IO.FS.readFile (root / baselineFile))).map some

/-- What Git gives for `start`, of the checked commit `HEAD`. Git is asked only for the value
that `baseOf` reads for that start: the merge base of `HEAD` and the revision for the run of a
developer, the commit that the start names for a commit before the change, and the parents of
`HEAD` for a pull request. Each other value is absent, and so is a value that Git does not give.
Thus a start that gives a commit makes no call of `git merge-base`. Git is not asked about a
revision that is empty or that starts with `-`. -/
def historyOf (root : System.FilePath) (start : Start) : IO History := do
  let given (out : IO.Process.Output) : Option String :=
    let text := out.stdout.trimAscii.toString
    if out.exitCode == 0 && !text.isEmpty then some text else none
  let asked (revision : String) : Bool := !revision.isEmpty && !revision.startsWith "-"
  match start with
  | .target revision =>
    if !asked revision then return ⟨[], none, none⟩
    return ⟨[], none, given (← git root #["merge-base", "HEAD", revision])⟩
  | .before commit =>
    if !asked commit then return ⟨[], none, none⟩
    let named ← git root #["rev-parse", "--verify", "--quiet", commit ++ "^{commit}"]
    return ⟨[], given named, none⟩
  | .pull _ =>
    let listed ← git root #["rev-list", "--parents", "--max-count=1", "HEAD"]
    return ⟨((given listed).map fun line => (line.splitOn " ").drop 1).getD [], none, none⟩
  | .unknown _ => return ⟨[], none, none⟩

/-- Why `start` has no base revision, with what Git gives. -/
def unavailable (start : Start) (history : History) : String :=
  "the base revision is not available: " ++
    match start with
    | .target revision =>
      s!"Git gives no merge base of `HEAD` and `{revision}`; get the full history of the \
        repository, or give the branch that the change is for with --target"
    | .before commit =>
      s!"the start of the check gave `{commit}` as the commit before the change, and Git has \
        no such commit; get the full history of the repository"
    | .pull head =>
      s!"the checked commit is not the merge of the head `{head}` of the pull request into its \
        target: its parents are {history.parents}, not a first parent and then that head"
    | .unknown text =>
      s!"the start of the check gave no base revision ({text}); give `before:` and the commit \
        before the change, or `pull:` and the head of a pull request, in the variable \
        {startVariable}, or no variable for the run of a developer"

/-- The base revision of check B2 for the start of the check (`baseOf`), with what Git gives
(`historyOf`). When there is none, the check refuses, and no other revision replaces it. -/
def baseRevision (options : Options) : IO (Except String String) := do
  let history ← historyOf options.root options.start
  match baseOf options.start history with
  | some commit => return .ok commit
  | none => return .error (unavailable options.start history)

/-- What the checks observe of each Markdown document of the commit `commit`, as Git gives it:
the documents of a base revision that has no baseline (`measureOne`). -/
def measure (options : Options) (commit : String) (vocabulary : Vocabulary) (head : Baseline) :
    IO (Except String (List Observed)) := do
  let listed ← git options.root #["ls-tree", "-r", "--name-only", "-z", commit]
  unless listed.exitCode == 0 do
    return .error s!"`git ls-tree -r {commit}` failed ({listed.stderr.trimAscii})"
  let paths := ((listed.stdout.splitOn "\x00").filter (!·.isEmpty)).filter isMarkdown
  let mut observed : List Observed := []
  for path in paths do
    let shown ← git options.root #["show", s!"{commit}:./{path}"]
    unless shown.exitCode == 0 do
      return .error s!"`git show {commit}:./{path}` failed ({shown.stderr.trimAscii})"
    observed := observed ++ [← measureOne head vocabulary path shown.stdout]
  return .ok observed

/-- The reference of the base revision (`baseRevision`) for check B2: its `prose-baseline.json`,
or, when that commit has no such file, what the checks observe of its Markdown documents with
the vocabulary `vocabulary` (`measure`). -/
def baseReference (options : Options) (vocabulary : Vocabulary) (head : Baseline) :
    IO (Except String Reference) := do
  let commit ← match ← baseRevision options with
    | .ok commit => pure commit
    | .error reason => return .error reason
  let listed ← git options.root #["ls-tree", "--name-only", commit, "--", baselineFile]
  unless listed.exitCode == 0 do
    return .error s!"`git ls-tree {commit}` failed ({listed.stderr.trimAscii})"
  if listed.stdout.trimAscii.toString.isEmpty then
    return (← measure options commit vocabulary head).map .measured
  let shown ← git options.root #["show", s!"{commit}:./{baselineFile}"]
  unless shown.exitCode == 0 do
    return .error s!"`git show {commit}:./{baselineFile}` failed ({shown.stderr.trimAscii})"
  match Baseline.parse shown.stdout with
  | some baseline => return .ok (.baseline baseline)
  | none =>
    return .error s!"the {baselineFile} of the base revision {commit} is not the print of a \
      baseline"

/-- The tracked Markdown documents among `tracked`, read from the working tree. -/
def documentsOf (root : System.FilePath) (tracked : List String) : IO (List Document) :=
  (tracked.filter isMarkdown).mapM fun (path : String) => do
    let source ← IO.FS.readFile (root / path)
    return ⟨path, source, read source⟩

/-- What the checks of a repository give. -/
structure Outcome where
  /-- The refusals of the rule IDs. -/
  ruleIds : List String
  /-- The refusals of the vocabulary, of the prose and of the baseline. -/
  prose : List String
  /-- What the checks of the vocabulary, the prose and the baseline accepted, when they
  accepted. -/
  summary : String
  /-- The number of tracked Markdown documents. -/
  documents : Nat

/-- The checks of the repository: the rule IDs of every tracked Markdown document, the
vocabulary, the checks C1 to C8 of every document with the baseline, and the baseline in
relation to the base revision. The reason, when Git does not list the files of the repository
or lists no Markdown document. -/
def examine (options : Options) : IO (Except String Outcome) := do
  let tracked ← match ← trackedFiles options.root with
    | .ok tracked => pure tracked
    | .error reason => return .error reason
  let documents ← documentsOf options.root tracked
  if documents.isEmpty then
    return .error s!"Git tracks no Markdown document below {options.root}"
  let ruleIds := documents.flatMap fun d => documentErrors d.path d.source d.reading
  let vocabulary ← loadVocabulary options tracked
  let baseline ← loadBaseline options.root tracked
  let mut prose : List String := []
  let mut summary := ""
  match vocabulary, baseline with
  | .ok vocabulary, .ok head =>
    let baseline := head.getD Baseline.empty
    let observed ← documents.mapM (observe options.root baseline vocabulary)
    let growth ← match ← baseReference options vocabulary baseline with
      | .ok reference =>
        pure (ratchetRefusals baselineFile reference head (documents.map (·.path)))
      | .error reason => pure [refusal baselineFile 1 ratchetCheck reason]
    prose := documentRefusals baselineFile baseline vocabulary documents observed ++ growth
    summary := s!"{vocabularyFile} is the print of a vocabulary with {rows vocabulary}, and each \
      source path is a tracked file (check {vocabularyCheck}); the checks C1 to C8 of the prose \
      give no finding that the baseline does not permit ({baseline.entries.length} of the \
      documents have an entry in {baselineFile}, checks {gateCheck} and {ratchetCheck})"
  | vocabulary, baseline =>
    prose := (match vocabulary with | .error refusals => refusals | .ok _ => []) ++
      (match baseline with | .error refusals => refusals | .ok _ => [])
  return .ok ⟨ruleIds, prose, summary, documents.length⟩

/-- Check the repository (`examine`). Exit code 0 when there is at least one document and
nothing is refused, and 1 otherwise, after printing each refusal. -/
def check (options : Options) : IO UInt32 := do
  let outcome ← match ← examine options with
    | .ok outcome => pure outcome
    | .error reason =>
      IO.eprintln s!"FAIL: {reason}"
      return 1
  unless outcome.ruleIds.isEmpty do
    IO.eprintln ("FAIL: tracked Markdown documents have a rule ID in prose that is not a link to \
      its rule page, or a construct the check does not read:\n" ++
      "\n".intercalate outcome.ruleIds)
  unless outcome.prose.isEmpty do
    IO.eprintln ("FAIL: the vocabulary, the prose of the tracked Markdown documents or the \
      baseline is refused (docs/guides/writing.md gives each check):\n" ++
      "\n".intercalate outcome.prose)
  unless outcome.ruleIds.isEmpty && outcome.prose.isEmpty do return 1
  IO.println s!"Markdown documents: {outcome.documents} tracked documents read by md4c; every \
    rule ID in their prose links to its rule page; {outcome.summary}"
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
    | .ok baseline => pure (baseline.getD Baseline.empty)
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
the document controls. A control of B2 is a baseline in relation to `B2.base.json`, or a first
baseline in relation to document controls that are the documents of a base revision with no
baseline, or the removal of the baseline. The names of the files of the directory are the
tracked files. The run below refuses unless each
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
  /-- The file read as the first baseline of a repository: the base revision has no baseline,
  and its documents are the document controls `documents` (check B2). -/
  | first (documents : List String) (file : String)
  /-- A head revision with no baseline, in relation to the baseline `base` of the base revision
  (check B2). -/
  | removed (base : String)

/-- The files of a subject. -/
def Subject.files : Subject → List String
  | .vocabulary own shared => own :: shared.toList
  | .document file | .gate file => [file]
  | .ratchet base file => [base, file]
  | .first documents file => file :: documents
  | .removed base => [base]

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
  -- `parse` refuses a replaced word with an apostrophe at its start and at its end: the form of
  -- a word of the vocabulary for a comparison is its lowercase.
  ⟨.vocabulary "C9.refuse-apostrophes.text", .refused "C9.refuse-apostrophes.text" 10 "C9"⟩,
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
  -- `longSteps` refuses a sentence of 21 words in a block quote, in an item of an unordered
  -- list and in a table cell, each in an item of an ordered list: the reader keeps the lists
  -- around a block.
  ⟨.document "C2.refuse-quote.text", .refused "C2.refuse-quote.text" 3 "C2"⟩,
  ⟨.document "C2.refuse-bullet.text", .refused "C2.refuse-bullet.text" 4 "C2"⟩,
  ⟨.document "C2.refuse-cell.text", .refused "C2.refuse-cell.text" 7 "C2"⟩,
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
  -- `replacedWords` refuses a replaced word in apostrophes: the form of a word of prose for a
  -- comparison has no apostrophe at its start or at its end.
  ⟨.document "C7.refuse-apostrophes.text", .refused "C7.refuse-apostrophes.text" 3 "C7"⟩,
  -- `abbreviations` accepts an abbreviation in code font and refuses it in prose.
  ⟨.document "C8.accept.text", .accepted⟩,
  ⟨.document "C8.refuse.text", .refused "C8.refuse.text" 3 "C8"⟩,
  -- `abbreviations` refuses an abbreviation in apostrophes, by the same form of a word.
  ⟨.document "C8.refuse-apostrophes.text", .refused "C8.refuse-apostrophes.text" 3 "C8"⟩,
  -- `gate` accepts a baseline with the numbers of each document control that has findings, and
  -- with the digest of a frozen document.
  ⟨.gate "B1.accept.json", .accepted⟩,
  -- `gate` refuses an entry with another number than the document has.
  ⟨.gate "B1.refuse-number.json", .refused "B1.refuse-number.json" 7 "B1"⟩,
  -- `gate` refuses a document with findings and no entry, at the line where its entry would be.
  ⟨.gate "B1.refuse-entry.json", .refused "B1.refuse-entry.json" 20 "B1"⟩,
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
  ⟨.ratchet "B2.base.json" "B2.refuse-frozen.json", .refused "B2.refuse-frozen.json" 5 "B2"⟩,
  -- `ratchet` refuses the removal of the baseline, when the base revision has one.
  ⟨.removed "B2.base.json", .refused "B2.base.json" 1 "B2"⟩,
  -- `ratchet` accepts a first baseline whose entry has the numbers of a document of the base
  -- revision, which has no baseline.
  ⟨.first ["C4.refuse.text"] "B2.first.json", .accepted⟩,
  -- `ratchet` refuses the same first baseline when the base revision does not have the
  -- document: a new document with a semicolon cannot come in with an entry that agrees with it.
  ⟨.first ["C4.accept.text"] "B2.first.json", .refused "B2.first.json" 5 "B2"⟩,
  -- `ratchet` refuses a first baseline with a larger number than the document of the base
  -- revision has.
  ⟨.first ["C4.refuse.text"] "B2.first.refuse-number.json",
    .refused "B2.first.refuse-number.json" 5 "B2"⟩,
  -- `ratchet` accepts a first baseline with a frozen entry that has the digest of the document
  -- of the base revision, and refuses one with a different digest.
  ⟨.first ["C1.accept.text"] "B2.first.frozen.json", .accepted⟩,
  ⟨.first ["C1.accept.text"] "B2.first.refuse-frozen.json",
    .refused "B2.first.refuse-frozen.json" 5 "B2"⟩]

/-! ## Controls of the base revision

A control of the base revision is a repository that the run makes with Git in a temporary
directory, a commit that the check reads, and the option `--target` and the variable
`REGULA_PROSE_START` as a start of the check gives them. The control is the check of that
repository (`examine`), as the documentation step does it. The values that GitHub gives for an
event are not a part of a control: no local run has them.

What a control tells apart. A control that expects a refusal fails when the check takes a base
that accepts. `origin/main` names the checked commit itself in each such control that does not
give it a different commit, thus a check that takes `origin/main`, or the checked commit, in
place of the correct base accepts, and the control fails. A control that expects no refusal can
tell the correct base apart only from a base that refuses. The comparison of a commit with
itself accepts each baseline that check B1 accepts, thus no control that expects no refusal
tells the correct base apart from the checked commit. The comment of each control gives the
bases that it tells apart from the correct one, and the comment of a control that expects no
refusal also gives each base that it does not tell apart. -/

/-- One commit of the repository of a control. -/
structure Commit where
  /-- The branch that gets the commit. -/
  branch : String
  /-- The branch whose commit is the parent, or `none` for a commit with no parent. -/
  parent : Option String
  /-- The files that the commit changes: the text of each one, or `none` to remove the file. -/
  files : List (String × Option String)
  /-- A branch that the commit merges into its parent, as the second parent. -/
  merges : Option String := none

/-- A control of the base revision of check B2. -/
structure RepositoryControl where
  /-- The name of the repository of the control (`repositories`). -/
  repository : String
  /-- The branch whose commit the check reads. -/
  head : String
  /-- The option `--target`, if the start gives it. A branch name in braces is the full name of
  the commit of that branch. -/
  target : Option String := none
  /-- The variable `REGULA_PROSE_START`, if the start sets it, with the same braces. -/
  start : Option String := none
  /-- The branch whose commit `origin/main` names. The checked commit itself, when `none`. -/
  origin : Option String := none
  /-- Read a clone that has only the checked commit and the commit of `origin/main`, each with
  no history, as a checkout of depth 1 has. -/
  shallow : Bool := false
  /-- The result that the control must give. -/
  expect : Expect

/-- The print of the vocabulary with no row: the `CONTEXT.md` of each repository. -/
def controlVocabulary : String := write Vocabulary.empty

/-- The print of a baseline with `entries`. -/
def controlBaseline (entries : List Entry) : String := String.ofList (ledgerOf entries).render

/-- An entry that permits `count` findings of check C4 and no other finding for `path`. -/
def semicolonEntry (path : String) (count : Nat) : Entry :=
  ⟨path.toList, .counts (((List.replicate 8 0).set 3 count).map fun n => (Nat.repr n).toList)⟩

/-- The files of a commit whose document `a.md` has `count` semicolons, of two or less, and
whose baseline permits them. -/
def semicolons (count : Nat) : List (String × Option String) :=
  [("a.md", some (match count with
      | 0 => "# A\n\nOne two three.\n"
      | 1 => "# A\n\nOne; two three.\n"
      | _ => "# A\n\nOne; two; three.\n")),
    (baselineFile,
      some (controlBaseline (if count == 0 then [] else [semicolonEntry "a.md" count])))]

/-- The repositories of the controls of the base revision, each with its name. -/
def repositories : List (String × List Commit) := [
  -- Commits for a push. `a` permits two findings, and its child `b` permits one. `c`, from `b`,
  -- adds a document with a semicolon and an entry that agrees with it, and `d`, from `c`, adds
  -- a document with no finding. `x`, from `b`, has no finding and no entry, and `y`, from `x`,
  -- has the finding and the entry of `b` again. `removed`, from `b`, has no finding and no
  -- baseline. `other` has no parent and permits one finding.
  ("line", [
    ⟨"a", none, (vocabularyFile, some controlVocabulary) :: semicolons 2, none⟩,
    ⟨"b", some "a", semicolons 1, none⟩,
    ⟨"c", some "b", [("new.md", some "# N\n\nNew text; more text.\n"),
      (baselineFile, some (controlBaseline [semicolonEntry "a.md" 1,
        semicolonEntry "new.md" 1]))], none⟩,
    ⟨"d", some "c", [("clean.md", some "# C\n\nA clean text.\n")], none⟩,
    ⟨"x", some "b", semicolons 0, none⟩,
    ⟨"y", some "x", semicolons 1, none⟩,
    ⟨"removed", some "b", [("a.md", some "# A\n\nOne two three.\n"), (baselineFile, none)],
      none⟩,
    ⟨"other", none, semicolons 1, none⟩]),
  -- Commits for a pull request. `target` permits one finding less than `main`. `change`, from
  -- `target`, has the two findings of `main` again, and `merge` is the merge of `change` into
  -- `target`. `good`, from `target`, adds a document with no finding. `later`, from `target`,
  -- adds a document with a semicolon and its entry, and `fine` is the merge of `good` into
  -- `later`.
  ("pulls", [
    ⟨"main", none, (vocabularyFile, some controlVocabulary) :: semicolons 2, none⟩,
    ⟨"target", some "main", semicolons 1, none⟩,
    ⟨"change", some "target", semicolons 2, none⟩,
    ⟨"good", some "target", [("clean.md", some "# C\n\nA clean text.\n")], none⟩,
    ⟨"later", some "target", [("late.md", some "# L\n\nLate text; more text.\n"),
      (baselineFile, some (controlBaseline [semicolonEntry "a.md" 1,
        semicolonEntry "late.md" 1]))], none⟩,
    ⟨"merge", some "target", [], some "change"⟩,
    ⟨"fine", some "later", [], some "good"⟩]),
  -- Commits for the run of a developer. The first commit of `main` permits one finding. `work`
  -- has two commits from it: the first has no finding and no entry, and the second has the
  -- finding and the entry again. `worse`, from the first commit of `main`, has one finding
  -- more. A later commit of `main` has no finding and no entry.
  ("local", [
    ⟨"main", none, (vocabularyFile, some controlVocabulary) :: semicolons 1, none⟩,
    ⟨"work", some "main", semicolons 0, none⟩,
    ⟨"work", some "work", semicolons 1, none⟩,
    ⟨"worse", some "main", semicolons 2, none⟩,
    ⟨"main", some "main", semicolons 0, none⟩]),
  -- The first commit has a frozen document. The branch `side` changes the document and removes
  -- its entry. A later commit of `main` removes the document and its entry.
  ("diverged", [
    ⟨"main", none, [(vocabularyFile, some controlVocabulary),
      ("record.md", some "# Record\n\nThe first text.\n"),
      (baselineFile, some (controlBaseline [⟨"record.md".toList, .frozen
        "f181adc34424559724d267a81d4090eedd38a8864b55641b801d6b20a593551b".toList⟩]))], none⟩,
    ⟨"side", some "main", [("record.md", some "# Record\n\nA changed text.\n"),
      (baselineFile, some (controlBaseline []))], none⟩,
    ⟨"main", some "main", [("record.md", none), (baselineFile, some (controlBaseline []))],
      none⟩])]

/-- The controls of the base revision. The comment of each control gives the base that the
check must take. For a control that expects a refusal, it gives a base that accepts, which the
control thus tells apart. For a control that expects no refusal, it gives the bases that refuse,
which the control tells apart, and the bases that it does not tell apart. -/
def repositoryControls : List RepositoryControl := [
  -- A push. The base is the commit before the push itself, and no merge base.
  -- `c` after `b`: the new entry is refused. The checked commit accepts.
  { repository := "line", head := "c", start := some "before:{b}",
    expect := .refused baselineFile 6 ratchetCheck },
  -- Two commits in one push, `c` and `d` after `b`: the new entry is refused. The first parent
  -- `c` accepts.
  { repository := "line", head := "d", start := some "before:{b}",
    expect := .refused baselineFile 6 ratchetCheck },
  -- A push that moves the branch back from `b` to its parent `a`: the larger number of `a` is
  -- refused. The merge base of the two is `a` itself, which accepts.
  { repository := "line", head := "a", start := some "before:{b}",
    expect := .refused baselineFile 5 ratchetCheck },
  -- A push to a history with no relation, from `other` to `a`: the larger number of `a` is
  -- refused at its entry. A merge base, which Git does not give, refuses at line 1.
  { repository := "line", head := "a", start := some "before:{other}",
    expect := .refused baselineFile 5 ratchetCheck },
  -- A push that removes the baseline is refused at line 1 of the baseline of `b`. The checked
  -- commit accepts.
  { repository := "line", head := "removed", start := some "before:{b}",
    expect := .refused baselineFile 1 ratchetCheck },
  -- The first push of a branch, where the commit before the push is 40 zeros: no commit has
  -- that name, and the check refuses. `origin/main`, the checked commit, accepts.
  { repository := "line", head := "c",
    start := some "before:0000000000000000000000000000000000000000",
    expect := .refused baselineFile 1 ratchetCheck },
  -- Accepted: two commits in one push, `x` and `y` after `b`, with the numbers of `b`. Told
  -- apart: the first parent `x` and `origin/main`, which is `x` here, refuse the entry. Not
  -- told apart: the merge base, which is `b`, and the checked commit.
  { repository := "line", head := "y", start := some "before:{b}", origin := some "x",
    expect := .accepted },
  -- Accepted: a push from `a` to `other`, which has no relation to `a` and permits less. Told
  -- apart: a merge base and the first parent, which Git does not give, refuse at line 1, and
  -- `origin/main`, which is `removed` here, refuses the entry. Not told apart: the checked
  -- commit.
  { repository := "line", head := "other", start := some "before:{a}", origin := some "removed",
    expect := .accepted },
  -- Accepted: a push from `c` to `y`, which permits nothing more than `c`. Told apart: the
  -- first parent `x` and `origin/main`, which is `x` here, refuse the entry. Not told apart:
  -- the merge base, which is `b`, and the checked commit.
  { repository := "line", head := "y", start := some "before:{c}", origin := some "x",
    expect := .accepted },
  -- A manual start. The base is the first parent of the commit, as `<commit>^`.
  -- `c`: the new entry is refused. The checked commit accepts.
  { repository := "line", head := "c", start := some "before:{c}^",
    expect := .refused baselineFile 6 ratchetCheck },
  -- `a` has no parent: the check refuses. `origin/main`, the checked commit, accepts.
  { repository := "line", head := "a", start := some "before:{a}^",
    expect := .refused baselineFile 1 ratchetCheck },
  -- Accepted: the release commit, compared with itself. Told apart: the first parent `b` and
  -- `origin/main`, which is `b` here, refuse the new entry of `c`. The merge base of a commit
  -- and itself is that commit.
  { repository := "line", head := "c", start := some "before:HEAD", origin := some "b",
    expect := .accepted },
  -- A variable that gives no base is refused, and `origin/main`, the checked commit, does not
  -- replace it: the empty variable, `before:` with no commit, and a text of no known form.
  { repository := "line", head := "c", start := some "",
    expect := .refused baselineFile 1 ratchetCheck },
  { repository := "line", head := "c", start := some "before:",
    expect := .refused baselineFile 1 ratchetCheck },
  { repository := "line", head := "c", start := some "{b}",
    expect := .refused baselineFile 1 ratchetCheck },
  -- The variable and `--target` together are refused at line 1. The variable alone refuses at
  -- line 6, and the target alone accepts.
  { repository := "line", head := "c", target := some "{c}", start := some "before:{b}",
    expect := .refused baselineFile 1 ratchetCheck },
  -- A pull request. The base is the first parent of the checked merge commit, when its second
  -- parent is the head that the start gives.
  -- The merge of `change` into `target` has the larger number of `main` again: refused. The
  -- second parent `change`, the checked commit, and the older commit `main`, which
  -- `origin/main` names here, accept.
  { repository := "pulls", head := "merge", start := some "pull:{change}", origin := some "main",
    expect := .refused baselineFile 5 ratchetCheck },
  -- Accepted: the merge of `good` into `later`. Told apart: the second parent `good`, which is
  -- also the merge base with the head, refuses the entry of `late.md`, and so does
  -- `origin/main`, which is `target` here. Not told apart: the checked commit.
  { repository := "pulls", head := "fine", start := some "pull:{good}", origin := some "target",
    expect := .accepted },
  -- The second parent of `merge` is not the head `good` that the start gives: refused at line
  -- 1. The first parent with no comparison of the head refuses at line 5.
  { repository := "pulls", head := "merge", start := some "pull:{good}",
    expect := .refused baselineFile 1 ratchetCheck },
  -- A checkout of the head of the pull request is no merge commit: refused at line 1. Its
  -- first parent refuses at line 5.
  { repository := "pulls", head := "change", start := some "pull:{change}",
    expect := .refused baselineFile 1 ratchetCheck },
  -- A checkout of the merge commit with no history has no parent: refused. `origin/main`, the
  -- checked commit, accepts.
  { repository := "pulls", head := "merge", start := some "pull:{change}", shallow := true,
    expect := .refused baselineFile 1 ratchetCheck },
  -- The run of a developer. The base is the merge base of the commit and the target.
  -- Accepted: `work`, with `origin/main` at the later commit of `main`. Told apart: that later
  -- commit and the first parent of `work` have no entry for `a.md` and refuse. Not told apart:
  -- the checked commit.
  { repository := "local", head := "work", origin := some "main", expect := .accepted },
  -- `worse` has one finding more than the merge base: refused. The checked commit accepts.
  { repository := "local", head := "worse", origin := some "main",
    expect := .refused baselineFile 5 ratchetCheck },
  -- Accepted: a commit that `origin/main` names, with no change. The merge base is the commit
  -- itself. Told apart: its first parent `target` permits less and refuses.
  { repository := "pulls", head := "change", origin := some "change", expect := .accepted },
  -- `--target` gives the branch `work`, whose merge base with `worse` is the first commit of
  -- `main`: refused. `origin/main`, the checked commit, accepts.
  { repository := "local", head := "worse", target := some "work",
    expect := .refused baselineFile 5 ratchetCheck },
  -- With the full history, the merge base of `side` and `main` has the frozen entry, and the
  -- change of the frozen document is refused. The later commit of `main` and the checked
  -- commit accept.
  { repository := "diverged", head := "side", origin := some "main",
    expect := .refused baselineFile 5 ratchetCheck },
  -- With no history, Git gives no merge base: refused at line 1. The later commit of `main`
  -- has no frozen entry and accepts.
  { repository := "diverged", head := "side", origin := some "main", shallow := true,
    expect := .refused baselineFile 1 ratchetCheck }]

/-- Run `git` with `args` in `directory` for a control, with no configuration of the user or of
the system and with one author, and give its output. -/
def gitControl (directory : System.FilePath) (args : Array String) : IO String := do
  let out ← IO.Process.output {
    cmd := "git", args, cwd := some directory,
    env := #[("GIT_CONFIG_GLOBAL", some "/dev/null"), ("GIT_CONFIG_SYSTEM", some "/dev/null"),
      ("GIT_AUTHOR_NAME", some "control"), ("GIT_AUTHOR_EMAIL", some "control@example.invalid"),
      ("GIT_COMMITTER_NAME", some "control"),
      ("GIT_COMMITTER_EMAIL", some "control@example.invalid")] }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"git {args} failed in {directory}: {out.stderr}"
  return out.stdout.trimAscii.toString

/-- Make the repository of `commits` in `directory`. A commit with no parent keeps the files of
the commit before it in the list, with its own changes. -/
def makeRepository (directory : System.FilePath) (commits : List Commit) : IO Unit := do
  IO.FS.createDirAll directory
  discard <| gitControl directory #["init", "--quiet", "--initial-branch", "start"]
  for commit in commits do
    match commit.parent with
    | some parent =>
      discard <| gitControl directory #["checkout", "--quiet", "-B", commit.branch, parent]
    | none => discard <| gitControl directory #["checkout", "--quiet", "--orphan", commit.branch]
    for (path, text) in commit.files do
      match text with
      | some text => IO.FS.writeFile (directory / path) text
      | none => IO.FS.removeFile (directory / path)
    match commit.merges with
    | some branch =>
      discard <| gitControl directory #["merge", "--quiet", "--no-ff", "--message",
        commit.branch, branch]
    | none =>
      discard <| gitControl directory #["add", "--all"]
      discard <| gitControl directory #["commit", "--quiet", "--message", commit.branch]

/-- `text` with each branch name in braces replaced by the full name of the commit of that
branch in the repository at `directory`. -/
def expand (directory : System.FilePath) (text : String) : IO String := do
  let mut result := ""
  let mut first := true
  for part in text.splitOn "{" do
    if first then
      result := part
      first := false
    else
      match part.splitOn "}" with
      | branch :: rest =>
        result := result ++ (← gitControl directory #["rev-parse", branch]) ++
          "}".intercalate rest
      | [] => pure ()
  return result

/-- The result of the controls of the base revision: what each control that does not give its
expected result gave. -/
def runRepositoryControls (judge : String → Expect → List String → List String) :
    IO (List String) :=
  IO.FS.withTempDir fun root => do
    for (name, commits) in repositories do
      makeRepository (root / name) commits
    let mut failures : List String := []
    let mut index := 0
    for control in repositoryControls do
      index := index + 1
      let made := root / control.repository
      discard <| gitControl made #["checkout", "--quiet", "--detach", control.head]
      let origin ← gitControl made #["rev-parse", control.origin.getD control.head]
      let directory ←
        if control.shallow then do
          let clone := root / s!"shallow-{index}"
          discard <| gitControl root #["clone", "--quiet", "--depth", "1", "--branch",
            control.head, s!"file://{made}", clone.toString]
          discard <| gitControl clone #["fetch", "--quiet", "--depth", "1", "origin",
            s!"{origin}:refs/remotes/origin/main"]
          pure clone
        else do
          discard <| gitControl made #["update-ref", "refs/remotes/origin/main", origin]
          pure made
      let target ← control.target.mapM (expand made)
      let start ← control.start.mapM (expand made)
      let subject := s!"repository `{control.repository}`, commit `{control.head}`\
        {if control.shallow then " with no history" else ""}\
        {(control.target.map fun text => s!", --target {text}").getD ""}\
        {(control.start.map fun text => s!", {startVariable}={text}").getD ""}\
        {(control.origin.map fun branch => s!", origin/main at `{branch}`").getD ""}"
      let result ← match ← examine { root := directory, start := Start.read target start } with
        | .ok outcome => pure (outcome.ruleIds ++ outcome.prose)
        | .error reason => pure [reason]
      failures := failures ++ judge subject control.expect result
    return failures

/-- Run the controls of `directory`. Exit code 0 when each control gives what `controls` expects
and the directory holds exactly the files of the controls, and when each control of the base
revision gives what `repositoryControls` expects. Exit code 1 otherwise. -/
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
  -- What a control that does not give its expected result gave.
  let judge (subject : String) (expect : Expect) (result : List String) : List String :=
    match expect, result with
    | .accepted, [] => []
    | .accepted, refusals => [s!"{subject}: expected no refusal, got: {refusals}"]
    | .refused .., [] => [s!"{subject}: expected a refusal, got none"]
    | .refused file line check, refusals =>
      let start := refusal file line check ""
      if refusals.all (·.startsWith start) then []
      else [s!"{subject}: expected each refusal to start with `{start}`, got: {refusals}"]
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
          pure (s!"{file} in relation to {base}",
            ratchetRefusals file (.baseline before) (some head) names)
        | before, head =>
          pure (s!"{file} in relation to {base}",
            (match before with | .error refusals => refusals | .ok _ => []) ++
              (match head with | .error refusals => refusals | .ok _ => []))
      | .first base file =>
        match baselineOf file (← text file) with
        | .error refusals => pure (s!"{file} as a first baseline", refusals)
        | .ok head =>
          let measured ← (documents.filter fun d => base.contains d.path).mapM fun d =>
            measureOne head vocabulary d.path d.source
          pure (s!"{file} as a first baseline for the documents {base}",
            ratchetRefusals file (.measured measured) (some head) names)
      | .removed base =>
        match baselineOf base (← text base) with
        | .error refusals => pure (s!"no baseline in relation to {base}", refusals)
        | .ok before =>
          pure (s!"no baseline in relation to {base}",
            ratchetRefusals base (.baseline before) none names)
    failures := failures ++ judge subject control.expect result
  let expected := controls.flatMap (·.subject.files)
  for name in names do
    unless expected.contains name do
      failures := failures ++ [s!"{name}: the directory has a file that is no control"]
  failures := failures ++ (← runRepositoryControls judge)
  unless failures.isEmpty do
    IO.eprintln ("FAIL: controls of the checks of Markdown prose:\n" ++ "\n".intercalate failures)
    return 1
  IO.println s!"Controls of the checks of Markdown prose: {controls.length} controls in \
    {directory} and {repositoryControls.length} controls of the base revision, in repositories \
    that the run made with Git, gave the expected results (each refusal starts with its file, \
    its line and its check)"
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
    let some options := Options.parse (← IO.getEnv startVariable) args
      | IO.eprintln "usage: lake exe regula-markdown REPOSITORY [--shared CONTEXT.md] [--target \
          REVISION] [--write-baseline | --list DOCUMENT]\n       lake exe regula-markdown \
          --controls DIRECTORY"
        return 1
    match options.list with
    | some path => list options path
    | none => if options.write then writeBaseline options else check options
