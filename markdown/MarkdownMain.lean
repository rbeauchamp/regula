import RegulaMarkdown
import RegulaCore.Vocabulary

/-! Checks every Markdown document the repository tracks for a rule ID in prose that is not a
link to its rule page (`Regula.Markdown.documentErrors`), and checks the vocabulary of the
repository, its `CONTEXT.md` (check C9 of the writing guide, `RegulaCore/Vocabulary.lean`). The
documents are the files Git tracks below the repository root whose extension is `md` or
`markdown`, as `git ls-files` lists them; each is read from the working tree. The documentation
step of acceptance runs it (`lean/RegulaVerification.lean`).

This program uses four registered decisions of `RegulaCore`: `documentErrors` for the rule IDs,
and `parse`, `adopt` and `untracked` for the vocabulary. `vocabularyOf` puts the three decisions
of the vocabulary together, and `explain` and `clashes` give the lines of a refusal
(`explain_nil_iff`, `clashes_nil_iff`). The other refusals of a repository have no registered
decision and no theorem: `vocabularyOf` refuses a vocabulary that names a shared vocabulary when
it is given none; `loadVocabulary` refuses when Git does not track `CONTEXT.md`, and when Git
does not list the files of the repository of the shared vocabulary; and `check` refuses when Git
does not list the files of the repository, and when it lists no Markdown document. The rest is
not proved: the list of tracked files is Git's, the content of a file is the file system's, and
md4c's reading of a document is `Regula.Markdown.read`'s (`RegulaMarkdown.lean`). -/

open Regula.Markdown Regula.Controlled

namespace Regula.Controlled.Run

/-- The file of the vocabulary, at the repository root. -/
def vocabularyFile : String := "CONTEXT.md"

/-- The name of the check of the vocabulary. -/
def vocabularyCheck : String := "C9"

/-- One refusal as a line of output: the file, the line, the check and the reason. -/
def refusal (file : String) (line : Nat) (check reason : String) : String :=
  s!"{file}:{line}: {check}: {reason}"

/-- What the program was asked to do. -/
structure Options where
  /-- The repository root. -/
  root : System.FilePath
  /-- The `CONTEXT.md` of the package that the vocabulary names as shared. -/
  shared : Option System.FilePath := none

/-- The options of the arguments `args`, if they are a root and known options. -/
def Options.parse : List String → Option Options
  | [root] => if root.startsWith "--" then none else some { root }
  | [root, "--shared", path] =>
    if root.startsWith "--" then none else some { root, shared := some path }
  | _ => none

/-- The paths of the files Git tracks below `directory`, relative to it, or the reason Git gives
none. -/
def trackedFiles (directory : System.FilePath) : IO (Except String (List String)) := do
  let listed ← IO.Process.output {
    cmd := "git", args := #["ls-files", "-z"], cwd := some directory }
  unless listed.exitCode == 0 do
    return .error s!"`git ls-files` failed in {directory}: {listed.stderr.trimAscii}"
  return .ok ((listed.stdout.splitOn "\x00").filter (!·.isEmpty))

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

/-- Check the repository: the rule IDs of every tracked Markdown document, and the vocabulary.
Exit code 0 when there is at least one document and nothing is refused, and 1 otherwise, after
printing each refusal. -/
def check (options : Options) : IO UInt32 := do
  let tracked ← match ← trackedFiles options.root with
    | .ok tracked => pure tracked
    | .error reason =>
      IO.eprintln s!"FAIL: {reason}"
      return 1
  let documents := tracked.filter isMarkdown
  if documents.isEmpty then
    IO.eprintln s!"FAIL: Git tracks no Markdown document below {options.root}"
    return 1
  let mut ruleIds : List String := []
  for document in documents do
    let source ← IO.FS.readFile (options.root / document)
    ruleIds := ruleIds ++ Regula.Markdown.check document source
  let vocabulary ← loadVocabulary options tracked
  unless ruleIds.isEmpty do
    IO.eprintln ("FAIL: tracked Markdown documents have a rule ID in prose that is not a link to \
      its rule page, or a construct the check does not read:\n" ++ "\n".intercalate ruleIds)
  match vocabulary with
  | .error refusals =>
    IO.eprintln ("FAIL: the vocabulary is refused (docs/guides/writing.md gives the check):\n" ++
      "\n".intercalate refusals)
    return 1
  | .ok vocabulary =>
    unless ruleIds.isEmpty do return 1
    IO.println s!"Markdown documents: {documents.length} tracked documents read by md4c; every \
      rule ID in their prose links to its rule page; {vocabularyFile} is the print of a \
      vocabulary with {rows vocabulary}, and each source path is a tracked file (check \
      {vocabularyCheck})"
    return 0

/-! ## Controls

The files of `lean/Fixtures/ControlledProse` are controls of the decisions of check C9
(`parse`, `adopt` and `untracked`) and of the one refusal of `vocabularyOf` that none of them
decides: a text that the check accepts, and texts that it refuses.
Each is read as `CONTEXT.md` is, by `vocabularyOf`, with the names of the files of the directory
as the tracked files. The run below refuses unless each control has the result that `controls`
gives, with the exact file, line and check at the start of each refusal, and unless the
directory holds these files and no other. A control is a text of the grammar, which has no place
for a comment, so the comment of each control is here. -/

/-- What a control must give. -/
inductive Expect where
  /-- The check accepts. -/
  | accepted
  /-- The check refuses, and each refusal starts with `file`, `line` and the check. -/
  | refused (file : String) (line : Nat)

/-- One control: the file read as the vocabulary of a repository, the file read as the shared
vocabulary that it names, if any, and the result. -/
structure Control where
  /-- The file read as `CONTEXT.md`. -/
  own : String
  /-- The file read as the `CONTEXT.md` of the shared package. -/
  shared : Option String := none
  /-- The result that the control must give. -/
  expect : Expect

/-- The controls. -/
def controls : List Control := [
  -- `parse` accepts a vocabulary with each of the five tables, and `untracked` accepts its
  -- sources.
  { own := "C9.accept.text", expect := .accepted },
  -- `parse` refuses rows that are not in the sequence of their terms.
  { own := "C9.refuse-order.text", expect := .refused "C9.refuse-order.text" 11 },
  -- `parse` refuses one term in a table of nouns and in a table of verbs.
  { own := "C9.refuse-term.text", expect := .refused "C9.refuse-term.text" 16 },
  -- `parse` refuses a definition of two sentences with a tab character between them.
  { own := "C9.refuse-sentences.text", expect := .refused "C9.refuse-sentences.text" 10 },
  -- `parse` refuses a definition that is a period and has no word.
  { own := "C9.refuse-no-word.text", expect := .refused "C9.refuse-no-word.text" 10 },
  -- `untracked` refuses a source path that is no tracked file.
  { own := "C9.refuse-source.text", expect := .refused "C9.refuse-source.text" 10 },
  -- The branch of `vocabularyOf` that refuses a vocabulary that names a shared vocabulary when
  -- it is given none. This refusal is of no registered decision.
  { own := "C9.project.accept.text", expect := .refused "C9.project.accept.text" 5 },
  -- `adopt` accepts a project vocabulary with the `Shared` tables of the vocabulary it names.
  { own := "C9.project.accept.text", shared := some "C9.accept.text", expect := .accepted },
  -- `adopt` refuses a row of a `Project` table that has the term of a row of a `Shared` table.
  { own := "C9.project.refuse-term.text", shared := some "C9.accept.text",
    expect := .refused "C9.project.refuse-term.text" 11 },
  -- `untracked` refuses a source path of a row of a `Shared` table that is no tracked file of
  -- the repository of the shared vocabulary.
  { own := "C9.project.accept.text", shared := some "C9.package.refuse-source.text",
    expect := .refused "C9.package.refuse-source.text" 10 }]

/-- Run the controls of `directory`. Exit code 0 when each control gives what `controls` expects
and the directory holds exactly the files of the controls, and 1 otherwise. -/
def runControls (directory : System.FilePath) : IO UInt32 := do
  let names := (← directory.readDir).toList.map (·.fileName)
  let source (name : String) : IO Source :=
    return ⟨name, ← IO.FS.readFile (directory / name), names⟩
  let mut failures : List String := []
  for control in controls do
    let own ← source control.own
    let shared ← control.shared.mapM source
    let subject := s!"{control.own}{(control.shared.map fun name => s!" with {name}").getD ""}"
    match control.expect, vocabularyOf own shared with
    | .accepted, .ok _ => pure ()
    | .accepted, .error refusals =>
      failures := failures ++ [s!"{subject}: expected no refusal, got: {refusals}"]
    | .refused .., .ok _ => failures := failures ++ [s!"{subject}: expected a refusal, got none"]
    | .refused file line, .error refusals =>
      let start := refusal file line vocabularyCheck ""
      unless !refusals.isEmpty && refusals.all (·.startsWith start) do
        failures := failures ++
          [s!"{subject}: expected each refusal to start with `{start}`, got: {refusals}"]
  let expected := controls.flatMap fun control => control.own :: control.shared.toList
  for name in names do
    unless expected.contains name do
      failures := failures ++ [s!"{name}: the directory has a file that is no control"]
  unless failures.isEmpty do
    IO.eprintln ("FAIL: controls of the check of the vocabulary:\n" ++ "\n".intercalate failures)
    return 1
  IO.println s!"Controls of the check of the vocabulary: {controls.length} controls in \
    {directory} gave the expected results (each refusal starts with its file, its line and the \
    check {vocabularyCheck})"
  return 0

end Regula.Controlled.Run

open Regula.Controlled.Run in
/-- Check the tracked Markdown documents and the vocabulary of the repository at the directory
given as the first argument (see `Regula.Controlled.Run.check`), or run the controls of a
directory. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--controls", directory] => runControls directory
  | _ =>
    let some options := Options.parse args
      | IO.eprintln "usage: lake exe regula-markdown REPOSITORY [--shared CONTEXT.md]\n       \
          lake exe regula-markdown --controls DIRECTORY"
        return 1
    check options
