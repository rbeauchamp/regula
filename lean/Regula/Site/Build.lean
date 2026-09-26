import Regula.Qualification.RuleExamples
import Regula.Checker.ResultProtocol
import RegulaCore.SiteDocs
import RegulaCore.SiteTheme

/-! # Rule-reference site builder

Operational builder of the published rule reference (issue #15). It admits the rule-example
corpus evidence, generates the Verso sources from the registry (`RegulaCore.Rule`), the rule
explanations (`RegulaCore.Guide`) and the admitted records, renders them with the pinned
Verso package in `website/`, assembles the GitHub Pages artifact with every snapshot of the
site archive and checks it.

## Main declarations

- `helpUrl_dev`: every help URL the linter emits is the site's development route of its rule.
- `admitShard`: a corpus shard export is used only when it is `COMPLETED`, admitted by the
  proved `ruleExampleQualification` executable, and its recorded checker, corpus and
  configuration bytes equal the current sources.
- `exampleOf`: the display form of one rule's two admitted records.
- `fetchArchive`: the snapshots of the site archive, read with the deployment gate's reader.
- `build`: generation, Verso rendering, assembly and `checkArtifact`.

## Boundaries

Process, filesystem, Git and Verso observations are trusted operational inputs. The pure
decisions (routes, escaping, filters, diffs, links, page structure, colour contrast) are proved in
`RegulaCore.Site`, `RegulaCore.SitePage`, `RegulaCore.SiteDocs` and `RegulaCore.SiteTheme`. Workspace paths of the
disposable qualification projects are displayed as `<example>`, `<scratch>` and `<regula>`; the
exact records remain in the corpus export this build consumed.
-/

namespace Regula.Site.Build

open Lean System Regula.Site Regula.Qualification RegulaQualification.Evidence

/-- The linter's emitted help URL is exactly the development page route of the site. Kernel-checked
when the `site` executable is built; this module is in the excluded operational `Regula` library. -/
theorem helpUrl_dev (id : RuleId) : Regula.helpUrl id = devUrl id := rfl

private def get (j : Json) (key : String) : IO Json := IO.ofExcept (field j key)
private def str (j : Json) (key : String) : IO String := IO.ofExcept (text j key)
private def arr (j : Json) (key : String) : IO (Array Json) := IO.ofExcept (array j key)
private def has (j : Json) (key : String) (value : Json) : Bool := (field j key).toOption == some value

/-- The pinned Verso revision of the website package. -/
def versoRevision (root : FilePath) : IO String := do
  let manifest ← readJson (root / "website/lake-manifest.json")
  let packages ← arr manifest "packages"
  let some verso ← packages.findM? (fun p => return (← str p "name") == "verso")
    | throw <| IO.userError "website lock manifest has no verso package"
  str verso "rev"

private def git (root : FilePath) (args : Array String) : IO String := do
  let result ← run root "git" args
  requireChecks [⟨s!"git {args}: {result.stderr}", result.exitCode == 0⟩]
  return result.stdout

/-- Build identity: the checked-out commit, whether the worktree is modified, and the
producer identity the checker executables embed. -/
def identity (root : FilePath) : IO Identity := do
  let head := (← git root #["rev-parse", "HEAD"]).trimAscii.toString
  let some revision := Commit.parse? head | throw <| IO.userError s!"not a commit identifier: {head}"
  let dirty := !(← git root #["status", "--porcelain", "--untracked-files=normal"]).isEmpty
  let producer := Regula.Checker.ResultProtocol.producer
  return { revision, dirty, toolchain := producer.toolchain, producerVersion := producer.producerVersion,
           versoRevision := ← versoRevision root }

/-- Admit one corpus shard export: completed, admitted by the proved qualifier executable,
and recorded against exactly the current checker, corpus and configuration sources. -/
def admitShard (root : FilePath) (current : Json) (path : FilePath) : IO Json := do
  let shard ← readJson path
  requireChecks [
    ⟨s!"{path}: corpus export outcome is COMPLETED", has shard "outcome" (.str "COMPLETED")⟩,
    ⟨s!"{path}: corpus export schema 1", has shard "schemaVersion" (toJson (1 : Nat))⟩,
    ⟨s!"{path}: evidence was recorded for other checker, corpus or configuration sources than this checkout",
      has shard "checkerAfter" current && has shard "checkerBefore" current⟩]
  let admitted ← run root (root / ".lake/build/bin/ruleExampleQualification").toString #[path.toString] cleanEnv
  requireChecks [⟨s!"{path}: corpus admission refused\n{admitted.stdout}{admitted.stderr}", admitted.exitCode == 0⟩]
  return shard

/-- Replace workspace paths of a disposable qualification project for display. -/
def displayText (project : String) (text : String) : String :=
  let scratch := (System.FilePath.mk project).parent.map (·.toString) |>.getD project
  ((text.replace (scratch ++ "/slot/root") "<regula>").replace project "<example>").replace scratch "<scratch>"

/-- Workspace-relative display path of an input of `project`, if it is one of the project's
own inputs rather than the checker's isolated copy or a documentation snippet alias. -/
def relativeInput (project uri : String) : Option String :=
  match uri.dropPrefix? (project ++ "/") with
  | some rest =>
    let rest := rest.toString
    if rest.startsWith "tmp/" || (uri.splitOn "#").length > 1 then none else some rest
  | none => none

/-- Every input file of one record: its sources and its configuration files (absent ones as
`none`), by workspace-relative path, with display-normalized content. -/
def inputs (record : Json) : IO (List (String × Option String)) := do
  let request ← get record "request"
  let project ← str request "project"
  let sources ← arr (← get record "before") "sources"
  let fromSources ← sources.toList.filterMapM fun s => do
    return (relativeInput project (← str s "uri")).map fun p => (p, s)
  let fromSources ← fromSources.mapM fun (p, s) => do return (p, some (displayText project (← str s "source")))
  let config ← IO.ofExcept (fromJson? (α := Array (String × Option String)) (← get request "configuration"))
  let fromConfig := config.toList.filterMap fun (uri, content) =>
    (relativeInput project uri).map fun p => (p, content.map (displayText project))
  return (fromSources ++ fromConfig).foldl (fun acc (p, c) => if acc.any (·.1 == p) then acc else acc ++ [(p, c)]) []

private def lookup (xs : List (String × Option String)) (p : String) : Option String :=
  (xs.find? (·.1 == p)).bind (·.2)

/-- Name of a Lean `Name` in the registry's structural JSON encoding (innermost first). -/
def nameText (j : Json) : String :=
  match j.getArr? with
  | .ok parts => String.intercalate "." (parts.toList.reverse.map fun part =>
      match part.getArr? with
      | .ok #[_, .str s] => s
      | .ok #[_, n] => n.compress
      | _ => part.compress)
  | .error _ => j.compress

private def ruleOf (s : String) : IO RuleId := do
  match RuleId.parse? s with
  | some id => pure id
  | none => throw <| IO.userError s!"unknown rule ID in evidence: {s}"

/-- Display form of one finding of a violating record. -/
def findingOf (project : String) (d : Json) : IO FindingView := do
  let rule ← ruleOf (← str d "id")
  let args ← get d "arguments"
  let (subjectKind, subject) := match field args "declaration", field args "root", field args "subject" with
    | .ok n, _, _ => ("Declaration", nameText n)
    | _, .ok n, _ => ("Execution root", nameText n)
    | _, _, .ok (.str s) => ("Subject", displayText project s)
    | _, _, _ => ("Finding", "")
  let location ← get d "location"
  let place ← match (← str location "kind") with
    | "source" => do
      let uri ← str location "uri"
      let path := match uri.dropPrefix? (project ++ "/") with
        | some rest =>
          let rest := rest.toString
          match rest.splitOn "/project/" with
          | [pre, post] => if pre.startsWith "tmp/" then post ++ " (the audit's fresh isolated copy)" else rest
          | _ => rest
        | none => displayText project uri
      let range ← get location "lspSelectionRange"
      let start ← get range "start"
      let line := (← IO.ofExcept ((← get start "line").getNat?)) + 1
      let column := (← IO.ofExcept ((← get start "character").getNat?)) + 1
      pure s!"{path}, line {line}, column {column}"
    | "module" => pure s!"module `{nameText (← get location "name")}`"
    | _ => pure ("project " ++ displayText project (← str location "identity"))
  let claim := match field d "claim" with | .ok (.str c) => some c | _ => none
  return { rule, severity := ← str d "severity", impact := ← str d "impact", mode := ← str d "mode",
           claim, subjectKind, subject, detail := displayText project (← str (← get d "arguments") "detail"), location := place }

/-- The fixture of rule `id` whose exact text is `text`, if any. -/
def fixtureOf (root : FilePath) (id : RuleId) (text : String) : IO (Option String) := do
  let folder := root / "examples/rules" / id.spelling
  let files ← (← folder.readDir).qsort (fun a b => a.fileName < b.fileName) |>.filterM fun e => return !(← e.path.isDir)
  for entry in files do
    if (← IO.FS.readFile entry.path) == text then
      return some s!"examples/rules/{id.spelling}/{entry.fileName}"
  return none

private def requestText (request : Json) (mode : String) : IO String := do
  let kind ← str request "kind"
  let project ← str request "project"
  let subject := displayText project (← str request "subject")
  let claim := match field request "claim" with | .ok (.str c) => c | _ => "none"
  let execution := match field request "execution" with | .ok (.str e) => e | _ => "report"
  let entry := "; run by the qualification runner's ruleExamples entry, which executes the same detector with dependency Git facts captured once for the campaign"
  return (· ++ entry) <| match kind with
    | "file" => s!"fresh single-file audit (axiomGate --file) of {subject} with claim {claim} and execution {execution}; evidence mode {mode}"
    | "policyNegative" => s!"single-file policy inspection of {subject} that keeps Lean's original compiler warning; evidence mode {mode}"
    | "documentation" => s!"documentation fence audit of {subject}; evidence mode {mode}"
    | _ => s!"fresh whole-project audit (axiomGate) of {subject}; evidence mode {mode}"

/-- The display form of one rule's admitted violation and fix records. -/
def exampleOf (root : FilePath) (id : RuleId) (violation fixed : Json) : IO (Example × EvidenceSummary) := do
  let vInputs ← inputs violation
  let fInputs ← inputs fixed
  let paths := (vInputs.map (·.1) ++ fInputs.map (·.1)).eraseDups.mergeSort (· ≤ ·)
  let shown (p : String) (t : Option String) : IO (Option ShownFile) := do
    match t with
    | some text => return some { path := p, fixture := ← fixtureOf root id text, text }
    | none => return none
  let displayed ← str violation "source"
  let mut changed : List ChangedFile := []
  let mut context : List ShownFile := []
  for p in paths do
    let v := lookup vInputs p
    let f := lookup fInputs p
    if v != f then
      changed := changed ++ [{ path := p, violation := ← shown p v, fixed := ← shown p f }]
    else if v == some displayed then
      if let some s ← shown p v then context := context ++ [s]
  requireChecks [⟨s!"{id.spelling}: the violating and corrected inputs differ", !changed.isEmpty⟩]
  let request ← get violation "request"
  let project ← str request "project"
  let mode ← str violation "mode"
  let result ← get violation "result"
  let findings ← (← arr result "diagnostics").toList.mapM (findingOf project)
  requireChecks [⟨s!"{id.spelling}: the violating run reports the rule", findings.any (·.rule == id)⟩]
  let status (s : String) : IO RunStatus := match RunStatus.parse? s with
    | some st => pure st
    | none => throw <| IO.userError s!"{id.spelling}: unknown run status {s}"
  let ex : Example := {
    kind := ← str violation "kind", request := ← requestText request mode,
    violationStatus := ← status (← str result "status"), fixedStatus := ← status (← str (← get fixed "result") "status"),
    changed, context, findings }
  return (ex, { rule := id, kind := ex.kind, violationStatus := ex.violationStatus.spelling, fixedStatus := ex.fixedStatus.spelling,
                emitted := (findings.map (·.rule)).eraseDups, shard := "" })

private def writeModule (dir : FilePath) (name : String) (content : String) : IO Unit := do
  let path := dir / (System.FilePath.mk ((name.replace "." "/") ++ ".lean"))
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path content

/-- Exact relative file names and bytes of a tree. -/
def snapshotTree (root : FilePath) : IO (List (String × ByteArray)) := do
  let root ← IO.FS.realPath root
  let mut files := []
  for path in ← root.walkDir do
    if !(← path.isDir) then
      let relative := String.intercalate "/" (path.components.drop root.components.length)
      files := (relative, ← IO.FS.readBinFile path) :: files
  return files.mergeSort (fun a b => a.1 ≤ b.1)

def writeTree (destination : FilePath) (files : List (String × ByteArray)) : IO Unit := do
  for (relative, bytes) in files do
    let path := destination / relative
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile path bytes

/-- Scratch directory of the fetched site archive; its `tree/rev/<commit>/` holds each snapshot. -/
def archiveDirectory (root : FilePath) : FilePath := root / "tmp/site-archive"

/-- Fetch the site archive of the published repository with `Regula.Site.Deployment`, the same
reader the deployment gate uses, and return its snapshot commits. An absent archive branch is
the empty archive; an unreachable repository fails the build. -/
def fetchArchive (root : FilePath) : IO (List Commit) := do
  let dir := archiveDirectory root
  let fetched ← run root "lean" #["--run", "lean/Regula/Site/Deployment.lean", "archive", repository, dir.toString] cleanEnv
  requireChecks [⟨s!"site archive\n{fetched.stdout}{fetched.stderr}", fetched.exitCode == 0⟩]
  let revisions ← IO.ofExcept (fromJson? (α := List String) (← get (← readJson (dir / "archive.json")) "revisions"))
  revisions.mapM fun r => match Commit.parse? r with
    | some c => pure c
    | none => throw <| IO.userError s!"site archive: not a commit identifier: {r}"

/-- Everything generated for one build, retained for the artifact check. -/
structure Generated where
  ident : Identity
  /-- The snapshots of the site archive, in archive order. -/
  archived : List Commit
  examples : List (RuleId × Example)
  summaries : List EvidenceSummary
  shards : List Json

/-- Admit both shards and derive every rule's example. The two shards must select disjoint
rules whose union is the registry, and contain one fix and one violation record per rule. -/
def evidence (root : FilePath) (ident : Identity) (archived : List Commit) (shardPaths : List FilePath) : IO Generated := do
  let inventory ← Regula.Checker.Lake.surfaceInventory root
  let paths ← Regula.Qualification.RuleExamples.sourcePaths root (inventory.moduleSources.map Prod.snd)
  let current ← Regula.Qualification.RuleExamples.snapshot paths
  let shards ← shardPaths.mapM (admitShard root current)
  let selected ← shards.mapM fun s => do
    return (← IO.ofExcept (fromJson? (α := List String) (← get s "selected")))
  let all := selected.flatten
  requireChecks [⟨"corpus shards select every registered rule exactly once",
    all.Nodup && all.length == RuleId.all.length && RuleId.all.all (fun id => all.contains id.spelling)⟩]
  let records ← shards.flatMapM fun s => do return (← arr s "records").toList
  let producer := Regula.Checker.ResultProtocol.producer
  let mut examples := []
  let mut summaries := []
  for id in RuleId.all do
    let mine ← records.filterM fun r => return (← str r "rule") == id.spelling
    let byPhase (phase : String) : IO Json := do
      let matching ← mine.filterM fun r => return (← str r "phase") == phase
      let [r] := matching | throw <| IO.userError s!"{id.spelling}: expected exactly one {phase} record"
      let result ← get r "result"
      requireChecks [
        ⟨s!"{id.spelling}/{phase}: result toolchain {producer.toolchain}", has result "toolchain" (.str producer.toolchain)⟩,
        ⟨s!"{id.spelling}/{phase}: result producer version", has result "producerVersion" (.str producer.producerVersion)⟩,
        ⟨s!"{id.spelling}/{phase}: result source revision is this commit",
          has result "sourceRevision" (.str ident.revision.val) ||
          (ident.dirty && has result "sourceRevision" (.str (ident.revision.val ++ ":unreleased-worktree")))⟩]
      return r
    let violation ← byPhase "Violation"
    let fixed ← byPhase "Fixed"
    requireChecks [⟨s!"{id.spelling}: corrected run is a completed positive",
      has fixed "kind" (.str "positive") && has (← get fixed "result") "status" (.str "completed")⟩]
    let (ex, summary) ← exampleOf root id violation fixed
    let shard := match selected.findIdx? (·.contains id.spelling) with
      | some i => s!"{i + 1}/{shardPaths.length}" | none => "?"
    examples := examples ++ [(id, ex)]
    summaries := summaries ++ [{ summary with shard }]
  return { ident, archived, examples, summaries, shards }

/-- Generate every Verso module of the manual into `website/Generated`, with the site
stylesheet (`Regula.Site.stylesheet`) as `website/Generated/regula.css`, which the website
package copies to each edition's root. -/
def generate (root : FilePath) (g : Generated) : IO Unit := do
  let out := root / "website/Generated"
  if ← out.pathExists then IO.FS.removeDirAll out
  let top := root / "website/Generated.lean"
  IO.FS.writeFile top (← IO.ofExcept (homePage g.ident))
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "regula.css") stylesheet
  let dir := root / "website"
  writeModule dir "Generated.Rules" (← IO.ofExcept (indexPage g.ident))
  writeModule dir "Generated.Versions" (← IO.ofExcept (versionsPage g.ident g.summaries))
  writeModule dir "Generated.Credits" (← IO.ofExcept (creditsPage g.ident))
  for (id, ex) in g.examples do
    for p in (guide id).repositoryPaths do
      requireChecks [⟨s!"{id.spelling}: cited repository path exists: {p}", ← (root / p).pathExists⟩]
    -- Each cited section of the standard, on its page in the same edition (`Clause.route` is
    -- relative to the edition root, like every generated link); the artifact link check
    -- requires the anchor to exist.
    let clauses := (descriptor id).normativeClauses.map fun c =>
      ({ label := c.label, url := c.route } : Regula.Site.Clause)
    writeModule dir (ruleModule id) (← IO.ofExcept (rulePage g.ident id clauses ex))
