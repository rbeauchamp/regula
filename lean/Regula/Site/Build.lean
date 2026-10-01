import Regula.Qualification.RuleExamples
import Regula.Checker.ResultProtocol
import RegulaCore.SiteDocs
import RegulaCore.SiteTheme

/-! # Rule-reference site builder

Operational builder of the published rule reference. It admits the rule-example corpus
evidence, generates the Verso sources from the registry (`RegulaCore.Rule`), the rule
explanations (`RegulaCore.Guide`) and the admitted records, renders them with the pinned Verso
package in `website/`, assembles the GitHub Pages artifact with the permanent edition of every
release and checks it.

## Main declarations

- `admitShard`: a corpus shard export is used only when it is `COMPLETED`, admitted by the
  proved `ruleExampleQualification` executable, and its recorded checker, corpus and
  configuration bytes equal the current sources.
- `exampleOf`: the display form of one rule's two admitted records.
- `tagState`, `downloadRelease`, `extractRelease`: the observations the release decisions
  (`labelAdmitted`, `releaseSource`, `publishable`) take: which commit, if any, a release tag
  names, whether a release's GitHub asset exists, and the permanent copy it holds.
- `build`: generation, Verso rendering, assembly and `checkArtifact`.

## Boundaries

Process, filesystem, Git, network and Verso observations are trusted operational inputs. The pure
decisions (editions, releases and routes, escaping, filters, diffs, links, page structure, colour
contrast) are proved in `RegulaCore.Edition`, `RegulaCore.Site`, `RegulaCore.SitePage`,
`RegulaCore.SiteDocs` and `RegulaCore.SiteTheme`.
Workspace paths of the
disposable qualification projects are displayed as `<example>`, `<scratch>` and `<regula>`; the
exact records remain in the corpus export this build consumed.
-/

namespace Regula.Site.Build

open Lean System Regula.Site Regula.Qualification RegulaQualification.Evidence

private def get (j : Json) (key : String) : IO Json := IO.ofExcept (field j key)
private def str (j : Json) (key : String) : IO String := IO.ofExcept (text j key)
private def arr (j : Json) (key : String) : IO (Array Json) := IO.ofExcept (array j key)
private def has (j : Json) (key : String) (value : Json) : Bool := (field j key).toOption ==
    some value

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
  let some revision := Commit.parse? head | throw <|
                                             IO.userError s!"not a commit identifier: {head}"
  let dirty := !(← git root #["status", "--porcelain", "--untracked-files=normal"]).isEmpty
  let producer := Regula.Checker.ResultProtocol.producer
  return { revision, dirty, toolchain := producer.toolchain, producerVersion :=
             producer.producerVersion,
           versoRevision := ← versoRevision root }

/-- Admit one corpus shard export: completed, admitted by the proved qualifier executable,
and recorded against exactly the current checker, corpus and configuration sources. -/
def admitShard (root : FilePath) (current : Json) (path : FilePath) : IO Json := do
  let shard ← readJson path
  requireChecks [
    ⟨s!"{path}: corpus export outcome is COMPLETED", has shard "outcome" (.str "COMPLETED")⟩,
    ⟨s!"{path}: corpus export schema 1", has shard "schemaVersion" (toJson (1 : Nat))⟩,
    ⟨s!"{path}: evidence was recorded for other checker, corpus or configuration sources than this \
      checkout",
      has shard "checkerAfter" current && has shard "checkerBefore" current⟩]
  let admitted ← run root (root / ".lake/build/bin/ruleExampleQualification").toString
      #[path.toString] cleanEnv
  requireChecks
      [⟨s!"{path}: corpus admission refused\n{admitted.stdout}{admitted.stderr}",
          admitted.exitCode == 0⟩]
  return shard

/-- Replace workspace paths of a disposable qualification project for display. -/
def displayText (project : String) (text : String) : String :=
  let scratch := (System.FilePath.mk project).parent.map (·.toString) |>.getD project
  ((text.replace (scratch ++ "/slot/root") "<regula>").replace project "<example>").replace scratch
      "<scratch>"

/-- Whether `uri` lies in the scratch directory of `project` (`Regula.Scratch.directory`), where
the checker keeps its isolated copy. -/
def inScratch (project uri : String) : Bool :=
  uri.startsWith ((Regula.Scratch.directory (System.FilePath.mk project)).toString ++ "/")

/-- Workspace-relative display path of an input of `project`, if it is one of the project's
own inputs rather than the checker's isolated copy or a documentation snippet alias. -/
def relativeInput (project uri : String) : Option String :=
  match uri.dropPrefix? (project ++ "/") with
  | some rest =>
    let rest := rest.toString
    if inScratch project uri || (uri.splitOn "#").length > 1 then none else some rest
  | none => none

/-- Every input file of one record: its sources and its configuration files (absent ones as
`none`), by workspace-relative path, with display-normalized content. -/
def inputs (record : Json) : IO (List (String × Option String)) := do
  let request ← get record "request"
  let project ← str request "project"
  let sources ← arr (← get record "before") "sources"
  let fromSources ← sources.toList.filterMapM fun s => do
    return (relativeInput project (← str s "uri")).map fun p => (p, s)
  let fromSources ← fromSources.mapM fun (p, s) => do
                                                    return (p, some
                                                        (displayText project (← str s "source")))
  let config ← IO.ofExcept
      (fromJson? (α := Array (String × Option String)) (← get request "configuration"))
  let fromConfig := config.toList.filterMap fun (uri, content) =>
    (relativeInput project uri).map fun p => (p, content.map (displayText project))
  return (fromSources ++ fromConfig).foldl
      (fun acc (p, c) => if acc.any (·.1 == p) then acc else acc ++ [(p, c)]) []

private def lookup (xs : List (String × Option String)) (p : String) : Option String :=
  (xs.find? (·.1 == p)).bind (·.2)

/-- The text Lean prints for a name a result diagnostic writes (`RegistryCodec.printedNameJson`),
or the JSON itself when it is not such a name. -/
def nameText (j : Json) : String :=
  match Regula.RegistryCodec.parsePrintedNameJson j with
  | .ok n => n.toString
  | .error _ => j.compress

private def ruleOf (s : String) : IO RuleId := do
  match RuleId.parse? s with
  | some id => pure id
  | none => throw <| IO.userError s!"unknown rule ID in evidence: {s}"

/-- Display form of one finding of a violating record. -/
def findingOf (project : String) (d : Json) : IO FindingView := do
  let rule ← ruleOf (← str d "id")
  let args ← get d "arguments"
  let (subjectKind, subject) := match field args "declaration", field args "root",
      field args "subject" with
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
          | [_, post] =>
            if inScratch project uri then post ++ " (the audit's fresh isolated copy)" else rest
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
           claim, subjectKind, subject, detail := displayText project
               (← str (← get d "arguments") "detail"), location := place }

/-- The fixture of rule `id` whose exact text is `text`, if any. -/
def fixtureOf (root : FilePath) (id : RuleId) (text : String) : IO (Option String) := do
  let folder := root / "examples/rules" / id.spelling
  let files ← (← folder.readDir).qsort (fun a b => a.fileName < b.fileName) |>.filterM fun e =>
      return !(← e.path.isDir)
  for entry in files do
    if (← IO.FS.readFile entry.path) == text then
      return some s!"examples/rules/{id.spelling}/{entry.fileName}"
  return none

/-- The audit that produced a rule-example record, as its page states it. -/
private def requestText (request : Json) : IO String := do
  let kind ← str request "kind"
  let project ← str request "project"
  let subject := displayText project (← str request "subject")
  let claim := match field request "claim" with | .ok (.str c) => c | _ => "none"
  let execution := match field request "execution" with | .ok (.str e) => e | _ => "report"
  return match kind with
    | "file" => s!"a fresh single-file audit of `{subject}` (`axiomGate --file`, claim `{claim}`, \
      execution `{execution}`)"
    | "policyNegative" => s!"a single-file policy inspection of `{subject}` that keeps Lean's \
      original compiler warning"
    | "documentation" => s!"a documentation fence audit of `{subject}`"
    | _ => s!"a fresh whole-project audit of `{subject}` (`axiomGate`)"

/-- The display form of one rule's admitted violation and fix records. -/
def exampleOf (root : FilePath) (id : RuleId) (violation fixed : Json) : IO
    (Example × EvidenceSummary) := do
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
  let result ← get violation "result"
  let findings ← (← arr result "diagnostics").toList.mapM (findingOf project)
  requireChecks
      [⟨s!"{id.spelling}: the violating run reports the rule", findings.any (·.rule == id)⟩]
  let status (s : String) : IO RunStatus := match RunStatus.parse? s with
    | some st => pure st
    | none => throw <| IO.userError s!"{id.spelling}: unknown run status {s}"
  let ex : Example := {
    kind := ← str violation "kind", request := ← requestText request,
    violationStatus := ← status (← str result "status"), fixedStatus := ← status
        (← str (← get fixed "result") "status"),
    changed, context, findings }
  return (ex,
      { rule := id, kind := ex.kind, violationStatus := ex.violationStatus.spelling, fixedStatus :=
          ex.fixedStatus.spelling,
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

/-- Write each relative file name and its bytes under `destination`, creating parent
directories; files already there that are not listed are left in place. -/
def writeTree (destination : FilePath) (files : List (String × ByteArray)) : IO Unit := do
  for (relative, bytes) in files do
    let path := destination / relative
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile path bytes

/-- The name of the GitHub release asset that holds the permanent copy of release `v`'s edition:
a gzip-compressed tar archive of that edition's files, paths relative to its root. -/
def releaseAsset (v : ReleaseVersion) : String := "regula-site-" ++ v.spelling ++ ".tar.gz"

/-- The download URL of `releaseAsset v`, attached to the release tagged `v<version>`. -/
def releaseAssetUrl (v : ReleaseVersion) : String :=
  repository ++ "/releases/download/v" ++ v.spelling ++ "/" ++ releaseAsset v

/-- Scratch directory of the fetched release copies; `<version>/` holds each extracted edition. -/
def releaseDirectory (root : FilePath) : FilePath := root / "tmp/site-releases"

/-- The commit that tag reference `ref` names in `git ls-remote` output: its peeled `^{}` line
when the tag is annotated, otherwise its own line. -/
def taggedCommit (listing ref : String) : Option String :=
  let entries := (listing.splitOn "\n").filterMap fun line => match line.splitOn "\t" with
    | [commit, name] => some (name, commit)
    | _ => none
  entries.lookup (ref ++ "^{}") <|> entries.lookup ref

/-- The state of the repository's tag `v<version>` relative to `head`: absent, naming `head`, or
naming another commit. The tag is read from the repository with `git ls-remote`, because CI
checkouts are shallow and have no tags; a failed read refuses. -/
def tagState (root : FilePath) (v : ReleaseVersion) (head : Commit) : IO TagState := do
  let listing ← git root #["ls-remote", "--tags", repository]
  return match taggedCommit listing ("refs/tags/v" ++ v.spelling) with
    | none => .absent
    | some commit => if commit == head.val then .head else .other

/-- Download release `v`'s asset into `releaseDirectory` and return whether it exists: HTTP 200
is present and 404 absent; any other answer or a failed transfer refuses. -/
def downloadRelease (root : FilePath) (v : ReleaseVersion) : IO Bool := do
  IO.FS.createDirAll (releaseDirectory root)
  let archive := releaseDirectory root / releaseAsset v
  let fetched ← run root "curl" #["--silent", "--show-error", "--location", "--max-time", "120",
    "--output", archive.toString, "--write-out", "%{http_code}", releaseAssetUrl v]
  requireChecks [⟨s!"release {v.spelling}: {releaseAssetUrl v}\n{fetched.stderr}",
    fetched.exitCode == 0⟩]
  match fetched.stdout.trimAscii.toString with
  | "200" => return true
  | "404" => return false
  | status => throw <| IO.userError s!"release {v.spelling}: {releaseAssetUrl v} answered HTTP \
      {status}"

/-- Extract the downloaded permanent copy of release `v`'s edition and return its files. Refuses
an unreadable archive, a symbolic link, a copy without a home page, and a copy whose `build.json`
does not record a clean build of `v` for this site. -/
def extractRelease (root : FilePath) (v : ReleaseVersion) : IO (List (String × ByteArray)) := do
  let dir := releaseDirectory root / v.spelling
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDirAll dir
  let archive := releaseDirectory root / releaseAsset v
  let extracted ← run root "tar" #["-xzf", archive.toString, "-C", dir.toString]
  requireChecks [⟨s!"release {v.spelling}: extract {releaseAsset v}\n{extracted.stderr}",
    extracted.exitCode == 0⟩]
  for path in ← dir.walkDir do
    requireChecks [⟨s!"release {v.spelling}: {path} is a symbolic link",
      (← path.symlinkMetadata).type != .symlink⟩]
  let files ← snapshotTree dir
  let some (_, recorded) := files.find? (·.1 == "build.json")
    | throw <| IO.userError s!"release {v.spelling}: the copy has no build.json"
  let build ← IO.ofExcept (Json.parse (← IO.ofExcept
    ((String.fromUTF8? recorded).elim (.error "build.json is not UTF-8") .ok)))
  requireChecks [
    ⟨s!"release {v.spelling}: build.json records Regula {v.spelling}",
      has build "producerVersion" (.str v.spelling)⟩,
    ⟨s!"release {v.spelling}: build.json records a clean build", has build "dirty" (.bool false)⟩,
    ⟨s!"release {v.spelling}: build.json records this site", has build "site" (.str siteBase)⟩,
    ⟨s!"release {v.spelling}: the copy has a home page", files.any (·.1 == "index.html")⟩]
  return files

/-- Everything generated for one build, retained for the artifact check. -/
structure Generated where
  /-- The identity of the build: commit, dirtiness, toolchain and producer versions. -/
  ident : Identity
  /-- Each rule's checked example, derived from its corpus records, in `RuleId.all` order. -/
  examples : List (RuleId × Example)
  /-- Each rule's evidence row, with the corpus shard that ran it, in `RuleId.all` order. -/
  summaries : List EvidenceSummary
  /-- The admitted corpus shard exports, in the order given. -/
  shards : List Json

/-- Admit both shards and derive every rule's example. The two shards must select disjoint
rules whose union is the registry, and contain one fix and one violation record per rule. -/
def evidence (root : FilePath) (ident : Identity) (shardPaths : List FilePath) : IO Generated := do
  let inventory ← Regula.Checker.Lake.surfaceInventory root
  let paths ← Regula.Qualification.RuleExamples.sourcePaths root
      (inventory.moduleSources.map Prod.snd)
  let current ← Regula.Qualification.RuleExamples.snapshot paths
  let shards ← shardPaths.mapM (admitShard root current)
  let selected ← shards.mapM fun s => do
    return (← IO.ofExcept (fromJson? (α := List String) (← get s "selected")))
  let all := selected.flatten
  requireChecks [⟨"corpus shards select every registered rule exactly once",
    all.Nodup && all.length == RuleId.all.length && RuleId.all.all
        (fun id => all.contains id.spelling)⟩]
  let records ← shards.flatMapM fun s => do return (← arr s "records").toList
  let producer := Regula.Checker.ResultProtocol.producer
  let mut examples := []
  let mut summaries := []
  for id in RuleId.all do
    let mine ← records.filterM fun r => return (← str r "rule") == id.spelling
    let byPhase (phase : String) : IO Json := do
      let matching ← mine.filterM fun r => return (← str r "phase") == phase
      let [r] := matching | throw <|
                             IO.userError s!"{id.spelling}: expected exactly one {phase} record"
      let result ← get r "result"
      requireChecks [
        ⟨s!"{id.spelling}/{phase}: result toolchain {producer.toolchain}", has result "toolchain"
            (.str producer.toolchain)⟩,
        ⟨s!"{id.spelling}/{phase}: result producer version", has result "producerVersion"
            (.str producer.producerVersion)⟩,
        ⟨s!"{id.spelling}/{phase}: result source revision is this commit",
          has result "sourceRevision" (.str ident.revision.val) ||
          (ident.dirty && has result "sourceRevision"
              (.str (ident.revision.val ++ ":unreleased-worktree")))⟩]
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
  return { ident, examples, summaries, shards }

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
  writeModule dir "Generated.Enforcement" (← IO.ofExcept (enforcementPage g.ident))
  writeModule dir "Generated.Coverage" (← IO.ofExcept (coveragePage g.ident))
  writeModule dir "Generated.Versions" (← IO.ofExcept (versionsPage g.ident))
  writeModule dir "Generated.Credits" (← IO.ofExcept (creditsPage g.ident))
  for (id, ex) in g.examples do
    for p in (guide id).repositoryPaths do
      requireChecks
          [⟨s!"{id.spelling}: cited repository path exists: {p}", ← (root / p).pathExists⟩]
    -- Each cited section of the standard, on its page in the same edition (`Clause.route` is
    -- relative to the edition root, like every generated link); the artifact link check
    -- requires the anchor to exist.
    let clauses := (descriptor id).normativeClauses.map fun c =>
      ({ label := c.label, url := c.route } : Regula.Site.Clause)
    writeModule dir (ruleModule id) (← IO.ofExcept (rulePage g.ident id clauses ex))

end Regula.Site.Build
