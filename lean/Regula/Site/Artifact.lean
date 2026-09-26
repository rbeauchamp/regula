import Regula.Site.Build

/-! # Rule-reference artifact assembly and check

Renders the generated manual with the pinned Verso package, assembles the GitHub Pages
artifact (`index.html`, `404.html`, `build.json`, `dev/`, every snapshot of the site archive
and, for a clean checkout, `rev/<commit>/`) and checks the assembled tree before it can be
uploaded.

## Main declarations

- `render`: run the website package's Verso executable (trusted process boundary).
- `assemble`: write the artifact tree; archived snapshots are copied verbatim.
- `checkArtifact`: the complete finite check of an assembled tree: size within
  `artifactBudget`, exact layout whose `rev/` children are exactly `artifactRevisions` of the
  archive and the current build, archived snapshots byte-identical to the archive,
  byte-identical current editions, one page per registered rule and no other rule route, page
  content equal to the admitted example text, every scanned link of the whole tree resolving
  under the project base path (`linkErrors_nil_iff`), and the registry's own site validator
  (`axiomGate --validate-site`) over the observed pages and emitted rule IDs.

## Retention

A published snapshot is never dropped by a later deployment: the archive is append-only (the
workflow pushes it only without force); a snapshot is archived before it is deployed (the CI
`archive` job precedes `deploy`); every deployed artifact contains every archived snapshot
(`archived_subset_artifactRevisions`, checked here against the fetched archive, again by the
deployment gate, and by the deploy job's check that the archive head is the gate's commit);
and deployments are serialized. The pure part is proved in `RegulaCore.Site`; Git, GitHub and
the workflow's ordering are trusted.

## Boundaries

The check observes files this process wrote and read back; it does not observe GitHub Pages.
Deployment is verified separately against the live site (`Regula.Site.Deployment`).
-/

namespace Regula.Site.Build

open Lean System Regula.Site Regula.Qualification

/-- Render the generated manual. The website package pins its own Verso lock; the root
package's search path is removed so the two workspaces never mix. The standard's `lean`
blocks import root-package modules that Lake does not trace for the standard's modules (their
`needs` only orders the build), so the standard's build outputs are removed first and every
example is elaborated again. Repository links of the standard name `revision`. -/
def render (root : FilePath) (destination : FilePath) (revision : String) : IO (List (String × ByteArray)) := do
  let website := root / "website"
  if ← destination.pathExists then IO.FS.removeDirAll destination
  for dir in [website / ".lake/build/lib/lean", website / ".lake/build/ir"] do
    if ← dir.pathExists then
      for entry in ← dir.readDir do
        if entry.fileName.startsWith "RegulaStandard" then
          if ← entry.path.isDir then IO.FS.removeDirAll entry.path else IO.FS.removeFile entry.path
  let built ← run website "lake" #["build"] cleanEnv
  requireChecks [⟨s!"Verso site build\n{built.stdout}{built.stderr}", built.exitCode == 0⟩]
  let rendered ← run website "lake" #["exe", "regula-site", "--output", destination.toString]
    (cleanEnv.push ("REGULA_SOURCE_REVISION", some revision))
  requireChecks [⟨s!"Verso rendering\n{rendered.stdout}{rendered.stderr}", rendered.exitCode == 0⟩]
  snapshotTree (destination / "html-multi")

private def page (title body : String) : String :=
  "<!doctype html>\n<html lang=\"en\"><head><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">" ++
  "<title>" ++ escape title ++ "</title><style>" ++ plainPageCss ++ "</style></head><body><main>" ++
  body ++ "</main></body></html>\n"

/-- The project-site root: a link (and immediate refresh) to the development edition. -/
def landing : String :=
  "<!doctype html>\n<html lang=\"en\"><head><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">" ++
  "<title>Regula rule reference</title><meta http-equiv=\"refresh\" content=\"0; url=dev/\"><link rel=\"canonical\" href=\"" ++
  siteBase ++ "dev/\"></head><body><main><h1>Regula rule reference</h1><p><a href=\"dev/\">Open the rule reference</a>.</p></main></body></html>\n"

/-- The page GitHub Pages serves for every unpublished path. Links are root-relative because
it is served at arbitrary paths. -/
def notFound (ident : Identity) : String :=
  page "Page not available — Regula" (
    "<h1>This page is not published</h1>" ++
    "<p>The address does not name a published page of the Regula rule reference.</p>" ++
    "<p>Released-version pages (<code>" ++ basePath ++ "v/…</code>) are not published because no package has been released, and revision snapshots (<code>" ++ basePath ++
    "rev/…</code>) exist only for commits whose site was published. An unavailable page is never redirected to the latest rules, whose meaning may differ from the version you linked.</p>" ++
    "<p>The explanations and checked examples of any revision are in its source on GitHub: <code>" ++ escape repository ++
    "/tree/&lt;commit&gt;/examples/rules/&lt;ID&gt;/</code> and <code>" ++ escape repository ++ "/blob/&lt;commit&gt;/lean/RegulaCore/Guide.lean</code>.</p>" ++
    "<p><a href=\"" ++ basePath ++ "dev/rules/\">Current development rule index</a>, built from commit <a href=\"" ++ escape (treeUrl ident) ++
    "\"><code>" ++ escape (shortRevision ident.revision) ++ "</code></a>.</p>")

private def shardField (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD .null

/-- The identity of one build. -/
def identityFields (g : Generated) : List (String × Json) := [
    ("schemaVersion", toJson (1 : Nat)), ("site", .str siteBase), ("revision", .str g.ident.revision.val),
    ("dirty", .bool g.ident.dirty), ("toolchain", .str g.ident.toolchain),
    ("producerVersion", .str g.ident.producerVersion), ("versoRevision", .str g.ident.versoRevision),
    ("rules", toJson (g.summaries.map fun s => Json.mkObj [
      ("id", .str s.rule.spelling), ("route", .str s.rule.route), ("helpUrl", .str (devUrl s.rule)),
      ("example", .str s.kind), ("violationStatus", .str s.violationStatus), ("fixedStatus", .str s.fixedStatus),
      ("emitted", toJson (s.emitted.map RuleId.spelling)), ("corpusShard", .str s.shard)])),
    ("evidence", toJson (g.shards.map fun s => Json.mkObj [
      ("shard", shardField s "shard"), ("attempt", shardField s "attempt"),
      ("selected", shardField s "selected")]))]

/-- The `build.json` of a revision snapshot: the identity of the build that produced it. -/
def snapshotJson (g : Generated) : Json := Json.mkObj (identityFields g)

/-- The current build's revision snapshot, if it is clean. -/
def currentSnapshot (g : Generated) : Option Commit :=
  if g.ident.dirty then none else some g.ident.revision

/-- The machine-readable identity of an artifact: the build's identity, its editions and the
archived snapshots it retains. The deployment check compares the live copy with these exact bytes. -/
def buildJson (g : Generated) : Json :=
  Json.mkObj (identityFields g ++ [
    ("editions", toJson (["dev/"] ++ (currentSnapshot g).toList.map (fun c => Edition.root (.rev c)))),
    ("archived", toJson (g.archived.map (·.val)))])

/-- Write the artifact tree: the rendered edition as `dev/`, every archived snapshot copied
verbatim from the archive, and the current clean build's snapshot unless it is archived. -/
def assemble (out : FilePath) (g : Generated) (edition : List (String × ByteArray)) (archive : FilePath) : IO Unit := do
  if ← out.pathExists then IO.FS.removeDirAll out
  IO.FS.createDirAll out
  writeTree (out / "dev") edition
  for c in g.archived do
    writeTree (out / Edition.root (.rev c)) (← snapshotTree (archive / "rev" / c.val))
  if let some c := currentSnapshot g then
    unless g.archived.contains c do
      writeTree (out / Edition.root (.rev c)) edition
      IO.FS.writeFile (out / Edition.root (.rev c) / "build.json") ((snapshotJson g).pretty ++ "\n")
  IO.FS.writeFile (out / "index.html") landing
  IO.FS.writeFile (out / "404.html") (notFound g.ident)
  IO.FS.writeFile (out / "build.json") ((buildJson g).pretty ++ "\n")

private def utf8 (path : String) (bytes : ByteArray) : IO String :=
  match String.fromUTF8? bytes with
  | some s => pure s
  | none => throw <| IO.userError s!"{path}: output is not UTF-8"

/-- Check an assembled artifact against the build that produced it and the archive it retains. -/
def checkArtifact (root out : FilePath) (g : Generated) (archive : FilePath) : IO Unit := do
  let files ← snapshotTree out
  let size := files.foldl (fun n f => n + f.2.size) 0
  requireChecks [⟨s!"artifact size {size} bytes is within the budget of {artifactBudget} bytes", size ≤ artifactBudget⟩]
  let revisions := artifactRevisions g.archived (currentSnapshot g)
  let revisionSet : Std.HashSet String := revisions.foldl (fun s c => s.insert c.val) {}
  let snapshotOf (p : String) : Option (String × String) := match p.splitOn "/" with
    | "rev" :: c :: rest@(_ :: _) => some (c, String.intercalate "/" rest)
    | _ => none
  let allowed (p : String) := p == "index.html" || p == "404.html" || p == "build.json" ||
    p.startsWith "dev/" || (snapshotOf p).any (revisionSet.contains ·.1)
  let unexpected := files.filter (fun f => !allowed f.1) |>.map (·.1)
  requireChecks [⟨s!"artifact has only the published layout and the snapshots {revisions.map (·.val)}; unexpected: {unexpected.take 5}", unexpected.isEmpty⟩]
  -- The Pages upload drops hidden files, so the checked tree must not contain any.
  let hidden := files.filter (fun f => (f.1.splitOn "/").any (·.startsWith ".")) |>.map (·.1)
  requireChecks [⟨s!"artifact has no hidden files (the Pages upload would drop them): {hidden.take 5}", hidden.isEmpty⟩]
  let dev := files.filterMap fun (p, b) => (p.dropPrefix? "dev/").map fun r => (r.toString, b)
  let mut snapshots : Std.HashMap String (Array (String × ByteArray)) := {}
  for (p, b) in files do
    if let some (c, rest) := snapshotOf p then
      snapshots := snapshots.insert c ((snapshots.getD c #[]).push (rest, b))
  for c in g.archived do
    requireChecks [⟨s!"archived snapshot rev/{c.val}/ is copied byte for byte",
      (snapshots.getD c.val #[]).toList == (← snapshotTree (archive / "rev" / c.val))⟩]
  if let some c := currentSnapshot g then
    unless g.archived.contains c do
      let snapshot := (snapshots.getD c.val #[]).toList
      requireChecks [
        ⟨"development and revision editions are byte-identical", snapshot.filter (·.1 != "build.json") == dev⟩,
        ⟨"revision snapshot records this build", snapshot.lookup "build.json" == some ((snapshotJson g).pretty ++ "\n").toUTF8⟩]
  let spellings := RuleId.all.map RuleId.spelling
  let ruleDirs := (dev.filterMap fun (p, _) => match p.splitOn "/" with
    | "rules" :: d :: _ :: _ => some d | _ => none).eraseDups
  requireChecks [⟨s!"rule routes are exactly the registry: {ruleDirs}",
    ruleDirs.all spellings.contains && spellings.all ruleDirs.contains⟩]
  let editions := if g.ident.dirty then [Edition.dev] else [Edition.dev, .rev g.ident.revision]
  for e in editions do
    for file in pageFiles e do
      requireChecks [⟨s!"rule page exists: {file}", files.any (·.1 == file)⟩]
  let mut checkedPages : List RuleId := []
  for (id, ex) in g.examples do
    let some (_, bytes) := files.find? (·.1 == Edition.dev.pageFile id) | throw <| IO.userError s!"missing page {id.spelling}"
    let html ← utf8 id.spelling bytes
    let title := id.spelling ++ ": " ++ (descriptor id).title
    let texts := ex.context.map (·.text) ++ ex.changed.flatMap (fun c =>
        (c.violation.filter (·.fixture.isSome)).toList.map (·.text) ++ (c.fixed.filter (·.fixture.isSome)).toList.map (·.text)) ++
      ex.findings.map (·.detail)
    requireChecks [
      ⟨s!"{id.spelling}: page title", html.contains title⟩,
      ⟨s!"{id.spelling}: page states its commit", html.contains g.ident.revision.val⟩,
      ⟨s!"{id.spelling}: page shows every admitted example text exactly", texts.all fun t => html.contains (escape t)⟩,
      ⟨s!"{id.spelling}: page states every required section", requiredHeadings.all (fun h => html.contains h)⟩]
    checkedPages := id :: checkedPages
  let pages ← files.mapM fun (p, bytes) => do
    if p.endsWith ".html" then return Page.ofHtml p (← utf8 p bytes) else return Page.ofOther p
  let errors := linkErrors pages
  requireChecks [⟨s!"{errors.length} unresolved link(s): {errors.take 10}", errors.isEmpty⟩]
  -- The registry's own validator over the page inventory, the pages whose example content was
  -- checked above, each rule's advertised availability and every emitted rule ID.
  let registry := out.parent.getD root / "site-registry.json"
  let artifact := out.parent.getD root / "site-artifact.json"
  let exported ← run root (root / ".lake/build/bin/axiomGate").toString #["--registry-out", registry.toString]
  requireChecks [⟨s!"registry export\n{exported.stdout}{exported.stderr}", exported.exitCode == 0⟩]
  let emitted := (g.examples.flatMap fun (_, ex) => ex.findings.map (·.rule)).eraseDups
  writeJson artifact (Json.mkObj [
    ("required", toJson (RuleId.all.map RegistryCodec.ruleJson)),
    ("emitted", toJson (emitted.map RegistryCodec.ruleJson)),
    ("pages", toJson (RuleId.all.map fun id => Json.mkObj [
      ("id", RegistryCodec.ruleJson id), ("route", toJson id.route),
      ("checkedExample", toJson (checkedPages.contains id)),
      ("advertisedEnforced", toJson ((descriptor id).availability == .existingChecker))]))])
  let validated ← run root (root / ".lake/build/bin/axiomGate").toString #["--validate-site", registry.toString, artifact.toString]
  requireChecks [⟨s!"registry site validation\n{validated.stdout}{validated.stderr}", validated.exitCode == 0⟩]
  IO.FS.removeFile registry
  IO.FS.removeFile artifact
  let recorded ← IO.FS.readFile (out / "build.json")
  requireChecks [⟨"build identity", recorded == (buildJson g).pretty ++ "\n"⟩]

/-- Complete build: read the site archive, admit evidence, generate, render, assemble and check. -/
def build (evidencePaths : List FilePath) (out : FilePath) : IO Unit := do
  -- Invalidate an earlier artifact before any step can fail.
  if ← out.pathExists then IO.FS.removeDirAll out
  let root ← rootDirectory
  let ident ← identity root
  let archived ← fetchArchive root
  let archive := archiveDirectory root / "tree"
  let g ← evidence root ident archived evidencePaths
  generate root g
  let edition ← render root (root / "tmp/site-render") ident.revision.val
  try
    assemble out g edition archive
    checkArtifact root out g archive
  catch error =>
    -- An unchecked artifact never remains where it could be served or uploaded.
    if ← out.pathExists then IO.FS.removeDirAll out
    throw error
  IO.FS.removeDirAll (root / "tmp/site-render")
  IO.FS.removeDirAll (archiveDirectory root)
  IO.println s!"site: PASS ({RuleId.all.length} rule pages per edition, {archived.length} archived snapshot(s) retained, {(← snapshotTree out).length} files, commit {ident.revision.val}{if ident.dirty then " with uncommitted changes" else ""}); artifact {out}"
  IO.println "The artifact check observes local files only; publication is verified against the deployed site."

end Regula.Site.Build
