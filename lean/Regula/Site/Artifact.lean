import Regula.Site.Build

/-! # Rule-reference artifact assembly and check

Renders the generated manual with the pinned Verso package, assembles the GitHub Pages
artifact (`index.html`, `404.html`, `build.json`, the development edition `dev/` and the
permanent edition `v/<version>/` of every release) and checks the assembled tree before it can
be uploaded.

## Main declarations

- `render`: run the website package's Verso executable (trusted process boundary).
- `releaseSources`, `releaseCopies`: each release's edition before banners, from
  `releaseSource`: the frozen copy whenever its release asset exists, and this build's rendered
  edition only in a build of the installed release while its tag is absent or names this commit,
  before that asset exists. `buildJson` records each source, whether the tag names this commit and
  the value of `publishable` for the sources, which `Deployment gate` requires.
- `publishedCopy`: a release's published edition: its copy, with the latest-release banner
  (`outdatedBanner`, `bannerTarget`) inserted into every HTML page (`insertBanner`) when a later
  release exists.
- `assemble`: write the artifact tree.
- `checkArtifact`: the complete finite check of an assembled tree: size within
  `artifactBudget`, only the published routes (`sitePath`) with every published edition present,
  the development edition equal to the rendered one, every release edition equal to its published
  copy, one page per registered rule in the development and installed editions and no other rule
  route, page content equal to the admitted example text, every scanned link of the whole tree
  resolving under the project base path (`linkErrors_nil_iff`), and the registry's own site
  validator (`axiomGate --validate-site`) over the observed pages and emitted rule IDs.

## Boundaries

The check observes files this process wrote and read back; it does not observe GitHub Pages.
That a release's copy is the one made at its release rests on the release asset, which GitHub
stores; the build refuses a copy that does not record a clean build of that release for this
site, and a build labelled as a release whose tag names another commit (`labelAdmitted`).
Deployment is verified separately against the live site (`Regula.Site.Deployment`).
-/

namespace Regula.Site.Build

open Lean System Regula.Site Regula.Qualification

/-- Render the generated manual. The website package pins its own Verso lock; the root
package's search path is removed so the two workspaces never mix. The standard's `lean`
blocks import root-package modules that Lake does not trace for the standard's modules (their
`needs` only orders the build), so the standard's build outputs are removed first and every
example is elaborated again. Repository links of the standard name `revision`. -/
def render (root : FilePath) (destination : FilePath) (revision : String) : IO
    (List (String × ByteArray)) := do
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
  "<!doctype html>\n<html lang=\"en\"><head><meta charset=\"utf-8\"><meta name=\"viewport\" \
    content=\"width=device-width, initial-scale=1\">" ++
  "<title>" ++ escape title ++ "</title><style>" ++ plainPageCss ++ "</style></head><body><main>" ++
  body ++ "</main></body></html>\n"

/-- The project-site root: a link (and immediate refresh) to the development edition, with the
`tagline` for link previews. -/
def landing : String :=
  "<!doctype html>\n<html lang=\"en\"><head><meta charset=\"utf-8\"><meta name=\"viewport\" \
    content=\"width=device-width, initial-scale=1\">" ++
  "<title>Regula rule reference</title><meta name=\"description\" content=\"" ++ escape tagline ++
  "\"><meta property=\"og:description\" content=\"" ++ escape tagline ++
  "\"><meta http-equiv=\"refresh\" content=\"0; url=dev/\"><link rel=\"canonical\" href=\"" ++
  siteBase ++ "dev/\"></head><body><main><h1>Regula rule reference</h1><p><a href=\"dev/\">Open \
    the rule reference</a>.</p></main></body></html>\n"

/-- The page GitHub Pages serves for every unpublished path. Links are root-relative because
it is served at arbitrary paths. -/
def notFound (ident : Identity) : String :=
  page "Page not available — Regula" (
    "<h1>This page is not published</h1>" ++
    "<p>The address does not name a published page of the Regula rule reference. The site \
      publishes the development version under <code>" ++ basePath ++ "dev/</code> and the \
      permanent copy of each release under <code>" ++ basePath ++ "v/&lt;version&gt;/</code>. An \
      unavailable page is never redirected to other rules, whose meaning may differ from the \
      version you linked.</p>" ++
    "<p>The explanations and checked examples of any commit are in its source on GitHub: \
      <code>" ++ escape repository ++
    "/tree/&lt;commit&gt;/examples/rules/&lt;ID&gt;/</code> and <code>" ++ escape repository ++
        "/blob/&lt;commit&gt;/lean/RegulaCore/Guide.lean</code>.</p>" ++
    "<p><a href=\"" ++ basePath ++ "dev/rules/\">Development rule index</a> and <a href=\"" ++
        basePath ++ "dev/versions/\">versions</a>, built from commit <a href=\"" ++
        escape (treeUrl ident) ++ "\"><code>" ++ escape (shortRevision ident.revision) ++
        "</code></a>.</p>")

private def shardField (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD .null

/-- The identity of one build. -/
def identityFields (g : Generated) : List (String × Json) := [
    ("schemaVersion", toJson (2 : Nat)), ("site", .str siteBase),
    ("revision", .str g.ident.revision.val),
    ("dirty", .bool g.ident.dirty), ("toolchain", .str g.ident.toolchain),
    ("producerVersion", .str g.ident.producerVersion),
    ("versoRevision", .str g.ident.versoRevision),
    ("rules", toJson (g.summaries.map fun s => Json.mkObj [
      ("id", .str s.rule.spelling), ("route", .str s.rule.route),
      ("helpUrl", .str (helpUrl s.rule)), ("example", .str s.kind),
      ("violationStatus", .str s.violationStatus), ("fixedStatus", .str s.fixedStatus),
      ("emitted", toJson (s.emitted.map RuleId.spelling)), ("corpusShard", .str s.shard)])),
    ("evidence", toJson (g.shards.map fun s => Json.mkObj [
      ("shard", shardField s "shard"), ("attempt", shardField s "attempt"),
      ("selected", shardField s "selected")]))]

/-- The `build.json` of the installed release's edition: the identity of the build that made
that release's copy. -/
def editionJson (g : Generated) : Json := Json.mkObj (identityFields g)

/-- The machine-readable identity of an artifact: the build's identity, its published editions,
how each release's edition was obtained (`releaseSource`) and whether the build's commit is the
one the installed release's tag names, and the value of `publishable` for the sources. The
deployment check compares the live copy with these exact bytes, and `Deployment gate` refuses to
publish unless the recorded `publishable` is `true`. -/
def buildJson (g : Generated) (tag : TagState) (sources : List (ReleaseVersion × ReleaseSource)) :
    Json :=
  Json.mkObj (identityFields g ++ [("editions", toJson (published.map Edition.root)),
    ("releaseSources", toJson (sources.map fun (v, s) => Json.mkObj [
      ("version", .str v.spelling), ("source", .str s.spelling)])),
    ("headTagged", .bool (tag == .head)),
    ("publishable", .bool (publishable (sources.map (·.2))))])

private def byPath (files : List (String × ByteArray)) : List (String × ByteArray) :=
  files.mergeSort (fun a b => a.1 ≤ b.1)

/-- The source of each release's edition, oldest first (`releaseSource`), from whether its release
asset exists and the state `tag` of the installed release's tag. Refuses a release without an
asset unless this build is that release's and its tag is absent or names this commit. -/
def releaseSources (root : FilePath) (tag : TagState) :
    IO (List (ReleaseVersion × ReleaseSource)) :=
  releases.mapM fun v => do
    match releaseSource installed v (← downloadRelease root v) tag with
    | some source => return (v, source)
    | none => throw <| IO.userError s!"release {v.spelling}: its release asset does not exist \
        yet, and only the release commit renders its edition; CI on main publishes the asset once \
        the release commit passes its checks"

/-- Each release's edition before banners, oldest first, from its source: the frozen copy, or the
rendered edition with its `build.json`. -/
def releaseCopies (root : FilePath) (g : Generated) (edition : List (String × ByteArray))
    (sources : List (ReleaseVersion × ReleaseSource)) :
    IO (List (ReleaseVersion × List (String × ByteArray))) :=
  sources.mapM fun (v, source) => match source with
    | .asset => return (v, ← extractRelease root v)
    | .render =>
      return (v, byPath (edition ++ [("build.json", ((editionJson g).pretty ++ "\n").toUTF8)]))

/-- The published files of release `v`'s edition, given `copy`, its files before banners, and
`latestFiles`, the paths of the latest release's edition: the copy itself for the latest release,
and otherwise the copy with `outdatedBanner` inserted into every HTML page. -/
def publishedCopy (latestFiles : List String) (v : ReleaseVersion)
    (copy : List (String × ByteArray)) : Except String (List (String × ByteArray)) :=
  match bannerRelease v with
  | none => .ok copy
  | some l =>
    copy.mapM fun (path, bytes) => do
      unless path.endsWith ".html" do return (path, bytes)
      let some text := String.fromUTF8? bytes | throw s!"v/{v.spelling}/{path}: not UTF-8"
      let banner := outdatedBanner v l path (bannerTarget latestFiles path)
      match insertBanner text banner with
      | .ok out => return (path, out.toUTF8)
      | .error e => throw s!"v/{v.spelling}/{path}: {e}"

/-- The published editions of every release, from their copies. -/
def publishedCopies (copies : List (ReleaseVersion × List (String × ByteArray))) :
    Except String (List (ReleaseVersion × List (String × ByteArray))) :=
  let latestFiles := match latest with
    | some l => ((copies.lookup l).getD []).map (·.1)
    | none => []
  copies.mapM fun (v, copy) => return (v, ← publishedCopy latestFiles v copy)

/-- Write the artifact tree: the rendered edition as `dev/` and each release's published
edition as `v/<version>/`. -/
def assemble (out : FilePath) (g : Generated) (tag : TagState)
    (sources : List (ReleaseVersion × ReleaseSource)) (edition : List (String × ByteArray))
    (editions : List (ReleaseVersion × List (String × ByteArray))) : IO Unit := do
  if ← out.pathExists then IO.FS.removeDirAll out
  IO.FS.createDirAll out
  writeTree (out / Edition.dev.root) edition
  for (v, files) in editions do
    writeTree (out / (Edition.release v).root) files
  IO.FS.writeFile (out / "index.html") landing
  IO.FS.writeFile (out / "404.html") (notFound g.ident)
  IO.FS.writeFile (out / "build.json") ((buildJson g tag sources).pretty ++ "\n")

private def utf8 (path : String) (bytes : ByteArray) : IO String :=
  match String.fromUTF8? bytes with
  | some s => pure s
  | none => throw <| IO.userError s!"{path}: output is not UTF-8"

/-- The files of edition `e` in an artifact listing, relative to the edition root. -/
private def editionFiles (files : List (String × ByteArray)) (e : Edition) :
    List (String × ByteArray) :=
  files.filterMap fun (p, b) => (p.dropPrefix? e.root).map fun r => (r.toString, b)

/-- Check an assembled artifact against the build that produced it, its rendered edition and the
published editions of the releases. -/
def checkArtifact (root out : FilePath) (g : Generated) (tag : TagState)
    (sources : List (ReleaseVersion × ReleaseSource)) (edition : List (String × ByteArray))
    (editions : List (ReleaseVersion × List (String × ByteArray))) : IO Unit := do
  let files ← snapshotTree out
  let size := files.foldl (fun n f => n + f.2.size) 0
  requireChecks
      [⟨s!"artifact size {size} bytes is within the budget of {artifactBudget} bytes", size ≤
          artifactBudget⟩]
  let unexpected := files.filter (fun f => !sitePath f.1) |>.map (·.1)
  requireChecks
      [⟨s!"artifact has only the published routes {published.map Edition.root}; unexpected: \
        {unexpected.take 5}", unexpected.isEmpty⟩]
  -- The Pages upload drops hidden files, so the checked tree must not contain any.
  let hidden := files.filter (fun f => (f.1.splitOn "/").any (·.startsWith ".")) |>.map (·.1)
  requireChecks
      [⟨s!"artifact has no hidden files (the Pages upload would drop them): {hidden.take 5}",
          hidden.isEmpty⟩]
  let dev := editionFiles files .dev
  requireChecks [⟨"the development edition is the rendered edition", dev == edition⟩]
  for (v, published) in editions do
    requireChecks [⟨s!"v/{v.spelling}/ is the published copy of release {v.spelling}",
      editionFiles files (.release v) == published⟩]
  let spellings := RuleId.all.map RuleId.spelling
  let ruleDirs := (dev.filterMap fun (p, _) => match p.splitOn "/" with
    | "rules" :: d :: _ :: _ => some d | _ => none).eraseDups
  requireChecks [⟨s!"rule routes are exactly the registry: {ruleDirs}",
    ruleDirs.all spellings.contains && spellings.all ruleDirs.contains⟩]
  -- The installed build's help links name pages of its edition (`helpUrl_pagePath`).
  for e in [Edition.dev, installed.edition].eraseDups do
    for file in pageFiles e do
      requireChecks [⟨s!"rule page exists: {file}", files.any (·.1 == file)⟩]
  let mut checkedPages : List RuleId := []
  for (id, ex) in g.examples do
    let some (_, bytes) := files.find? (·.1 == Edition.dev.pageFile id)
      | throw <| IO.userError s!"missing page {id.spelling}"
    let html ← utf8 id.spelling bytes
    let title := id.spelling ++ ": " ++ (descriptor id).title
    let texts := ex.context.map (·.text) ++ ex.changed.flatMap (fun c =>
        (c.violation.filter (·.fixture.isSome)).toList.map (·.text) ++
        (c.fixed.filter (·.fixture.isSome)).toList.map (·.text)) ++
      ex.findings.map (·.detail)
    requireChecks [
      ⟨s!"{id.spelling}: page title", html.contains title⟩,
      ⟨s!"{id.spelling}: page states its commit", html.contains g.ident.revision.val⟩,
      ⟨s!"{id.spelling}: page shows every admitted example text exactly", texts.all fun t =>
          html.contains (escape t)⟩,
      ⟨s!"{id.spelling}: page states every required section", requiredHeadings.all
          (fun h => html.contains h)⟩]
    checkedPages := id :: checkedPages
  let pages ← files.mapM fun (p, bytes) => do
    if p.endsWith ".html" then return Page.ofHtml p (← utf8 p bytes) else return Page.ofOther p
  let errors := linkErrors pages
  requireChecks [⟨s!"{errors.length} unresolved link(s): {errors.take 10}", errors.isEmpty⟩]
  -- The registry's own validator over the page inventory, the pages whose example content was
  -- checked above and every emitted rule ID.
  let registry := out.parent.getD root / "site-registry.json"
  let artifact := out.parent.getD root / "site-artifact.json"
  let exported ← run root (root / ".lake/build/bin/axiomGate").toString
      #["--registry-out", registry.toString]
  requireChecks [⟨s!"registry export\n{exported.stdout}{exported.stderr}", exported.exitCode == 0⟩]
  let emitted := (g.examples.flatMap fun (_, ex) => ex.findings.map (·.rule)).eraseDups
  writeJson artifact (Json.mkObj [
    ("required", toJson (RuleId.all.map RegistryCodec.ruleJson)),
    ("emitted", toJson (emitted.map RegistryCodec.ruleJson)),
    ("pages", toJson (RuleId.all.map fun id => Json.mkObj [
      ("id", RegistryCodec.ruleJson id), ("route", toJson id.route),
      ("checkedExample", toJson (checkedPages.contains id))]))])
  let validated ← run root (root / ".lake/build/bin/axiomGate").toString
      #["--validate-site", registry.toString, artifact.toString]
  requireChecks
      [⟨s!"registry site validation\n{validated.stdout}{validated.stderr}",
          validated.exitCode == 0⟩]
  IO.FS.removeFile registry
  IO.FS.removeFile artifact
  let recorded ← IO.FS.readFile (out / "build.json")
  requireChecks [⟨"build identity", recorded == (buildJson g tag sources).pretty ++ "\n"⟩]

/-- Where a release build writes its edition as the release asset (`releaseAsset`). -/
def releasePackage (root : FilePath) (v : ReleaseVersion) : FilePath :=
  root / "tmp/site-release" / releaseAsset v

/-- Complete build: refuse a release label whose tag names another commit, decide each release
edition's source, admit evidence, generate, render, collect the release editions, assemble and
check. A clean build that rendered its release's edition, the release commit's before its
release is published, also writes that edition as the release asset. -/
def build (evidencePaths : List FilePath) (out : FilePath) : IO Unit := do
  -- Invalidate an earlier artifact before any step can fail.
  if ← out.pathExists then IO.FS.removeDirAll out
  let root ← rootDirectory
  let ident ← identity root
  let tag ← match installed with
    | .release v => tagState root v ident.revision
    | .unreleased => pure .absent
  requireChecks [⟨s!"a build labelled {installed.spelling} is refused once tag \
    v{installed.spelling} names another commit: only the release commit that CI on main creates \
    carries a release label, and main and pull requests keep Regula.installed .unreleased",
    labelAdmitted installed tag⟩]
  let sources ← releaseSources root tag
  let g ← evidence root ident evidencePaths
  generate root g
  let edition ← render root (root / "tmp/site-render") ident.revision.val
  let editions ← IO.ofExcept (publishedCopies (← releaseCopies root g edition sources))
  try
    assemble out g tag sources edition editions
    checkArtifact root out g tag sources edition editions
  catch error =>
    -- An unchecked artifact never remains where it could be served or uploaded.
    if ← out.pathExists then IO.FS.removeDirAll out
    throw error
  IO.FS.removeDirAll (root / "tmp/site-render")
  if ← (releaseDirectory root).pathExists then IO.FS.removeDirAll (releaseDirectory root)
  if let .release v := installed then
    if sources.any (·.2 == .render) then
      if !ident.dirty then
        let package := releasePackage root v
        if let some parent := package.parent then IO.FS.createDirAll parent
        let packed ← run root "tar" #["-czf", package.toString, "-C",
          (out / (Edition.release v).root).toString, "."]
        requireChecks [⟨s!"release asset {package}\n{packed.stderr}", packed.exitCode == 0⟩]
        IO.println s!"site: release {v.spelling}'s edition is written to {package}; CI \
          attaches it as the release asset once every check of this commit passes"
      else IO.println s!"site: release {v.spelling}'s edition is a preview rendered from \
        uncommitted changes; only a clean build writes its asset"
  IO.println s!"site: PASS ({RuleId.all.length} rule pages, editions \
    {published.map Edition.root}, {(← snapshotTree out).length} files, \
    commit {ident.revision.val}{if ident.dirty then " with uncommitted changes" else ""}); \
    artifact {out}"
  IO.println "The artifact check observes local files only; publication is verified against the \
    deployed site."

end Regula.Site.Build
