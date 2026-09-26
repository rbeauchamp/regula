import Lean

/-! # Site archive, deployment gate and deployed rule-reference verification

Reads the site archive, gates and verifies publication of the artifact the CI `site` job
validated. It imports only Lean's core so the deployment jobs can run it with the pinned
toolchain alone:

```text
lean --run lean/Regula/Site/Deployment.lean archive REPOSITORY DIR   # used by `lake exe site build`
lean --run lean/Regula/Site/Deployment.lean gate ARTIFACT_DIR        # before archiving and deploying
lean --run lean/Regula/Site/Deployment.lean verify ARTIFACT_DIR      # after deploying
```

The site archive is the branch `site-archive-regula`. It holds only `rev/<commit>/` snapshot
directories, each with a `build.json` naming its commit. `archive` fetches its head (an absent
branch is the empty archive) and extracts it; the site builder copies every archived snapshot
into the artifact verbatim.

`gate` (in the unprivileged `deploy-gate` job) requires the artifact to be built from a clean
checkout of `GITHUB_SHA` and that commit to still be the head of `main` (`git ls-remote`), so a
re-run of an older run cannot publish over a newer revision. It fetches the archive again and
requires the artifact's `rev/` snapshots to be exactly the archived ones, byte for byte, plus
the new snapshot of `GITHUB_SHA`, which must not be archived yet. It then writes the next
archive commit (the archive head plus the new snapshot; an orphan commit when there is no
archive) as a Git bundle, and reports the parent and the new commit as job outputs. The
`archive` job pushes it without force, so a concurrent writer makes the push fail instead of
losing a snapshot, and the privileged deploy job refuses unless the archive head is that
commit and `main` is still at `GITHUB_SHA`.

`verify` requires `REGULA_PAGE_URL` to be the artifact's recorded site, the live `build.json`
to equal the artifact's bytes (retrying while the deployment propagates), every rule page of
every edition listed in `build.json` to be served with the artifact's exact bytes, the
`build.json` of every revision snapshot to be served with the artifact's bytes, and an
unpublished route to be answered with HTTP 404 and the artifact's `404.html`. It compares only
those files.

## Boundaries

These are observations at one time through `git` and `curl`, not proofs: GitHub, Pages, its
CDN and the network are external. Requests carry a per-attempt query string so that a cached
copy is unlikely to satisfy the comparison; whether the CDN keys on it is not established.
That the archive is append-only rests on the workflow pushing only without force; a
repository rule on `site-archive-regula` would enforce it for every writer.
-/

namespace Regula.Site.Deployment
open Lean System

private def fail (message : String) : IO α := throw <| IO.userError s!"deployment verification: {message}"

/-- Fetch `url` into `path`; returns the HTTP status (0 when no response). -/
def fetch (url : String) (path : FilePath) : IO Nat := do
  let out ← IO.Process.output { cmd := "curl", args := #["--silent", "--show-error", "--max-time", "60",
    "--output", path.toString, "--write-out", "%{http_code}", url] }
  return out.stdout.trimAscii.toString.toNat?.getD 0

private def field (j : Json) (key : String) : IO Json := IO.ofExcept (j.getObjVal? key)
private def str (j : Json) (key : String) : IO String := do IO.ofExcept (← field j key).getStr?

private def env (name : String) : IO String := do
  match ← IO.getEnv name with
  | some v => if v.isEmpty then fail s!"{name} is empty" else pure v
  | none => fail s!"{name} is not set"

/-! ## Site archive -/

/-- The branch that retains every revision snapshot published under the `/regula/` base path. -/
def archiveRef : String := "refs/heads/site-archive-regula"

/-- A full lowercase hexadecimal commit identifier, as `Regula.Site.IsCommit`. -/
def isCommit (s : String) : Bool :=
  s.length == 40 && s.toList.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

private def git (args : Array String) (env : Array (String × Option String) := #[]) : IO String := do
  let out ← IO.Process.output { cmd := "git", args := #["-c", "core.autocrlf=false"] ++ args, env }
  unless out.exitCode == 0 do fail s!"git {args}: {out.stderr}"
  return out.stdout

/-- Exact relative file names and bytes of a tree (empty when it does not exist). -/
def readTree (root : FilePath) : IO (List (String × ByteArray)) := do
  unless ← root.pathExists do return []
  let root ← IO.FS.realPath root
  let mut files := []
  for path in ← root.walkDir do
    if !(← path.isDir) then
      files := (String.intercalate "/" (path.components.drop root.components.length), ← IO.FS.readBinFile path) :: files
  return files.mergeSort (fun a b => a.1 ≤ b.1)

/-- A fetched archive: its head (`none` for an absent branch), its snapshot commits in path
order, the scratch Git directory holding it and the directory it is extracted to. -/
structure Archive where
  head : Option String
  revisions : List String
  gitDir : FilePath
  tree : FilePath

/-- Fetch and extract the archive of `repository` into `dir`. Refuses an archive with any
entry that is not a regular file under `rev/<commit>/`, or a snapshot whose `build.json` does
not name its own commit as a clean build. -/
def fetchArchive (repository : String) (dir : FilePath) : IO Archive := do
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDirAll (dir / "tree")
  let dir ← IO.FS.realPath dir
  let gitDir := dir / "git"
  let tree := dir / "tree"
  let _ ← git #["init", "--quiet", "--bare", gitDir.toString]
  if (← git #["ls-remote", repository, archiveRef]).trimAscii.isEmpty then
    return { head := none, revisions := [], gitDir, tree }
  let g := #["--git-dir", gitDir.toString]
  let _ ← git (g ++ #["fetch", "--quiet", "--depth=1", "--no-tags", repository, archiveRef])
  let head := (← git (g ++ #["rev-parse", "FETCH_HEAD^{commit}"])).trimAscii.toString
  let listing ← git (g ++ #["ls-tree", "-r", "-z", "--full-tree", head])
  let mut grouped : List String := []
  for entry in listing.splitOn "\x00" do
    if entry.isEmpty then continue
    let [mode, path] := entry.splitOn "\t" | fail s!"unreadable archive entry {entry}"
    unless mode.startsWith "100644 blob " do fail s!"archive entry {path} is not a regular file"
    match path.splitOn "/" with
    | "rev" :: c :: _ :: _ =>
      unless isCommit c do fail s!"archive entry {path} is not under rev/<commit>/"
      unless grouped.head? == some c do grouped := c :: grouped
    | _ => fail s!"archive entry {path} is not under rev/<commit>/"
  let revisions := grouped.reverse
  unless revisions.Nodup do fail "archive listing is not grouped by snapshot"
  let env := #[("GIT_INDEX_FILE", some (dir / "extract-index").toString)]
  let _ ← git (g ++ #["read-tree", head]) env
  let _ ← git (g ++ #["--work-tree", tree.toString, "checkout-index", "--all", "--force"]) env
  for c in revisions do
    let build ← IO.ofExcept (Json.parse (← IO.FS.readFile (tree / "rev" / c / "build.json")))
    unless (← str build "revision") == c && (← field build "dirty") == .bool false do
      fail s!"archived snapshot rev/{c}/ does not record itself as a clean build of {c}"
  return { head := some head, revisions, gitDir, tree }

/-- The snapshot directories of an artifact. -/
def snapshotDirs (artifact : FilePath) : IO (List String) := do
  unless ← (artifact / "rev").pathExists do return []
  let entries ← (artifact / "rev").readDir
  return (entries.toList.map (·.fileName)).mergeSort (· ≤ ·)

/-- Append the artifact's snapshot of `sha` to the archive: a commit whose parent is the
archive head (none for the first snapshot), written as a Git bundle of that one commit. -/
def appendSnapshot (archive : Archive) (artifact : FilePath) (sha : String) (bundle : FilePath) : IO String := do
  let g := #["--git-dir", archive.gitDir.toString]
  let env := #[("GIT_INDEX_FILE", some (archive.gitDir / "append-index").toString),
    ("GIT_AUTHOR_NAME", some "github-actions[bot]"),
    ("GIT_AUTHOR_EMAIL", some "41898282+github-actions[bot]@users.noreply.github.com"),
    ("GIT_COMMITTER_NAME", some "github-actions[bot]"),
    ("GIT_COMMITTER_EMAIL", some "41898282+github-actions[bot]@users.noreply.github.com")]
  let _ ← git (g ++ #["read-tree", archive.head.getD "--empty"]) env
  let artifact ← IO.FS.realPath artifact
  let _ ← git (g ++ #["--work-tree", artifact.toString, "add", "--force", "--", s!"rev/{sha}"]) env
  let tree := (← git (g ++ #["write-tree"]) env).trimAscii.toString
  let parent := match archive.head with | some h => #["-p", h] | none => #[]
  let commit := (← git (g ++ #["commit-tree", tree] ++ parent ++
    #["-m", s!"Archive the rule-reference snapshot of {sha}"]) env).trimAscii.toString
  let _ ← git (g ++ #["update-ref", archiveRef, commit])
  if let some parent := bundle.parent then IO.FS.createDirAll parent
  let _ ← git (g ++ #["bundle", "create", "--quiet", bundle.toString, archiveRef] ++
    (archive.head.map (fun h => #["^" ++ h])).getD #[])
  return commit

/-- Refuse to publish unless the artifact is a clean build of `GITHUB_SHA`, that commit is
still the head of `main`, and the artifact's snapshots are exactly the archive's plus the new
one; then write the next archive commit as a bundle. -/
def gate (artifact : FilePath) : IO Unit := do
  let build ← IO.ofExcept (Json.parse (← IO.FS.readFile (artifact / "build.json")))
  let sha ← env "GITHUB_SHA"
  unless (← field build "dirty") == .bool false do fail "the artifact was built from uncommitted changes"
  unless (← str build "revision") == sha do fail s!"the artifact is for {← str build "revision"}, not {sha}"
  let repository := (← env "GITHUB_SERVER_URL") ++ "/" ++ (← env "GITHUB_REPOSITORY")
  let out ← IO.Process.output { cmd := "git", args := #["ls-remote", repository, "refs/heads/main"] }
  unless out.exitCode == 0 do fail s!"cannot read the head of main: {out.stderr}"
  let head := ((out.stdout.splitOn "\t").headD "").trimAscii.toString
  unless head == sha do fail s!"main has moved to {head}; not publishing the older {sha}"
  let archive ← fetchArchive repository ("tmp" / "site-archive-gate")
  if archive.revisions.contains sha then
    fail s!"the snapshot of {sha} is already archived; the next push to main publishes it"
  let expected := (sha :: archive.revisions).mergeSort (· ≤ ·)
  let present ← snapshotDirs artifact
  unless present == expected do
    fail s!"the artifact's snapshots {present} are not the archived snapshots plus {sha}"
  for c in archive.revisions do
    unless (← readTree (artifact / "rev" / c)) == (← readTree (archive.tree / "rev" / c)) do
      fail s!"archived snapshot rev/{c}/ differs in the artifact"
  let snapshot ← IO.ofExcept (Json.parse (← IO.FS.readFile (artifact / "rev" / sha / "build.json")))
  unless (← str snapshot "revision") == sha && (← field snapshot "dirty") == .bool false do
    fail s!"rev/{sha}/build.json does not record a clean build of {sha}"
  let commit ← appendSnapshot archive artifact sha ("tmp" / "site-archive.bundle")
  let parent := archive.head.getD ""
  if let some outputs ← IO.getEnv "GITHUB_OUTPUT" then
    IO.FS.withFile outputs .append fun h => h.putStr s!"archive-parent={parent}\narchive-commit={commit}\n"
  IO.FS.removeDirAll ("tmp" / "site-archive-gate")
  IO.println s!"deployment gate: PASS (clean artifact of {sha}, the current head of main, with all {archive.revisions.length} archived snapshots unchanged); archive commit {commit} on {if parent.isEmpty then "a new archive" else parent} written to tmp/site-archive.bundle"

def run (artifact : FilePath) (pageUrl : String) : IO Unit := do
  let recorded ← IO.FS.readBinFile (artifact / "build.json")
  let build ← IO.ofExcept (Json.parse (← IO.FS.readFile (artifact / "build.json")))
  let site ← str build "site"
  let revision ← str build "revision"
  let pageUrl := if pageUrl.endsWith "/" then pageUrl else pageUrl ++ "/"
  unless pageUrl == site do fail s!"deployed at {pageUrl}, but the artifact is for {site}"
  unless (← field build "dirty") == .bool false do fail "the artifact was built from uncommitted changes"
  let scratch := artifact.parent.getD "." / "deployment-check"
  IO.FS.createDirAll scratch
  let probe := s!"?regula-deployment={revision}"
  -- The deployment is atomic; wait until the live identity is this artifact's.
  let mut matched := false
  for attempt in [1:21] do
    let status ← fetch (site ++ "build.json" ++ probe ++ s!"-{attempt}") (scratch / "build.json")
    if status == 200 then
      if (← IO.FS.readBinFile (scratch / "build.json")) == recorded then
        matched := true
        break
    IO.println s!"attempt {attempt}: live build.json is not this artifact yet (HTTP {status}); waiting"
    IO.sleep 15000
  unless matched do fail s!"the live site does not serve the artifact of {revision}"
  let editions ← IO.ofExcept ((← field build "editions").getArr?)
  let rules ← IO.ofExcept ((← field build "rules").getArr?)
  let mut checked := 0
  for edition in editions do
    let edition ← IO.ofExcept edition.getStr?
    for rule in rules do
      let route ← str rule "route"
      let file := edition ++ route ++ "index.html"
      let status ← fetch (site ++ edition ++ route ++ probe) (scratch / "page.html")
      unless status == 200 do fail s!"{file}: HTTP {status}"
      unless (← IO.FS.readBinFile (scratch / "page.html")) == (← IO.FS.readBinFile (artifact / file)) do
        fail s!"{file}: live bytes differ from the validated artifact"
      checked := checked + 1
  let snapshots ← snapshotDirs artifact
  for c in snapshots do
    let file := s!"rev/{c}/build.json"
    let status ← fetch (site ++ file ++ probe) (scratch / "snapshot.json")
    unless status == 200 do fail s!"{file}: HTTP {status}"
    unless (← IO.FS.readBinFile (scratch / "snapshot.json")) == (← IO.FS.readBinFile (artifact / file)) do
      fail s!"{file}: live bytes differ from the validated artifact"
  let status ← fetch (site ++ "v/0.0.0-unpublished/rules/RG1001/" ++ probe) (scratch / "missing.html")
  unless status == 404 do fail s!"unpublished route answered HTTP {status}, expected 404"
  unless (← IO.FS.readBinFile (scratch / "missing.html")) == (← IO.FS.readBinFile (artifact / "404.html")) do
    fail "unpublished route did not serve the artifact's not-available page"
  IO.FS.removeDirAll scratch
  IO.println s!"deployment verification: PASS ({site} serves the artifact of {revision}: build.json, {checked} rule pages, the build.json of {snapshots.length} revision snapshots, not-available page); an observation at this time, not a guarantee of availability"

end Regula.Site.Deployment

def main (args : List String) : IO UInt32 := do
  match args with
  | ["archive", repository, dir] =>
    let archive ← Regula.Site.Deployment.fetchArchive repository dir
    IO.FS.writeFile (System.FilePath.mk dir / "archive.json") ((Lean.Json.mkObj [
      ("head", match archive.head with | some h => .str h | none => .null),
      ("revisions", Lean.toJson archive.revisions)]).compress ++ "\n")
    IO.println s!"site archive: {archive.revisions.length} snapshot(s) at {archive.head.getD "an absent branch"}"
    return 0
  | ["gate", artifact] => Regula.Site.Deployment.gate artifact; return 0
  | ["verify", artifact] =>
    let some pageUrl ← IO.getEnv "REGULA_PAGE_URL" | IO.eprintln "REGULA_PAGE_URL is not set"; return 2
    Regula.Site.Deployment.run artifact pageUrl; return 0
  | _ => IO.eprintln "usage: lean --run lean/Regula/Site/Deployment.lean (archive REPOSITORY DIR | gate ARTIFACT_DIR | verify ARTIFACT_DIR)"; return 2
