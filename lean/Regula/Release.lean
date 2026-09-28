import Lean

/-! # Release automation

The steps of a Regula release, run by the `Release` workflow (`.github/workflows/release.yml`)
with the pinned toolchain alone, so they need no build:

```text
lean --run lean/Regula/Release.lean prepare   # derive the version, create and tag the commit
lean --run lean/Regula/Release.lean publish   # attach the site edition and publish the release
lean --run lean/Regula/Release.lean record    # open the pull request that lists the release
```

A release's version is the Lean release in `lean-toolchain`, the Lean ecosystem's tag convention
(`v4.34.0` for `leanprover/lean4:v4.34.0`), so there is at most one release per supported
toolchain. `prepare` creates the release commit as a child of the `main` commit the workflow runs
on: that commit with `Regula.installed` set to the release and the release appended to
`Regula.releases` (`RegulaCore/Edition.lean`). GitHub creates and signs it, and `prepare` refuses
unless GitHub reports its signature verified; it then creates the tag `v<version>` naming it.
`main` itself never carries the release label. The workflow runs the checks of `ci.yml` on the
tagged commit, whose site build renders the release's edition as the release asset. `publish`
creates the GitHub release with the notes and that asset, published only once the asset is
attached (immutable releases then freeze both). `record` opens the pull request that appends the
release to `Regula.releases` on `main`, whose site build takes the edition from the asset, and
starts its checks.

Every step resumes: `prepare` reuses a tag without a published release and reports `record` once
the release is published, and `record` updates its branch to the current `main`. It refuses a
toolchain that is not a stable release, a version already listed on `main`, and a tag whose
commit does not carry the release label.

## Boundaries

GitHub (its API through `gh`, signing, tags, releases, pull requests and Actions) is trusted and
observed, not proved. The edit of `RegulaCore/Edition.lean` is text: `prepare` and `record` read
their own output back and refuse unless it names the intended build and releases, and the
kernel checks the edited module's theorems (`releases_ascending`, `installed_listed`) when the
workflow builds the release commit and when the record pull request's checks build it.
-/

namespace Regula.Release

open Lean System

private def fail {α : Type} (message : String) : IO α :=
  throw <| IO.userError s!"release: {message}"

/-- A release version `major.minor.patch`: the Lean release it supports. -/
structure Version where
  /-- The major version. -/
  major : Nat
  /-- The minor version. -/
  minor : Nat
  /-- The patch version. -/
  patch : Nat
  deriving DecidableEq, Repr

/-- The version as it is written, such as `4.34.0`. -/
def Version.spelling (v : Version) : String := s!"{v.major}.{v.minor}.{v.patch}"

/-- The tag of the release. -/
def Version.tag (v : Version) : String := "v" ++ v.spelling

/-- The literal `RegulaCore.Edition` writes for the version. -/
def Version.literal (v : Version) : String := s!"⟨{v.major}, {v.minor}, {v.patch}⟩"

/-- Three decimal components separated by dots, and nothing else. -/
def parseVersion (text : String) : Option Version :=
  match text.splitOn "." with
  | [a, b, c] =>
    if [a, b, c].all fun s => !s.isEmpty && s.all Char.isDigit then
      some ⟨a.toNat!, b.toNat!, c.toNat!⟩
    else none
  | _ => none

/-- The release version of a `lean-toolchain`: a stable Lean release `leanprover/lean4:vX.Y.Z`.
A release candidate or nightly toolchain has none. -/
def toolchainVersion (toolchain : String) : Option Version :=
  (toolchain.trimAscii.toString.dropPrefix? "leanprover/lean4:v").bind fun rest =>
    parseVersion rest.toString

/-- The first line of `text` that starts with `pre`, with its index. -/
private def findLine (lines : List String) (pre : String) : Option (Nat × String) :=
  (lines.zipIdx.find? fun (line, _) => line.startsWith pre).map fun (line, i) => (i, line)

/-- The build `installed` names: `none` for `.unreleased`, `some v` for `.release v`. -/
def installedOf (edition : String) : Except String (Option Version) := do
  let some (_, line) := findLine (edition.splitOn "\n") "def installed : Build := "
    | throw "RegulaCore/Edition.lean has no `def installed : Build := ` line"
  let value := (line.dropPrefix? "def installed : Build := ").map (·.toString) |>.getD ""
  if value == ".unreleased" then return none
  let some inner := (value.dropPrefix? ".release ⟨").bind (·.toString.dropSuffix? "⟩")
    | throw s!"unexpected `installed`: {value}"
  match parseVersion (inner.toString.replace ", " ".") with
  | some v => return some v
  | none => throw s!"unexpected `installed`: {value}"

/-- The releases `releases` lists, in order: the literals between `[` and `]` of the definition,
which spans the lines from `def releases` to the next blank line. -/
def releasesOf (edition : String) : Except String (List Version) := do
  let lines := edition.splitOn "\n"
  let some (start, _) := findLine lines "def releases : List ReleaseVersion :="
    | throw "RegulaCore/Edition.lean has no `def releases : List ReleaseVersion :=` line"
  let span := (lines.drop start).takeWhile (!·.trimAscii.isEmpty)
  let text := " ".intercalate span
  let some body := (text.splitOn "[")[1]? | throw "`releases` is not a list literal"
  let some inner := (body.splitOn "]").head? | throw "`releases` is not a list literal"
  let items := (inner.splitOn "⟨").drop 1
  items.mapM fun item => do
    let some literal := (item.splitOn "⟩").head? | throw s!"unexpected release literal {item}"
    match parseVersion (literal.replace ", " ".") with
    | some v => return v
    | none => throw s!"unexpected release literal {literal}"

/-- `RegulaCore/Edition.lean` with `installed` set to `build` (`none` for `.unreleased`) and
`releases` set to `versions`, written on one line when it fits in 100 characters. -/
def withEdition (edition : String) (build : Option Version) (versions : List Version) :
    Except String String := do
  let lines := edition.splitOn "\n"
  let some (installedAt, _) := findLine lines "def installed : Build := "
    | throw "RegulaCore/Edition.lean has no `def installed` line"
  let some (releasesAt, _) := findLine lines "def releases : List ReleaseVersion :="
    | throw "RegulaCore/Edition.lean has no `def releases` line"
  let span := ((lines.drop releasesAt).takeWhile (!·.trimAscii.isEmpty)).length
  let installedLine := "def installed : Build := " ++
    (match build with | none => ".unreleased" | some v => ".release " ++ v.literal)
  let literals := versions.map (·.literal)
  let oneLine := "def releases : List ReleaseVersion := [" ++ ", ".intercalate literals ++ "]"
  -- Otherwise the list starts on the next line, each line filled to at most 100 characters.
  let wrapped := literals.zipIdx.foldl (init := ([] : List String)) fun acc (lit, i) =>
    let piece := lit ++ (if i + 1 == literals.length then "]" else ",")
    match acc with
    | [] => ["  [" ++ piece]
    | last :: rest =>
      if (last ++ " " ++ piece).length ≤ 100 then (last ++ " " ++ piece) :: rest
      else ("   " ++ piece) :: last :: rest
  let releaseLines := if oneLine.length ≤ 100 then [oneLine]
    else "def releases : List ReleaseVersion :=" :: wrapped.reverse
  let rewritten := (lines.set installedAt installedLine).zipIdx.flatMap fun (line, i) =>
    if i == releasesAt then releaseLines
    else if releasesAt < i && i < releasesAt + span then []
    else [line]
  let result := "\n".intercalate rewritten
  -- Read the edit back: it must name exactly the intended build and releases.
  unless (← installedOf result) == build && (← releasesOf result) == versions do
    throw "the edited RegulaCore/Edition.lean does not read back as intended"
  return result

/-! ## GitHub -/

/-- The repository `owner/name` the workflow runs in. -/
private def repository : IO String := do
  match ← IO.getEnv "GITHUB_REPOSITORY" with
  | some r => if r.isEmpty then fail "GITHUB_REPOSITORY is empty" else pure r
  | none => fail "GITHUB_REPOSITORY is not set"

private def env (name : String) : IO String := do
  match ← IO.getEnv name with
  | some v => if v.isEmpty then fail s!"{name} is empty" else pure v
  | none => fail s!"{name} is not set"

/-- Run `gh` with `args`; its standard output, or a failure with its standard error. -/
private def gh (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := "gh", args }
  unless out.exitCode == 0 do fail s!"gh {args}: {out.stderr}"
  return out.stdout

/-- `gh api` with the JSON `body` sent as the request. -/
private def ghPost (method path : String) (body : Json) : IO Json := do
  IO.FS.createDirAll "tmp"
  let file : FilePath := "tmp/release-request.json"
  IO.FS.writeFile file body.compress
  let out ← gh #["api", "--method", method, path, "--input", file.toString]
  IO.FS.removeFile file
  IO.ofExcept (Json.parse out)

private def ghGet (path : String) : IO Json := do
  IO.ofExcept (Json.parse (← gh #["api", path]))

private def str (j : Json) (key : String) : IO String := IO.ofExcept (j.getObjValAs? String key)

/-- The commit tag `tag` names, if the tag exists (peeling an annotated tag). -/
def taggedCommit (repo tag : String) : IO (Option String) := do
  let refs ← ghGet s!"repos/{repo}/git/matching-refs/tags/{tag}"
  let refs ← IO.ofExcept refs.getArr?
  let some ref ← refs.findM? (fun r => return (← str r "ref") == s!"refs/tags/{tag}")
    | return none
  let object ← IO.ofExcept (ref.getObjVal? "object")
  let sha ← str object "sha"
  if (← str object "type") == "tag" then
    return some (← str (← IO.ofExcept ((← ghGet s!"repos/{repo}/git/tags/{sha}").getObjVal?
      "object")) "sha")
  return some sha

/-- The release of `tag` among all releases (drafts included), if any. -/
def releaseOf (repo tag : String) : IO (Option Json) := do
  let pages ← gh #["api", "--paginate", "--slurp", s!"repos/{repo}/releases?per_page=100"]
  let pages ← IO.ofExcept ((← IO.ofExcept (Json.parse pages)).getArr?)
  for page in pages do
    for release in ← IO.ofExcept page.getArr? do
      if (← str release "tag_name") == tag then return some release
  return none

/-- `RegulaCore/Edition.lean` at commit `sha`. -/
def editionAt (repo sha : String) : IO String :=
  gh #["api", "-H", "Accept: application/vnd.github.raw",
    s!"repos/{repo}/contents/lean/RegulaCore/Edition.lean?ref={sha}"]

/-- A commit with parent `parent` whose tree is `parent`'s with `Edition.lean` replaced by
`edition`, created and signed by GitHub; refused unless GitHub reports the signature verified. -/
def editionCommit (repo parent edition message : String) : IO String := do
  let blob ← ghPost "POST" s!"repos/{repo}/git/blobs"
    (Json.mkObj [("content", edition), ("encoding", "utf-8")])
  let base ← ghGet s!"repos/{repo}/git/commits/{parent}"
  let baseTree ← str (← IO.ofExcept (base.getObjVal? "tree")) "sha"
  let tree ← ghPost "POST" s!"repos/{repo}/git/trees" (Json.mkObj [
    ("base_tree", baseTree),
    ("tree", Json.arr #[Json.mkObj [("path", "lean/RegulaCore/Edition.lean"),
      ("mode", "100644"), ("type", "blob"), ("sha", ← str blob "sha")]])])
  let commit ← ghPost "POST" s!"repos/{repo}/git/commits" (Json.mkObj [
    ("message", message), ("tree", ← str tree "sha"), ("parents", Json.arr #[parent])])
  let sha ← str commit "sha"
  let verified := (commit.getObjValD "verification").getObjValD "verified"
  unless verified == .bool true do
    fail s!"GitHub did not verify the signature of the release commit {sha}"
  return sha

/-- Append `key=value` to the step outputs file `GITHUB_OUTPUT`. -/
private def output (key value : String) : IO Unit := do
  let path ← env "GITHUB_OUTPUT"
  let handle ← IO.FS.Handle.mk path .append
  handle.putStrLn s!"{key}={value}"

/-! ## Steps -/

/-- Derive the version, then create and tag the release commit, or resume: writes the outputs
`version`, `commit` (the tagged commit) and `stage` (`build`, or `record` once the release is
published). -/
def prepare : IO Unit := do
  let repo ← repository
  let head ← env "GITHUB_SHA"
  let toolchain ← IO.FS.readFile "lean-toolchain"
  let some v := toolchainVersion toolchain
    | fail s!"lean-toolchain is {toolchain.trimAscii}; a release needs a stable Lean release"
  let tag := v.tag
  output "version" v.spelling
  if let some release ← releaseOf repo tag then
    if !(release.getObjValD "draft" == .bool true) then
      IO.println s!"release {tag} is published; recording it on main"
      output "commit" ((← taggedCommit repo tag).getD "")
      output "stage" "record"
      return
  if let some commit ← taggedCommit repo tag then
    let installed ← IO.ofExcept (installedOf (← editionAt repo commit))
    unless installed == some v do
      fail s!"tag {tag} names {commit}, whose RegulaCore/Edition.lean does not install {tag}"
    IO.println s!"tag {tag} names the release commit {commit}; resuming"
    output "commit" commit
    output "stage" "build"
    return
  let edition ← IO.FS.readFile "lean/RegulaCore/Edition.lean"
  unless (← IO.ofExcept (installedOf edition)) == none do
    fail "main's RegulaCore/Edition.lean is not unreleased"
  let listed ← IO.ofExcept (releasesOf edition)
  if listed.contains v then fail s!"{tag} is already listed in main's Regula.releases"
  let released ← IO.ofExcept (withEdition edition (some v) (listed ++ [v]))
  let commit ← editionCommit repo head released
    s!"release: Regula {tag} for Lean {tag}\n\nSets Regula.installed to the release and appends \
      it to Regula.releases; the tag {tag} names this commit, a child of {head} on main."
  discard <| ghPost "POST" s!"repos/{repo}/git/refs"
    (Json.mkObj [("ref", s!"refs/tags/{tag}"), ("sha", commit)])
  IO.println s!"created the release commit {commit} and tagged it {tag}"
  output "commit" commit
  output "stage" "build"

/-- The release notes written above GitHub's generated list of changes. -/
def notes (v : Version) (repo : String) : String :=
  let tag := v.tag
  s!"Regula {tag} supports Lean {tag} (`leanprover/lean4:{tag}`), its only supported toolchain.\n\n\
    Require it in `lakefile.toml`:\n\n\
    ```toml\n[[require]]\nname = \"regula\"\ngit = \"https://github.com/{repo}\"\nrev = \"{tag}\"\n\
    ```\n\n\
    or in `lakefile.lean`: `require regula from git \"https://github.com/{repo}\" @ \"{tag}\"`. \
    Set `lean-toolchain` to `leanprover/lean4:{tag}`, then run `lake update regula`, \
    `lake exe regula init` and `lake lint`. To update from an earlier release, change the tag \
    and `lean-toolchain`, run `lake update regula`, and run `lake exe regula init` again: it \
    rewrites only what the new release changes.\n\n\
    The rule reference of this release is https://rbeauchamp.github.io/regula/v/{v.spelling}/; \
    `regula-site-{v.spelling}.tar.gz` is its permanent copy.\n"

/-- Attach the release edition the checks wrote and publish the release of the tagged commit. -/
def publish : IO Unit := do
  let repo ← repository
  let some v := parseVersion (← env "RELEASE_VERSION") | fail "RELEASE_VERSION is not a version"
  let commit ← env "RELEASE_COMMIT"
  let tag := v.tag
  unless (← taggedCommit repo tag) == some commit do fail s!"tag {tag} does not name {commit}"
  let asset : FilePath := s!"tmp/site-release/regula-site-{v.spelling}.tar.gz"
  unless ← asset.pathExists do fail s!"the checks wrote no release edition {asset}"
  if let some release ← releaseOf repo tag then
    unless release.getObjValD "draft" == .bool true do
      IO.println s!"release {tag} is already published"
      return
    -- An unpublished draft of an earlier attempt; publishing starts again from the notes.
    let id ← IO.ofExcept (release.getObjValAs? Nat "id")
    discard <| gh #["api", "--method", "DELETE", s!"repos/{repo}/releases/{id}"]
  IO.FS.createDirAll "tmp"
  IO.FS.writeFile "tmp/release-notes.md" (notes v repo)
  -- `gh` creates the release as a draft, uploads the asset, then publishes it.
  discard <| gh #["release", "create", tag, asset.toString, "--repo", repo, "--verify-tag",
    "--title", s!"Regula {tag}", "--notes-file", "tmp/release-notes.md", "--generate-notes",
    "--latest"]
  let some release ← releaseOf repo tag | fail s!"release {tag} was not created"
  let assets ← IO.ofExcept ((release.getObjValD "assets").getArr?)
  unless release.getObjValD "draft" == .bool false &&
      (← assets.anyM fun a => return (← str a "name") == s!"regula-site-{v.spelling}.tar.gz") do
    fail s!"release {tag} is not published with its site asset"
  IO.println s!"published release {tag} with regula-site-{v.spelling}.tar.gz"

/-- Open (or update) the pull request that appends the release to `Regula.releases` on `main`,
and start its checks. -/
def record : IO Unit := do
  let repo ← repository
  let some v := parseVersion (← env "RELEASE_VERSION") | fail "RELEASE_VERSION is not a version"
  let tag := v.tag
  let main ← str (← IO.ofExcept ((← ghGet s!"repos/{repo}/git/ref/heads/main").getObjVal?
    "object")) "sha"
  let edition ← editionAt repo main
  unless (← IO.ofExcept (installedOf edition)) == none do
    fail "main's RegulaCore/Edition.lean is not unreleased"
  let listed ← IO.ofExcept (releasesOf edition)
  if listed.contains v then
    IO.println s!"{tag} is already listed in main's Regula.releases; nothing to record"
    return
  let recorded ← IO.ofExcept (withEdition edition none (listed ++ [v]))
  let commit ← editionCommit repo main recorded
    s!"release: record Regula {tag}\n\nAppends {tag} to Regula.releases, so every deployment \
      publishes its permanent edition from the release asset; Regula.installed stays unreleased."
  let branch := s!"release/{tag}"
  let existing ← ghGet s!"repos/{repo}/git/matching-refs/heads/{branch}"
  let exists_ := (← IO.ofExcept existing.getArr?).any fun r =>
    r.getObjValD "ref" == .str s!"refs/heads/{branch}"
  if exists_ then
    discard <| ghPost "PATCH" s!"repos/{repo}/git/refs/heads/{branch}"
      (Json.mkObj [("sha", commit), ("force", true)])
  else
    discard <| ghPost "POST" s!"repos/{repo}/git/refs"
      (Json.mkObj [("ref", s!"refs/heads/{branch}"), ("sha", commit)])
  -- A pull request opened with the workflow's token starts no workflow; dispatch the checks.
  discard <| gh #["workflow", "run", "ci.yml", "--repo", repo, "--ref", branch]
  let owner := (repo.splitOn "/").head!
  let open_ ← ghGet s!"repos/{repo}/pulls?state=open&head={owner}:{branch}"
  if (← IO.ofExcept open_.getArr?).isEmpty then
    let created ← IO.Process.output { cmd := "gh", args := #["pr", "create", "--repo", repo,
      "--base", "main", "--head", branch,
      "--title", s!"release: record Regula {tag}",
      "--body", s!"Appends {tag} to `Regula.releases`. The release {tag} is published with its \
        site edition as a release asset; once this merges, every deployment serves \
        https://rbeauchamp.github.io/regula/v/{v.spelling}/ from that asset. \
        `Regula.installed` stays unreleased on main.\n\nOpened by the Release workflow, which \
        also started this branch's checks (checks do not start on their own for a pull request \
        the workflow opens)."] }
    unless created.exitCode == 0 do
      -- The repository setting "Allow GitHub Actions to create and approve pull requests" is
      -- off: the release is published and its branch checked, but the pull request is not open.
      fail s!"could not open the pull request ({created.stderr.trimAscii}). Open it from \
        https://github.com/{repo}/compare/main...{branch}?expand=1, or turn on the repository \
        setting that lets GitHub Actions create pull requests and re-run this workflow"
  IO.println s!"recorded {tag} on branch {branch} ({commit}); its pull request awaits review"

end Regula.Release

/-- Command line of `lean --run lean/Regula/Release.lean`: `prepare`, `publish` or `record`;
returns 2 on a usage error. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["prepare"] => Regula.Release.prepare; return 0
  | ["publish"] => Regula.Release.publish; return 0
  | ["record"] => Regula.Release.record; return 0
  | _ => IO.eprintln "usage: lean --run lean/Regula/Release.lean (prepare | publish | record)"
         return 2
