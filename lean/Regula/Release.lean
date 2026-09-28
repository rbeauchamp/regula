import Lean

/-! # Release automation

The steps of a Regula release, run with the pinned toolchain alone, so they need no build. The
`Release` workflow (`.github/workflows/release.yml`) runs the first; `ci.yml` runs the others on
`main`:

```text
lean --run lean/Regula/Release.lean open       # open the release pull request
lean --run lean/Regula/Release.lean installed  # the release this commit installs, if any
lean --run lean/Regula/Release.lean tag        # tag the release commit v<version>
lean --run lean/Regula/Release.lean publish    # attach the site edition and publish the release
lean --run lean/Regula/Release.lean reset      # open the pull request that ends the release
```

A release's version is the Lean release in `lean-toolchain`, the Lean ecosystem's tag convention
(`v4.34.0` for `leanprover/lean4:v4.34.0`), so there is at most one release per supported
toolchain. `open` creates the release commit as a child of the `main` commit the workflow runs
on: that commit with `Regula.installed` set to the release, the release appended to
`Regula.releases` (`RegulaCore/Edition.lean`), and the release stamped into every rule lifecycle
position still `.unreleased` (`RegulaCore/Rule.lean`, `stampRules`). GitHub creates and
signs it, and `open` refuses unless GitHub reports its signature verified; it then opens its pull
request, which merges through normal review. On `main`, once acceptance and the rule-example
shards pass on a commit that carries the release label, `tag` names it `v<version>`
(`tagAction`), so its site build renders the release's edition, deploys it and keeps it as the
release asset. Once the deployment is verified, `publish` creates the GitHub release with the
notes and that asset of the commit the tag names, published only once the asset is attached
(immutable releases then freeze both), and `reset` opens the pull request that sets
`Regula.installed` back to `.unreleased`.

Other pull requests still merge during a release. A release is cut from whichever labelled head
of `main` first completes the whole chain: until the release is published, `tag` creates the tag
at the head of `main` or moves it there (`tagAction_converges`), so a re-run of CI on `main`
recovers from a run that a later merge cancelled. Once it is published, `tag` never changes the
tag (`tagAction_published`) and refuses every other commit that still carries the label, after
making sure the reset pull request is open; the site build refuses them too.

Every step resumes: `open` updates its branch and keeps an open pull request, `reset` leaves an
open reset pull request alone unless it conflicts with `main`, `tag` keeps a tag that already
names the commit, and `publish` replaces an unpublished draft and skips a published release. They
refuse a toolchain that is not a stable release, a version already listed or tagged when the
release opens, and a stale run whose commit is no longer the head of `main` unless the tag already
names it.

## Boundaries

GitHub (its API through `gh`, signing, tags, releases, pull requests and Actions) is trusted and
observed, not proved. `tagAction` is the decision the tag step executes, and its theorems are
checked by the kernel each time `lean --run` elaborates this file; what the step observes
(whether the release is published, the head of `main`, the tag) and the tag write are GitHub's.
The edits of `RegulaCore/Edition.lean` and `RegulaCore/Rule.lean` are text: `open` and `reset`
read their edit of `Edition.lean` back and refuse unless it names the intended build and
releases, and the kernel checks the edited modules' theorems (`releases_ascending`,
`installed_listed`, `release_attributes_rules`, `lifecycle_listed`) when each pull request's
checks build them.
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

/-- The literal `RegulaCore.Edition` and `RegulaCore.Rule` write for the version. -/
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

/-- `RegulaCore/Rule.lean` with every `.unreleased` on a line that starts `lifecycle :=` replaced
by release `v`: the introduction of each new rule and the retirement of each newly retired one.
A convenience, not a check: `release_attributes_rules` is what refuses a release build in which
any lifecycle position is still `.unreleased`, however it is written. -/
def stampRules (rules : String) (v : Version) : String :=
  "\n".intercalate <| (rules.splitOn "\n").map fun line =>
    if line.trimAsciiStart.toString.startsWith "lifecycle :=" then
      line.replace ".unreleased" s!"(.release {v.literal})"
    else line

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

/-! ## The tag decision

A release is cut from whichever release-labelled head of `main` first completes the whole chain.
While the release is unpublished (no GitHub release, or only a draft), the tag step creates tag
`v<version>` at the commit it runs on, or moves it there, provided that commit is still the head
of `main`; once the release is published, the tag never changes, and every other commit that
carries the release label is refused. -/

/-- Where tag `v<version>` points, relative to the commit the tag step runs on: the three cases
of the site build's `Regula.TagState`. -/
inductive Tag where
  /-- The tag does not exist. -/
  | absent
  /-- The tag names this commit. -/
  | head
  /-- The tag names another commit. -/
  | other
  deriving DecidableEq, Repr

/-- What the tag step does with tag `v<version>`. -/
inductive TagAction where
  /-- Create the tag at this commit. -/
  | create
  /-- Move the tag from another commit to this one. -/
  | move
  /-- Leave the tag, which already names this commit. -/
  | keep
  /-- Change nothing and fail. -/
  | refuse
  deriving DecidableEq, Repr

/-- The tag step's decision, given whether the release is `published`, whether this commit is the
`current` head of `main`, and the state of the tag. -/
def tagAction (published current : Bool) : Tag → TagAction
  | .head => .keep
  | .absent => if !published && current then .create else .refuse
  | .other => if !published && current then .move else .refuse

/-- The step creates the tag exactly for the head of `main` of an unpublished release without
one. -/
theorem tagAction_create_iff (published current : Bool) (tag : Tag) :
    tagAction published current tag = .create ↔
      published = false ∧ current = true ∧ tag = .absent := by
  cases published <;> cases current <;> cases tag <;> decide

/-- The step moves the tag exactly to the head of `main` of an unpublished release whose tag names
another commit. -/
theorem tagAction_move_iff (published current : Bool) (tag : Tag) :
    tagAction published current tag = .move ↔
      published = false ∧ current = true ∧ tag = .other := by
  cases published <;> cases current <;> cases tag <;> decide

/-- The step keeps the tag exactly when it already names this commit. -/
theorem tagAction_keep_iff (published current : Bool) (tag : Tag) :
    tagAction published current tag = .keep ↔ tag = .head := by
  cases published <;> cases current <;> cases tag <;> decide

/-- The step refuses exactly when the tag does not name this commit and the release is published
or this commit is no longer the head of `main`. -/
theorem tagAction_refuse_iff (published current : Bool) (tag : Tag) :
    tagAction published current tag = .refuse ↔
      tag ≠ .head ∧ (published = true ∨ current = false) := by
  cases published <;> cases current <;> cases tag <;> decide

/-- Once the release is published, the step never writes the tag. -/
theorem tagAction_published (current : Bool) (tag : Tag) :
    tagAction true current tag = .keep ∨ tagAction true current tag = .refuse := by
  cases current <;> cases tag <;> decide

/-- While the release is unpublished, the step on the head of `main` never refuses: the tag then
names that commit. -/
theorem tagAction_converges (tag : Tag) : tagAction false true tag ≠ .refuse := by
  cases tag <;> decide

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

/-- A commit with parent `parent` whose tree is `parent`'s with each `(path, content)` of `files`
replacing that file, created and signed by GitHub; refused unless GitHub reports the signature
verified. -/
def filesCommit (repo parent : String) (files : List (String × String)) (message : String) :
    IO String := do
  let entries ← files.mapM fun (path, content) => do
    let blob ← ghPost "POST" s!"repos/{repo}/git/blobs"
      (Json.mkObj [("content", content), ("encoding", "utf-8")])
    return Json.mkObj [("path", path), ("mode", "100644"), ("type", "blob"),
      ("sha", ← str blob "sha")]
  let base ← ghGet s!"repos/{repo}/git/commits/{parent}"
  let baseTree ← str (← IO.ofExcept (base.getObjVal? "tree")) "sha"
  let tree ← ghPost "POST" s!"repos/{repo}/git/trees" (Json.mkObj [
    ("base_tree", baseTree), ("tree", Json.arr entries.toArray)])
  let commit ← ghPost "POST" s!"repos/{repo}/git/commits" (Json.mkObj [
    ("message", message), ("tree", ← str tree "sha"), ("parents", Json.arr #[parent])])
  let sha ← str commit "sha"
  let verified := (commit.getObjValD "verification").getObjValD "verified"
  unless verified == .bool true do
    fail s!"GitHub did not verify the signature of the commit {sha}"
  return sha

/-- A signed commit on `parent` that replaces `RegulaCore/Edition.lean` with `edition`. -/
def editionCommit (repo parent edition message : String) : IO String :=
  filesCommit repo parent [("lean/RegulaCore/Edition.lean", edition)] message

/-- The commit `main` names now. -/
private def mainHead (repo : String) : IO String := do
  str (← IO.ofExcept ((← ghGet s!"repos/{repo}/git/ref/heads/main").getObjVal? "object")) "sha"

/-- Point `branch` at `commit`, start `ci.yml` on it, and open its pull request with `title` and
`body` unless one is open. A pull request opened with a workflow's token starts no workflow,
hence the dispatch. GitHub opens it only when the repository lets GitHub Actions create pull
requests; otherwise this fails with the link that opens it. -/
private def proposeBranch (repo branch commit title body : String) : IO Unit := do
  let existing ← ghGet s!"repos/{repo}/git/matching-refs/heads/{branch}"
  let exists_ := (← IO.ofExcept existing.getArr?).any fun r =>
    r.getObjValD "ref" == .str s!"refs/heads/{branch}"
  if exists_ then
    discard <| ghPost "PATCH" s!"repos/{repo}/git/refs/heads/{branch}"
      (Json.mkObj [("sha", commit), ("force", true)])
  else
    discard <| ghPost "POST" s!"repos/{repo}/git/refs"
      (Json.mkObj [("ref", s!"refs/heads/{branch}"), ("sha", commit)])
  discard <| gh #["workflow", "run", "ci.yml", "--repo", repo, "--ref", branch]
  let owner := (repo.splitOn "/").head!
  let open_ ← ghGet s!"repos/{repo}/pulls?state=open&head={owner}:{branch}"
  if (← IO.ofExcept open_.getArr?).isEmpty then
    let created ← IO.Process.output { cmd := "gh", args := #["pr", "create", "--repo", repo,
      "--base", "main", "--head", branch, "--title", title, "--body", body] }
    unless created.exitCode == 0 do
      fail s!"could not open the pull request ({created.stderr.trimAscii}). Open it from \
        https://github.com/{repo}/compare/main...{branch}?expand=1, or turn on the repository \
        setting that lets GitHub Actions create pull requests and re-run this job"
  IO.println s!"branch {branch} names {commit}; its pull request awaits review"

/-- The open pull request from `branch`, with the details GitHub computes for one pull request
(such as `mergeable`, which is `null` until GitHub has computed it), if there is one. -/
private def openPull (repo branch : String) : IO (Option Json) := do
  let owner := (repo.splitOn "/").head!
  let pulls ← IO.ofExcept
    (← ghGet s!"repos/{repo}/pulls?state=open&head={owner}:{branch}").getArr?
  let some pull := pulls[0]? | return none
  let number ← IO.ofExcept (pull.getObjValAs? Nat "number")
  return some (← ghGet s!"repos/{repo}/pulls/{number}")

/-- Append `key=value` to the step outputs file `GITHUB_OUTPUT`. -/
private def output (key value : String) : IO Unit := do
  let path ← env "GITHUB_OUTPUT"
  let handle ← IO.FS.Handle.mk path .append
  handle.putStrLn s!"{key}={value}"

/-! ## Steps -/

/-- `RegulaCore/Edition.lean` in the checkout. -/
private def editionFile : FilePath := "lean/RegulaCore/Edition.lean"

/-- `RegulaCore/Rule.lean` in the checkout. -/
private def rulesFile : FilePath := "lean/RegulaCore/Rule.lean"

/-- The release the checked-out commit installs; `none` when it is unreleased. -/
private def installedHere : IO (Option Version) := do
  IO.ofExcept (installedOf (← IO.FS.readFile editionFile))

/-- Open the release pull request: a commit on the `main` commit the workflow runs on that sets
`Regula.installed` to the release of `lean-toolchain`, appends it to `Regula.releases` and
stamps it into every rule lifecycle position still `.unreleased` (`stampRules`). Refuses a
version already tagged or listed, and a `main` that still installs a release. -/
def openRelease : IO Unit := do
  let repo ← repository
  let head ← env "GITHUB_SHA"
  let toolchain ← IO.FS.readFile "lean-toolchain"
  let some v := toolchainVersion toolchain
    | fail s!"lean-toolchain is {toolchain.trimAscii}; a release needs a stable Lean release"
  let tag := v.tag
  if let some commit ← taggedCommit repo tag then
    fail s!"tag {tag} already names {commit}; the next release needs the next Lean release"
  let edition ← IO.FS.readFile editionFile
  unless (← IO.ofExcept (installedOf edition)) == none do
    fail "main's Regula.installed is a release: merge that release's reset pull request first"
  let listed ← IO.ofExcept (releasesOf edition)
  if listed.contains v then fail s!"{tag} is already listed in main's Regula.releases"
  let released ← IO.ofExcept (withEdition edition (some v) (listed ++ [v]))
  let rules := stampRules (← IO.FS.readFile rulesFile) v
  let commit ← filesCommit repo head
    [(editionFile.toString, released), (rulesFile.toString, rules)]
    s!"release: Regula {tag} for Lean {tag}\n\nSets Regula.installed to the release, appends \
      it to Regula.releases and stamps it into every rule lifecycle position still \
      unreleased. Once this is on main, CI tags it {tag}, deploys its edition, \
      publishes the release and opens the pull request that sets Regula.installed back to \
      .unreleased."
  proposeBranch repo s!"release/{tag}" commit s!"release: Regula {tag}"
    s!"Releases Regula {tag} for Lean {tag}: sets `Regula.installed` to the release, appends \
      it to `Regula.releases` and stamps it into every rule lifecycle position still \
      `.unreleased`.\n\n\
      Once this merges, CI on `main` tags the head of `main` {tag} after acceptance and the \
      rule-example shards pass, deploys https://rbeauchamp.github.io/regula/v/{v.spelling}/, \
      publishes the GitHub release with that edition as its asset once the deployment is \
      verified, and opens the pull request that sets `Regula.installed` back to `.unreleased`. \
      Other pull requests still merge meanwhile; until the release is published the tag follows \
      the head of `main`, and afterwards CI refuses every other commit that still carries the \
      release label until that reset pull request merges.\n\n\
      Opened by the Release workflow, which also started this branch's checks (checks do not \
      start on their own for a pull request a workflow opens)."

/-- Write the step output `release`: the version the checked-out commit installs, empty when it
is unreleased. -/
def reportInstalled : IO Unit := do
  let release := ((← installedHere).map (·.spelling)).getD ""
  output "release" release
  IO.println (if release.isEmpty then "this commit is unreleased"
    else s!"this commit installs release {release}")

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

/-- Attach the release edition the site build wrote and publish the release of the checked-out
commit, which its tag must name; a published release is left as it is. -/
def publish : IO Unit := do
  let repo ← repository
  let head ← env "GITHUB_SHA"
  let some v ← installedHere | fail "this commit is unreleased; there is nothing to publish"
  let tag := v.tag
  unless (← taggedCommit repo tag) == some head do fail s!"tag {tag} does not name {head}"
  if let some release ← releaseOf repo tag then
    unless release.getObjValD "draft" == .bool true do
      IO.println s!"release {tag} is already published"
      return
    -- An unpublished draft of an earlier attempt; publishing starts again from the notes.
    let id ← IO.ofExcept (release.getObjValAs? Nat "id")
    discard <| gh #["api", "--method", "DELETE", s!"repos/{repo}/releases/{id}"]
  let asset : FilePath := s!"tmp/site-release/regula-site-{v.spelling}.tar.gz"
  unless ← asset.pathExists do fail s!"the site build wrote no release edition {asset}"
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

/-- Once the release of the checked-out commit is published, make sure the pull request that sets
`Regula.installed` on `main` back to `.unreleased`, keeping `Regula.releases`, is open: open it
when none is, and rebuild an open one on the head of `main` only when it can no longer merge (a
conflict), leaving its branch, checks and approvals alone otherwise. Nothing is left to do once
`main` is unreleased. -/
def reset : IO Unit := do
  let repo ← repository
  let some v ← installedHere | fail "this commit is unreleased; there is no release to end"
  let tag := v.tag
  let some release ← releaseOf repo tag | fail s!"release {tag} is not published"
  if release.getObjValD "draft" == .bool true then fail s!"release {tag} is not published"
  let main ← mainHead repo
  let edition ← editionAt repo main
  match ← IO.ofExcept (installedOf edition) with
  | none =>
    IO.println "main's Regula.installed is already unreleased; nothing to reset"
    return
  | some w => unless w == v do fail s!"main installs {w.tag}, not {tag}"
  let branch := s!"release/{tag}-reset"
  if let some pull ← openPull repo branch then
    let conflicted := pull.getObjValD "mergeable" == .bool false ||
      pull.getObjValD "mergeable_state" == .str "dirty"
    unless conflicted do
      IO.println s!"the reset pull request from {branch} is open; leaving it as it is"
      return
  let listed ← IO.ofExcept (releasesOf edition)
  let unreleased ← IO.ofExcept (withEdition edition none listed)
  let commit ← editionCommit repo main unreleased
    s!"release: end Regula {tag}\n\nSets Regula.installed back to .unreleased now that the release \
      {tag} is published; Regula.releases keeps it, so every deployment serves its edition from \
      the release asset."
  proposeBranch repo branch commit s!"release: end Regula {tag}"
    s!"Sets `Regula.installed` back to `.unreleased` after the release {tag}, published with its \
      site edition as a release asset. `Regula.releases` keeps {tag}, so every deployment serves \
      https://rbeauchamp.github.io/regula/v/{v.spelling}/ from that asset. Until this merges, \
      the site build refuses every other commit that carries the release label.\n\n\
      Opened by CI once the release was published, which also started this branch's checks \
      (checks do not start on their own for a pull request a workflow opens)."

/-- Execute `tagAction` for the checked-out release commit: create tag `v<version>` here, move it
here or keep it, and otherwise fail. Refusing a published release first makes sure its reset pull
request is open, so a re-run of CI on `main` always ends the release. -/
def tagRelease : IO Unit := do
  let repo ← repository
  let head ← env "GITHUB_SHA"
  let some v ← installedHere | fail "this commit is unreleased; there is nothing to tag"
  let tag := v.tag
  let published := (← releaseOf repo tag).any fun r => r.getObjValD "draft" != .bool true
  let current := (← mainHead repo) == head
  let tagged ← taggedCommit repo tag
  let state : Tag := match tagged with
    | none => .absent
    | some commit => if commit == head then .head else .other
  match tagAction published current state with
  | .keep => IO.println s!"tag {tag} already names {head}"
  | .create =>
    discard <| ghPost "POST" s!"repos/{repo}/git/refs"
      (Json.mkObj [("ref", s!"refs/tags/{tag}"), ("sha", head)])
    IO.println s!"tagged {head} {tag}"
  | .move =>
    discard <| ghPost "PATCH" s!"repos/{repo}/git/refs/tags/{tag}"
      (Json.mkObj [("sha", head), ("force", true)])
    IO.println s!"moved tag {tag} from {tagged.getD ""} to {head}, the head of main; the release \
      is not published yet"
  | .refuse =>
    if published then
      reset
      fail s!"release {tag} is published from {tagged.getD "an absent tag"}; main's CI refuses \
        every other commit that carries the release label until the reset pull request, which \
        sets Regula.installed back to .unreleased, merges"
    fail s!"{head} is no longer the head of main; the run on main's head tags it"

end Regula.Release

/-- Command line of `lean --run lean/Regula/Release.lean`: `open`, `installed`, `tag`, `publish`
or `reset`; returns 2 on a usage error. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["open"] => Regula.Release.openRelease; return 0
  | ["installed"] => Regula.Release.reportInstalled; return 0
  | ["tag"] => Regula.Release.tagRelease; return 0
  | ["publish"] => Regula.Release.publish; return 0
  | ["reset"] => Regula.Release.reset; return 0
  | _ =>
    IO.eprintln
      "usage: lean --run lean/Regula/Release.lean (open | installed | tag | publish | reset)"
    return 2
