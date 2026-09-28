import Lean

/-! # Release automation

The steps of a Regula release, run with the pinned toolchain alone, so they need no build. The
`Release` workflow (`.github/workflows/release.yml`) runs the first; `ci.yml` runs the others:

```text
lean --run lean/Regula/Release.lean open        # push the branch of the release pull request
lean --run lean/Regula/Release.lean unreleased  # refuse a release label on main or a pull request
lean --run lean/Regula/Release.lean candidate   # create the release commit for CI to check
lean --run lean/Regula/Release.lean adopt       # derive it on main's commit, check it, adopt it
lean --run lean/Regula/Release.lean publish     # publish the checked release, creating its tag
```

A release's version is the Lean release in `lean-toolchain`, the Lean ecosystem's tag convention
(`v4.34.0` for `leanprover/lean4:v4.34.0`), so there is at most one release per supported
toolchain. `main` never carries a release label: `Regula.installed` (`RegulaCore/Edition.lean`)
is `.unreleased` on every commit of `main` and of a pull request, which `unreleased` checks in
CI's required `verify` job.

`open` creates the commit of the release pull request as a child of the `main` commit the
workflow runs on: the release appended to `Regula.releases` unless it is listed, and stamped into
each `.unreleased` on a line that starts `lifecycle :=` (`RegulaCore/Rule.lean`, `stampRules`, a
convenience); `Regula.installed` stays `.unreleased`. GitHub creates and signs it, and `open`
refuses unless GitHub reports its signature verified. It pushes it as the branch
`release/v<version>` and writes the link that opens its pull request to the job summary; a
maintainer opens the pull request from that link, which starts its checks, and merges it through
normal review. When that pull request is already open, `open` starts the checks of the rebuilt
branch by dispatching `ci.yml` on it, because a push with the workflow's token starts no workflow.
No step creates a pull request: the repository does not let GitHub Actions create one.

On `main`, once acceptance and the rule-example shards pass on a commit that lists a release not
yet published, `candidate` creates the release commit, a signed child of that commit that is not
on `main` and whose only change sets `Regula.installed` to the release, and points the branch
`release/v<version>-candidate` at it. CI then runs on the release commit, with its release label,
the same checks as on `main`: both acceptance steps, both rule-example shards and the site build,
which renders the release's edition and writes it as the release asset. The jobs that run them
check out the commit of `main` itself, derive the release commit's content there with `main`'s
own code, and adopt the release commit's name only once they have shown that it is exactly that
content (`adopt`). The kernel's check of
`release_attributes_rules` there is what guarantees that no rule lifecycle position is still
`.unreleased`. Only once all of them pass does `publish` create the GitHub release with the notes
and that asset, published only once the asset is attached; publishing creates tag `v<version>`
at the release commit (immutable releases then freeze both). No step writes the tag otherwise, so
if any check fails there is no tag and no release. The site build of `main` runs after that and
takes the release's edition from the asset.

Other pull requests still merge during a release. Until the release is published, each run of
`candidate` on the head of `main` creates a fresh release commit on it (`tagAction_converges`),
so a re-run of CI on `main` finishes a release that a later merge cancelled. Once it is
published, no step changes anything (`tagAction_published`). If a pull request that adds or
retires a rule merges to `main` before the release is published, the release commit fails
`release_attributes_rules` and nothing is published; running the Release workflow on `main` again
as a new run stamps that rule too (a re-run reuses its original commit).

Every step resumes: `open` rebuilds its branch on the commit its run started from, `candidate`
creates a fresh release commit, and `publish` replaces an unpublished draft and skips a published
release. They refuse a toolchain that is not a stable release; `open` refuses a published
release, an earlier listed release not yet published, and a `main` with nothing left to stamp;
`candidate` refuses a release commit on a `lean-toolchain` that is not the release's; and
`candidate` and `publish` refuse, while the release is unpublished, a run whose commit is no
longer the head of `main` and a tag that names another commit.

## Boundaries

GitHub (its API through `gh`, signing, tags, releases, pull requests and Actions) and `git` (the
tree it writes, the objects it fetches and its resets) are trusted and observed, not proved.
`tagAction` is the decision the candidate and publish steps execute, and its theorems are
checked by the kernel each time `lean --run` elaborates this file; what the steps
observe (whether the release is published, the head of `main`, the tag), that publishing a release
creates its tag at the given commit, and the order of CI's jobs are GitHub's. The edits of
`RegulaCore/Edition.lean` and `RegulaCore/Rule.lean` are text: `open`, `candidate` and `adopt`
read their edit of `Edition.lean` back and refuse unless it names the intended build and releases,
and the kernel checks the edited modules' theorems (`releases_ascending`, `installed_listed`,
`release_attributes_rules`, `lifecycle_listed`) when the release pull request's checks and CI's
checks of the release commit build them.
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

/-- The `RegulaCore/Edition.lean` of the release commit of release `v` on a commit of `main` whose
`RegulaCore/Edition.lean` is `edition`, listing `listed`, and whose `lean-toolchain` is
`toolchain`: `edition` with `installed` set to `v`. Refuses a release whose Lean release is not
`toolchain`'s. `candidate` commits it (`releaseCommit`) and `adopt` derives it in its workspace,
both through this one function. -/
def releaseEdition (edition toolchain : String) (listed : List Version) (v : Version) :
    Except String String := do
  unless toolchainVersion toolchain == some v do
    throw s!"lean-toolchain is {toolchain.trimAscii}, not the Lean release of {v.tag}"
  withEdition edition (some v) listed

/-! ## The release decision

A release is cut from whichever head of `main` listing it first completes the whole chain. While
the release is unpublished (no GitHub release, or only a draft), the candidate step creates a
fresh release commit on the commit it runs on, provided that commit is still the head of `main`,
and CI checks it; the publish step then publishes the release, which creates tag `v<version>` at
that release commit. No step writes the tag otherwise, so the tag exists only for a published
release, and once the release is published nothing changes. -/

/-- Where tag `v<version>` points, relative to the release commit a step handles: the three cases
of the site build's `Regula.TagState`. Before the candidate step creates its release commit, an
existing tag names another commit. -/
inductive Tag where
  /-- The tag does not exist. -/
  | absent
  /-- The tag names the release commit. -/
  | head
  /-- The tag names another commit. -/
  | other
  deriving DecidableEq, Repr

/-- What a release step does. -/
inductive TagAction where
  /-- Proceed: create the release commit (candidate step), or publish it, which creates the tag
  there (publish step). -/
  | release
  /-- Change nothing: the release is published. -/
  | skip
  /-- Change nothing and fail. -/
  | refuse
  deriving DecidableEq, Repr

/-- The decision of the candidate and publish steps, given whether the release is `published`,
whether the run's commit is the `current` head of `main`, and the state of the tag. -/
def tagAction (published current : Bool) (tag : Tag) : TagAction :=
  if published then .skip
  else if current && tag != .other then .release
  else .refuse

/-- A step proceeds exactly for the head of `main` of an unpublished release whose tag is absent
or names the release commit, so publication never leaves the tag naming another commit. -/
theorem tagAction_release_iff (published current : Bool) (tag : Tag) :
    tagAction published current tag = .release ↔
      published = false ∧ current = true ∧ (tag = .absent ∨ tag = .head) := by
  cases published <;> cases current <;> cases tag <;> decide

/-- A step changes nothing exactly when the release is published. -/
theorem tagAction_skip_iff (published current : Bool) (tag : Tag) :
    tagAction published current tag = .skip ↔ published = true := by
  cases published <;> cases current <;> cases tag <;> decide

/-- A step refuses exactly when the release is unpublished and the run's commit is no longer the
head of `main` or the tag names another commit. -/
theorem tagAction_refuse_iff (published current : Bool) (tag : Tag) :
    tagAction published current tag = .refuse ↔
      published = false ∧ (current = false ∨ tag = .other) := by
  cases published <;> cases current <;> cases tag <;> decide

/-- Once the release is published, no step writes anything. -/
theorem tagAction_published (current : Bool) (tag : Tag) : tagAction true current tag = .skip := by
  cases current <;> cases tag <;> decide

/-- While the release is unpublished and no tag names another commit, a step on the head of
`main` proceeds. -/
theorem tagAction_converges (tag : Tag) (h : tag ≠ .other) :
    tagAction false true tag = .release := by
  cases tag <;> simp_all [tagAction]

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

/-- Whether the release of `tag` is published: it exists and is not a draft. -/
def published (repo tag : String) : IO Bool := do
  return (← releaseOf repo tag).any fun r => r.getObjValD "draft" != .bool true

/-- The tree of commit `sha`, as GitHub reads it back. -/
def commitTree (repo sha : String) : IO String := do
  str (← IO.ofExcept ((← ghGet s!"repos/{repo}/git/commits/{sha}").getObjVal? "tree")) "sha"

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

/-- The open pull request from `branch`, if there is one. -/
private def openPull (repo branch : String) : IO (Option Json) := do
  let owner := (repo.splitOn "/").head!
  let pulls ← IO.ofExcept
    (← ghGet s!"repos/{repo}/pulls?state=open&head={owner}:{branch}").getArr?
  return pulls[0]?

/-- `s` percent-encoded for a URL query value: every byte outside RFC 3986's unreserved set. -/
def percentEncode (s : String) : String :=
  let hex (n : Nat) : Char := "0123456789ABCDEF".toList[n]!
  String.join (s.toUTF8.toList.map fun b =>
    let c := Char.ofNat b.toNat
    if b.toNat < 128 && (c.isAlphanum || c == '-' || c == '.' || c == '_' || c == '~') then
      c.toString
    else "%" ++ (hex (b.toNat / 16)).toString ++ (hex (b.toNat % 16)).toString)

/-- Point branch `branch` at `commit`: create it, or move it there from wherever it points. -/
private def pointBranch (repo branch commit : String) : IO Unit := do
  let existing ← ghGet s!"repos/{repo}/git/matching-refs/heads/{branch}"
  let exists_ := (← IO.ofExcept existing.getArr?).any fun r =>
    r.getObjValD "ref" == .str s!"refs/heads/{branch}"
  if exists_ then
    discard <| ghPost "PATCH" s!"repos/{repo}/git/refs/heads/{branch}"
      (Json.mkObj [("sha", commit), ("force", true)])
  else
    discard <| ghPost "POST" s!"repos/{repo}/git/refs"
      (Json.mkObj [("ref", s!"refs/heads/{branch}"), ("sha", commit)])

/-- Point `branch` at `commit`; its pull request is a maintainer's to open. When one is already
open, start the checks of the rebuilt branch by dispatching `ci.yml` on it, because a push with
the workflow's token starts no workflow. Otherwise write the link that opens it, with `title` and
`body` filled in, to the job summary (`GITHUB_STEP_SUMMARY`) and the log; opening it starts its
checks. The workflow never creates a pull request: the repository does not let GitHub Actions
create one. -/
private def pushBranch (repo branch commit title body : String) : IO Unit := do
  pointBranch repo branch commit
  if let some pull ← openPull repo branch then
    discard <| gh #["workflow", "run", "ci.yml", "--repo", repo, "--ref", branch]
    let url := (pull.getObjValD "html_url").getStr?.toOption.getD branch
    IO.println s!"branch {branch} names {commit}; its pull request {url} is open, and the \
      dispatched run of ci.yml checks it"
    return
  let link := s!"https://github.com/{repo}/compare/main...{branch}?expand=1&title=\
    {percentEncode title}&body={percentEncode body}"
  let summary := s!"### Open the pull request `{title}`\n\nThe signed branch `{branch}` names \
    `{commit}`. Open its pull request from [this link]({link}); opening it starts its checks.\n"
  if let some path ← IO.getEnv "GITHUB_STEP_SUMMARY" then
    let handle ← IO.FS.Handle.mk path .append
    handle.putStr summary
  IO.println s!"branch {branch} names {commit}; open its pull request from {link}"

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

/-- Push the branch of the release pull request: a commit on the `main` commit the workflow runs
on that appends the release of `lean-toolchain` to `Regula.releases` unless it is listed and
stamps it into each `.unreleased` on a `lifecycle :=` line (`stampRules`), leaving
`Regula.installed` unreleased. Refuses a published release, an earlier listed release not yet
published, and a `main` that already lists the release with nothing left to stamp. -/
def openRelease : IO Unit := do
  let repo ← repository
  let head ← env "GITHUB_SHA"
  let toolchain ← IO.FS.readFile "lean-toolchain"
  let some v := toolchainVersion toolchain
    | fail s!"lean-toolchain is {toolchain.trimAscii}; a release needs a stable Lean release"
  let tag := v.tag
  if ← published repo tag then
    fail s!"release {tag} is published; the next release needs the next Lean release"
  let edition ← IO.FS.readFile editionFile
  let listed ← IO.ofExcept (releasesOf edition)
  if let some last := listed.getLast? then
    unless last == v || (← published repo last.tag) do
      fail s!"release {last.tag} is listed on main but not published yet; CI on main publishes it"
  let ready ← IO.ofExcept (withEdition edition none (if listed.contains v then listed else
    listed ++ [v]))
  let rules ← IO.FS.readFile rulesFile
  let stamped := stampRules rules v
  if ready == edition && stamped == rules then
    fail s!"main already lists {tag} and no `lifecycle :=` line says .unreleased; CI on main \
      releases it"
  let commit ← filesCommit repo head
    [(editionFile.toString, ready), (rulesFile.toString, stamped)]
    s!"release: Regula {tag} for Lean {tag}\n\nLists {tag} in Regula.releases and stamps it into \
      each .unreleased on a `lifecycle :=` line; Regula.installed stays unreleased. Once \
      this is on main, CI creates the release commit, which sets Regula.installed to the \
      release, runs main's checks on it and, once they pass, publishes the release, which tags \
      it {tag}."
  pushBranch repo s!"release/{tag}" commit s!"release: Regula {tag}"
    s!"Prepares Regula {tag} for Lean {tag}: lists it in `Regula.releases` and stamps it into \
      each `.unreleased` on a `lifecycle :=` line. `Regula.installed` stays \
      `.unreleased`: `main` never carries a release label.\n\n\
      Once this merges and acceptance and the rule-example shards pass on `main`, CI creates \
      the release commit, a signed child of the head of `main` that is not on `main` and whose \
      only change sets `Regula.installed` to the release. It runs both acceptance steps, both \
      rule-example shards and the site build on that commit with its release label, and only \
      once they all pass publishes the GitHub release with its edition as the asset, which \
      creates tag {tag} at that commit; `main` then deploys \
      https://rbeauchamp.github.io/regula/v/{v.spelling}/ from that asset. Other pull requests \
      still merge meanwhile: until the release is published, each run on the head of `main` \
      creates a fresh release commit on it.\n\n\
      If a pull request that adds or retires a rule merges to `main` before the release is \
      published, the release commit fails `release_attributes_rules` and nothing is published: \
      run the Release workflow on `main` again as a new run (a re-run reuses its \
      original commit): it stamps that rule too, on this branch while this pull request is \
      open, and in a new pull request from it once this one has merged.\n\n\
      Until the release is published, the `site` check of this branch refuses: the release's \
      edition exists only once CI builds it from the release commit. `verify` is the required \
      check.\n\n\
      The Release workflow pushed this signed branch, and a maintainer opened this pull request \
      from the link in the job summary, which started its checks; when the workflow rebuilds \
      the branch while this pull request is open, it starts them by dispatching `ci.yml`."

/-- Refuse unless the checked-out commit is unreleased: no commit of `main` or of a pull request
carries a release label; only the release commit that `candidate` creates does, and publication
tags it. -/
def requireUnreleased : IO Unit := do
  match ← installedHere with
  | none => IO.println "this commit is unreleased"
  | some v => fail s!"this commit sets Regula.installed to {v.tag}; only the release commit that \
      CI on main creates for {v.tag} carries a release label, so main and every pull request \
      keep it .unreleased"

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

/-- Publish release `v<version>` of the release commit `RELEASE_COMMIT` once CI has checked it:
attach the release edition its site build wrote and publish the release, which creates tag
`v<version>` at that commit, as `tagAction` decides; a published release is left as it is.
Refuses unless `VERIFIED_COMMIT` and `SITE_COMMIT`, the commits `adopt` adopted in
`release-verify` and `release-site`, are `RELEASE_COMMIT`, so the tag names the commit the
checked edition records. -/
def publish : IO Unit := do
  let repo ← repository
  let head ← env "GITHUB_SHA"
  let commit ← env "RELEASE_COMMIT"
  for name in ["VERIFIED_COMMIT", "SITE_COMMIT"] do
    let adopted ← env name
    unless adopted == commit do
      fail s!"{name} is {adopted}: the checks adopted another commit than {commit}"
  let some v ← IO.ofExcept (installedOf (← editionAt repo commit))
    | fail s!"{commit} is unreleased; there is nothing to publish"
  let tag := v.tag
  let state : Tag := match ← taggedCommit repo tag with
    | none => .absent
    | some named => if named == commit then .head else .other
  match tagAction (← published repo tag) ((← mainHead repo) == head) state with
  | .skip =>
    IO.println s!"release {tag} is already published"
    return
  | .refuse => fail s!"release {tag} is not published, and {head} is no longer the head of main \
      or tag {tag} names another commit than {commit}"
  | .release => pure ()
  if let some draft ← releaseOf repo tag then
    -- An unpublished draft of an earlier attempt; publishing starts again from the notes.
    let id ← IO.ofExcept (draft.getObjValAs? Nat "id")
    discard <| gh #["api", "--method", "DELETE", s!"repos/{repo}/releases/{id}"]
  let asset : FilePath := s!"tmp/site-release/regula-site-{v.spelling}.tar.gz"
  unless ← asset.pathExists do fail s!"the site build wrote no release edition {asset}"
  IO.FS.createDirAll "tmp"
  IO.FS.writeFile "tmp/release-notes.md" (notes v repo)
  -- `gh` creates the release as a draft, uploads the asset, then publishes it, which creates the
  -- tag at `commit` unless it already names it.
  discard <| gh #["release", "create", tag, asset.toString, "--repo", repo, "--target", commit,
    "--title", s!"Regula {tag}", "--notes-file", "tmp/release-notes.md", "--generate-notes",
    "--latest"]
  let some release ← releaseOf repo tag | fail s!"release {tag} was not created"
  let assets ← IO.ofExcept ((release.getObjValD "assets").getArr?)
  unless release.getObjValD "draft" == .bool false &&
      (← assets.anyM fun a => return (← str a "name") == s!"regula-site-{v.spelling}.tar.gz") do
    fail s!"release {tag} is not published with its site asset"
  unless (← taggedCommit repo tag) == some commit do
    fail s!"release {tag} is published, but its tag does not name {commit}"
  IO.println s!"published release {tag} of {commit} with regula-site-{v.spelling}.tar.gz"

/-- The release commit of release `v` on `main`'s commit `head`, whose `RegulaCore/Edition.lean`
is `edition` listing `listed`: a signed child of `head` whose only change sets
`Regula.installed` to `v`. Refuses a release whose Lean release is not `lean-toolchain`'s. That no
rule lifecycle position is still `.unreleased` is not checked here: the kernel checks it
(`release_attributes_rules`) when CI builds the release commit, before anything is published. -/
def releaseCommit (repo head edition : String) (listed : List Version) (v : Version) :
    IO String := do
  let tag := v.tag
  editionCommit repo head
    (← IO.ofExcept (releaseEdition edition (← IO.FS.readFile "lean-toolchain") listed v))
    s!"release: Regula {tag} for Lean {tag}\n\nSets Regula.installed to the release. CI created \
      this release commit on {head}, the head of main; it is not on main, and publishing the \
      release {tag} after CI has checked it creates the tag here."

/-- The candidate step, on the checked-out commit of `main` for its latest listed release: when
`tagAction` proceeds, create a fresh release commit on it (`releaseCommit`) and point the branch
`release/v<version>-candidate` at it, of which `adopt` fetches only that one commit (depth 1);
leave a published release alone, and otherwise fail. Neither the tag nor the release exists yet.
Writes the step outputs `commit`, the release commit, and `tree`, its tree, both empty when there
is nothing to release. -/
def candidate : IO Unit := do
  let repo ← repository
  let head ← env "GITHUB_SHA"
  let edition ← IO.FS.readFile editionFile
  let listed ← IO.ofExcept (releasesOf edition)
  let nothing (reason : String) : IO Unit := do
    output "commit" ""
    output "tree" ""
    IO.println reason
  let some v := listed.getLast? | nothing "main lists no release; there is nothing to release"
  let tag := v.tag
  let tagged ← taggedCommit repo tag
  match tagAction (← published repo tag) ((← mainHead repo) == head)
      (if tagged.isSome then .other else .absent) with
  | .skip => nothing s!"release {tag} is published; there is nothing to release"
  | .refuse =>
    if let some named := tagged then
      fail s!"tag {tag} names {named}, but release {tag} is not published; only publication \
        creates the tag"
    fail s!"{head} is no longer the head of main; the run on main's head releases {tag}"
  | .release =>
    let commit ← releaseCommit repo head edition listed v
    let tree ← commitTree repo commit
    let branch := s!"release/{tag}-candidate"
    pointBranch repo branch commit
    output "commit" commit
    output "tree" tree
    IO.println s!"created the release commit {commit} (tree {tree}) on {head} as branch \
      {branch}; CI checks it before publishing {tag}"

/-- Run `git` with `args` in the checkout; its standard output without surrounding whitespace, or
a failure with its standard error. -/
private def git (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := "git", args }
  unless out.exitCode == 0 do fail s!"git {args}: {out.stderr}"
  return out.stdout.trimAscii.toString

/-- The values of the header fields `name` of the raw commit object `raw` (`git cat-file commit`),
in order; the header ends at the first empty line, and a signature's continuation lines start
with a space, so they never match. -/
def commitFields (raw name : String) : List String :=
  ((raw.splitOn "\n").takeWhile (!·.isEmpty)).filterMap fun line =>
    (line.dropPrefix? (name ++ " ")).map (·.toString)

/-- The adopt step of `release-verify` and `release-site`, which check out `main`'s commit
`GITHUB_SHA` itself (no job output names what they check out) and are given `RELEASE_TREE`, the
tree of the release commit `candidate` created on that commit. In order, refusing at the first
mismatch:

1. Derive the release commit's `RegulaCore/Edition.lean` in the workspace with
   `releaseEdition`, from the workspace's own `Edition.lean` and `lean-toolchain`: the function
   and inputs `candidate` committed (`releaseCommit`).
2. Stage it; `git write-tree` must be `RELEASE_TREE`.
3. Fetch only that one commit (depth 1) that `release/v<version>-candidate` names, with the
   version from the workspace's own `Edition.lean`; its tree must be `RELEASE_TREE` and its
   parents exactly `[GITHUB_SHA]`.
4. `git reset --soft` to it, which writes no file; the worktree must then be clean at it. Write
   it as the step output `commit`.

The correspondence: the content every later step builds and runs is `main`'s commit with the edit
`main`'s own code derived. That tree is the release commit's tree, and the release commit's only
parent is that same commit of `main`, so the release commit is exactly the content these jobs
check. Its name is adopted only after that is shown, and no file comes from it, so every identity
the checks record (the checker's compiled source revision, the site's revision and repository
links, the release asset's `build.json`) names the release commit without any override. A mismatch
fails the job, so `publish` does not run and no tag is written. -/
def adopt : IO Unit := do
  let head ← env "GITHUB_SHA"
  let expected ← env "RELEASE_TREE"
  let edition ← IO.FS.readFile editionFile
  let listed ← IO.ofExcept (releasesOf edition)
  let some v := listed.getLast? | fail "main lists no release; there is no release commit"
  IO.FS.writeFile editionFile
    (← IO.ofExcept (releaseEdition edition (← IO.FS.readFile "lean-toolchain") listed v))
  discard <| git #["add", "--", editionFile.toString]
  let derived ← git #["write-tree"]
  unless derived == expected do
    fail s!"the release edit of {head} has tree {derived}, not the release commit's tree \
      {expected}"
  let branch := s!"release/{v.tag}-candidate"
  discard <| git #["fetch", "--no-tags", "--depth=1", "origin", s!"refs/heads/{branch}"]
  let commit ← git #["rev-parse", "--verify", "FETCH_HEAD^{commit}"]
  let raw ← git #["cat-file", "commit", commit]
  let trees := commitFields raw "tree"
  let parents := commitFields raw "parent"
  unless trees == [expected] && parents == [head] do
    fail s!"{branch} names {commit}, whose tree is {trees} and parents {parents}, not tree \
      {expected} with the one parent {head}"
  discard <| git #["reset", "--soft", commit]
  let status ← git #["status", "--porcelain", "--untracked-files=normal"]
  unless status.isEmpty && (← git #["rev-parse", "HEAD"]) == commit do
    fail s!"the workspace is not clean at {commit}:\n{status}"
  output "commit" commit
  IO.println s!"adopted the release commit {commit}: its tree {expected} is {head} with the \
    release edit main's code derives, and its only parent is {head}"

end Regula.Release

/-- Command line of `lean --run lean/Regula/Release.lean`: `open`, `unreleased`, `candidate`,
`adopt` or `publish`; returns 2 on a usage error. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["open"] => Regula.Release.openRelease; return 0
  | ["unreleased"] => Regula.Release.requireUnreleased; return 0
  | ["candidate"] => Regula.Release.candidate; return 0
  | ["adopt"] => Regula.Release.adopt; return 0
  | ["publish"] => Regula.Release.publish; return 0
  | _ =>
    IO.eprintln "usage: lean --run lean/Regula/Release.lean \
      (open | unreleased | candidate | adopt | publish)"
    return 2
