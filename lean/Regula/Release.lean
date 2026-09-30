import Lean

/-! # Release automation

The steps of a Regula release, run with the pinned toolchain alone, so they need no build. The
`Release` workflow (`.github/workflows/release.yml`) runs `open`, the `Title` workflow
(`.github/workflows/title.yml`) runs `title`, and `ci.yml` runs the others:

```text
lean --run lean/Regula/Release.lean open        # push the branch of the release pull request
lean --run lean/Regula/Release.lean unreleased  # refuse a release label on main or a pull request
lean --run lean/Regula/Release.lean agree       # refuse a lakefile or table the releases contradict
lean --run lean/Regula/Release.lean title       # refuse a pull request title that is not a header
lean --run lean/Regula/Release.lean candidate   # create the release commit for CI to check
lean --run lean/Regula/Release.lean adopt       # derive it on main's commit, check it, adopt it
lean --run lean/Regula/Release.lean publish     # publish the checked release, creating its tag
```

## Versions

Regula numbers its own releases by Semantic Versioning, in the `version` of its `lakefile.lean`,
and tags each release `v<version>`. A release supports exactly one Lean toolchain, the
`lean-toolchain` of its release commit, and `Regula.releases` (`RegulaCore/Edition.lean`) records
each release's version with that toolchain. The first release, `v4.34.0`, was numbered by the Lean
release it supports before Regula numbered its own (`Version.legacy`): its semantic version is
`0.1.0` (`Version.semver`), which orders it before every later release, and its lakefile declares
no version, which Lake and Reservoir read as `0.0.0` (`Version.declared`), so they too rank it
below every later release (`lakeLt_declared`, `admits_lake`).

A release's version is derived, not chosen (`nextVersion`). Pull requests merge by squash, so
each commit of `main` is one pull request, whose title, a Conventional Commits header that the
`title` step requires, is the commit's subject. Of the commits of `main` since the previous
release, a breaking change (`type!:`, or a `BREAKING CHANGE:` footer) calls for a major bump, or
a minor one before 1.0; `feat` for a minor bump; `fix` and `perf` for a patch; and every other
type for none (`Header.bump`, `derive`). A `lean-toolchain` other than the previous release's
calls for at least a minor bump. The Release workflow's `bump` input may raise the bump and never
lowers it (`nextBump_ge_derived`, `nextBump_ge_requested`, `nextBump_moved`); a derivation over a
commit whose subject is not such a header is undecided and needs that input (`derive_eq_none`).
The derived version follows its predecessor (`nextVersion_follows`): it is later, a patch release
keeps its predecessor's toolchain, and a release that starts a new line resets the lower
components. `main`'s `lakefile.lean` declares the version of the latest listed release, and the
adoption guide's compatibility table lists every listed release with its toolchain; `agree`
checks both on every commit, the version as Lake itself reads it (`lake reservoir-config`).

## Steps

`main` never carries a release label: `Regula.installed` (`RegulaCore/Edition.lean`) is
`.unreleased` on every commit of `main` and of a pull request, which `unreleased` checks in CI's
required `verify` job.

`open` derives the version and creates the commit of the release pull request as a child of the
`main` commit the workflow runs on: the release appended with its toolchain to `Regula.releases`,
`lakefile.lean`'s `version` set to it, its row added to the adoption guide's compatibility table,
and the release stamped into each `.unreleased` on a line that starts `lifecycle :=`
(`RegulaCore/Rule.lean`, `stampRules`, a convenience); `Regula.installed` stays `.unreleased`.
While the last listed release is not published yet, `open` lists the release it derives in its
place instead, restamping its stamps (`restampRules`). GitHub creates and signs the commit, and
`open` refuses unless GitHub reports its signature verified. It pushes it as the branch
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
as a new run stamps that rule too, at the version the commits then call for (a re-run reuses its
original commit).

Every step resumes: `open` rebuilds its branch on the commit its run started from, `candidate`
creates a fresh release commit, and `publish` replaces an unpublished draft and skips a published
release. They refuse a toolchain that is not a stable release; `open` refuses a derivation that
releases nothing, an earlier listed release not yet published, and a `main` with nothing left to
change; `candidate` refuses a release commit whose `lean-toolchain` is not the toolchain the
release records; and `candidate` and `publish` refuse, while the release is unpublished, a run
whose commit is no longer the head of `main` and a tag that names another commit.

## Boundaries

GitHub (its API through `gh`, signing, tags, releases, pull requests and Actions) and `git` (the
tree it writes, the history and objects it fetches and its resets) are trusted and observed, not
proved. `tagAction` is the decision the candidate and publish steps execute, and `nextVersion` and
`admits` the ones `open` executes; their theorems are checked by the kernel each time `lean --run`
elaborates this file. What the steps observe (whether the release is published, the head of
`main`, the tag, the commits since the previous release), that publishing a release creates its
tag at the given commit, and the order of CI's jobs are GitHub's; that Lake reads a package's
version from its `lakefile.lean` and that Reservoir indexes each version tag with that version,
ordering them by it, is Lake's and Reservoir's behaviour. The edits of `RegulaCore/Edition.lean`,
`RegulaCore/Rule.lean`, `lakefile.lean` and the adoption guide are text: `open`, `candidate` and
`adopt` read their edits back and refuse unless they name the intended build, releases, version
and table, `agree` checks the version with Lake's own reading, and the kernel checks the edited
modules' theorems (`releases_ascending`, `releases_follow`, `installed_listed`,
`release_attributes_rules`, `lifecycle_listed`, `introduced_startsLine`) when the release pull
request's checks and CI's checks of the release commit build them.
-/

namespace Regula.Release

open Lean System

private def fail {α : Type} (message : String) : IO α :=
  throw <| IO.userError s!"release: {message}"

/-! ## Versions -/

/-- A version `major.minor.patch`: a Regula release's, or a Lean release's. -/
structure Version where
  /-- The major version. -/
  major : Nat
  /-- The minor version. -/
  minor : Nat
  /-- The patch version. -/
  patch : Nat
  deriving DecidableEq, Repr

/-- The version as it is written, such as `0.2.0`. -/
def Version.spelling (v : Version) : String := s!"{v.major}.{v.minor}.{v.patch}"

/-- The tag of the version. -/
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

/-- The Lean release of a `lean-toolchain`: a stable Lean release `leanprover/lean4:vX.Y.Z`. A
release candidate or nightly toolchain has none. -/
def toolchainVersion (toolchain : String) : Option Version :=
  (toolchain.trimAscii.toString.dropPrefix? "leanprover/lean4:v").bind fun rest =>
    parseVersion rest.toString

/-- The legacy release `v4.34.0` (`Regula.ReleaseVersion.legacy`): Regula's first release,
numbered by the Lean release it supports before Regula numbered its own. -/
def Version.legacy : Version := ⟨4, 34, 0⟩

/-- The semantic version of release `v` (`Regula.ReleaseVersion.semver`), which orders releases
and from which the next version is derived: its own, and `0.1.0` for the legacy release. -/
def Version.semver (v : Version) : Version := if v = legacy then ⟨0, 1, 0⟩ else v

/-- The version Lake and Reservoir read for release `v`: the `version` its `lakefile.lean`
declares. The legacy release's declares none, which Lake reads as its default `0.0.0`; every later
release's declares its own version, which `agree` checks. -/
def Version.declared (v : Version) : Version := if v = legacy then ⟨0, 0, 0⟩ else v

/-- Lexicographic order of the components, which is Lake's order of versions without a `-`
suffix (`Lake.StdVer`, whose `SemVerCore` derives `Ord` over major, minor and patch). -/
def Version.lex (a b : Version) : Prop :=
  a.major < b.major ∨
    a.major = b.major ∧ (a.minor < b.minor ∨ a.minor = b.minor ∧ a.patch < b.patch)

instance (a b : Version) : Decidable (a.lex b) := by unfold Version.lex; infer_instance

/-- Release order (`Regula.ReleaseVersion`'s `<`): lexicographic in the semantic versions. -/
instance : LT Version := ⟨fun a b => a.semver.lex b.semver⟩

instance (a b : Version) : Decidable (a < b) := inferInstanceAs (Decidable (a.semver.lex b.semver))

/-- Release order unfolded. -/
theorem Version.lt_iff (a b : Version) : a < b ↔ a.semver.lex b.semver := Iff.rfl

/-- Every version but the legacy release's is its own semantic version. -/
theorem Version.semver_of_ne {v : Version} (h : v ≠ legacy) : v.semver = v := by
  simp [semver, h]

/-- Every release but the legacy one declares its own version. -/
theorem Version.declared_of_ne {v : Version} (h : v ≠ legacy) : v.declared = v := by
  simp [declared, h]

/-- No release precedes itself. -/
theorem Version.lt_irrefl (v : Version) : ¬ v < v := by
  rw [lt_iff]; unfold lex; omega

/-- Release order is Lake's order of the versions the releases declare, for every later release
than the legacy one: the legacy release, declared `0.0.0`, is below every release after it, and
every other release declares its semantic version. -/
theorem Version.lakeLt_declared {a b : Version} (h : a < b) (hb : b ≠ legacy) :
    a.declared.lex b.declared := by
  rw [lt_iff, semver_of_ne hb] at h
  rw [declared_of_ne hb]
  by_cases ha : a = legacy
  · subst ha
    simp only [semver, declared, lex] at h ⊢
    simp only [↓reduceIte] at h ⊢
    omega
  · rwa [semver_of_ne ha, ← declared_of_ne ha] at h

/-! ## Releases and the version rules -/

/-- A release (`Regula.ListedRelease`): its version and the Lean release of the one toolchain it
supports. -/
structure Release where
  /-- The release version. -/
  version : Version
  /-- The Lean release of the one toolchain the release supports. -/
  toolchain : Version
  deriving DecidableEq, Repr

/-- Whether `a` and `b` are on the same line: the same major and minor semantic version. -/
def Version.sameLine (a b : Version) : Bool :=
  a.semver.major == b.semver.major && a.semver.minor == b.semver.minor

/-- Whether release `next` may directly follow release `prev` (`Regula.ListedRelease.follows`):
`next` is later; a patch release (one on `prev`'s line) keeps `prev`'s toolchain, so a release on
another toolchain bumps at least the minor version; and a release that starts a new line has
patch `0`, and minor `0` too when it bumps the major version. -/
def follows (prev next : Release) : Bool :=
  decide (prev.version < next.version) &&
    if prev.version.sameLine next.version then prev.toolchain == next.toolchain
    else next.version.semver.patch == 0 &&
      (next.version.semver.major == prev.version.semver.major || next.version.semver.minor == 0)

/-- Whether release `next` may be appended to the listed releases `listed`, oldest first: it is
later than every listed release and follows the last one. -/
def admits (listed : List Release) (next : Release) : Bool :=
  listed.all (fun r => decide (r.version < next.version)) && listed.getLast?.all (follows · next)

/-- A release is admitted exactly when it is later than every listed release and follows the
last one. -/
theorem admits_iff (listed : List Release) (next : Release) :
    admits listed next = true ↔ (∀ r ∈ listed, r.version < next.version) ∧
      ∀ prev, listed.getLast? = some prev → follows prev next = true := by
  unfold admits
  cases listed.getLast? <;> simp

/-- An admitted release's version is none of the listed releases', so its tag is new. -/
theorem admits_new {listed : List Release} {next : Release} (h : admits listed next = true) :
    ∀ r ∈ listed, r.version ≠ next.version := by
  intro r hr he
  have := ((admits_iff _ _).mp h).1 r hr
  rw [he] at this
  exact Version.lt_irrefl _ this

/-- Once the legacy release is listed, Lake's order of the declared versions, by which Reservoir
ranks a package's versions, puts an admitted release above every listed one, the legacy release
included. -/
theorem admits_lake {listed : List Release} {next : Release} (h : admits listed next = true)
    (hl : ∃ r ∈ listed, r.version = Version.legacy) :
    ∀ r ∈ listed, r.version.declared.lex next.version.declared := by
  have hlt := ((admits_iff _ _).mp h).1
  obtain ⟨l, hl, he⟩ := hl
  have hne : next.version ≠ Version.legacy := by
    intro hn
    have := hlt l hl
    rw [he, hn] at this
    exact Version.lt_irrefl _ this
  intro r hr
  exact Version.lakeLt_declared (hlt r hr) hne

/-- A release on another toolchain than its predecessor's is not on its line: it bumps at least
the minor version. -/
theorem follows_toolchain {prev next : Release} (h : follows prev next = true)
    (ht : prev.toolchain ≠ next.toolchain) : prev.version.sameLine next.version = false := by
  unfold follows at h
  cases hs : prev.version.sameLine next.version
  · rfl
  · simp [hs, ht] at h

/-- A release that follows its predecessor has patch `0` exactly when it starts a new line, so a
release that may introduce a rule (`Regula.introduced_startsLine`) is not a patch release. -/
theorem follows_patch_iff {prev next : Release} (h : follows prev next = true) :
    next.version.semver.patch = 0 ↔ prev.version.sameLine next.version = false := by
  unfold follows at h
  cases hs : prev.version.sameLine next.version
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.2.1]
  · simp only [hs, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, Version.lt_iff] at h
    simp only [Version.sameLine, Bool.and_eq_true, beq_iff_eq] at hs
    have hlt := h.1
    unfold Version.lex at hlt
    simp only [Bool.true_eq_false, iff_false]
    omega

/-! ## Conventional Commits -/

/-- The types of a Conventional Commits header that pull request titles, and so the commits of
`main`, use. -/
inductive CommitType where
  /-- A new feature, rule or rule tightening. -/
  | feat
  /-- A bug fix. -/
  | fix
  /-- Documentation only. -/
  | docs
  /-- A change that neither fixes a bug nor adds a feature. -/
  | refactor
  /-- A performance improvement. -/
  | perf
  /-- Tests or checks only. -/
  | test
  /-- The build or dependencies. -/
  | build
  /-- Continuous integration. -/
  | ci
  /-- Maintenance, including release pull requests. -/
  | chore
  /-- A revert of an earlier commit. -/
  | revert
  deriving DecidableEq, Repr

/-- Every commit type. -/
def CommitType.all : List CommitType :=
  [.feat, .fix, .docs, .refactor, .perf, .test, .build, .ci, .chore, .revert]

/-- The type as a header writes it. -/
def CommitType.spelling : CommitType → String
  | .feat => "feat" | .fix => "fix" | .docs => "docs" | .refactor => "refactor"
  | .perf => "perf" | .test => "test" | .build => "build" | .ci => "ci" | .chore => "chore"
  | .revert => "revert"

/-- The type a header spells `s`, if any. -/
def CommitType.ofSpelling (s : String) : Option CommitType := all.find? (·.spelling == s)

/-- Every type is read back from its spelling. -/
theorem CommitType.ofSpelling_spelling (t : CommitType) : ofSpelling t.spelling = some t := by
  cases t <;> decide

/-- A Conventional Commits header `type(scope)!: summary`. -/
structure Header where
  /-- The type. -/
  type : CommitType
  /-- The scope, if any. -/
  scope : Option String
  /-- Whether the commit is a breaking change. -/
  breaking : Bool
  /-- The summary. -/
  summary : String
  deriving Repr

/-- The header `line` writes, if it is a Conventional Commits header `type(scope)!: summary`: a
`CommitType` in lower case, an optional nonempty scope without parentheses, an optional `!` that
marks a breaking change, then `: ` and a summary on the same line that does not start with
whitespace. -/
def parseHeader (line : String) : Option Header := do
  let parts := line.splitOn ": "
  let lead ← parts.head?
  let summary := ": ".intercalate parts.tail
  guard (!summary.isEmpty && summary.trimAsciiStart.toString == summary &&
    !summary.contains '\n' && !summary.contains '\r')
  let breaking := lead.endsWith "!"
  let kind := if breaking then (lead.dropEnd 1).toString else lead
  match kind.splitOn "(" with
  | [type] => return ⟨← CommitType.ofSpelling type, none, breaking, summary⟩
  | [type, rest] =>
    let scope ← (rest.dropSuffix? ")").map (·.toString)
    guard (!scope.isEmpty && !scope.contains '(' && !scope.contains ')')
    return ⟨← CommitType.ofSpelling type, some scope, breaking, summary⟩
  | _ => none

/-- Whether the body of a commit message has a breaking-change footer: a line that starts
`BREAKING CHANGE: ` or `BREAKING-CHANGE: `. -/
def breakingFooter (body : String) : Bool :=
  (body.splitOn "\n").any fun line =>
    line.startsWith "BREAKING CHANGE: " || line.startsWith "BREAKING-CHANGE: "

/-- The header of commit message `message`: its first line, a breaking change also when the rest
has a breaking-change footer; `none` when the first line is not a Conventional Commits header.
A squash commit's message is its pull request's title and description. -/
def parseCommit (message : String) : Option Header :=
  let lines := message.splitOn "\n"
  (parseHeader (lines.headD "")).map fun h =>
    { h with breaking := h.breaking || breakingFooter ("\n".intercalate lines.tail) }

/-! ## The derived version -/

/-- A version bump, in increasing order. -/
inductive Bump where
  /-- Nothing to release. -/
  | none
  /-- A patch release: fixes on the same toolchain. -/
  | patch
  /-- A minor release. -/
  | minor
  /-- A major release. -/
  | major
  deriving DecidableEq, Repr

/-- The position of a bump in increasing order. -/
def Bump.rank : Bump → Nat
  | .none => 0 | .patch => 1 | .minor => 2 | .major => 3

instance : LE Bump := ⟨fun a b => a.rank ≤ b.rank⟩

instance (a b : Bump) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.rank ≤ b.rank))

/-- The greater of two bumps. -/
def Bump.max (a b : Bump) : Bump := if a.rank ≤ b.rank then b else a

/-- The bump as the workflow's input and the logs write it. -/
def Bump.spelling : Bump → String
  | .none => "none" | .patch => "patch" | .minor => "minor" | .major => "major"

/-- The bump spelled `s`, if any. -/
def Bump.ofSpelling (s : String) : Option Bump :=
  [Bump.none, .patch, .minor, .major].find? (·.spelling == s)

/-- A bump is at most its maximum with another. -/
theorem Bump.le_max_left (a b : Bump) : a ≤ a.max b := by
  show a.rank ≤ (a.max b).rank
  unfold Bump.max
  split <;> omega

/-- A bump is at most another's maximum with it. -/
theorem Bump.le_max_right (a b : Bump) : b ≤ a.max b := by
  show b.rank ≤ (a.max b).rank
  unfold Bump.max
  split <;> omega

/-- Bump order is transitive. -/
theorem Bump.le_trans {a b c : Bump} (h : a ≤ b) (h' : b ≤ c) : a ≤ c :=
  Nat.le_trans h h'

/-- The maximum of two bumps is `none` exactly when both are. -/
theorem Bump.max_eq_none_iff (a b : Bump) : a.max b = .none ↔ a = .none ∧ b = .none := by
  cases a <;> cases b <;> decide

/-- The bump commit header `h` calls for, `initial` while the previous release is before 1.0: a
breaking change a major bump (a minor one before 1.0), `feat` a minor one, `fix` and `perf` a
patch, and every other type none. -/
def Header.bump (initial : Bool) (h : Header) : Bump :=
  if h.breaking then (if initial then .minor else .major)
  else match h.type with
    | .feat => .minor
    | .fix | .perf => .patch
    | _ => .none

/-- The bump the commits of `main` since the previous release call for, given their headers
(`parseCommit`): the greatest any of them calls for, `none` when there is none; undecided (no
bump) when a commit's subject is not a Conventional Commits header. -/
def derive (initial : Bool) : List (Option Header) → Option Bump
  | [] => some .none
  | none :: _ => none
  | some h :: rest => (derive initial rest).map (·.max (h.bump initial))

/-- The derived bump is at least the bump of every commit. -/
theorem derive_ge (initial : Bool) :
    ∀ {commits : List (Option Header)} {d : Bump}, derive initial commits = some d →
      ∀ h, some h ∈ commits → h.bump initial ≤ d
  | [], _, _, _, hm => by simp at hm
  | none :: _, _, hd, _, _ => by simp [derive] at hd
  | some h' :: rest, d, hd, h, hm => by
    simp only [derive, Option.map_eq_some_iff] at hd
    obtain ⟨a, ha, rfl⟩ := hd
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      exact Bump.le_max_right _ _
    · exact Bump.le_trans (derive_ge initial ha h hm) (Bump.le_max_left _ _)

/-- The derivation is undecided exactly when a commit's subject is not a Conventional Commits
header. -/
theorem derive_eq_none (initial : Bool) :
    ∀ commits : List (Option Header), derive initial commits = none ↔ none ∈ commits
  | [] => by simp [derive]
  | none :: _ => by simp [derive]
  | some h :: rest => by simp [derive, derive_eq_none initial rest]

/-- The commits call for no release exactly when each is a Conventional Commits header whose
type calls for none: no breaking change, `feat`, `fix` or `perf`. -/
theorem derive_eq_none_bump (initial : Bool) :
    ∀ commits : List (Option Header), derive initial commits = some .none ↔
      ∀ c ∈ commits, ∃ h, c = some h ∧ h.bump initial = .none
  | [] => by simp [derive]
  | none :: _ => by simp [derive]
  | some h :: rest => by
    simp only [derive, Option.map_eq_some_iff, Bump.max_eq_none_iff, List.mem_cons,
      forall_eq_or_imp, Option.some.injEq, exists_eq_left', ← derive_eq_none_bump initial rest]
    constructor
    · rintro ⟨a, ha, rfl, hb⟩; exact ⟨hb, ha⟩
    · rintro ⟨hb, ha⟩; exact ⟨.none, ha, rfl, hb⟩

/-- The bump of the release: the `derived` bump raised to `requested` (the workflow's `bump`
input) when that is greater, or `requested` alone when the derivation is undecided; then at
least `minor` when `lean-toolchain` `moved` from the previous release's. `none` when the
derivation is undecided and nothing was requested; `some .none` when nothing is released. -/
def nextBump (moved : Bool) (derived requested : Option Bump) : Option Bump :=
  let raised := match derived, requested with
    | some d, some r => some (d.max r)
    | some d, none => some d
    | none, r => r
  raised.map fun b => if moved then b.max .minor else b

/-- The workflow never lowers the derived bump. -/
theorem nextBump_ge_derived {moved : Bool} {d : Bump} {requested : Option Bump} {b : Bump}
    (h : nextBump moved (some d) requested = some b) : d ≤ b := by
  unfold nextBump at h
  cases requested <;> cases moved <;> simp only [Option.map_some, Option.some.injEq,
    Bool.false_eq_true, ↓reduceIte] at h <;> subst h
  · exact Nat.le_refl _
  · exact Bump.le_max_left _ _
  · exact Bump.le_max_left _ _
  · exact Bump.le_trans (Bump.le_max_left _ _) (Bump.le_max_left _ _)

/-- A requested bump is honoured: the bump is at least it. -/
theorem nextBump_ge_requested {moved : Bool} {derived : Option Bump} {r b : Bump}
    (h : nextBump moved derived (some r) = some b) : r ≤ b := by
  unfold nextBump at h
  cases derived <;> cases moved <;> simp only [Option.map_some, Option.some.injEq,
    Bool.false_eq_true, ↓reduceIte] at h <;> subst h
  · exact Nat.le_refl _
  · exact Bump.le_max_left _ _
  · exact Bump.le_max_right _ _
  · exact Bump.le_trans (Bump.le_max_right _ _) (Bump.le_max_left _ _)

/-- A release on another toolchain than the previous release's is at least a minor release. -/
theorem nextBump_moved {derived requested : Option Bump} {b : Bump}
    (h : nextBump true derived requested = some b) : Bump.minor ≤ b := by
  unfold nextBump at h
  simp only [↓reduceIte, Option.map_eq_some_iff] at h
  obtain ⟨a, _, rfl⟩ := h
  exact Bump.le_max_right _ _

/-- Without a request, the bump is exactly the derived one, raised to `minor` for a toolchain
move. -/
theorem nextBump_derived (moved : Bool) (d : Bump) :
    nextBump moved (some d) none = some (if moved then d.max .minor else d) := rfl

/-- An undecided derivation with nothing requested releases nothing. -/
theorem nextBump_undecided (moved : Bool) : nextBump moved none none = none := rfl

/-- The version after `v` for bump `b`; none for `none`. A patch bump increments the patch; a
minor one the minor, resetting the patch; a major one the major, resetting both. -/
def Version.bump (v : Version) : Bump → Option Version
  | .none => none
  | .patch => some ⟨v.major, v.minor, v.patch + 1⟩
  | .minor => some ⟨v.major, v.minor + 1, 0⟩
  | .major => some ⟨v.major + 1, 0, 0⟩

/-- The version of the release after `prev` on toolchain `toolchain`, from the headers of the
commits of `main` since `prev` (`parseCommit`) and the workflow's `requested` bump: `prev`'s
semantic version bumped by `nextBump`. None when nothing is released, or when the derivation is
undecided and nothing was requested. -/
def nextVersion (prev : Release) (toolchain : Version) (commits : List (Option Header))
    (requested : Option Bump) : Option Version :=
  (nextBump (prev.toolchain != toolchain) (derive (prev.version.semver.major == 0) commits)
    requested).bind prev.version.semver.bump

/-- A version bumped from a release's semantic version follows it, provided it is not the legacy
release's number and a patch bump keeps the release's toolchain. -/
theorem bump_follows {prev : Release} {toolchain : Version} {b : Bump} {n : Version}
    (h : prev.version.semver.bump b = some n) (hn : n ≠ Version.legacy)
    (ht : b = .patch → prev.toolchain = toolchain) : follows prev ⟨n, toolchain⟩ = true := by
  have hs : n.semver = n := Version.semver_of_ne hn
  cases b with
  | none => simp [Version.bump] at h
  | patch =>
    simp only [Version.bump, Option.some.injEq] at h
    subst h
    simp only [follows, Version.lt_iff, hs, Version.sameLine, Version.lex, ht rfl]
    simp
  | minor =>
    simp only [Version.bump, Option.some.injEq] at h
    subst h
    simp only [follows, Version.lt_iff, hs, Version.sameLine, Version.lex]
    simp
  | major =>
    simp only [Version.bump, Option.some.injEq] at h
    subst h
    simp only [follows, Version.lt_iff, hs, Version.sameLine, Version.lex]
    simp

/-- The derived version follows the previous release (`follows`): it is later, a patch release
keeps its toolchain, and a new line resets the lower components. The legacy release's number
`4.34.0` is excluded: its tag exists, and `admits` refuses it. -/
theorem nextVersion_follows {prev : Release} {toolchain : Version}
    {commits : List (Option Header)} {requested : Option Bump} {n : Version}
    (h : nextVersion prev toolchain commits requested = some n) (hn : n ≠ Version.legacy) :
    follows prev ⟨n, toolchain⟩ = true := by
  unfold nextVersion at h
  obtain ⟨b, hb, hv⟩ := Option.bind_eq_some_iff.mp h
  refine bump_follows hv hn fun hp => ?_
  subst hp
  cases hm : (prev.toolchain != toolchain)
  · simpa using hm
  · rw [hm] at hb
    have := nextBump_moved hb
    exact absurd this (by decide)

/-! ## `RegulaCore/Edition.lean`, `RegulaCore/Rule.lean`, `lakefile.lean` and the adoption guide -/

/-- The first line of `lines` that starts with `pre`, with its index. -/
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

/-- The first line of the definition of `releases`. -/
private def releasesLine : String := "def releases : List ListedRelease :="

/-- The literal `RegulaCore.Edition` writes for a release: its version, then its toolchain. -/
def Release.literal (r : Release) : String := s!"⟨{r.version.literal}, {r.toolchain.literal}⟩"

/-- The releases `releases` lists, in order: the `⟨major, minor, patch⟩` literals between `[`
and `]` of the definition, which spans the lines from `def releases` to the next blank line, read in
pairs, a version then its toolchain. -/
def releasesOf (edition : String) : Except String (List Release) := do
  let lines := edition.splitOn "\n"
  let some (start, _) := findLine lines releasesLine
    | throw s!"RegulaCore/Edition.lean has no `{releasesLine}` line"
  let span := (lines.drop start).takeWhile (!·.trimAscii.isEmpty)
  let text := " ".intercalate span
  let some body := (text.splitOn "[")[1]? | throw "`releases` is not a list literal"
  let some inner := (body.splitOn "]").head? | throw "`releases` is not a list literal"
  let items := ((inner.splitOn "⟨").drop 1).filter (!·.trimAscii.isEmpty)
  let versions ← items.mapM fun item => do
    let some literal := (item.splitOn "⟩").head? | throw s!"unexpected release literal {item}"
    match parseVersion (literal.replace ", " ".") with
    | some v => return v
    | none => throw s!"unexpected release literal {literal}"
  let rec pairs : List Version → Except String (List Release)
    | [] => return []
    | v :: t :: rest => return ⟨v, t⟩ :: (← pairs rest)
    | [v] => throw s!"the release {v.tag} has no toolchain"
  pairs versions

/-- `RegulaCore/Rule.lean` with every `.unreleased` on a line that starts `lifecycle :=` replaced
by release `v`: the introduction of each new rule and the retirement of each newly retired one.
A convenience, not a check: `release_attributes_rules` is what refuses a release build in which
any lifecycle position is still `.unreleased`, however it is written. -/
def stampRules (rules : String) (v : Version) : String :=
  "\n".intercalate <| (rules.splitOn "\n").map fun line =>
    if line.trimAsciiStart.toString.startsWith "lifecycle :=" then
      line.replace ".unreleased" s!"(.release {v.literal})"
    else line

/-- `RegulaCore/Rule.lean` with release `old`, listed but not published, replaced by `new` on every
line that starts `lifecycle :=`: `open` lists the release the commits now call for in place of an
unpublished one. A convenience like `stampRules`: `lifecycle_listed` is what refuses a lifecycle
position that names a release `Regula.releases` does not list. -/
def restampRules (rules : String) (old new : Version) : String :=
  "\n".intercalate <| (rules.splitOn "\n").map fun line =>
    if line.trimAsciiStart.toString.startsWith "lifecycle :=" then
      line.replace s!"(.release {old.literal})" s!"(.release {new.literal})"
    else line

/-- Whether `RegulaCore/Rule.lean` introduces a rule no release has: a line that starts
`lifecycle := .active .unreleased` or `lifecycle := .retired .unreleased`. A convenience:
`introduced_startsLine` is what refuses a patch release that introduces a rule. -/
def introducesRules (rules : String) : Bool :=
  (rules.splitOn "\n").any fun line =>
    let text := line.trimAsciiStart.toString
    text.startsWith "lifecycle := .active .unreleased" ||
      text.startsWith "lifecycle := .retired .unreleased"

/-- `RegulaCore/Edition.lean` with `installed` set to `build` (`none` for `.unreleased`) and
`releases` set to `releases`, written on one line when it fits in 100 characters. -/
def withEdition (edition : String) (build : Option Version) (releases : List Release) :
    Except String String := do
  let lines := edition.splitOn "\n"
  let some (installedAt, _) := findLine lines "def installed : Build := "
    | throw "RegulaCore/Edition.lean has no `def installed` line"
  let some (releasesAt, _) := findLine lines releasesLine
    | throw "RegulaCore/Edition.lean has no `def releases` line"
  let span := ((lines.drop releasesAt).takeWhile (!·.trimAscii.isEmpty)).length
  let installedLine := "def installed : Build := " ++
    (match build with | none => ".unreleased" | some v => ".release " ++ v.literal)
  let literals := releases.map (·.literal)
  let oneLine := releasesLine ++ " [" ++ ", ".intercalate literals ++ "]"
  -- Otherwise the list starts on the next line, each line filled to at most 100 characters.
  let wrapped := literals.zipIdx.foldl (init := ([] : List String)) fun acc (lit, i) =>
    let piece := lit ++ (if i + 1 == literals.length then "]" else ",")
    match acc with
    | [] => ["  [" ++ piece]
    | last :: rest =>
      if (last ++ " " ++ piece).length ≤ 100 then (last ++ " " ++ piece) :: rest
      else ("   " ++ piece) :: last :: rest
  let releaseLines := if oneLine.length ≤ 100 then [oneLine]
    else releasesLine :: wrapped.reverse
  let rewritten := (lines.set installedAt installedLine).zipIdx.flatMap fun (line, i) =>
    if i == releasesAt then releaseLines
    else if releasesAt < i && i < releasesAt + span then []
    else [line]
  let result := "\n".intercalate rewritten
  -- Read the edit back: it must name exactly the intended build and releases.
  unless (← installedOf result) == build && (← releasesOf result) == releases do
    throw "the edited RegulaCore/Edition.lean does not read back as intended"
  return result

/-- The `RegulaCore/Edition.lean` of the release commit of release `r` on a commit of `main` whose
`RegulaCore/Edition.lean` is `edition`, listing `listed`, and whose `lean-toolchain` is
`toolchain`: `edition` with `installed` set to `r`'s version. Refuses a release whose recorded
toolchain is not `toolchain`. `candidate` commits it (`releaseCommit`) and `adopt` derives it in
its workspace, both through this one function. -/
def releaseEdition (edition toolchain : String) (listed : List Release) (r : Release) :
    Except String String := do
  unless toolchainVersion toolchain == some r.toolchain do
    throw s!"lean-toolchain is {toolchain.trimAscii}, not leanprover/lean4:{r.toolchain.tag}, \
      the toolchain {r.version.tag} records"
  withEdition edition (some r.version) listed

/-- The first characters of the `version` line of `lakefile.lean`. -/
private def versionPrefix : String := "  version := v!\""

/-- The `version` line of `lakefile.lean` for version `v`. -/
def versionLine (v : Version) : String := versionPrefix ++ v.spelling ++ "\""

/-- The version the `version := v!"…"` line of `lakefile.lean` declares: a text reading, which
`agree` confirms with Lake's own. -/
def lakefileVersionOf (lakefile : String) : Except String Version := do
  let some (_, line) := findLine (lakefile.splitOn "\n") versionPrefix
    | throw s!"lakefile.lean has no line that starts `{versionPrefix}`"
  let some inner := (line.dropPrefix? versionPrefix).bind (·.toString.dropSuffix? "\"")
    | throw s!"unexpected version line {line}"
  match parseVersion inner.toString with
  | some v => return v
  | none => throw s!"unexpected version line {line}"

/-- `lakefile.lean` declaring version `v` on its `version` line. -/
def withLakeVersion (lakefile : String) (v : Version) : Except String String := do
  let lines := lakefile.splitOn "\n"
  let some (i, _) := findLine lines versionPrefix
    | throw s!"lakefile.lean has no line that starts `{versionPrefix}`"
  let result := "\n".intercalate (lines.set i (versionLine v))
  unless (← lakefileVersionOf result) == v do
    throw "the edited lakefile.lean does not read back as intended"
  return result

/-- The first line of the adoption guide's compatibility table. -/
def tableHeader : String := "| Regula tag | Lean toolchain | Rule reference |"

/-- The adoption guide's compatibility table of `releases`, newest first: each release's tag, its
one toolchain and its rule reference. -/
def compatibilityTable (releases : List Release) : String :=
  "\n".intercalate <| tableHeader :: "| --- | --- | --- |" :: releases.reverse.map fun r =>
    s!"| `{r.version.tag}` | `leanprover/lean4:{r.toolchain.tag}` | \
      [v/{r.version.spelling}/](https://rbeauchamp.github.io/regula/v/{r.version.spelling}/) |"

/-- The compatibility table of adoption guide `guide`: the lines from `tableHeader` to the next
blank line. -/
def tableOf (guide : String) : Option String :=
  let lines := guide.splitOn "\n"
  (findLine lines tableHeader).map fun (i, _) =>
    "\n".intercalate ((lines.drop i).takeWhile (!·.trimAscii.isEmpty))

/-- Adoption guide `guide` with its compatibility table replaced by that of `releases`. -/
def withTable (guide : String) (releases : List Release) : Except String String := do
  let lines := guide.splitOn "\n"
  let some (i, _) := findLine lines tableHeader
    | throw "docs/guides/adoption.md has no compatibility table"
  let span := ((lines.drop i).takeWhile (!·.trimAscii.isEmpty)).length
  let table := compatibilityTable releases
  let result := "\n".intercalate (lines.take i ++ table.splitOn "\n" ++ lines.drop (i + span))
  unless tableOf result == some table do
    throw "the edited docs/guides/adoption.md does not read back as intended"
  return result

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

/-! ## GitHub and `git` -/

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

/-- Run `git` with `args` in the checkout; its standard output without surrounding whitespace, or
a failure with its standard error. -/
private def git (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := "git", args }
  unless out.exitCode == 0 do fail s!"git {args}: {out.stderr}"
  return out.stdout.trimAscii.toString

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

/-- Append `text` to the job summary (`GITHUB_STEP_SUMMARY`), when there is one. -/
private def summarize (text : String) : IO Unit := do
  if let some path ← IO.getEnv "GITHUB_STEP_SUMMARY" then
    let handle ← IO.FS.Handle.mk path .append
    handle.putStr text

/-- Point `branch` at `commit`; its pull request is a maintainer's to open. When one is already
open, start the checks of the rebuilt branch by dispatching `ci.yml` on it, because a push with
the workflow's token starts no workflow. Otherwise write the link that opens it, with `title` and
`body` filled in, to the job summary and the log; opening it starts its checks. The workflow never
creates a pull request: the repository does not let GitHub Actions create one. -/
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
  summarize s!"### Open the pull request `{title}`\n\nThe signed branch `{branch}` names \
    `{commit}`. Open its pull request from [this link]({link}); opening it starts its checks.\n"
  IO.println s!"branch {branch} names {commit}; open its pull request from {link}"

/-- Append `key=value` to the step outputs file `GITHUB_OUTPUT`. -/
private def output (key value : String) : IO Unit := do
  let path ← env "GITHUB_OUTPUT"
  let handle ← IO.FS.Handle.mk path .append
  handle.putStrLn s!"{key}={value}"

/-- The messages of the commits of `main` since release `prev`, newest first: the first-parent
commits after the merge base of its tag's commit and `HEAD`, which is the commit of `main` its
release commit was created on (its parent), or, for the legacy release, whose tag names a commit
of `main`, that commit itself. Needs the checkout's full history and tags. -/
private def messagesSince (prev : Version) : IO (List String) := do
  let tagged ← git #["rev-parse", "--verify", s!"refs/tags/{prev.tag}^\{commit}"]
  let base ← git #["merge-base", tagged, "HEAD"]
  let log ← git #["log", "-z", "--first-parent", "--format=%B", s!"{base}..HEAD"]
  return (log.splitOn "\x00").filterMap fun m =>
    let m := m.trimAscii.toString
    if m.isEmpty then none else some m

/-- The version Lake reads from `lakefile.lean`: `lake reservoir-config`, whose `version` is what
Reservoir indexes a version tag with. -/
private def lakeVersion : IO Version := do
  let out ← IO.Process.output { cmd := "lake", args := #["reservoir-config"] }
  unless out.exitCode == 0 do fail s!"lake reservoir-config: {out.stderr}"
  let json ← IO.ofExcept (Json.parse out.stdout)
  let text ← IO.ofExcept (json.getObjValAs? String "version")
  let some v := parseVersion text
    | fail s!"Lake reads the version {text} from lakefile.lean, not `major.minor.patch`"
  return v

/-! ## Steps -/

/-- `RegulaCore/Edition.lean` in the checkout. -/
private def editionFile : FilePath := "lean/RegulaCore/Edition.lean"

/-- `RegulaCore/Rule.lean` in the checkout. -/
private def rulesFile : FilePath := "lean/RegulaCore/Rule.lean"

/-- The package configuration in the checkout. -/
private def lakefileFile : FilePath := "lakefile.lean"

/-- The adoption guide in the checkout, whose compatibility table lists the releases. -/
private def guideFile : FilePath := "docs/guides/adoption.md"

/-- The release the checked-out commit installs; `none` when it is unreleased. -/
private def installedHere : IO (Option Version) := do
  IO.ofExcept (installedOf (← IO.FS.readFile editionFile))

/-- The derivation of the next version after `prev`, one line per commit, as the job summary and
the log show it. -/
private def derivation (prev : Release) (messages : List String) : String :=
  let initial := prev.version.semver.major == 0
  "\n".intercalate <| messages.map fun m =>
    let subject := (m.splitOn "\n").headD ""
    match parseCommit m with
    | some h => s!"- {(h.bump initial).spelling}: {subject}"
    | none => s!"- undecided, not a Conventional Commits header: {subject}"

/-- Push the branch of the release pull request. On the `main` commit the workflow runs on, derive
the version of the next release (`nextVersion`) from the commits of `main` since the previous
published release, `lean-toolchain` and the `RELEASE_BUMP` input (`derived`, `patch`, `minor` or
`major`; `derived` raises nothing), and commit that release: appended with its toolchain to
`Regula.releases` in place of a listed release not yet published, if any, whose stamps it
restamps (`restampRules`); `lakefile.lean`'s `version` set to it; the adoption guide's
compatibility table regenerated; and the release stamped into each `.unreleased` on a
`lifecycle :=` line (`stampRules`), leaving `Regula.installed` unreleased. Refuses a derivation
that releases nothing, a release `admits` refuses, a patch release when a rule is introduced, an
earlier listed release not yet published, and a `main` that already lists the release with
nothing left to change. -/
def openRelease : IO Unit := do
  let repo ← repository
  let head ← env "GITHUB_SHA"
  let requested ← match (← IO.getEnv "RELEASE_BUMP").getD "derived" with
    | "derived" => pure none
    | s => match Bump.ofSpelling s with
      | some b => pure (some b)
      | none => fail s!"RELEASE_BUMP is {s}; it is derived, patch, minor or major"
  let toolchainText ← IO.FS.readFile "lean-toolchain"
  let some toolchain := toolchainVersion toolchainText
    | fail s!"lean-toolchain is {toolchainText.trimAscii}; a release needs a stable Lean release"
  let edition ← IO.FS.readFile editionFile
  let listed ← IO.ofExcept (releasesOf edition)
  let some last := listed.getLast?
    | fail "RegulaCore/Edition.lean lists no release; the legacy release v4.34.0 is always listed"
  -- A listed release that is not published yet is pending: the derived release takes its place.
  let pending ← if ← published repo last.version.tag then pure none else pure (some last)
  let prior := if pending.isSome then listed.dropLast else listed
  let some prev := prior.getLast?
    | fail s!"release {last.version.tag} is the only listed release, and it is not published"
  unless ← published repo prev.version.tag do
    fail s!"release {prev.version.tag} is listed on main but not published yet; CI on main \
      publishes it"
  let messages ← messagesSince prev.version
  let commits := messages.map parseCommit
  let initial := prev.version.semver.major == 0
  let moved := prev.toolchain != toolchain
  let derived := derive initial commits
  let explained := s!"The {messages.length} commits of main since {prev.version.tag} call for:\n\n\
    {derivation prev messages}\n\nDerived bump: {(derived.map (·.spelling)).getD "undecided"}; \
    requested: {(requested.map (·.spelling)).getD "none"}; lean-toolchain \
    {if moved then s!"moved from {prev.toolchain.spelling} to {toolchain.spelling}, which calls \
      for at least minor" else s!"unchanged at {toolchain.spelling}"}.\n"
  IO.println explained
  summarize s!"### Version derivation\n\n{explained}\n"
  let some v := nextVersion prev toolchain commits requested
    | fail (if derived.isNone && requested.isNone then s!"the derivation is undecided: a commit \
        of main since {prev.version.tag} is not a Conventional Commits header; run the Release \
        workflow again with its bump input set to patch, minor or major"
      else s!"nothing to release: the commits of main since {prev.version.tag} call for no \
        release and lean-toolchain is unchanged; run the Release workflow again with its bump \
        input set to release anyway")
  let next : Release := ⟨v, toolchain⟩
  let tag := v.tag
  unless admits prior next do
    fail s!"{tag} for Lean {toolchain.spelling} does not follow the listed releases: it must be \
      later than each, and follow {prev.version.tag} by the version rules"
  if ← published repo tag then fail s!"release {tag} is published"
  let rules ← IO.FS.readFile rulesFile
  let restamped := match pending with
    | some p => if p.version == v then rules else restampRules rules p.version v
    | none => rules
  if v.semver.patch != 0 && introducesRules restamped then
    fail s!"{tag} is a patch release, but main introduces a rule, which only a minor or major \
      release may (introduced_startsLine); the pull request that added it should have been a \
      feat: run the Release workflow again with its bump input set to minor"
  let stamped := stampRules restamped v
  let releases := prior ++ [next]
  let ready ← IO.ofExcept (withEdition edition none releases)
  let lakefile ← IO.FS.readFile lakefileFile
  let versioned ← IO.ofExcept (withLakeVersion lakefile v)
  let guide ← IO.FS.readFile guideFile
  let tabled ← IO.ofExcept (withTable guide releases)
  if ready == edition && stamped == rules && versioned == lakefile && tabled == guide then
    fail s!"main already lists {tag} and no `lifecycle :=` line says .unreleased; CI on main \
      releases it"
  let replaced := match pending with
    | some p => if p.version == v then "" else s!" in place of {p.version.tag}, not yet published,"
    | none => ""
  let title := s!"chore(release): Regula {tag} for Lean {toolchain.spelling}"
  let commit ← filesCommit repo head
    [(editionFile.toString, ready), (rulesFile.toString, stamped),
      (lakefileFile.toString, versioned), (guideFile.toString, tabled)]
    s!"{title}\n\nLists {tag} for Lean {toolchain.spelling} in Regula.releases{replaced} sets \
      the lakefile's version to {v.spelling}, adds it to the adoption guide's compatibility \
      table and stamps it into each .unreleased on a `lifecycle :=` line; Regula.installed \
      stays unreleased. Once this is on main, CI creates the release commit, which sets \
      Regula.installed to the release, runs main's checks on it and, once they pass, publishes \
      the release, which tags it {tag}."
  pushBranch repo s!"release/{tag}" commit title
    s!"Prepares Regula {tag} for Lean {toolchain.spelling} (`leanprover/lean4:{toolchain.tag}`)\
      {replaced}: lists it with its toolchain in `Regula.releases`, sets `lakefile.lean`'s \
      `version` to `{v.spelling}`, adds it to the compatibility table of the adoption guide and \
      stamps it into each `.unreleased` on a `lifecycle :=` line. `Regula.installed` stays \
      `.unreleased`: `main` never carries a release label.\n\n\
      The Release workflow derived the version from the {messages.length} commits of `main` \
      since {prev.version.tag} (derived bump {(derived.map (·.spelling)).getD "undecided"}, \
      requested {(requested.map (·.spelling)).getD "none"}); its job summary lists each \
      commit's bump.\n\n\
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
      original commit): it stamps that rule too, at the version the commits then call for, on \
      this branch while this pull request is open, and in a new pull request from it once this \
      one has merged.\n\n\
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

/-- Refuse release data that what adopters read contradicts: unless the version Lake reads from
`lakefile.lean` (`lake reservoir-config`) is the one the latest listed release declares
(`Version.declared`), and the adoption guide's compatibility table is `compatibilityTable` of
`Regula.releases`. -/
def agree : IO Unit := do
  let listed ← IO.ofExcept (releasesOf (← IO.FS.readFile editionFile))
  let some latest := listed.getLast? | fail "RegulaCore/Edition.lean lists no release"
  let declared := latest.version.declared
  let lake ← lakeVersion
  unless lake == declared do
    fail s!"Lake reads version {lake.spelling} from lakefile.lean, but the latest listed release \
      {latest.version.tag} declares {declared.spelling}; only the release pull request changes \
      the version"
  let table := compatibilityTable listed
  unless tableOf (← IO.FS.readFile guideFile) == some table do
    fail s!"the compatibility table of {guideFile} is not the one Regula.releases gives; it is \
      \n\n{table}\n"
  IO.println s!"lakefile.lean declares {lake.spelling}, the version of {latest.version.tag}, and \
    the compatibility table lists the {listed.length} listed releases"

/-- Refuse unless the pull request title `TITLE` is a Conventional Commits header
(`parseHeader`): squash merges make it the subject of the pull request's commit on `main`, from
which the Release workflow derives the next version. -/
def requireTitle : IO Unit := do
  let title ← env "TITLE"
  match parseHeader title with
  | some h =>
    IO.println s!"the title is a Conventional Commits header of type {h.type.spelling}\
      {if h.breaking then ", a breaking change" else ""}; before 1.0 its commit calls for a \
      {(h.bump true).spelling} bump, from 1.0 a {(h.bump false).spelling} bump, and a \
      BREAKING CHANGE: footer in the description makes it a breaking change"
  | none =>
    fail s!"the pull request title \"{title}\" is not a Conventional Commits header \
      `type(scope)!: summary` with type one of \
      {", ".intercalate (CommitType.all.map (·.spelling))}, an optional scope, `!` for a \
      breaking change, then `: ` and a summary; squash merges make the title the subject of \
      the commit on main, from which the Release workflow derives the next version \
      (docs/guides/contributing.md#pull-request-titles)"

/-- The release notes written above GitHub's generated list of changes. -/
def notes (r : Release) (repo : String) : String :=
  let tag := r.version.tag
  s!"Regula {tag} supports Lean {r.toolchain.spelling} (`leanprover/lean4:{r.toolchain.tag}`), \
    its only supported toolchain.\n\n\
    Require it in `lakefile.toml`:\n\n\
    ```toml\n[[require]]\nname = \"regula\"\ngit = \"https://github.com/{repo}\"\nrev = \"{tag}\"\n\
    ```\n\n\
    or in `lakefile.lean`: `require regula from git \"https://github.com/{repo}\" @ \"{tag}\"`. \
    Set `lean-toolchain` to `leanprover/lean4:{r.toolchain.tag}`, then run `lake update regula`, \
    `lake exe regula init` and `lake lint`. To update from an earlier release, change the tag, \
    and `lean-toolchain` when this release supports another toolchain, run \
    `lake update regula`, and run `lake exe regula init` again: it rewrites only what the new \
    release changes. The compatibility table of the adoption guide \
    (https://github.com/{repo}/blob/main/docs/guides/adoption.md#1-require-regula) lists every \
    release's toolchain.\n\n\
    The rule reference of this release is \
    https://rbeauchamp.github.io/regula/v/{r.version.spelling}/; \
    `regula-site-{r.version.spelling}.tar.gz` is its permanent copy.\n"

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
  let edition ← editionAt repo commit
  let some v ← IO.ofExcept (installedOf edition)
    | fail s!"{commit} is unreleased; there is nothing to publish"
  let some r := (← IO.ofExcept (releasesOf edition)).find? (·.version == v)
    | fail s!"{commit} installs {v.tag}, which its Regula.releases does not list"
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
  IO.FS.writeFile "tmp/release-notes.md" (notes r repo)
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

/-- The release commit of release `r` on `main`'s commit `head`, whose `RegulaCore/Edition.lean`
is `edition` listing `listed`: a signed child of `head` whose only change sets
`Regula.installed` to `r`'s version. Refuses a release whose recorded toolchain is not
`lean-toolchain`'s. That no rule lifecycle position is still `.unreleased` is not checked here:
the kernel checks it (`release_attributes_rules`) when CI builds the release commit, before
anything is published. -/
def releaseCommit (repo head edition : String) (listed : List Release) (r : Release) :
    IO String := do
  let tag := r.version.tag
  editionCommit repo head
    (← IO.ofExcept (releaseEdition edition (← IO.FS.readFile "lean-toolchain") listed r))
    s!"chore(release): Regula {tag} for Lean {r.toolchain.spelling}\n\nSets Regula.installed to \
      the release. CI created this release commit on {head}, the head of main; it is not on \
      main, and publishing the release {tag} after CI has checked it creates the tag here."

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
  let some r := listed.getLast? | nothing "main lists no release; there is nothing to release"
  let tag := r.version.tag
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
    let commit ← releaseCommit repo head edition listed r
    let tree ← commitTree repo commit
    let branch := s!"release/{tag}-candidate"
    pointBranch repo branch commit
    output "commit" commit
    output "tree" tree
    IO.println s!"created the release commit {commit} (tree {tree}) on {head} as branch \
      {branch}; CI checks it before publishing {tag}"

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
  let some r := listed.getLast? | fail "main lists no release; there is no release commit"
  IO.FS.writeFile editionFile
    (← IO.ofExcept (releaseEdition edition (← IO.FS.readFile "lean-toolchain") listed r))
  discard <| git #["add", "--", editionFile.toString]
  let derived ← git #["write-tree"]
  unless derived == expected do
    fail s!"the release edit of {head} has tree {derived}, not the release commit's tree \
      {expected}"
  let branch := s!"release/{r.version.tag}-candidate"
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

/-- Command line of `lean --run lean/Regula/Release.lean`: `open`, `unreleased`, `agree`,
`title`, `candidate`, `adopt` or `publish`; returns 2 on a usage error. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["open"] => Regula.Release.openRelease; return 0
  | ["unreleased"] => Regula.Release.requireUnreleased; return 0
  | ["agree"] => Regula.Release.agree; return 0
  | ["title"] => Regula.Release.requireTitle; return 0
  | ["candidate"] => Regula.Release.candidate; return 0
  | ["adopt"] => Regula.Release.adopt; return 0
  | ["publish"] => Regula.Release.publish; return 0
  | _ =>
    IO.eprintln "usage: lean --run lean/Regula/Release.lean \
      (open | unreleased | agree | title | candidate | adopt | publish)"
    return 2
