module

public import RegulaCore.RuleId

/-! # Releases, site editions and version-matched links

The rule reference publishes a development edition `dev/`, rebuilt by every deployment of
`main`, and one permanent edition `v/<version>/` for each release. A finding's help link and a
rule's clause links name the edition of the installed Regula build: its release's `v/<version>/`
pages, and `dev/` only for an unreleased build.

## Main declarations

- `ReleaseVersion`, `ReleaseVersion.legacy`, `ReleaseVersion.semver`, `LeanRelease`,
  `ListedRelease`, `ListedRelease.follows`, `Build`, `installed`, `releases`, `versions`,
  `releases_ascending`, `releases_follow`, `installed_listed`: this build's version and every
  listed release with the one Lean toolchain it supports, oldest first, each following its
  predecessor by the version rules.
- `follows_startsLine_iff`: a release that follows its predecessor has patch version `0` exactly
  when it is not a patch release.
- `latest`, `latest_greatest`: the latest release is the greatest.
- `Edition`, `Edition.root`, `Build.edition`, `published`, `mem_published`,
  `installed_published`: the editions a deployment publishes, which include the installed
  build's.
- `Edition.url`, `Edition.url_dev_iff`, `helpUrl`, `helpUrl_pagePath`, `helpUrl_release`,
  `helpUrl_unreleased`, `helpUrl_dev_iff`: the help link of a rule targets the installed
  release's page, and `dev/` exactly for an unreleased build.
- `TagState`, `labelAdmitted`, `labelAdmitted_release_iff`, `labelAdmitted_unreleased`,
  `releaseSource`, `releaseSource_render_iff`, `releaseSource_asset_iff`,
  `releaseSource_preview_iff`, `publishable`, `publishable_iff`: a build carries a release label
  only while the release's tag is absent or names its commit; only such a build renders the
  release's edition from source, and only before its release asset exists; once the asset exists
  every build takes the edition from it; an unreleased build previews only the latest listed
  release, and only while neither its asset nor its tag exists; and only an artifact whose every
  release edition is its asset is deployed.
- `sitePath`, `sitePath_iff`: the route policy of the published artifact: its root files and
  the files of the published editions, nothing else.

## Boundaries

`installed` and `releases` are data that the release steps set (`lean/Regula/Release.lean`).
That Lake and Reservoir read each release's version from its `lakefile.lean` is their
behaviour, not a consequence of these definitions (`Regula.Release.Version.lakeLt_declared`).
Whether a release asset exists and which commit a tag names are the site build's observations,
which these decisions take as inputs; that the asset stays the copy attached at the release rests
on GitHub. That a published release's edition is served is the deployment's observation, not a
consequence of these definitions.
-/

@[expose] public section

namespace Regula

/-- A release version `major.minor.patch`: Regula's own semantic version, which its tag
`v<version>` and its `lakefile.lean`'s `version` carry, except for the legacy release. -/
structure ReleaseVersion where
  /-- The major version. -/
  major : Nat
  /-- The minor version. -/
  minor : Nat
  /-- The patch version. -/
  patch : Nat
  deriving DecidableEq, Repr

/-- The version as it is written, such as `0.2.0`. -/
def ReleaseVersion.spelling (v : ReleaseVersion) : String :=
  toString v.major ++ "." ++ toString v.minor ++ "." ++ toString v.patch

/-- The legacy release `v4.34.0`, Regula's first: numbered by the Lean release it supports before
Regula numbered its own releases. Its tag, its lifecycle stamps and its edition `v/4.34.0/` keep
that number. -/
def ReleaseVersion.legacy : ReleaseVersion := ⟨4, 34, 0⟩

/-- The semantic version of a release, which orders releases: its own version, and `0.1.0` for
the legacy release, so that release precedes every own-numbered one, the first of which is
`0.2.0`. -/
def ReleaseVersion.semver (v : ReleaseVersion) : ReleaseVersion :=
  if v = legacy then ⟨0, 1, 0⟩ else v

/-- The components of the semantic version in significance order, which release order compares
lexicographically. -/
def ReleaseVersion.parts (v : ReleaseVersion) : List Nat :=
  [v.semver.major, v.semver.minor, v.semver.patch]

/-- The release line: the major and minor components of the semantic version, which a patch
release keeps. -/
def ReleaseVersion.line (v : ReleaseVersion) : List Nat := [v.semver.major, v.semver.minor]

/-- Release order: lexicographic in the major, minor and patch components of the semantic
versions. -/
instance : LT ReleaseVersion := ⟨fun a b => a.parts < b.parts⟩

instance (a b : ReleaseVersion) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.parts < b.parts))

/-- Three-component lexicographic order with equal leading components compares the last. -/
private theorem lex3 {m n p q : Nat} (h : List.Lex (· < ·) [m, n, p] [m, n, q]) : p < q := by
  cases h with
  | rel h => exact absurd h (Nat.lt_irrefl _)
  | cons h => cases h with
    | rel h => exact absurd h (Nat.lt_irrefl _)
    | cons h => cases h with
      | rel h => exact h
      | cons h => cases h

/-- A later release on the same line has a greater patch component. -/
theorem ReleaseVersion.patch_lt_of_line {a b : ReleaseVersion} (hl : a.line = b.line)
    (h : a < b) : a.semver.patch < b.semver.patch := by
  have h' : List.Lex (· < ·) [a.semver.major, a.semver.minor, a.semver.patch]
      [b.semver.major, b.semver.minor, b.semver.patch] := h
  simp only [ReleaseVersion.line, List.cons.injEq, and_true] at hl
  rw [hl.1, hl.2] at h'
  exact lex3 h'

/-- A stable Lean release `major.minor.patch`: the toolchain
`leanprover/lean4:v<major>.<minor>.<patch>`. -/
structure LeanRelease where
  /-- The major version. -/
  major : Nat
  /-- The minor version. -/
  minor : Nat
  /-- The patch version. -/
  patch : Nat
  deriving DecidableEq, Repr

/-- The Lean release as it is written, such as `4.34.0`. -/
def LeanRelease.spelling (t : LeanRelease) : String :=
  toString t.major ++ "." ++ toString t.minor ++ "." ++ toString t.patch

/-- The `lean-toolchain` of the Lean release. -/
def LeanRelease.toolchain (t : LeanRelease) : String := "leanprover/lean4:v" ++ t.spelling

/-- A release of Regula: its version and the one Lean toolchain it supports, the
`lean-toolchain` of its release commit. -/
structure ListedRelease where
  /-- The release version. -/
  version : ReleaseVersion
  /-- The Lean release of the one toolchain the release supports. -/
  toolchain : LeanRelease
  deriving DecidableEq, Repr

/-- Whether release `next` may directly follow release `prev`, by Semantic Versioning over the
semantic versions: `next` is later; a patch release (one that keeps `prev`'s line) keeps
`prev`'s toolchain, so a release on another toolchain bumps at least the minor version; and a
release that starts a new line has patch `0`, and minor `0` too when it bumps the major version.
`Regula.Release.follows` is the decision the release steps execute. -/
def ListedRelease.follows (prev next : ListedRelease) : Bool :=
  decide (prev.version < next.version) &&
    if prev.version.line = next.version.line then prev.toolchain == next.toolchain
    else next.version.semver.patch == 0 &&
      (next.version.semver.major == prev.version.semver.major || next.version.semver.minor == 0)

/-- A release that follows its predecessor has patch version `0` exactly when it is not a patch
release: when it starts a new line. -/
theorem follows_startsLine_iff {prev next : ListedRelease} (h : prev.follows next = true) :
    next.version.semver.patch = 0 ↔ prev.version.line ≠ next.version.line := by
  unfold ListedRelease.follows at h
  by_cases hl : prev.version.line = next.version.line
  · simp only [hl, ite_true, Bool.and_eq_true, decide_eq_true_eq] at h
    have := ReleaseVersion.patch_lt_of_line hl h.1
    simp only [hl, ne_eq, not_true_eq_false, iff_false]
    omega
  · simp only [hl, ite_false, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    simp only [ne_eq, hl, not_false_eq_true, iff_true]
    exact h.2.1

/-- What a Regula build is: a release, or an unreleased development build. -/
inductive Build where
  /-- The release `version`. -/
  | release (version : ReleaseVersion)
  /-- A build of an unreleased commit. -/
  | unreleased
  deriving DecidableEq, Repr

/-- The version text of a build in reports and on the site: the release, or `unreleased`. -/
def Build.spelling : Build → String
  | .release v => v.spelling
  | .unreleased => "unreleased"

/-- A build is a release among `rs`, or unreleased. -/
def Build.listedIn (b : Build) (rs : List ReleaseVersion) : Prop :=
  match b with
  | .release v => v ∈ rs
  | .unreleased => True

instance (b : Build) (rs : List ReleaseVersion) : Decidable (b.listedIn rs) := by
  cases b <;> unfold Build.listedIn <;> infer_instance

/-- Whether a build may introduce a rule: an unreleased build, or a release whose semantic version
has patch `0`, which starts a release line (`follows_startsLine_iff`). -/
def Build.startsLine : Build → Bool
  | .release v => v.semver.patch == 0
  | .unreleased => true

/-- This build of Regula: always `.unreleased` on `main` and in every pull request, which CI's
required `verify` job checks. The only build labelled `.release v` is the release commit that CI
on `main` creates once `main` lists `v` unpublished: a child of the head of `main`, not on `main`,
whose only change sets this label. CI checks it with its label (acceptance, the rule-example
shards and the site build) before anything is published; publishing the release then creates tag
`v<version>` at it, and once the release is published nothing changes
(`Regula.Release.tagAction` in `lean/Regula/Release.lean`, with its theorems). The site build
refuses a build labelled `.release v` once the tag names another commit (`labelAdmitted`); it
renders `v<version>`'s edition from source only in a build of `v` while the tag is absent or
names its commit, and only before the release asset exists; an unreleased build, such as the
release pull request's, previews the latest listed release's edition while neither its asset nor
its tag exists, and every other build takes the frozen asset (`releaseSource`); and only an
artifact whose every release edition is its asset is deployed (`publishable`). -/
def installed : Build := .unreleased

/-- Every release with the one Lean toolchain it supports, oldest first. The release pull request
appends it; CI on `main` then publishes it. -/
def releases : List ListedRelease :=
  [⟨⟨4, 34, 0⟩, ⟨4, 34, 0⟩⟩, ⟨⟨0, 2, 0⟩, ⟨4, 34, 0⟩⟩, ⟨⟨0, 3, 0⟩, ⟨4, 34, 0⟩⟩,
   ⟨⟨0, 3, 1⟩, ⟨4, 34, 0⟩⟩, ⟨⟨0, 4, 0⟩, ⟨4, 34, 0⟩⟩, ⟨⟨0, 4, 1⟩, ⟨4, 34, 0⟩⟩,
   ⟨⟨0, 4, 2⟩, ⟨4, 34, 0⟩⟩, ⟨⟨0, 4, 3⟩, ⟨4, 34, 0⟩⟩]

/-- The version of every release, oldest first. -/
def versions : List ReleaseVersion := releases.map (·.version)

/-- Releases are listed oldest first, each once. -/
theorem releases_ascending : versions.Pairwise (· < ·) := by decide

/-- Every release follows its predecessor (`ListedRelease.follows`). -/
theorem releases_follow : (releases.zip releases.tail).all (fun p => p.1.follows p.2) = true := by
  decide

/-- A released build is a listed release. -/
theorem installed_listed : installed.listedIn versions := by decide

/-- The latest release, if any. -/
def latest : Option ReleaseVersion := versions.getLast?

/-- The latest release is a release, and no release is later. -/
theorem latest_greatest {l : ReleaseVersion} (h : latest = some l) :
    l ∈ versions ∧ ∀ v ∈ versions, v = l ∨ v < l := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp h
  have hp := releases_ascending
  rw [hys] at hp ⊢
  refine ⟨by simp, fun v hv => ?_⟩
  rcases List.mem_append.mp hv with hv | hv
  · exact Or.inr ((List.pairwise_append.mp hp).2.2 v hv l (by simp))
  · exact Or.inl (by simpa using hv)

/-- An edition of the rule reference. -/
inductive Edition where
  /-- The development edition, rebuilt by every deployment of `main`. -/
  | dev
  /-- The permanent edition of the release `version`. -/
  | release (version : ReleaseVersion)
  deriving DecidableEq, Repr

/-- The edition's directory below the project site root. -/
def Edition.root : Edition → String
  | .dev => "dev/"
  | .release v => "v/" ++ v.spelling ++ "/"

/-- Directory route of a rule page within an edition, derived from the rule identity. -/
def Edition.pagePath (e : Edition) (id : RuleId) : String := e.root ++ id.route

/-- Artifact file of a rule page. -/
def Edition.pageFile (e : Edition) (id : RuleId) : String := e.pagePath id ++ "index.html"

/-- Distinct rules have distinct routes in every edition. -/
theorem Edition.pagePath_injective (e : Edition) {a b : RuleId}
    (h : e.pagePath a = e.pagePath b) : a = b :=
  RuleId.route_injective ((String.append_right_inj _).mp h)

/-- Distinct rules have distinct page files in every edition. -/
theorem Edition.pageFile_injective (e : Edition) {a b : RuleId}
    (h : e.pageFile a = e.pageFile b) : a = b :=
  e.pagePath_injective ((String.append_left_inj _).mp h)

/-- The edition whose pages describe a build: its release's, or the development edition. -/
def Build.edition : Build → Edition
  | .release v => .release v
  | .unreleased => .dev

/-- Only an unreleased build is described by the development edition. -/
theorem Build.edition_eq_dev_iff (b : Build) : b.edition = .dev ↔ b = .unreleased := by
  cases b <;> simp [Build.edition]

/-- The state of a release's tag `v<version>` in the repository relative to a site build's
commit, as the build observes it. `labelAdmitted` takes the state of the installed release's tag,
where an unreleased build has no release tag and observes `absent`; `releaseSource` takes the
state of the tag of the release whose edition it decides, in a released and an unreleased build
alike. -/
inductive TagState where
  /-- The tag does not exist yet. -/
  | absent
  /-- The tag names the build's commit. -/
  | head
  /-- The tag names another commit. -/
  | other
  deriving DecidableEq, Repr

/-- Whether build `b` may carry its label, given the state `tag` of its release's tag. -/
def labelAdmitted : Build → TagState → Bool
  | .release _, .other => false
  | _, _ => true

/-- A release label is admitted exactly while its tag is absent (the release commit that CI checks
before publication creates the tag) or names this commit; once the tag names another commit, every
build that carries the label is refused. -/
theorem labelAdmitted_release_iff {v : ReleaseVersion} {tag : TagState} :
    labelAdmitted (.release v) tag = true ↔ tag = .absent ∨ tag = .head := by
  cases tag <;> simp [labelAdmitted]

/-- An unreleased build is always admitted. -/
theorem labelAdmitted_unreleased (tag : TagState) : labelAdmitted .unreleased tag = true := by
  cases tag <;> rfl

/-- Where a site build takes a release's edition from. -/
inductive ReleaseSource where
  /-- The frozen copy: the release asset attached at the release. -/
  | asset
  /-- The edition this build renders from its own sources, as a build of that release. -/
  | render
  /-- A stand-in for the edition of a release not yet published: the edition an unreleased build
  renders from its own sources, which carries no release label. -/
  | preview
  deriving DecidableEq, Repr

/-- The machine name of each source in the artifact's `build.json`. -/
def ReleaseSource.spelling : ReleaseSource → String
  | .asset => "asset"
  | .render => "render"
  | .preview => "preview"

/-- The source of release `v`'s edition in a site build of `b`, given whether `v`'s release asset
exists and the state `tag` of tag `v<version>` of `v` relative to the build's commit: the asset
whenever it exists; before it exists, the rendered edition in a build of `v` whose tag is absent
or names its commit, and a preview in an unreleased build while `v` is the latest listed release
and its tag is absent, which is a release CI on `main` has yet to publish; and otherwise `none`,
which the build refuses. -/
def releaseSource (b : Build) (v : ReleaseVersion) (assetExists : Bool) (tag : TagState) :
    Option ReleaseSource :=
  if assetExists then some .asset
  else if b = .release v ∧ tag ≠ .other then some .render
  else if b = .unreleased ∧ latest = some v ∧ tag = .absent then some .preview
  else none

/-- A release's edition is rendered from source only by a build of that release before its asset
exists, while its tag is absent or names the build's commit. -/
theorem releaseSource_render_iff (b : Build) (v : ReleaseVersion) (assetExists : Bool)
    (tag : TagState) : releaseSource b v assetExists tag = some .render ↔
      assetExists = false ∧ b = .release v ∧ (tag = .absent ∨ tag = .head) := by
  unfold releaseSource
  cases assetExists <;> cases tag <;> by_cases h : b = .release v <;> simp_all

/-- Once a release asset exists, every build takes that release's edition from it. -/
theorem releaseSource_asset_iff (b : Build) (v : ReleaseVersion) (assetExists : Bool)
    (tag : TagState) : releaseSource b v assetExists tag = some .asset ↔ assetExists = true := by
  unfold releaseSource
  cases assetExists <;> cases tag <;> by_cases h : b = .release v <;> simp_all

/-- A release's edition is previewed only by an unreleased build, only for the latest listed
release, and only while neither its asset nor its tag exists. A release whose tag exists and
whose asset is missing is therefore refused, never previewed; that publishing a release is what
creates its tag is the release steps' behaviour (`lean/Regula/Release.lean`), not a consequence
of these definitions. -/
theorem releaseSource_preview_iff (b : Build) (v : ReleaseVersion) (assetExists : Bool)
    (tag : TagState) : releaseSource b v assetExists tag = some .preview ↔
      assetExists = false ∧ b = .unreleased ∧ latest = some v ∧ tag = .absent := by
  unfold releaseSource
  cases assetExists <;> cases tag <;> cases b <;> simp

/-- Whether an artifact whose release editions came from `sources` may be deployed: every release
edition is its frozen asset, none rendered from source and none a preview. The release commit's
site build renders its release's edition only to write it as the release asset, and an unreleased
build previews one only to check the rest of its artifact; the site build records this value in
the artifact's `build.json`, which `Deployment gate` requires to be `true`. -/
def publishable (sources : List ReleaseSource) : Bool := sources.all (· == .asset)

/-- An artifact is publishable exactly when every release edition in it is its frozen asset. -/
theorem publishable_iff (sources : List ReleaseSource) :
    publishable sources = true ↔ ∀ s ∈ sources, s = .asset := by
  simp [publishable]

/-- The editions every deployment publishes: the development edition and each release's. -/
def published : List Edition := .dev :: versions.map .release

/-- An edition is published exactly when it is the development edition or a release's. -/
theorem mem_published (e : Edition) :
    e ∈ published ↔ e = .dev ∨ ∃ v ∈ versions, e = .release v := by
  simp [published, eq_comm]

/-- The edition describing the installed build is published. -/
theorem installed_published : installed.edition ∈ published := by
  have h := installed_listed
  revert h
  cases installed with
  | unreleased => intro _; simp [Build.edition, published]
  | release v => intro h; exact (mem_published _).mpr (Or.inr ⟨v, h, rfl⟩)

/-- The GitHub Pages project-site origin every edition lives under. -/
def siteBase : String := "https://rbeauchamp.github.io/regula/"

/-- The URL of `route` in edition `e`; `route` is relative to the edition root. -/
def Edition.url (e : Edition) (route : String) : String := siteBase ++ e.root ++ route

/-- A development-edition URL names the development edition. -/
theorem Edition.url_dev_iff (e : Edition) (route : String) :
    e.url route = Edition.dev.url route ↔ e = .dev := by
  constructor
  · intro h
    have hroot : e.root = "dev/" := by
      have := (String.append_left_inj route).mp h
      exact (String.append_right_inj siteBase).mp this
    cases e with
    | dev => rfl
    | release v =>
      have := congrArg String.toList hroot
      simp [Edition.root, String.toList_append] at this
  · intro h; rw [h]

/-- The rule-reference page of `id` in the installed build's edition: a human pointer, never the
only source of the fix (every diagnostic carries the remedy itself). -/
def helpUrl (id : RuleId) : String := installed.edition.url id.route

/-- The help link is the rule's page route in the installed build's edition, which every
deployment publishes (`installed_published`). -/
theorem helpUrl_pagePath (id : RuleId) :
    helpUrl id = siteBase ++ installed.edition.pagePath id := by
  simp [helpUrl, Edition.url, Edition.pagePath, String.append_assoc]

/-- A release's help link is its own edition's page. -/
theorem helpUrl_release {v : ReleaseVersion} (h : installed = .release v) (id : RuleId) :
    helpUrl id = siteBase ++ ("v/" ++ v.spelling ++ "/") ++ id.route := by
  simp [helpUrl, h, Build.edition, Edition.url, Edition.root]

/-- An unreleased build's help link is the development page. -/
theorem helpUrl_unreleased (h : installed = .unreleased) (id : RuleId) :
    helpUrl id = siteBase ++ "dev/" ++ id.route := by
  simp [helpUrl, h, Build.edition, Edition.url, Edition.root]

/-- The help link is a development page exactly when the installed build is unreleased. -/
theorem helpUrl_dev_iff (id : RuleId) :
    helpUrl id = Edition.dev.url id.route ↔ installed = .unreleased :=
  (Edition.url_dev_iff _ _).trans (Build.edition_eq_dev_iff _)

/-- The files of the published artifact outside its editions. -/
def rootFiles : List String := ["index.html", "404.html", "build.json"]

/-- Whether `path` belongs to the published site: a root file or a file of a published
edition. The site build refuses an artifact with any other path. -/
def sitePath (path : String) : Bool :=
  rootFiles.contains path || published.any fun e => path.startsWith e.root

/-- The route policy: a path is published exactly when it is a root file or lies in the
development edition or a release's edition. -/
theorem sitePath_iff (path : String) :
    sitePath path = true ↔ path ∈ rootFiles ∨ ∃ e ∈ published, path.startsWith e.root = true := by
  simp [sitePath]

end Regula
