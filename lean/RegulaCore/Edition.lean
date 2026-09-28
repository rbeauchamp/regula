module

public import RegulaCore.RuleId

/-! # Releases, site editions and version-matched links

The rule reference publishes a development edition `dev/`, rebuilt by every deployment of
`main`, and one permanent edition `v/<version>/` for each release. A finding's help link and a
rule's clause links name the edition of the installed Regula build: its release's `v/<version>/`
pages, and `dev/` only for an unreleased build.

## Main declarations

- `ReleaseVersion`, `Build`, `installed`, `releases`, `releases_ascending`, `installed_listed`:
  this build's version and every published release, oldest first.
- `latest`, `latest_greatest`: the latest release is the greatest.
- `Edition`, `Edition.root`, `Build.edition`, `published`, `mem_published`,
  `installed_published`: the editions a deployment publishes, which include the installed
  build's.
- `Edition.url`, `Edition.url_dev_iff`, `helpUrl`, `helpUrl_pagePath`, `helpUrl_release`,
  `helpUrl_unreleased`, `helpUrl_dev_iff`: the help link of a rule targets the installed
  release's page, and `dev/` exactly for an unreleased build.
- `TagState`, `labelAdmitted`, `labelAdmitted_release_iff`, `releaseSource`,
  `releaseSource_render_iff`, `releaseSource_asset_iff`, `publishable`, `publishable_iff`: a
  build carries a release label only while the release's tag is absent or names its commit, and
  renders that release's edition from source only then and before its release asset exists; once
  the asset exists every build takes the edition from it; only a build whose commit the tag names
  may publish a rendered release edition or write its asset.
- `sitePath`, `sitePath_iff`: the route policy of the published artifact: its root files and
  the files of the published editions, nothing else.

## Boundaries

`installed` and `releases` are data that the release steps set (`lean/Regula/Release.lean`).
Whether a release asset exists and which commit a tag names are the site build's observations,
which these decisions take as inputs; that the asset stays the copy attached at the release rests
on GitHub. That a published release's edition is served is the deployment's observation, not a
consequence of these definitions.
-/

@[expose] public section

namespace Regula

/-- A release version `major.minor.patch`. -/
structure ReleaseVersion where
  /-- The major version. -/
  major : Nat
  /-- The minor version. -/
  minor : Nat
  /-- The patch version. -/
  patch : Nat
  deriving DecidableEq, Repr

/-- The version as it is written, such as `0.1.0`. -/
def ReleaseVersion.spelling (v : ReleaseVersion) : String :=
  toString v.major ++ "." ++ toString v.minor ++ "." ++ toString v.patch

/-- The components in significance order, which release order compares lexicographically. -/
def ReleaseVersion.parts (v : ReleaseVersion) : List Nat := [v.major, v.minor, v.patch]

/-- Release order: lexicographic in major, minor and patch. -/
instance : LT ReleaseVersion := ⟨fun a b => a.parts < b.parts⟩

instance (a b : ReleaseVersion) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.parts < b.parts))

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

/-- This build of Regula. It is `.release v` only in the release's pull request and in the commit
on `main` that merging it creates, which tag `v<version>` then names; the reset pull request the
release steps open next sets it back to `.unreleased`. The site build enforces this: it refuses a
build labelled `.release v` once the tag names another commit (`labelAdmitted_release_iff`), so
no other commit that carries the label passes until the reset merges; it renders `v<version>`'s
edition from source only in such a build and only before the release asset exists, and otherwise
takes the frozen asset (`releaseSource`); and only a build whose commit the tag names may publish
a rendered release edition or write the asset (`publishable`). -/
def installed : Build := .unreleased

/-- Every published release, oldest first. The release's pull request appends it. -/
def releases : List ReleaseVersion := []

/-- Releases are listed oldest first, each once. -/
theorem releases_ascending : releases.Pairwise (· < ·) := by decide

/-- A released build is a published release. -/
theorem installed_listed : installed.listedIn releases := by decide

/-- The latest release, if any. -/
def latest : Option ReleaseVersion := releases.getLast?

/-- The latest release is a release, and no release is later. -/
theorem latest_greatest {l : ReleaseVersion} (h : latest = some l) :
    l ∈ releases ∧ ∀ v ∈ releases, v = l ∨ v < l := by
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

/-- The state of the repository's tag `v<version>` for the installed release, as a site build
observes it. An unreleased build has no release tag and observes `absent`. -/
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

/-- A release label is admitted exactly while its tag is absent (the release's own pull request
and commit, before tagging) or names this commit; once the tag names another commit, every build
that still carries the label is refused. -/
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
  /-- The edition this build renders from its own sources. -/
  | render
  deriving DecidableEq, Repr

/-- The machine name of each source in the artifact's `build.json`. -/
def ReleaseSource.spelling : ReleaseSource → String
  | .asset => "asset"
  | .render => "render"

/-- The source of release `v`'s edition in a site build of `b`, given whether `v`'s release asset
exists and the state `tag` of `b`'s release tag: the asset whenever it exists, the rendered
edition only in a build of `v` whose tag is absent or names its commit before the asset exists,
and otherwise `none`, which the build refuses. -/
def releaseSource (b : Build) (v : ReleaseVersion) (assetExists : Bool) (tag : TagState) :
    Option ReleaseSource :=
  if assetExists then some .asset
  else if b = .release v ∧ tag ≠ .other then some .render
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

/-- Whether an artifact whose release editions came from `sources` may be published, and a
rendered release edition written as its asset: a release edition rendered from source only by a
build whose commit the release's tag names. The site build records its value in the artifact's
`build.json`, which `Deployment gate` requires to be `true`. -/
def publishable (sources : List ReleaseSource) (tag : TagState) : Bool :=
  !sources.contains .render || tag == .head

/-- An artifact is publishable exactly when it has no rendered release edition or its commit is
the one the release's tag names. -/
theorem publishable_iff (sources : List ReleaseSource) (tag : TagState) :
    publishable sources tag = true ↔ (.render ∈ sources → tag = .head) := by
  cases tag <;> simp [publishable]

/-- The editions every deployment publishes: the development edition and each release's. -/
def published : List Edition := .dev :: releases.map .release

/-- An edition is published exactly when it is the development edition or a release's. -/
theorem mem_published (e : Edition) :
    e ∈ published ↔ e = .dev ∨ ∃ v ∈ releases, e = .release v := by
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
