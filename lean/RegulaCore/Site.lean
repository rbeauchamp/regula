import RegulaCore.Account
import RegulaCore.Guide
import Regula.Contract
import Std.Data.HashMap
import Regula.Decision

/-! # Rule-reference site: routes, editions and pure output checks

This module is the pure model of the published rule reference. The operational builder in
`Regula.Site` reads evidence, runs Verso and walks the output tree; every decision it takes
about that data is a function here. The editions and the route policy are
`RegulaCore.Edition`.

## Main declarations

- `pageFiles`, `pageFiles_nodup`, `mem_pageFiles`: the rule pages of an edition, derived only
  from the closed `RuleId`: duplicate-free and total over the registry. `artifactBudget`
  bounds the artifact's size.
- `rootEdition`, `rootEdition_eq_dev_iff`, `rootEdition_eq_release_iff`, `rootEdition_published`:
  the edition the project-site root opens is the greatest release's, or the development edition
  exactly while no release exists, and it is published.
- `pageRoute`, `stablePage`, `stablePages`, `mem_stablePages`, `sitePath_of_mem_stablePages`,
  `stableTarget`: the stable routes, which name no edition: one for each HTML page of
  `rootEdition` below a `stableRoots` directory, and the address it opens, the same page of
  that edition.
- `siteAnchors`: the pages and fragments that a document names on the site, which the site
  build checks against the artifact for the root `README.md`, by `missingAnchors`.
- `bannerRelease`, `bannerRelease_eq_some`, `bannerTarget`, `bannerTarget_mem`, `outdatedBanner`,
  `bannerAnchor`, `insertBanner`, `insertBanner_ok`: the note at the top of every page of an
  earlier release's edition, which names the latest release and links the same page there, or
  that edition's home page when the page does not exist there.
- `escape`, `escape_safe`: HTML text escaping; escaped text contains none of the markup
  characters `<`, `>`, `"`, `'` or the backtick that would end a Verso code fence.
- `htmlBlock`, `htmlBlock_ok`: the only way the generator inserts raw HTML into Verso source (by
  inspection of the generator; guide prose and clause labels enter as Verso markup).
- `Selection`, `emptySelections`, `mem_emptySelections`: the index filters and the exact
  set of filter combinations for which the no-match notice is shown.
- `admitDiff`: a line diff admitted only when it reproduces both compared texts.
- `Tag`, `scanTags`, `LinkOK`, `linkErrors`, `linkErrors_nil_iff`: link validation of an
  output tree against the project base path, through an index of the pages by path
  (`mem_pageIndex`, `linkOKIn_pageIndex`).
- `standardAnchors`, `missingAnchors`, `missingAnchors_nil_iff`: the section and checklist-row
  anchors the registry links, checked against the rendered standard's pages.
- `standardUrl`, `routesAfter`, `routeAnchor`, `documentAnchors`: the pages and anchors that
  documentation links in the development standard, checked by the same `missingAnchors`.
- `renderedRows`, `rowsMismatch`, `rowsMismatch_eq_none_iff`: the checklist rows of a rendered
  page, which must be exactly `checklistRows`; `guide_checklist_listed`: every row a rule
  explanation lists is one of them.
- `rulesOfRow`, `mem_rulesOfRow`, `residualsOfRow`, `mem_residualsOfRow`: the checklist coverage
  page's rules and review obligations of each row, the inverses of the explanations' `checklist`
  and of `Residual.rows` by construction; `residual_rows_listed`, `residualsOfRow_ne_nil`: every
  obligation carries checklist rows, and every checklist row carries an obligation.

## Assumptions and boundaries

`scanTags` is a small HTML tokenizer for the builder's own output. `linkErrors_nil_iff`
states that every link it extracted resolves; it does not prove that the tokenizer finds
every link a browser would follow, that GitHub Pages serves the files, or that external
links are live. `routesAfter` finds each literal occurrence of `standardUrl`; a link into the
standard written any other way (relative, another edition, percent-encoded) is not found.
`siteAnchors` finds each literal occurrence of `siteBase` the same way, and reads the route after
it up to the first character that is not `isRouteChar`, so an address written any other way is
not found and a route with such a character, a `.` for example, is read only up to it.
`renderedRows` relies on the standard's `checklistRow` role being the only producer of
`checklistRowClass` (by inspection of `website/RegulaExample.lean`). `insertBanner` relies on
Verso writing each page's content column as `bannerAnchor`; the build refuses a page without
exactly one. Deployment, Verso rendering and browser behavior are operational observations
recorded by the builder and in the website guide.
-/

namespace Regula.Site

open Regula.Checker.Account (Residual)

/-- The repository whose sources the site documents. -/
def repository : String := "https://github.com/rbeauchamp/regula"

/-- The one-line description of Regula that link previews show. -/
def tagline : String :=
  "A strict linter for Lean: no holes, no hidden axioms, no unstated trust, and a fix for every \
    finding."

/-- The URL path of the project site. Absolute links in the output must start with it. -/
def basePath : String := "/regula/"

/-! ## Identity and routes -/

/-- Lowercase hexadecimal digit. -/
def isHexLower (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- A full lowercase hexadecimal Git commit identifier. -/
def IsCommit (s : String) : Prop := s.length = 40 ∧ s.toList.all isHexLower = true

instance (s : String) : Decidable (IsCommit s) := inferInstanceAs (Decidable (_ ∧ _))

/-- A validated commit identifier. -/
abbrev Commit := { s : String // IsCommit s }

/-- The commit identifier `s`, when it is 40 lowercase hexadecimal digits (`IsCommit`). -/
def Commit.parse? (s : String) : Option Commit :=
  if h : IsCommit s then some ⟨s, h⟩ else none

/-- Every rule page of an edition, in registry order. -/
def pageFiles (e : Edition) : List String := RuleId.all.map e.pageFile

/-- The page inventory has no duplicate route. -/
theorem pageFiles_nodup (e : Edition) : (pageFiles e).Nodup :=
  List.Pairwise.map e.pageFile (fun _ _ h eq => h (e.pageFile_injective eq)) RuleId.all_nodup

/-- The page inventory contains every registered rule. -/
theorem mem_pageFiles (e : Edition) (id : RuleId) : e.pageFile id ∈ pageFiles e :=
  List.mem_map_of_mem (RuleId.mem_all id)

/-- Upper bound on an artifact's total file bytes, below GitHub Pages' 1 GB limit on a published
site. Each release adds one permanent edition. -/
def artifactBudget : Nat := 900000000

/-! ## HTML text -/

/-- Characters that end HTML text or attribute values, or a Verso code fence. -/
def markupChar (c : Char) : Bool :=
  c == '<' || c == '>' || c == '"' || c == '\'' || c == '`'

/-- Entity for one character; every other character is kept. -/
def escapeChar (c : Char) : List Char :=
  if c = '&' then ['&', 'a', 'm', 'p', ';']
  else if c = '<' then ['&', 'l', 't', ';']
  else if c = '>' then ['&', 'g', 't', ';']
  else if c = '"' then ['&', 'q', 'u', 'o', 't', ';']
  else if c = '\'' then ['&', '#', '3', '9', ';']
  else if c = '`' then ['&', '#', '9', '6', ';']
  else [c]

/-- Escape text for HTML element content or a quoted attribute value. -/
def escape (s : String) : String := String.ofList (s.toList.flatMap escapeChar)

theorem escapeChar_safe (c d : Char) (h : d ∈ escapeChar c) : markupChar d = false := by
  unfold escapeChar at h
  by_cases h1 : c = '&' <;> simp only [h1, ite_true, ite_false] at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide
  by_cases h2 : c = '<' <;> simp only [h2, ite_true, ite_false] at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> decide
  by_cases h3 : c = '>' <;> simp only [h3, ite_true, ite_false] at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> decide
  by_cases h4 : c = '"' <;> simp only [h4, ite_true, ite_false] at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  by_cases h5 : c = '\'' <;> simp only [h5, ite_true, ite_false] at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide
  by_cases h6 : c = '`' <;> simp only [h6, ite_true, ite_false] at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [List.mem_singleton] at h
  subst h
  simp [markupChar, h2, h3, h4, h5, h6]

/-- Escaped text cannot open or close a tag or attribute value, or a Verso fence. -/
theorem escape_safe (s : String) : ∀ d ∈ (escape s).toList, markupChar d = false := by
  intro d hd
  simp only [escape, String.toList_ofList, List.mem_flatMap] at hd
  obtain ⟨c, _, hc⟩ := hd
  exact escapeChar_safe c d hc

/-- Raw HTML enters a generated Verso document only as a fenced `html` block, and only when
it contains no backtick, so no line of it can close the fence. -/
def htmlBlock (html : String) : Except String String :=
  if html.toList.contains '`' then .error "raw HTML contains a backtick"
  else .ok ("```html\n" ++ html ++ "\n```\n")

/-- Admission of a raw block is exactly the absence of backticks, and the block is exactly
the fenced input. -/
theorem htmlBlock_ok (html out : String) (h : htmlBlock html = .ok out) :
    html.toList.contains '`' = false ∧ out = "```html\n" ++ html ++ "\n```\n" := by
  unfold htmlBlock at h
  split at h
  · cases h
  · rename_i hc
    exact ⟨by simpa using hc, (Except.ok.inj h).symm⟩

/-- Escaped text never makes a block inadmissible: escaping is the data path into raw HTML. -/
theorem escape_no_backtick (s : String) : (escape s).toList.contains '`' = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hm := escape_safe s '`' (by simpa using h)
  simp [markupChar] at hm

/-! ## Site root -/

/-- The edition the project-site root opens, the stable address the repository links: the latest
release's edition, or the development edition while no release exists. -/
def rootEdition : Edition :=
  match latest with
  | some l => .release l
  | none => .dev

/-- The site root opens the development edition exactly while no release exists. -/
theorem rootEdition_eq_dev_iff : rootEdition = .dev ↔ versions = [] := by
  rw [← List.getLast?_eq_none_iff]
  unfold rootEdition latest
  cases versions.getLast? <;> simp

/-- Release order is asymmetric, without the classical order instances of `Nat`. -/
private theorem releaseVersion_lt_asymm {a b : ReleaseVersion} (h : a < b) : ¬ b < a := by
  suffices lex : ∀ {x y : List Nat}, List.Lex (· < ·) x y → ¬ List.Lex (· < ·) y x from lex h
  intro x y h
  induction h with
  | nil => intro h; cases h
  | rel h => intro h'; cases h' with
    | rel h'' => exact Nat.lt_asymm h h''
    | cons => exact Nat.lt_irrefl _ h
  | cons _ ih => intro h'; cases h' with
    | rel h'' => exact Nat.lt_irrefl _ h''
    | cons h'' => exact ih h''

/-- The site root opens release `l`'s edition exactly when `l` is the greatest release. -/
theorem rootEdition_eq_release_iff (l : ReleaseVersion) :
    rootEdition = .release l ↔ l ∈ versions ∧ ∀ v ∈ versions, v = l ∨ v < l := by
  unfold rootEdition
  cases hl : latest with
  | none =>
    simp only [reduceCtorEq, false_iff, not_and]
    intro hmem
    simp [List.getLast?_eq_none_iff.mp hl] at hmem
  | some m =>
    obtain ⟨hm, hmax⟩ := latest_greatest hl
    simp only [Edition.release.injEq]
    constructor
    · rintro rfl; exact ⟨hm, hmax⟩
    · rintro ⟨hl, hlmax⟩
      rcases hlmax m hm with h | hml
      · exact h
      · rcases hmax l hl with h | hlm
        · exact h.symm
        · exact absurd hlm (releaseVersion_lt_asymm hml)

/-- The site root opens a published edition. -/
theorem rootEdition_published : rootEdition ∈ published := by
  cases h : rootEdition with
  | dev => simp [published]
  | release l =>
    exact (mem_published _).mpr (Or.inr ⟨l, ((rootEdition_eq_release_iff l).mp h).1, rfl⟩)

/-! ## Stable routes -/

/-- The route of the artifact file `file`: its directory for an `index.html`, and the file itself
otherwise. -/
def pageRoute (file : String) : String :=
  if file.endsWith "index.html" then (file.dropEnd 10).toString else file

/-- Whether the file at `path` of an edition, relative to the edition root, has a stable route:
it is an HTML page below a `stableRoots` directory. -/
def stablePage (path : String) : Bool :=
  path.endsWith ".html" && stableRoots.any fun r => path.startsWith r

/-- The files of the stable routes, relative to the site root, given `files`, the paths of the
files of `rootEdition` relative to its root: each stable route has the path of its page in that
edition. -/
def stablePages (files : List String) : List String := files.filter stablePage

/-- The site has a stable route exactly for each HTML page of `rootEdition` below a `stableRoots`
directory. A page that only another edition has, such as the page of a rule that is in no
release while a release exists, has none. -/
theorem mem_stablePages (files : List String) (path : String) :
    path ∈ stablePages files ↔ path ∈ files ∧ path.endsWith ".html" = true ∧
      ∃ r ∈ stableRoots, path.startsWith r = true := by
  simp [stablePages, stablePage]

/-- Every file of a stable route is a path of the published site. -/
theorem sitePath_of_mem_stablePages {files : List String} {path : String}
    (h : path ∈ stablePages files) : sitePath path = true :=
  (sitePath_iff path).mpr (Or.inr (Or.inr ((mem_stablePages files path).mp h).2.2))

/-- The address that the stable route with file `path` opens: the same page of `rootEdition`,
below the project base path. -/
def stableTarget (path : String) : String := basePath ++ rootEdition.root ++ pageRoute path

/-! ## Release banners -/

/-- The path, relative to the latest release's edition root, that the banner of the page at
`path` links: the same page when the latest edition has it (its files are `files`, relative to
its root), otherwise that edition's home page. -/
def bannerTarget (files : List String) (path : String) : String :=
  if path ∈ files then path else "index.html"

/-- The release that the pages of release `v`'s edition name in their banner: the latest
release, when it is not `v` itself. -/
def bannerRelease (v : ReleaseVersion) : Option ReleaseVersion :=
  latest.bind fun l => if v = l then none else some l

/-- An edition carries a banner exactly when a later release is the latest, and the banner names
it (`latest_greatest`: no release is later than it). -/
theorem bannerRelease_eq_some (v l : ReleaseVersion) :
    bannerRelease v = some l ↔ latest = some l ∧ v ≠ l := by
  unfold bannerRelease
  cases latest with
  | none => simp
  | some m =>
    by_cases h : v = m
    · subst h; simp
    · simp only [h, ite_false, Option.bind_some, Option.some.injEq]
      exact ⟨fun e => ⟨e, e ▸ h⟩, fun ⟨e, _⟩ => e⟩

/-- A banner never links a missing page of an edition that has a home page. -/
theorem bannerTarget_mem {files : List String} (home : "index.html" ∈ files) (path : String) :
    bannerTarget files path ∈ files := by
  unfold bannerTarget
  split
  · assumption
  · exact home

/-- The note at the top of the page at `path` of release `v`'s edition while `latest` is the
latest release: it names the latest release and links `target` in its edition, the same page
when `target` is `path`. -/
def outdatedBanner (v latest : ReleaseVersion) (path target : String) : String :=
  "<div class=\"regula-outdated\" role=\"note\"><p>This page documents Regula " ++
    escape v.spelling ++ ". The latest release is Regula " ++ escape latest.spelling ++
    ": <a href=\"" ++
    escape (basePath ++ (Edition.release latest).root ++ pageRoute target) ++ "\">" ++
    (if target == path then "this page in Regula " else "the rule reference of Regula ") ++
    escape latest.spelling ++ "</a>.</p></div>"

/-- The start tag of the content column of every Verso page, where a banner goes: the top of the
page's content, below Verso's fixed header. -/
def bannerAnchor : String := "<div class=\"content-wrapper\">"

/-- The page `page` with `banner` inserted directly after its `bannerAnchor`. It is admitted only
when the page has exactly one such tag and splits around it into parts that reassemble to the
page. -/
def insertBanner (page banner : String) : Except String String :=
  match page.splitOn bannerAnchor with
  | [before, after] =>
    if before ++ bannerAnchor ++ after = page then .ok (before ++ bannerAnchor ++ banner ++ after)
    else .error "the page does not reassemble around its content column"
  | _ => .error "the page does not have exactly one content column"

/-- An admitted insertion changes the page only by the banner, directly after `bannerAnchor`. -/
theorem insertBanner_ok {page banner out : String} (h : insertBanner page banner = .ok out) :
    ∃ before after, page = before ++ bannerAnchor ++ after ∧
      out = before ++ bannerAnchor ++ banner ++ after := by
  unfold insertBanner at h
  split at h
  · rename_i before after _
    split at h
    · rename_i hp
      exact ⟨before, after, hp.symm, (Except.ok.inj h).symm⟩
    · cases h
  · cases h

/-! ## Index filters -/

/-- Every rule category, in the index filter's order (`mem_categories`). -/
def categories : List RuleCategory :=
  [.foundation, .declaration, .execution, .environment, .configuration, .elaboration,
    .coverage, .admission, .documentation]

theorem mem_categories (c : RuleCategory) : c ∈ categories := by
  cases c <;> simp [categories]

/-- Every evidence mode, in the index filter's order (`mem_modes`). -/
def modes : List EvidenceMode :=
  [.editorSnapshot, .incrementalProject, .freshProject, .freshFile, .documentationExample,
    .serializedGraph]

theorem mem_modes (m : EvidenceMode) : m ∈ modes := by
  cases m <;> simp [modes]

/-- The category's identifier in the index filter's markup and CSS. -/
def _root_.Regula.RuleCategory.slug : RuleCategory → String
  | .foundation => "foundation" | .declaration => "declaration" | .execution => "execution"
  | .environment => "environment" | .configuration => "configuration"
  | .elaboration => "elaboration" | .coverage => "coverage" | .admission => "admission"
  | .documentation => "documentation"

/-- The category's display name. -/
def _root_.Regula.RuleCategory.label : RuleCategory → String
  | .foundation => "Foundation" | .declaration => "Declaration" | .execution => "Execution"
  | .environment => "Environment" | .configuration => "Configuration"
  | .elaboration => "Elaboration" | .coverage => "Coverage" | .admission => "Admission"
  | .documentation => "Documentation"

/-- The scope's display text. -/
def _root_.Regula.RuleScope.label : RuleScope → String
  | .declaration => "declaration" | .project => "project" | .executionRoot => "execution root"
  | .documentationFence => "documentation fence" | .module => "module"
  | .materialDeclaration => "registered material declaration"

/-- The evidence mode's display text. -/
def modeLabel : EvidenceMode → String
  | .editorSnapshot => "editor snapshot" | .incrementalProject => "incremental project"
  | .freshProject => "fresh project" | .freshFile => "fresh file"
  | .documentationExample => "documentation example" | .serializedGraph => "serialized graph"

/-- One filter state: each dimension is either unrestricted (`none`) or one value. -/
structure Selection where
  /-- The selected rule category, or `none` for every category. -/
  category : Option RuleCategory
  /-- The selected evidence mode, or `none` for every mode. -/
  mode : Option EvidenceMode

/-- A rule is listed under a selection when it matches every restricted dimension. -/
def Selection.admits (s : Selection) (id : RuleId) : Bool :=
  s.category.all (fun c => decide (c = (descriptor id).category)) &&
  s.mode.all (fun m => decide (m ∈ (descriptor id).evidenceModes))

/-- Each finite dimension together with its unrestricted choice. -/
def options {α : Type} (values : List α) : List (Option α) := none :: values.map some

theorem mem_options {α : Type} (values : List α) (h : ∀ v, v ∈ values) (o : Option α) :
    o ∈ options values := by
  cases o with
  | none => simp [options]
  | some v => simp [options, h v]

/-- Every filter state the index form can express. -/
def selections : List Selection :=
  (options categories).flatMap fun c => (options modes).map fun m => ⟨c, m⟩

theorem mem_selections (s : Selection) : s ∈ selections := by
  rcases s with ⟨c, m⟩
  simp only [selections, List.mem_flatMap, List.mem_map]
  exact ⟨c, mem_options _ mem_categories c, m, mem_options _ mem_modes m, rfl⟩

/-- Filter states under which no registered rule is listed. -/
def emptySelections : List Selection :=
  selections.filter fun s => !(RuleId.all.any s.admits)

/-- The no-match notice is emitted for exactly the filter states that list no rule. -/
theorem mem_emptySelections (s : Selection) :
    s ∈ emptySelections ↔ ∀ id, s.admits id = false := by
  simp only [emptySelections, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.any_eq_false, Bool.not_eq_true]
  exact ⟨fun h id => h.2 id (RuleId.mem_all id), fun h => ⟨mem_selections s, fun id _ => h id⟩⟩

/-! ## Line diffs -/

/-- One line of a displayed diff. -/
inductive DiffLine where
  /-- A line present before and after the change. -/
  | keep (line : String)
  /-- A line present only before the change. -/
  | remove (line : String)
  /-- A line present only after the change. -/
  | add (line : String)
  deriving DecidableEq

/-- The line this diff line contributes to the text before the change. -/
def DiffLine.before : DiffLine → List String
  | .keep l | .remove l => [l]
  | .add _ => []

/-- The line this diff line contributes to the text after the change. -/
def DiffLine.after : DiffLine → List String
  | .keep l | .add l => [l]
  | .remove _ => []

/-- Keep the longest common prefix and suffix and replace the middle. -/
def prefixDiff : List String → List String → List DiffLine
  | a :: as, b :: bs => if a = b then .keep a :: prefixDiff as bs else
      let suffix := ((a :: as).reverse.zip (b :: bs).reverse).takeWhile
          (fun p => p.1 = p.2) |>.length
      let middleA := (a :: as).take ((a :: as).length - suffix)
      let middleB := (b :: bs).take ((b :: bs).length - suffix)
      middleA.map .remove ++ middleB.map .add ++
          ((a :: as).drop ((a :: as).length - suffix)).map .keep
  | as, bs => as.map .remove ++ bs.map .add

/-- A displayed diff is admitted only when it reproduces both compared line lists. -/
def admitDiff (before after : List String) :
    Except String { d : List DiffLine // d.flatMap DiffLine.before = before ∧
      d.flatMap DiffLine.after = after } :=
  let d := prefixDiff before after
  if h : d.flatMap DiffLine.before = before ∧ d.flatMap DiffLine.after = after then .ok ⟨d, h⟩
  else .error "diff does not reproduce its inputs"

/-- Non-vacuity: a one-line change is admitted as keep/remove/add. -/
theorem admitDiff_control :
    (admitDiff ["a", "b", "c"] ["a", "x", "c"]).toBool = true := by decide

/-! ## Output links -/

/-- One start tag: lowercase name and attributes with entity-decoded values. -/
structure Tag where
  /-- The lowercase tag name. -/
  name : String
  /-- The attributes in order: lowercase name and entity-decoded value (empty when none is
  given). -/
  attributes : List (String × String)
  deriving DecidableEq, Repr

/-- Decode the entities the builder and Verso emit in attribute values. -/
def decodeEntities (s : String) : String :=
  ((((s.replace "&quot;" "\"").replace "&#39;" "'").replace "&lt;" "<").replace "&gt;" ">").replace
      "&amp;" "&"

private def isSpace (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r' ||
    c == '\x0c'

/-- Attribute list of a tag body (the text after the tag name, before `>`). -/
def parseAttributes : Nat → List Char → List (String × String)
  | 0, _ => []
  | fuel + 1, input =>
    let input := input.dropWhile (fun c => isSpace c || c == '/')
    if input.isEmpty then [] else
    let name := input.takeWhile (fun c => !(isSpace c || c == '=' || c == '/' || c == '>'))
    let rest := (input.drop name.length).dropWhile isSpace
    let key := (String.ofList name).toLower
    if name.isEmpty then parseAttributes fuel (input.drop 1) else
    match rest with
    | '=' :: afterEq =>
      match afterEq.dropWhile isSpace with
      | '"' :: body =>
        let value := body.takeWhile (· != '"')
        (key, decodeEntities (String.ofList value)) :: parseAttributes fuel
        (body.drop (value.length + 1))
      | '\'' :: body =>
        let value := body.takeWhile (· != '\'')
        (key, decodeEntities (String.ofList value)) :: parseAttributes fuel
        (body.drop (value.length + 1))
      | body =>
        let value := body.takeWhile (fun c => !isSpace c)
        (key, decodeEntities (String.ofList value)) :: parseAttributes fuel (body.drop value.length)
    | _ => (key, "") :: parseAttributes fuel rest

/-- The text of a tag up to its closing `>`, skipping `>` inside quoted attribute values. -/
def tagBody : List Char → Option Char → List Char
  | [], _ => []
  | c :: rest, none =>
    if c == '>' then [] else c :: tagBody rest (if c == '"' || c == '\'' then some c else none)
  | c :: rest, some q => c :: tagBody rest (if c == q then none else some q)

/-- Tokenizer state: ordinary markup, or raw text of a comment or script/style element. -/
inductive ScanMode where
  /-- Ordinary markup, where a `<` may start a tag. -/
  | markup
  /-- Inside an HTML comment, until `-->`. -/
  | comment
  /-- Inside the raw text of a `script` or `style` element, until its end tag. -/
  | raw (element : String)

/-- Start tags of an HTML document, skipping comments and script/style contents. -/
def scanTags (html : String) : List Tag :=
  let chunks := (html.splitOn "<").drop 1
  (chunks.foldl (fun (acc : ScanMode × List Tag) chunk =>
    let (mode, tags) := acc
    match mode with
    | .comment => (if (chunk.splitOn "-->").length > 1 then .markup else .comment, tags)
    | .raw element =>
      if (chunk.toLower.startsWith ("/" ++ element)) then (.markup, tags) else (.raw element, tags)
    | .markup =>
      if chunk.startsWith "!--" then
        (if ((chunk.drop 3).toString.splitOn "-->").length > 1 then .markup else .comment, tags)
      else if chunk.startsWith "/" || chunk.startsWith "!" || chunk.startsWith "?" then
            (.markup, tags)
      else
        let body := tagBody chunk.toList none
        let name := String.ofList (body.takeWhile (fun c => !(isSpace c || c == '/' || c == '>')))
            |>.toLower
        if name.isEmpty then (.markup, tags) else
        let rest := body.drop name.length
        let tag : Tag := ⟨name, parseAttributes (rest.length + 1) rest⟩
        (if name == "script" || name == "style" then .raw name else .markup, tag :: tags))
    (ScanMode.markup, [])).2.reverse

/-- Attribute lookup. -/
def Tag.get? (t : Tag) (key : String) : Option String := (t.attributes.find? (·.1 == key)).map (·.2)

/-- Link-bearing attributes the builder checks. -/
def Tag.links (t : Tag) : List String :=
  (["href", "src"].filterMap t.get?).filter (fun _ => t.name != "base")

/-- Fragment targets a document defines. -/
def Tag.ids (t : Tag) : List String :=
  (t.get? "id").toList ++ (if t.name == "a" then (t.get? "name").toList else [])

/-- One scanned output file: its artifact path, whether it is HTML, the fragment targets it
defines, its `<base href>` if any, and the links it contains. -/
structure Page where
  /-- The file's path in the artifact. -/
  path : String
  /-- The file is HTML and was scanned. -/
  html : Bool
  /-- The fragment targets it defines: every `id`, and the `name` of each `a`. -/
  ids : List String
  /-- The `href` of its first `base` element, if any. -/
  base : Option String
  /-- The `href` and `src` values of its tags other than `base`. -/
  links : List String
  deriving DecidableEq, Repr

/-- Scan the HTML file `source` at artifact path `path` for its targets, base and links. -/
def Page.ofHtml (path source : String) : Page :=
  let tags := scanTags source
  { path, html := true, ids := tags.flatMap Tag.ids,
    base := (tags.find? (·.name == "base")).bind (·.get? "href"),
    links := tags.flatMap Tag.links }

/-- A non-HTML file at `path`: it defines no targets and contains no links. -/
def Page.ofOther (path : String) : Page :=
    { path, html := false, ids := [], base := none, links := [] }

/-- Directory part of an artifact path, with trailing `/`, or empty at the root. -/
def directory (path : String) : String :=
  match (path.splitOn "/").dropLast with
  | [] => ""
  | parts => String.intercalate "/" parts ++ "/"

/-- Normalize `.` and `..` segments; `none` when a path leaves the artifact root. -/
def normalize (path : String) : Option String :=
  let segments := path.splitOn "/"
  let trailing := segments.getLast? == some "" || segments.getLast? == some "." ||
      segments.getLast? == some ".."
  let step (acc : Option (List String)) (s : String) : Option (List String) :=
    acc.bind fun stack =>
      if s == "" || s == "." then some stack
      else if s == ".." then (match stack with | [] => none | _ :: rest => some rest)
      else some (s :: stack)
  (segments.foldl step (some [])).map fun stack =>
    let joined := String.intercalate "/" stack.reverse
    if trailing && !joined.isEmpty then joined ++ "/" else joined

/-- What a link denotes after resolution against the base path. -/
inductive Target where
  /-- A reference with a scheme other than `javascript:` or `data:`. -/
  | external
  /-- The artifact file `path` (a directory denotes its `index.html`), with `fragment` after
  `#`, empty when there is none. -/
  | internal (path : String) (fragment : String)
  /-- A refused link, for `reason`. -/
  | invalid (reason : String)
  deriving DecidableEq

/-- The RFC 3986 scheme of a URI reference: a letter followed by letters, digits, `+`, `-` or
`.`, ending at a `:` that precedes any `/`, `?` or `#`. Every other reference is relative. -/
def scheme? (link : String) : Option String :=
  let head := link.toList.takeWhile (fun c => c != ':' && c != '/' && c != '?' && c != '#')
  match head with
  | c :: rest =>
    if (link.toList.drop head.length).head? == some ':' && c.isAlpha &&
        rest.all (fun d => d.isAlphanum || d == '+' || d == '-' || d == '.') then
      some (String.ofList head).toLower
    else none
  | [] => none

/-- Resolve a link in the page at `from`. A reference with a scheme is external, except that
`javascript:` and `data:` references are refused. A root-relative path must lie under
`basePath`. Relative references resolve against the page's `<base href>` (itself resolved
against the page, then reduced to its directory) when present. Directory targets denote their
`index.html`. -/
def resolve (page : Page) (link : String) : Target :=
  match scheme? link with
  | some s => if s == "javascript" || s == "data" then .invalid "script or data URL" else .external
  | none =>
    let (beforeFragment, fragment) := match link.splitOn "#" with
      | [] => ("", "")
      | p :: rest => (p, String.intercalate "#" rest)
    let pathPart := (beforeFragment.splitOn "?").headD ""
    let underBase (p : String) : Option String :=
      if p.startsWith basePath then some (p.drop basePath.length).toString else none
    let absolute : Option String :=
      if pathPart.startsWith "/" then underBase pathPart
      else
        -- The base URL, as an artifact path; the document itself when there is no `<base>`.
        let baseUrl := match page.base with
          | none => some page.path
          | some b => if b.startsWith "/" then underBase b else some (directory page.path ++ b)
        -- Normalize the base first, so a trailing `..` or `.` segment denotes its directory.
        (baseUrl.bind normalize).map fun u => if pathPart.isEmpty then u else
                                                                        directory u ++ pathPart
    match absolute with
    | none => .invalid s!"link outside {basePath}"
    | some raw =>
      match normalize raw with
      | none => .invalid "link leaves the artifact root"
      | some p =>
        let file := if p.isEmpty || p.endsWith "/" then p ++ "index.html" else p
        .internal file fragment

/-- The link of `page` resolves within the artifact `pages`: scheme URLs are accepted, an
internal target is an existing file (or directory with `index.html`) and a fragment
names an `id` of that HTML target. -/
def LinkOK (pages : List Page) (page : Page) (link : String) : Prop :=
  match resolve page link with
  | .external => True
  | .invalid _ => False
  | .internal file fragment =>
    ∃ target ∈ pages, (target.path = file ∨ target.path = file ++ "/index.html") ∧
      (fragment = "" ∨ ¬ target.html ∨ fragment ∈ target.ids)

instance (pages : List Page) (page : Page) (link : String) : Decidable
    (LinkOK pages page link) := by
  unfold LinkOK
  split <;> infer_instance

/-- Scanned pages grouped by artifact path, so a link target is found without scanning every
page. -/
def pageIndex (pages : List Page) : Std.HashMap String (List Page) :=
  pages.foldl (fun m p => m.insert p.path (p :: m.getD p.path [])) ∅

private theorem mem_foldl_index (pages : List Page) (m : Std.HashMap String (List Page))
    (path : String) (t : Page) :
    t ∈ (pages.foldl (fun m p => m.insert p.path (p :: m.getD p.path [])) m).getD path [] ↔
      t ∈ m.getD path [] ∨ (t ∈ pages ∧ t.path = path) := by
  induction pages generalizing m with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih, Std.HashMap.getD_insert]
    by_cases h : p.path = path
    · subst h
      simp only [beq_self_eq_true, ite_true, List.mem_cons]
      constructor
      · rintro ((rfl | hm) | ⟨hm, hp⟩)
        · exact Or.inr ⟨Or.inl rfl, rfl⟩
        · exact Or.inl hm
        · exact Or.inr ⟨Or.inr hm, hp⟩
      · rintro (hm | ⟨rfl | hm, hp⟩)
        · exact Or.inl (Or.inr hm)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr ⟨hm, hp⟩
    · have hb : (p.path == path) = false := by simpa using h
      simp only [hb, Bool.false_eq_true, ite_false, List.mem_cons]
      constructor
      · rintro (hm | ⟨hm, hp⟩)
        · exact Or.inl hm
        · exact Or.inr ⟨Or.inr hm, hp⟩
      · rintro (hm | ⟨rfl | hm, hp⟩)
        · exact Or.inl hm
        · exact absurd hp h
        · exact Or.inr ⟨hm, hp⟩

/-- The index lists exactly the pages with each path. -/
theorem mem_pageIndex (pages : List Page) (path : String) (t : Page) :
    t ∈ (pageIndex pages).getD path [] ↔ t ∈ pages ∧ t.path = path := by
  rw [pageIndex, mem_foldl_index]
  simp

/-- `LinkOK`, decided through an index of the pages. -/
def linkOKIn (index : Std.HashMap String (List Page)) (page : Page) (link : String) : Bool :=
  match resolve page link with
  | .external => true
  | .invalid _ => false
  | .internal file fragment =>
    (index.getD file [] ++ index.getD (file ++ "/index.html") []).any fun target =>
      fragment == "" || !target.html || target.ids.contains fragment

theorem linkOKIn_pageIndex (pages : List Page) (page : Page) (link : String) :
    linkOKIn (pageIndex pages) page link = true ↔ LinkOK pages page link := by
  unfold linkOKIn LinkOK
  split
  · simp
  · simp
  · rename_i file fragment _
    simp only [List.any_eq_true, List.mem_append, mem_pageIndex, Bool.or_eq_true,
      beq_iff_eq, Bool.not_eq_true', List.contains_iff_mem]
    constructor
    · rintro ⟨t, (⟨ht, hp⟩ | ⟨ht, hp⟩), hf⟩
      · exact ⟨t, ht, Or.inl hp, by simpa [or_assoc] using hf⟩
      · exact ⟨t, ht, Or.inr hp, by simpa [or_assoc] using hf⟩
    · rintro ⟨t, ht, (hp | hp), hf⟩
      · exact ⟨t, Or.inl ⟨ht, hp⟩, by simpa [or_assoc] using hf⟩
      · exact ⟨t, Or.inr ⟨ht, hp⟩, by simpa [or_assoc] using hf⟩

/-- Every unresolved link, reported with its page. -/
@[regula_decision]
def linkErrors (pages : List Page) : List String :=
  let index := pageIndex pages
  pages.flatMap fun page => page.links.filterMap fun link =>
    if linkOKIn index page link then none else some s!"{page.path}: unresolved link {link}"

/-- The executed check returns no error exactly when every scanned link of every scanned
page resolves. -/
theorem linkErrors_nil_iff (pages : List Page) :
    linkErrors pages = [] ↔ ∀ page ∈ pages, ∀ link ∈ page.links, LinkOK pages page link := by
  simp only [linkErrors, List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff]
  constructor
  · intro h page hp link hl
    have := h page hp link hl
    by_cases hn : linkOKIn (pageIndex pages) page link = true
    · exact (linkOKIn_pageIndex pages page link).mp hn
    · simp [hn] at this
  · intro h page hp link hl
    simp [(linkOKIn_pageIndex pages page link).mpr (h page hp link hl)]

/-- Registered contract of the executed link check, as a two-way decision
(`linkErrors_nil_iff`): it reports nothing for no page, and reports a `javascript:` link. -/
theorem checked_linkErrors : Regula.ExecutableContract linkErrors
    (Regula.Decides (· = [])
      fun pages => ∀ page ∈ pages, ∀ link ∈ page.links, LinkOK pages page link) :=
  ⟨.of_iff linkErrors_nil_iff ⟨[], (linkErrors_nil_iff []).mpr (by simp)⟩
    ⟨[⟨"a", true, [], none, ["javascript:x"]⟩], by decide +kernel⟩⟩

/-! Evaluated controls (observations of the compiled tokenizer, not proofs): a missing
target is reported, a resolving relative link with a fragment under a `<base href>` is
accepted, a root-relative link outside the base path is reported, and script text is not
scanned as markup. The string operations do not reduce in the kernel. -/
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkErrors [Page.ofHtml "dev/index.html" "<a href=\"rules/\">x</a>"] != []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkErrors [Page.ofHtml "dev/rules/index.html"
  "<base href=\"./../\"><a href=\"rules/#top\">x</a><h1 id=\"top\">t</h1>"] == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkErrors [Page.ofHtml "dev/index.html" "<a href=\"/other/x\">x</a>"] != []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkErrors
    [Page.ofHtml "dev/index.html" "<script>if (a<b) {}</script><a href=\"https://x.org/\">x</a>"] ==
    []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkErrors [Page.ofHtml "dev/index.html" "<a href=\"missing/?u=http://x\">x</a>"] != []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkErrors [Page.ofHtml "dev/index.html" "<a href=\"javascript://x\">x</a>"] != []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkErrors
    [Page.ofHtml "dev/rules/a.html" "<base href=\"x\"><a href=\"missing.html\">x</a>"] != []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkErrors [Page.ofHtml "dev/index.html" "<a title=\"a>b\" href=\"missing/\">x</a>"] != []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkErrors [Page.ofHtml "dev/rules/a.html" "<base href=\"..\"><a href=\"x\">x</a>",
  Page.ofOther "dev/rules/x"] != []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkErrors
    [Page.ofHtml "dev/rules/a.html" "<base href=\"..\"><a href=\"x\">x</a>",
        Page.ofOther "dev/x"] == []

/-! ## Normative clause anchors -/

/-- GitHub's heading anchor for an ASCII heading: lowercase, spaces to hyphens, other
punctuation removed. -/
def headingSlug (heading : String) : String :=
  String.ofList
      ((heading.toLower.toList.filter
          (fun c => c.isAlphanum || c == ' ' || c == '-' || c == '_')).map
    (fun c => if c == ' ' then '-' else c))

/-- Every anchor the registry links in the standard, as its page below the standard's root and
its fragment: each cited section on its chapter page and each checklist row a rule page lists
on the checklist page. -/
def standardAnchors : List (String × String) :=
  Clause.all.map (fun c => (c.chapter ++ "/index.html", c.anchor)) ++
    ((RuleId.all.flatMap fun id => (guide id).checklist).eraseDups.map
      fun row => (checklistChapter ++ "/index.html", row))

/-- The standard of the development edition. Documentation links into the standard are this URL
followed by a route below the standard's root. -/
def standardUrl : String := siteBase ++ "dev/standard/"

/-- A character that continues a route written after `standardUrl`: an ASCII letter or digit,
`-`, `_`, `/` or `#`. Anything else, including Markdown delimiters, whitespace and a sentence's
closing `.`, ends the route. -/
def isRouteChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c == '/' || c == '#'

/-- The route after each occurrence of `url` in `text`, in order: the longest run of
`isRouteChar` characters following it. Every occurrence counts, whatever Markdown surrounds it
(link, autolink, code span or plain text). -/
def routesAfter (url text : String) : List String :=
  ((text.splitOn url).drop 1).map fun rest => String.ofList (rest.toList.takeWhile isRouteChar)

/-- The page below the standard's root and the fragment a route names: the text before the
first `#`, with `index.html` appended when it is empty or ends in `/`, and the text after it,
empty when the route names only a page. -/
def routeAnchor (route : String) : String × String :=
  let path := String.ofList (route.toList.takeWhile (· != '#'))
  (if path.isEmpty || path.endsWith "/" then path ++ "index.html" else path,
    String.ofList ((route.toList.dropWhile (· != '#')).drop 1))

/-- Every anchor that the documents `texts` link in the standard: the page and fragment of each
route written after `standardUrl`. -/
def documentAnchors (texts : List String) : List (String × String) :=
  texts.flatMap fun text => (routesAfter standardUrl text).map routeAnchor

/-- Every page and fragment that the document `text` names on the site: the page and fragment of
each route written after `siteBase`, relative to the site root. An address with no route names
the `index.html` of the site root. -/
def siteAnchors (text : String) : List (String × String) :=
  (routesAfter siteBase text).map routeAnchor

/-- The anchors that no page with their path defines. An empty fragment needs only the page. -/
@[regula_decision]
def missingAnchors (pages : List Page) (anchors : List (String × String)) : List
    (String × String) :=
  let index := pageIndex pages
  anchors.filter fun anchor =>
    !((index.getD anchor.1 []).any fun page => anchor.2 == "" || page.ids.contains anchor.2)

/-- The executed check returns nothing exactly when each anchor's path is a page that has its
fragment as an `id` or the fragment is empty. -/
theorem missingAnchors_nil_iff (pages : List Page) (anchors : List (String × String)) :
    missingAnchors pages anchors = [] ↔
      ∀ anchor ∈ anchors, ∃ page ∈ pages, page.path = anchor.1 ∧
          (anchor.2 = "" ∨ anchor.2 ∈ page.ids) := by
  simp [missingAnchors, List.filter_eq_nil_iff, mem_pageIndex, Decidable.or_iff_not_imp_left]

/-- Registered contract of the executed anchor check, as a two-way decision
(`missingAnchors_nil_iff`): it reports nothing for no anchor, and reports an anchor of a page
that no page list holds. -/
theorem checked_missingAnchors : Regula.ExecutableContract missingAnchors (fun run =>
    Regula.Decides (· = [])
      (fun input : List Page × List (String × String) =>
        ∀ anchor ∈ input.2, ∃ page ∈ input.1, page.path = anchor.1 ∧
          (anchor.2 = "" ∨ anchor.2 ∈ page.ids))
      (Function.uncurry run)) :=
  ⟨.of_iff (fun input => missingAnchors_nil_iff input.1 input.2)
    ⟨([], []), (missingAnchors_nil_iff [] []).mpr (by simp)⟩
    ⟨([], [("page", "")]), fun accepted => by
      simpa using (missingAnchors_nil_iff [] [("page", "")]).mp accepted⟩⟩

/-! ## Checklist rows and coverage -/

/-- The checklist rows a rendered page defines, in document order: the `id` of each element of
class `checklistRowClass`. -/
def renderedRows (html : String) : List String :=
  (scanTags html).filterMap fun t =>
    if t.get? "class" == some checklistRowClass then t.get? "id" else none

/-- How the rendered checklist's rows differ from `checklistRows`, or `none` when they are the
same list. -/
@[regula_decision]
def rowsMismatch (rendered : List String) : Option String :=
  if rendered == checklistRows then none else
    some s!"rendered rows missing from checklistRows: {rendered.filter (· ∉ checklistRows)}; \
      checklistRows not rendered: {checklistRows.filter (· ∉ rendered)}; otherwise a row is \
      repeated or out of the checklist's order"

/-- The executed row check passes exactly when the rendered rows are `checklistRows`. -/
theorem rowsMismatch_eq_none_iff (rendered : List String) :
    rowsMismatch rendered = none ↔ rendered = checklistRows := by
  unfold rowsMismatch
  split <;> simp_all

/-- Registered contract of the executed row check, as a two-way decision
(`rowsMismatch_eq_none_iff`): it reports no mismatch for `checklistRows` itself, and one for the
empty list. -/
theorem checked_rowsMismatch : Regula.ExecutableContract rowsMismatch
    (Regula.Decides (· = none) (· = checklistRows)) :=
  ⟨.of_iff rowsMismatch_eq_none_iff
    ⟨checklistRows, (rowsMismatch_eq_none_iff _).mpr rfl⟩
    ⟨[], fun accepted => absurd ((rowsMismatch_eq_none_iff _).mp accepted) (by decide)⟩⟩

/-- Every row a rule explanation lists is a checklist row. -/
theorem guide_checklist_listed (id : RuleId) :
    ∀ row ∈ (guide id).checklist, row ∈ checklistRows := by
  cases id <;> decide

/-- The rules whose explanation lists checklist row `row`, in registry order. -/
def rulesOfRow (row : String) : List RuleId :=
  RuleId.all.filter fun id => row ∈ (guide id).checklist

/-- The coverage page lists a rule under a row exactly when the rule's explanation lists that
row: the page is the inverse of `Guide.checklist`. -/
theorem mem_rulesOfRow (row : String) (id : RuleId) :
    id ∈ rulesOfRow row ↔ row ∈ (guide id).checklist := by
  simp [rulesOfRow, RuleId.mem_all]

/-- The review obligations that carry checklist row `row`, in `Residual.all` order. -/
def residualsOfRow (row : String) : List Residual :=
  Residual.all.filter fun r => row ∈ r.rows

/-- The coverage page lists an obligation under a row exactly when the obligation carries that
row: the page is the inverse of `Residual.rows`. -/
theorem mem_residualsOfRow (row : String) (r : Residual) :
    r ∈ residualsOfRow row ↔ row ∈ r.rows := by
  simp [residualsOfRow, Residual.mem_all]

/-- Every obligation carries a row, and every row it carries is a checklist row. -/
theorem residual_rows_listed (r : Residual) :
    r.rows ≠ [] ∧ ∀ row ∈ r.rows, row ∈ checklistRows := by
  cases r <;> decide

/-- Every checklist row carries a review obligation, so no row passes on a checker result alone,
whether or not a rule lists it. -/
theorem residualsOfRow_ne_nil : ∀ row ∈ checklistRows, residualsOfRow row ≠ [] := by
  decide

/-! Evaluated controls (observations of the compiled scanners, not proofs): a route ends at a
Markdown delimiter or a sentence's closing `.`, an autolink and a code span count, a page route
names its `index.html`, and only elements of the row class are rows. -/
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentAnchors ["[a](" ++ standardUrl ++ "8-compliance-audit/#DOC-04). <" ++ standardUrl ++
  ">; `" ++ standardUrl ++ "introduction/`."] ==
  [("8-compliance-audit/index.html", "DOC-04"), ("index.html", ""), ("introduction/index.html", "")]
-- A document's addresses of the site: the site root, a stable route and a route with a fragment.
-- A stable route has a file exactly for a page of the root edition below a stable root.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard siteAnchors ("[a](" ++ siteBase ++ ") [b](" ++ stableUrl "rules/RG1001/" ++ ")\n\n[c]: " ++
    stableUrl "standard/#top") ==
  [("index.html", ""), ("rules/RG1001/index.html", ""), ("standard/index.html", "top")]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard stablePages ["index.html", "regula.css", "rules/index.html", "rules/RG1001/index.html",
    "standard/8-compliance-audit/index.html", "standard/x.css", "versions/index.html"] ==
  ["rules/index.html", "rules/RG1001/index.html", "standard/8-compliance-audit/index.html"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard pageRoute "rules/RG1001/index.html" == "rules/RG1001/" && pageRoute "rules/a.html" ==
  "rules/a.html"
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard renderedRows
    "<h2 id=\"audit-matrix\">x</h2><code id=\"A-1\" class=\"checklist-row\">A-1</code>" ==
  ["A-1"]

end Regula.Site
