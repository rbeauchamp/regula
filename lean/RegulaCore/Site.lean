import RegulaCore.Account
import RegulaCore.Guide
import Regula.Contract
import Std.Data.HashMap

/-! # Rule-reference site: identity, routes and pure output checks

This module is the pure model of the published rule reference (issue #15). The operational
builder in `Regula.Site` reads evidence, runs Verso and walks the output tree; every
decision it takes about that data is a function here.

## Main declarations

- `Edition`, `Edition.pageFile`, `pageFiles`: the route of every rule page in a published
  edition, derived only from the closed `RuleId`; `pageFiles_nodup` and `mem_pageFiles`
  make the page inventory duplicate-free and total over the registry.
- `artifactRevisions`, `mem_artifactRevisions`, `archived_subset_artifactRevisions`,
  `artifactRevisions_mono`: the revision snapshots of an artifact are exactly the archived
  snapshots plus the current clean build's, so an artifact never drops an archived snapshot
  and appending to the archive never removes one from a later artifact. `artifactBudget` bounds
  the artifact's size.
- `escape`, `escape_safe`: HTML text escaping; escaped text contains none of the markup
  characters `<`, `>`, `"`, `'` or the backtick that would end a Verso code fence.
- `htmlBlock`, `htmlBlock_ok`: the only way the generator inserts raw HTML into Verso source (by inspection of the generator; guide prose and clause labels enter as Verso markup).
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
- `renderedRows`, `codeLinkLabel`, `linkedRows`, `rowMapMismatch`, `rowMapMismatch_eq_none_iff`:
  the checklist rows of a rendered page and the labels and rows a row map links, each of which
  must be that list.

## Assumptions and boundaries

`scanTags` is a small HTML tokenizer for the builder's own output. `linkErrors_nil_iff`
states that every link it extracted resolves; it does not prove that the tokenizer finds
every link a browser would follow, that GitHub Pages serves the files, or that external
links are live. `routesAfter` finds each literal occurrence of `standardUrl`; a link into the
standard written any other way (relative, another edition, percent-encoded) is not found.
`renderedRows` relies on the standard's `checklistRow` role being the only producer of
`checklistRowClass` (by inspection of `website/RegulaExample.lean`). Deployment, Verso rendering
and browser behavior are operational observations recorded by the builder and in the website
guide.
-/

namespace Regula.Site

/-- The repository whose sources the site documents. -/
def repository : String := "https://github.com/rbeauchamp/regula"

/-- The GitHub Pages project-site origin every published edition lives under. -/
def siteBase : String := "https://rbeauchamp.github.io/regula/"

/-- The URL path of the project site. Absolute links in the output must start with it. -/
def basePath : String := "/regula/"

/-! ## Identity and routes -/

/-- Lowercase hexadecimal digit. -/
def isHexLower (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- A full lowercase hexadecimal Git commit identifier. -/
def IsCommit (s : String) : Prop := s.length = 40 ∧ s.toList.all isHexLower = true

instance (s : String) : Decidable (IsCommit s) := inferInstanceAs (Decidable (_ ∧ _))

/-- A validated commit identifier. Revision routes only accept this type. -/
abbrev Commit := { s : String // IsCommit s }

/-- The commit identifier `s`, when it is 40 lowercase hexadecimal digits (`IsCommit`). -/
def Commit.parse? (s : String) : Option Commit :=
  if h : IsCommit s then some ⟨s, h⟩ else none

/-- A published edition of the rule reference. `dev` is the latest successful deployment;
`rev c` is the snapshot of commit `c`. Released-package editions (`v/<version>/`) are part
of the route policy but none is published, so the type has no constructor for them. -/
inductive Edition where
  /-- The development edition: the latest successful deployment of `main`. -/
  | dev
  /-- The snapshot of commit `commit`. -/
  | rev (commit : Commit)

/-- Artifact directory of an edition, relative to the project site root. -/
def Edition.root : Edition → String
  | .dev => "dev/"
  | .rev c => "rev/" ++ c.val ++ "/"

/-- Directory route of a rule page within an edition, derived from the rule identity. -/
def Edition.pagePath (e : Edition) (id : RuleId) : String := e.root ++ id.route

/-- Artifact file of a rule page. -/
def Edition.pageFile (e : Edition) (id : RuleId) : String := e.pagePath id ++ "index.html"

/-- Distinct rules have distinct routes in every edition. -/
theorem Edition.pagePath_injective (e : Edition) {a b : RuleId}
    (h : e.pagePath a = e.pagePath b) : a = b :=
  RuleId.route_injective ((String.append_right_inj _).mp h)

theorem Edition.pageFile_injective (e : Edition) {a b : RuleId}
    (h : e.pageFile a = e.pageFile b) : a = b :=
  e.pagePath_injective ((String.append_left_inj _).mp h)

/-- The canonical development URL of a rule's explanation. -/
def devUrl (id : RuleId) : String := siteBase ++ Edition.dev.pagePath id

/-- Every rule page of an edition, in registry order. -/
def pageFiles (e : Edition) : List String := RuleId.all.map e.pageFile

/-- The page inventory has no duplicate route. -/
theorem pageFiles_nodup (e : Edition) : (pageFiles e).Nodup :=
  List.Pairwise.map e.pageFile (fun _ _ h eq => h (e.pageFile_injective eq)) RuleId.all_nodup

/-- The page inventory contains every registered rule. -/
theorem mem_pageFiles (e : Edition) (id : RuleId) : e.pageFile id ∈ pageFiles e :=
  List.mem_map_of_mem (RuleId.mem_all id)

/-! ## Retained revision snapshots -/

/-- The revision snapshots of an artifact: every snapshot of the site archive, then the
snapshot of the current build when it is clean (`some c`) and not yet archived. -/
def artifactRevisions (archived : List Commit) (current : Option Commit) : List Commit :=
  match current with
  | some c => if c ∈ archived then archived else archived ++ [c]
  | none => archived

/-- An artifact has exactly the archived snapshots and the current clean build's snapshot. -/
theorem mem_artifactRevisions (archived : List Commit) (current : Option Commit) (c : Commit) :
    c ∈ artifactRevisions archived current ↔ c ∈ archived ∨ current = some c := by
  cases current with
  | none => simp [artifactRevisions]
  | some d =>
    by_cases h : d ∈ archived
    · simp only [artifactRevisions, h, ite_true, Option.some.injEq]
      exact ⟨Or.inl, fun hc => hc.elim id (fun e => e ▸ h)⟩
    · simp [artifactRevisions, h, eq_comm]

/-- No archived snapshot is dropped from an artifact. -/
theorem archived_subset_artifactRevisions (archived : List Commit) (current : Option Commit) :
    archived ⊆ artifactRevisions archived current :=
  fun _ h => (mem_artifactRevisions _ _ _).mpr (Or.inl h)

/-- A larger archive yields a larger artifact: appending to the archive never removes a
snapshot from a later artifact. -/
theorem artifactRevisions_mono {archived archived' : List Commit} (h : archived ⊆ archived')
    (current : Option Commit) :
    artifactRevisions archived current ⊆ artifactRevisions archived' current := by
  intro c hc
  rw [mem_artifactRevisions] at hc ⊢
  exact hc.imp (fun m => h m) id

/-- A duplicate-free archive yields a duplicate-free snapshot list. -/
theorem artifactRevisions_nodup {archived : List Commit} (h : archived.Nodup)
    (current : Option Commit) : (artifactRevisions archived current).Nodup := by
  cases current with
  | none => exact h
  | some d =>
    by_cases hd : d ∈ archived
    · simpa [artifactRevisions, hd] using h
    · simp only [artifactRevisions, hd, ite_false]
      exact List.nodup_append.mpr ⟨h, (by simp), fun a ha b hb => by
        simp only [List.mem_singleton] at hb; subst hb; exact fun e => hd (e ▸ ha)⟩

/-- Upper bound on an artifact's total file bytes. It is below GitHub Pages' 1 GB limit on a
published site, which archived snapshots approach linearly in the number of deployments. -/
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

/-- Every availability, in the index filter's order (`mem_availabilities`). -/
def availabilities : List Availability := [.existingChecker, .plannedEngine]

theorem mem_availabilities (a : Availability) : a ∈ availabilities := by
  cases a <;> simp [availabilities]

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

/-- The availability's identifier in the index filter's markup and CSS. -/
def _root_.Regula.Availability.slug : Availability → String
  | .existingChecker => "existingChecker" | .plannedEngine => "plannedEngine"

/-- The availability's display text. -/
def _root_.Regula.Availability.label : Availability → String
  | .existingChecker => "Enforced by the checker" | .plannedEngine => "Planned"

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
  /-- The selected availability, or `none` for every availability. -/
  availability : Option Availability

/-- A rule is listed under a selection when it matches every restricted dimension. -/
def Selection.admits (s : Selection) (id : RuleId) : Bool :=
  s.category.all (fun c => decide (c = (descriptor id).category)) &&
  s.mode.all (fun m => decide (m ∈ (descriptor id).evidenceModes)) &&
  s.availability.all (fun a => decide (a = (descriptor id).availability))

/-- Each finite dimension together with its unrestricted choice. -/
def options {α : Type} (values : List α) : List (Option α) := none :: values.map some

theorem mem_options {α : Type} (values : List α) (h : ∀ v, v ∈ values) (o : Option α) :
    o ∈ options values := by
  cases o with
  | none => simp [options]
  | some v => simp [options, h v]

/-- Every filter state the index form can express. -/
def selections : List Selection :=
  (options categories).flatMap fun c => (options modes).flatMap fun m =>
    (options availabilities).map fun a => ⟨c, m, a⟩

theorem mem_selections (s : Selection) : s ∈ selections := by
  rcases s with ⟨c, m, a⟩
  simp only [selections, List.mem_flatMap, List.mem_map]
  exact ⟨c, mem_options _ mem_categories c, m, mem_options _ mem_modes m, a,
    mem_options _ mem_availabilities a, rfl⟩

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
      let suffix := ((a :: as).reverse.zip (b :: bs).reverse).takeWhile (fun p => p.1 = p.2) |>.length
      let middleA := (a :: as).take ((a :: as).length - suffix)
      let middleB := (b :: bs).take ((b :: bs).length - suffix)
      middleA.map .remove ++ middleB.map .add ++ ((a :: as).drop ((a :: as).length - suffix)).map .keep
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
  ((((s.replace "&quot;" "\"").replace "&#39;" "'").replace "&lt;" "<").replace "&gt;" ">").replace "&amp;" "&"

private def isSpace (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r' || c == '\x0c'

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
        (key, decodeEntities (String.ofList value)) :: parseAttributes fuel (body.drop (value.length + 1))
      | '\'' :: body =>
        let value := body.takeWhile (· != '\'')
        (key, decodeEntities (String.ofList value)) :: parseAttributes fuel (body.drop (value.length + 1))
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
      else if chunk.startsWith "/" || chunk.startsWith "!" || chunk.startsWith "?" then (.markup, tags)
      else
        let body := tagBody chunk.toList none
        let name := String.ofList (body.takeWhile (fun c => !(isSpace c || c == '/' || c == '>'))) |>.toLower
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
def Page.ofOther (path : String) : Page := { path, html := false, ids := [], base := none, links := [] }

/-- Directory part of an artifact path, with trailing `/`, or empty at the root. -/
def directory (path : String) : String :=
  match (path.splitOn "/").dropLast with
  | [] => ""
  | parts => String.intercalate "/" parts ++ "/"

/-- Normalize `.` and `..` segments; `none` when a path leaves the artifact root. -/
def normalize (path : String) : Option String :=
  let segments := path.splitOn "/"
  let trailing := segments.getLast? == some "" || segments.getLast? == some "." || segments.getLast? == some ".."
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
        (baseUrl.bind normalize).map fun u => if pathPart.isEmpty then u else directory u ++ pathPart
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

instance (pages : List Page) (page : Page) (link : String) : Decidable (LinkOK pages page link) := by
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

/-- Registered contract of the executed link check. -/
theorem checked_linkErrors : Regula.ExecutableContract linkErrors (fun run =>
    ∀ pages, run pages = [] ↔ ∀ page ∈ pages, ∀ link ∈ page.links, LinkOK pages page link) :=
  ⟨linkErrors_nil_iff⟩

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
#guard linkErrors [Page.ofHtml "dev/index.html" "<script>if (a<b) {}</script><a href=\"https://x.org/\">x</a>"] == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkErrors [Page.ofHtml "dev/index.html" "<a href=\"missing/?u=http://x\">x</a>"] != []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkErrors [Page.ofHtml "dev/index.html" "<a href=\"javascript://x\">x</a>"] != []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkErrors [Page.ofHtml "dev/rules/a.html" "<base href=\"x\"><a href=\"missing.html\">x</a>"] != []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkErrors [Page.ofHtml "dev/index.html" "<a title=\"a>b\" href=\"missing/\">x</a>"] != []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkErrors [Page.ofHtml "dev/rules/a.html" "<base href=\"..\"><a href=\"x\">x</a>",
  Page.ofOther "dev/rules/x"] != []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkErrors [Page.ofHtml "dev/rules/a.html" "<base href=\"..\"><a href=\"x\">x</a>", Page.ofOther "dev/x"] == []

/-! ## Normative clause anchors -/

/-- GitHub's heading anchor for an ASCII heading: lowercase, spaces to hyphens, other
punctuation removed. -/
def headingSlug (heading : String) : String :=
  String.ofList ((heading.toLower.toList.filter (fun c => c.isAlphanum || c == ' ' || c == '-' || c == '_')).map
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

/-- The anchors that no page with their path defines. An empty fragment needs only the page. -/
def missingAnchors (pages : List Page) (anchors : List (String × String)) : List (String × String) :=
  let index := pageIndex pages
  anchors.filter fun anchor =>
    !((index.getD anchor.1 []).any fun page => anchor.2 == "" || page.ids.contains anchor.2)

/-- The executed check returns nothing exactly when each anchor's path is a page that has its
fragment as an `id` or the fragment is empty. -/
theorem missingAnchors_nil_iff (pages : List Page) (anchors : List (String × String)) :
    missingAnchors pages anchors = [] ↔
      ∀ anchor ∈ anchors, ∃ page ∈ pages, page.path = anchor.1 ∧ (anchor.2 = "" ∨ anchor.2 ∈ page.ids) := by
  simp [missingAnchors, List.filter_eq_nil_iff, mem_pageIndex, Decidable.or_iff_not_imp_left]

/-- Registered contract of the executed anchor check. -/
theorem checked_missingAnchors : Regula.ExecutableContract missingAnchors (fun run =>
    ∀ pages anchors, run pages anchors = [] ↔
      ∀ anchor ∈ anchors, ∃ page ∈ pages, page.path = anchor.1 ∧ (anchor.2 = "" ∨ anchor.2 ∈ page.ids)) :=
  ⟨missingAnchors_nil_iff⟩

/-! ## Checklist row map -/

/-- The checklist rows a rendered page defines, in document order: the `id` of each element of
class `checklistRowClass`. -/
def renderedRows (html : String) : List String :=
  (scanTags html).filterMap fun t =>
    if t.get? "class" == some checklistRowClass then t.get? "id" else none

/-- The label of a link whose destination follows `before`, when that label is one code span:
`some label` exactly when `before` ends with ``[`label`](`` and `label` has no backtick. -/
def codeLinkLabel (before : String) : Option String :=
  match before.toList.reverse with
  | '(' :: ']' :: '`' :: rest =>
    let label := rest.takeWhile (· != '`')
    match rest.drop label.length with
    | '`' :: '[' :: _ => some (String.ofList label.reverse)
    | _ => none
  | _ => none

/-- The checklist rows a document links, in order: for each occurrence of the checklist page's
URL followed by `#`, the link's code-span label (`codeLinkLabel`) and the fragment after it. -/
def linkedRows (text : String) : List (Option String × String) :=
  let url := standardUrl ++ checklistChapter ++ "/#"
  ((text.splitOn url).dropLast.map codeLinkLabel).zip (routesAfter url text)

/-- How the rows a row map links differ from the checklist's rows, or `none` when each link is
labelled with its fragment and the fragments are the same list. -/
def rowMapMismatch (linked : List (Option String × String)) (rows : List String) : Option String :=
  if linked == rows.map fun row => (some row, row) then none else
    let fragments := linked.map (·.2)
    some s!"rows it does not link: {rows.filter (· ∉ fragments)}; linked fragments that are not rows: {fragments.filter (· ∉ rows)}; links not labelled with their fragment as one code span: {(linked.filter fun link => link.1 != some link.2).map (·.2)}; otherwise a row is linked more than once or out of the checklist's order"

/-- The executed row-map check passes exactly when the map links the checklist's rows, each
once, in the checklist's order, each labelled with exactly its row as one code span, and links
no other fragment of the checklist page. -/
theorem rowMapMismatch_eq_none_iff (linked : List (Option String × String)) (rows : List String) :
    rowMapMismatch linked rows = none ↔ linked = rows.map fun row => (some row, row) := by
  unfold rowMapMismatch
  split <;> simp_all

/-- Registered contract of the executed row-map check. -/
theorem checked_rowMapMismatch : Regula.ExecutableContract rowMapMismatch (fun run =>
    ∀ linked rows, run linked rows = none ↔ linked = rows.map fun row => (some row, row)) :=
  ⟨rowMapMismatch_eq_none_iff⟩

/-! Evaluated controls (observations of the compiled scanners, not proofs): a route ends at a
Markdown delimiter or a sentence's closing `.`, an autolink and a code span count, a page route
names its `index.html`, a row link's label is read only from a code span that is the whole link
text, and only elements of the row class are rows. -/
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentAnchors ["[a](" ++ standardUrl ++ "9-compliance-audit/#DOC-04). <" ++ standardUrl ++
  ">; `" ++ standardUrl ++ "introduction/`."] ==
  [("9-compliance-audit/index.html", "DOC-04"), ("index.html", ""), ("introduction/index.html", "")]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkedRows ("| [`A-1`](" ++ standardUrl ++ "9-compliance-audit/#A-1) |\n[x](" ++ standardUrl ++
  "9-compliance-audit/)") == [(some "A-1", "A-1")]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkedRows ("[`A-1`](" ++ standardUrl ++ "9-compliance-audit/#A-2) [A-3](" ++ standardUrl ++
  "9-compliance-audit/#A-3) [x `A-4`](" ++ standardUrl ++ "9-compliance-audit/#A-4)") ==
  [(some "A-1", "A-2"), (none, "A-3"), (none, "A-4")]
example : (rowMapMismatch [(some "A-1", "A-2")] ["A-2"] != none) = true := by decide
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard renderedRows "<h2 id=\"audit-matrix\">x</h2><code id=\"A-1\" class=\"checklist-row\">A-1</code>" ==
  ["A-1"]

end Regula.Site
