import RegulaCore.Guidance
import RegulaCore.Prose
import RegulaCore.Guide

/-! # Rule-reference page sources

Pure construction of the Verso source of every generated page of the rule reference. The
operational builder (`Regula.Site.Build`) supplies the resolved clause links; it writes exactly the
strings returned here.

## Main declarations

- `Identity`: the exact build identity every page states (commit, toolchain, linter version).
- `Example`, `Example.of`, `ShownFile`: the display form of one rule's example pair, read from the
  registry.
- `leadFactsHtml`: what checks the rule and the line `lake lint` prints for it, as `regula explain`
  states them (`Regula.Guidance.checkedBy`, `Regula.Guidance.reportForm`).
- `ruleSections`, `ruleSections_sublist`, `required_mem_ruleSections`: every rule page has
  every required section and only sections of the fixed page order, in that order, by
  construction; the proof-shape and configuration sections appear when the rule has them.
- `rulePage`: the Verso module of one rule page: status chips, the problem, *What to do* and
  the example first. What the checked rules share is stated once, on the enforcement page
  (`enforcementRoute`), which each of their pages links. Data enters raw HTML only through `escape`
  (`escape_safe`) and raw HTML enters Verso only through `htmlBlock` (`htmlBlock_ok`).
- `indexHtml`: the no-JavaScript rule catalogue with CSS-only select filters whose no-match
  notice is emitted for exactly `emptySelections` (`mem_emptySelections`).

## Boundaries

These functions define page text. That Verso renders it, that browsers apply the CSS filters
as specified and that the output is served are observations recorded by the builder and in
`docs/guides/website.md`, not consequences of these definitions.
-/

namespace Regula.Site

open Regula.Review (Residual Trusted)

/-- Exact identity of one site build. -/
structure Identity where
  /-- The checked-out commit the site is built from. -/
  revision : Commit
  /-- The build used uncommitted changes on top of `revision` (local previews only). -/
  dirty : Bool
  /-- The Lean toolchain the checker executables were built with. -/
  toolchain : String
  /-- The producer version the checker executables embed. -/
  producerVersion : String
  /-- The Verso revision pinned in the website package's lock manifest. -/
  versoRevision : String

/-- A file of a rule's example pair: its repository path and exact text. -/
structure ShownFile where
  /-- The file's repository path (`ExamplePair.compliantPath`, `ExamplePair.noncompliantPath`). -/
  path : String
  /-- The file's exact text. -/
  text : String

/-- Display form of one rule's example pair. -/
structure Example where
  /-- The noncompliant file. -/
  noncompliant : ShownFile
  /-- The compliant file. -/
  compliant : ShownFile

/-- The example pair that the registry holds for rule `id`. -/
def Example.of (id : RuleId) : Example :=
  let e := (descriptor id).examples
  { noncompliant := { path := e.noncompliantPath id, text := e.noncompliant }
    compliant := { path := e.compliantPath id, text := e.compliant } }

/-- Resolved normative clause: its registry text and its URL at the build revision. -/
structure Clause where
  /-- The clause's citation text (`Regula.Clause.label`). -/
  label : String
  /-- The clause's link target (the builder passes `Regula.Clause.route`, relative to the
  edition root). -/
  url : String

/-! ## Links -/

/-- The first 12 characters of a commit identifier. -/
def shortRevision (c : Commit) : String := String.ofList (c.val.toList.take 12)

/-- The GitHub URL of repository file `path` at the build revision. -/
def blobUrl (ident : Identity) (path : String) : String :=
  repository ++ "/blob/" ++ ident.revision.val ++ "/" ++ path

/-- The GitHub URL of the repository tree at the build revision. -/
def treeUrl (ident : Identity) : String := repository ++ "/tree/" ++ ident.revision.val

/-- Resolve the `@repo/` link token of guide prose to the build revision, and make each rule ID in
its prose a link to that rule's page in the same edition (`Prose.linkVerso`). -/
def resolveProse (ident : Identity) (text : String) : String :=
  Prose.linkVerso
    (text.replace "(@repo/" ("(" ++ repository ++ "/blob/" ++ ident.revision.val ++ "/"))

/-- Repository paths linked by `@repo/` tokens in a prose string. -/
def proseLinks (text : String) : List String :=
  ((text.splitOn "(@repo/").drop 1).map fun rest => ((rest.splitOn ")").headD "").splitOn "#"
                                                     |>.headD ""

/-- Every repository path a guide links or cites. -/
def Guide.repositoryPaths (g : Guide) : List String :=
  g.sources ++ ([g.problem.toString] ++ g.trigger ++ g.rationaleDetail ++
    g.proofShape ++ g.established ++ g.notEstablished ++ g.configuration ++ g.limitations).flatMap
        proseLinks

/-! ## HTML fragments (all data escaped) -/

private def code (s : String) : String := "<code>" ++ escape s ++ "</code>"

private def link (url text : String) : String :=
  "<a href=\"" ++ escape url ++ "\">" ++ text ++ "</a>"

/-- Target of the page-level links Verso emits (`route/#tag`); Verso gives the page heading no
`id`. -/
def pageAnchor (tag : String) : String := "<span id=\"" ++ escape tag ++ "\"></span>"

/-- The rule's ID as a link to its page in the same edition (`RuleId.route`, resolved through the
page's `<base href>`). -/
def ruleLink (id : RuleId) : String := link id.route id.spelling

/-- Inline text whose only markup is backtick code spans (the registry's one-line fields): the
spans become `code` elements, each rule ID outside them becomes a link to its page (`ruleLink`)
and all other text is escaped, so no backtick survives. -/
def inlineHtml (text : String) : String :=
  let parts := text.splitOn "`"
  String.join ((List.range parts.length).zip parts |>.map fun (i, part) =>
    if i % 2 == 1 then code part else Prose.rewriteIds escape ruleLink part)

/-- The label of the edition line: `development` for an unreleased build, otherwise the release. -/
def buildLabel : Build → String
  | .unreleased => "development"
  | .release v => "Regula " ++ v.spelling

/-- The version line every generated page carries: the installed build's label, the commit and
toolchain it was built from, and the versions page of its edition. Links are relative to the
edition root, so the same pages serve any edition. -/
def editionHtml (ident : Identity) : String :=
  let sep := " · "
  "<aside class=\"regula-edition\" aria-label=\"Documentation version\"><p><span \
    class=\"regula-pill\">" ++ escape (buildLabel installed) ++ "</span> built from " ++
  (if ident.dirty then "uncommitted changes on " else "") ++ link (treeUrl ident)
  (code (shortRevision ident.revision)) ++ sep ++ "Lean " ++ escape ident.toolchain ++ sep ++
  (if ident.dirty then "local preview" ++ sep else "") ++ link "versions/" "versions" ++
      "</p></aside>"

private def joinComma (xs : List String) : String := String.intercalate ", " xs

/-- The lifecycle sentence of a retired rule's chip: the release that retired it and its
replacement. -/
def lifecycleText {id : RuleId} : Lifecycle id → String
  | .active introduced => "Active since " ++ introduced.spelling
  | .retired introduced version replacement =>
      "Retired in " ++ version.spelling ++ " (introduced " ++ introduced.spelling ++ ")" ++
      (match replacement with | some r => "; replaced by " ++ r.val.spelling | none => "")

/-- Every rule's findings are errors under a strict claim, as the enforcement page states once
for all of them. -/
theorem descriptor_severity_error (id : RuleId) :
    (descriptor id).defaultStrictSeverity = .error := by
  cases id <;> rfl

private def chip (body : String) : String := "<li class=\"regula-chip\">" ++ body ++ "</li>"

/-- The rule's status chips: category, scope and, when retired, its lifecycle. -/
def chipsHtml (id : RuleId) : String :=
  let d := descriptor id
  "<ul class=\"regula-chips\" aria-label=\"Rule status\">" ++
  chip ("Category <strong>" ++ escape d.category.label ++ "</strong>") ++
  chip ("Scope <strong>" ++ escape d.scope.label ++ "</strong>") ++
  (match d.lifecycle with
    | .active _ => ""
    | .retired .. => chip ("<strong>" ++ inlineHtml (lifecycleText d.lifecycle) ++ "</strong>"))
        ++ "</ul>"

private def fact (term value : String) : String := "<dt>" ++ term ++ "</dt><dd>" ++ value ++ "</dd>"

/-- The route of the page that states once what every rule page shares: strict impact, local
options, where rules run, the form of a finding, the open obligations and trusted mechanisms, and
how examples are produced. -/
def enforcementRoute : String := "enforcement/"

/-- The one definition of obligation `r`, on the enforcement page. -/
def residualRoute (r : Residual) : String := enforcementRoute ++ "#" ++ r.spelling

/-- The obligations `rs`, each linked to its definition on the enforcement page. -/
def residualLinks (rs : List Residual) : String :=
  joinComma (rs.map fun r => link (residualRoute r) (code r.spelling))

/-- The facts shown under the lead: the rule's one-line requirement, what checks it and the form of
the line `lake lint` prints for it, both as `regula explain` states them (`Guidance.checkedBy`,
`Guidance.reportForm`), and, unless the rule is retired, a link to what the checked rules share. -/
def leadFactsHtml (id : RuleId) : String :=
  let d := descriptor id
  "<dl class=\"regula-facts\">" ++
  fact "Requirement" (inlineHtml d.requirement) ++
  fact "Checked by" (inlineHtml (Guidance.checkedBy id)) ++
  (match Guidance.reportForm id with
    | some form => fact "Finding form" (code form)
    | none => "") ++
  (if d.lifecycle.isRetired then "" else
    fact "Enforcement" ("Strict: see " ++ link enforcementRoute "how rules are enforced" ++ ".")) ++
  "</dl>"

/-- The rule's sources, under *Sources*: its resolved clause links, the checklist rows of its
explanation, its detector sources at the build revision and which steps of its decision are
proved. -/
def sourceFactsHtml (ident : Identity) (clauses : List Clause)
    (checklist sources : List String) (linkage : String) : String :=
  "<dl class=\"regula-facts\">" ++
  fact "Normative clauses" (joinComma (clauses.map fun c => link c.url (escape c.label))) ++
  fact "Checklist rows" (joinComma (checklist.map fun r => link (checklistRoute r) (code r))) ++
  fact "Detector, policy and proof sources"
      (joinComma (sources.map fun p => link (blobUrl ident p) (code p))) ++
  fact "Proved linkage" (inlineHtml linkage) ++ "</dl>"

private def lines (text : String) : List String :=
  let ls := text.splitOn "\n"
  if ls.getLast? == some "" then ls.dropLast else ls

private def preHtml (text : String) : String :=
  "<pre class=\"regula-code\"><code>" ++ escape text ++ "</code></pre>"

/-- Split a diff into maximal runs of unchanged lines and single changed lines. -/
def diffRuns : List DiffLine → List (List String ⊕ DiffLine)
  | [] => []
  | .keep l :: rest => match diffRuns rest with
    | .inl ls :: runs => .inl (l :: ls) :: runs
    | runs => .inl [l] :: runs
  | line :: rest => .inr line :: diffRuns rest

private def keepHtml (l : String) : String := "<span class=\"regula-keep\">  " ++ escape l ++
    "</span>\n"

private def foldHtml (n : Nat) : String := "<span class=\"regula-keep\">  ⋯ " ++ toString n ++
    " unchanged lines</span>\n"

/-- Show at most `context` unchanged lines around each change; longer runs are summarized. -/
def keepRunHtml (context : Nat) (first last : Bool) (ls : List String) : String :=
  let n := ls.length
  let head := if first then 0 else context
  let tail := if last then 0 else context
  if n ≤ head + tail + 1 then String.join (ls.map keepHtml)
  else String.join ((ls.take head).map keepHtml) ++ foldHtml (n - head - tail) ++ String.join
        ((ls.drop (n - tail)).map keepHtml)

/-- An admitted diff with `+`/`-` markers, so status never depends on colour. Unchanged runs
far from a change are summarized; the full texts are shown separately. -/
def diffHtml (d : List DiffLine) : String :=
  let runs := diffRuns d
  "<pre class=\"regula-diff\"><code>" ++ String.join
      ((List.range runs.length).zip runs |>.map fun (i, run) =>
    match run with
    | .inl ls => keepRunHtml 3 (i == 0) (i + 1 == runs.length) ls
    | .inr (.remove l) => "<del class=\"regula-remove\">- " ++ escape l ++ "</del>\n"
    | .inr (.add l) => "<ins class=\"regula-add\">+ " ++ escape l ++ "</ins>\n"
    | .inr (.keep l) => keepHtml l) ++ "</code></pre>"

/-- A file of a rule's example pair: a link to it at the build revision, and its exact text. -/
def shownHtml (ident : Identity) (f : ShownFile) : String :=
  "<figure class=\"regula-file\"><figcaption>" ++ link (blobUrl ident f.path) (code f.path) ++
    "</figcaption>" ++ preHtml f.text ++ "</figure>"

/-- The sentence above each example: where its files come from. -/
def exampleNote : String :=
  "The noncompliant and the compliant file of the rule's example pair, as the registry holds \
    them. No run of the checker produced this example."

/-- A rule's example: the noncompliant file, the correction diff and the compliant file. -/
def exampleHtml (ident : Identity) (ex : Example) : Except String String := do
  let before := lines ex.noncompliant.text
  let after := lines ex.compliant.text
  let d ← admitDiff before after
  let terminator :=
    if before == after then "<p>Only the final line terminator differs.</p>" else ""
  return "<div class=\"regula-example\"><p>" ++ escape exampleNote ++ "</p>" ++
    "<h3>Noncompliant file</h3>" ++ shownHtml ident ex.noncompliant ++
    "<h3>Correction</h3><figure class=\"regula-diff-panel\"><figcaption>Change from " ++
    code ex.noncompliant.path ++ " to " ++ code ex.compliant.path ++ "</figcaption>" ++
    diffHtml d.val ++ "</figure>" ++ terminator ++
    "<h3>Compliant file</h3>" ++ shownHtml ident ex.compliant ++ "</div>"

/-! ## Verso text -/

private def paragraphs (ident : Identity) (xs : List String) : String :=
  String.join (xs.map fun p => resolveProse ident p ++ "\n\n")

private def numbered (ident : Identity) (xs : List String) : String :=
  String.join
      ((List.range xs.length).zip xs |>.map fun (i, p) => s!"{i + 1}. " ++ resolveProse ident p ++
                                                           "\n") ++ "\n"

private def bullets (ident : Identity) (xs : List String) : String :=
  String.join (xs.map fun p => "* " ++ resolveProse ident p ++ "\n") ++ "\n"

/-- A generated section heading with a stable tag for deep links. -/
def sectionHead (id : RuleId) (suffix heading : String) : String :=
  "# " ++ heading ++ "\n%%%\ntag := \"" ++ id.spelling ++ "-" ++ suffix ++
      "\"\nnumber := false\n%%%\n\n"

/-- The headings of a rule page's sections, in page order. -/
def sectionOrder : List String :=
  ["Example", "How to fix it", "Why it matters", "What triggers it", "Required proof shape",
    "What a passing result establishes", "Configuration and exceptions",
    "Limitations and unsupported cases", "Sources"]

/-- The headings every rule page has. The proof shape and configuration sections appear only
when the rule's explanation has them. -/
def requiredHeadings : List String :=
  ["Example", "How to fix it", "Why it matters", "What triggers it",
    "What a passing result establishes", "Limitations and unsupported cases", "Sources"]

/-- Every section of a rule page, in order, with its heading, stable tag suffix and Verso body,
before optional sections without content are dropped. `ex` is the example body, `facts` the sources
and `obligations` the linked open review obligations, each already admitted as raw HTML. -/
def allRuleSections (ident : Identity) (id : RuleId) (g : Guide) (ex facts obligations : String) :
    List (String × String × String) := [
  ("Example", "example", ex),
  ("How to fix it", "fix", numbered ident (descriptor id).rewrites),
  ("Why it matters", "rationale", paragraphs ident
      ((descriptor id).rationale :: g.rationaleDetail)),
  ("What triggers it", "trigger", paragraphs ident g.trigger),
  ("Required proof shape", "proof-shape", paragraphs ident g.proofShape),
  ("What a passing result establishes", "established",
    paragraphs ident g.established ++ "It does not establish:\n\n" ++
        bullets ident g.notEstablished ++
    obligations ++ "\n"),
  ("Configuration and exceptions", "configuration", paragraphs ident g.configuration),
  ("Limitations and unsupported cases", "limitations", paragraphs ident g.limitations),
  ("Sources", "sources", facts ++ "\n")]

/-- The sections of a rule page: every required section, and each optional one that has
content. -/
def ruleSections (ident : Identity) (id : RuleId) (g : Guide) (ex facts obligations : String) :
    List (String × String × String) :=
  (allRuleSections ident id g ex facts obligations).filter fun s =>
    s.1 ∈ requiredHeadings || !s.2.2.isEmpty

/-- A rule page's sections follow the fixed page order. -/
theorem ruleSections_sublist (ident : Identity) (id : RuleId) (g : Guide)
    (ex facts obligations : String) :
    List.Sublist ((ruleSections ident id g ex facts obligations).map (·.1)) sectionOrder :=
  List.filter_sublist.map _

/-- Every rule page has every required section. -/
theorem required_mem_ruleSections (ident : Identity) (id : RuleId) (g : Guide)
    (ex facts obligations : String) {heading : String} (h : heading ∈ requiredHeadings) :
    heading ∈ (ruleSections ident id g ex facts obligations).map (·.1) := by
  simp only [requiredHeadings, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ruleSections, allRuleSections, requiredHeadings]

/-- A title usable in a Lean string literal and a Verso heading without escaping. -/
def plainTitle (s : String) : Bool :=
  s.toList.all fun c => c.isAlphanum || c == ' ' || c == ':' || c == '-' || c == ',' || c == '.'

/-- Complete Verso module of one rule page. It opens with the status chips, the problem as the
lead paragraph and *What to do* (styled by adjacency to the chips), then the facts of
`leadFactsHtml`, and then the sections, the registry's example pair first. -/
def rulePage (ident : Identity) (id : RuleId) (clauses : List Clause) : Except String String := do
  let d := descriptor id
  let g := guide id
  let title := id.spelling ++ ": " ++ d.title
  unless plainTitle title do throw s!"{id.spelling}: title needs escaping"
  let notice ← htmlBlock (pageAnchor id.spelling ++ editionHtml ident ++ chipsHtml id)
  let leadFacts ← htmlBlock (leadFactsHtml id)
  let exampleBlock ← htmlBlock (← exampleHtml ident (Example.of id))
  let facts ← htmlBlock (sourceFactsHtml ident clauses g.checklist g.sources g.linkage.toString)
  let obligations ← htmlBlock ("<p>It leaves these review obligations open: " ++
      residualLinks g.residuals ++ ".</p>")
  let exampleBody := exampleBlock ++ "\n" ++ resolveProse ident d.examples.correction ++ "\n\n"
  let sections := ruleSections ident id g exampleBody facts obligations
  return "import VersoManual\nimport RegulaSite\nopen Verso.Genre Manual RegulaSite\n\n#doc \
    (Manual) \"" ++ title ++
    "\" =>\n%%%\ntag := \"" ++ id.spelling ++ "\"\nfile := \"" ++ id.spelling ++
        "\"\nshortTitle := \"" ++ id.spelling ++
    "\"\nnumber := false\n%%%\n\n" ++ notice ++ "\n" ++
    resolveProse ident g.problem.toString ++ "\n\n**What to do.** " ++
        resolveProse ident d.remedy ++ "\n\n" ++
    leadFacts ++ "\n" ++
    String.join (sections.map fun (heading, suffix, body) => sectionHead id suffix heading ++ body)

/-! ## Rule index -/

private def selectId (dimension : String) : String := "f-" ++ dimension

private def select (dimension label : String) (values : List (String × String)) : String :=
  "<label>" ++ label ++ "<select id=\"" ++ selectId dimension ++ "\" name=\"" ++
      dimension ++ "\">" ++
  String.join ((("all", "All") :: values).map fun (value, text) =>
    "<option value=\"" ++ value ++ "\"" ++ (if value == "all" then " selected" else "") ++ ">" ++
        escape text ++ "</option>") ++
  "</select></label>"

private def optionSlug {α : Type} (slug : α → String) : Option α → String
  | none => "all"
  | some v => slug v

/-- The selector that matches while `dimension`'s select has `value` chosen. -/
private def chosen (dimension value : String) : String :=
  ":has(#" ++ selectId dimension ++ " option[value=\"" ++ value ++ "\"]:checked)"

private def selectionSelector (s : Selection) : String :=
  ".regula-index" ++ chosen "category" (optionSlug RuleCategory.slug s.category) ++
  chosen "check" (optionSlug RuleCheck.slug s.check)

/-- Filter CSS: one hiding rule per restricted value, and the no-match notice for exactly the
selections in `emptySelections`. -/
def filterCss : String :=
  String.join (categories.map fun c => ".regula-index" ++ chosen "category" c.slug ++
    " tr.regula-rule:not(.category-" ++ c.slug ++ "){display:none}\n") ++
  String.join (checks.map fun c => ".regula-index" ++ chosen "check" c.slug ++
    " tr.regula-rule:not(.check-" ++ c.slug ++ "){display:none}\n") ++
  String.join
      (emptySelections.map fun s => selectionSelector s ++
                                     " tr.regula-no-match{display:table-row}\n")

private def ruleRow (id : RuleId) : String :=
  let d := descriptor id
  let tag (text : String) := " <span class=\"regula-tag\">" ++ escape text ++ "</span>"
  let check := checkOf id
  "<tr class=\"regula-rule category-" ++ d.category.slug ++ " check-" ++ check.slug ++ "\">" ++
  "<th scope=\"row\"><a href=\"" ++ id.route ++ "\">" ++ code id.spelling ++ "</a></th>" ++
  "<td><a class=\"regula-title\" href=\"" ++ id.route ++ "\">" ++ escape d.title ++ "</a>" ++
  (match d.lifecycle with | .active _ => "" | .retired .. => tag "Retired") ++ "</td>" ++
  "<td>" ++ escape d.category.label ++ "<span class=\"regula-sub\">" ++ escape d.scope.label ++
      "</span></td>" ++
  "<td>" ++ (if check == .retired then escape check.label else code check.label) ++ "</td></tr>"

/-- The complete catalogue, derived from the registry, with CSS-only filters over the exact
category and check. -/
def indexHtml : String :=
  "<div class=\"regula-index\"><form class=\"regula-filters\" aria-label=\"Filter rules\" \
    action=\"#\">" ++
  select "category" "Category" (categories.map fun c => (c.slug, c.label)) ++
  select "check" "Checked by" (checks.map fun c => (c.slug, c.label)) ++
  "<input type=\"reset\" value=\"Reset\"></form>" ++
  "<div class=\"regula-scroll\" role=\"region\" aria-label=\"Rule catalogue\" \
    tabindex=\"0\"><table class=\"regula-rules\"><caption>All " ++ toString RuleId.all.length ++
        " registered rules</caption><thead><tr>" ++
  "<th scope=\"col\">ID</th><th scope=\"col\">Rule</th><th scope=\"col\">Category</th><th \
    scope=\"col\">Checked by</th></tr></thead><tbody>" ++
  String.join (RuleId.all.map ruleRow) ++
  "<tr class=\"regula-no-match\"><td colspan=\"4\">No registered rule matches the selected \
    filters. Use <strong>Reset</strong> to show every rule.</td></tr>" ++
  "</tbody></table></div><style>" ++ filterCss ++ "</style></div>"

end Regula.Site
