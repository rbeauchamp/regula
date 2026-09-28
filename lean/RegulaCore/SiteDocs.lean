import RegulaCore.SitePage
import RegulaCore.Lint

/-! # Rule-reference manual structure

Pure construction of the generated Verso manual around the rule pages: the home page, the
rule index part that includes every rule page, the enforcement page that states once what every
rule shares, the checklist coverage page, the versions page and the credits page.

## Main declarations

- `ruleModule`, `ruleModules`, `ruleModules_nodup`: the generated Verso module of each rule,
  one per registry entry.
- `homePage`, `indexPage`, `enforcementPage`, `coveragePage`, `versionsPage`, `creditsPage`: the
  remaining generated modules. The coverage page lists each checklist row with `rulesOfRow` and
  `residualsOfRow`, the inverses of the rule explanations' `checklist` and of `Residual.rows`
  (`mem_rulesOfRow`, `mem_residualsOfRow`). The enforcement page defines each obligation once,
  under the element id its identifier names (`residualRoute`).
- `EvidenceSummary`: one rule's checked-example evidence, as `build.json` records it.

## Boundaries

Links to repository documents point at the build revision on GitHub; whether GitHub serves
them is outside this module. The versions text describes the publishing workflow in
`.github/workflows/ci.yml`; that the workflow behaves so is an operational observation.
-/

namespace Regula.Site

open Regula.Checker.Account (Residual Trusted)
open Regula.Checker.Lint (Outcome)

/-- Generated Verso module name of a rule page. -/
def ruleModule (id : RuleId) : String := "Generated.Rules." ++ id.spelling

theorem ruleModule_injective {a b : RuleId} (h : ruleModule a = ruleModule b) : a = b :=
  RuleId.spelling_injective ((String.append_right_inj _).mp h)

/-- The generated rule-page modules, one per rule in registry order. -/
def ruleModules : List String := RuleId.all.map ruleModule

/-- One generated module per rule and no duplicate module. -/
theorem ruleModules_nodup : ruleModules.Nodup :=
  List.Pairwise.map ruleModule (fun _ _ h eq => h (ruleModule_injective eq)) RuleId.all_nodup

private def header (imports : List String) (title tag : String) (file : Option String)
    (split : Bool := true) (toc : Bool := true) : String :=
  "import VersoManual\nimport RegulaSite\n" ++ String.join
      (imports.map fun m => "import " ++ m ++ "\n") ++
  "open Verso.Genre Manual RegulaSite\n\n#doc (Manual) \"" ++ title ++ "\" =>\n%%%\ntag := \"" ++
      tag ++ "\"\n" ++
  (match file with | some f => "file := \"" ++ f ++ "\"\n" | none => "") ++ "number := false\n" ++
  (if split then "" else "htmlSplit := .never\n") ++ (if toc then "" else "htmlToc := false\n") ++
  "%%%\n\n"

private def subsection (tag heading : String) : String :=
  "# " ++ heading ++ "\n%%%\ntag := \"" ++ tag ++ "\"\nnumber := false\n%%%\n\n"

/-- The site's home page (the edition root): what Regula rejects and where a newcomer starts,
then the four things a reader comes to do, in order. -/
def homePage (ident : Identity) : Except String String := do
  let notice ← htmlBlock (pageAnchor "regula" ++ editionHtml ident)
  let doc (path text : String) := "[" ++ text ++ "](" ++ blobUrl ident path ++ ")"
  return header ["Generated.Rules", "Generated.Enforcement", "Generated.Coverage",
      "RegulaStandard", "Generated.Versions", "Generated.Credits"]
      "Regula rule reference" "regula" none ++
    notice ++ "\n" ++
    "**Regula for Lean** is a strict linter: `lake lint` does not accept a project with a \
      `sorry`, a project axiom, a compiler-trusting proof such as `native_decide`, or an axiom \
      beyond the foundation you chose, and names every `extern` and `implemented_by` boundary \
      your executables reach. Every rule below has a checked failing example, its fix, and what \
      a pass does and does not establish. **New here?** Start with " ++
        doc "README.md" "what it checks and how to try it" ++ ".\n\n" ++
    "1. **Decide whether to adopt.** The [rule index](rules/) lists all " ++
        toString RuleId.all.length ++ " rules, and [how rules are enforced](enforcement/) \
          states what they share: a violation fails the result, and missing evidence never \
          passes. The " ++ doc "docs/guides/adoption.md" "adoption guide" ++
              " covers installation, `lake lint`, editor feedback and CI; " ++
      "[the standard](standard/) and its [compliance checklist](standard/8-compliance-audit/) \
        define what the rules enforce; every Lean example of the standard is elaborated when this \
        site is built.\n" ++
    "2. **Look up a rule.** Every finding names a rule ID such as `RG1002` (editor code \
      `Regula.RG1002`) and ends with the URL of its page in the reference of the installed \
      Regula version; the editor's *View explanation* link opens the same page. A rule page \
      starts with what is wrong, what to do and a checked example. Open the \
      [rule index](rules/), or press `/` to search.\n" ++
    "3. **Review a Regula pass.** A finding is a violation, which makes the result FAIL, or \
      incomplete, which makes it INCOMPLETE because required evidence is missing; neither is \
      accepted. A pass is mechanical: each rule page states what the check establishes and which \
      review obligations stay with you, and [checklist coverage](coverage/) maps every row of \
      the compliance checklist to the rules that report on it and the review obligations it \
      carries.\n" ++
    "4. **Challenge a rule.** Each rule page gives the rule's rationale, its normative clauses and \
      its detector sources at the commit the page was built from. To dispute a rule or report a \
      wrong result, [open an issue](" ++ repository ++ "/issues).\n\n" ++
    "{include Generated.Rules}\n\n{include Generated.Enforcement}\n\n{include \
      Generated.Coverage}\n\n{include RegulaStandard}\n\n{include Generated.Versions}\n\n{include \
      Generated.Credits}\n"

/-- The rule index part, which includes every rule page. The index table lists every rule, so
Verso's list of the part's pages is turned off. -/
def indexPage (ident : Identity) : Except String String := do
  let notice ← htmlBlock (pageAnchor "rules" ++ editionHtml ident)
  let table ← htmlBlock indexHtml
  return header ruleModules "Rule index" "rules" (some "rules") (toc := false) ++ notice ++ "\n" ++
    "Every rule the linter can emit, generated from its typed registry. The filters work without \
      JavaScript. What every rule shares is on [how rules are enforced](enforcement/).\n\n" ++
    table ++ "\n" ++ String.join (ruleModules.map fun m => "{include " ++ m ++ "}\n\n")

/-- The `lake lint` exit codes, from the driver's own classification. -/
def exitCodesText : String :=
  ", ".intercalate ([Outcome.accepted, .violation, .configuration, .incomplete].map fun o =>
    "`" ++ toString o.exitCode ++ "` " ++ o.label)

/-- The enforcement page: what every rule page would otherwise repeat, stated once. -/
def enforcementPage (ident : Identity) : Except String String := do
  let notice ← htmlBlock (pageAnchor "enforcement" ++ editionHtml ident)
  let trusted ← htmlBlock ("<ul>" ++ String.join (Trusted.all.map fun t =>
      "<li><code>" ++ escape t.spelling ++ "</code>: " ++ escape t.detail ++ "</li>") ++ "</ul>")
  let obligations ← htmlBlock ("<ul>" ++ String.join (Residual.all.map fun r =>
      "<li id=\"" ++ escape r.spelling ++ "\"><code>" ++ escape r.spelling ++ "</code>: " ++
        inlineHtml r.description ++ ".</li>") ++ "</ul>")
  return header [] "How rules are enforced" "enforcement" (some "enforcement") (split := false) ++
      notice ++ "\n" ++
    "Every rule of the [rule index](rules/) is enforced the same way. This page states once what \
      their pages share.\n\n" ++
    subsection "enforcement-impact" "Strict impact" ++
    "Every rule's findings are errors under a strict claim. An established violation makes the \
      result FAIL; missing or unsupported evidence makes it INCOMPLETE. Neither is accepted. \
      `lake lint` exits with " ++ exitCodesText ++ "; it exits `2` when every finding of a FAIL \
      is RG2002. The editor shows a rule's local findings as warnings (errors under \
      `warningAsError`); they are not project results, and the rule pages say which rules the \
      editor reports.\n\n" ++
    subsection "enforcement-options" "No local exception" ++
    "No source option, attribute or command-line flag makes a rule pass on a claimed surface. \
      `set_option linter.regula false` and `regula.localFoundation` never waive a rule: \
      `lake lint`, the build-lint `policy` target and `axiomGate` still apply it. Where Regula's \
      local linter reports a finding during a project build (`axiomGate` and the `policy` target \
      keep it on by default; `lake lint` builds with it off, whatever the source sets \
      `linter.regula` to), that finding is a build warning, so the result is INCOMPLETE under \
      RG2003 instead of carrying the rule's finding. Switching the local linter off changes which \
      finding is reported, never whether the result is accepted. Hiding a diagnostic does not \
      establish the property it checks. RG5002 and RG5003 check the declarations registered with \
      `@[regula_material]`; removing a registration changes the reviewed claim, not only their \
      result.\n\n" ++
    subsection "enforcement-commands" "Where rules run" ++
    "Project enforcement runs through `lake lint` (incremental), `lake lint -- --fresh` and \
      `lake exe axiomGate` (fresh whole-project audits from empty build output), and the \
      build-lint `policy` target; `lake exe docFenceAudit` audits documentation examples. Each \
      rule page lists where the rule is reported. See the " ++
        "[adoption guide](" ++ blobUrl ident "docs/guides/adoption.md" ++ ").\n\n" ++
    subsection "enforcement-message" "How a finding reads" ++
    "The first line of every finding has the form `" ++ sharedMessageForm ++ "`. The finding \
      then gives the rule's remedy and ends with the rule's page in the reference of the \
      installed Regula version, and `lake exe regula explain <ID>` prints the full rule \
      offline.\n\n" ++
    subsection "enforcement-obligations" "Open review obligations" ++
    "Every accepted result lists every review obligation below as open, whatever rules it checked \
      (`R-GRAPH` only for a serialized-graph claim). A listed identifier is an open obligation, \
      never a completed review. Each rule page names the obligations its own result leaves \
      open, and [checklist coverage](coverage/) the checklist rows whose review each \
      carries.\n\n" ++
    obligations ++ "\n" ++
    subsection "enforcement-trusted" "Trusted mechanisms" ++
    "Every accepted result also relies on these trusted mechanisms (the checker's `Trusted` \
      account), which no rule verifies:\n\n" ++ trusted ++ "\n" ++
    subsection "enforcement-examples" "Checked examples" ++
    "Each rule page's example was produced for the page's commit by the rule-example corpus \
      campaign, admitted by the rule-example qualifier (whose admission relations are proved; \
      capture and process authenticity are trusted), and checked against the commit's checker, \
      corpus and configuration sources before the site was generated. The site build refuses \
      stale, incomplete or partial evidence. The campaign is scoped qualification of the \
      detectors for these inputs, not a proof that the detectors are correct for every \
      input.\n\n" ++
    "* " ++ exampleKindText "policyRejection" ++ "\n" ++
    "* " ++ exampleKindText "diagnosticDemonstration" ++ "\n\n"

private def coverageRow (row : String) : String :=
  let rules := rulesOfRow row
  "<tr><th scope=\"row\"><a href=\"" ++ checklistRoute row ++ "\"><code>" ++ escape row ++
      "</code></a></th><td>" ++
  (if rules.isEmpty then "Review only" else ", ".intercalate (rules.map fun id =>
      "<a href=\"" ++ id.route ++ "\"><code>" ++ id.spelling ++ "</code></a>")) ++ "</td><td>" ++
  residualLinks (residualsOfRow row) ++ "</td></tr>"

/-- The checklist coverage page: every row of the compliance checklist with the rules whose
explanation lists it (`mem_rulesOfRow`) and the review obligations that carry it
(`mem_residualsOfRow`), each of which carries at least one row (`residualsOfRow_ne_nil`). -/
def coveragePage (ident : Identity) : Except String String := do
  let notice ← htmlBlock (pageAnchor "coverage" ++ editionHtml ident)
  let table ← htmlBlock ("<div class=\"regula-scroll\" role=\"region\" aria-label=\"Checklist \
      coverage\" tabindex=\"0\"><table class=\"regula-rules\"><caption>Every checklist row, the \
      rules that report on it and its review obligations</caption><thead><tr><th \
      scope=\"col\">Row</th><th scope=\"col\">Rules</th><th scope=\"col\">Review \
      obligations</th></tr></thead><tbody>" ++ String.join (checklistRows.map coverageRow) ++
      "</tbody></table></div>")
  return header [] "Checklist coverage" "coverage" (some "coverage") (split := false) ++
      notice ++ "\n" ++
    "Each row of the [compliance checklist](standard/8-compliance-audit/) with the rules whose \
      page lists it and the review obligations it carries. The rules are derived from the rule \
      explanations, so they and the rule pages cannot disagree; the obligations are derived from \
      the checklist rows each obligation carries, as defined on [how rules are \
      enforced](enforcement/). A row that no rule lists is semantic review only. Every row carries \
      at least one obligation, so no row passes on a checker result alone: the checklist states \
      each row's required result and verification.\n\n" ++ table ++ "\n"

/-- One rule's checked-example evidence, as the artifact's `build.json` records it. -/
structure EvidenceSummary where
  /-- The rule whose checked example this row reports. -/
  rule : RuleId
  /-- The example kind the corpus recorded for the violating run. -/
  kind : String
  /-- The status of the violating run, as `RunStatus.spelling` prints it. -/
  violationStatus : String
  /-- The status of the corrected run, as `RunStatus.spelling` prints it. -/
  fixedStatus : String
  /-- The distinct rule IDs of the violating run's findings. -/
  emitted : List RuleId
  /-- The corpus shard that produced the example, as `index/count`. -/
  shard : String

/-- The versions page: this build's identity, the published editions and the release list. -/
def versionsPage (ident : Identity) : Except String String := do
  let notice ← htmlBlock (pageAnchor "versions" ++ editionHtml ident)
  let identity ← htmlBlock ("<dl class=\"regula-facts\">" ++
    "<dt>Regula</dt><dd><code>" ++ escape ident.producerVersion ++ "</code></dd>" ++
    "<dt>Commit</dt><dd><a href=\"" ++ escape (treeUrl ident) ++ "\"><code>" ++
        escape ident.revision.val ++ "</code></a></dd>" ++
    "<dt>Lean toolchain (linter and examples)</dt><dd><code>" ++ escape ident.toolchain ++
        "</code></dd>" ++
    "<dt>Verso revision</dt><dd><code>" ++ escape ident.versoRevision ++ "</code></dd>" ++
    "<dt>Releases</dt><dd>" ++ (if releases.isEmpty then "none yet" else
      ", ".intercalate (releases.reverse.map fun v =>
        "<a href=\"" ++ escape (basePath ++ (Edition.release v).root) ++ "\">" ++
            escape v.spelling ++ "</a>")) ++ "</dd>" ++
    "</dl>")
  return header [] "Versions" "versions" (some "versions") (split := false) ++
      notice ++ "\n" ++ identity ++ "\n" ++
    "* `" ++ siteBase ++ "` opens the latest release's copy, or the development version while no \
      release exists: the stable address to share.\n" ++
    "* `" ++ siteBase ++ "dev/` is the development version, rebuilt from `main` by every \
      deployment. An unreleased Regula build's findings link here.\n" ++
    "* `" ++ siteBase ++ "v/<version>/` is the permanent copy of a release, made when it is \
      released. A released Regula build's findings link to its own release's copy. Once a later \
      release exists, every page of an earlier copy names the latest release and links the same \
      page there.\n\n" ++
    "A route that is not published shows the site's not-available page. It never redirects to \
      other rules: an old link cannot silently acquire changed semantics. Rule IDs are never \
      reused for a changed rule; a retired rule keeps a page that says so.\n"

/-- The credits and licenses page. -/
def creditsPage (ident : Identity) : Except String String := do
  let notice ← htmlBlock (pageAnchor "credits" ++ editionHtml ident)
  return header [] "Credits and licenses" "credits" (some "credits") (split := false) ++
      notice ++ "\n" ++
    "Regula and this site's generated content are released under the [MIT license](" ++
        blobUrl ident "LICENSE" ++ "). The rule explanations are original.\n\n" ++
    "**Lean and Lake.** The linter, its editor messages and its Lake integration are built on Lean \
      4 and Lake by the Lean FRO and contributors (Apache 2.0), used through the pinned toolchain \
      as dependencies. The editor's *View explanation* link is Lean's own error-description \
      widget, shown in the infoview of the VS Code Lean 4 extension (leanprover/vscode-lean4). The \
      linter's strict JSON parser adapts the container recursion of Lean's \
      `Lean/Data/Json/Parser.lean` (Copyright (c) 2019 Gabriel Ebner; authors Gabriel Ebner and \
      Marc Huisinga; Apache 2.0) to reject duplicate keys; its notice is kept in the source and \
      the [Apache 2.0 license text](" ++ blobUrl ident "LICENSES/Apache-2.0.txt" ++
          ") is in the repository.\n\n" ++
    "**Verso.** This site is generated with [Verso](https://github.com/leanprover/verso) by the \
      Lean FRO and contributors (Apache 2.0), pinned at revision `" ++ ident.versoRevision ++
          "` ([license](https://github.com/leanprover/verso/blob/" ++ ident.versoRevision ++
              "/LICENSE)). Verso's stylesheets and its search and table-of-contents scripts are \
                served with every page; the site adds its own theme layer on top (a stylesheet and \
                a small script for the light, dark and system colour themes). The separation of \
                documentation and example toolchains follows David Thrane Christiansen's \
                [package-docs \
                template](https://github.com/leanprover/verso-templates/tree/76c9edf5a70f14d272af0f\
                0f354ec833ac22c350/package-docs); no template text is copied. Verso bundles the \
                third-party JavaScript components listed below with their licenses. Pages also \
                load the [marked](https://github.com/markedjs/marked) Markdown library (MIT) from \
                the jsDelivr CDN, as Verso configures by default.\n\n" ++
    "**con-leche.** The closed typed rule registry, its canonical metadata, the complete, \
      request-indexed acceptance design and the proved equality of executed decisions with their \
      reference definitions follow ideas from \
      [con-leche](https://github.com/leanprover/con-leche/tree/c431b1ca1b7a93486dd3e0440d3ee82abe90\
      ccd0) by Joachim Breitner and contributors (Lean FRO), in particular `Kernel/PropWhen.lean`, \
      `Cached/Installed.lean` and `Frontend/Scan/Equiv.lean`. No con-leche code or proof is \
      copied, and con-leche's theorems are not claimed for Regula. con-leche did not design this \
      site.\n\n" ++
    "**Rule-page structure.** The page layout of cause, rationale, fix, configuration, examples \
      and limitations follows [Microsoft's CA1416 code-analysis rule \
      page](https://learn.microsoft.com/en-us/dotnet/fundamentals/code-analysis/quality-rules/ca141\
      6) as one illustrative reference; no .NET content is used, and no affiliation with or \
      endorsement by Microsoft is implied. Other linters (Clippy, Roslyn, ESLint, Ruff, Pyrefly, \
      HLint) informed the design.\n\n" ++
    "**Mathlib.** The `regula` package that projects require imports only Lean's core libraries and \
      requires no other package. The checker repository's Mathlib-dependent package (the \
      standard's Mathlib examples) and this site depend on \
      [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache 2.0) and so on \
      [Batteries](https://github.com/leanprover-community/batteries) (Apache 2.0), which Mathlib \
      requires.\n\n" ++
    "Crediting a project does not imply its endorsement of Regula. The complete attribution \
      account is in the " ++ "[design-influences guide](" ++
          blobUrl ident "docs/guides/design-influences.md" ++ ").\n\n" ++
    "{licenseInfo}\n"

end Regula.Site
