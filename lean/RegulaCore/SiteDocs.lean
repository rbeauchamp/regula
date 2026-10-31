import RegulaCore.SitePage
import RegulaCore.Verdict

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

## Boundaries

Links to repository documents point at the build revision on GitHub; whether GitHub serves
them is outside this module. The versions text describes the publishing workflow in
`.github/workflows/ci.yml`; that the workflow behaves so is an operational observation.
-/

namespace Regula.Site

open Regula.Review (Residual Trusted)

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

/-- The site's home page (the edition root): what Regula rejects, in the words of the root
`README.md` (`summary`), and where a newcomer starts, then the four things a reader comes to do. -/
def homePage (ident : Identity) : Except String String := do
  let notice ← htmlBlock (pageAnchor "regula" ++ editionHtml ident)
  let doc (path text : String) := "[" ++ text ++ "](" ++ blobUrl ident path ++ ")"
  return header ["Generated.Rules", "Generated.Enforcement", "Generated.Coverage",
      "RegulaStandard", "Generated.Versions", "Generated.Credits"]
      "Regula rule reference" "regula" none ++
    notice ++ "\n" ++
    "**Regula.** " ++ summary ++ " This site is the reference of the Regula edition above: a page \
      for each rule, and the standard that the rules come from. **New here?** " ++
        doc "README.md#try-it" "Try it" ++ " on one module, then " ++
        doc "README.md#add-it-to-your-project" "add it to your project" ++ ".\n\n" ++
    "1. **Look up a rule.** Each finding names a rule ID. In the terminal, the first finding of each \
      rule in a run links the page of the rule, and later findings of that rule refer to it. The \
      editor and the JSON report link the page with each finding. A rule page starts with the \
      problem, the fix and an example that the checker rejects. Open the [rule index](rules/), or \
      push `/` to search.\n" ++
    "2. **Adopt Regula.** The " ++ doc "docs/guides/adoption.md" "adoption guide" ++
      " tells how to install and run Regula, in the terminal, in the editor and in CI.\n" ++
    "3. **Review a pass.** A pass is mechanical. Each rule page tells what the check shows and \
      which review stays with you. [How rules are enforced](enforcement/) and \
      [checklist coverage](coverage/) give the details.\n" ++
    "4. **Challenge a rule.** Each rule page gives the reason for the rule, its clauses in the \
      [standard](standard/) and the source of its check. To dispute a rule, \
      [open an issue](" ++ repository ++ "/issues).\n\n" ++
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

/-- The `lake lint` exit codes of Regula's checker (`Regula.Closed.Verdict.exitCodes`). -/
def exitCodesText : String := Regula.Closed.Verdict.exitCodes

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
      result FAIL. A build that Regula's checker cannot load, or an input that does not have the \
      closed form, makes it INCOMPLETE, never a pass. Neither is accepted. `lake lint` exits with " ++
      exitCodesText ++ ".\n\n" ++
    subsection "enforcement-options" "No local exception" ++
    "No source option, attribute or command-line flag makes a rule pass on a claimed surface. The \
      checker reads no option that a source file sets: it reads the declarations Lean loads from \
      the finished build, Lake's targets and modules, and the claim. Hiding a diagnostic does not \
      establish the property it checks. " ++ Prose.relativeCitation .decisionContract ++ " checks \
      the functions registered with `Regula.RegisteredDecision`; removing a registration changes the \
      reviewed claim, not only its result.\n\n" ++
    subsection "enforcement-commands" "Where rules run" ++
    "Project enforcement runs through `lake lint`, which runs Regula's checker on the finished \
      build of the project. Build the claimed targets with `lake build --wfail` first: a module \
      without its compiled files makes the run INCOMPLETE. Lean's own tools decide two rules: " ++
      Prose.relativeCitation .sourceBuild ++ " is `lake build --wfail`, and " ++
      Prose.relativeCitation .admission ++ " is `lake check`. See the " ++
        "[adoption guide](" ++ blobUrl ident "docs/guides/adoption.md" ++ ").\n\n" ++
    subsection "enforcement-message" "How a finding reads" ++
    "Each finding is one line: the rule ID, the constant, module or target it reports, the \
      detail, and the rule's page in the reference. `lake exe regula explain <ID>` prints the full \
      rule offline.\n\n" ++
    subsection "enforcement-obligations" "Open review obligations" ++
    "A pass leaves every review obligation below open, whatever rules it checked. Each rule page \
      names the obligations its own result leaves open, and [checklist coverage](coverage/) the \
      checklist rows whose review each carries.\n\n" ++
    obligations ++ "\n" ++
    subsection "enforcement-trusted" "Trusted mechanisms" ++
    "A pass also relies on these trusted mechanisms, which no rule verifies:\n\n" ++ trusted ++
      "\n" ++
    subsection "enforcement-examples" "Rule examples" ++
    "Each rule page shows the rule's example pair as the registry holds it. No run of the checker \
      produced it: the specification of the smaller Regula states the cases each rule decides.\n\n"

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
      ", ".intercalate (releases.reverse.map fun r =>
        "<a href=\"" ++ escape (basePath ++ (Edition.release r.version).root) ++ "\">" ++
            escape r.version.spelling ++ "</a> for Lean " ++ escape r.toolchain.spelling)) ++
        "</dd>" ++
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
      page there.\n" ++
    "* An address below " ++
    " or ".intercalate (stableRoots.map fun r => "`" ++ stableUrl r ++ "`") ++
    " is a stable address. It names no version and opens the same page of the version that `" ++
    siteBase ++ "` opens. It does not keep a fragment.\n\n" ++
    "An address that names a version never redirects and never changes its meaning: `dev/` is \
      always the development version, and `v/<version>/` is always the copy of that release. \
      While a release exists, a stable address opens the same page of the latest release: its \
      target moves at each release, and it has no page for a rule that no release has. To cite \
      a rule as one release has it, use the address of that release.\n\n" ++
    "A route that is not published shows the site's not-available page, which never redirects \
      to other rules. Rule IDs are never reused for a changed rule; a retired rule keeps a page \
      that says so.\n"

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
      linter's strict JSON parser adapts the string, number and container parsers of Lean's \
      `Lean/Data/Json/Parser.lean` (Copyright (c) 2019 Gabriel Ebner; authors Gabriel Ebner and \
      Marc Huisinga; Apache 2.0), made total and rejecting duplicate keys, and restates the \
      whitespace and literal parsing of `Std/Internal/Parsec/String.lean` (Copyright (c) 2021 \
      Microsoft Corporation; authors Dany Fabian and Henrik Böving; Apache 2.0); its compact \
      printer adapts `Lean/Data/Json/Printer.lean` (Copyright (c) 2019 Gabriel Ebner; authors \
      Gabriel Ebner, Marc Huisinga and Wojciech Nawrocki; Apache 2.0). Their notices are kept in \
      the source and the [Apache 2.0 license text](" ++ blobUrl ident "LICENSES/Apache-2.0.txt" ++
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
      requires no other package, and the standard's examples and this site import no Mathlib \
      module.\n\n" ++
    "Crediting a project does not imply its endorsement of Regula. The complete attribution \
      account is in the " ++ "[design-influences guide](" ++
          blobUrl ident "docs/guides/design-influences.md" ++ ").\n\n" ++
    "{licenseInfo}\n"

end Regula.Site
