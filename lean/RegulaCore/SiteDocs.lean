import RegulaCore.SitePage

/-! # Rule-reference manual structure

Pure construction of the generated Verso manual around the rule pages: the home page, the
rule index part that includes every rule page, the versions-and-evidence page and the
credits page.

## Main declarations

- `ruleModule`, `ruleModules`, `ruleModules_nodup`: the generated Verso module of each rule,
  one per registry entry.
- `homePage`, `indexPage`, `versionsPage`, `creditsPage`: the remaining generated modules.
- `EvidenceSummary`: the per-rule evidence line shown on the versions page.

## Boundaries

Links to repository documents point at the build revision on GitHub; whether GitHub serves
them is outside this module. The version policy text describes the publishing workflow in
`.github/workflows/ci.yml`; that the workflow behaves so is an operational observation.
-/

namespace Regula.Site

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
    (split : Bool := true) : String :=
  "import VersoManual\nimport RegulaSite\n" ++ String.join
      (imports.map fun m => "import " ++ m ++ "\n") ++
  "open Verso.Genre Manual RegulaSite\n\n#doc (Manual) \"" ++ title ++ "\" =>\n%%%\ntag := \"" ++
      tag ++ "\"\n" ++
  (match file with | some f => "file := \"" ++ f ++ "\"\n" | none => "") ++ "number := false\n" ++
  (if split then "" else "htmlSplit := .never\n") ++ "%%%\n\n"

/-- The site's home page (the edition root): its purpose in one line, then the four things a
reader comes to do, in order. -/
def homePage (ident : Identity) : Except String String := do
  let notice ← htmlBlock (pageAnchor "regula" ++ editionHtml ident "")
  let doc (path text : String) := "[" ++ text ++ "](" ++ blobUrl ident path ++ ")"
  return header ["Generated.Rules", "RegulaStandard", "Generated.Versions", "Generated.Credits"]
      "Regula rule reference" "regula" none ++
    notice ++ "\n" ++
    "Regula is a strict linter for Lean 4. This reference shows exactly what each of its rules \
      holds your agents' code to.\n\n" ++
    "1. **Look up a rule.** Every finding names a rule ID such as `RG1002` (editor code \
      `Regula.RG1002`) and ends with the URL of its page here, such as `" ++ devUrl .proofHole ++
          "`; the editor's *View explanation* link opens the same page. A rule page starts with \
            what is wrong, what to do and a checked example. Open the [rule index](rules/), or \
            press `/` to search.\n" ++
    "2. **Review a Regula pass.** A finding is a violation, which makes the result FAIL, or \
      incomplete, which makes it INCOMPLETE because required evidence is missing; neither is \
      accepted. A pass is mechanical: under *What a passing result establishes*, each rule page \
      states what the check establishes and which review obligations stay with you. " ++
          doc "docs/guides/rule-coverage.md" "Rule coverage" ++ " lists every obligation.\n" ++
    "3. **Decide whether to adopt.** The [rule index](rules/) lists all " ++
        toString RuleId.all.length ++ " rules. Each is strict: a violation fails the result, and \
          missing evidence never passes. The " ++ doc "docs/guides/adoption.md" "adoption guide" ++
              " covers installation, `lake lint`, editor feedback and CI; " ++
      "[the standard](standard/) and its [compliance checklist](standard/9-compliance-audit/) \
        define what the rules enforce; every Lean example of the standard is elaborated when this \
        site is built.\n" ++
    "4. **Challenge a rule.** Each rule page gives the rule's rationale, its normative clauses and \
      its detector sources at the commit the page was built from. To dispute a rule or report a \
      wrong result, [open an issue](" ++ repository ++ "/issues).\n\n" ++
    "{include Generated.Rules}\n\n{include RegulaStandard}\n\n{include \
      Generated.Versions}\n\n{include Generated.Credits}\n"

/-- The rule index part, which includes every rule page. -/
def indexPage (ident : Identity) : Except String String := do
  let notice ← htmlBlock (pageAnchor "rules" ++ editionHtml ident "rules/")
  let table ← htmlBlock indexHtml
  return header ruleModules "Rule index" "rules" (some "rules") ++ notice ++ "\n" ++
    "Every rule the linter can emit, generated from its typed registry. The filters work without \
      JavaScript.\n\n" ++
    table ++ "\n" ++ String.join (ruleModules.map fun m => "{include " ++ m ++ "}\n\n")

/-- One rule's evidence line on the versions page. -/
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

private def evidenceRow (e : EvidenceSummary) : String :=
  "<tr><th scope=\"row\"><a href=\"" ++ e.rule.route ++ "\"><code>" ++ e.rule.spelling ++
      "</code></a></th><td>" ++
  escape e.kind ++ "</td><td><code>" ++ escape e.violationStatus ++ "</code></td><td><code>" ++
      escape e.fixedStatus ++
  "</code></td><td>" ++ escape (String.intercalate ", " (e.emitted.map RuleId.spelling)) ++
      "</td><td>" ++ escape e.shard ++ "</td></tr>"

/-- The versions-and-evidence page. -/
def versionsPage (ident : Identity) (evidence : List EvidenceSummary) : Except String String := do
  let notice ← htmlBlock (pageAnchor "versions" ++ editionHtml ident "versions/")
  let identity ← htmlBlock ("<dl class=\"regula-facts\">" ++
    "<dt>Commit</dt><dd><a href=\"" ++ escape (treeUrl ident) ++ "\"><code>" ++
        escape ident.revision.val ++ "</code></a></dd>" ++
    "<dt>Lean toolchain (linter and examples)</dt><dd><code>" ++ escape ident.toolchain ++
        "</code></dd>" ++
    "<dt>Linter version</dt><dd><code>" ++ escape ident.producerVersion ++
        "</code> (no released package)</dd>" ++
    "<dt>Verso revision</dt><dd><code>" ++ escape ident.versoRevision ++ "</code></dd>" ++
    "<dt>Rules</dt><dd>" ++ toString RuleId.all.length ++ " registered, " ++
        toString evidence.length ++ " with checked examples</dd>" ++
    "</dl>")
  let table ← htmlBlock
      ("<div class=\"regula-scroll\" role=\"region\" aria-label=\"Checked rule examples\" \
        tabindex=\"0\"><table class=\"regula-rules\"><caption>Checked rule examples of this \
        build</caption><thead><tr>" ++
    "<th scope=\"col\">Rule</th><th scope=\"col\">Example kind</th><th scope=\"col\">Violating \
      run</th><th scope=\"col\">Corrected run</th>" ++
    "<th scope=\"col\">Emitted rule IDs</th><th scope=\"col\">Corpus \
      shard</th></tr></thead><tbody>" ++
    String.join (evidence.map evidenceRow) ++ "</tbody></table></div>")
  return header [] "Versions and evidence" "versions" (some "versions") (split := false) ++
      notice ++ "\n" ++ identity ++ "\n" ++
    "# Routes\n%%%\ntag := \"versions-routes\"\nnumber := false\n%%%\n\n" ++
    "* `" ++ siteBase ++ "dev/rules/<ID>/` is the development explanation. It always shows the \
      most recent successfully deployed revision of `main`; the linter's diagnostics link \
      here.\n" ++
    "* `" ++ siteBase ++ "rev/<commit>/rules/<ID>/` is the snapshot of one published commit. Each \
      deployment publishes the snapshot of its own commit and every earlier published snapshot, \
      byte for byte: a snapshot is archived before it is deployed, the archive is append-only, and \
      a deployment must contain every archived snapshot.\n" ++
    "* `" ++ siteBase ++ "v/<version>/rules/<ID>/` is reserved for immutable pages of released \
      packages. No package has been released, so no such page exists.\n\n" ++
    "A route that is not published shows the site's not-available page, which names the source of \
      every revision on GitHub. It never redirects to the latest rules: an old link cannot \
      silently acquire changed semantics. Rule IDs are never reused for a changed rule; a retired \
      rule keeps a page that says so.\n\n" ++
    "# Evidence\n%%%\ntag := \"versions-evidence\"\nnumber := false\n%%%\n\n" ++
    "Every example on this site was produced for this exact commit by the rule-example corpus \
      campaign, admitted by the rule-example qualifier (whose admission relations are proved; \
      capture and process authenticity are trusted), and checked against the commit's checker, \
      corpus and configuration sources before the site was generated. The site build refuses \
      stale, incomplete or partial evidence.\n\n" ++
    table ++ "\n" ++
    "A diagnostic demonstration shows an INCOMPLETE result by design; it is not accepted negative \
      evidence. The corpus campaign is scoped qualification of the detectors for these inputs, not \
      a proof that the detectors are correct for every input.\n\n" ++
    "# Hosting limits\n%%%\ntag := \"versions-hosting\"\nnumber := false\n%%%\n\n" ++
    "The site is a static GitHub Pages project site. It uses no cookies, accounts or analytics. \
      Search and the page table of contents use Verso's JavaScript, the colour-theme control uses \
      the site's own script (the choice is kept in the browser's local storage, never sent \
      anywhere), and pages load one library from the jsDelivr CDN (see the credits); every \
      explanation, link and the rule catalogue work without JavaScript, with the colours following \
      the operating system's light or dark setting. A deployment can lag `main` while checks run \
      or after they fail; each page states the commit it was built from. Every published snapshot \
      is kept, so the site grows with each deployment; the build refuses an artifact larger \
      than " ++ toString (artifactBudget / 1000000) ++ " MB, below GitHub Pages' 1 GB limit on a \
      published site. Removing snapshots would change what their routes mean and needs a separate \
      decision.\n"

/-- The credits and licenses page. -/
def creditsPage (ident : Identity) : Except String String := do
  let notice ← htmlBlock (pageAnchor "credits" ++ editionHtml ident "credits/")
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
      endorsement by Microsoft is implied. Other linters' references (Clippy, ESLint, Ruff, HLint) \
      informed the design as documented in the " ++
    "[ecosystem study](" ++ blobUrl ident "docs/guides/ecosystem-design.md" ++ ").\n\n" ++
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
