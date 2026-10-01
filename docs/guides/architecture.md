# Architecture

How Regula is built. One typed rule registry drives the checker, the editor linter, the
`lake lint` driver, the offline `regula` command and the rule-reference site, so every surface
shows the same rule. The [standard](https://rbeauchamp.github.io/regula/dev/standard/) owns
normative meaning; this guide owns the implementation contract. What each part proves, observes
or trusts is in [proofs and boundaries](proofs-and-boundaries.md).

## Packages and libraries

The root `regula` package, the one adopters require, needs nothing beyond the Lean toolchain and
imports no Mathlib. Its libraries (`lakefile.lean`, `foundation_manifest.json`):

| Library | Role | Claim |
| --- | --- | --- |
| `RegulaPolicy` | Pure policy: domain types, admission, declaration/execution decisions, the acceptance plan and its theorems. Imports only Init, Std, `Lean.PrivateName` (for generated native-axiom names) and the import-free `Regula.Contract`. | Claimed, Standard-Logical |
| `RegulaCore` | The rule registry (`RuleId`, `Rule`, `Guide`), the pure projections the checker executes (`Policy`, `Coordinates`, `Source`, `Assembly`, `EditorPolicy`, `Lint`, `Account`), agent guidance (`Feedback`, `Guidance`), project setup (`Setup`) and the site's pure decisions (`Edition`, `Site*`). Imports the policy library, never the reverse, and Lean's `Lean.Data.Position` but not `Lean.Data.Lsp.Utf16`, whose closure contains `Lean.Environment`. | Claimed |
| `RegulaQualification` | Pure observation requirements and checked contracts for qualification campaigns, not process launchers; testing requirements are not production policy, so they belong neither in `RegulaPolicy` nor in the mathematical `Audit` examples. | Claimed |
| `RegulaVerification`, `RegulaProvision` | Toolchain-only acceptance runner and local provisioning. | Claimed |
| `AuditApp` (with standalone root `Main`) | A complete application whose admission, update and composition contracts are proved about the definitions its executable runs. | Claimed |
| `Regula` | The operational checker: Lake loading, probes, workers, transport, CLI and project setup, linter hooks, qualification drivers, the site builder and the release steps. | Excluded; self-audited ([contributing](contributing.md#repository-conformance)) |
| `Fixtures` | Isolated positive controls and intended-failure mutations. | Excluded; never imported by a claimed surface |

The `regula_audit` package in [`audit/`](../../audit/lakefile.lean) holds everything that
imports Mathlib (the `Audit` library of the standard's examples) and requires the root package by
relative path, as a Mathlib adopter does. The Verso package in [`website/`](../../website/)
renders the standard and the rule reference; it requires both packages only so the standard's
examples can import their modules, each in its own helper process.

Executables: `axiomGate` (declaration, execution and documentation audits), `lint` (the
`lake lint` driver), `regula` (project setup and offline guidance), `docFenceAudit`,
`freshChecker` (optional serialized-graph check), `checkerSelftest`, `qualify`, `ruleExamples`
and `ruleExampleQualification` (qualification), `site` (the rule reference) and `auditApp`.

## The rule registry

`RuleId` ([`RegulaCore.RuleId`](../../lean/RegulaCore/RuleId.lean)) is a closed inductive type
with 22 constructors; `spelling`, `parse?`, `all` and `route` are the executed definitions, and a
route (`rules/<ID>/`) cannot be set independently. `descriptor : (id : RuleId) → RuleDescriptor id`
([`RegulaCore.Rule`](../../lean/RegulaCore/Rule.lean)) is exhaustive, so there is no runtime
registration table whose missing entries silently disappear. A descriptor carries title,
category, scope, evidence kind, normative clauses (the closed `Clause` type of
[`RegulaCore.Standard`](../../lean/RegulaCore/Standard.lean)), applicability, strict default,
supported evidence modes and lifecycle. Every registered rule is enforced by the checker. Its
message form is not a field but `messageForm id`, the same `messageLine` the checker renders.

Every descriptor also carries the agent-facing guidance, with no defaults, so a rule without it
does not compile: a one-line `requirement`, a short `rationale`, a one-line imperative `remedy`,
at least one compliant rewrite and the checked `examples` pair. The pair is the exact bytes of
`examples/rules/<ID>/Fixed.<ext>` and `Violation.<ext>`, embedded with `include_str`; the
`RegulaCore` library `needs` the corpus directory, so editing an example rebuilds the registry,
and `RegistryChecks` rereads every file and refuses a mismatch. A pair's `audience` is `adopter`
(shown to agents as written) or `qualification` (RG1003's stand-in dependency and RG2001's runner
requests, which agent-facing output replaces with the pair's `correction` sentence).
`RuleDescriptor.wellFormed` (nonempty fields within byte budgets, one-line requirement and
remedy, distinct examples) is checked by compiled evaluation over `RuleId.all` when
`RegulaCore.Guidance` builds. Every finding (`RegulaCore.Feedback`), the `regula` command, the
agent briefing, the registry and result exports and the site render these fields; none keeps a
copy. [`RegulaCore.Guide`](../../lean/RegulaCore/Guide.lean) holds each rule's explanation (one
exhaustive definition over `RuleId`), including the checklist rows it contributes to and the
review obligations it leaves open.

To add or change a rule:

1. Establish its exact Lean predicate and its place in the [coverage](#coverage-of-the-standard).
2. Add the constructor, spelling and parser branch, descriptor, guide entry and dependent payload;
   update the closed inventory (`RuleId.all`) and its proofs.
3. Add the detector and the adapter that invokes it before enabling its modes; add the example
   pair and its `corpus.json` entry; regenerate the dogfooded skill
   (`lake exe regula skill > .agents/skills/regula/SKILL.md`).
4. Preserve existing qualification controls and qualify the changed admission and output paths
   (standard [§7.8](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#78-qualify-checker-implementations-with-independent-mutations)).

Keep detectors separate from adapters, and construct `Finding` through the sole registry,
preserving its original `Name`, supported mode, impact and genuine location. Do not rerun a
complete imported environment scan per command, create a second policy implementation or use
parser regexes for ownership; add modes only for actual producer interfaces and document their
partial scope.

Metadata text, a nonempty mode list and a green build are not proofs of detector adequacy, and a
lifecycle or predicate change still requires semantic review. Never reuse an ID for a changed
predicate. A compatible clarification retains the rule's identity and records the applicable
implementation version. `Lifecycle.active` records the release that introduced the rule.
`Lifecycle.retired` keeps the descriptor as a tombstone with its introduction, retirement and
optional replacement, which carries a proof that it is a different ID. Every rule states its
lifecycle (the field has no default), and each lifecycle position is a `Build`: a new rule is
`.active .unreleased`, and a newly retired one records `.unreleased` as its retirement, until the
next release, whose release pull request the Release workflow stamps with it
([release](contributing.md#release)). `release_attributes_rules` proves that when `installed` is
a release no lifecycle position of any rule is `.unreleased`, so a release commit that misses one
does not build, `lifecycle_listed` that every release a lifecycle names is in `versions`, and
`introduced_startsLine` that no patch release introduces a rule.
Checklist rows of the standard are not diagnostic IDs. No rule bans `Float`, `IO`, local mutation
syntax, classical erased proofs, noncomputable mathematical definitions or arbitrary naming
styles.

## Findings and locations

`Diagnostic id` ([`Regula.Diagnostic`](../../lean/Regula/Diagnostic.lean)) carries `Payload id`
(structural declaration names, execution roots or context arguments), a primary location, related
locations, evidence mode, claim context, strict impact and display severity; collections store
the dependent pair `Finding`, so no invalid rule/payload combination exists. `makeDiagnostic`
requires the mode to be one the descriptor supports. Strict impact is `violation` or
`incomplete`; display severity cannot change it or the acceptance decision. All rules are strict
errors when applicable (`descriptor_severity_error`). Rules keep only the technical exceptions of
standard §§7.4–7.6: authenticated generated helpers, separately classified teaching native
proofs, and the origin-checked boundaries of the toolchain's trusted base. The profile and
execution parsers stay the configuration authority: claim text in a diagnostic describes that
context and is not an independent policy decision.

`Location` is a source range (exact text with byte offsets for full and selection ranges), a
module, or a project/configuration scope. `admitSource` (claimed `RegulaCore.Source`) checks
bounds, character boundaries, ordering and containment; a declaration with a recorded range is
located at it, one Lean generated without a range at the range of the declaration its finding is
attributed to, where the finding carries the attribution (`Findings.findingLocation`), a
declaration without a recorded range otherwise falls back to module attribution, and an
inconsistent supplied range fails rather than acquiring an invented location. `sourceFromReport`
additionally requires the recorded code-point and UTF-16 coordinates to agree with that text.
Report lines are one-based and columns count Unicode code points; `startUtf16` and `endUtf16` are
zero-based UTF-16 columns within their lines, computed with Lean's
`leanPosToLspPos`. Native messages use Lean code-point positions, and the same validated
selection supplies both the JSON LSP range and the native position. Fence declaration findings
use labelled virtual snippet locations whose snapshot is the exact verbatim snippet, never
Markdown coordinates; aggregate fence errors keep their document and fence origin in context
attribution. Filesystem paths stay native diagnostic filenames; project reports may keep
disposable source-copy paths as evidence beside the actual source text, without asserting that
those paths stay live after the run, and no textual path substitution is applied. Names are
written by `Regula.StructuralName` as the text Lean prints only where Lean's parser reads that text
back as the same name, and otherwise structurally (tagged string and numeric components,
innermost first; `printedNameJson_roundtrip`), and display-only worker records cannot supply a
declaration diagnostic. A source location's text is its `sourceText` member; a result file
stores each text once and the member is then its index, so `parseDiagnostic` reads the document
`SourceTexts.expand` returns ([output schemas](#output-schemas)). `parseDiagnostic` reconstructs
the indexed payload and admitted
source location and compares the input with its canonical re-encoding, refusing unknown fields,
unsupported modes and IDs, invalid coordinates and altered redundant text or help URLs; the
proved name, ID and mode codec laws are not a proof of Lean's JSON parser, `FileMap` or the
complete diagnostic decoder.

## Evidence modes and results

Modes are `editorSnapshot`, `incrementalProject`, `freshProject`, `freshFile` and
`documentationExample`; `serializedGraph` is a separate claim. A result carries its exact scope,
source and configuration identity, toolchain and dependency identity, stages, findings and
unresolved obligations. Status is `completed`, `rejected`, `incomplete` or `classified`
(no-profile and compiler-trusting file runs). `completed` means the scoped mechanical checks
completed and were accepted, never whole-standard conformance; the report account behind it and
its proof obligations are in [proofs and boundaries](proofs-and-boundaries.md#the-acceptance-boundary).
Internal failures are incomplete, never fabricated violations or empty successes, and an editor
snapshot never becomes a project result. Source compilation is distinct from later inspection: a
normal pinned-compiler exit with a source-located error or warning can establish an emitted
diagnostic, while crashes, termination and inspection exceptions are incomplete, and flattened
Lake build failures stay incomplete with the original text kept; neither permits acceptance.
RG2001 reports setup failures in fresh, incremental and file audits, and a failed inspection
worker with the worker's own error text; in a project or file audit, an inspected environment
that loads a root-package module outside every library is refused as RG2004, a violation, naming
the module and its importers, while a documentation audit leaves that fence incomplete;
documentation-audit setup failures print `FAIL` without a finding. Combined project
and documentation output stays incomplete while its documentation stage is pending, and
configuration that has not been admitted has null `scope` and `mode` and an incomplete status.
Recognizable output destinations are invalidated before argument parsing where their paths can
be resolved: absolute destinations first, without requiring valid project configuration, and
relative destinations once the project root is resolved. Callers must require the current
invocation's successful completion, never reuse a previous report after a failed command.

## Output schemas

```sh
lake exe axiomGate --registry-out tmp/registry.json
lake exe axiomGate --validate-registry tmp/registry.json
lake exe axiomGate --file Example.lean --claim standard-logical --json-out tmp/result.json
lake exe axiomGate --with-docs --json-out tmp/result.json
```

Each export is versioned on its own: the surface manifest is schema 2, the registry schema 4, the
result schema 8, the worker packet schema 1, the rule-example corpus export schema 1, the
acceptance link schema 1 and the site's `build.json` schema 2. Registry and result envelopes carry
`schemaVersion`, `producerVersion`, `toolchain` and `sourceRevision` from
`Regula.Checker.Producer.identity`: `producerVersion` is the installed release's spelling
(`unreleased` for an unreleased build), and `sourceRevision` is the checker source's Git revision,
captured when `Regula.Checker.Producer` is elaborated with Git anchored to the checker package's
own directory and suffixed `:unreleased-worktree` when that worktree had changes. Both are build
metadata, not authenticated binary identity.

- **Registry, schema 4:** the canonical `rules`, whose `normativeClauses` are
  `{section, title, source, url}` objects (the cited section's number, heading, Verso source path
  and URL in the installed build's edition). `parseDescriptor` compares input with canonical
  re-encoding, refusing unknown or missing fields, changed routes and stale lifecycle data.
  Registry admission rejects duplicate external IDs, missing clauses, pages or examples, unknown
  JSON fields or versions, and invalid lifecycle references.
- **Result, schema 8:** `scope`, `mode`, `status`, `stages` (the stages
  `RegulaPolicy.requiredStages` requires for the mode, plus the documentation stages of a
  `--with-docs` run), `stagesCompleted`, `complete`, `stagesNotRun`, `diagnostics` (each with its
  `remedy`, in run order), `rules` (the guidance of every rule that fired, once each, in registry
  order) and `unresolved`. A writer records the stages its run completed: a context failure the
  stages its call site finished, and a finished audit every stage; an empty documentation scan
  leaves the documentation stages unrecorded. `stagesCompleted` is the recorded stages without
  each stage a stopping finding (an incomplete finding, or an RG2002 or RG2003 refusal) left
  unfinished and every later one; `complete` holds exactly when no required stage is missing.
  One function, `ResultProtocol.guidanceFields`, derives these members for writer and reader,
  and `ResultProtocol.admitGuidance` re-derives them on admission. The
  [adoption guide](adoption.md#machine-readable-report) documents the members for adopters.
- **Source texts:** since schema 7 a result file holds each distinct source text once, in its
  top-level `sourceTexts`, and every `sourceText` member (a source location; a `sourceAccount`
  entry; in `scope`, a project's `sources`, a file audit's own text, a documentation
  rule-example's `documents`, and the frontend transcripts, source bindings and histories; in
  `acceptance` and `documentationAcceptance`, the snapshot's sources and an environment's
  `fileSource`) is the index of its text there. Checker code builds and reads the
  document with the text in each member and `sourceTexts` `null`; `ResultProtocol.writeDocument`
  writes its `SourceTexts.intern`, and each reader that decodes a diagnostic or reads a text
  (`ResultProtocol.readDocument`, the qualification drivers' `readResult`) takes the file through
  `SourceTexts.expand`, which refuses a list that is not distinct strings and an index outside
  it; a rule-example record keeps that expanded document. `SourceTexts.expand_intern` proves
  `expand` returns exactly the document `intern` was given, `intern_table` that the written list
  has no text twice, exactly the texts of the document's `sourceText` members, and that every
  such member of the written document is an index, and `intern_isOk_iff` that `intern` writes
  exactly the documents with one `null` `sourceTexts` member and string `sourceText` members.
  These are laws of `Json` values, including malformed object trees; they are not laws of JSON
  text or of Lean's `partial` `Json` equality. So the text a file's findings share is written
  once: the written size is that of the distinct texts plus the rest of the document, which
  carries one index for each member. That is an argument from the construction, not a theorem
  about byte counts, and it bounds source text only: a string elsewhere in the document is
  written where it occurs. Project configuration text stays inline in `request`, `effective` and
  `scope.configuration`.
- **Execution accounts:** since schema 8 a result file holds each environment report's
  `execution` in a shared form: `names` (every name its roots reach, in the order of
  `canonicalNames`), `modules` and `nameModules` (each name's module), the seven edge channels
  (`compilerEdges`, `logicalEdges`, `candidateEdges`, `historyEdges`, `currentReplacementEdges`,
  `activeSimplificationEdges`, `helperEdges`) as pairs of name indices, `boundaries` (each
  boundary record once, with the index of its name as `node`), `unavailableCode`, and `roots`,
  one entry per root. Checker code builds and reads the document with `execution` as an array of
  complete root accounts (name, module, boundaries, unresolved paths, compiler edges and
  closure), as before; `ResultProtocol.writeDocument` writes `SharedExecution.write` of it and
  every reader (`ResultProtocol.readDocument`, the qualification drivers' `readResult`) takes the
  file through `SharedExecution.read`. The reader (`SharedExecution.restore?`,
  `SharedExecution.rebuildRoot`) derives a root's account from its entry: its visits are the walk
  from the root over the edges the collector follows (`SharedExecution.walkLoop`), unless the
  entry lists them; its reached names are the visited ones; each channel's edges are those leaving
  a reached name; its required code is the targets of its compiler edges, and the root if its
  entry says so; its boundaries are its visited names' records in visit order, each with the
  reached names that call it. An entry can also hold a root's account as it is (`explicit`).
  The writer proposes a shared form (`ExecutionShare.proposals`) and keeps it only if the reader
  returns the logical value itself from it, decided by `SharedExecution.same`
  (`same_eq`: a `true` answer is an equality); otherwise it writes the logical value as it is.
  So `SharedExecution.expand_intern` and `read_write` hold for every `Json` value whatever is
  proposed: reading what was written returns exactly the document the writer was given, so the
  checker's and the qualification oracles' theorems about the document they read are theorems
  about the document that was written. The law is about `Json` values; that parsing a file's
  text returns the value that was compressed into it is the JSON implementation's round trip,
  trusted as it was for earlier schemas. That the proposal is kept, and so that the file is
  small, is not a theorem: it holds when the collector's accounts have the form the reader
  derives, which `Probe.executionWalk` is written to produce (it queues names in the order of
  `canonicalNames`), and when a rebuilt account is the same tree as the logical one, for which
  the account codecs and the reader list each object's members in key order, as the JSON parser
  inserts them. The `history` qualification and `RegistryChecks` observe both. The written
  member then holds each reached name, edge and boundary record once per environment and a
  constant-size entry per root, where the logical member repeats them for every root that
  reaches them.
- **Kernel types:** since schema 8 a result file carries a declaration's `type`, the `repr` of
  its kernel type expression, in a report's `declarations` and in a frontend transcript's
  `addedDeclarations` only when the audit is run with `--kernel-types`
  (`ProducerReport.declarationResultJson`, `Frontend.commandResultJson`); `prettyType` is the
  type as Lean prints it. The in-memory report and worker transport always keep `type`, which
  the role decisions compare. The producer qualification runs its controls with
  `--kernel-types`, because its oracle compares the kernel expression, which two different
  types that print alike would not show in `prettyType`.
- **Names:** since schema 6 every Lean name of a result, in `diagnostics`, `scope` and
  `acceptance` alike, and of the producer report it renders, is written one way
  (`RegistryCodec.printedNameJson`): the text Lean prints for it, or, only where Lean's parser does
  not read that text back as the name, its structural components as a JSON array.
  `printedNameJson_roundtrip` proves the reader (`parsePrintedNameJson`) recovers every name,
  `printedNameJson_eq_str_iff` that a name is a string exactly when Lean's parser reads its printed
  text back, and `parsePrintedNameJson_str` that the reader admits a string only as that text.
  Admission reads names back with that reader: producer reports through `Regula.Report`'s
  instances and diagnostics through `DiagnosticCodec.parseDiagnostic`, which also refuses a
  diagnostic unequal to its canonical re-encoding.
- **Attribution:** the collector records, for each declaration, the declaration Lean generated it
  from, one step (`Collect.generatedFrom?`), by trying the closed families of
  `RegulaPolicy.GeneratedFamily` in the order of `GeneratedFamily.all`, each with its own clause of
  the exhaustive match `Collect.generatedBy?`: constructors, projections, recursors (the relation
  Lean's `findDeclarationRanges?` uses), equation lemmas (`Meta.declFromEqLikeName`), reserved
  names (`isReservedName`) and matchers by a mark Lean's generator leaves; a well-founded or
  `partial_fixpoint` definition's `_unary`, `_mutual` or `mutual` and a structural recursion's `_f`
  and `_sunfold` by its equation information; auxiliary declarations `mkAuxDeclName` names under
  `f`, such as `f._proof_n`, when a constituent of `f`'s declaration (its type or value, or, for an
  inductive type, the type, a constructor's type or a field's default value of any type of its
  mutual block, which Lean elaborates under its first type's name), its equation information or
  `f.eq_def`'s statement uses them, or, with the chain running through the recursion helper
  below, `f._unsafe_rec`'s value does, or, with the chain running through it, a declaration named
  under `f` at any depth that is not itself a generated auxiliary declaration (it is not
  auxiliary-named, or it has a recorded declaration range), such as a `where` or `let rec` helper,
  or another such auxiliary declaration with no recorded range that is itself related does, and an
  RPC wrapper or `initialize` action by the extension that records it;
  constructor lemmas and type constructions where the environment shows their generator ran on
  the type (its precondition, under Lean's default options, or the mark it leaves on a sibling it
  generates in the same run); and field defaults by Lean's own lookup
  (`getEffectiveDefaultFnForField?`). A
  compiled recursion helper `f._unsafe_rec`, which the environment ties to `f` only by its name, is
  related to `f` when the admitted scope authorizes it (`Findings.stepOf` over
  `authorizedUnsafeRecHelpers`), and `Findings.helperStep_base` proves `f` is then an audited
  definition in the helper's module with its type, and that Lean's recursion compiler was observed
  to regenerate the helper. No clause rests on a name alone, so an elaborator or macro Lean names
  `«_aux_…»` inside a namespace is not related; and a clause that reads the relation from the
  declaration's name applies only to a declaration with no recorded declaration range, which Lean
  records for what an author writes and not for these generated declarations, so a theorem an
  author names like one of them keeps its own location. The RG1005 rewrite names the families from
  `GeneratedFamily.all` and `GeneratedFamily.text`, and `RegistryChecks` requires the adoption
  guide to quote it verbatim, so the guidance and the guide name exactly the families the checker
  relates; the [enumeration](proofs-and-boundaries.md#generated-declaration-families) records
  every family Lean v4.34.0 generates and why each is related or not. In a declaration-policy
  finding of a project audit, a file audit or a rule example (the rules `Policy.ruleForMember`
  decides), `arguments.sourceDeclaration` is the end of that chain over the audited declarations
  (`Findings.sourceName?`), and `sourceName?_eq_some_iff` proves it is exactly the name the
  recorded relation leads to from the declaration and relates to nothing further: a declaration
  Lean did not generate from another, or one outside the audited declarations. The finding keeps
  the range Lean recorded for its declaration, as for a constructor or a field; without one, it is
  located at the source declaration's range when that has one and its module has a snapshot
  (`Findings.findingLocation`), and its `related` then names the declaration's own module. Other
  declaration findings carry no attribution: a documentation example's, a material-documentation
  one (RG5002, RG5003) and the editor linter's record `null` and their declaration's own location
  (`Findings.declarationLocation`). Which clause records which declaration is Lean's behavior,
  read from its environment, not proved;
  derived instances and the declarations deriving handlers add, such as an enumeration's `ofNat`,
  are not related, since Lean records no such relation. The `lake lint` text prints the RG1005
  findings under one declaration at one location as one block, and a generated declaration with a
  range of its own as its own block under the same declaration
  (`groupFindings`, `groupEntry`, `Finding.sameGroup`; `declarationFinding_groupUnder?` proves such
  a finding groups under the declaration it is attributed to) and folds their lines in its closing
  `FAIL` summary into one count; the JSON keeps them one per declaration, in the same order
  (`groupFindings_flatten`).
- **Scope:** In `axiomGate` and `ruleExamples` results, `scope.configuration` keeps the project
  configuration files in full, as path/optional-text pairs with `null` for an absent file. The
  `freshChecker` `serializedGraph` output has no `scope`, so it carries no configuration text,
  and no consumer reads it there. File `scope.report`, project `scope.surfaces[*].report` (the
  library's environment) and `scope.surfaces[*].executables[*].report` (each claimed
  executable's root, inspected alone) keep the complete observed declaration and execution
  inventories, including trusted boundaries and correspondence evidence; in `axiomGate` results
  `scope.toolchainBase` lists every boundary the toolchain owns once for the whole audit, with
  the environments and roots that reach it; project scope also keeps its source snapshots, Lake
  library inventory and completed stage names. File scope keeps its nullable foundation claim,
  execution claim and exact source even without findings.
- **Acceptance account:** a completed result's `acceptance.account` renders the report account:
  `coverage` (only `freshWholeProject` is whole-project acceptance), `checked` (the theorem
  `RegulaPolicy.accept_iff` and the job count), `contracts` (each RG1007 registration with its
  implementation, rendered requirement and `unresolvedReview` of `R-INTENT` and `R-INVARIANT`),
  per-environment `execution` counts, `fences` by expectation, `trusted` mechanisms and the run's
  `unresolvedReview` identifiers. A completed envelope's `mode` is the account's, and a listed
  identifier names an open obligation, not a completed review.
- **Snapshot rendering:** `acceptance.snapshot` renders the audited sources in full, the
  configuration by URI and each dependency by package, pinned revision and input-scoped `dirty`
  bit (a dirty or path dependency as `{package, revision, dirty: true}`, with no content
  identity). It omits `acceptance.environments[*].importedModules` and the report's `modules`
  and `moduleOrigins` import-closure lists; owned modules remain in `census.modules`. The run
  still freezes and rechecks every captured byte in memory; only the serialization is bounded,
  so a result's size follows the audited project, not its dependencies.
- **Environments:** the rendered `acceptance.environments` array keeps each environment's
  ordinal, module assignment, infrastructure modules, declaration/root/replay inventory and
  optional file binding, not the modules it merely imports. Local job subjects contain that
  ordinal and their local subject, and the common snapshot is rendered once.

- **Worker transport:** a separate protocol with its own version, request identity and
  producer/toolchain binding. Wire results carry observations, never proofs or an accepted flag;
  the parent revalidates and reruns the pure decision.
- **Site artifact:** `axiomGate --validate-site REGISTRY ARTIFACT` admits an object with `required`
  and `emitted` rule-ID arrays and `pages`, each page with `id`, `route` and `checkedExample`. It
  requires the expected producer and registry, unique and complete required pages, canonical
  routes and checked examples, and every emitted ID within the required scope, and refuses unknown
  fields. The site builder supplies the observed inventory and checked-example evidence; the
  validator does not prove filesystem or compiler observations.

## Enforcement paths

- **Editor.** `Regula.Linter` registers Lean command and module linters; no build or external
  process runs in them. Messages carry codes such as `Regula.RG1001`, real ranges and the rule's
  URL, and attach Lean's own `Lean.errorDescriptionWidget` (published with `logMessage`, not
  `logAt`, which would attach a Lean-manual link) so the infoview shows **View explanation**; the
  message text keeps the URL for clients without widgets. The widget's text alternative is empty,
  and `warningAsError` promotes these warnings uniformly. Pinned LSP diagnostics have no
  `codeDescription`, and registering an external error name does not redirect Lean's widget, so
  no Lean fork or project JavaScript is used. `linter.regula` (default true, following
  `linter.all`) and `regula.localFoundation` (`classification-only` by default, or a profile)
  control local feedback only; Lean's `withSetOptionIn` restores scoped `set_option … in` options.
- **`lake lint`.** `lintDriver := "regula/lint"`, in either lakefile format, runs the same
  `axiomGate` project audit, incrementally or with `--fresh`, and maps its recorded result to exit
  codes (claimed `RegulaCore.Lint`). An audit keeps at most one `Lint.Observation` (a later
  record replaces an earlier one), from which its result status, its summary counts by impact
  and the exit code `axiomGate` itself returns are derived (`gateExitCode`), and the driver
  reports the exit code its own audit returned (`classify_gateExitCode`). A standalone
  `axiomGate` run builds without the driver's audit-build marker, so it can record another result
  for the same project.
- **Enforcing build.** The sample's uncached sole-default `policy` target runs `axiomGate
  --build-lint` on plain `lake build`
  (standard [§7.11](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#711-opt-in-enforcing-build-linter)).
- **Project, file and documentation audits.** `axiomGate` (fresh, `--incremental`, `--file`,
  `--with-docs`) and `docFenceAudit`; `freshChecker` for the optional serialized-graph claim.

The checker uses Core, Std and Lean APIs only: `ConstantInfo`, `Lean.collectAxioms`, module
indices, declaration ranges, file maps, elaboration info, Lake's elaborated library arrays and
executable roots, the command and module linter hooks, and the pinned compiler IR. Lean's
environment-linter framework supports local omission, so it cannot establish mandatory coverage.
Upstream linters are reused by requiring them (standard
[§6.7](https://rbeauchamp.github.io/regula/dev/standard/6-code-organization/#67-community-conventions-and-linters)),
not reimplemented as rules. Pin-sensitive interfaces are those of Lean 4.34.0
(`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`), for example
[`FileMap`](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/Lean/Data/Position.lean),
[UTF-16 conversion](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/Lean/Data/Lsp/Utf16.lean),
[command hooks](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/Lean/Elab/Command.lean)
and [`lintDriver`](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/lake/Lake/Config/PackageConfig.lean);
a toolchain upgrade requalifies them. Check the Lean version and commit before pin-sensitive
inspection; the compiler-dependent account is specified in standard §7.6.

## Rule examples

[`examples/rules/<ID>/`](../../examples/rules/) holds each rule's `Violation` and `Fixed` source,
or an unchanged `Example.lean` with a changed dependency (RG1003) or configuration (RG2001,
RG2002, RG2006) pair; RG2006's pair is the package's `lakefile.lean`, to which the run appends the
`require` line of its producer slot, and RG2002's pair is two manifests for one layout, in which
the run gives library `Example` the submodule glob and `lean_exe cli` its root `Example.Cli`
(`Cli.lean`) inside that library. [`corpus.json`](../../examples/rules/corpus.json) fixes each
phase's invocation, evidence mode, expected IDs, subreasons, message patterns, subjects and full
primary locations before execution; its [README](../../examples/rules/README.md) gives the
authoring rules and placeholders. Keep a pair's `correction` sentence and its fixtures in the
same change. The RG5001, RG5002 and RG5003 corrections each preserve exactly
`∀ n : Nat, n = n`, with the same proof and no new assumptions; only documentation is added.

`Website.ExampleExpectation` has exactly four accepted kinds: positive, compiler rejection (one
effective error matching the restricted pattern), policy rejection (the expected findings, none
extra; RG1001's source elaborates and is then rejected) and trusted teaching. The
compiler-rejection pattern and the policy-rejection expected-diagnostic specification are
nonempty; a policy rejection requires completed real checker rejection for the exact source,
configuration and mode, matching the expected rule ID, the subreason where specified, and the
expected primary and related source ranges or explicit module or project location. A source-free
detector keeps its module or project location; an example adapter must not manufacture a source
range. `Website.ExampleBinding` retains an admitted snapshot, mode and typed `ExampleRequest`;
`validateBoundExample` checks binding and completion and the exact diagnostic list before
applying the four-kind policy. RG2001, RG2005 and RG3001 instead have **diagnostic
demonstrations** of unavailable analysis: completed, authentic production of the expected
INCOMPLETE finding with the exact source, configuration, mode, rule, reason and locations,
outside the four kinds, never accepted evidence. A crash, missing response, stale source or
unrelated error is not a demonstration, and no rule can become conforming by expecting its own
unavailability; each corrected counterpart runs its applicable completed positive checks. The
demonstration guarantees (`incomplete_example_refused`, `admitDemonstration_sound` and
`_complete`, `demonstration_completed`, `demonstration_observed_incomplete`,
`demonstration_not_accepted`) depend exactly on `propext`,
`Classical.choice` and `Quot.sound`: Standard-Logical, not Kernel-only. If the initial configuration read fails, the result keeps the original IO
diagnostic as RG2001, incomplete, with an empty source account and a null effective
configuration; it cannot qualify as an example or a demonstration. After that read succeeds,
early terminal failures keep the producer's request and any configuration captured before the
failure.

The runner (`Regula.Qualification.RuleExamples`) copies each phase byte for byte into its own
fresh Core-only adopter workspace (standard §7.8's fresh-workspace form) with empty root build
output and unique result paths, checks source and configuration readback, runs at most five
detector invocations concurrently and consumes evidence in registry and phase order. Each
invocation may launch subprocesses. File
fixtures are separate from the warning-free positive library used to prepare dependencies. The
adapters reuse `SourceBinding.withUnchanged`, typed `SourceAudit` outcomes and the documentation
driver's frozen snapshots and serialize only after snapshot checks complete, so a typed refusal
or process exception cannot become a qualifying example. The producer captures its own parsed
invocation and effective configuration, including absent files and Lake package overrides;
copied configuration paths are compared relative to their recorded roots without rewriting
source or diagnostic identities, a changed effective package override is refused, and neither
configuration relocation nor a combined `--with-docs` request is authorized. The qualifier also
compares the actual effective configuration and the file or per-surface claim and execution with
the request. The campaign applies
`ResultProtocol.admitGuidance` to every result it admits.

An export (corpus schema 1) records the exact sources, commands, original compiler output,
canonical results, expected locations, mode and checker build identity, the exact checker source
bytes before and after the campaign, the admission controls and whether the selection is the
complete corpus; unrun selected rules are never a complete-corpus pass. The qualifier
(`Checker.RuleExampleQualification`) checks the selection against the closed registry, requires
both phases of each selected rule once, and is the single admission of every canonical record;
by `qualify_sound` it refuses, among others, a demonstration relabelled to another rule while
keeping its findings, and a record whose observed sources are not in its bound snapshot, whose
displayed source is stale or whose required source account was dropped. Three refusal controls are admitted individually and must be refused:
`RG1005/WrongClaim`, authentic Standard-Logical output of RG1005's violation refused against its
frozen Kernel-only request; and `RG4004/TrustedControl` and `RG4004/NegativeControl`, a
trusted-teaching fence and a compiler-rejection fence that complete as `classified` and are
refused as a positive documentation correction. The full corpus is 47 productions (44
Fixed/Violation phases plus these 3 controls), 3 individual control admissions and one corpus
admission of every record. These controls qualify the adapters; the universal data predicates
and their proofs remain distinct from observed process behavior. Version fields alone do not
authenticate whole binaries; the producer and filesystem remain trusted.

```sh
lake build axiomGate ruleExamples ruleExampleQualification qualify
lake exe qualify rule-examples --evidence tmp/rule-examples.json
```

`--rules RG1001 RG1002` after the evidence path scopes a development run; `--shard K/N` selects
every rule at corpus position K − 1 modulo N, keeping RG5002 with RG5001 so their shared
fresh-project theorem-type check still runs (`mem_selectRules_shard`,
`mem_selectRules_some_shard`, `rg5001_rg5002_same_shard`). CI runs the two shards through
`./scripts/verify.sh diagnostics rule-examples 1/2` and `2/2`, and the site build admits both
exports again. The `ruleExamples` and `ruleExampleQualification` executables are excluded in the
root manifest solely as operational qualification tooling of the excluded `Regula` library; no
product module or detector is exempted from its applicable qualification. The corpus is
qualification, not acceptance, and no website, editor, serialized-graph or full-project claim
follows from it alone.

## Rule reference site

The site builder (`lake exe site`) generates Verso source from the registry, `RegulaCore.Guide`
and the admitted rule-example exports of the same commit, renders it with the pinned Verso
package, and publishes the standard beside the rule pages. The [website guide](website.md) owns
its sources, guarantees, editions, help links and publication.

## Coverage of the standard

Every normative requirement has a disposition: a rule, proof evidence the standard requires, or
semantic review. The rules and review obligations cover the modules as follows; a row list means
the rows whose review or mechanical check the clauses feed, not that those rows pass.

| Normative clauses | Checklist obligations and treatment |
| --- | --- |
| Introduction (scope, keywords, example convention); module 0 | SCOPE-01–05, THEOREM-01/04/06/09, FOUND-01–05, DOC-03–05. Kernel truth, adequacy and non-vacuity remain distinct. |
| 1.1–1.2 | TYPE-01/02/06, THEOREM-01–05/07, FOUND-01/02, COMP-02. Intrinsic and justified raw-boundary alternatives both remain valid. |
| 1.3–1.6 | SCOPE-02–05, TYPE-02/05, THEOREM-01/07/08, DOC-01/02, DECL-01–04, COMP-01–04. Explicit constrained parameters fall under TYPE-01/02 and THEOREM-01/03. |
| 2.1–2.4 | TYPE-01–06, SCOPE-03, THEOREM-03/07/08. Tags, totalized domains, assumptions, reuse and refinement have distinct obligations. |
| 3.1–3.5 | THEOREM-01–06/10, TYPE-03/05, FOUND-01–05, DOC-01/02. Proof readability and economy recommendations are review guidance, not mandatory tactic or size rules. |
| 3.6–3.8 | COMP-01–04, SCOPE-03/05, THEOREM-01/03/05/07, BUILD-02/03. Metaprogram output validity is not producer correctness; §3.6's contract obligation includes optimizations, which meet the same contract ([performance notes](performance-notes.md) are guidance). |
| 3.9–3.10 | THEOREM-04/08/09, SCOPE-02/03, DOC-02, FOUND-01/02. Conditional and open claims are not rejected for lacking an antecedent witness. |
| 4.1–4.4 | TYPE-01–05, THEOREM-01/02/07/08, SCOPE-02/03. Numeric and mathematical-interface adequacy are specified-domain obligations. |
| 4.5 | FOUND-01–05, BUILD-02, COMP-01. The exact least label is reported separately from the selected maximum and from executable witnesses. |
| 5.1–5.4 | DOC-01/02, THEOREM-01, SCOPE-02. Presence checks are RG5001–RG5003, and RG5001 also checks module-docstring placement; prose fidelity, intent adequacy and readability remain review. |
| 6.1–6.7 | DECL-01/04 (acyclic imports and actual elaboration), DOC-01, TYPE-06, SCOPE-04. Naming, import minimality and layout are recommendations. The §6.7 community linters are required configuration: RG2003 rejects their warnings, RG2006 checks their Lake enablement and rejects a target-wide disable, and every declaration-scoped disable (§6.2) is DECL-01 review. RG5001 checks module-docstring placement (§5.3) and repeated imports (§6.4). Batteries' environment linters are recommended; no community linter discharges a row. |
| 7.1–7.5 | DECL-01–04, FOUND-01–05, THEOREM-01/07. Exact environment, ownership, admission, attribution and contract scope. |
| 7.6–7.7 | COMP-01–04, DOC-03–05. Conservative compiler closure and the exact document-worker protocol. |
| 7.8–7.9 | MUT-01–05; checker qualification and the optional serialized graph are conditional. |
| 7.10–7.11 | BUILD-01–04, DECL-01–04. The adoption mode and the actual enabled invocation determine supported enforcement. |
| 8 and Critical Violations | The checklist, the result rule and triage; no relaxed compliance level. |

The review obligations no mechanical result discharges are the checker's `Residual` type in
[`RegulaCore.Account`](../../lean/RegulaCore/Account.lean), each with one description
(`Residual.description`): `R-INTENT`, `R-INVARIANT`, `R-LAWS`, `R-BOUNDARY`, `R-NONVACUITY`,
`R-DOC`, `R-COST`, `R-QUALIFY` and `R-GRAPH`. The site's
[enforcement page](https://rbeauchamp.github.io/regula/dev/enforcement/) defines them, each rule
page links the ones its rule leaves open, and `lake exe regula explain` prints them. Every
accepted result lists them as unresolved where applicable (`R-GRAPH` only for a
serialized-graph claim), and each RG1007 contract it reports carries `R-INTENT` and
`R-INVARIANT`. A listed identifier is an open obligation, never a completed review; no heuristic
detector replaces one.

The site's [checklist coverage](https://rbeauchamp.github.io/regula/dev/coverage/) page lists
every checklist row with the rules whose explanation lists it and the obligations it carries,
generated from each rule's `checklist` and each obligation's `Residual.rows` and inverted by
construction (`Regula.Site.mem_rulesOfRow`, `mem_residualsOfRow`). A row no rule lists is
semantic review only. Every obligation carries at least one row, each a checklist row
(`residual_rows_listed`), and every checklist row carries at least one obligation
(`residualsOfRow_ne_nil`), both kernel-checked. Which rows a rule lists and which an obligation
carries are reviewed with the rule or obligation, against each row's required verification; the
kernel checks cover only membership and coverage, and no row passes on a presence check or a
checker PASS alone.

## Credits

Lean's authors supply the linter, elaboration, message and Lake APIs; Verso's authors supply
rendering. Design influences (including con-leche and Microsoft CA1416) and the license notices
of adapted code are credited in [design influences](design-influences.md). No external tool
defines Lean policy or permits suppressing mandatory requirements.
