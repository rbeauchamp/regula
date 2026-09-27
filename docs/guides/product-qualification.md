# Product qualification

This is the integrated account of the Regula linter and its rule-reference website
(issue #10). It records, per rule and per supported route, what is proved about the executed
code, what is checked by a command, what was observed, what is trusted and what remains
semantic review. It is repository practice, not part of the normative standard; the rule
predicates live in [the standard](https://rbeauchamp.github.io/regula/dev/standard/) and the
[coverage map](rule-coverage.md). Observations, commands, timings and revisions of the
qualification run are recorded in the [qualification record][q10].

Evidence classes used below:

- **Proved**: a kernel-checked Lean theorem about the definition that callers execute, usually
  through an `ExecutableContract` registration whose `.run` the caller invokes.
- **Checked**: a command's own validation of its output or inputs (a build, a corpus admission, a
  site check); it establishes that property for the inputs it ran on.
- **Observed**: a bounded observation of a real run (adopter journeys, editor, browser, hosting).
- **Trusted**: Lean's elaborator, kernel and compiler, Lake loading, source and dependency
  acquisition, environment extraction, worker processes, JSON transport, the native runtime,
  VS Code and the Lean 4 extension, browsers and GitHub Pages.
- **Review**: the nine residual obligations (R-INTENT … R-GRAPH) of the
  [coverage map](rule-coverage.md#residual-semantic-and-research-accounts); no command
  discharges them.

## Scope

The registry has exactly twenty-two rules (`RegulaCore.RuleId`, `RuleId.all`); every one is
`existingChecker` and has an executed emission site. The supported toolchain is the pinned
[`lean-toolchain`](../../lean-toolchain) (Lean 4.34.0); the checker imports only Lean, Std and
Lake. The only supported editor client is VS Code with the `leanprover.lean4` extension.

Success comes from one place: an `AcceptedRun` built by `RegulaPolicy.accept`, whose
`accept_iff` states that acceptance holds exactly when the run is complete for its plan
(`CompleteFor`) and every stage observation meets its policy (`AllPolicyOK`). `lake lint`
exits 0 only through `Regula.Checker.Lint.accepted_sound` (audit exit 0 and a recorded
`completed` status of the requested mode imply such a run); its exit classes are the claimed
`RegulaCore.Lint.checked_classify`. Those theorems prove the success direction. They do not prove
which rule a failure receives; the per-rule linkage below says which rule mappings are proved.

## Per-rule capability and evidence

`D` is the shared declaration decision: `RegulaPolicy.declarationFailure` (the first failed
requirement of `declarationRequirements`, `declarationFailure_ordered`), mapped to a rule by the
injective `ruleForFailure`. Project, file and documentation paths run it through
`Policy.ruleForMember` (`checked_memberRule.run`, equal to `ruleFor` by `ruleForMember_eq`);
the editor runs `checked_editorDecision.run`, proved equal to the project decision on the
editor domain (`editor_request_sound`/`_complete`, `editor_decision_none_iff`/`_rule`/`_pending`
in `RegulaCore.Policy`). Its proofs take the observed declaration fields (`collectAxioms`
axioms, unsafe/partial flags, contract observations) and the recomputed generated-role
evidence as given. Modes are the rule's registry `evidenceModes`, which `makeDiagnostic`
enforces at construction (a finding in an unlisted mode is an error, never a silent pass); each
listed mode has an executed emission site. For RG5001–RG5003 the correspondence is proved:
`Regula.Checker.Acceptance.documentationPresence_modes` states that their modes are exactly the
modes whose required stages (`RegulaPolicy.requiredStages`) include documentation presence. Stage
names are the required-stage slots of `RegulaPolicy.Stage` whose observation the rule reports.

| Rule | Normative obligation | Detector and adapter | Modes (routes) | Stage | Proved linkage | Qualification | Limits | Credit |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| RG1001 | §8.5; FOUND-01 | D (`projectAxiom`); `Findings.declarationFinding` | editor, incremental, fresh, file, docs | declarationPolicy | D | corpus; native, lint-driver, build-policy, fixture controls | Native teaching axioms are RG1004 | Lean `ConstantInfo` |
| RG1002 | §8.5; FOUND-02 | D (`sorryAx` in axioms) | editor, incremental, fresh, file, docs | declarationPolicy | D | corpus (diagnostic inspection that keeps Lean's warning); native, fixture controls | Lean's `sorry` warning makes project and claimed-file audits stop at RG2003 first | Lean `collectAxioms` |
| RG1003 | §8.5; FOUND-03 | D (axiom outside the standard and compiler sets) | editor, incremental, fresh, file, docs | declarationPolicy | D | corpus (project, vendored dependency); native, fixture controls | Imported axioms are not exempt | Lean `collectAxioms` |
| RG1004 | §8.5; FOUND-05 | D (compiler-trusting or native-role axiom on a conforming claim) | editor, incremental, fresh, file, docs | declarationPolicy, transcript | D; role sets from `authorize` | corpus; native, fixture controls | Editor defers role authentication (RG2005) | Lean frontend transcripts |
| RG1005 | §8.5, §4.5; FOUND-03/04 | D (`ProfileOK` fails) | editor (with `regula.localFoundation`), incremental, fresh, file | declarationPolicy | D | corpus plus wrong-claim refusal control; native, build-policy controls | Documentation fences use Standard-Logical or teaching requests, under neither of which it can fire | Lean `collectAxioms` |
| RG1006 | §8.4; COMP-02 | D (unsafe or partial, not an authenticated helper) | editor, incremental, fresh, file, docs | declarationPolicy, transcript | D; `authorizedUnsafeRecHelpers_iff` | corpus; native, fixture controls | Editor defers helper authentication (RG2005) | Lean frontend transcripts |
| RG1007 | §8.12, §8.5; BUILD-03, THEOREM-07 | D (contract observation has a failure) | editor, incremental, fresh, file, docs | declarationPolicy | D over the observation; `Collect.executableContract?` is operational | corpus; native, build-policy controls | Adequacy of `R` and caller linkage are R-INTENT, R-INVARIANT | Lean type checker |
| RG2001 | §8.1; DECL-01/04 | Setup failures and every escaped audit error not prefixed `manifest-` (`AxiomGate` catch-all) | incremental, fresh, file | setup, before any stage | None: classification by error prefix, fail-closed | corpus demonstration (INCOMPLETE by design) | Always INCOMPLETE; `docFenceAudit` setup failures print FAIL without a finding | Lake workspace loader |
| RG2002 | §8.2; DECL-04 | `Manifest.parse`/`load`, `checkClassification`; editor `Rules.request` | editor, incremental, fresh, file | configuration | `Manifest.parse_sound`, `parseValue_complete` (excluded library, kernel-checked); `checked_editorRequest` | corpus; structural, build-policy, lint-driver (exit 2), native controls | Routing by `manifest-` prefix is unproved; editor never guesses scope | Lake elaborated package model |
| RG2003 | §8.3; DECL-01, BUILD-01 | `Lake.buildChecked` result lines; file compile via `SourceAudit` | incremental, fresh, file | build | Acceptance side only (`BuildOK`) | corpus; build-policy, lint-driver (exit 3), `sourceDiagnosticFailure` controls | Project runs: always INCOMPLETE. File runs reject warnings only with `--claim` | Lake build |
| RG2004 | §8.2; DECL-02/03 | Inline inventory checks in `AxiomGate` | incremental, fresh | discovery | Acceptance side only (`ScopeOK`, `checked_surfaceAssignments`) | corpus; structural, environments controls | Violation for `unexpected-project-module`; INCOMPLETE for omission, not-fresh, attribution mismatch | Lake module arrays, `.olean` origin |
| RG2005 | §8.3; DECL-01/02 | `Admission.validate`, source freshness, authentication; editor pending | editor, incremental, fresh, file, docs | admission, transcript | Acceptance side (`AdmissionOK`); `editor_decision_pending` | corpus demonstration; fixture, history controls | Always INCOMPLETE; imported base trusted | Lean `Environment.replay` |
| RG2006 | §8.1, §6.7, §6.2; DECL-01 | `RegulaPolicy.Community.failures` on each claimed target's Lake `leanOptions`, `weakLeanArgs` and `leanArgs` (`Lake.buildOptions`); Mathlib from the surface's loaded environment | incremental, fresh | configuration (reported after inspection; a violation does not stop the run) | `failures_eq_nil_iff`, `conforming_of_mathlib`, `leanArgument_mem_failures_iff` (the `-D` reading over argument characters) and five fixed-argument cases; reading Lake's configuration is operational | corpus; self-lint (Regula's own targets, Mathlib and core-only) | `linter.missingDocs` not yet decided; source `set_option`, `lake` command-line options and extra `lean` arguments other than `-D` not read | Lake `LeanLib`/`LeanExe` configuration |
| RG3001 | §8.6; COMP-03 | `executionFailureRecords` → `RuleDiagnostics.executionFinding` | incremental, fresh, file | execution, history | `executionFailureRecords_empty_iff`, `checked_executionFailures`, `executionRule_injective` | corpus demonstration; policy-domain controls | Always INCOMPLETE; closure overapproximates runtime edges; not an editor rule | Lean compiler IR |
| RG3002 | §8.6; COMP-03/04 | Same, checked-mode branch | incremental, fresh, file | execution, origin (Init native-runtime exemption) | Same; `BoundaryOK` | corpus; fixture, build-policy controls | Native runtime stays trusted; external code unproved | Lean compiler IR |
| RG4001 | §8.7; DOC-03 | `Documentation.scan` | docs | documentScan | Acceptance side (`DocumentOK`); scanner unproved | corpus; fence corpus controls | Structure only | — |
| RG4002 | §8.7; DOC-04 | `assessPositive` (D plus warning check) | docs | example | D; `ExampleExpectationOK`; `incomplete_example_refused` | corpus; fence corpus controls | Standard-Logical only | Lean elaborator |
| RG4003 | §8.7; DOC-05 | `auditNegative` with `matchesPattern` | docs | example | `matchesPattern_iff` on the executed matcher | corpus; fence corpus controls | Worker non-completion is INCOMPLETE | — |
| RG4004 | §8.7; DOC-05 | `assessPositive` teaching branch | docs | example | `checked_memberFoundation`, `labelOf_member` | corpus plus teaching refusal controls | Never a conforming positive | Lean frontend transcripts |
| RG5001 | §5.3, §6.4; DOC-01 | `Linter.Documentation.moduleObservation` (module-doc metadata; Lean's header and first-command parser on the bound source) decided by `RegulaPolicy.ModuleHeader.failures` | editor, incremental, fresh | documentationPresence | `failures_eq_nil_iff`, `mem_repeated_iff`; acceptance side (`DocumentationPresenceOK`, `modulePresence_iff`); the parse is operational | corpus; native (`MisplacedDoc`, `RepeatedImport`), producers controls; self-audit | Presence, position and repeated imports only (R-DOC) | Lean module-doc and parser APIs |
| RG5002 | §5.1; DOC-01 | `materialDocumentationFailure` on `findDocString?` of `@[regula_material]` public declarations | editor, incremental, fresh | documentationPresence | `materialDocumentationFailure_eq_none_iff`/`_missingDocstring_iff`, `ruleForMaterialDocumentation_injective` | corpus; native, producers controls | Registration completeness is R-DOC | Lean `findDocString?` |
| RG5003 | §5.2; DOC-02 | Same, missing Intent section | editor, incremental, fresh | documentationPresence | `materialDocumentationFailure_eq_missingIntent_iff`, `hasIntentSection_iff` | corpus; native controls | Presence only; intent adequacy is R-INTENT | Lean `findDocString?` |

"Corpus" is the [rule-example campaign](rule-examples.md): one violating and one corrected
record per rule in fresh workspaces, admitted by the proved `ruleExampleQualification` relations
and rendered on the rule's page. It qualifies the detectors on those inputs; it does not prove
them correct for every input. The registry, complete acceptance and executed-form equality draw on
con-leche's designs (see [design influences](design-influences.md)); the credit column names the
Lean facility each detector observes.

**Foundations of the cited proofs.** Theorems in `RegulaPolicy` and `RegulaCore` belong to claimed
Standard-Logical surfaces: ordinary acceptance re-elaborates them from source and checks each
declaration's exact axiom set against that profile. Theorems in the excluded `Regula` library
(`Manifest.parse_sound`, `parseValue_complete`, `Regula.Site.Build.helpUrl_dev`) are
kernel-checked by the warning-as-error `lake build`; `foundation_manifest.json` records an
in-module `collectAxioms` Standard-Logical ceiling for that library's transport-admission
theorems. The acceptance audit does not inspect them. The hypotheses of
the `D` theorems are stated above; the others are the observations named in each row.

**Evidence commands.** Each "Qualification" entry names a campaign run by
`./scripts/verify.sh diagnostics <partition>` (fixtures, structural, cli, environments,
build-policy, lint-driver, producers, history, rule-examples 1/2 and 2/2) or inside ordinary
acceptance (registry, native and CLI qualification). The #10 runs, with exact revisions and
timings, are listed in the [qualification record][q10-runs].

Every declaration, context and execution finding is a `Diagnostic id` whose `helpUrl id` is the
development route of `id` (`Regula.Site.Build.helpUrl_dev`), and whose text is
`messageLine id …` (`RegulaCore.Rule`, the rule's published message form) followed by the
rule's remedy and that URL with the offline `lake exe regula explain` command
(`RegulaCore.Feedback.standalone`). A command-line run prints its findings with
`Feedback.render`: each rule's first finding adds its requirement, rationale, rewrites and
compliant example (or the correction, where the checked files are qualification inputs), with the order and once-per-rule properties proved there.

## Supported routes

| Route | What runs | Result | Evidence |
| --- | --- | --- | --- |
| Editor, `import Regula.Linter` | Command and module hooks over the current snapshot | `editorSnapshot` feedback: RG1001–RG1007, RG2002, RG2005, RG5001–RG5003 at their ranges; never project acceptance | Proved editor/project equality above; observed in VS Code ([editor journeys][j14], [#10 journey][q10-editor]) |
| `lake lint` | `regula/lint` driver: builds the manifest's targets with the audit-build marker (local findings off whatever the source sets `linter.regula` to), then the `axiomGate` project audit | `incrementalProject`; exit 0/1/2/3 | `accepted_sound`, `checked_classify`; `liveFeedback_auditBuild`; lint-driver campaign (17 controls); [#10 fresh-adopter journey][q10-cli] |
| `lake lint -- --fresh` | Same audit in an isolated copy from empty build output | `freshProject`, the only fresh whole-project claim | Observed PASS in the [fresh adopter][q10-cli] |
| `lake lint -- --json-out PATH` | Same audit, result schema 3 | `status`, the stage evidence `stages` and `stagesCompleted` with `complete` and `stagesNotRun`, diagnostics in run order with source ranges, `remedy` and `helpUrl`, and each fired rule's guidance (`rules`) | `ResultProtocol.admitGuidance` on every rule-example result |
| `lake exe regula explain\|rules\|agent-guide\|skill` | Prints registry-generated Markdown; no audit | Exit 0, or 2 for an invalid invocation | `parseCommand_sound`, `parseCommand_arguments`; committed skill checked equal in acceptance |
| `lake lint -- --explain-config`, `--help` | No audit | Exit 2; establish nothing | Observed (both, [record][q10]); lint-driver campaign covers `--explain-config` |
| `lake exe lint` | Same driver without Lake dispatch | As `lake lint` | Observed PASS in the [fresh adopter][q10-routes]; for packages whose `lintDriver` is taken |
| Build-lint `policy` target | Sole default target runs `axiomGate --build-lint` | Incremental audit; failure fails `lake build` | build-policy campaign |
| `lake exe axiomGate` | Fresh project audit (default), `--incremental`, `--file F [--claim P]`, `--with-docs` | Accepted account and exit status | Ordinary acceptance dogfoods it on every claimed library |
| `docFenceAudit`, `./scripts/verify.sh docs` | Every Lean fence under `docs/` and, with `--verso`, every `lean` block of the Verso standard, which it builds and renders | `documentationExample` | Acceptance step 2 |
| Workers | `axiomGate` inspection and fence diagnostic workers, with indexed result admission (`checked_indexedResults`) | A crashed, abnormally terminated or incomplete worker is INCOMPLETE, never a pass | Proved admission; fixtures and fence-corpus controls (abnormal termination) |
| `freshChecker` | Optional serialized-graph recheck (§8.9) | Emits no rule findings | Optional MUT-05 claim; not part of product acceptance |
| Direct `lean`, `lake build <other target>`, `lake lint --builtin-only`, TOML `lake build` | Nothing of Regula's project audit | Not enforcement | Documented as such everywhere |

Incremental and cached paths re-evaluate current policy on every run: the driver and the
`policy` target have no cached verdict, and a configuration change reloads the manifest
(lint-driver repeated cached violation and build-policy cached-failure and
configuration-change controls). Local
options (`linter.regula`, `regula.localFoundation`, `warningAsError`) change only local feedback;
the project audit still rejects. A cancelled editor collection reports nothing for that
declaration (observed in VS Code, [record][j14-snapshots]), and a failed one reports RG2005
(`Regula.Linter` `unavailable`), never an invented rule or a PASS. Unknown rules cannot occur:
the registry is closed, and codecs refuse unknown IDs, fields and modes.

## Adopter journeys

On a new project that required the linter by Git revision `a52bf1f` and followed the
[adoption guide](adoption.md) ([record][q10]). These runs exercised that revision; the #10
changes to evidence modes, message rendering, explanations and credits were covered instead by
ordinary acceptance, both corpus shards, the site build and the lint-driver and producers
campaigns at the #10 revisions ([record][q10-runs]).

- `lake lint` accepted the clean project (exit 0), and `lake lint -- --fresh` gave fresh
  whole-project acceptance.
- A project axiom gave the project-logical-axiom finding at its declaration with the rule URL
  (exit 1); a Choice-Free surface using `Classical.byCases` gave the axiom-profile finding
  (exit 1), and the documented fix (a proof with fewer axioms) returned exit 0; an unclassified
  library gave the configuration-classification finding (exit 2), fixed by an exclusion; a
  missing module docstring gave the module-documentation finding (exit 1); an unused-variable
  warning gave the warning-free-elaboration finding (exit 3); turning the linter's
  live-feedback option off did not hide a project-logical-axiom violation (exit 1).
- A second library importing `Mathlib.Algebra.Group.Basic` (Standard-Logical) was accepted by
  `lake lint` and `lake lint -- --fresh`.
- A `sorry` gave the warning-free-elaboration finding (exit 3), not the proof-hole finding:
  Lean's own warning stops the audit first. The proof-hole rule's page (RG1002) and the adoption
  guide say so.
- In VS Code, the same `sorry` showed Lean's warning and the proof-hole finding at the
  declaration with its rule code, the text URL and Lean's **View explanation** anchor
  (`target=_blank`, `rel="noreferrer noopener"`, no Lean-manual link). A trusted click reached
  the anchor, and the configured external browser started immediately afterwards; the URL it
  received and the page it showed were not observable from this environment. The same URL
  served the matching rule page of the deployed commit. The documented fix cleared the
  diagnostic, and `lake lint` accepted.

These are bounded observations of real runs, not theorems about the tools.

## Community linters beside Regula

Standard §6.7 requires every claimed library to enable Lean's `linter.missingDocs` and, with
Mathlib, Mathlib's standard linter set without its three Mathlib-repository linters; it and the
[adoption guide](adoption.md#community-conventions-and-linters) recommend running Batteries'
linters beside `lake lint`. The first run below exercises that exact configuration. The earlier
runs after it observe the Mathlib and Batteries routes without `linter.missingDocs` or the
exclusions.

### The required configuration in the `lake new` layout

These controls ran on 2026-09-26 (Lean 4.34.0) on a disposable adopter in the layout that
`lake new Adopter math` creates: a root `Adopter.lean` in the working directory importing
`Adopter.Basic` and `Adopter.Long`. Its `lakefile.toml` held the template's `[leanOptions]`
plus exactly the options of the adoption guide: `linter.missingDocs`, `autoImplicit`, and the
standard set with `weak.linter.style.header`, `weak.linter.hashCommand` and
`weak.linter.style.longFile` off. It required Mathlib `5ed2965` by Git revision and this
repository's checker by path, with `lintDriver = "regula/lint"`, and its one claimed library
(Standard-Logical) had the adoption guide's globs. `Adopter.Basic` imported
`Mathlib.Order.Basic` and held a documented definition, a documented theorem and a passing
`#guard`; `Adopter.Long` held 800 documented definitions in 1608 lines. Regula's RG5001 also
required a module docstring in the import-only root.

- The clean library: `lake build` emitted no warning, and `lake lint` and
  `lake lint -- --fresh` both exited 0 (`PASS`).
- Without `weak.linter.style.header = false`: a header warning (`Copyright too short!`) in each
  of the two modules the root imports; `lake lint` exit 3 (`INCOMPLETE`, RG2003).
- Without `weak.linter.hashCommand = false`: a warning on the `#guard`
  (`` `#`-commands, such as '#guard', are not allowed in 'Mathlib' ``); `lake lint` exit 3.
- Without `weak.linter.style.longFile = 0`: no warning on the 1608-line module. The set does not
  turn that line-count option on downstream, so the explicit `0` removed nothing here.
- A docstring line of 101 characters: Mathlib's `This line exceeds the 100 character limit`
  warning and `lake lint` exit 3. The same line under `set_option linter.style.longLine false in`
  with a comment giving the reason: no warning, exit 0.
- An undocumented definition: `missing doc string for public def undocumented` and
  `lake lint` exit 3.

The header and `hashCommand` exclusions each removed their linter's warnings, and the `longFile`
setting was inert. Of the set's other linters only `linter.style.longLine` was exercised, and it
still fired, as did `linter.missingDocs`.

### RG2006 and the RG5001 header checks

These controls ran on 2026-09-27 (Lean 4.34.0, Mathlib `5ed2965`) with `lake lint` on the
repository and on the `examples/build-lint` adopter, each mutation undone before the next
control. They are observations of the operational adapters; the decisions they feed are proved
(`RegulaPolicy.Community.failures_eq_nil_iff`, `RegulaPolicy.ModuleHeader.failures_eq_nil_iff`).

- The unchanged adopter, and this repository (whose `Audit`, `AuditApp` and `auditApp` targets
  enable the Mathlib set and whose other claimed targets are core-only): `PASS`, exit 0.
- `set_option pp.all false` before an adopter module's docstring: RG5001 "make the module
  docstring the first command after the imports", exit 1.
- `import Regula.Contract` twice: RG5001 "remove the repeated import of `Regula.Contract`",
  exit 1.
- The adopter's `autoImplicit` option removed, `relaxedAutoImplicit` set to `true`,
  `weak.linter.unusedVariables` set to `false` and `moreLeanArgs := #["-DmaxHeartbeats=400000"]`:
  one RG2006 finding for `Widget` naming the other three failures, exit 1; the
  `-DmaxHeartbeats=400000` argument, which sets no checked option, is not reported. (Before
  RG2006 was narrowed to `-D` settings that contradict a checked option, the same control named
  the argument as a fourth failure.)
- The adopter unchanged except `moreLeanArgs := #["-DmaxHeartbeats=400000", "-qD",
  "autoImplicit=true", "--tstack=100000"]`: one RG2006 finding for `Widget` naming only
  `autoImplicit` set to `"true"`, exit 1.
- The repository's `Audit` library without its Mathlib options: one RG2006 finding for `Audit`
  naming the four Mathlib options, exit 1; the core-only targets were not reported.

The two `moreLeanArgs` runs observe the adapter; the `-D` decision itself is kernel-checked in
`RegulaPolicy.Community`. `leanArgument_mem_failures_iff` shows that it reports a `-D` argument
exactly when some `-D` form (`-Dname=value`, flags before the `D` as in `-qD`, or `-D` followed
by `name=value` as the next argument; `Defines`, over the arguments' characters) sets a checked
option to a contradicting value, a linter being turned off by the string `"false"`. For every
`leanOptions`, `autoImplicit_argument_fails`, `maxHeartbeats_argument_passes`,
`linter_argument_fails`, `excluded_linter_argument_passes` and `plugin_argument_passes` fix five
argument lists; each case whose argument names an option takes the name `lean` reads as a
hypothesis, because `String.toName` is `partial` and the kernel cannot evaluate it. That this
reading matches the `lean` command line remains assumed.

The native-linter campaign's `MisplacedDoc` and `RepeatedImport` controls exercise the same
RG5001 decision in the editor path, and the rule-example corpus the RG2006 pair.

### Earlier runs: the Mathlib and Batteries routes

These controls ran on 2026-09-26 on a disposable adopter (Lean 4.34.0, Mathlib `5ed2965`, this
repository's checker by path) whose `lakefile.toml` set `weak.linter.mathlibStandardSet`,
`autoImplicit` and `relaxedAutoImplicit` under `[leanOptions]`, and whose one claimed library
(Standard-Logical) imported `Mathlib.Order.Basic` and held a documented definition and theorem.
With `lintDriver = "regula/lint"`:

- The clean library: `lake lint` exit 0 (`ACCEPTED`), so the standard set emitted nothing there.
- One docstring line of 101 characters: `lake lint` exit 3 (`INCOMPLETE`), RG2003 `build-failed` with
  Mathlib's `This line exceeds the 100 character limit` warning as its evidence.
- The same line under `set_option linter.style.longLine false in` on its declaration: exit 0.
- A declaration under `set_option linter.unusedVariables false in` with an unused argument:
  exit 0. The audit sees no disabled linter, which is why standard §6.2 leaves that check to
  review.
- `lake build` then `lake exe runLinter`: exit 0 for the clean library and exit 1 (Batteries'
  `unusedArguments`) for the previous mutation, which Regula had accepted.

With `lintDriver = "batteries/runLinter"`, after `lake build`: `lake lint` (Batteries' linters)
and `lake exe lint` (Regula) both exited 0 on the clean library. An undocumented definition gave
`lake lint` exit 1 (`docBlame`) and `lake exe lint` exit 0. Earlier, `runLinter` without a
rebuild linted the stale build of a previous mutation, which is why the guide runs `lake build`
first.

These observe two small adopters through the `lakefile.toml` route on this toolchain. They are
not a theorem about either tool, and the `lakefile.lean` spelling of the options was not run.

## Website

- **Proved** (claimed `RegulaCore.Site*` and `RegulaCore.Guide`, except `helpUrl_dev` in the excluded
  `Regula.Site.Build`): one page route per rule per edition and none shared
  (`pageFiles_nodup`, `mem_pageFiles`), escaping (`escape_safe`, `htmlBlock_ok`), filter no-match
  set (`mem_emptySelections`), link-check soundness for scanned links (`linkErrors_nil_iff`), the
  nine sections (`ruleSections_headings`), nonempty explanations (`guide_wellFormed`), archive
  monotonicity (`artifactRevisions_mono`), the lossless single "Project" index label
  (`projectModes_coincide`), WCAG 2.x contrast of every text token on every background token in
  both colour themes (`ink_on_paper`, `control_on_paper` over the brackets of `channel_bracket`:
  exact integer statements, read as WCAG ratios through one argued step about real powers), and
  `helpUrl_dev` for every emitted help link.
- **Checked** by `./scripts/verify.sh site`: evidence identity and freshness, exact rule-route
  set, example text in pages, `axiomGate --validate-site`, byte-identical editions, size budget.
  CI's `verify-deployment` checks the live `build.json`, every rule page of every edition and
  the 404 route byte for byte against the validated artifact.
- **Checked** for the standard (`./scripts/verify.sh docs` and the site build): every `lean` block
  elaborates where it is written as its kind requires, the fence audit classifies the same blocks,
  every cross-reference and checklist-row anchor resolves, every section the registry cites is a
  part of the elaborated standard with its tag and exact heading in its chapter
  (`website/StandardMain.lean`), and the rendered standard defines the anchor of every cited
  section and every row a rule page links (`Regula.Site.standardAnchors`, `missingAnchors_nil_iff`)
  and every page and anchor `docs/` links in the development standard
  (`Regula.Site.documentAnchors`), and the [coverage map](rule-coverage.md#complete-chapter-9-row-map)
  links exactly the rendered checklist rows, in order, each labelled with its row
  (`Regula.Site.rowMapMismatch_eq_none_iff`).
- **Observed** on the live site (deployed `a52bf1f`, before #10; [record][q10]): all 21 `dev/`
  and `rev/` rule routes return their pages; unknown IDs, unreleased versions and unpublished
  revisions return the not-available page (HTTP 404) without redirecting; search finds rules;
  keyboard traversal reaches the table of contents and rule index with visible focus; the index
  lists 21 rules. At 390 px every rule page scrolled horizontally because the attribution's
  commit hash did not wrap; #10 adds wrapping for inline code and links; its local build
  showed no horizontal scroll at 390 px on any
  rule page or on the index, versions and credits pages (the credits page's long plain-text URL,
  also present on the live site, is covered by paragraph wrapping).
- **Hosting**: GitHub Pages project site from GitHub Actions, no custom domain, no release, no
  paid hosting. The site lags `main` while checks run; each page names its commit. Operator
  settings not configured: `site` and the corpus shards are not required status checks, and
  `site-archive-regula` has no force-push/deletion protection ([website guide](website.md)).

## Changes made by this qualification

Review of the delivered product found and fixed:

- Registry evidence modes that no path emits: RG1005 and RG2001–RG2003 no longer list
  documentation examples, RG2004 lists only project modes, RG5001–RG5003 list editor and
  project modes. The site's evidence-mode filters and each page follow.
- RG1007 cited §8.6; its predicate is stated in §8.12 and §8.5.
- The published message form (`RG1001:{subject}:{detail}`) was not what the checker prints; it
  is now derived from the same `messageLine` the checker renders, and the account text names
  RG1007 through the registry.
- Explanations: the `sorry` route (RG1002), the editor's actual scope (RG2005, RG3001, RG5001),
  RG2004's two impact classes, RG2001's catch-all role, RG2003's file-mode `--claim` condition,
  INCOMPLETE fence outcomes (RG4002–RG4004), complete checklist rows, and a rule-specific
  strict-impact row with `lake lint` exit classes.
- Credits: the adapted Lean JSON parser (Apache 2.0) now has its verbatim notice, the Apache
  text in `LICENSES/`, and a credits entry; Verso's license is linked; the CDN-loaded marked
  library, Batteries and the vscode-lean4 infoview are credited; no endorsement is implied.
- Narrow-screen layout: long inline code, links and paragraph text now wrap.
- A theorem (`documentationPresence_modes`) now fixes the documentation-presence rules' modes to
  the stage structure at build time.
- Stale documentation: two-command acceptance, twenty-one rules, delivered integration, the
  docs index.

## Remaining limits

- The human transcript names the file and declaration of a finding; exact ranges are in
  `--json-out` and the editor.
- RG2001/RG2002 routing of escaped errors is by error-message prefix, and RG1007 contract
  extraction, RG2004 inventory checks, the fence scanner and RG5001 presence are operational
  code in the excluded `Regula` library; the acceptance theorems cover their observations, not
  their extraction.
- Editor: only VS Code with the Lean 4 extension; no latency claim; the browser-side page view
  after the external hand-off is not observable from this environment beyond the process
  hand-off and the live route.
- A small Mathlib-importing library was accepted incrementally and fresh, and two small adopters
  ran Regula beside Mathlib's syntax linters, one of them in the `lake new` layout with the
  complete §6.7 configuration, and Batteries' `runLinter`
  ([above](#community-linters-beside-regula)); there is no Mathlib-scale adopter or
  other-editor claim, and no released versions (`/v/` pages need a separately authorized
  release).
- Diagnostic help links target the moving `/dev/` route, so an adopter pinned at an older
  revision reads the latest deployed explanation there; the unchanged text of any published
  revision stays at `/rev/<commit>/rules/<ID>/`, and versioned `/v/` links await a release.
- All nine residual obligations stay open; every accepted account lists them.
- Known gap (recorded 2026-09-27): no claimed target of this repository enables
  `linter.missingDocs` (standard §6.7; the 2026-09-26 community-alignment audit counted about
  720 definitions without a docstring), so `DOGFOOD-01` does not hold for that obligation until
  [#97](https://github.com/rbeauchamp/regula/issues/97) is closed. The other §6.7 options,
  Mathlib's standard set on `Audit`, `AuditApp` and `auditApp`, are enabled and RG2006 checks
  them.

## Optional external checking

[#8](https://github.com/rbeauchamp/regula/issues/8) (con-leche export research) ended in a **no-go**
([decision record](con-leche-research.md)), so [#9](https://github.com/rbeauchamp/regula/issues/9)
(adapter) is closed as not planned. There is no con-leche checking integration. No export was
checked, so export compatibility is unperformed rather than passed or failed. Neither issue was
part of or blocked core delivery. The optional serialized-graph claim remains `freshChecker`.
Con-ron is excluded.

[q10]: https://github.com/rbeauchamp/regula/blob/11e05c682ee76ddf9b7cd81fdb827b572469ed57/session/evidence/issue-10-qualification.md
[q10-cli]: https://github.com/rbeauchamp/regula/blob/11e05c682ee76ddf9b7cd81fdb827b572469ed57/session/evidence/issue-10-qualification.md#fresh-adopter-cli-journey
[q10-editor]: https://github.com/rbeauchamp/regula/blob/11e05c682ee76ddf9b7cd81fdb827b572469ed57/session/evidence/issue-10-qualification.md#editor-journey-vs-code
[q10-routes]: https://github.com/rbeauchamp/regula/blob/11e05c682ee76ddf9b7cd81fdb827b572469ed57/session/evidence/issue-10-qualification.md#additional-route-observations-base-a52bf1f-fresh-adopter
[q10-runs]: https://github.com/rbeauchamp/regula/blob/11e05c682ee76ddf9b7cd81fdb827b572469ed57/session/evidence/issue-10-qualification.md#commands-and-results-for-the-10-change
[j14]: https://github.com/rbeauchamp/regula/blob/11e05c682ee76ddf9b7cd81fdb827b572469ed57/session/evidence/issue-14-editor-journeys.md
[j14-snapshots]: https://github.com/rbeauchamp/regula/blob/11e05c682ee76ddf9b7cd81fdb827b572469ed57/session/evidence/issue-14-editor-journeys.md#stale-and-cancelled-snapshots
