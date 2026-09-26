# Proof-driven engineering foundation status

This is the bounded implementation baseline for [Project 9](https://github.com/users/rbeauchamp/projects/9),
established by [#38](https://github.com/rbeauchamp/regula/issues/38).
It adds no normative rule and does not claim whole-checker verification or full
repository conformance. Its purpose is to make the remaining foundation work
executable without repeating established proofs or weakening their statements.

## Baseline and scope

The source baseline is `708507199f693aa330b0c87086402d89d813da1b` on
2026-09-18. Lean is `4.34.0`, compiler commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`; Mathlib is
`5ed2965256430c3649e86755f9576b54eca72435`. The documentation project uses
Lean `4.34.0` and Verso `cad4b633e75ea769b851f12f9ca3b4f0dfcc625f`.
The tracked toolchain and manifests remain authoritative at later revisions.

The selected scope is rows F01–F12 below and the explicit successor obligations.
References identify definitions to inspect, not a replacement module/declaration
inventory. Claimed coverage comes from Lake's elaborated root-package libraries,
`getModuleArray`, executable roots, and Lean environment attribution, through
[`Lake.surfaceInventory`](../../lean/Regula/Checker/Lake.lean).
Additional imported modules must still be reconciled; the `modules` facet is not
silently substituted for the configured array.

The [manifest](../../foundation_manifest.json) claims `RegulaPolicy`,
`RegulaVerification`, `RegulaQualification`, `Audit`, and `AuditApp`,
plus the standalone `auditApp` root `Main`. The operational `Regula` library
and its checker executables remain excluded from the conforming proof surface;
`Fixtures` remains isolated. A library's Standard-Logical upper bound is not
every declaration's exact axiom set.
#41 adds the claimed `RegulaCore` library; see the #41 delivery below.

Global integration has one owner: [#7](https://github.com/rbeauchamp/regula/issues/7),
with [PR #33](https://github.com/rbeauchamp/regula/pull/33). The #38 baseline
above remains historical. The current implementation below includes PR #33's
environment-indexed integration at `e19018e47b73ac732853ad90297bcc94d15854b3`
and the [retained-role repair](https://github.com/rbeauchamp/regula/blob/11e05c682ee76ddf9b7cd81fdb827b572469ed57/session/evidence/ci-role-retention.md).
That checkpoint's hosted ordinary gate exceeded 420 seconds; local success does
not establish hosted readiness. Implementation linkage is present, while final
qualification, exact-head hosted CI and integrated delivery remain separate gates.
#7 closed on 2026-09-23 after PR #33 and follow-ups #45–#49; the #43 closure below
reconciles the resulting rows.

## Component and obligation inventory

Status notation: **E** = existing type/construction/theorem establishes the stated
Lean relation; **L** = missing global execution linkage on this baseline;
**R** = a selected adapter relation still needs explicit evidence;
**T** = trusted acquisition/execution or semantic-review boundary. Several may
apply to different parts of one row. An R is a project obligation, not a claim
that every helper needs a separately named theorem.

| ID | Definition and actual consumer | Existing guarantee and remaining obligation | Status / owner |
| --- | --- | --- | --- |
| F01 | [`ExecutableContract`, `run`, `run_eq`](../../lean/Regula/Contract.lean); [`Collect.executableContract?`](../../lean/Regula/Collect.lean) feeds collected declarations and policy `ContractOK`. | The field proves exactly `R f`; `run` is definitionally `f`. Recognition checks the elaborated closed registration and executable root, not intended adequacy or every caller. Preserve supported universes, full domain and root coverage; review the required relation independently. #43: any definition, theorem or opaque whose type reduces to `ExecutableContract _ impl R` is recognized as a registration; `ContractOK` then requires it closed, with `impl` a named, computable, safe, non-partial definition or opaque of non-`Prop` type that does not return a type. The structure itself is in the excluded `Regula.Contract`, imported by claimed modules. | **E/T**; #39, reporting #42 (report account `ContractAccount`). |
| F02 | [`Inventory`, `admitInventory`, `admitExecution`](../../lean/RegulaPolicy/Admission.lean); [`Policy.admitScope`](../../lean/Regula/Checker/Policy.lean) is called by project, file, fence, rule-example, acceptance freeze, environment-census and self-test inspection. | Admitted values carry validity; exact admission retains input observations, and execution admission has a preservation theorem. The adapter first checks frontend coordinates, then admits inventory and computes roles. #39: `admitScope` runs `checkedScope` (`ScopeContract`): first coordinate refusal in transcript order, then exactly `admitInventory` with `authorize`; success iff every coordinate check and `InventoryValid` hold, retaining both arrays. Supplied transcripts are not authenticated. #41: `checkedScope` is on claimed `RegulaCore` and quantifies over every coordinate check; the adapter passes `Frontend.validateCoordinates`, which runs the claimed `checkedCoordinates` (`CoordinateContract`: success iff `CoordinatesAgree`, refusal with the first unmet obligation in traversal order) at Lean's LSP UTF-16 column function (see #41 delivery). | Core and coordinate check **E** (claimed); Lean's UTF-16 column function and acquisition **T**; #41 (delivered). |
| F03 | [`policyFor`, `foundationFor`, `declarationFailure`](../../lean/RegulaPolicy/Decision.lean); `Policy.ruleForMember`, `labelOfMember`, `classifyMember` (#40) in the project/file gates and the fence, rule-example and self-test audits, with `ruleFor`, `reasonFor`, `labelOf` kept for arbitrary input; [`Linter.Rules.declarations`](../../lean/Regula/Linter/Rules.lean) for local feedback. | Existing equivalences cover membership, policy, all six classification outcomes and ordered first failure. #39: `request` runs `checkedRequest` (`RequestContract`, by spelling); `ruleFor` runs `checkedRule` (`RuleContract`) over `policyFor`, with `ruleForFailure_injective` and `reasonFor_eq_some_iff`. #40: per-declaration callers iterate the admitted inventory and run the member forms `checkedMemberFailure`/`checkedMemberFoundation`/`checkedMemberRule`, equal to `policyFor`/`foundationFor`/`ruleFor` on every member, without the membership scan. Environment collection remains separate. #41: these projections, `labelOf`/`labelOfMember` and the registry they map to are on claimed `RegulaCore`; `classify`/`classifyMember` stay adapter renderers. | Core and projections **E** (claimed), collection **T**; #41 (delivered). |
| F04 | [`executionFailureRecords`, `executionSummary`](../../lean/RegulaPolicy/Execution.lean); `Policy.executionFailureRecords`, `executionFailures` and gate rendering. | Empty pure failures iff `ExecutionOK` for every admitted finite inventory and mode. #39: `Policy.executionFailureRecords` is the decision's own records (identity); `executionRule` is injective; `executionSummary` runs `checkedSummary` (`SummaryContract`). Counts describe observations of a conservative account, not a minimal native call graph. #41: `executionRule` is on claimed `RegulaCore`. #42: `executionFailures` is claimed `RegulaCore.Policy` and runs `checkedExecutionFailures` (`ExecutionFailuresContract`: line `k` renders record `k`, none added or dropped, so the lines are empty iff `ExecutionOK`); accepted execution counts reach the report account. #43: the account runs `checkedSummary.run`, and an execution finding's rule is `executionRule failure.id` by its type (see #43 closure). | Decision, projection, failure text and counts **E**, extraction **T**; #42 (see #42 delivery). |
| F05 | [`CensusOK`, `requiredJobs`, `Plan`, `admitPlan`](../../lean/RegulaPolicy/Plan.lean); [`accept`, `Accepted.report`](../../lean/RegulaPolicy/Acceptance.lean). | Coordinator-fixed requests retain the full claim and separate environment inventories. Plan fields require exact derived jobs and claim; accepted evidence requires completeness and policy for those inputs. The actual freeze/finish callers, `Documentation.finishDocuments` and `FreshChecker.finishGraph` (both through `finalize`) consume this evidence. #7 delivered this integration (PR #33 with #45–#49). #41: the pure census assembly is on claimed `RegulaCore`. `surfaceAssignments`, `conformingProfile`, `histories`, the environment-job lookup and documentation-evidence selection have contracts. `accept` decides the other stages of `observations` again. | Core and linkage **E/T**; delivered by #7, census assembly claimed by #41. |
| F06 | [`ResultState.insertResult`, `collect`](../../lean/RegulaPolicy/ResultState.lean); [`finalize`](../../lean/RegulaPolicy/Acceptance.lean); [`Common.admitIndexedWorkerResults`](../../lean/Regula/Checker/Common.lean). | Insertion and full-sequence collection retain unknown, duplicate and binding refusals. `finalize_iff` relates actual raw occurrences to exact required-slot policy coverage; split IO collection/acceptance carries equality to this finalizer. #39: `admitIndexedWorkerResults` and `mapWorkQueue` run `checkedIndexedResults` (`IndexedResultsContract`). Packet decoding and worker execution remain distinct. #41: the decision was already claimed; `admitIndexedWorkerResults` decodes worker JSON and `mapWorkQueue` schedules in-process IO tasks, and both only render refusal text around it. #43: `Documentation.auditTasks` now runs `checkedIndexedResults` too, replacing a hand-written collection and unproved slot projection. Scheduling and concurrency are trusted. | Collection, finalization and worker projection **E**, transport **T**; #41 (delivered). |
| F07 | [`evaluate`, `checkedEvaluation`](../../lean/RegulaQualification/Checks.lean); [`Qualification.requireChecks`](../../lean/Regula/Qualification/Support.lean) calls `checkedEvaluation.run`. | Exact success iff all supplied assertions hold, first false assertion, and append/bind composition are already proved and consumed. The empty list succeeds. The evaluator cannot establish that an adapter supplied all needed assertions or truthful IO observations. Retain the implementation and inspect changed callers; do not rebuild a generic assertion framework. Success uses `Guards.listForM_eq_ok` and first refusal `RegulaPolicy.forM_eq_error` (`Traversal`), via `evaluate_eq_forM`; `checkedScope` uses the same two laws (#40, #41). Statements unchanged. Other callers (`RegulaQualification` `Json`, `Registry`, `Evidence`, `Native`) also run `checkedEvaluation.run`; none calls `evaluate` directly. | **E/T**; boundary account #41 (delivered). |
| F08 | [`AuditApp.RequiredContracts`, `checkedExecutable`](../../lean/AuditApp/Limiter.lean); [`Main`](../../lean/Main.lean) invokes the contract with `requiredContracts`. | Admission, updates, frames, exact success/refusal and strict composition concern the actual runner. The intrinsic bound alone would not prove those relations. [`Refinement`](../../lean/AuditApp/Refinement.lean) relates that runner to finite abstract paths. Retain as the reference pattern; it is not a theorem about checker orchestration or OS effects. | **E/T**; reuse #39; no selected application rewrite. |
| F09 | [`CanonicalSet` decisions and `ExactlyOne`](../../lean/RegulaPolicy/Collections.lean), used by admission/role/plan predicates; [`Economy.sumTo_csimp`](../../lean/Audit/Economy.lean) illustrates proved replacement. | Std supplies extensional collections and laws; adjacent-order and singleton-head equivalences already avoid redundant work. The arithmetic example proves one universal identity and an equality of executable definitions. Preserve duplicate-rejection versus set-normalization semantics and separate kernel reduction from compiler replacement. #40 retained these unchanged (see #40 delivery). | **E/T**; #40 review complete. |
| F10 | [`AxiomGate.auditSurfaceAt`, `auditSurface`, `auditFile`, `run`](../../lean/Regula/Checker/AxiomGate.lean); [`Documentation.auditBuiltProject`](../../lean/Regula/Checker/Documentation.lean), [`DocFenceAudit.run`](../../lean/Regula/Checker/DocFenceAudit.lean); sample [`policy` target](../../examples/build-lint/lakefile.lean). | Actual project/file/fence/build-lint success consumes accepted evidence; project-with-docs consumes same-snapshot `CombinedAccepted`. The [success-call-site map](policy-acceptance.md) distinguishes workers/help/local feedback and incremental modes from fresh conformance. The private fence finalizer consumes unchanged admitted task output. #42: every project, file, build-lint, combined and graph verdict line is `Account.pass`, and all account text is `Account.lines`, of `Account.account` on the accepted run; only a fresh project claim reads as whole-project acceptance. The documentation audit prints no PASS verdict, and its per-fence labels come from task results after an `AcceptedRun` exists (see #43 closure). #43: the acceptance-link record requires an `Account` and is written only after `run`'s outer recheck passed (see #43 closure). | Linkage **E/T**, delivered by #7; report projection **E** (claimed account), printing **T**; #42 (see #42 delivery). |
| F11 | [`Workspace.withRootWorkspace`](../../lean/Regula/Checker/Workspace.lean), `Lake.surfaceInventory`, [`SourceBinding`](../../lean/Regula/Checker/SourceBinding.lean), [`Admission.validate`](../../lean/Regula/Checker/Admission.lean), [`Frontend`](../../lean/Regula/Checker/Frontend.lean), [`ProducerReport`](../../lean/Regula/Checker/ProducerReport.lean). | Existing source/configuration, complete inventory, compiler and replay observations are bound to the accepted request and terminally reconciled. Policy validity does not authenticate their observations, filesystem, external processes or native code. Qualification and the trusted IO boundaries of [policy acceptance §1](policy-acceptance.md#1-observed-call-flow-and-every-success-boundary) and `Account.Trusted` remain required; no wholesale proof of these mechanisms is selected. #41 lists these as the remaining adapters of the narrowed exclusion. | Bound integration implemented; acquisition **T**; #7, explicit adapter boundary #41 (delivered). |
| F12 | [`ResultProtocol`](../../lean/Regula/Checker/ResultProtocol.lean), [`RuleDiagnostics`](../../lean/Regula/Checker/RuleDiagnostics.lean), existing gate/fence renderers and [`rule coverage`](rule-coverage.md). | Public accepted projections consume `AcceptedRun.report`; typed diagnostics or serialized success flags cannot reconstruct acceptance. #42: a `completed` status is `Account.Status.completed`, which requires an `Account`, the subtype of data projected from some `AcceptedRun`; `acceptance.account` JSON renders its coverage, checked relation, RG1007 contracts with open R-INTENT/R-INVARIANT, execution counts, fence kinds, trusted mechanisms and residual identifiers. Positive/rejection/teaching/incomplete distinctions remain. | Global linkage **E**, account **E** (claimed), JSON/text encoding **T**; #7 then #42 (see #42 delivery). |

## Read-back of the essential relations

These are readings of existing elaborated declarations, not proposed substitute
models. Quantifiers over the displayed inputs are universal unless explicitly
existential; implicit inputs and typeclass assumptions still matter.

- **Contract:** for any universe-polymorphic `α`, implementation `f : α` and
  predicate `R : α → Prop`, `ExecutableContract f R` contains `R f`.
  `run_eq` proves its `run = f`. Neither `R := fun _ => True` nor the name of a
  theorem establishes the intended requirement. A dependent result type may
  already establish that requirement; no duplicate proof field is needed.
- **Admission:** `admitInventory_exact ds ts h` assumes
  `h : InventoryValid ds ts` and returns exactly those arrays with their proof.
  It does not assert that arbitrary input is valid. `admitExecution_preserves`
  quantifies over roots and a returned inventory: a successful admission implies
  exact input-root retention and `ExecutionValid roots`. Nonanonymous/unique
  identities, coordinates and closure relations concern supplied data.
- **Classification:** `policyFor_none_iff i roles d r` equates no refusal with
  `d ∈ i.declarations ∧ DeclarationOK d r roles.native roles.helpers`.
  `foundationFor_iff` similarly equates each successful label with membership
  and `ClassificationOK`. `roles : Roles i` binds authorization to that
  inventory. `executionFailureRecords_empty_iff i c` equates no failures with
  `ExecutionOK i c`; in report mode trusted boundaries may remain, but unresolved
  paths do not satisfy the relation. No statement authenticates extraction.
- **Insertion:** `insertResult_success_iff` quantifies over key/payload types,
  `[Ord κ]`, `[TransOrd κ]`, `[LawfulEqOrd κ]`, fixed `required`, fixed `bound`,
  `[DecidableRel bound]`, current state, key and payload. Success exists iff the
  key is required, its lookup is empty, and binding holds. `insertResult_frame`
  additionally assumes a successful returned state and `other ≠ key`; every
  other lookup is unchanged. Public construction enforces subset/binding
  validity, not a history of insertions or latest-state/single-use discipline.
- **Acceptance:** for `c : Claim`, `i : Census`, `p : Plan c i`,
  `roles : CensusRoles i` and `s : ResultTable p`, `accept_iff` states
  `(∃ a, accept p roles s = .ok a) ↔ CompleteFor p s ∧ AllPolicyOK p roles s`.
  `CompleteFor` includes `PlanOK` and a completed observation at every required
  slot; `AllPolicyOK` requires its exact stage policy. `accepted_report_identity`
  preserves the claim/census/jobs/table. `accepted_covers_slot` assumes
  `slot < p.jobs.size` and gives one lookup, its full job key, policy, and unique
  lookup value. These do not assert that an arbitrary census is adequate or that
  some external worker truly executed. Negative/teaching expectation acceptance
  does not establish positive program conformance.
- **Assertion sequence:** `evaluate_success checks` is iff all supplied Boolean
  assertions are true. `evaluate_error checks label` supplies an existential
  satisfied prefix, first false check with that label, and unevaluated suffix.
  `evaluate_append` is exact `Except.bind` composition. Duplicate labels are
  permitted; an empty input satisfies the conjunction. Caller obligation coverage
  is separate from this evaluator's universal correctness.
- **Stateful example:** `runChecked_success ops l final` is iff `Fits ops l`
  and `final = run ops l`. `runChecked_error` identifies a fitting prefix whose
  next grant is full, with final state exactly that prefix's result. Earlier
  updates survive refusal; the suffix does not run. `checkedExecutable` quantifies
  over `RequiredContracts`, natural capacity and operation lists, and specifies
  exact positive-capacity admission plus that same runner. These are unbounded
  Lean naturals; truncated subtraction is justified by the relevant guards.
  They do not prove machine overflow behavior, elapsed time, concurrency,
  resource availability, external liveness or IO effects.

Canonical collection decisions require their actual comparator/equality laws.
Positions and slots are naturals; UTF-8 bytes, character positions and UTF-16
columns remain distinct in frontend/source adapters. Serialized identities and
ordered result occurrences may not be replaced by display strings, set equality
or hashes merely because those alternatives look equivalent.

## Selected successor deliverables

### #7: complete the existing acceptance integration

F05/F06/F10/F11/F12 retain #7's full scope. Its independent inventory and fixed
plan must determine required work before result admission. Every applicable
project, file, fence, build-lint and combined project-with-docs success must
consume evidence for that same request/mode. Internal worker success and
help/configuration output remain distinct. Preserve source admission, provenance,
all rule/example categories and unknown refusal; do not weaken global identity
to repair composition collisions. Use the existing PR, not a second collector.

The PR #33 CI repair retains this document's #38 baseline above and adds the
environment-indexed census, exact occurrence collector and public success-path
integration ([repair receipt](https://github.com/rbeauchamp/regula/blob/11e05c682ee76ddf9b7cd81fdb827b572469ed57/session/evidence/ci-environment-census.md)).
F05/F06/F10/F11/F12 are not marked closed until the applicable proof, independent
review, complete cold acceptance and diagnostic evidence pass and delivery is integrated.
The successor boundaries below remain unchanged; #39 is not a prerequisite for
completing #7. (#7 is now closed; see the #43 closure.)

### #39: close the selected component relations

The finite implementation set is: `Policy.admitScope`; the profile/request and
declaration/execution failure projections in `Policy`; the pure
`executionSummary` count relation; and any worker sequence/projection relation
not already discharged by #7 for `Common.admitIndexedWorkerResults`.

Admission success must retain the exact declaration/transcript inputs and roles
for that inventory. Completeness is conditional on the existing coordinate check
and inventory predicate; refusal must retain their current order. Projections
must preserve the selected request, diagnostic category/root/detail and order.
Summary counts describe their actual categories, including root-unresolved
entries and unresolved boundary entries; they are not counts of distinct runtime
paths. Worker output must cover exactly the requested slot sequence without
dropping duplicates, rebinding payloads or substituting a shorter plan.

Reuse F01/F07/F08 and #7's final APIs. Use reduction, existing proofs or required
proof-bearing interfaces where sufficient. No generic admission/state/runner DSL
is selected: current recurrence justifies shared evidence, not another framework.
Keep specifications independently reviewable so deleting a proof cannot silently
delete its requirement. Semantic review still owns adequacy and caller coverage.

#### #39 delivery

Each requirement is a named `Prop` definition, separate from its proof. A closed
`ExecutableContract` registration proves that definition about the actual
implementation. Callers execute the registration's `run`, which is definitionally
that implementation. Deleting the proof therefore breaks every caller, and a
weakened definition is visible to review.

| Registration | Implementation | Required relation | Callers |
| --- | --- | --- | --- |
| [`checkedScope`](../../lean/RegulaCore/Policy.lean) | private `admitScopeImpl` via `Policy.admitScope` | `ScopeContract`: (1) with `ts.toList = before ++ t :: after`, every `before` check `.ok ()` and `validateCoordinates ds t = .error e`, the result is `.error e`; (2) when every coordinate check succeeds, the result is exactly `(admitInventory ds ts).map (⟨·, authorize ·⟩)`; (3) success iff every coordinate check succeeds and `InventoryValid ds ts`; (4) success retains `ds` and `ts`. `Roles.eq_authorize` already fixes the roles. | project, file, fence, rule-example, acceptance freeze, environment census and self-test inspection |
| `checkedRequest` | private `requestImpl` via `Policy.request` | `RequestContract`: no claim gives `.classification`; `.teaching` iff compiler-trusting; `.conforming q` iff `profile.toString = q.spelling`. `Profile.parse?_eq_some_iff` states the spelling input meaning. | `ruleFor`, `ruleForMember` (#40); `Acceptance.conformingProfile` |
| `checkedRule` | private `ruleForImpl` via `Policy.ruleFor` | `RuleContract`: `none` iff `policyFor … (request claim) = none`, and `some (ruleForFailure f)` iff that decision is `some f`. With `ruleForFailure_injective` and `policyFor_ordered`, the rule is the first failed requirement's. `reasonFor_eq_some_iff` gives the same relation for applicability text. | `reasonFor`; through `MemberRuleContract` (#40), the project/file gates, fence and rule-example audits now run `checkedMemberRule` |
| [`checkedSummary`](../../lean/RegulaPolicy/Execution.lean) | `executionSummary`, now a named `ExecutionSummary` | `SummaryContract`: roots and boundaries are observation counts, checked/trusted are filter counts, and `unresolved` equals the number of `executionUnresolved` records of `executionFailureRecords` for every claim. `executionSummary_partition` proves checked + trusted + unresolved boundaries = boundaries. | `Policy.executionSummary`, both gate renderers; since #43 also `Account.accountImpl` |
| [`checkedIndexedResults`](../../lean/RegulaPolicy/ResultState.lean) | `@admitIndexedResults`, universe-fixed `α : Type` | `IndexedResultsContract`: `.ok out` iff `out.size = count`, every `binding i out[i]`, and `responses.Perm ((List.range count).zip out.toList)`. Duplicates, unknown or missing slots, rebound payloads and shorter plans are refused. Every satisfying array is returned. | `Common.admitIndexedWorkerResults` (compile batch), `Common.mapWorkQueue`; since #43 also `Documentation.auditTasks` |

The `Policy.ExecutionFailure` record was replaced by an alias of the decision's
own record type. The gate consumes those records, so kind, root, detail and order
are preserved by identity. The total bridge `executionRule` is injective, and
`RuleDiagnostics.executionFinding` no longer has an unreachable wrong-rule branch.
`SourceAudit.compileBatch` no longer repeats the size and binding checks that
`checkedIndexedResults` proves. It keeps the IO check that each source snapshot
is unchanged.

Limits: `ScopeContract` is conditional on the existing `validateCoordinates`
check and on `InventoryValid`. Neither authenticates the supplied transcripts.
`IndexedResultsContract` concerns decoded responses; JSON transport, child
completion and payload truth remain trusted. The `Policy` registrations are in
the excluded operational `Regula` library. They are kernel-checked by
`lake build` (warnings are errors), but the axiom gate does not audit them until
#41 moves them to a claimed surface (done; see #41 delivery). The ordinary gate recognizes `checkedSummary`
and `checkedIndexedResults` on `RegulaPolicy`; the latter exercises a
type-polymorphic implementation. Recognition is unchanged.

Exact axiom sets on Lean 4.34.0: `{}` for `ruleForFailure_injective`,
`executionRule_injective` and `Profile.parse?_eq_some_iff`. Every other new
theorem above has `{propext, Classical.choice, Quot.sound}`.

No new scenario control was added. The existing invalid-evidence and restored
controls on the actual `admitIndexedWorkerResults` consumer (`PolicyQualification.transport`)
still pass. They qualify detection; they are not correctness evidence. The
contracts above are the correctness evidence.

### #40: complete a bounded economy pass

Review these four candidates and either implement a justified simplification or
record the specific reason to retain the current form:

1. `CompleteFor` already uses `p.valid` through `completeFor_iff_slots`, with
   decision and finalizer correspondence proofs. The CI repair also retains
   admitted role receipts instead of reauthorizing at each job, with exact
   equality to recomputation. These are implemented; do not repeat them as
   missing work. Keep runtime and hosted evidence scoped to their receipts.
2. Repeated inventory membership in `policyFor`/`foundationFor` and their callers:
   investigate a reused lawful membership decision/index with proved equivalence,
   preserving invalid-inventory precedence and the fixed observed inventory.
3. `Checks.evaluate_error`/`evaluate_append` and the selected worker fold:
   reuse existing list/monadic laws where they simplify exact first-refusal and
   composition proofs. Do not rewrite the already proved evaluator solely for
   shorter source; `mvcgen` is optional, not a migration objective.
4. Existing `CanonicalSet`/`ExactlyOne` decisions and `Audit.Economy`: retain and
   reuse their equivalences, Std laws, and analytic proof pattern. Do not repeat
   a previously completed optimization or replace the teaching recursion whose
   elaboration/reduction behavior is explicitly the subject of the example.

No speedup is established by this candidate list. Any new cost claim identifies
elaboration/search, artifact, kernel or native execution cost. Derive eliminated
work first; measure only an unresolved empirical decision with a stated budget
and criterion. Preserve the required foundation profile and exact statements.

#### #40 delivery

The bounded candidate set is the four candidates above, plus the uniqueness and
traversal proofs the issue lists. Two changes were selected; the others are
retained for the reasons given.

| Candidate | Decision | Before → after, and reason |
| --- | --- | --- |
| 1. `CompleteFor` / `PlanOK` | Retained | Already derived from `p.valid` (`completeFor_iff_slots`); role receipts are retained, not reauthorized. Nothing left to remove. |
| 2. Inventory membership in `policyFor`/`foundationFor` callers | **Replaced** | Every product per-declaration caller iterated the inventory it had just admitted, yet each call re-decided `d ∈ i.declarations`. The new member forms take the membership proof from iteration (`for h : d in inventory.declarations`), so no scan runs. `policyFor`/`foundationFor` are unchanged for arbitrary input, including invalid-inventory precedence. |
| 3a. Pure `Except` traversal proofs | **Replaced** | `Policy`'s private `forM_ok`/`forM_first` repeated the induction behind `evaluate_success`/`evaluate_error`. Both now reuse `RegulaQualification.forM_eq_ok`/`forM_eq_error` (#41: `forM_eq_error` is in `RegulaPolicy.Traversal`, and the success law is `RegulaPolicy.Guards.listForM_eq_ok`); `evaluate_eq_forM` identifies the unchanged recursive `evaluate` with `checks.forM Check.step`. `forM_first` (one direction) became the `←` half of an exact first-refusal equivalence. |
| 3b. `evaluate_append` via core `List.forM_append` | Retained | The core law is for any lawful monad; using it raises this theorem's exact set from `{propext}` to `{propext, Quot.sound}`. The five-line induction keeps `{propext}`. |
| 3c. Worker fold `mapM_ok`, `Template.mapM_related` | Retained | They prove different conclusions: indexed pointwise versus `List.Forall₂`. A shared `Forall₂` form would import Batteries into `RegulaPolicy` solely to shorten proofs. #39 already gave both worker callers one permutation characterization. |
| 3d. `Std.Do`/`mvcgen` | Not adopted | The selected programs are pure `Except` traversals, and the laws above discharge them directly. |
| 4. `CanonicalSet`/`ExactlyOne`, `Audit.Economy` | Retained | These equivalences are already the derived decisions (adjacent order, singleton head, `sumTo_csimp`). The teaching recursion is itself the subject. |
| Uniqueness (`distinct_iff`) | Retained | This is already a hash-set cardinality decision with a proved equivalence to `Pairwise (· ≠ ·)`. |
| Verbose `classify` listing in `auditSurface` | Retained | It lists a filtered, sorted copy, so membership would need a `qsort` permutation proof. The listing is verbose-only. |

New registrations. Each requirement is a named `Prop`, separate from its proof:

| Registration | Implementation | Required relation | Callers |
| --- | --- | --- | --- |
| [`checkedMemberFailure`](../../lean/RegulaPolicy/Decision.lean) | `memberFailure i roles d member request := declarationFailure d request roles.native roles.helpers` | `MemberFailureContract`: for all `i`, `roles : Roles i`, `d`, `member : d ∈ i.declarations` and `request`, the result equals `policyFor i roles d request`. | `Policy.ruleForMember`; `checkedEditorDecision` (`Linter.Rules.declarations`, since #14) |
| `checkedMemberFoundation` | `memberFoundation i roles d member := labelOf d.axioms roles.native` | `MemberFoundationContract`: `foundationFor i roles d = .ok (memberFoundation i roles d member)` for every member; the member form has no error case. | `Policy.labelOfMember`, and through it `classifyMember` |
| [`checkedMemberRule`](../../lean/RegulaCore/Policy.lean) | private `ruleForMemberImpl` via `Policy.ruleForMember decl claim scope member` | `MemberRuleContract`: equals `ruleFor decl claim scope` for every `member : decl ∈ scope.inventory.declarations`. Therefore `RuleContract` and first-failure precedence carry over unchanged. | project gate `auditSurfaceAt`, file gate `auditFile`, `Documentation.assessPositive`, rule-example policy audit, self-test `renderFileAudit` |

Supporting theorems are `labelOf_member` (`labelOf decl scope = .ok (labelOfMember …)`) and
`classifyMember_eq` (`classifyMember decl scope member = classify decl scope`).
The shared traversal laws are `forM_eq_ok`/`forM_eq_error`; since #41 they are
[`Guards.listForM_eq_ok`](../../lean/RegulaPolicy/Guards.lean) and
[`forM_eq_error`](../../lean/RegulaPolicy/Traversal.lean). The first
is success iff every element succeeds; the second is refusal with `e` iff some split
`before ++ x :: after` has every `before` element succeeding and `f x = .error e`.
`EvaluationContract` and `ScopeContract` are unchanged.

Caller linkage. `ScopeContract` (4) gives `scope.inventory.declarations = ds` for the
array each caller admitted, and `admitInventory_exact` does the same for the linter.
So iterating the inventory visits the same sequence as before. Each element's rule,
reason and classification are equal by the contracts above. IO effects in the
loop bodies keep their order, and diagnostics, findings and snapshots are unchanged.
The file gate now computes one rule per declaration; its reason is `reasonFor`'s by
definition. Its unreachable "internal rule classification mismatch" branch is gone.

Structural saving (native execution only; no timing is claimed or needed). The
derived `DecidableEq Declaration` has no pointer shortcut. Deciding membership of the
`k`-th element therefore compares it with each of the `k` earlier records, which fail at
`name`. It then compares all fields of the equal record, including strings and arrays.
One decision over each of `n` members did `n(n+1)/2` such comparisons, and `n` of them
were full-record. Now it does none. Per declaration, the project gate removed one scan
plus two per violation. The file gate removed two, plus, per violation,
two scans and one duplicate rule computation; its self-test mirror removed two. `assessPositive` removed two per unit
declaration, the rule-example audit removed one plus one per violation, and the editor
snapshot removed one. The rule-reference prototype, since removed, still used
`reasonFor` at the time. For proofs, the saving is reuse, not size: one pair of traversal
inductions now serves the evaluator and scope admission, where two separate ones did
before. Source lines grew, since `forM_eq_error` proves both directions and
`forM_first` proved one. No artifact size, elaboration time or kernel time was measured,
and none is claimed. No compiler replacement (`csimp`, `implemented_by`) was added.

Exact axiom sets on Lean 4.34.0 are as follows. `{}` for `evaluate_eq_forM`.
`{propext}` for `evaluate_append`, unchanged. `{propext, Quot.sound}` for `forM_eq_ok`,
`forM_eq_error`, `evaluate_success`, `evaluate_error` and `checkedEvaluation`; the last
three are unchanged. `{propext, Classical.choice, Quot.sound}` for
`checkedMemberFailure`, `checkedMemberFoundation`, `checkedMemberRule`, `labelOf_member`,
`classifyMember_eq` and `checkedScope`, the last unchanged. All are within each
library's Standard-Logical claim.

Evidence (local, warm, observations only). Each row names the head or base it was
observed on. None is evidence for the final rebased head, whose acceptance is its
exact-head CI run.

| Check | Observed on | Result |
| --- | --- | --- |
| `./scripts/verify.sh` | this change over base `4aa6c89` | PASS, 121 s. 40 owned modules, 5377 declarations. The gate recognizes `checkedMemberFailure` and `checkedMemberFoundation` on `RegulaPolicy`. |
| `./scripts/verify.sh docs` | this change over base `4aa6c89` | PASS, 126 s (70/70, 23/23, 1/1) |
| `./scripts/verify.sh` | head `2f090ab` (this change over `8de0e85`) | PASS, 121 s. 41 owned modules, 5431 declarations. The gate recognizes `checkedMemberFailure` and `checkedMemberFoundation`. |
| `./scripts/verify.sh docs` | head `2f090ab` (this change over `8de0e85`) | PASS, 82 s |
| `diagnostics fixtures` | this change over base `4aa6c89` | PASS, 173 s |
| `diagnostics cli` | this change over base `4aa6c89` | PASS, 358 s (60 `axiomGate --file` invocations: file gate and self-test mirror) |
| `diagnostics rule-examples 1/2`, `2/2` | this change over base `4aa6c89` | PASS, 130 s and 92 s (rule-example policy audit) |
| `diagnostics build-policy` | this change over base `4aa6c89` | PASS, 282 s (`--build-lint` through the changed project-gate loop) |

These diagnostics qualify detection on the changed paths; they are not correctness
evidence. The two acceptance steps exercise the project gate and `assessPositive`,
and the editor linter (`Linter.Rules`) through the ordinary step's native-linter
qualification. The structural, environments, producers and history diagnostics were not
run locally, since their capabilities are unchanged; CI Diagnostics covers them.
Axiom sets came from `#print axioms` on the built modules.

Limits. The member forms decide nothing about non-members; `policyFor` remains the API
for arbitrary input. The new core registrations are on the claimed `RegulaPolicy`
surface. `checkedMemberRule` shares the #39 `Policy` limit: it is kernel-checked by
`lake build` but not audited by the gate until #41. The shared traversal laws live in
`RegulaQualification.Checks`, which `Checker/Policy.lean` imports; a #41 move of
`checkedScope` into a claimed policy module must move or restate them. (#41 moved `forM_eq_error` and reused `Guards.listForM_eq_ok`; see above.) No scenario control was added.
The contracts are the correctness evidence; qualification detects, it does not prove.

### #41: bring the selected pure adapters into the conforming surface

The migration set is the pure implementations selected in #39, plus the accepted
assembly/projection definitions delivered by #7 where they are still excluded.
Reconcile this set after #7/#39; definitions already conforming need no duplicate
move. Separate reusable pure policy projections from frontend/IO imports and
connect their callers. Narrow manifest exclusions only with supported coverage;
file moves or theorem wrappers alone are not closure. F11's extraction, source,
kernel-replay and process mechanisms retain explicit trusted boundaries and
their existing qualification requirements. No wholesale migration of every
operational helper, parser or renderer is a prerequisite.

#### #41 delivery

The exclusion held the selected pure components in `Checker/Policy.lean` and #7's pure
census assembly in `Checker/Acceptance.lean`. They now live in a new claimed library, [`RegulaCore`](../../lean/RegulaCore/Policy.lean):
a Lake `.submodules` glob, manifest claim `standard-logical`, execution `report`. The
policy library may not import the rule registry (see
[policy acceptance §5](policy-acceptance.md#5-pure-module-boundary-and-migration)), and
the rule projections need it. So the registry moved with them. Moved declarations keep
their names and namespaces. These call sites changed:

- `AxiomGate` renders `surface.execution.spelling`, since `Manifest.Surface.execution`
  is now `RegulaPolicy.ExecutionClaim` itself.
- `Acceptance.historyObservations` only concatenates the reports' outcomes and runs
  `checkedHistories`.
- `Frontend.validateCoordinates` is now `checkedCoordinates.run lspUtf16Column`, and
  `Diagnostic.sourceFromReport` is `sourceFromReportWith lspUtf16Column`.
- `observations` runs `checkedEnvironmentJob` for environment jobs.
- `checkedScope` and `evaluate_success` use `Guards.listForM_eq_ok` for the success law.

| Component | Now in | Change and reason |
| --- | --- | --- |
| `PolicyScope`, `checkedScope` (`ScopeContract`); the adapter `Policy.admitScope` stays in `Checker/Policy.lean` | `RegulaCore.Policy` | `ScopeContract` now quantifies over every coordinate check `check : CoordinateCheck`, with the same four clauses. The adapter `Policy.admitScope ds ts` is `checkedScope.run Frontend.validateCoordinates ds ts`. Instantiating the contract at that check gives the #39 relation exactly. |
| `validateCoordinates`, now `coordinateCheck` (`checkedCoordinates`, `CoordinateContract`) | [`RegulaCore.Coordinates`](../../lean/RegulaCore/Coordinates.lean) | New contract, for every UTF-16 column function. Success holds exactly when `CoordinatesAgree`: each command's `added` equals its `addedDeclarations` names; each command, evaluator and binding range has positive lines, round-trips through the transcript's `FileMap` at both ends, and starts no later than it stops; and each declaration of the transcript's module has ranges that convert against the snapshot (`RangesConvert`). Refusal is exactly the message of the first unmet entry of `coordinateObligations`, listed in traversal order (`Decides`, `FirstUnmet`). The loops became `List.forM` traversals, and the inventory guard became `commandInventory`. Order and messages are unchanged. |
| `SourceCandidate`, `admitSource`, `SourceLocation`; `sourceFromReport`'s conversion, now `sourceFromReportWith` with `reportedRange` (`reportedRange_eq`) | [`RegulaCore.Source`](../../lean/RegulaCore/Source.lean) | Moved from `Regula.Diagnostic`, with the UTF-16 column as a parameter `Utf16Column`. `Diagnostic` keeps `lspUtf16Column` (Lean's `FileMap.leanPosToLspPos`), `sourceFromReport` at that column, and the LSP range renderers. The module imports only `Lean.Data.Position` and the policy domain. |
| `Profile`, `request` (`checkedRequest`), `Profile.parse?_eq_some_iff` | `RegulaCore.Policy` | Moved unchanged. |
| `ruleFor` (`checkedRule`), `ruleForMember` (`checkedMemberRule`), `reasonFor`, `reasonFor_eq_some_iff`, `applicability_ruleForFailure_injective` | `RegulaCore.Policy` | Moved unchanged. |
| `labelOf`, `labelOfMember`, `labelOf_member` | `RegulaCore.Policy` | Moved unchanged. |
| `executionRule`, `executionRule_injective` | `RegulaCore.Policy` | Moved unchanged. |
| Registry `RuleId`, `Rule` (`ruleForFailure`, `descriptor`) | `RegulaCore.RuleId`, `RegulaCore.Rule` | Moved from `Regula.RuleId`/`Regula.Rule`. `Regula.Diagnostic` imports the new module. |
| `forM_eq_error` | [`RegulaPolicy.Traversal`](../../lean/RegulaPolicy/Traversal.lean) | Moved from `RegulaQualification.Checks`, which now imports it. The statement is unchanged. The module imports only `Init`. The success law `forM_eq_ok` was not moved: `checkedScope` and `evaluate_success` use the existing `RegulaPolicy.Guards.listForM_eq_ok` instead. |
| `conformingProfile` (`checkedConformingProfile`, `ConformingProfileContract`) | [`RegulaCore.Assembly`](../../lean/RegulaCore/Assembly.lean) | New contract: success exactly with the conforming profile of the same spelling, and refusal exactly for compiler-trusting. It is proved by reduction to the new `request_contract` (`RequestContract` stated about `request`). Nothing downstream rechecks a surface's profile. |
| `surfaceAssignments` (`checkedSurfaceAssignments`, `SurfaceAssignmentsContract`) | `RegulaCore.Assembly` | New contract: success exactly with one `SurfaceAssigned` claim surface per manifest surface, in order. That relation fixes the library name, the execution claim, the profile of the manifest's spelling, and the modules: the first same-named Lake library's modules followed by each claimed executable's first same-named root. The implementation was restated as a per-surface `mapM` with the same refusals and messages. Nothing downstream rechecks profile or execution. |
| `configuredTargets`, `discoveredTargets` | `RegulaCore.Assembly` | Moved unchanged, without a contract. They are total field projections of the manifest and Lake records, so a contract would restate them. The claimed `TargetPartitionOK` checks them against each other and against the contracted claim surfaces. |
| `FrozenEnvironment`, `Frozen`, `frozenEnvironmentRoles` (`_eq`), `modulePresence` (`_iff`), `observations` | `RegulaCore.Assembly` | Moved unchanged except as below and in the next two rows, without a new contract of their own. The claimed `accept` decides again every stage but documentation presence. `ResultBound` and `PolicyOK` fix key, snapshot and completion, and `StageOK`/`LocalStageOK` bind each record to its job's subject and census; for example, a declaration must be in the inventory with the key's module and name. For those stages a wrong choice is refused, and the remaining risk is a spurious refusal. |
| Evidence selection, now `checkedEnvironmentEvidence` (`DocumentationEvidenceContract`) | `RegulaCore.Assembly` | New soundness contract, because `LocalStageOK` checks only that a docstring is present, not whose it is. A success reports the presence of the only record with the job's module name, or with its module and declaration names; a refusal fails closed. `observations` runs this registration on the environment `checkedEnvironmentJob` selects. |
| Environment lookup, now `checkedEnvironmentJob` (`EnvironmentJobContract`) | `RegulaCore.Assembly` | New contract for every environment job, documentation slots included. Success means exactly one frozen environment has the job's `census.request.key`, and the evidence is that environment's `checkedEnvironmentEvidence` result for the job's stage and subject. A missing or duplicate key is refused. `observations` runs this registration. |
| History assembly, now `histories` (`checkedHistories`, `HistoriesContract`); `ProducerReport.HistoryOutcome` | `RegulaCore.Assembly` | New contract: success exactly when every outcome completed, with one exact copy (module, path, before and after sources, replacement edges) per outcome in order. An unavailable history is refused, never dropped. `HistoryOK` cannot tell whether the replacement edges were copied faithfully, so this is not decided again downstream. `historyObservations` now only concatenates the reports' outcomes and runs this. The unsupported-evaluator list stays empty here: the operational `--replacement-history-worker` refuses a module with unsupported evaluators, so such a history arrives unavailable and is refused. |
| Manifest records (`Manifest.Surface`, `Manifest`, exclusions) and Lake inventory records (`Lake.SurfaceInventory` and parts) | `RegulaCore.Assembly` | Data types moved so the contracts can state them. Parsing and Lake loading stay in `Checker/Manifest.lean` and `Checker/Lake.lean`. |
| `mapM_eq_ok` | `RegulaPolicy.Traversal` | Was private `mapM_ok` in `ResultState`. It is now shared by `checkedIndexedResults`, `checkedSurfaceAssignments` and `checkedHistories`; the statement is unchanged. |
| `checkedSummary`, `checkedIndexedResults`, `checkedMemberFailure`, `checkedMemberFoundation`; #7's `Plan`, `ResultState`, `accept`, `finalize`, `combineAccepted` | `RegulaPolicy` | Already claimed, so not moved again. |

The narrowed exclusion keeps the following. Each item is a total projection, observes
something external, or only renders text around a claimed decision.

- `Diagnostic.lspUtf16Column` is Lean's `FileMap.leanPosToLspPos` column.
  `Frontend.validateCoordinates` and `sourceFromReport` pass it to the claimed
  `checkedCoordinates` and `sourceFromReportWith`. It stays outside the claimed closure
  because `Lean.Data.Lsp.Utf16` imports `Lean.Environment`. The contracts hold for every
  column function, so they do not verify Lean's UTF-16 arithmetic. That arithmetic is a
  pinned toolchain function, trusted in the same way as `FileMap.toPosition`, which is
  `partial` and which the contracts treat as opaque.
- `Checker/Acceptance.historyObservations` only concatenates each report's outcomes
  (`flatMap`) before running `checkedHistories`.
- `Checker/Policy.lean` keeps the text renderers `executionFailures`,
  `describeBoundary`, `classify` and `classifyMember`, with `classifyMember_eq`. (#42 later
  moved `executionFailures` to claimed `RegulaCore.Policy`.)
- `Common.admitIndexedWorkerResults` decodes worker JSON and `mapWorkQueue` schedules
  in-process IO tasks; both render refusal text around the claimed `checkedIndexedResults`.
- `Checker/Acceptance`'s `freeze`, `finish`, `buildObservation` and `sourceSnapshots`
  read IO-derived records and hand them to the claimed plan and finalizer.
  `ResultProtocol`'s JSON projections are #42's reporting work.
- The F11 mechanisms stay trusted: Workspace, Lake inventory, SourceBinding, Admission
  replay, Frontend transcript production, ProducerReport and Probe. They use `IO`,
  `Environment` or `Meta`.
- The #51/#52 transport-admission theorems were not in the #39 selection. They keep
  their in-module `collectAxioms` ceiling.

Caller linkage. Every #39/#40 caller still executes the same registration's `run`.
`Policy.admitScope` now passes the frontend check, itself `checkedCoordinates.run`, to
the core registration. `sourceFromReport` callers (`Findings`, and `DiagnosticCodec`
and `RegistryChecks` through `admitSource`) run the moved claimed definitions. The
unchanged callers now run the new registrations. `surfaceAssignments` is called by the
project gate `auditSurfaceAt` (including build-lint), `FreshChecker` and the
environment-census qualification. `conformingProfile` is called by the file gate. All seven excluded checker executables reach these definitions through
`Checker.Policy`, by way of `Manifest` and `Lake`: `axiomGate`, `docFenceAudit`,
`freshChecker`, `checkerSelftest`, `qualify`, `ruleExamples` and
`ruleExampleQualification`. The claimed `auditApp` does not use them.

Coverage, from ordinary acceptance on Lean 4.34.0 and Mathlib `5ed29652`, on this
delivery's final Lean sources rebased onto main `ecd78bc`:

- 6 claimed libraries, 49 owned modules and 6586 owned declarations. #40's head
  `e2d00b5` had 41 modules and 5446 declarations. Main added
  `RegulaQualification.CorpusWindow` in #55.
- The excluded `Regula` library has 71 modules, down from 73 on main.
- `RegulaCore` has 6 modules and 1064 attributed declarations: `Assembly` 381,
  `Coordinates` 61, `Policy` 188, `Rule` 293, `RuleId` 96 and `Source` 45.
- Exact axiom sets across those 1064: 768 `{}`, 108 `{propext}`, 13
  `{propext, Quot.sound}` and 175 `{propext, Classical.choice, Quot.sound}`.
- The gate recognizes ten registrations on `RegulaCore`: `checkedScope`,
  `checkedRequest`, `checkedRule`, `checkedMemberRule`, `checkedCoordinates`,
  `checkedConformingProfile`, `checkedSurfaceAssignments`, `checkedHistories`,
  `checkedEnvironmentEvidence` and `checkedEnvironmentJob`.
- Execution coverage for `RegulaCore`: 408 roots and 3242 boundaries (489 checked,
  2753 trusted), 0 unresolved. The trusted boundaries are reported Lean core and runtime
  mechanisms, not verified ones.

Named axiom sets, from `#print axioms`:

| Set | Declarations |
| --- | --- |
| `{}` | `Profile.parse?_eq_some_iff`, `executionRule_injective`, `ruleForFailure_injective`, `RuleId.parse_spelling`, `RuleId.all_nodup` |
| `{propext}` | `RuleId.spelling_injective`, `RuleId.mem_all`, `modulePresence_iff`, `decides_pure`, `decides_guard` |
| `{propext, Quot.sound}` | `forM_eq_error`, `RuleId.route_injective`; `Guards.listForM_eq_ok`, `evaluate_success`, `evaluate_error`, `checkedEvaluation` (unchanged) |
| `{propext, Classical.choice, Quot.sound}` | `checkedCoordinates`, `coordinateCheck_decides`, `coordinateObligations_hold`, `commandCoordinates_decides`, `rangeCoordinates_decides`, `sourceFromReportWith_decides`, `reportedRange_eq`, `Decides.ok_iff`, `Decides.bind`, `decides_forM`, `decides_forM_map`, `firstUnmet_append`, `all_iff_not_firstUnmet`, `checkedEnvironmentJob`, `checkedScope`, `checkedRequest`, `request_contract`, `checkedRule`, `checkedMemberRule`, `reasonFor_eq_some_iff`, `applicability_ruleForFailure_injective`, `labelOf_member`, `checkedConformingProfile`, `checkedSurfaceAssignments`, `checkedHistories`, `checkedEnvironmentEvidence`, `frozenEnvironmentRoles_eq`, `mapM_eq_ok` |

Moved declarations keep the sets they had before the move. `checkedScope` and
`evaluate_success` keep theirs after switching to `Guards.listForM_eq_ok`.

Limits. The core contracts concern supplied declarations, transcripts, and manifest,
Lake and history records. They do not authenticate how transcript bytes were acquired, and
they do not verify Lean's UTF-16 column function. They also do not authenticate manifest
parsing, Lake loading, environment extraction, compiler or
worker processes, JSON transport, or native code. Report mode reports the trusted
runtime boundaries; it does not verify them. `classifyMember_eq` and the adapter
renderers remain kernel-checked by `lake build` only. No scenario control was added:
the contracts are the correctness evidence, and the existing controls qualify
detection.

Evidence (local, warm, observations only). "Final" means this delivery's Lean sources
rebased onto main `ecd78bc`. `16d694b` preceded the coordinate, environment-job, history
and documentation-evidence contracts, the traversal-law collapse and the rebase:

| Check | Lean sources | Result |
| --- | --- | --- |
| `./scripts/verify.sh` | final | PASS, 172 s. 6 claimed libraries, 49 owned modules, 6586 declarations; all ten `RegulaCore` registrations recognized |
| `./scripts/verify.sh docs` | final | PASS, 178 s (70/70, 23/23, 1/1); only this table changed afterwards |
| `checkerSelftest --forced-collector-only` | final | PASS, 313 s (fresh positive, excluded-source refusal, restored) |
| `diagnostics fixtures` | final | PASS, 129 s |
| `diagnostics environments` | `16d694b` | PASS, 204 s |
| `diagnostics build-policy` | `16d694b` | PASS, 266 s |
| `diagnostics structural` | `16d694b` | FAIL, 211 s; pre-existing: the same 37 failure labels as main `fa62dd1` (300 s) |

At `16d694b` the `structural` partition failed with 37 failures, and main `fa62dd1`
failed with the same 37 failure labels. Its `structuralManifestText` then omitted
libraries that the repository had, so most controls were refused as an unclassified
library (RG2002) before reaching their intended diagnostic. The rest (the unknown-library
wording, correspondence and init-module-origin controls) failed the same way on main. It
therefore gave no import-boundary evidence for this change. The partition's later repair
is recorded under "Structural partition status" in
[Lean qualification tooling](lean-qualification.md#control-inventory).

For the changed import boundary, the existing `checkerSelftest --forced-collector-only`
control uses the real manifest, including `RegulaCore`. It runs a fresh positive,
then refuses a claimed module that imports the excluded `Regula.Collect`, then runs
a restored positive. Its mutation targets `AuditApp`, not `RegulaCore`. It covers
the new surface only because the gate applies one import check to every claimed
library.

The fixtures partition runs the policy fixtures through `admitScope` and
`ruleForMember`. The environments partition covers packaging, including external
adoption of the changed Lake package. The build-policy partition runs `--build-lint`
through the project gate's census assembly. `cli` was not run: the file gate reaches
the same definitions through a front door this change does not touch. Ordinary
acceptance runs the final history and evidence assembly on the real project. That
includes the environment-census qualification's omitted, duplicate and rebound
environment and source-binding mutations. CI Diagnostics runs producers, history and
both rule-example shards.

### #42 and #43: report and reconcile the established scope

#42 covers the existing project/file/fence/build-lint result projections and
human/machine reporting in F04/F10/F12. Derive scope and mechanical success from
the accepted evidence, retain exact implementation/requirement identity and
foundation/execution boundaries, and expose the relevant existing residual-review
identifiers. A displayed identifier is not a completed review. Preserve stable
diagnostics and source attribution; version any necessary transport change with
its actual consumers. Full editor workflows and website delivery stay in Project 8.

#### #42 delivery

One report account, [`RegulaCore.Account`](../../lean/RegulaCore/Account.lean)
(namespace `Regula.Checker.Account`, claimed `standard-logical`, execution `report`),
is the only source of rendered success. `account run` runs the registration
`checkedAccount : ExecutableContract accountImpl AccountContract` on one `AcceptedRun`; no
report path evaluates acceptance again.

- `AccountContract`, stated apart from its proof, fixes the account's meaning for every
  claim and accepted run. Mode, scope, surfaces, toolchain and job count are the accepted
  report's own. `coverage` is `coverageOf` the claim's mode; `coverage_fresh_iff` derives
  that it is `freshWholeProject` iff the claim is a fresh project claim, which is always
  project-scoped (`fresh_scope`). `contracts` are exactly the census
  environments' RG1007 registrations: registration, module, implementation root and the
  collector's rendered requirement. `execution` is `executionSummary` of each accepted
  environment in order. The fence counts partition the accepted fences by expectation.
  `trusted` is `Trusted.all`. Every `Residual` of `rule-coverage.md` is unresolved, and
  R-GRAPH is listed only for a serialized-graph claim.
- `Account` is the subtype of data equal to `checkedAccount.run run` for some run.
  `Account.accepted` gives that run with `CompleteFor ∧ AllPolicyOK`, the relation of
  `RegulaPolicy.accept_iff` (named by `acceptanceTheorem`).
- `Status` (`completed (a : Account)`, `rejected`, `incomplete`, `classified`) replaces
  `ResultProtocol.Status`. `Status.completed_accepted` proves that a status spelled
  `completed` holds an account and that account's run. Missing, incomplete or unsupported
  evidence has no `AcceptedRun`, so it cannot be rendered `completed`. That the run is the
  current request's, not an earlier or unrelated accepted run, is each caller's binding,
  checked by inspection; `resultJson` takes a completed envelope's `mode` from the account.
- By inspection of the call sites, every project, file, build-lint, combined and graph
  verdict line is `Account.pass label` (the documentation audit prints none), and
  `Account.lines` renders the
  checked relation, each contract with its open R-INTENT/R-INVARIANT, execution counts,
  fence kinds, trusted mechanisms and residual identifiers. `Coverage.text_eq_fresh_iff`
  proves only fresh whole-project coverage uses the whole-project wording. The former
  "exact Lake surfaces conform" is removed as an overstatement of a mechanical result.
- `ResultProtocol.accountJson` renders the account as the additive `acceptance.account`
  member, then within result schema 1: coverage, the acceptance theorem and job count, contracts,
  execution counts, fence kinds, trusted mechanisms and residual identifiers (mode, scope,
  surfaces and toolchain are already in `acceptance`). These renderers are unproved adapter
  text. No existing key changed; the
  rule-example projection already drops `acceptance`, and the other consumers test
  only its presence. The top-level `unresolved` array keeps its
  meaning, missing mechanical evidence; review obligations are `unresolvedReview`.
- `executionFailures` moved to claimed `RegulaCore.Policy` and runs
  `checkedExecutionFailures` (`ExecutionFailuresContract`).

Callers: `AxiomGate.auditSurfaceAt` (fresh, incremental and build-lint), `auditSurface`
(combined `--with-docs`), `auditFile`, `Documentation.auditBuiltProject` (through
`DocFenceAudit.run` and the combined audit), `FreshChecker.run`, `RuleExamples.documentation`
and `ResultProtocol.acceptedValue`/`acceptedJson`. The per-declaration "executable contract"
lines are replaced by the account's contract lines. `build policy linter: PASS` remains a
prefix of the build-lint success line.

Limits. The account proves which fields project the accepted run; the IO, printing and JSON
encoding around it stay adapter code in the excluded `Regula` library, and nothing here
authenticates the observations the run consumed. `Trusted` names fixed mechanism classes,
not a proof that the list is complete. Printing a residual identifier records an open
obligation; no type records a completed review. Library-reuse and proof-economy advice
remain review, not hard errors.

Evidence on Lean 4.34.0 (`293d5d0c`), Mathlib `5ed29652`. Ordinary acceptance covers 6
claimed libraries, 50 owned modules and 6913 owned declarations, and recognizes
`checkedAccount` and `checkedExecutionFailures` among the RG1007 registrations;
`RegulaCore` execution coverage is 540 roots and 4656 boundaries (711 checked, 3945
trusted), 0 unresolved. `#print axioms`: `checkedAccount`, `Account.accepted`,
`coverage_fresh_iff`, `Status.spelling_eq_completed_iff`, `Status.completed_accepted` and
`checkedExecutionFailures` are `{propext, Classical.choice, Quot.sound}`; `fresh_scope`
and `Residual.mem_all` are `{propext}`; `coverageOf_fresh_iff`, `Coverage.text_eq_fresh_iff`
and `Residual.spelling_injective` use no axioms.

#43 closes this inventory after the selected work is integrated and reviewed,
with final proof/compiler, applicable qualification, ordinary acceptance and CI
evidence. A selected obligation cannot be closed by renaming it a trusted
boundary. Larger discoveries require separately scoped follow-ups; they do not
silently turn this project into a whole-runtime or whole-repository rewrite.
Then update #14/#15/#10 with the settled APIs and next executable tasks and
release the foundation scheduling hold while preserving other native blockers.

#### #43 closure

This section closes the F01–F12 inventory. It was reconciled on main `3cc121d` (#42 integrated through
[PR #59](https://github.com/rbeauchamp/regula/pull/59)) on Lean 4.34.0 (`293d5d0c`),
Mathlib `5ed29652` and, for the documentation prototype, Verso `cad4b633`, all unchanged since
the #38 baseline. The foundation deliveries are #38 (PR #44), #7 (PR #33 with #45–#49), #39
(PR #50), #40 (PR #53), #41 (PR #56) and #42 (PR #59). All six predecessor issues are closed;
#42 closed on 2026-09-23 after PR #59 merged. This closure was delivered by
[PR #64](https://github.com/rbeauchamp/regula/pull/64); #43 closed on 2026-09-24 after
reconciliation against its acceptance criteria.

Each row was read against its actual definitions, statements, hypotheses and call sites. No
selected obligation is missing: every selected relation has a definition, a theorem about the
executed definition, and callers that run it; F11's acquisition mechanisms stay trusted by
design, as #38 selected. One nonconformance with standard §8.6, found after scope selection, was separately scoped as
[#63](https://github.com/rbeauchamp/regula/issues/63) and did not block this closure:
`Probe.replacementCorrespondence` classified a correspondence comparison that did not complete
(kernel resource exhaustion or timeout) as `trusted` rather than `unresolved`. The F04
execution counts reported here were qualified by it. #63 is now resolved: the comparison is
classified by `RegulaPolicy.DefeqComparison.classify`, and `classify_trusted_iff` proves that
only a completed negative comparison is trusted. The
reconciliation found stale guide text, which the rows above now
correct. It also found four places where a caller reached a proved relation by inspection
instead of through its registration or type. They are now closed by reduction to existing
proofs; no new specification and no scenario control were added.

| Row | Former linkage | Now |
| --- | --- | --- |
| F06 | `Documentation.auditTasks` repeated `admitIndexedResults` by hand: `ResultState.collect`, then an unproved per-slot projection that threw "documentation task was not assessed". | It runs `checkedIndexedResults.run tasks.size` with binding `tasks[i]? = some r.task`. `IndexedResultsContract` gives one result per task, in task order, each bound to its own task; the throw is replaced by the contract's `IndexedFailure.missing` refusal. |
| F04 | `RuleDiagnostics.executionFinding` chose the finding's rule with its own `match`, so `executionRule` did not reach the findings path. | `executionDiagnostic kind` returns `Diagnostic (Policy.executionRule kind)`, and the finding is `⟨executionRule failure.id, _⟩`, so its rule is the registry bridge's by construction. The impact (`incomplete` or `violation`) is still chosen per branch. |
| F04/F12 | `Account` computed execution counts with `executionSummary` directly, bypassing `checkedSummary`. | `accountImpl` runs `checkedSummary.run`, so the account now depends on `SummaryContract`'s proof. `AccountContract` is unchanged and still stated with `executionSummary`; this adds no new guarantee. |
| F10 | `AcceptanceLink.record` wrote `"status": "accepted"` from a raw digest and job count, inside the audit and before `AxiomGate.run`'s outer configuration recheck, so a refusal by that recheck left an accepted record. | `record` cannot be called without an `AcceptanceLink.Pending`, whose `Account.Account` is a projection of some `AcceptedRun`, and writes that account's job count. The audit only computes the pending identity, before its success line; `auditSurface` returns it out of the bracketed action, and `run` records it only after `withUnchanged` returned `.ok` with exit code 0 and the result file was written. A refused run keeps the `incomplete` record written before the audit started. That it is this run's account, and that the digest matches it, is caller binding; the file is trusted as written, as `require` states. |

Behavior is unchanged except the refusal text of a documentation-result admission failure
and the F10 ordering: the acceptance-link record and its `recorded` line now follow the PASS line
and the outer recheck, and a refusal by that recheck no longer leaves an accepted record. The
first, second and fourth changes are in the excluded `Regula` library, kernel-checked by the
warning-as-error `lake build`. `checkedAccount` stays in claimed `RegulaCore` with the same
statement, since `checkedSummary.run` reduces to `executionSummary` (`run_eq` is `rfl`).

Remaining linkage checked by inspection, not by theorem, in addition to #41's adapter list above.
None is a selected obligation left open: each is IO dataflow, adapter rendering, or Project 8 scope.
The separately scoped §8.6 nonconformance #63, now resolved, was not linkage; it is recorded
with the obligations preserved for Project 8 below.

- **Current-request binding.** Each success caller builds its claim from its own captured inputs,
  freezes the plan and finishes it in the same procedure, so the `AcceptedRun c` it renders is
  that claim's. Callers carry it as `(c : Claim) × AcceptedRun c`, and `Account` forgets `c`.
  Indexing `Account`/`Status` by `Claim` would make the index visible but would not tie it to
  the command line without typing the IO procedure; the combined path already requires
  `CombinedAccepted evidence.claim dc documents`.
- **Documentation audit output.** `DocFenceAudit.run` and standalone `auditBuiltProject` print no
  `Account.pass` verdict; they print the account's job count, mode and `Account.lines`. Per-fence
  `PASS`/`PASS_NEG`/`PASS_TRUSTED` labels come from task results and print only after
  `finishDocuments` returned an `AcceptedRun`.
- **Exit code is authoritative.** `AxiomGate.run` brackets the audit with
  `SourceBinding.withUnchanged` on the invoking checkout's configuration. The audit already ran
  its own terminal recheck before acceptance, but the outer recheck runs after the PASS line. A
  configuration change during the run can therefore refuse with exit 1 after a printed PASS.
  The `--acceptance-link` record is written only after that recheck passed with exit code 0
  (F10 above), so such a refusal leaves no accepted record; a failure writing the record itself
  also exits 1 after the PASS line.
- **Hand-assembled observations.** `Documentation.finishDocuments` and `FreshChecker.finishGraph`
  assemble their observations without the #41 `observations` contracts and call `finalize`
  directly. `accept` decides those stages again (`ExampleExpectationOK`, `GraphOK`), so a wrong
  selection can only cause a refusal. That `exampleObservation` projects the raw compiler errors
  and inspection faithfully is adapter dataflow.
- **Editor linter.** At the #43 closure, `Linter.Rules.request` parsed the editor option without
  a contract and `Rules.declarations` rendered the rule after `checkedMemberFailure.run`. #14
  closes both: they run the claimed `RegulaCore.EditorPolicy` registrations
  `checkedEditorRequest` (`EditorRequestContract`) and `checkedEditorDecision`
  (`EditorDecisionContract`). The editor linter is a `module` and cannot import the
  non-module `RegulaCore.Policy`, so it cannot run `checkedRequest`/`checkedMemberRule`
  directly; `RegulaCore.Policy` instead proves the correspondence. `editor_request_sound` and
  `editor_request_complete`: the editor request domain is exactly `request claim` for claims
  other than compiler-trusting. `editor_decision_none_iff`, `editor_decision_rule` and
  `editor_decision_pending`: for the same member and request, the editor passes exactly when
  `ruleForMember` selects no rule, a rendered rule is `ruleForMember`'s, and a pending
  decision withholds a rule `ruleForMember` selects. The loop that renders each decision as a
  finding is checked by inspection.
- **Trusted definitions.** `ExecutableContract`, `run` and `run_eq` live in the excluded
  `Regula.Contract`, which claimed modules import deliberately (standard §8). `Residual` and
  the `rule-coverage.md` list are synchronized by review, and `Trusted` is a fixed list of
  mechanism classes, not a completeness proof.

Preserved for Project 8. The twenty rules RG1001–RG1007, RG2001–RG2005, RG3001–RG3002,
RG4001–RG4004 and RG5001–RG5002 keep the #38 baseline identifiers and descriptors; the registry
moved to `RegulaCore.RuleId`/`RegulaCore.Rule` (#41) and gained only proofs. (Later, #71 added RG5003,
and #10 narrowed several descriptors' evidence modes to the modes that emit them, corrected
RG1007's clauses and derived the message form; see the
[product qualification](product-qualification.md).) Since the
baseline, stable diagnostics keep their rule, payload, location, mode, claim and impact.

- **Invocation.** Since the #38 baseline, #7 (PR #33) added `axiomGate --acceptance-link`,
  removed the internal `--surface-worker`, and routed every success through accepted evidence;
  #42 replaced the success text with the account. The public forms are `axiomGate` fresh
  (default), `--incremental`, `--file` with `--claim`/`--execution`, `--with-docs`,
  `--build-lint`, `--json-out` and `--acceptance-link`; `docFenceAudit`; `freshChecker`; and the
  two acceptance steps. This closure changes none of them.
- **Accepted-result API.** `RegulaPolicy.AcceptedRun c` (`acceptedRun_claim`, `accept_iff`,
  `CombinedAccepted`). Success verdicts and the `completed` status go through `Account.account`,
  `Account.pass`, `Account.lines` and `Account.Status` (`ResultProtocol.Status` abbreviates it).
  `ResultProtocol.acceptedJson` also renders `AcceptedRun.report` fields directly, with the
  account as `accountJson`.
- **Reports.** #7 (PR #33) added the `acceptance` member to completed results, plus
  `documentationAcceptance` for `--with-docs`; #42 added `acceptance.account`. Both were
  additive within result schema 1. #61 then moved results to schema 2, which renders the
  snapshot through `ResultProtocol.snapshotJson` and omits the import-closure lists so result
  size tracks the audited project; the `acceptance` and `acceptance.account` members remain
  ([rule registry](rule-registry.md)).
- **Coverage.** Ordinary acceptance at this closure still reports 6 claimed libraries, 50 owned
  modules and 6913 owned declarations, as at `3cc121d`. Every source, admission and ownership
  stage of the plan is unchanged, and no rule, claim or exclusion was relaxed. `RegulaCore`
  execution coverage reads 540 roots and 5511 boundary observations (817 checked, 4694 trusted),
  0 unresolved; #42 recorded 4656 boundaries at its earlier head `642d756`. These are
  observation counts of a conservative account, not a measure of assurance. They were taken
  before #63 was resolved, when a correspondence comparison that did not complete (kernel
  resource exhaustion or timeout) was counted as trusted rather than unresolved, so these
  counts, including 0 unresolved, may overstate what was decided. After the fix, local acceptance
  reported the same `RegulaCore` counts, again with 0 unresolved, so in that run no trusted
  boundary came from an incomplete comparison.
- **Resolved obligation.** [#63](https://github.com/rbeauchamp/regula/issues/63)
  (standard §8.6): an incomplete correspondence comparison is now classified `unresolved`. The
  fix followed [PR #60](https://github.com/rbeauchamp/regula/pull/60), which changed the
  same `Probe.lean` correspondence path; this closure did not change it.
- **After the closure (#14).** The `lint` executable (`lintDriver = "regula/lint"`) runs the
  project audit and classifies its exit through the claimed `RegulaCore.Lint` registration
  `checkedClassify` (`ClassifyContract`); `accepted_sound` proves exit 0 implies an
  `AcceptedRun` of the requested mode. The editor linter runs `RegulaCore.EditorPolicy`
  (see **Editor linter** above). Both add owned `RegulaCore` modules and RG1007 registrations.

Evidence (arm64 macOS and CI, observations only). The local rows below (`lake build`,
`./scripts/verify.sh` 157 s, `./scripts/verify.sh docs` 90 s, rule-examples 1/2 105 s and 2/2
84 s) ran before the F10 acceptance-link ordering repair. That repair introduced
`AcceptanceLink.Pending`, made `auditSurface` return the pending identity instead of writing the
link, added `withSourceEvidenceOr`, and made `AxiomGate.run` call `AcceptanceLink.record` only
after the outer `withUnchanged` recheck passes with exit code 0.

| Check | Result |
| --- | --- |
| `lake build` (warnings are errors) | PASS |
| `#print axioms` | `checkedAccount`, `Account.accepted`, `coverage_fresh_iff`, `Status.completed_accepted`: `{propext, Classical.choice, Quot.sound}`, as #42 recorded |
| `./scripts/verify.sh` | PASS, 157 s cold-root; 6 libraries, 50 modules, 6913 declarations; all RG1007 registrations recognized |
| `./scripts/verify.sh docs` | PASS, 90 s (70/70 positive, 23/23 compiler-rejection, 1/1 trusted teaching) |
| `diagnostics rule-examples 1/2`, `2/2` | PASS, 105 s and 84 s (11 and 9 rules; RG3001/RG3002 exercise the retyped execution findings) |

Evidence covering the repaired code:

| Check | Result |
| --- | --- |
| Pipeline live test at the repair commit: `./scripts/verify.sh` | PASS, 173 s; the accepted link was recorded only after the outer recheck |
| Pipeline live test at the repair commit: `./scripts/verify.sh docs` | PASS, 93 s |
| Pipeline live test: configuration changed after inner acceptance | the outer recheck refused with exit 1; the link stayed incomplete |
| Exact-head CI at `9bfe3a1` (before the rebase onto `cde1041`) | PASS: verify ordinary 384 s, docs 158 s; diagnostics history, producers, rule-examples 1/2 and 2/2; CodeQL |
| Exact-head CI at `a9e1ecc` (`9bfe3a1` merged with main `cde1041`, #61) | PASS: verify, diagnostics history, producers, rule-examples 1/2 and 2/2; CodeQL |

The final head's acceptance is its exact-head CI run.

The docs step exercises `Documentation.auditTasks` and the acceptance link. `fixtures`, `cli`,
`structural`, `environments`, `build-policy`, `producers`, `history` and `serialized-graph` were
not run locally (CI ran `producers` and `history`): this closure does not touch their capabilities. The `structural` partition's
pre-existing failure (its stale `structuralManifestText`, recorded under #41) is unchanged and is
separately scoped. These runs qualify detection; they are not correctness evidence.

## Evidence and maintenance

The native `lake exe axiomGate -- --incremental --legacy-json-out <report>`
inspection completed successfully on this baseline. Its Lake-derived inventory
and attributed declaration counts were as follows. Suffixes below have the
library prefix; `(root)` denotes the module named exactly as the library.

| Surface | Modules | Attributed declarations |
| --- | --- | ---: |
| `RegulaPolicy` | `(root)`, `Specification`, `Identity`, `Claim`, `Decision`, `Pattern`, `Foundation`, `Execution`, `Admission`, `Domain`, `RoleSpecification`, `Plan`, `Collections`, `Codec`, `Observation`, `ResultState`, `Acceptance` | 3649 |
| `RegulaVerification` | `(root)` | 101 |
| `RegulaQualification` | `Checks`, `Json`, `Evidence`, `Registry`, `Launcher`, `Template`, `Website`, `Producer`, `History`, `Native` | 443 |
| `Audit` | `(root)`, `Research`, `Basic`, `Economy`, `Server`, `DocPrelude`, `DocClaims` | 313 |
| `AuditApp` and standalone executable | `(root)`, `Limiter`, `Refinement`, `Demo`; standalone `Main` | 196 |

These are inventory observations, not proof-volume or completeness metrics.
This incremental inspection is not ordinary acceptance or fresh-source conformance.
An ad hoc `lean --run` inventory probe hit an IR-interpreter assertion before
returning an inventory; it supplies no successful inventory evidence or established
root-cause diagnosis. The native checker supplied the inventory above. A separate
non-running Lean probe successfully elaborated the selected type/axiom queries.

The baseline read-back inspected the existing declarations on the pinned Lean
toolchain, including their elaborated types and transitive axioms. This is scoped
evidence, not a new proof of the collector or the IO mechanisms. The inspected
axiom sets are:

| Exact set | Inspected declarations |
| --- | --- |
| Empty | `ExecutableContract.run_eq`; `AuditApp.admit_exact`. |
| `{propext}` | `RegulaPolicy.exactlyOne_iff_head`; `RegulaQualification.evaluate_append`. |
| `{propext, Quot.sound}` | `CanonicalSet.adjacentOrdered_iff`; qualification `evaluate_success`, `evaluate_error`, `checkedEvaluation`; `AuditApp.runChecked_success`, `runChecked_error`; `Economy.sumTo_eq_closedSum`, `sumTo_csimp`. |
| `{propext, Quot.sound, Classical.choice}` | Policy `admitInventory_exact`, `admitExecution_preserves`, `policyFor_none_iff`, `foundationFor_iff`, `executionFailureRecords_empty_iff`, `admitPlan_exact`, `ResultState.insertResult_success_iff`, `insertResult_frame`, `accept_iff`, `accepted_report_identity`, `accepted_covers_slot`, `CanonicalSet.normalized_iff_ordered`; `AuditApp.checkedExecutable`. |

Unqualified policy names in this table are in `RegulaPolicy`; qualification
names are in `RegulaQualification`. Universe parameters remain those of the
elaborated declarations. These sets describe these proofs, not the minimum
foundations of their propositions or a ranking of software assurance.

Issue #38 changes this guide and its index only. It does not change Lean source,
normative requirements, manifests, detection behavior or proof statements.
Relevant review rows are SCOPE-02/03/05, TYPE-01/05, THEOREM-03/07/10,
BUILD-03, DOC-02 and DOGFOOD-03/04 at this guide's scope. No new mutation campaign
or optional serialized-graph claim follows from this planning delivery.
The delivery PR records focused inspection, independent semantic review, exact
head CI and merged-main evidence separately; an existing proof or green build
does not complete F05/F10's remaining delivery gates. (The #43 closure records their
integration.)

Successors update these same rows with exact integrated definitions, changed
coverage, evidence and remaining boundaries. Keep the source baseline distinguishable
from later closure; do not append another competing status document. Repository
workflow and deadlines remain in [AGENTS.md](../../AGENTS.md); normative meaning
remains in the [standard](../standard/README.md).
