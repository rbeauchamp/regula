# Review and closure

## Freeze the subject

Record the checkout, intended changes, and exact commit or comparison when available.
For a repository without commits, identify the staged tree; do not create a commit or
remote to satisfy review bookkeeping. Consult an issue only when one governs the task.
Use AGENTS.md for required reading, independent review, and verification policy.

For a diff, cover changed claims and their dependencies. Include a baseline defect when
it contradicts the claimed result; unrelated defects do not turn a scoped review into a
repository-wide audit. Full compliance covers every applicable module 8 row, the
repository's `DOGFOOD-*` rows (`docs/guides/contributing.md`), and every surface.

## Independent review

For delivery PRs, assign the independent review required by AGENTS.md. Give reviewers the
frozen subject, requested outcome, raw artifacts, and relevant [lenses](lean-lens-contracts.md).
Keep discovery independent of the author's findings or earlier verdicts. For focused repair
verification, supply the finding and repair so the reviewer can check closure.

Reviewers do not edit shared files or delegate further. Separate materially distinct risks;
coordinate expensive commands through one owner to avoid competing builds. Collect assigned
reviews before modifying their frozen subject. If independent review is unavailable, report
that gate as incomplete while completing unaffected authorized work.

## Accepted-result review

For acceptance changes, use [the acceptance boundary](../../../../docs/guides/proofs-and-boundaries.md#the-acceptance-boundary)
and assign distinct fresh-context proof and integration review. The proof review checks
that the executed collector/finalizer derives complete coverage and approved predicates
for every required slot, with explicit hypotheses and exact axiom sets. Statement-reference
or axiom-closure audits alone do not establish proof-body/execution linkage.

The integration review traces every success branch through `AcceptedRun.report` (and
`CombinedAccepted` for project/docs), independently frozen requests/censuses, raw packet
reconstruction and unchanged source/ownership/admission guards. Check exact mode and
snapshot identity, full replay preservation, infrastructure disjointness/authentication,
original-file/temporary-copy binding, grouped fence units and optional graph roots.
Review constructor/caller visibility without claiming hostile in-process unforgeability.
For a multi-environment census, verify the original full claim and coordinator-fixed
request partition; local roles, roots, replay, histories and origins must resolve in
the job's exact environment. Equal names across environments must not be flattened
or deduplicated, and configuration/discovery/build obligations remain global.
Help, planning, workers, local editor observations and diagnostic demonstrations must
stay explicitly non-audit; rendered JSON/status cannot reconstruct a proof.
For adoption adapters (`lint`, the build `policy` target, native editor messages),
check that success reaches exit 0 only through the audit's own accepted result
(`Lint.accepted_sound`), that exit classes follow the recorded status, and that help
links come from the registry's `helpUrl`. Editor claims need observation in the supported
client; a link string or browser check alone does not qualify an editor interaction.

## Rule and site changes

A change to a rule reviews its registry descriptor (`RegulaCore/Rule.lean`), its explanation
(`guide` in `RegulaCore/Guide.lean`), its fixtures and `corpus.json` entry, and its detector together.
Check that the explanation states exactly what the detector rejects, which impact it reports,
what a pass establishes and which `Residual` obligations stay open, with no suppression advice
that implies conformance; that the correction preserves the violation's intended proposition or
behavior; and that an ID keeps its meaning (a changed predicate needs a new ID and a retired
descriptor). For site changes, check the generated pages in a browser at a narrow and a wide
width and trace every claim in [the website guide](../../../../docs/guides/website.md) to its
theorem or recorded observation. A passing site build is not semantic review of the prose.

## Evidence and repairs

Check findings against the exact Lean claim and supported pin. A checker bypass repair needs
a positive control, an independent single-fault mutation rejected for the intended reason
through the public entry point, and a restored positive control. Wrong-reason failures do
not close the finding. Qualification observations do not prove universal checker correctness.

Keep prose, definitions, and checker policy aligned where they encode the same claim.
Preserve module 7's assurance boundary: a recursion helper is admitted only when Lean's own
recursion compiler regenerates its base from it, up to compilation erasure, whatever evaluator
produced it, a native-proof axiom
rests on its natively replayed statement and command provenance instead, and arbitrary process
or trusted-plugin compromise is outside scope. Module 7 §7.5 also puts code that deliberately
changes Lean's environment, compiler or build to make a check pass outside scope. An example is a
direct write to an environment extension's state that bypasses the command or attribute Lean
gives for it.
Ordinary declarations, attributes such as `implemented_by`, `extern` and `csimp`, and
`initialize` stay in scope (§7.6).

Choose checks from AGENTS.md and the applicable checklist rows:

| Changed claim | Evidence focus |
| --- | --- |
| Lean definitions or proof claims | Relevant compiler/proof checks and semantic review. |
| Settled conformance | Complete acceptance command plus applicable semantic rows. |
| Checker behavior or detection claims | Focused qualification of affected capabilities and invocation paths. |
| Lake lint driver, build target or editor adapter | `diagnostics lint-driver` or `build-policy` as affected; `qualify native` for linter messages; recorded client observation for editor interaction. |
| Optional serialized-graph claim | Supported fresh-checker evidence for that exact graph. |
| Rule metadata, explanations, fixtures or site generation | Both corpus shards and `./scripts/verify.sh site` at the same commit; browser observation of affected pages; semantic review of the explanation. |
| Instructions or editorial changes with unchanged Lean claims and inputs | References, instruction behavior, and scoped review. |

Reuse prior semantic or diagnostic evidence when its relevant inputs, toolchain, and claim
remain unchanged; identify the earlier snapshot and why it still applies. CI is a separate
exact-PR-head gate. AGENTS.md owns commands, deadlines, and integration requirements.
After integration, locate and await the main push workflow for the exact merge SHA.
Record its terminal outcome separately from reviewed-head/synthetic-merge checks;
failed, skipped or unfinished required stages leave delivery reconciliation open.

## Report and stop

For each finding, give its location, failed claim, evidence, applicable row when relevant,
and closure criterion. Distinguish standard nonconformance, Lean quality, and repository
quality. Optional teaching improvements are not automatically normative defects.

Report coverage and missing evidence at the requested scope. CLEAN means no validated defect
was found within that coverage. Apply the checklist Result Rule: demonstrated violations
are FAIL; missing or unfinished required evidence is INCOMPLETE when no violation is known.
PASS requires all applicable evidence. A full audit reports every applicable
row, supported pins, declaration/axiom coverage, execution boundaries, and relevant controls.

Finish authorized repairs and their verification. Do not confuse review success with merged
delivery, create new publication authority, or pass an explicit user stopping point. Name
any remaining gate and preserve the reviewed work when blocked.
