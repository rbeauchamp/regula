# Repository instructions

## Mission and scope

- This repository delivers Regula, a strict linter for Lean with a linked rule-reference website,
  backed by a strict public standard for dependent types, theorem statements,
  proofs, axioms, elaboration, modules, and Lean code in Lean 4 projects, especially where
  correctness is critical.
- The standard defines normative meaning: its only source is the Verso library in
  `website/RegulaStandard/`, published under `standard/` of the rule-reference site.
  `docs/guides/` contains practical guidance.
  `audit/Audit/` and the Lean-oriented checkers must dogfood the applicable rules.
- `lean/Regula/` implements mechanically checkable requirements; `examples/build-lint/`
  is the reference build integration. Keep enforced rules, required proof evidence, and
  remaining semantic-review obligations distinct.
- The normative standard excludes general software-process requirements: lifecycle,
  traceability, provenance, CI/CD, release, deployment, operations, risk/waiver, certification,
  and organizational policy. Repository maintenance instructions belong here or in the guides;
  a separate general-practices standard is out of scope.
- Strict rules must have a precise Lean, dependent-type, proof, or Lean-code rationale. Put
  domain-specific material in examples or named Lean-domain profiles.

- Follow `docs/guides/architecture.md` and `docs/guides/proofs-and-boundaries.md` for the
  product contract. Keep typed rule metadata, diagnostics and checked website
  examples synchronized. Follow `docs/guides/design-influences.md` for contribution-specific
  attribution; no single research reference brands every issue or deliverable. Distinguish planned work
  from currently supported enforcement and published pages.

## Start every task

- Verify the checkout and worktree status before making claims or edits. Record exact
  `HEAD` when present; for a repository with no commits, state that explicitly and identify
  the staged tree when one is available. Do not create a commit merely to obtain a `HEAD`.
- Use `README.md` and `docs/README.md` to establish scope when needed; read every affected
  normative module completely before changing or auditing its Lean claims. For unrelated
  skill, handoff, or mechanical edits, read the governing instructions and affected sources.
  When working an open issue, that issue is authoritative until closed; existing green checks
  are scoped results only.
- For a PR review, pre-merge pass, or independent compliance audit, use the repository-local
  `.agents/skills/pr-review-toolkit/SKILL.md`. The standard's module 8
  (`website/RegulaStandard/ComplianceAudit.lean`) is the checklist SSOT.
- Every delivery PR requires independent review by at least one fresh-context reviewer.
  Scope reading and checks to the changed claims; use distinct reviewers for materially
  different semantic and implementation risks. The local review skill owns assignments
  and completion criteria.
- After repair, obtain focused independent verification of the affected claims. Reuse
  evidence whose relevant inputs and claims remain unchanged; rerun only invalidated checks.
- Preserve unrelated changes. Use `tmp/` for isolated probes and remove your probes afterward.

## Issue delivery

- When working an issue, its acceptance criteria define the deliverable. Follow the local
  review skill for delivery review. A planning issue or an agent's review response alone
  is not a completed delivery. Keep workflow requirements here and in skill guidance,
  outside the normative Lean standard.
- Complete authorized implementation, local repairs, checks, and targeted review without
  repeatedly requesting permission. Use existing session authorization for external actions;
  requiring a PR does not itself grant permission to publish, merge, or change visibility.
- Mark an issue Done only after its acceptance criteria and required review/checks pass and
  its completing PR is integrated. A partial PR references the issue without closing it.

## Lean-specific requirements

- State the exact elaborated theorem, quantifiers, assumptions, and transitive dependencies. Do
  not strengthen a Lean result into a claim about an unrelated implementation.
- Ban `sorryAx`, project logical `axiom` declarations (Lean 4 has no `constant` command;
  `opaque` is classified separately), `sorry`, and `admit` from every
  conforming proof surface. Express assumptions as parameters, hypotheses, or proof-bearing
  fields.
- Report exact foundation strength: Kernel-only is empty; Choice-Free permits only `propext` and
  `Quot.sound`; Standard-Logical additionally permits `Classical.choice`. Do not treat these as
  general software-assurance rankings.
- Distinguish logical and executable decidability, noncomputability, kernel reduction, native
  evaluation, `partial`, `unsafe`, runtime replacement, `extern`, and FFI wherever the
  distinction affects a Lean claim.
- Discover modules, declarations, and dependencies through Lean/Lake semantics, not fixed file
  lists or source-format regexes. Unknowns and omissions fail the affected claim.
- Check every positive and negative Lean behavior claim on the declared supported toolchain.
  Isolate intentionally invalid fixtures from positive checked surfaces.

## Implementation language

- Project-owned implementation code must be Lean 4, with explicit behavioral contracts
  proved about the actual definitions used by callers. A translation into Lean or a
  successful build alone does not establish behavioral correctness.
- Do not add or run Python or other implementation-language replacements. Existing
  non-Lean implementations are migration debt, not authorization to extend them.
- Keep `scripts/verify.sh` to the minimum shell needed for acceptance and its external
  deadline. Any additional shell script requires explicit operator approval, including
  shell programs embedded in CI or generated by Lean.
- Operator-approved exception: the `Install Elan and pinned Lean` step in
  `.github/actions/provision/action.yml`, shared by the CI workflows, may use shell
  solely to install pinned Elan/Lean and
  required system tools (GNU coreutils timeout and ShellCheck), expose their paths,
  and check their availability/versions. This bootstrap runs before Lean is available;
  it must not implement policy decisions, validation logic, or test orchestration.
  Those remain Lean-driven after provisioning. Expanding this exception requires
  explicit operator approval. Installation and runtime mechanisms remain trusted,
  not formally verified by the project's Lean contracts.
- Operator-approved exception: `scripts/provision.sh` may use shell solely to run
  `lean/RegulaProvision.lean` from the repository root, the local setup linking a copy to
  the shared, read-only Mathlib. `scripts/verify.sh` runs it before its deadline under its
  own 1800-second GNU timeout and stops with a message if it fails or times out. It must
  not implement policy decisions, validation logic, or test orchestration.
- Use Lean/Lake APIs for orchestration where available. Distinguish pure proved
  behavior from trusted compiler/runtime, filesystem, and process effects; qualification
  observations do not prove those external mechanisms.
- This policy governs project-owned implementation, not a claim that the Lean toolchain,
  external dependencies, declarative configuration, or generated website assets are
  themselves implemented and formally verified in Lean.

## Changes and verification

- Change normative prose, Lean fixtures, and Lean-specific checkers together when they encode
  the same claim. Prefer Lean-native inspection and include positive controls plus adversarial
  mutations in the change itself, before review. After moving a path or changing a command,
  search the whole repository (docstrings, CI YAML, guides, Lean-printed messages) for the old
  form before review.
- Reuse established Lean and Mathlib definitions when they fit. Avoid arbitrary style mandates
  and application governance in the universal standard.
- Keep documentation, docstrings, rule pages, diagnostics, checker names, and checker output no
  stronger than the exact Lean property established. Before review, check each new sentence that
  cites a theorem or check against its actual statement, hypotheses, and caller; name what it
  leaves uncovered.
- Respect the assurance boundary stated in standard module 7: a recursion helper is admitted only
  when Lean's own recursion compiler regenerates its base from it, up to compilation erasure,
  whatever evaluator produced it, a
  native-proof axiom rests on its natively replayed statement and command provenance instead, and a
  modified Lean executable, compromised process, and arbitrary trusted plugins are outside this
  Lean-source standard. Do not recursively expand reviews into
  stronger threat models after the documented boundary has direct positive and negative evidence.
- For a PR, establish the standard's module 8 rows affected by its changes and dependencies.
  A full repository-compliance claim requires every applicable row across all claimed surfaces
  to be `PASS`; a scoped PR review does not establish that broader claim.
  `MUT-*` applies when checker behavior is implemented or changed; `DOGFOOD-*` (this
  repository's own rows, in `docs/guides/contributing.md`) applies to this repository; `MUT-05`
  applies to the optional serialized-graph claim. A `FAIL`,
  `INCOMPLETE`, unknown, omission, skip, timeout, or unsupported check blocks the affected claim.

In a fresh copy, run `./scripts/provision.sh` before the first `lake build`; otherwise Lake
clones and builds a per-copy Mathlib. Then use `lake build` for the Lean development loop.
Complete local acceptance is two commands, run in this order:

```sh
./scripts/verify.sh
./scripts/verify.sh docs
```

Each has its own hard, no-exception 420-second deadline; the first includes cold
root-package builds. Before that deadline starts, each `verify.sh` invocation runs
`scripts/provision.sh` as setup under its own separate 1800-second limit; a failure or
timeout there stops the run before verification begins.
There is no override or grace period; GNU coreutils timeout sends SIGKILL to the
verification process group at the deadline. A partial or over-budget run fails.
Do not bypass the deadline by treating separately run inner checks as acceptance.
Provision pinned dependency artifacts (including the website package's pinned Verso,
`(cd website && lake build verso/VersoManual)`) and GNU coreutils timeout before
verification; network/toolchain installation is setup, not a verification pass. OS scheduling and
signal delivery are trusted mechanisms, not a hard real-time theorem.

The first builds the acceptance executables and type-checks the diagnostic modules,
checks every claimed declaration of the root `regula` package with fresh source elaboration and
kernel admission, and records the content identity of its inputs: the inputs it accepted plus the
`docs/` Markdown and the standard's Verso package sources (with the `audit/` sources they import)
it only brackets, not accepts. The second checks every Markdown document Git tracks for a rule ID
in prose that is not a link to its rule page (it needs a Git checkout), runs the same fresh check
over the Mathlib-dependent `audit/` package, then audits every documentation example, builds the
Verso standard fresh (elaborating each `lean` block where it is written) and renders it, and
refuses unless its own inputs have that identity. This exact two-step split is the only permitted
division of acceptance. Diagnostic native binaries are built when those diagnostics are requested.
Complete applicable theorem/type/prose review too; command success alone is not full
semantic conformance.

Checker changes receive focused qualification for affected capabilities and invocation
paths under standard §7.8. Long mutation, external-adopter, build-integration,
and optional serialized-graph campaigns are diagnostics, not automatic merge gates, except
those the diagnostics workflow runs: its required `diagnostics` check refuses a merge unless
each of them that applies passed.
Retain their controls and applicable evidence; never relabel an unrun campaign PASS.
`./scripts/verify.sh diagnostics [partition]` runs a selected existing campaign under
the same 420-second deadline; `rule-examples 1/2` and `2/2` run the corpus in two shards.
The full corpus is 47 productions (44 phases plus 3 refusal controls), 3 individual
control admissions and one corpus admission of every record; each production runs in its
own fresh workspace, so no restored rerun repeats it.
Use `./scripts/verify.sh serialized-graph` for an explicit separate graph-checking claim.
Do not partition either acceptance step further to evade its limit. A requested broader
claim still needs its actual evidence.

On every PR and `main`, CI runs both acceptance steps in one job, the two rule-example
shards, and then `./scripts/verify.sh site`, which builds and checks the rule-reference site (its own
420-second limit; never part of acceptance). The
[contributor guide](docs/guides/contributing.md#choose-focused-diagnostics) lists which
workflow runs each diagnostic and when; the
[website guide](docs/guides/website.md#publication) owns publication. Merge requires passing
CI on the reviewed PR head, applicable focused review and diagnostics.
Preserve PR, signature, history, and conversation protections. Finish authorized publication,
exact-head merge, and owned branch cleanup. Skill/handoff-only edits need proportionate
checks when Lean inputs and claims are unchanged.

Report the tested Lean/Mathlib versions, exact Lake modules and declaration/axiom
coverage, applicable diagnostics, and failures or missing evidence. Keep performance
budgets and delivery workflow here,
not as universal requirements in the normative Lean standard.

## Maintaining this file

Keep this file for knowledge useful to almost every future agent session in this project.
Do not repeat what the codebase already shows; point to the authoritative file or command instead.
Prefer rewriting or pruning existing entries over appending new ones.
When updating this file, preserve this bar for all agents and keep entries concise.
