# Lean CI precedents and limits

These records explain why a technique was useful, not a latency promise for another
project. Regula's current policy is owned by [AGENTS.md](../../../../AGENTS.md)
and [verify.sh](../../../../scripts/verify.sh). Consult their current contents rather
than copying a historical budget from this file.

## Regula: distinguish decisions, scheduling and orchestration

The timings and hosted outcomes below were observed; they are not proofs.

1. **Equivalent canonical-set decisions.** `RegulaPolicy/Collections.lean` proves
   adjacent strict ordering equivalent to the existing normalization equality under its
   comparator hypotheses. `Domain.lean` installs those decisions for actual name/edge
   admission conditions. This removes sorting/deduplication from that decision without
   changing its proposition. The structural bound is at most `max(n-1,0)` comparisons;
   comparing structured names still has input-dependent cost. Compiled caller inspection
   and focused duplicate/order controls qualified execution; the proofs do not verify
   machine code. This change alone did not bring hosted acceptance within its deadline.
2. **An inner worker cap.** Ordinary documentation checking passed `jobs=4`, but inspection
   imposed `min jobs 2`. Removing that extra cap retained isolated child environments,
   unique scratch and results associated with their original indices. It reduced one local
   inspection observation from 63.301s to 43.627s. Whole hosted ordinary acceptance then
   completed, but a downstream corpus campaign still timed out. Neither the speedup nor
   sufficient memory is universal.
3. **Repeated qualifier elaboration.** The corpus called `lake env lean --run
   RuleExampleQualification.lean` after each produced receipt. A native executable of
   that unchanged entrypoint removed repeated elaboration; its Lake target, tooling
   classification and build instructions changed together. On the same complete export,
   interpreted and native invocations returned identical successful output in 17.18s and
   1.22s respectively. The final hosted run completed all required stages; this is not a
   proof that arbitrary native/interpreted programs are equivalent.
4. **Terminal source-account output.** The producer retains captured sources in memory
   and serializes at terminal boundaries instead of repeatedly serializing every growing
   prefix. Every required terminal path still carries its captured evidence, including
   failure paths. See [proofs and boundaries](../../../../docs/guides/proofs-and-boundaries.md#producers).
   Before/after equality does not authenticate the process or exclude change-and-restore.

The corpus's displayed `detectorSeconds` brackets the fresh checker subprocess, including
nested builds, fence compilation/import/admission and result serialization as applicable.
Fixture setup, Python export and the subsequent qualifier are outside that timer.
For example, [RG4001]'s orphan-marker fixture also has a valid Lean fence: the documentation
driver checks that fence before emitting its structural finding. Seconds for that complete
invocation do not measure the scanner alone. The separate native-editor observations
use already-live snapshots and provisioned imports, not fresh project admission.

## Regula: invocation-local Lake environment capture

A post-merge 420s failure is distinct from an observed local overhead reduction. Repeated
`lake env lean` calls loaded an unchanged workspace for each of 36 controls. Capturing
the actual environment for each parent-environment state retained individual compiler
children and exact control outcomes. The bounded paired diagnostic compares sources,
arguments, effective environments/executables and outputs; it does not certify fresh
root inputs or isolate all timing effects, and its observations are platform-specific.
Use paired timing as focused repair evidence,
not a recurring CI gate: scheduling noise can reverse the observed delta without changing
functional results. Follow the actual post-merge main workflow:
identical trees and green synthetic-merge checks did not establish main CI success.

## Regula: sequential diagnostic budgets and shared writes

At `0d2d6142192967f4873305cbf1ec5d8227607a36`,
ordinary hosted verification passed, while the combined producer/history420 run finished
all 21 producer invocations but only 2 of 17 history invocations. The aggregate failed;
a producer PASS did not establish completed history qualification or green CI.
The authorized repair uses two sequential hard420 diagnostic gates with full coverage.
It does not change ordinary cold420 or prove a runtime upper bound.
Superseded 2026-09-22: these campaigns now run as parallel capability-triggered diagnostics
jobs, each under its own 420s ([contributor guide](../../../../docs/guides/contributing.md#choose-focused-diagnostics)).

Separate fixture roots shared `.lake/packages`; a prior prebuild did not enforce
read-only module outputs, trace/hash sidecars or artifact/Git metadata. At pinned
Lean4.33.1, workspace configuration caches are workspace-local: different dependency
package indices alone did not establish a shared configuration-cache collision.
No race was demonstrated and no physical timeout cause was established. Sequential
execution avoids requiring a new shared-write or descendant-containment argument.
A Python timeout that kills/waits its direct checker child alone does not establish
that nested Lake/compiler descendants have stopped before scratch cleanup; an outer
SIGKILL cannot execute user-space cleanup. The OS remains a trusted boundary.

## Regula: the gate beside the rest of ordinary acceptance (2026-10-06)

Observed on hosted `ubuntu-24.04` runners with four processors; these are not bounds.
Over 18 CI runs the first acceptance step took 226 to 414 s under its 420-second deadline. In
five of them read phase by phase, every phase was 1.6 to 1.8 times longer in the slowest run
(405 s) than in the fastest (236 s), so the spread was runner speed. In [run 37513374192](https://github.com/rbeauchamp/regula/actions/runs/37513374192)
the step took 364 s: the build 173 s, `qualify combined` 25 s, and the gate 157 s, of which its
isolated build took about 66 s.

What follows is an estimate from the durations Lake logs for each job. Lake measures them with
`IO.monoMsNow` around the job, so they are elapsed time: a job that waits for a processor, or
that uses several threads, logs the same way, and their sum is not processor work. The build
logged 273 jobs whose durations sum to 640 s, and by those durations about four jobs were in
progress from its start to its end. The gate's isolated build logged 163 s, with one or two jobs
in progress during its last 40 s. The modules the gate executable imports logged 414 of the
640 s, and their longest import chain with the gate's own C file logged 96 s. If each job needs
about one processor for its logged duration, and that duration does not change with what runs
beside it, then about 225 s of the build's work did not have to precede the gate, and the step
would take about 300 s on that runner. Neither assumption was measured, so that figure is a
prediction.

The driver now builds the gate first and runs it beside the complete build and the other checks
([proofs and boundaries](../../../../docs/guides/proofs-and-boundaries.md#the-acceptance-boundary)).
In one local probe (14 processors, two threads for each side) the second build compiled 106
jobs, none of them a module the gate imports, and the gate recorded the same input identity as
the sequential run. That probe shows the arrangement works; it does not show the hosted gain,
because the local machine has processors to spare. The hosted times of the new schedule are in
the pull request that closed [issue 246](https://github.com/rbeauchamp/regula/issues/246).
Not established: that two Lake processes in one build directory never interfere (one of them
builds nothing here), and any upper bound on the step's time.

An independent review of the first version found one path on which the gate was not joined: the
line that announced another command's failure could itself raise before the wait. The driver's
orchestration is now a `BaseIO` action, and one pure decision with a registered contract
(`RegulaVerification.passed`) decides the result from how every command ended.

## Regula: Veil scout for the corpus harness (2026-09-23)

On 2026-09-23, Veil ([verse-lab/veil](https://github.com/verse-lab/veil), main `517f2ba`)
was evaluated for the rule-example corpus harness: producer window, joins, cleanup,
final export and deadline kill. It found no protocol bug. It was not adopted: it pins
Lean v4.32.0 against Regula's v4.34.0 and is a pre-release (Veil 2.0). By default
it closes SMT goals with `sorry` (`veil.smt.trust := true`; set it to `false` for kernel
reconstruction). Its explicit-state model checker deduplicates states by a 64-bit hash
and emits no certificate, so a clean run is testing, not proof. Its model has no checked
link to the executed code. Direct theorems about the executed step function
(`RegulaQualification.CorpusWindow`) took about 45 lines and 0.25s to check.
This is dated evidence for that harness, not a general verdict on Veil.

## Public Acorn: reusable work still needs exact ownership

Public source: [delivered change](https://github.com/rbeauchamp/acorn/pull/4), integrated
at [6d3e95bf](https://github.com/rbeauchamp/acorn/commit/6d3e95bf2dc267436d4b34508d2afd48e1ab11c8).
The [run at 6d3e95bf](https://github.com/rbeauchamp/acorn/actions/runs/35098724752/job/104802455043)
completed its required cold verification in approximately 239s on Ubuntu 24.04.
Logged stage observations were build166.986s, compiled boundary15.057s,
native admission26.100s and combined ownership/axiom/corpus12.403s, plus other overhead.
These are observations of the combined delivered change, not isolated causal estimates.

- [36701b25](https://github.com/rbeauchamp/acorn/commit/36701b255339aea25574209c590383bfcff70638)
  removed forced Lake reconfiguration while retaining validated traces and uncached project
  artifacts, and batched hashing while checking count, digest shape and filename association.
- [e74975d5](https://github.com/rbeauchamp/acorn/commit/e74975d55545e3cd9d2439226b468e2e50949ca3)
  narrowed broad imports and changed target scheduling so independent work could proceed.
  Required preflight still preceded application compilation.
- [48f3c8b0](https://github.com/rbeauchamp/acorn/commit/48f3c8b034c5ece4948c9077d542a41cbdd5d178)
  reused compiler-loaded dependency regions across isolated executable environments and
  combined related audits in one environment. Each executable retained its own main;
  IR owners had to belong to that entry's serialized import closure, and shared regions
  had to outlive their consumers. This is not permission to merge Regula fence
  environments or weaken their ownership checks.
- [4a727ace](https://github.com/rbeauchamp/acorn/commit/4a727ace81496a1acb417f6355e78de9760a1168)
  used standard Ubuntu x64 and separated pinned dependency provisioning from the cold
  project gate. Platform/toolchain/lock identities scoped artifact reuse; project outputs
  and acceptance remained uncached.

The public delivery record says macOS missed both its former 300s budget and its explicitly
authorized 360s budget. Those statements are delivery-record claims; the 239s run at 6d3e95bf
Ubuntu result was independently read from job metadata and logs. A deadline increase
changes policy, not throughput. Neither Acorn's budget nor its runner choice overrides
another repository's requirements. No private Acorn source is required for this guidance.

## Skill authoring

This skill follows the system `skill-creator` guidance and OpenAI's
[Rethinking skills and prompts for GPT-6 Astra](https://developers.openai.com/blog/rethinking-skills-and-prompts-for-gpt-6-astra):
use a narrow discovery description, expose details when relevant, and retain decision-bearing
constraints instead of prescribing a long fixed itinerary. Repository rules remain authoritative.

[RG4001]: https://rbeauchamp.github.io/regula/dev/rules/RG4001/
