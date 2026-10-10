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

These values are observations on hosted `ubuntu-24.04` runners with four processors, and they
are not bounds. In 18 CI runs, the time of the first acceptance step was 226 s to 414 s with its
420-second deadline. An examination of five of those runs gave the time of each phase. In the
slowest of those five runs the step took 405 s, and in the fastest it took 236 s. Each phase was
1.6 to 1.8 times longer in the slowest run than in the fastest run. Thus the cause of the
difference was the speed of the runner.

In [run 37513374192](https://github.com/rbeauchamp/regula/actions/runs/37513374192), the time of
the step was 364 s. The build was 173 s, `qualify combined` was 25 s and the gate was 157 s. The
isolated build of the gate was approximately 66 s of those 157 s.

The next values are an estimate from the durations that Lake logs for each job. Lake measures
each duration with `IO.monoMsNow` before and after the job, and thus a duration is elapsed time.
A job that is idle until it gets a processor, or that uses more than one thread, logs its
duration in the same way. Thus the sum of the durations is not processor work. The build logged
273 jobs, and the sum of their durations is 640 s. By those durations, approximately four jobs
were in progress from the start of the build to its end.

The isolated build of the gate logged 163 s, with one or two jobs in progress during its last
40 s. The modules that the gate executable imports logged 414 s of the 640 s. The longest import
chain of those modules, with the C file of the gate, logged 96 s.

The estimate uses two assumptions. The first assumption is that each job uses approximately one
processor for its logged duration. The second assumption is that this duration does not change
when other work operates at the same time. If the two assumptions are correct, approximately
225 s of the work of the build was not necessary before the gate. The first estimate of the time
of the step on that runner was thus approximately 300 s. No measurement shows that the two
assumptions are correct.

After that change, the driver built the gate first. Then it operated the gate at the same time
as the complete build and the other checks. A later change removed that schedule
([one build for the first acceptance step](#regula-one-build-for-the-first-acceptance-step-2026-10-07)).

In one local probe (14 processors, two threads for each side), the second build compiled 106
jobs. None of those jobs was a module that the gate imports. The gate recorded the same input
identity as the sequential run.

That probe shows that the arrangement operates. It does not show the hosted gain. The hosted
times of the new schedule are at the end of this section.

Two items are not established. The first item is that two Lake processes in one build directory
do not interfere (one of them builds nothing here). The second item is an upper bound of the
time of the step.

Four pairs of local runs compared the new schedule with the sequential run of the first
acceptance step, on one machine with 14 processors. Each run started with no build output of the
root package, and other projects used the machine during the runs. The times of the runs were
158 s to 194 s. In each pair, the difference of the two times was smaller than 8 s
(+7.2 s, +1.0 s, -0.5 s and -3.9 s, new schedule minus sequential run). Thus those runs showed no
gain.

With the new schedule, the gate started 32 s to 37 s earlier in the step and took 32 s to 39 s
longer. Lake logged the durations of the jobs of the isolated build of the gate. Their sum was
182 s to 261 s with the new schedule and 103 s to 116 s with the sequential run. Thus the second
assumption was not correct on that machine.

In the last pair, the processor time of the step was 727 s with the new schedule and 703 s with
the sequential run. Thus the two schedules used approximately the same processor time in that
pair. The measurement does not identify the cause of the longer durations. During that pair,
other processes used approximately three to four processors, and the unused memory of the
machine decreased to approximately 100 MB. The hosted runner is a different machine with four
processors. Thus these runs do not show the hosted result.

After those runs, the driver started each command that operated at the same time as the gate
with `nice -n 19`. The gate kept the priority of the driver. The purpose was that the other
commands did not make the gate slower. The program and the arguments of each command did not
change.

The step ended when the gate and the other commands were complete. It ended when the gate ended
only if the other commands ended first.

One local pair of cold runs compared that schedule with the sequential run on the same machine.
A sampler looked for builds of a different directory each 10 s, and it found none during the two
runs. The time of the step was 121.6 s with the schedule and 134.3 s with the sequential run.
The gate took approximately 89 s at the same time as the other commands and approximately 78 s in
the sequential run. The other commands ended 34 s after the start of the gate.

Thus the gate was approximately 11 s slower than alone. The low priority did not remove the full
delay on that machine. Three more runs are not a part of that pair. One run of the schedule took
127.0 s, with no record of other builds. Two sequential runs took 148.2 s and 140.4 s, and a
build of a different directory operated during each of them. One pair is not a distribution.

The estimate for the hosted reference run with low priority is approximately 275 s to 300 s,
where the step took 364 s. It has three parts. They are approximately 7 s before the early
build, approximately 110 s for the early build, and 157 s to 180 s for the gate. The larger value
for the gate uses the delay of the local pair.

That estimate is a prediction, and it uses three assumptions. The first two assumptions are that
the scheduler gives the gate the processors that it can use and that memory is not the limit.
The third assumption is that the other commands end before the gate ends. If they end after the
gate, their time after the gate adds to the estimate. These notes show that the other commands
ended first only for the local pair, on 14 processors.

Two hosted runs then measured the schedule with low priority
([pull request 252](https://github.com/rbeauchamp/regula/pull/252), CI run 37556704230,
attempts 1 and 2). The first step took 386 s and 351 s. The documentation step of the same jobs
took 243 s and 222 s, and the change does not touch its work. Thus the ratio of the two steps
compares the schedules on runners of different speeds. That ratio was 1.59 and 1.58.

Two sequential runs measured the tree of commit `4e9a1fd8`, which was the base of the pull
request for the two hosted runs. Their ratios were 1.71 and 1.74 (CI runs 37542593631 and
37540594216, 295 s and 351 s for the first step). The comparison is between that tree with the
sequential schedule and the tree of the pull request with the new schedule. Thus the ratios
compare two trees and not only two schedules.

By those ratios, the measured gain is approximately 8 percent of the first step, which is
approximately 30 s at those runner speeds. The estimate above is a gain of 65 s to 90 s on the
reference run. The hosted runs refute that estimate.

The sample is small: two runs for each schedule, with the sequential runs on the tree of commit
`4e9a1fd8`. Two earlier trees each had two sequential runs. Their ratios were 1.68 and 1.59 for
one tree, and 1.68 and 1.58 for the other. Thus two runs of one tree can give ratios that are
0.10 apart. The lowest ratio of a sequential run is equal to the ratio of the schedule. The gain
is a measurement on this sample, and it is not established.

The gate took 251 s and 229 s at the same time as the low-priority commands. It took 139 s and
164 s alone in the two sequential runs of the tree of commit `4e9a1fd8`. Thus `nice -n 19` did
not keep the gate at the speed that it has alone, and the first assumption was not correct on
the hosted runner. A possible cause is that the four processors of the runner are hardware
threads of two cores. No run measured the processor topology or the processor time. Thus that
cause is a hypothesis.

In the two hosted runs, the other commands ended approximately 25 s before the gate. Before
that, the two chains operated at the same time.
Thus a different sequence of the same commands can probably decrease the time only a small
quantity more. For more margin, less work in the step or a second runner is necessary. In the
slower of the two runs, the margin of the step was 34 s.

After those runs, `main` moved to commit `5dcae344`.
[CI run 37560297066](https://github.com/rbeauchamp/regula/actions/runs/37560297066) measured
`main` at that commit, with the sequential schedule. The 420-second deadline killed
`./scripts/verify.sh` in the first step of that run. The step took 425 s and ended with exit
status 137. The documentation step did not start.

These notes record no hosted run of the new schedule on a tree that contains that commit. Each
hosted figure of the new schedule in these notes is for the tree with the base `4e9a1fd8`. Those
figures are the times 386 s and 351 s, the margin of 34 s and the gain of approximately
8 percent. Thus they do not show the time or the margin of the step for a later tree.

An independent review of the first version found one path on which the driver did not wait for
the gate. On that path, the line that reported the failure of a different command could raise an
exception before the driver waited for the gate. At this time, the orchestration of the driver
is a `BaseIO` action. One pure decision with a registered decision contract
(`RegulaVerification.passed`) gives the result from the end of each command.

## Regula: one build for the first acceptance step (2026-10-07)

The first acceptance step built the claimed libraries two times. The root build compiled them
in the checkout, and the gate compiled them again in its isolated copy. Five hosted runs
measured the tree of 71 owned modules with the sequential schedule (CI runs 37590092134,
37566600166, 37566370794, 37558661121 and 37560297066). In the first four runs, the first step
took 309 s, 318 s, 410 s and 420 s. The deadline killed the fifth run at 425 s.

In those runs, the build in the copy of the gate took 55 s to 76 s. That is 17.7 to 17.8 percent
of the step in each run. The root build was 41 to 44 percent, and the inspection was 26 to
27 percent. Thus the difference between the runs is the speed of the runner.

At this time, the driver makes one copy of the checkout, and the complete step operates in it
([proofs and boundaries](../../../../docs/guides/proofs-and-boundaries.md#the-acceptance-boundary)).
The gate audits the build output of that copy and makes no copy of its own. The schedule of
pull request 252 was a stopgap, and the driver has one sequence of commands again. The gate
cannot start before the build of the copy ends, because it audits that build output.

The figures of that stopgap are these. Its two hosted runs took 351 s and 386 s, with ratios of
1.58 and 1.59 to the documentation step. That is 5 to 8 percent less than the sequential runs.
For the slowest runner observed, that gives 387 s to 400 s by calculation, which is a margin of
20 s to 33 s.

The calculation for this sequence uses the killed run 37560297066 as the slowest runner
observed. It removes the second build of the claimed libraries, which took 76 s in that run. It
adds the 17 jobs that only the copy of the gate compiled. It also adds two Lake processes of
the gate that compile nothing. The result is 352 s to 365 s under the 420-second deadline,
which is a margin of 55 s to 68 s. That result is a prediction and not a measurement.

One sequence with two chains was also possible. An estimate for it is 328 s to 341 s on the same
runner. That estimate uses the gain of the two hosted runs of the stopgap for the work that
overlaps, which is 12 percent. A second Lake process then writes the build directory that the
gate inspects. Thus the change does not use two chains.

A local measurement with two threads gave these times. The copy took 0.15 s, and the build took
106 s. The registry checks took 2 s, the qualification controls took 20 s, and the gate took
67 s. The copy had 488 files of 6.7 MB.

In that measurement, the Lake builds of the gate compiled no job. After the
rename of the build output to a checkout that had none, the documentation step passed. It
compiled only the five C files of the Markdown checker, as a hosted run of `main` does.

The criterion for the hosted result was set before a hosted run of this sequence. The
documentation step does not change, and thus it measures the runner. The ratio of the first
step to the documentation step was 1.60 to 1.67 in the four complete sequential runs. The
prediction for this sequence is 1.34 to 1.45. Two hosted runs with a ratio of 1.47 or less
confirm the prediction. A ratio of 1.55 or more refutes it.

The criterion has the date 2026-10-07. Two hosted runs then measured this sequence on the head
`63993d55` of [pull request 262](https://github.com/rbeauchamp/regula/pull/262). They are
attempts [1](https://github.com/rbeauchamp/regula/actions/runs/37637451453/attempts/1) and
[2](https://github.com/rbeauchamp/regula/actions/runs/37637451453/attempts/2) of CI run
37637451453, on two runners.

| Attempt | First step | Documentation step | Ratio | Margin of the first step | Margin of the documentation step |
| --- | --- | --- | --- | --- | --- |
| 1 | 283 s | 205 s | 1.38 | 143 s | 215 s or more |
| 2 | 265 s | 190 s | 1.39 | 161 s | 230 s or more |

The two ratios are 1.47 or less. Thus the two runs confirm the prediction by that criterion. The
margin of a step is the time that stays before its 420-second deadline. The deadline of the
first step started approximately 6 s after the start of the step.

For the slowest runner observed, the margin is calculated and not measured. The calculation
uses the 425.5 s of the killed run 37560297066 with the sequential schedule. It multiplies that
time by a measured ratio of 1.3804 or 1.3947. It divides the product by a sequential ratio of
1.597 to 1.674. The result is 346 s to 367 s under the deadline, which is a calculated margin
of 53 s to 74 s. The sample is two runs.

Two reviews of an earlier design found nine defects. That design built in the checkout from
empty build output and recorded that fact for the gate. Each defect was in a comparison of two
observations at two times, and each correction added one more such comparison. The design with
the copy has no such comparison of the audited inputs. The gate reads the copy that the driver
built, and the result names the one statement that the gate cannot read.

## Regula: the gate beside the rest of the first step, after a prebuild (2026-10-10)

Issue [#324](https://github.com/rbeauchamp/regula/issues/324) asked for a margin of the first
step again. The part of the step under the deadline is the window from `verification: start git
diff --check` to `local verification: PASS`. On the slow runner class, that window took 372 s to
394 s in the five CI runs of `main` from `b2215df3` to `8e11edb4`. The documentation step took
271 s to 286 s in the same runs.

The job logs give the parts of the window in those runs. The build took 207 s to 222 s, the
registry checks 2 s and the qualification controls 26 s to 29 s. The gate took 135 s to
139 s. The build is processor-bound. Lake logged 798 s to 853 s of jobs for each build, on 4
processors. In each 10 s of the build of `8e11edb4`, approximately four jobs ran, except in the
last 10 s.

The ratio of the first step to the documentation step was 1.35 to 1.45 in 24 runs of `main`.
Those runs are from `0464b88e` to `8e11edb4`, on the two runner classes. Thus that ratio
measures the step and not the runner. On the slow class, the window grew from 344 s at
`0464b88e` to 394 s at `64fe9908`. The jobs of the build grew from 691 s to 853 s, and the gate
from 129 s to 139 s.

The gate prints no time spans on CI. One local run with `REGULA_TIMING=1` gave these parts of a
gate of 80 s:

- Before its audit: 12.4 s. That run also cloned the Verso packages, which CI provisions before
  the step.
- The module-scope preflight: 5.6 s, seven workers one after the other.
- The inspections: 46.8 s. `RegulaPolicy` took 35.3 s, and `RegulaCore` 34.5 s.
- The freeze and the acceptance of the results: 12.1 s.

In that run, `RegulaCore` started 12.3 s after the inspections started, because three smaller
environments came before it in claim order. Its inspection ended last. The gate does no work two
times that this change can remove. The preflight imports each environment, and the inspection
imports it again, but the preflight must refuse before the inspections start.

Lake logged 655 s to 664 s of jobs for the targets of the gate and their imports. A schedule of
the logged jobs over their imports, on four processors, gave 213 s to 217 s for the complete
build. The logs gave 218 s to 222 s. The same schedule gave 181 s to 186 s for the targets of the
gate alone.

This change has three parts:

- The driver builds the targets of the gate first. The gate then runs beside the rest of the
  step, which runs at low priority.
- The inspection starts the environment with the most owned modules first, of those that can
  start.
- The preflight runs three workers at a time.

The prediction for the slow class is a window of 306 s to 345 s. The lower value adds no time
for the commands at low priority. The higher value adds 20 percent to the gate. A previous note
above shows that the hosted gain of such a schedule was less than half of its prediction. Thus
the criterion was set before a hosted run.

Three slow-class runs with a window of 360 s or less confirm the target of a margin of 60 s. A
slow-class run with a window of more than 375 s refutes the prediction. A slow-class run has a
documentation step of 255 s or more.

One local run of this change on 14 processors took 114 s for the window. The local profile of
`e0232383` took 130 s without its clone of Verso. In that run the gate took 75 s, and it ended
36 s after the commands at low priority. During the gate, the build wrote only the outputs of
other modules, the C objects for `qualify` and `docFenceAudit`, and those two executables. It
wrote no `.olean`, trace or hash file of a claimed module, and no C object that `axiomGate` or
`auditApp` links. That is an observation of one run, not a proof.

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
