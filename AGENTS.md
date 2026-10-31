# Repository instructions

## Mission and scope

- This repository delivers Regula, a checker of Lean builds that exists to be trusted and to be the example of how Lean 4 code should be written. `README.md` and `specification/README.md` state the purpose in their first paragraph.
- Regula's checks are exactly RG1001 to RG1006, RG1010 and RG2001. `lean/Regula/` implements them, and `specification/` states and proves them. Regula gives up any rule, feature or package it cannot prove rather than patching it, documenting a limit or keeping a stated gap.
- RG1010 is the language check, which reads each source file before anything is compiled and refuses anything outside a closed set. Its table `lean/Regula/LanguageSet.lean` and its hypotheses H1 and H2 in `specification/README.md` are read again at each upgrade of Lean.
- `Regula.Contract` and `Regula.Decision` stay as a library that gives no verdict until the other project that imports them moves them.

## Start every task

- Verify the checkout and worktree status before making claims or edits. Record exact `HEAD`.
- Use `README.md` and `specification/README.md` to establish scope. Read every affected module completely before changing or auditing its Lean claims. When working an open issue, that issue is authoritative until closed; existing green checks are scoped results only.
- Every delivery PR requires independent review by at least one fresh-context reviewer. Scope reading and checks to the changed claims; use distinct reviewers for materially different semantic and implementation risks.
- After repair, obtain focused independent verification of the affected claims. Reuse evidence whose relevant inputs and claims remain unchanged; rerun only invalidated checks.
- Preserve unrelated changes. Use `tmp/` for isolated probes and remove your probes afterward.

## Issue delivery

- When working an issue, its acceptance criteria define the deliverable. A planning issue or an agent's review response alone is not a completed delivery.
- Complete authorized implementation, local repairs, checks, and targeted review without repeatedly requesting permission. Use existing session authorization for external actions; requiring a PR does not itself grant permission to publish, merge, or change visibility.
- Mark an issue Done only after its acceptance criteria and required review/checks pass and its completing PR is integrated. A partial PR references the issue without closing it.

## Lean-specific requirements

- State the exact elaborated theorem, quantifiers, assumptions, and transitive dependencies. Do not strengthen a Lean result into a claim about an unrelated implementation.
- Ban `sorryAx`, project logical `axiom` declarations, `sorry`, and `admit` from every proof surface. Express assumptions as parameters, hypotheses, or proof-bearing fields.
- Report exact foundation strength: Kernel-only is empty; Choice-Free permits only `propext` and `Quot.sound`; Standard-Logical additionally permits `Classical.choice`. Do not treat these as general software-assurance rankings.
- Distinguish logical and executable decidability, noncomputability, kernel reduction, native evaluation, `partial`, `unsafe`, runtime replacement, `extern`, and FFI wherever the distinction affects a Lean claim.
- Discover modules, declarations, and dependencies through Lean/Lake semantics, not fixed file lists or source-format regexes. Unknowns and omissions fail the affected claim.

## Implementation language

- Project-owned code is Lean 4, with explicit behavioral contracts proved about the actual definitions used by callers. A translation into Lean or a successful build alone does not establish behavioral correctness.
- Do not add Python, shell or other implementation-language programs. Any shell script requires explicit operator approval.
- Use Lean/Lake APIs where available. Distinguish pure proved behavior from trusted compiler/runtime, filesystem, and process effects.

## Changes and verification

- Revise the specification from the intent first, independently of the code, then the code. Change the specification, the proofs and the checker together when they encode the same claim. After moving a path or changing a command, search the whole repository for the old form before review.
- Keep documentation, docstrings, diagnostics and checker output no stronger than the exact Lean property established. Before review, check each new sentence that cites a theorem or check against its actual statement, hypotheses, and caller; name what it leaves uncovered. No text claims that Regula is free of bugs.
- Respect the trusted base that `specification/README.md` lists, and change that list when a change changes it.

No package of this repository requires Mathlib. Use `lake build` for the Lean development loop. The specification is a package of its own: `lake build` in `specification/`, from a shell whose working directory is that directory.

The merge gate is the local gate, `lean --run lean/Regula/DiagnosticsGate.lean local`. Its steps are `localSteps` in that file. It needs the pinned toolchain and a read of lean-intent from GitHub. The no-mistakes validation pipeline runs it as its Test step on each commit that it validates, as `.no-mistakes.yaml` configures. The repository has no CI workflow. Merge requires a pass of the local gate on the reviewed head and applicable focused review. Preserve PR, signature, history, and conversation protections. Finish authorized publication, exact-head merge, and owned branch cleanup.

The pipeline reads `.no-mistakes.yaml` and the PR template from the default branch, so the paths they name, `lean/Regula/DiagnosticsGate.lean` and `lean/Regula/TestListing.lean`, move only in two steps: first a change that keeps both paths working, then one that uses the new path.

Report the tested Lean version, the Lake modules and declaration/axiom coverage, applicable diagnostics, and failures or missing evidence.

## Maintaining this file

Keep this file for knowledge useful to almost every future agent session in this project. Do not repeat what the codebase already shows; point to the authoritative file or command instead. Prefer rewriting or pruning existing entries over appending new ones. When updating this file, preserve this bar for all agents and keep entries concise.
