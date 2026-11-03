# Repository instructions

## Mission and scope

- This repository delivers Regula. `README.md` states its purpose and the owner's constraint on all work under "Purpose and constraint", `specification/README.md` states each check and what is proved of it, and `specification/confirmation.md` records each decision of the owner's.
- Regula's checks are exactly RG1001 to RG1006, RG1010, RG1011 and RG2001. `lean/Regula/` implements them, and `specification/` states and proves them.
- Simplicity governs every change, by the owner's constraint of 2026-11-01, which `README.md` states under "Purpose and constraint" with the owner's decision on the size of the full verdict. Read it before adding or repairing anything.
- RG1010 is the language check, which reads each source file before anything is compiled and refuses anything outside a closed set. Its table `lean/Regula/LanguageSet.lean` and its hypotheses H1 and H2 in `specification/README.md` are read again at each upgrade of Lean.
- `Regula.Contract` and `Regula.Decision` stay as a library that gives no verdict until the other project that imports them moves them.

## Start every task

- Verify the checkout and worktree status before making claims or edits. Record exact `HEAD`.
- Use `README.md` and `specification/README.md` to establish scope. Read every affected module completely before changing or auditing its Lean claims. When working an open issue, that issue is authoritative until closed; existing green checks are scoped results only.
- Read `CONTRIBUTING.md` before any change. It holds every rule that binds a change to Regula, the merge gate, and the lessons of past defects, stated as rules.
- Preserve unrelated changes. Use `tmp/` for isolated probes and remove your probes afterward.

## Maintaining this file

Keep this file for knowledge useful to almost every future agent session in this project. Do not repeat what the codebase already shows; point to the authoritative file or command instead. Prefer rewriting or pruning existing entries over appending new ones. When updating this file, preserve this bar for all agents and keep entries concise. A rule for changes belongs in `CONTRIBUTING.md`, and a decision of the owner's in `specification/confirmation.md`, with its effect stated where it governs work.
