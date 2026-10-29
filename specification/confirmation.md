# The owner's confirmation of the specification

This file records the owner's answer to the plain-word consequences of [the specification](README.md).

- **Date**: 2026-10-29.
- **The owner's words**: "Confirm all".
- **Source**: the owner's answer to the review of the consequences, which the owner's agent passed to the author of this specification on that date.
- **Answer**: each consequence is confirmed, with each recommendation that the review gave.

## What the answer covers

- Each item of the section "Consequences for the owner's confirmation" of the specification, as this file's commit gives it.
- The fate of the Mathlib integration package in `integration/mathlib/`. It retires with [#484], when [#484] has fixed and recorded the Mathlib members of its two allowlists.
- Seven decisions, each as its recommendation stated it:
  1. A recursion helper is admitted by its form ([RG1006]). Its execution is the question of [RG3002] under a checked claim.
  2. Commands that run code and options set in source stay unseen, as an accepted risk (`RG2007`).
  3. The owner's committed confirmation record names the deliverables of a project. A deliverable that the record names and the project lacks fails `RG6001`, and a project with no record fails too.
  4. The structural check that a record does not reach its implementation stays the rule. The owner's record carries the order of confirmation and implementation, and the owner's act.
  5. The three decision kinds stay for adopters ([RG1008]). Regula registers its own admission decisions with two-way contracts.
  6. A cycle of runtime replacements fails [RG3001].
  7. `RG6001` also requires lean-intent's O2 before a run and its degenerate check of each record.

## The form of this record

lean-intent's statements (`LeanIntent.Statement`) record an answer to one consequence of one intent record, with the text that lean-intent shows for it. These consequences are of the specification document, not of an intent record. Thus this file states the same facts in plain words: the date, the owner's words, the source and the consequences that the answer covers.

The file is not signed. Its authority is that of the commit that adds it.

[#484]: https://github.com/rbeauchamp/regula/issues/484
[RG1006]: https://rbeauchamp.github.io/regula/dev/rules/RG1006/
[RG1008]: https://rbeauchamp.github.io/regula/dev/rules/RG1008/
[RG3001]: https://rbeauchamp.github.io/regula/dev/rules/RG3001/
[RG3002]: https://rbeauchamp.github.io/regula/dev/rules/RG3002/
