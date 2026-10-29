Replace this paragraph with a summary of the change: what it does and why. The description becomes the body of the one commit that the change adds to `main`. Write it for a reader who did not see the work.

Keep the four headings below, with the same text and in the same sequence. Replace the text under each heading with the items of this change. If a heading has no item for this change, write None and the reason. Write each paragraph and each list item on one line. Then remove this paragraph.

# Mission accounting

Give these items for the change:

- **Mission properties.** The properties of the mission of the project that the change depends on.
- **Formal claims.** The theorems, types, constructions and checks in the code that give each property. Give the name or the path of each.
- **Trusted base.** Each assumption that the change uses without a proof, with the source that states it.
- **Where a proof can make it smaller.** Each property that still depends on such an assumption, and the proof that can remove that assumption.
- **Specifications.** For each specification that the change adds or changes, tell in plain words what it requires, permits and does not permit. Give examples, and tell which cases it does not include.

Write each claim no stronger than its evidence.

# Decisions

- Give each decision of the change and its reason in one sentence, so that a reader can change it later.
- If the change does less or more than its issue or its intent, tell the difference, the decision and its reason.

# Accepted risk

- Give each risk that the change accepts without a proof, a type or a check.
- For each risk, tell what can go wrong, where, and why the cost is small or easy to correct.
- Give each review finding that does not stop the merge, and its reason.
- Give each check that did not run or did not complete, and the cause.

# Root cause

This section is only for a change that repairs a defect. For a different change, write None and tell that the change repairs no defect.

- **Failed property.** The property of the mission that failed.
- **Contract.** The executable contract that prevents each failure of this class: a proof, a type, a construction or a check.
- **Assumption.** The step where the work used an assumption in place of that contract.
- **Class.** The class of the defect, the search that found its sites, and each site. For each site, tell if the change repairs it, if an issue records it, or if it is an accepted risk.
- **Cause.** Why the class was possible, and why no check found it. Go from the intent through the specification, the design, the code and the checks to the instructions and tools of the author. Stop at a part that a change can correct. Do not give an error of a person as the cause.
- **Correction.** The change to that part, in this pull request or in the issue that records it.
