# Rule source fixtures

These files are the source of truth for all twenty-three rule-reference examples. The rule
registry embeds each rule's `Fixed` and `Violation` file verbatim as its compliant and
noncompliant example, so diagnostics, `lake exe regula` and the agent briefing show these exact
bytes, except that [RG1003]'s stand-in dependency and [RG2001]'s runner requests are qualification
inputs, for which they state the correction instead; editing a file rebuilds the registry.
Every file here is intentionally outside every positive Lake library of this repository.
[RG2002]'s `Cli.lean` is the root of the `lean_exe cli` that both of its manifests classify; only
inside the runner's scratch fixture project does it become the module `Example.Cli` of that
project's `Example` library. A violation can elaborate successfully;
the actual registered detector must produce its advertised result.

[`corpus.json`](corpus.json) fixes expected rule IDs, reasons, modes, subjects and locations.

Add or change source files first. Select the actual supported detector stage; do not force a
project-only rule into an editor callback. Fix the intended diagnostic specification in
`corpus.json`, including all additional findings. Its location fields are explicit expected
coordinates, checked against the exact source by the registry codec. Whole-field placeholders
refer to invocation paths or exact source-owned bytes; they never rewrite actual findings.
Markdown snippet slices are explicit fixture byte anchors, not a second Markdown detector.
The production Markdown scanner still owns classification and fence semantics.

The [architecture guide](../../docs/guides/architecture.md#rule-examples) gives each source pair's exact
remediation, accepted-example and diagnostic-demonstration distinctions, qualification
commands, and the export and trust contracts of the rule-reference website.

[RG1003]: https://rbeauchamp.github.io/regula/dev/rules/RG1003/
[RG2001]: https://rbeauchamp.github.io/regula/dev/rules/RG2001/
[RG2002]: https://rbeauchamp.github.io/regula/dev/rules/RG2002/
