# Rule source fixtures

These files are the source of truth for all twenty-two rule-reference examples. The rule
registry embeds each rule's `Fixed` and `Violation` file verbatim as its compliant and
noncompliant example, so diagnostics, `lake exe regula` and the agent briefing show these exact
bytes, except that RG1003's stand-in dependency and RG2001's runner requests are qualification
inputs, for which they state the correction instead; editing a file rebuilds the registry. They are intentionally outside every positive Lake
library. A violation can elaborate successfully;
the actual registered detector must produce its advertised result.

[`corpus.json`](corpus.json) fixes expected rule IDs, reasons, modes, subjects and locations.
The [architecture guide](../../docs/guides/architecture.md#rule-examples) gives each source pair's exact
remediation, accepted-example and diagnostic-demonstration distinctions, qualification
commands, and the export and trust contracts of the rule-reference website.
