# Rule source fixtures

These files are the source of truth for all twenty-two rule-reference examples. The rule
registry embeds each rule's `Fixed` and `Violation` file verbatim as its compliant and
noncompliant example, so diagnostics, `lake exe regula` and the agent briefing show these exact
bytes, except that RG1003's stand-in dependency and RG2001's runner requests are qualification
inputs, for which they state the correction instead; editing a file rebuilds the registry. They are intentionally outside every positive Lake
library. A violation can elaborate successfully;
the actual registered detector must produce its advertised result.

## Authoring

Add or change the source files first, and keep a pair's `correction` sentence and its fixtures
in the same change. Select the detector stage that actually supports the rule; do not force a
project-only rule into an editor callback. Then fix the intended diagnostic specification in
[`corpus.json`](corpus.json): expected rule IDs, reasons, modes, subjects and locations, listing
every additional finding (generated declarations and underlying diagnostics included; none may
disappear). Location fields are explicit expected coordinates, checked against the exact source
by the registry codec. A source-free detector keeps its module or project location; never
manufacture a source range for it.

A `Violation` phase's `diagnostics` template may use placeholders. Each fills a whole string
field, never a substring (`RegulaQualification.Template.replace`), and refers to an invocation
path or exact source-owned bytes; placeholders never rewrite actual findings.

| Placeholder | Value |
| --- | --- |
| `$SOURCE` | The path of the phase's source in its workspace; in a project run, the path the checker captured for the `Example` module in its owned copy. |
| `$SOURCE_TEXT` | The exact text of that source file. |
| `$PROJECT` | The phase's workspace root. |
| `$DOCS` | The workspace's `docs` directory. |
| `$SNIPPET_URI`, `$SNIPPET_TEXT` | For a documentation `Violation` with `"snippet": [start, stop, origin]`: the virtual location `<docs>/<origin>#lean-snippet` and the UTF-8 text of the source's bytes `start` to `stop`. |

Snippet slices are explicit fixture byte anchors, not a second Markdown detector; the production
Markdown scanner still owns classification and fence semantics.

The [architecture guide](../../docs/guides/architecture.md#rule-examples) gives each source
pair's accepted-example and diagnostic-demonstration distinctions, the qualification commands,
and the export and trust contract the rule-reference website consumes.
