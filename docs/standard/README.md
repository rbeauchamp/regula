# Regula standard

The Regula standard is written in [Verso](https://github.com/leanprover/verso). Its only source
is the `RegulaStandard` library of the Verso package in [`website/`](../../website/):
[`website/RegulaStandard.lean`](../../website/RegulaStandard.lean) (front page and introduction)
and [`website/RegulaStandard/`](../../website/RegulaStandard/) (modules 0–9 and Critical
Violations). There is no Markdown copy.

It is published with the rule reference at
<https://rbeauchamp.github.io/regula/dev/standard/>; every section and checklist row has a
stable anchor there (for example
`https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#DOC-04`).

Every `lean` block of the standard is one complete Lean module, elaborated where it is written
when the standard is built, and audited by `./scripts/verify.sh docs`; the convention is in the
standard's introduction. The Verso sources are plain text, so an agent without network access
reads the standard there, including from an adopting project's `.lake/packages/regula/`.
