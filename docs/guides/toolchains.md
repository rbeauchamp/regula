# Supported toolchain

This Regula revision supports Lean **4.34.1**, commit
`5045d0056413266e57c625dcd7c365b10e377c52`. Both the version and the full commit must match.
`RegulaPolicy.Compiler` supplies the identity checked by Lake configuration, collection,
admission and `regula doctor`. The observed Core capability must also agree with that policy.

The Mathlib integration package pins Mathlib `v4.34.1`
(`d13f23b723b8a846827a245b89c10fc7d3f11612`); its [only source change from `v4.34.0`](https://github.com/leanprover-community/mathlib4/compare/v4.34.0...v4.34.1)
is the matching `lean-toolchain`. Verso and the other dependency revisions are unchanged.
Dependency artifacts remain keyed by the compiler identity and package pins; artifacts built
with Lean 4.34.0 are not reused for this compiler. The ordinary verification deadlines remain
unchanged. Published Regula releases keep their original toolchains in the
[compatibility table](adoption.md#1-require-regula); changing compiler support calls for a new
minor release, not relabelling an existing release.

Install the pinned release through Elan. `doctor` resolves a project's selector only among the
exact names Elan lists as installed, then compares that compiler's reported identity. It installs
nothing; a toolchain override cannot hide a project pinned to an unsupported compiler.

Unsupported versions require a future deliberate port, with updated contracts, qualification,
acceptance and review. This revision provides no candidate preparation or qualification command,
source compiler installer, source dependency mode, or compiled toolchain snapshot interface.
Historical diagnostic envelopes remain inadmissible as ordinary audit evidence. Historical
published artifacts and their notices are unchanged.

See [contributing](contributing.md) for setup and verification and
[adoption](adoption.md) for release compatibility.

Compiler self-reports, Elan, the compiler/runtime and filesystem effects remain trusted. Exact
identity agreement does not authenticate a modified compiler binary. Regula's audit-input
snapshots still establish unchanged-input evidence; they are independent of removed compiler
packaging.
