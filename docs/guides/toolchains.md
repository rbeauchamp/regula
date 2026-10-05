# Supported toolchain

This Regula revision supports the exact Lean version and full commit declared by
[`RegulaPolicy.Compiler`](../../lean/RegulaPolicy/Compiler.lean), with the Elan selector in
[`lean-toolchain`](../../lean-toolchain). Both the version and the full commit must match.
That policy supplies the identity checked by Lake configuration, collection,
admission and `regula doctor`. The observed Core capability must also agree with that policy.

The [supported-toolchain pins](../../README.md#supported-toolchain) identify the separate
Mathlib integration dependency. See the contributor guide for
[dependency artifact reuse](contributing.md#share-one-mathlib-across-local-copies) and the
[release policy](contributing.md#release), and the adoption guide's
[compatibility table](adoption.md#1-require-regula) for published releases' toolchains.

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
