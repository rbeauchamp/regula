# Supported toolchain

This Regula revision supports Lean **4.34.0**, commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. Both the version and the full commit must match.
`RegulaPolicy.Compiler` supplies the identity checked by Lake configuration, collection,
admission and `regula doctor`. The observed Core capability must also agree with that policy.

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
