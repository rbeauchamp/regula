# Security policy

Report a vulnerability privately through GitHub's [private vulnerability reporting](https://github.com/rbeauchamp/regula/security/advisories/new), not in a public issue. Include the commit, your Lean toolchain, what fails and the smallest reproduction.

A vulnerability is a project that a rule of the [specification](specification/README.md) must refuse and that passes, or a run of the checker that harms the machine that runs it. What the specification's [trusted base](specification/README.md#the-trusted-base) lists, such as a project's own code that runs during its build, is outside this policy until the base changes.

Regula has one maintainer, so it promises no response time. Fixes land on `main`. Regula has no supported release of its present form.
