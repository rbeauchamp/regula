# Security policy

## Report a vulnerability

Report it privately through GitHub's
[private vulnerability reporting](https://github.com/rbeauchamp/regula/security/advisories/new)
(**Security → Advisories → Report a vulnerability**), not in a public issue. Richard Beauchamp
is the responsible maintainer. Keep the details in the private report until a fix is published.

Include:

- the affected release or commit, and your Lean toolchain;
- the impact: which rule's guarantee or which boundary below fails, and what that gives an
  attacker or a violating project;
- the smallest reproduction (a Lean project, file or command), or the reasoning that shows it.

Regula has one maintainer, so it promises no response time. A confirmed vulnerability is fixed on
`main` and in the next release, and its advisory is then published.

## Supported versions

Only `main` and the [latest published release](https://github.com/rbeauchamp/regula/releases/latest)
receive fixes; earlier releases are not patched. Each release supports exactly one Lean release,
so moving to the latest release can also mean moving your `lean-toolchain`.

## What counts as a vulnerability

Regula's guarantees are those its [rule reference](https://rbeauchamp.github.io/regula/dev/rules/)
and [standard](https://rbeauchamp.github.io/regula/dev/standard/) state, within the trust boundary
recorded in [proofs and boundaries](docs/guides/proofs-and-boundaries.md). A vulnerability is a way
to break one of them on purpose:

- **A violating project that passes.** Lean source makes `lake lint` exit 0, or an audit report a
  `completed` account, while a claimed declaration breaks a rule's stated guarantee: for example,
  a `sorryAx`, project axiom, unknown axiom or axiom outside the claimed foundation in its
  transitive dependencies (RG1001–RG1003, RG1005); a native-proof axiom, a `partial` or `unsafe`
  definition or a recursion helper admitted outside the conditions of standard §7.4–§7.5 (RG1004,
  RG1006); or an unresolved `extern` or `implemented_by` path (RG3001), or in `checked` mode an
  unproved one (RG3002), that the audit accepts. This includes declarations the project's own
  macros, elaborators, tactics or evaluators produce (§7.5).
- **Regula acting outside what it documents.** Regula runs external programs with argument
  arrays, never through a generated shell program, and keeps scratch work under the checked
  project's `tmp/`. An input, such as a path or a module or file name, that makes Regula's own
  code run a command, or write or delete a file, beyond what its documentation describes is a
  vulnerability.
- **A release or site published unchecked.** A flaw in the CI and release workflows
  (`.github/workflows/`, `lean/Regula/Release.lean`) that could publish a release, a tag or the
  rule-reference site from content that did not pass the checks the
  [release procedure](docs/guides/contributing.md#release) requires, or leave a release's tag
  naming a commit other than its checked release commit.

## What does not

- **Code the audit builds.** Auditing a project runs its code with your permissions: Lake runs a
  `lakefile.lean`, elaboration runs the project's macros, elaborators and tactics, and Regula's
  report worker runs its modules' initializers. Regula is not a sandbox. The standard's boundary
  assumes the pinned Lean process and the libraries it imports are not compromised (§7.5), so code
  that attacks the checker process or your machine this way is outside it. Audit only code you
  would build; to check an untrusted proof against a fixed statement, use
  [comparator](https://github.com/leanprover/comparator).
- **What Regula trusts.** Lean's kernel, elaborator, compiler and runtime, Lake, Git, the
  filesystem, the operating system, GNU timeout and imported libraries such as Mathlib are trusted;
  report their vulnerabilities to their maintainers. So are the GitHub services the release relies
  on: Actions, commit-signature verification, tags and immutable releases.
- **Semantic review.** Whether a theorem states what you meant, and the other
  [review obligations](docs/guides/architecture.md#coverage-of-the-standard) every accepted account
  lists, are left to review; a pass never claims them.
- **Ordinary bugs.** A false positive, or a missed finding that nobody could use to make a violating
  project pass, belongs in a [public issue](https://github.com/rbeauchamp/regula/issues). If you
  are unsure, report privately; you will be asked to open a public issue if it is not a
  vulnerability.
