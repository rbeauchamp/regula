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

## Scope

Regula's guarantees are those that its
[rule reference](https://rbeauchamp.github.io/regula/dev/rules/) and
[standard](https://rbeauchamp.github.io/regula/dev/standard/) state, in the trust boundary that
[proofs and boundaries](docs/guides/proofs-and-boundaries.md) records. These guarantees are for
honest code: code that does not deliberately change Lean's environment, compiler or build to make
a check pass. Code that makes such a change through a mechanism for which the standard or a rule
page states a check is also honest code. Ordinary declarations, attributes such as
`implemented_by`, `extern` and `csimp`, and `initialize` are honest code.
[Section 7.6 of the standard](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#76-classify-lean-computation-mechanisms-exactly)
tells how Regula treats each of them. Honest code can also use macros, elaborators, tactics and
evaluators in the usual way, and the guarantees include the declarations that such use makes.

Where the standard or a rule page states a check for a mechanism, that statement governs, and the
mechanism is in scope. The examples below are out of scope only where no such statement covers
them. Code that makes one of these changes to make a check pass is not honest code:

- A direct write to the state of an environment extension that no rule or section of the standard
  checks. Such a write goes around the command or attribute that Lean gives for that extension.
- A declaration of a dependency that a metaprogram adds with `debug.skipKernelTC`.
- A user compiler pass (`@[cpass]`), or a direct write that stores a compiled body that Lean's
  compiler did not make. An example is a forged `fdecl` body in the IR extension. Regula reports a
  write that leaves a retained compiled body missing, or that leaves an opaque export placeholder,
  as unresolved.
- An `f._unsafe_rec` companion that Regula does not inspect, for example one in a dependency.
- A native build setting: `extern_lib`, `moreLinkArgs` or `moreLeancArgs`.

Regula checks for some changes of this kind, where the standard or a rule page states the check.
For example, it replays the declarations of the project that are not `unsafe` or `partial` through
Lean's kernel. It calculates the axioms of each declaration of the project from that kernel, not
from the axiom table `exportedAxiomsExt` that Lean writes for each module. It also replays and
checks the modules of a path dependency in the project's Git work tree that the claimed modules
import, except Regula's own. But a pass makes no claim that the project has none of the changes in
the list.
The [README](README.md) puts Regula at the `#print axioms` step of
[Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

The later steps of that page, `lean4checker` and comparator, replay declarations through Lean's
kernel. Thus the two refuse a declaration that `debug.skipKernelTC` adds and that the kernel does
not accept. `lean4checker` does not calculate or compare axiom sets, thus it does not find a direct
write to the axiom table. Comparator calculates the axioms from the declarations that it exports,
not from that table. It refuses each axiom that is not one of its permitted axioms.

No step of that page checks the changes to compiled code. These are a compiler pass, a direct
write that stores a compiled body that Lean's compiler did not make and a native build setting. An
`_unsafe_rec` companion that Regula does not inspect is also such a change. The checks of Regula
that read compiled code trust that the project makes none of these changes. To check a proof from
a source that you do not trust, use [comparator](https://github.com/leanprover/comparator).

Regula owns the path dependencies in the Git work tree of the project only in a supported
workspace. In it, each owned package, the root package included, keeps Lake's default output
layout. Also, no two packages provide a module of the same name. For this condition, Regula counts
the library modules of each package and the executable roots of each owned package. Regula refuses
any other workspace before it builds the project or a copy of it.

Lake builds the program that runs the audit before that check, for example the `lake lint` driver.
The verification driver of this repository also builds its own copy first. These two builds are of
Regula's own package.

Regula reserves the module name prefixes `Regula` and `RegulaPolicy` to itself. In each audit, only
the running checker's own package can provide a module under them with any source. A different
package can provide one only with a source that is byte-identical to the checker's source of that
module. Thus the module that Regula loads in its place is compiled from the same text. This check
assumes that the package's Lean options for the module do not change what the text elaborates to.

A module under these prefixes in a package other than the root package is Regula's own code, also
in an owned path dependency. No audit owns it or inspects it as project code. Regula's own audit
checks it with its whole library.

## What counts as a vulnerability

A vulnerability is a way to break one of these guarantees on purpose:

- **A violating project that passes.** Honest code makes `lake lint` exit 0, or an audit report a
  `completed` account, while a claimed declaration breaks a guarantee that the
  [rule reference](https://rbeauchamp.github.io/regula/dev/rules/) states.
- **Regula acting outside what it documents.** Regula runs external programs with argument
  arrays, never through a generated shell program, and keeps scratch work under the checked
  project's `.lake/regula-scratch/`. An input, such as a path or a module or file name, that
  makes Regula's own code run a command, or write or delete a file, beyond what its
  documentation describes is a vulnerability.
- **A release or site published unchecked.** A flaw in the CI and release workflows
  (`.github/workflows/`, `lean/Regula/Release.lean`) that could publish a release, a tag or the
  rule-reference site from content that did not pass the checks the
  [release procedure](docs/guides/contributing.md#release) requires, or leave a release's tag
  naming a commit other than its checked release commit.

## What does not

- **Deliberate changes to Lean's environment, compiler or build.** A way to make a check pass with
  code that is not honest code, as the [scope](#scope) tells, is not a vulnerability. To ask that
  Regula find more such changes, open a [public issue](https://github.com/rbeauchamp/regula/issues).
- **Code the audit builds.** An audit runs the code of the project with your permissions. Lake runs
  a `lakefile.lean`, elaboration runs the macros, elaborators and tactics of the project, and the
  report worker of Regula runs the initializers of the modules of the project. Regula is not a
  sandbox: its trust boundary includes the pinned Lean process and the libraries that it imports.
  Thus code that attacks the checker process or your computer in this way is outside that
  boundary. Audit only code that you would build.
- **What Regula trusts.** Regula trusts Lean's kernel, elaborator, compiler and runtime, Lake, Git,
  the filesystem, the operating system and GNU timeout. It also trusts each package that the
  project requires from outside its Git work tree, for example Mathlib, and the account names each
  of them. Regula does not replay the declarations of these packages through Lean's kernel, and it
  reads their axioms from the data that their builds wrote. Report a vulnerability
  of one of these items to its maintainers. Regula also trusts the GitHub services that a release
  uses: Actions, commit-signature verification, tags and immutable releases.
- **Semantic review.** Whether a theorem states what you meant, and the other
  [review obligations](docs/guides/architecture.md#coverage-of-the-standard) every accepted account
  lists, are left to review; a pass never claims them.
- **Ordinary bugs.** A false positive, or a missed finding that nobody could use with honest code
  to make a violating project pass, belongs in a
  [public issue](https://github.com/rbeauchamp/regula/issues). If you are unsure, report
  privately; you will be asked to open a public issue if it is not a vulnerability.
