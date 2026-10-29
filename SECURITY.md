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
For example, it calculates the axioms of each claimed declaration from the declarations that Lean
loads from the build. It does not read the axiom table `exportedAxiomsExt` that Lean writes for
each module. But a pass makes no claim that the project has none of the changes in the list.

Regula does the `#print axioms` step of
[Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/) for each
declaration that a project claims. It does not replay the modules through Lean's kernel. For that
step, run the toolchain's own `leanchecker` by its path in the toolchain's installation directory.
`lake env leanchecker` can run a package's own program of that name instead, because `lake env`
puts the binary directory of each package first on `PATH`.
[Comparator](https://github.com/leanprover/comparator) judges a proof of a fixed statement from a
source that you do not trust.

The later steps of that page, the toolchain's `leanchecker` and comparator, replay declarations
through Lean's kernel. Thus the two refuse a declaration that `debug.skipKernelTC` adds and that
the kernel does not accept. `leanchecker` does not calculate or compare axiom sets, thus it does
not find a direct write to the axiom table. Comparator calculates the axioms from the declarations
that it exports, not from that table. It refuses each axiom that is not one of its permitted axioms.

No step of that page checks the changes to compiled code. These are a compiler pass, a direct
write that stores a compiled body that Lean's compiler did not make and a native build setting. An
`_unsafe_rec` companion that Regula does not inspect is also such a change. The checks of Regula
that read compiled code trust that the project makes none of these changes.

Regula checks the modules of the root package only, and it reads each one from the root
package's build. When Lean's search path finds the `.olean` of a module of a target outside that
build, the run is `incomplete`. A dependency with a module of the same name can cause this. The modules of a dependency are not checked. The modules of Regula in a project's
dependencies are Regula's code, and Regula's own gate checks them.

Lake builds the program that runs the check, the `lake lint` driver, before the check. The
verification driver of this repository also builds its own copy first. These two builds are of
Regula's own package.

## What counts as a vulnerability

A vulnerability is a way to break one of these guarantees on purpose:

- **A violating project that passes.** Honest code makes `lake lint` exit 0 while a claimed
  declaration breaks a guarantee that the
  [rule reference](https://rbeauchamp.github.io/regula/dev/rules/) states.
- **Regula acting outside what it documents.** The checker that `lake lint` runs writes no file.
  It starts a second process of itself, in an environment that isolates Git, where Lake's load of
  the workspace can run Git. Regula's other programs run external programs with argument arrays,
  never through a generated shell program, and keep scratch work under the project's
  `.lake/regula-scratch/`. An input, such as a path or a module or file name, that makes Regula's
  own code run a command, or write or delete a file, beyond what its
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
- **Code the build runs.** The build that comes before a check runs the code of the project with
  your permissions. Lake runs a `lakefile.lean`, and elaboration runs the macros, elaborators and
  tactics of the project. Regula is not a sandbox: its trust boundary includes the pinned Lean
  process and the libraries that it imports. Thus code that attacks the checker process or your
  computer in this way is outside that boundary. Check only code that you would build.
- **What Regula trusts.** Regula trusts Lean's kernel, elaborator, compiler and runtime, Lake, Git,
  the filesystem, the operating system and GNU timeout. It also trusts each package that the
  project requires, for example Mathlib. Regula does not replay declarations through Lean's
  kernel, and it reads the declarations of the project and of these packages from their builds. Report a vulnerability of one of these items to its maintainers. Regula also
  trusts the GitHub services that a release uses: Actions, commit-signature verification, tags and
  immutable releases.
- **Semantic review.** Whether a theorem states what you meant, and the other
  [review obligations](docs/guides/architecture.md#coverage-of-the-standard) that the rule
  reference lists, are left to review; a pass never claims them.
- **Ordinary bugs.** A false positive, or a missed finding that nobody could use with honest code
  to make a violating project pass, belongs in a
  [public issue](https://github.com/rbeauchamp/regula/issues). If you are unsure, report
  privately; you will be asked to open a public issue if it is not a vulnerability.
