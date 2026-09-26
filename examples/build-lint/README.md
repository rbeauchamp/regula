# Build and lint enforcement example

This package is the reference `lakefile.lean` integration for `lake lint` and the enforcing
ordinary `lake build`. It demonstrates how an adopting project uses the existing linter; the implementation
lives in [`lean/Regula/Checker/`](../../lean/Regula/Checker/).

It requires the checker by local path. From this directory:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake build   # enforcing default target
lake lint    # the same audit through the configured lint driver
```

The package sets `lintDriver := "regula/lint"`. `lake lint` exits 0 (accepted),
1 (violation), 2 (invalid configuration) or 3 (incomplete); see the
[adoption guide](../../docs/guides/adoption.md#6-enforce-with-lake-lint-lake-build-and-ci).

To use it elsewhere, copy this directory and change `require regula from
"../.."` in `lakefile.lean` to the checker's path or an exact git revision. Lake resolves
the dependency manifest; no files named `Audit` or `Fixtures` are required. The checker
has transitive Mathlib dependencies, but this Core-only example does not compile Mathlib.
The environment setting skips Mathlib’s optional cache download during dependency resolution.

`policy` is the sole default target. It builds the checker via Lake's executable target,
then invokes the Lean build linter. The linter builds every manifested surface by its
explicit Lake target and inspects the completed environment. It does not recursively invoke
the default target, and it never caches a successful policy verdict. An unchanged second
`lake build` still runs policy inspection.

`foundation_manifest.json` selects Kernel-only with checked execution. Change `claim` to
`choice-free` or `standard-logical` to select those maximum profiles. The selection is
mandatory once enabled. For example, adding the following declaration to `Widget.lean`
is permitted under Standard-Logical and fails with `label-exceeds-claim` under Choice-Free:

```lean
theorem classicalTruth : True :=
  Classical.choice (show Nonempty True from ⟨True.intro⟩)
```

`Widget.successorContract` requires the exact relation `∀ n, f n = n + 1` about
`Widget.successor : Nat → Nat` and `Widget.next` consumes that evidence. The relation is
not carried by the return type, so an implementation of the same type that returns
anything else cannot satisfy the unchanged requirement, and missing/weaker evidence cannot
either. A passing build lists that registration with its implementation and requirement,
and marks R-INTENT and R-INVARIANT unresolved: Lean checked the stated relation, not that it
is the intended one or that every caller uses it. Replacing a registered executable with a
noncomputable definition fails; classical evidence about a computable definition remains
allowed under Standard-Logical.
`Widget.Additional` is intentionally absent from the umbrella imports, but is discovered
and inspected through the library's all-submodules glob.

To disable build policy, remove the `@[default_target]` annotation on `policy` and put it
on `lean_lib Widget`. Ordinary Lean proof obligations still apply, but that build no longer
enforces the manifest. Explicit `lake build Widget`, editor elaboration, and direct `lean`
also do not invoke `policy`. The supported adapter uses `lakefile.lean`; the manual gate
continues to support both Lake file formats. Do not use this target in `extraDepTargets`
or run it concurrently with another build of its claimed modules.

Native arithmetic remains trusted even with checked execution. This linter enforces declared
requirements, not their adequacy or completeness, fresh-source conformance, kernel normalization,
or native correctness. See [the exact scope and limits](https://rbeauchamp.github.io/regula/dev/standard/8-tooling-and-machine-audit/#812-opt-in-enforcing-build-linter).
Qualification copies these actual files and mutates disposable adopters through plain
`lake build`; it is included in `lake exe checkerSelftest --build-bound --jobs 4`. The `lint-driver`
partition (`./scripts/verify.sh diagnostics lint-driver`) qualifies `lake lint` the same way.

## Enforcement boundary

The [compliance checklist](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/) remains the rule
inventory. Its `BUILD-01`–`BUILD-04` rows describe this integration:

- **Build enforcement:** the enabled policy target rejects warnings and policy violations,
  checks declared foundation and execution profiles, and inspects manifested modules even
  when they are cached or absent from umbrella imports.
- **Required proof evidence:** registered executable contracts require kernel-checked
  evidence for the exact predicate applied to the named implementation. The project supplies
  that predicate and its proof; the linter does not infer the intended behavior.
- **Semantic review:** specification adequacy, completeness, and correspondence to prose
  remain review obligations under the checklist's `SCOPE-*`, `TYPE-*`, `THEOREM-*`, and
  documentation rows. A passing build alone does not establish full conformance.

See [module 8 §8.12](https://rbeauchamp.github.io/regula/dev/standard/8-tooling-and-machine-audit/#812-opt-in-enforcing-build-linter)
for the supported adapter and exact enforcement limits. Editor elaboration does not run
this build policy. For live editor diagnostics, see [lake-lint-toml](../lake-lint-toml/README.md).

## Direction

Lean provides native linter infrastructure, and Batteries and Mathlib extend it using
Lean metaprogramming. A separately distributed policy package can reuse that infrastructure;
[Lake supports lint drivers from dependencies](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/),
and [Batteries supports custom linters](https://leanprover-community.github.io/mathlib4_docs/Batteries/Tactic/Lint/Frontend.html).

Regula uses that infrastructure: a Lake lint driver, this build target, and native
command/module linters for editor feedback. Before adding rules, map the compliance checklist
to existing checks and reuse those that establish the required property.

The kernel checks supplied proofs; the linter enforces the presence and linkage of required
evidence and the declared policy. Writing a linter in Lean does not by itself prove the
linter correct. Ruff and Pyright are usability references, not reasons to build another
parser or duplicate Lean's analysis machinery.
