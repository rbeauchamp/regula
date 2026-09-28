# Build and lint enforcement example

This package is the reference `lakefile.lean` integration for `lake lint` and the enforcing
ordinary `lake build`. It demonstrates how an adopting project uses the existing linter; the implementation
lives in [`lean/Regula/Checker/`](../../lean/Regula/Checker/).

It requires the checker by local path. From this directory:

```sh
lake update
lake build   # enforcing default target
lake lint    # the same audit through the configured lint driver
```

Its `leanOptions` enable Lean's `linter.missingDocs` and turn off automatic implicits
(standard §6.7 and §7.1), so the enforcing build rejects an undocumented public definition.
A library that imports Mathlib also enables Mathlib's standard linter set as the
[adoption guide](../../docs/guides/adoption.md#community-conventions-and-linters) shows.

The package sets `lintDriver := "regula/lint"`. `lake lint` exits 0 (accepted),
1 (violation), 2 (invalid configuration) or 3 (incomplete); see the
[adoption guide](../../docs/guides/adoption.md#6-enforce-with-lake-lint-lake-build-and-ci).

To use it elsewhere, copy this directory and change `require regula from
"../.."` in `lakefile.lean` to the checker's path or an exact git revision. Lake resolves
the dependency manifest; no files named `Audit` or `Fixtures` are required. The checker
requires no other package, so the lock manifest records only `regula`.

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
/-- `True`, proved through `Classical.choice`, so its axioms include `Classical.choice`. -/
theorem classical_true : True :=
  Classical.choice (show Nonempty True from ⟨True.intro⟩)
```

`Widget.successor_contract` requires the exact relation `∀ n, f n = n + 1` about
`Widget.successor : Nat → Nat` and `Widget.next` consumes that evidence. The relation is
not carried by the return type, so an implementation of the same type that returns
anything else cannot satisfy the unchanged requirement, and missing/weaker evidence cannot
either. A passing build lists that registration with its implementation and requirement,
and marks R-INTENT and R-INVARIANT unresolved: Lean checked the stated relation, not that it
is the intended one or that every caller uses it.
`Widget.Additional` is intentionally absent from the umbrella imports, but is discovered
and inspected through the library's all-submodules glob.

To disable build policy, remove the `@[default_target]` annotation on `policy` and put it
on `lean_lib Widget`. That build then no longer enforces the manifest. Explicit
`lake build Widget`, editor elaboration and direct `lean` never invoke `policy`; for live
editor diagnostics, see [lake-lint-toml](../lake-lint-toml/README.md). Do not use this target
in `extraDepTargets` or run it concurrently with another build of its claimed modules.

Native arithmetic remains trusted even with checked execution, and a passing build does not
establish the adequacy or completeness of the declared requirements. See
[standard §7.11](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#711-opt-in-enforcing-build-linter)
for the exact scope and limits. The `build-policy` and `lint-driver` diagnostics copy these
files into disposable adopters and mutate them.
