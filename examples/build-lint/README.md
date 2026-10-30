# Build and lint example

This package is the reference `lakefile.lean` integration of Regula. It shows how an adopting project builds its claimed surface and runs the checker. The implementation of the checker is in [`lean/Regula/`](../../lean/Regula/).

The package requires the checker by its local path. From this directory:

```sh
lake update
lake build --wfail   # the claimed surface, with warnings as errors
lake lint            # Regula's checker over the finished build
```

Its `leanOptions` enable the `linter.missingDocs` of Lean and turn off automatic implicits (standard §6.7 and §7.1). Thus the build refuses an undocumented public definition. A library that imports Mathlib also enables the standard linter set of Mathlib, as the [adoption guide](../../docs/guides/adoption.md#community-conventions-and-linters) shows.

The package sets `lintDriver := "regula/lint"`. `lake lint` exits 0 (pass), 1 (fail) or 2 (incomplete). The [adoption guide](../../docs/guides/adoption.md#4-run-lake-lint) gives the details.

To use it in a different place, copy this directory. Then change `require regula from "../.."` in `lakefile.lean` to the path of the checker or to a release tag ([adoption guide](../../docs/guides/adoption.md#1-require-regula)). The checker requires no other package, thus the lock manifest records only `regula`.

`foundation_manifest.json` selects Kernel-only with checked execution. Change `claim` to `choice-free` or `standard-logical` to select those maximum profiles. For example, the checker accepts this declaration in `Widget.lean` under Standard-Logical. Under Choice-Free, it reports the declaration as [RG1005]:

```lean
/-- `True`, proved through `Classical.choice`, so its axioms include `Classical.choice`. -/
theorem classical_true : True :=
  Classical.choice (show Nonempty True from ⟨True.intro⟩)
```

`Widget.successor_contract` requires the exact relation `∀ n, f n = n + 1` about `Widget.successor : Nat → Nat`, and `Widget.next` consumes that evidence. The return type does not carry the relation. Thus an implementation of the same type that returns a different value cannot satisfy the unchanged requirement. Lean checked the stated relation, but not that it is the intended relation or that each caller uses it. `Widget.Additional` is not in the imports of the root module, but the glob `.andSubmodules` of the library includes it.

Native arithmetic stays trusted, also with checked execution. A pass does not establish the adequacy or the completeness of the declared requirements.

[RG1005]: https://rbeauchamp.github.io/regula/dev/rules/RG1005/
