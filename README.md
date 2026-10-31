# Regula

Regula exists to be trusted, and to be the example of how Lean 4 code should be written: well factored, well designed, following best practice, and formally proven. Its owner decided that being free of bugs outranks every lint rule and feature, so Regula gives up any rule, feature or package it cannot prove rather than patching it, documenting a limit or keeping a stated gap. Only Lean, its kernel and Lake's own behaviour are meant to stay trusted; Regula's own code is meant to be proved, or so thin that it only calls Lean. That is the aim and not a claim about this revision: the [trusted base](specification/README.md#the-trusted-base) lists what is not yet proved.

Regula is a checker of a finished Lean build. It refuses a project whose declarations depend on `sorry`, a project axiom, `native_decide` or an axiom outside the profile the project states, or that holds an `unsafe` or `partial` declaration without the form of Lean's recursion helper, or a `while` or `repeat` of its own. It also refuses a build it cannot load.

## The checks

| Rule | What it refuses |
| --- | --- |
| RG1001 | A claimed module declares an `axiom`, even one that nothing uses. |
| RG1002 | A constant of a claimed module depends on `sorryAx`, directly or through an import. |
| RG1003 | A constant of a claimed module depends on an axiom other than Lean's `propext`, `Quot.sound` and `Classical.choice`, and RG1002 and RG1004 do not name it. |
| RG1004 | A constant of a claimed module depends on an axiom with the name form that `native_decide` gives. |
| RG1005 | A constant of a claimed module depends on an axiom that the project's profile does not admit. |
| RG1006 | A claimed module holds an `unsafe` or `partial` constant without the form of Lean's recursion helper, or a constant whose value mentions `Lean.Loop.mk` or `repeatM`, which `while` and `repeat` compile to. |
| RG2001 | The checker cannot load the build, or its input does not have the closed form. The verdict is `incomplete`. |

The claimed modules are the modules of the root package's default targets, with each module of the root package that their imports reach. These are the modules that `lake build` and `lake check` work on. A target that is not a default target, and that no default target imports, is outside the claim.

The profiles are `kernel-only` (no axiom), `choice-free` (`propext` and `Quot.sound`) and `standard-logical` (those two and `Classical.choice`). A project states one, in `lintDriverArgs`.

## Use it

Regula reads one Lean release, `leanprover/lean4:v4.35.0`, and no release of Regula has this form yet, so a project requires a commit of `main`. Add this to `lakefile.toml`, and put that toolchain in `lean-toolchain`:

```toml
name = "demo"
defaultTargets = ["Demo"]
lintDriver = "regula/lint"
lintDriverArgs = ["standard-logical"]

[[require]]
name = "regula"
git = "https://github.com/rbeauchamp/regula"
rev = "main"

[[lean_lib]]
name = "Demo"
```

Then run the three commands in order, on one build:

```sh
lake build --wfail
lake check --inadvisably-no-sandbox
lake lint
```

On Linux with `bwrap` installed, `lake check` runs in its sandbox without the flag. For this module as `Demo.lean`, `lake build` warns at `double`, and `lake lint` also refuses `twice`, whose proof depends on `double`:

```lean
theorem double (n : Nat) : n + n = 2 * n := by sorry

theorem twice (n : Nat) : 2 * n = n + n := (double n).symm
```

```text
regula: read 1 claimed modules and 2 of their constants
RG1002 twice (module Demo): depends on sorryAx
RG1002 double (module Demo): depends on sorryAx
RG1005 twice (module Demo): depends on [sorryAx], outside the profile
RG1005 double (module Demo): depends on [sorryAx], outside the profile
regula: fail, 4 findings
```

The exit code of `lake lint` is 0 for `pass`, 1 for `fail` and 2 for `incomplete`.

## What a pass means

A pass of the three commands on one build means that the proofs of the claimed modules are sound and use only axioms that the profile allows. It says nothing about what a compiled program runs: `@[implemented_by]`, `@[extern]` and `@[csimp]` on a safe definition all pass, and so does a forged recursion helper, which the [entry of RG1006](specification/README.md#rg1006-unsafe-and-partial-declarations) describes. A pass of `lake lint` alone means less, because only `lake check` replays the proofs in Lean's kernel.

The commands `lake build --wfail` and `lake check` are Lean's own, and Regula makes no claim of its own about what they decide.

## Work on Regula

The [specification](specification/README.md) states each rule and its proofs, and lists what stays trusted. The gate of a change runs the steps of `localSteps` in [`lean/Regula/DiagnosticsGate.lean`](lean/Regula/DiagnosticsGate.lean), and needs the pinned toolchain and a read of lean-intent from GitHub:

```sh
lean --run lean/Regula/DiagnosticsGate.lean local
```

[`AGENTS.md`](AGENTS.md) gives the repository's rules for changes.

## License

[MIT](LICENSE).
