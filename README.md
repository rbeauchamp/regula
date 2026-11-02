# Regula

Regula is a checker of Lean builds. Its purpose is to be trusted, and to be the example of how Lean 4 code should be written: well factored, well designed, following best practice, and formally proven. Its owner decided that being free of bugs outranks every lint rule and feature, so Regula gives up any rule, feature or package it cannot prove rather than patching it, documenting a limit or keeping a stated gap. Only Lean, its kernel and Lake's own behaviour are meant to stay trusted; Regula's own code is meant to be proved, or so thin that it only calls Lean. The [run of the checker](specification/README.md#the-run-of-the-checker) states what is proved of its effects, and the [trusted base](specification/README.md#the-trusted-base) what stays assumed.

Regula is meant to be to Lean linters what [seL4](https://sel4.systems/Verification/proofs.html) is to kernels: the most trusted one, because its claim is exact and proved. That sentence states the aim and does not say it has been reached. Simplicity is how it becomes achievable, as in [LionsOS](https://trustworthy.systems/projects/LionsOS), where each component does only the minimum its use case needs. On 2026-11-01 the owner made this a constraint over all work on Regula, and it governs every later change:

- Removal comes first: before adding or repairing anything, ask whether it can be deleted, or its input narrowed, so the need goes away.
- Hard proofs are a warning: a proof far harder than the code it covers means the code should get simpler, not only better proved.
- Simplicity never replaces proof: RG1001 to RG1006, the two verdicts and the demand for no bugs all stand.
- One use case: one toolchain, one way to run it, a closed input, and a truthful refusal for anything else. Refusing something outside a narrow published contract is not a false refusal.
- A claim in the style of seL4: exactly what is proved, for which inputs, under which listed assumptions, with no superlatives in public until the proofs back them.
- The work follows it too: the simplest analysis that answers the question, with no frameworks.

So this rules out adding 1,000 lines to keep an unusual folder layout working, adding a mode to avoid a refusal, or keeping a tool in the repository for one analysis. It still allows a long proof of something truly hard, such as the two-way axiom rules.

Regula refuses a project whose declarations depend on `sorry`, a project axiom, `native_decide` or an axiom outside the profile the project states, or that holds an `unsafe` or `partial` declaration, or a constant with the name of a recursion helper, without the form that RG1006 exempts, or a `while` or `repeat` of its own. It also refuses a build it cannot load. Started from its own package, before anything is compiled, it can also read each Lean file of the claim and the Lake configuration, and refuse anything outside a closed set of allowed constructs, so that no code the project wrote runs during the build.

It gives one of two verdicts, and its output says which. The **proof verdict** means that the proofs of the claimed modules are sound and use only axioms the profile allows. The **full verdict** also means that no code written in the project ran while Lake built it. Only a project with no dependency in its Lake configuration and no Mathlib in its imports can have the full verdict.

## The checks

| Rule | What it refuses |
| --- | --- |
| RG1001 | A claimed module declares an `axiom`, even one that nothing uses. |
| RG1002 | A constant of a claimed module depends on `sorryAx`, directly or through an import. |
| RG1003 | A constant of a claimed module depends on an axiom other than Lean's `propext`, `Quot.sound` and `Classical.choice`, and RG1002 and RG1004 do not name it. |
| RG1004 | A constant of a claimed module depends on an axiom with the name form that `native_decide` gives. |
| RG1005 | A constant of a claimed module depends on an axiom that the project's profile does not admit. |
| RG1006 | A claimed module holds a constant that is `unsafe`, `partial` or named as a recursion helper, without the exempted form of one, or a constant whose value mentions `Lean.Loop.mk` or `repeatM`, which `while` and `repeat` compile to. |
| RG1010 | A Lean file of the claim, the Lake configuration or `lean-toolchain` holds something outside the closed set. Only the full gate reads this. |
| RG2001 | The checker cannot load the build, the full gate stops on a case of [its closed list](specification/README.md#the-closed-list-of-refusals) with exit 2, its input does not have the closed form, or a claimed module holds a constant that Lean's import replaced and that is no theorem within the profile or has a recursion helper's name. The verdict is `incomplete`. |

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

On Linux with `bwrap` installed, `lake check` runs in its sandbox without the flag. For this module as `Demo.lean`, `lake build --wfail` fails at `double`, and a plain `lake build` only warns there. After that plain build, `lake check` refuses `sorryAx`, and `lake lint` also refuses `twice`, whose proof depends on `double`:

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
  4 findings
regula: proof verdict: fail
```

The exit code of `lake lint` is 0 for `pass`, 1 for `fail` and 2 for `incomplete`. The last line is the verdict. Regula starts each diagnostic line with two spaces and displays embedded newline and carriage-return characters as `\n` and `\r`, so diagnostic text cannot insert a verdict line. The full gate also displays Lake's own build output.

## The full gate

Start the checker from its own package: that is a precondition of the full verdict, beside the `PATH` you run it with. The checker does not test who started it, and a start from a project's Lake is outside the contract, because Lake runs a project's `lakefile.lean` when it loads it, and code that runs first can change what any later step sees. So build Regula in a checkout of its own, and from that checkout's directory name the project in the variable `REGULA_FULL`:

```sh
git clone https://github.com/rbeauchamp/regula
cd regula
lake build lint
REGULA_FULL=/path/to/project lake exe lint standard-logical
```

Regula publishes [a closed list of refusals](specification/README.md#the-closed-list-of-refusals), and each refusal is proved true of what Lean, Lake or the operating system answered in that run. A project with no refusal, on which the rules hold, passes. So "no false refusal" means that a refusal is never untrue, and it does not mean that every reasonable project passes.

The checker reads `lean-toolchain`, `lakefile.lean` by name and `lakefile.toml` before any Lake call on the project. Then it runs the check and, for an admitted project, the build, its replay and the rules, in that order, in one process. Every Lake call and child process works in a directory the checker made for this run. That directory holds only what the checker read and judged, with the pinned `lean-toolchain`, and the checker asks to remove it afterwards. So nothing in the project's directory is written, and its `.lake`, its manifest and its other files are not used.

The project needs a `module` header on each file, a `lean-toolchain` that says `leanprover/lean4:v4.35.0`, and `lakefile.toml` with no `require` in it. The checker fetches and runs nothing of a dependency. The project's default targets are libraries, so a default executable is refused, the `lake new` application template among them, and it still gets the proof verdict. No target has its own `srcDir`, and the package's source directory has names of ASCII letters, digits, `_` and `'` only. The project's libraries name their modules with `roots` or with `globs` of single modules, since `Data.+` and `Data.*` need a directory listing, which the checker refuses. The real path of each file the checker reads must be exactly its own path below the project's real path, so no source is reached through a symbolic link. A file that the build needs and that the check does not read, such as a data file, is absent, so the build fails and the verdict is `fail`. A project with no dependency needs no `require` of Regula for this.

For this module as `Demo.lean`, the checker prints `regula: full verdict: pass, under the hypotheses H1 to H5 and the trusted base of its specification, at Lean 4.35.0, on /path/to/project`:

```lean
module

public section

/-- Addition commutes. -/
theorem swap (a b : Nat) : a + b = b + a := by omega
```

The exit code is 0 only for a pass of the full verdict, whose last line ends with the directory it audited. It is 1 when the check refuses the project, which compiles nothing, or when the verdict is `fail`. It is 2 when the check gives `incomplete` (RG2001), as on a module's file that it cannot read, which also compiles nothing, or when the verdict is `incomplete`. It is 3 when only a proof verdict is possible, for a project with a `require` in `lakefile.toml` or with Mathlib in its imports. Then nothing is built, and the last line says so and names the three commands that give that verdict, which you run in the project: they run the project's code and its dependencies'.

The check refuses `run_cmd`, `#eval`, `#guard`, `run_tac`, `by_elab`, `native_decide`, `decide +native`, `macro`, `syntax`, `notation`, `elab`, `initialize`, `@[local macro k]`, `lakefile.lean` and a plugin in `lakefile.toml`. It admits Regula's own core, and library code that uses `simp`, `omega`, `decide +kernel`, `variable` and `deriving DecidableEq`. Those are examples. The rule is a closed table, so anything it does not hold is refused, including whatever a later Lean adds and a construct that is harmless. The [specification](specification/README.md#the-language-check) gives the table's criterion.

`lake lint` in a project gives a proof verdict about that project, and a pass ends with that project's directory. No argument names a project, so a project's `lintDriverArgs` cannot choose what is audited: anything other than one profile is refused, with exit 2. `lakefile.toml` has no key that sets a variable, so a value of `REGULA_FULL` is the request of the person who started the run. With it set, `lake lint` is the full gate on the directory it names, and in a project with a `require` that gives the line that says only a proof verdict is possible. A value left set in your shell gives a full verdict on that directory instead of the project you are in, so read the directory at the end of the last line. A program that the project planted can print any line, so a full verdict is only as good as the start from the checker's own package: read it only from a checker you built apart from the project.

## What a pass means

A pass of the proof verdict, from the three commands on one build, means that the proofs of the claimed modules are sound and use only axioms that the profile allows. It says nothing about what a compiled program runs: `@[implemented_by]`, `@[extern]` and `@[csimp]` on a safe definition all pass, and so does a constant of the form that RG1006 exempts, which names no origin, when a module's own code adds it during the build, such as with `run_cmd`, as the [entry of RG1006](specification/README.md#rg1006-unsafe-and-partial-declarations) describes. A pass of `lake lint` alone means less, because only `lake check` replays the proofs in Lean's kernel.

A pass of the full verdict means that as well, and that while Lake built the files the check read, no code written in the project ran, and no file installed anything that replaces what the compiler runs for a definition. That rests on five hypotheses, which the [specification](specification/README.md#h1-and-h2) states and which are read again at each upgrade of Lean: H1 and H2 about Lean 4.35.0, that the tree the check read is the tree Lean elaborates, and that what the closed set admits runs no such code; H3 about Lake, that what its build compiles is what the check read; H4 about the operating system's `realpath`, that a path that crosses a link gets another real path; and H5 about Lake, that it takes `lakefile.toml` as its configuration when nothing answers to `lakefile.lean`. It also rests on the rest of the specification's [trusted base](specification/README.md#the-trusted-base). No proof here can examine Lean's own program, so a route that H2 misses would be a false pass. The full verdict says nothing about what a theorem's statement means to a reader or what another process does, and a project with a dependency does not get it.

The commands `lake build --wfail` and `lake check` are Lean's own, and Regula makes no claim of its own about what they decide.

## Work on Regula

The [specification](specification/README.md) states each rule and its proofs, and lists what stays trusted. The gate of a change runs the steps of `localSteps` in [`lean/Regula/DiagnosticsGate.lean`](lean/Regula/DiagnosticsGate.lean), and needs the pinned toolchain and a read of lean-intent from GitHub:

```sh
lean --run lean/Regula/DiagnosticsGate.lean local
```

[`AGENTS.md`](AGENTS.md) gives the repository's rules for changes.

## License

[MIT](LICENSE).
