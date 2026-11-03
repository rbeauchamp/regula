# Regula

You use coding agents to write Lean 4, both as a functional programming language and as a theorem prover, because you want verified software rather than plausible code. A green `lake build` does not guarantee that: an agent can finish with a `sorry` that only warned, a declared `axiom`, `native_decide`, an `unsafe` or `partial` definition, a `while` loop, or build-time code that ran on your machine, and you cannot read every proof by hand.

Regula is a strict Lean 4 linter built to hold coding agents to verified engineering standards across both functional programming and theorem proving:

- **Actionable agent diagnostics:** `lake lint` reads the finished build, reports exact findings such as `RG1002 double (module Demo): depends on sorryAx` (rule, constant and module), and ends with a verdict line (`regula: proof verdict: fail`) and exit code (0 for `pass` and for nothing else).
- **Proved rules, not heuristics:** Each rule, RG1001 to RG1006 and RG1011, is proved in Lean 4 to refuse every violation and only violations over its input (`rg1001_exact` to `rg1006_exact`, `rg1011_exact`).
- **Proved foundation today, broader standard ahead:** `v0.13.0` ships the 8-rule soundness, totality and build-isolation core, and `main` adds RG1011, which no release has yet; planned engineering standards, fix guidance and design, refactoring and architecture rules ship only once formally specified and proved ([Purpose and constraint](#purpose-and-constraint), [Work on Regula](#work-on-regula)).

Regula gives one of two verdicts, and its output names which one ran ([full scope and assumptions](#what-a-pass-means)):

- **Proof verdict** (`lake build --wfail` and `lake lint` on one build, with no option of Lake's): works with dependencies and Mathlib, replays only the [claimed modules'](#the-checks) dependency cone in Lean's kernel, and means the claimed proofs are sound and use only allowed axioms, for a project that places no file or code aimed at the checker or the toolchain.
- **Full verdict** (`REGULA_FULL=DIR lake exe lint PROFILE` from a Regula checkout built apart from the project, with no option of Lake's): for standalone library projects with no `require` dependency in Lake's configuration and no Mathlib in its imports; also checks source files before compiling (RG1010) so no project-written code runs during the build and no file installs a compiler replacement, under hypotheses H1 to H5 and the [trusted base](specification/README.md#the-trusted-base), even if the project is aimed at the checker.

A pass does not mean your code is correct: no checker can say a theorem states what you meant, so theorem statements stay yours to read, and beyond RG1011's refusal of `@[implemented_by]` and `@[extern]` on a claimed constant the proof verdict says nothing about what a compiled program runs.

## Use it

Put `leanprover/lean4:v4.35.0` in `lean-toolchain`, and add this to `lakefile.toml`:

```toml
name = "demo"
defaultTargets = ["Demo"]
lintDriver = "regula/lint"
lintDriverArgs = ["standard-logical"]

[[require]]
name = "regula"
git = "https://github.com/rbeauchamp/regula"
rev = "v0.13.0"

[[lean_lib]]
name = "Demo"
```

Run `lake update regula` so the manifest selects `v0.13.0`. Then run the two commands in order on one build, from the project's own directory with no option of Lake's and `REGULA_FULL` unset:

```sh
lake build --wfail
lake lint
```

For this `Demo.lean`, `lake build --wfail` fails at `double`, while a plain `lake build` only warns there. After that plain build, `lake lint` refuses `double` and `twice` (whose proof depends on `double`):

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

- **Exit codes:** 0 for `pass`, 1 for `fail`, 2 for `incomplete`.
- **Output format:** Diagnostic lines start with two spaces and escape newlines and carriage returns as `\n` and `\r`, so diagnostic text cannot forge the final verdict line. A `pass` ends its last line with the audited directory (the full gate also prints Lake's build output beforehand).

## The checks

Nine checks cover proof foundations, program totality, compiled code, pre-build source admission, and kernel cone replay. RG1011 is on `main` and in no release yet; `v0.13.0` has the other eight:

| Rule | Area | What it refuses |
| --- | --- | --- |
| RG1001 | Proofs & axioms | A claimed module declares an `axiom`, even one that nothing uses. |
| RG1002 | Proofs & axioms | A constant of a claimed module depends on `sorryAx`, directly or through an import. |
| RG1003 | Proofs & axioms | A constant of a claimed module depends on an axiom other than Lean's `propext`, `Quot.sound` and `Classical.choice`, and RG1002 and RG1004 do not name it. |
| RG1004 | Proofs & axioms | A constant of a claimed module depends on an axiom with the name form that `native_decide` gives. |
| RG1005 | Proofs & axioms | A constant of a claimed module depends on an axiom that the project's profile does not admit. |
| RG1006 | Totality & safety | A claimed module holds a constant that is `unsafe`, `partial` or named as a recursion helper, without the exempted form of one, or a constant whose value mentions `Lean.Loop.mk` or `repeatM`, which `while` and `repeat` compile to. |
| RG1011 | Compiled code | A constant of a claimed module has `@[implemented_by]` or `@[extern]`, so a compiled program runs other code in its place than the definition its proofs are about. `@[csimp]` is not refused, because its theorem states that the replacement equals the original, and the kernel checks that theorem when the claim's cone holds it. |
| RG1010 | Language subset | A Lean file of the claim, the Lake configuration or `lean-toolchain` holds something outside the closed set. Only the full gate reads this. |
| RG2001 | Environment & replay | The checker cannot load the build, the full gate stops on a case of [its closed list](specification/README.md#the-closed-list-of-refusals) with exit 2, its input does not have the closed form, or a claimed module holds a constant the merged environment does not show to the rules and that is no theorem within the profile, has a recursion helper's name, or has unread or forbidden replacement attributes in its own module, or Lean's kernel does not accept the replay of the claim's cone. The verdict is `incomplete`. |

- **Claimed modules:** the modules of the root package's default targets plus each root-package module their imports reach (what `lake build` builds; targets that no default target reaches are outside the claim).
- **Profiles (`lintDriverArgs`):** `kernel-only` (no axiom), `choice-free` (`propext` and `Quot.sound`), and `standard-logical` (`propext`, `Quot.sound` and `Classical.choice`).

## Why not just `lake check`

The proof verdict does not need `lake check`. `lake check` replays the entire imported environment in Lean's kernel (refusing constants that mention `sorryAx` or axioms outside `propext`, `Quot.sound` and `Classical.choice`), which did not finish on a 24 GiB Mac for a Mathlib project ([issue 541](https://github.com/rbeauchamp/regula/issues/541)), and it skips unreferenced constants with Lean-internal names such as a theorem of `False` added via `debug.skipKernelTC` (measured). `lake lint` replays only the claim's cone, and `lake build --wfail` fails on `sorry`'s warning.

On a one-module project at Lean 4.35.0, `lake build --wfail` and `lake check` both exited 0 on every row below, an observation of Lean's commands at that release and no claim of Regula's:

| In the project | What refuses it |
| --- | --- |
| An axiom that nothing uses | `lake lint`, RG1001 |
| A `partial def` or an `unsafe def` | `lake lint`, RG1006 |
| A `while` loop | `lake lint`, RG1006 |
| A proof that uses `Classical.choice`, under the profile `choice-free` | `lake lint`, RG1005 |
| `run_cmd`, whose code ran during the build | The full gate, RG1010, before it compiles anything |

Where `lake check` also refuses (as on `sorry` or an axiom in use), `lake lint` reports a rule code. RG1001 to RG1006 and RG1011 read only the loaded build's constants, with the two attributes by which Lean replaces a constant's compiled code, its claimed modules and profile, so they decide nothing about source text, the compiled code itself or build logs.

## Before you adopt it

- **Toolchain & release:** Regula `v0.13.0` reads only `leanprover/lean4:v4.35.0`; require it by tag `v0.13.0` (in `v0.12.0`, the proof verdict also needed `lake check` and the checker did not replay the claim's cone).
- **Named configurations:** The claim holds only for `leanprover/lean4:v4.35.0`, one published run per verdict with no option of Lake's (`lake lint` in the project's own directory with `REGULA_FULL` unset, or `REGULA_FULL=DIR lake exe lint PROFILE` from a Regula checkout built apart from the project), on macOS 27.2 (Apple silicon) or Ubuntu 24.04.5 LTS (x86-64). Anything else (Windows, other Linux or macOS versions, `lake -d`, `lake -f`, starting the full gate from a project's Lake, or `lake lint` with `REGULA_FULL` set) is outside the contract ([the trusted base](specification/README.md#the-named-configurations)) and not a defect.
- **No `lake -d` or `lake -f`:** Lake gives a program nothing a project cannot set to identify the selected workspace, so `lake lint` still audits the current directory and can exit 0 naming it rather than the option's target. No argument names a project, and anything in `lintDriverArgs` other than one profile exits 2, so a project cannot choose what is audited.
- **Dependencies:** Projects with a `require` dependency or Mathlib imports can have only the proof verdict, whose two commands run project and dependency code.
- **Memory:** Cone replay holds every constant the claim depends on in memory ([measured](specification/README.md#what-a-pass-means) at 4.3 GiB and two minutes importing Mathlib); much larger cones may exceed machine memory, a limit of the named configuration rather than a defect.
- **Full gate table:** Refuses anything outside a closed table (`macro`, `syntax`, `notation`, `lakefile.lean`, default executables, and unlisted harmless constructs included); see [The full gate](#the-full-gate).

## What a pass means

### Proof verdict

- **Guarantee:** Passing `lake build --wfail` and `lake lint` on one build means the proofs of the claimed modules are sound and use only axioms the profile allows, for a project that places no file or code aimed at the checker or the toolchain.
- **Kernel cone replay:** `lake lint` gives Lean's `Kernel.Environment.replay` each constant of the claimed modules and every constant reached through what each mentions in Lean's data (type, value, inductive block, and `Eq` for a quotient), with the constants the kernel itself builds into a term, and nothing else, into an empty environment. When two modules declare a theorem of one name and type, Lean's import keeps one, and the replay also gets each claimed module's differing copy under a name no constant of the build has, checking every module's proof. An unsound proof in a reached dependency fails it too.
- **Outside its scope:** Because both commands run in the project's Lake, a project aimed at the checker can forge a pass via a library loaded from the project's library directory into the checker, a doctored Regula from its configuration or package directory, a `lakefile.lean`, or build-time code ([the specification](specification/README.md#a-project-aimed-at-the-checker)). On `main`, RG1011 refuses each constant of a claimed module that has `@[implemented_by]` or `@[extern]`. Beyond that it says nothing about compiled execution: `@[csimp]` passes, whose theorem the kernel checks only when the claim's cone holds it, and so does a claimed constant that calls a dependency's or the toolchain's constant with either attribute, or an RG1006-exempted constant, which names no origin, when a module's own code adds it during the build such as via `run_cmd` ([RG1011](specification/README.md#rg1011-replaced-compiled-code), [RG1006](specification/README.md#rg1006-unsafe-and-partial-declarations)). `lake lint` without `lake build --wfail` reads whatever build is on disk.
- **Trusted commands:** `lake build --wfail` and `Kernel.Environment.replay` are Lake's and Lean's own; Regula makes no claim of its own about what they decide, and proves which constants it gives the replay.

### Full verdict

- **Guarantee:** Passing the full gate establishes everything above (closing the four checker-attack routes), plus that while Lake built the files read, no project-written code ran and no file installed anything that replaces what the compiler runs for a definition.
- **Hypotheses ([H1 to H5](specification/README.md#h1-and-h2), re-read at each Lean upgrade):** H1 and H2 about Lean 4.35.0 (the tree read is the tree Lean elaborates, and what the closed set admits runs no such code; no proof here can examine Lean's own program, so a route H2 misses would be a false pass), H3 about Lake (its build compiles what the check read), H4 about OS `realpath` (a path crossing a link gets another real path), and H5 about Lake (it takes `lakefile.toml` when nothing answers to `lakefile.lean`), plus the specification's [list of assumptions](specification/README.md#the-trusted-base) about Lean, Lake and the OS.
- **Outside its scope:** What a theorem's statement means to a reader, what another process does, and any project with a dependency or Mathlib.

## The full gate

Build and start the checker from its own checkout apart from the project (a precondition alongside `PATH`, since Lake runs a project's `lakefile.lean` on load and the checker does not test who started it):

```sh
git clone --branch v0.13.0 https://github.com/rbeauchamp/regula
cd regula
lake build lint
REGULA_FULL=/path/to/project lake exe lint standard-logical
```

Before any Lake call on the project, the checker reads `lean-toolchain`, `lakefile.lean` by name and `lakefile.toml`. In one process, it runs the check and, if admitted, builds, replays the claim's cone and runs the rules inside a fresh temporary directory holding only the judged files and pinned `lean-toolchain` (asking to remove it afterward); nothing in the project directory is written, and its `.lake`, manifest and other files are unused.

Project requirements (no `require` of Regula needed; nothing of a dependency is fetched or run):

- **Configuration:** `lean-toolchain` says `leanprover/lean4:v4.35.0`, `lakefile.toml` has no `require` and uses only keys in the closed set, and no `lakefile.lean` exists.
- **Closed language ([specification](specification/README.md#the-language-check)):** Each file starts with `module`. Admitted examples: Regula's own core, and library code using `simp`, `omega`, `decide +kernel`, `variable` and `deriving DecidableEq`. Refused examples: `run_cmd`, `#eval`, `#guard`, `run_tac`, `by_elab`, `native_decide`, `decide +native`, `macro`, `syntax`, `notation`, `elab`, `initialize`, `@[local macro k]` and a plugin in `lakefile.toml`, plus anything outside the closed table (even if harmless, or added in a later Lean).
- **Targets & paths:** Default targets are libraries (default executables, including `lake new`'s template, are refused here and still get the proof verdict); no target has its own `srcDir`; the package's source directory lies at or below the project, with component names of ASCII letters, digits, `_` and `'` only; libraries name modules via `roots` or single-module `globs` (not `Data.+` or `Data.*`, which need a directory listing); each read file's real path is its exact path below the project's real path, so no read file is reached through a symbolic link; and any unread file the build needs (such as a data file) is absent, so the build fails and the verdict is `fail`.

For this `Demo.lean`, the checker prints `regula: full verdict: pass, under the hypotheses H1 to H5 and the trusted base of its specification, at Lean 4.35.0, on /path/to/project`:

```lean
module

public section

/-- Addition commutes. -/
theorem swap (a b : Nat) : a + b = b + a := by omega
```

- **Exit codes:** 0 only for a full-verdict `pass` (last line ends with the audited directory); 1 when the language check refuses (compiles nothing) or the verdict is `fail`; 2 when the language check gives `incomplete` (RG2001, such as an unreadable module file, compiling nothing) or the post-build verdict is `incomplete`; 3 when `require` in `lakefile.toml` or Mathlib in imports leaves only a proof verdict (builds nothing, says so on the last line, and names the two project commands, which run project and dependency code).
- **No false refusal:** Regula publishes [a closed list of refusals](specification/README.md#the-closed-list-of-refusals), each proved true of what Lean, Lake or the OS answered in that run; a project with no refusal on which the rules hold passes. "No false refusal" means a refusal is never untrue, not that every reasonable project passes.
- **Shell safety:** `lakefile.toml` has no key that sets an environment variable, so `REGULA_FULL` comes from whoever started the run; with it set, `lake lint` runs the full gate on that directory (outside the contract, printing the proof-verdict-only line if `require` is present). Read a full verdict only from a checker built apart from the project (a planted program can print any line), and check the directory at the end of the last line in case `REGULA_FULL` stayed set in your shell.

## Purpose and constraint

Regula is a checker of Lean builds whose claim is meant to be exact and proved, so that people can trust it, and whose own code is meant to be the example of how Lean 4 code should be written: well factored, well designed, following best practice, and formally proven. Its owner decided on 2026-10-31 that being free of bugs outranks every lint rule and feature, so Regula gives up any rule, feature or package it cannot prove rather than patching it, documenting a limit or keeping a stated gap. Only Lean, its kernel and Lake's own behaviour are meant to stay trusted, with a short list of behaviours of the operating system, each tied to the platforms on which it was observed; Regula's own code is meant to be proved, or so thin that it only calls Lean. The [run of the checker](specification/README.md#the-run-of-the-checker) states what is proved of its effects, and the [trusted base](specification/README.md#the-trusted-base) what stays assumed.

That floor is a foundation, not a frozen scope ([the record of 2026-11-03](specification/confirmation.md#2026-11-03-regulas-direction-and-the-readme)). Regula's long-term goal is to capture a strict Lean 4 engineering standard and enforce it as a linter across both theorem proving and functional programming, pairing exact diagnostics with actionable fix guidance so coding agents meet both functional and non-functional requirements across soundness, totality, design, refactoring and architecture. Today (`v0.13.0`), Regula ships only eight proved checks, those above but RG1011, which `main` adds after that release, and emits neither fix suggestions nor a standalone design or architecture standard: earlier unproved rules and helpers were removed under the 2026-10-31 rule, and each new standard item, fix or rule lands only once it is simple enough to specify and prove to the same bar.

Regula aims to be for Lean linters what [seL4](https://sel4.systems/Verification/proofs.html) is for kernels: a tool whose claim is exact and proved, which is what earns trust. That sentence states the aim and does not say it has been reached. Simplicity is how it becomes achievable, as in [LionsOS](https://trustworthy.systems/projects/LionsOS), where each component does only the minimum its use case needs. On 2026-11-01 the owner made this a constraint over all work on Regula, and it governs every later change:

- Removal comes first: before adding or repairing anything, ask whether it can be deleted, or its input narrowed, so the need goes away.
- Hard proofs are a warning: a proof far harder than the code it covers means the code should get simpler, not only better proved.
- Simplicity never replaces proof: RG1001 to RG1006, the two verdicts and the demand for no bugs all stand.
- One use case: one toolchain, one way to run it, a closed input, and a truthful refusal for anything else. Refusing something outside a narrow published contract is not a false refusal.
- A claim in the style of seL4: exactly what is proved, for which inputs, under which listed assumptions, with no superlatives in public until the proofs back them.
- The work follows it too: the simplest analysis that answers the question, with no frameworks.

So this rules out adding 1,000 lines to keep an unusual folder layout working, adding a mode to avoid a refusal, or keeping a tool in the repository for one analysis. It still allows a long proof of something truly hard, such as the two-way axiom rules.

The full verdict stays at its built size. On 2026-11-01 the owner was shown that the full verdict had 11,518 lines of specification and 1,698 of program, about 6.8 to 1, against about 4,300 and 1,900 without it, about 2 to 1, and the case each way, and chose to keep it. So simplicity does not outrank the confirmed full verdict at this size. The size stays a warning, and work that shrinks it without losing a word the owner confirmed is welcome, as [the record](specification/confirmation.md#the-size-of-the-full-verdict) says.

## Work on Regula

Regula is built spec-first in Lean 4: specifications are written and proved non-vacuous before code changes, and every decision-bearing function is proved over the definitions the executable runs.

- **Where to contribute:** Work is welcome across building out the Lean 4 engineering standard, adding actionable fix guidance to diagnostics, proposing and proving new checks across functional programming, theorem proving, design, refactoring and architecture (each specified and proved before shipping), and shrinking the full verdict's specification without losing a confirmed guarantee.
- **Layout:** [`lean/Regula/`](lean/Regula/) holds the checker, each rule's check in a module of its own below [`lean/Regula/Rules/`](lean/Regula/Rules/); [`specification/`](specification/) holds the [`lean-intent`](https://github.com/rbeauchamp/lean-intent) specifications, bidirectional proofs and closed assumption list, each rule's statement and proofs below [`specification/RegulaSpecification/Rules/`](specification/RegulaSpecification/Rules/). Adding a rule is those two modules and a line in each registry ([how](CONTRIBUTING.md#adding-a-rule)).
- **Local gate:** With Lean `v4.35.0` installed (and GitHub access on first build for `lean-intent`), run `lean --run lean/Regula/DiagnosticsGate.lean local`.
- **Contributor docs:** [The specification](specification/README.md) states each rule, proof and assumption; [`specification/confirmation.md`](specification/confirmation.md) records the owner's decisions; and [`CONTRIBUTING.md`](CONTRIBUTING.md) gives every rule for changes and reviews.

## License

[MIT](LICENSE).
