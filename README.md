# Regula

You use coding agents to write Lean 4—both as a functional programming language and as a theorem prover—because you want verified software rather than plausible code. A green `lake build` does not guarantee that: an agent can finish with a `sorry` that only warned, a declared `axiom`, `native_decide`, an `unsafe` or `partial` definition, a `while` loop, or build-time code that ran on your machine, and you cannot read every proof by hand.

In Lean 4, proofs are erased at compile time, so compiled binaries run the executable definitions directly. Pairing a coding agent that generates code and proofs at build time with Lean's kernel and a proved checker verifies those proofs once before the program runs, without runtime proof search—provided nothing lets proof holes, unprofiled axioms, non-termination, hidden panics, or unproved replacements of compiled code slip between a proof and the compiled program.

Regula is a strict Lean 4 linter built to hold coding agents to verified engineering standards across both functional programming and theorem proving:

- **Actionable agent diagnostics:** `lake lint` reads the finished build, reports exact findings such as `RG1002 double (module Demo): depends on sorryAx` (rule, constant and module) paired with an indented `fix:` guidance line beneath each finding, and ends with a verdict line (`regula: proof verdict: fail`) and exit code (`0` for `pass` and for nothing else).
- **Proved rules, not heuristics:** Each rule, RG1001 to RG1006 and RG1011 to RG1013, is proved in Lean 4 to refuse every violation and only violations over its input (`rg1001_exact` to `rg1006_exact`, `rg1011_exact` to `rg1013_exact`).
- **Proved foundation today, broader standard ahead:** Regula ships all eleven proved checks (RG1001 to RG1006, RG1010 to RG1013, and RG2001) on Lean `v4.36.0`, proved-safe fix guidance on every registered rule, and the standalone Lean 4 engineering standard in [`STANDARD.md`](STANDARD.md), distinguishing enforced rules from manual and planned practices. Further standard items and new design, refactoring and architecture lint rules remain planned and ship only once formally specified and proved ([Purpose and constraint](#purpose-and-constraint), [Work on Regula](#work-on-regula)).

Regula gives one of two verdicts across three run routes, and its output names which verdict ran ([full scope and assumptions](#what-a-pass-means)):

| Route | Command | Target projects | Checks and trust boundary | Exit codes |
| --- | --- | --- | --- | --- |
| **In-tree proof verdict** | `lake build --wfail && lake lint` (in project directory, no Lake options, `REGULA_FULL` and `REGULA_PROOF` unset) | Any Lean `v4.36.0` project, including `[[require]]` dependencies and Mathlib ([setup](#in-tree-proof-verdict-lake-lint)) | Runs `RG1001`–`RG1006`, `RG1011`–`RG1013`, and `RG2001` kernel cone replay of [claimed modules](#the-checks). Runs project and dependency code; holds only for a project placing no file or code aimed at the checker or toolchain (no `RG1010`). | `0` (`pass`), `1` (`fail`), `2` (`incomplete`) |
| **Out-of-tree proof verdict** | `lake build --wfail` in `DIR`, then `REGULA_PROOF=DIR lake exe lint PROFILE` (from a Regula checkout built apart from the project, no Lake options, `REGULA_FULL` unset) | Already-built zero-dependency `lakefile.toml` packages without `lakefile.lean`, with non-empty `lean_lib` `defaultTargets`, and without adding `regula` to `[[require]]` or modifying `DIR/lakefile.toml` or `DIR/lake-manifest.json` ([setup and limits](#out-of-tree-proof-verdict-regula_proofdir)) | Runs `RG1001`–`RG1006`, `RG1011`–`RG1013`, and `RG2001` kernel cone replay on built `.olean` files. Does not rebuild `DIR`, check stale edits, or run `RG1010`; holds only for a project placing no file or code aimed at the checker or toolchain ([Proof verdict](#proof-verdict)). | `0` (`pass`), `1` (`fail`), `2` (`incomplete`) |
| **Full verdict** | `REGULA_FULL=DIR lake exe lint PROFILE` (from a Regula checkout built apart from the project, no Lake options, `REGULA_PROOF` unset) | Standalone library projects with `lean_lib` `defaultTargets`, no `require` in `lakefile.toml`, no Mathlib imports, and no `lakefile.lean` ([The full gate](#the-full-gate)) | Reads and checks project config and sources (`RG1010`), copying admitted inputs into an isolated temporary tree for `lake build --wfail`, then runs `RG1001`–`RG1006`, `RG1011`–`RG1013`, and `RG2001` kernel cone replay on that build. Holds under H1–H5 and [the trusted base](specification/README.md#the-trusted-base), even if the project is aimed at the checker ([Full verdict](#full-verdict)). | `0` (`pass`), `1` (`refused` / `fail`), `2` (`incomplete`), `3` (`proofOnly`, builds nothing) |

A pass does not mean your code is correct: no checker can say a theorem states what you meant, so theorem statements stay yours to read. Beyond RG1011's refusal of unexempted `@[implemented_by]` and `@[extern]` on a claimed constant, of an initialization function (`@[init]` or `@[builtin_init]`) on a claimed definition, and of an exported (`global` or `scoped`) `@[csimp]` entry registered in a claimed module whose theorem is not declared in any claimed module, and RG1012's refusal of a claimed definition whose value mentions a panic form, the proof verdict says nothing about what a compiled program runs.

## Use it

Released installs use `<latest-release-tag>` from [GitHub Releases](https://github.com/rbeauchamp/regula/releases/latest) for the current release, or that release's own tag from [the release history](https://github.com/rbeauchamp/regula/releases) when following an archived release. Unreleased checkouts test directly against that checkout (via a local `path` requirement for `lake lint`, or by building and running from that checkout apart from the project for `REGULA_PROOF` and `REGULA_FULL`) rather than an earlier release tag that may not implement the documented commands or checks.

### In-tree proof verdict (`lake lint`)

Put `leanprover/lean4:v4.36.0` in `lean-toolchain`. For a released install, check the latest release tag on [GitHub Releases](https://github.com/rbeauchamp/regula/releases/latest) and add this to `lakefile.toml`, replacing `<latest-release-tag>` with that tag (use that release's own tag when reading an archived release, or replace `git` and `rev` with `path = "/path/to/regula"` when testing an unreleased Regula checkout):

```toml
name = "demo"
defaultTargets = ["Demo"]
lintDriver = "regula/lint"
lintDriverArgs = ["standard-logical"]

[[require]]
name = "regula"
git = "https://github.com/rbeauchamp/regula"
rev = "<latest-release-tag>"

[[lean_lib]]
name = "Demo"
```

Run `lake update regula`, then run `lake build --wfail` and `lake lint` in order on one build (chaining with `&&` so a failed update or build stops before `lake lint` reads a stale build), from the project's own directory with no option of Lake's and `REGULA_FULL` and `REGULA_PROOF` unset:

```sh
lake update regula &&
  lake build --wfail &&
  lake lint
```

For this `Demo.lean`, `lake build --wfail` fails at `double`, while a plain `lake build` only warns there. After that plain build, `lake lint` refuses `double` and `twice` (whose proof depends on `double`):

```lean
module

public section

theorem double (n : Nat) : n + n = 2 * n := by sorry

theorem twice (n : Nat) : 2 * n = n + n := (double n).symm
```

```text
  regula: read 1 claimed modules and 2 of their constants
  RG1002 twice (module Demo): depends on sorryAx
  fix: complete the proof or remove the unfinished declaration rather than leaving sorry or admit; if inherited from a dependency, complete that declaration first
  RG1002 double (module Demo): depends on sorryAx
  fix: complete the proof or remove the unfinished declaration rather than leaving sorry or admit; if inherited from a dependency, complete that declaration first
  RG1005 twice (module Demo): depends on [sorryAx], outside the profile
  fix: remove the dependency on axioms outside the configured profile (kernel-only, choice-free, or standard-logical); sorryAx, native-proof, and non-standard axioms are refused by every profile
  RG1005 double (module Demo): depends on [sorryAx], outside the profile
  fix: remove the dependency on axioms outside the configured profile (kernel-only, choice-free, or standard-logical); sorryAx, native-proof, and non-standard axioms are refused by every profile
  4 findings
regula: proof verdict: fail
```

- **Exit codes:** `0` for `pass`, `1` for `fail`, `2` for `incomplete`.
- **Output format:** Diagnostic lines—including each finding's `fix:` guidance line beneath it—start with two spaces and escape newlines and carriage returns as `\n` and `\r`, so neither findings nor fix guidance can forge the final verdict line. A `pass` ends its last line with the audited directory (the full gate also prints Lake's build output beforehand).

### Out-of-tree proof verdict (`REGULA_PROOF=DIR`)

Use this route for zero-dependency `lakefile.toml` packages that use metaprogramming, `macro`, or deriving handlers refused by `RG1010`, without adding `regula` to `[[require]]` or modifying `DIR/lakefile.toml` or `DIR/lake-manifest.json`. For a released install, check the latest release tag on [GitHub Releases](https://github.com/rbeauchamp/regula/releases/latest), clone and build Regula apart from the project (replacing `<latest-release-tag>`, or using that release's own tag for an archived release), build the target package with `lake build --wfail`, and run `REGULA_PROOF=DIR lake exe lint PROFILE` (with no option of Lake's and `REGULA_FULL` unset), chaining with `&&` so `lake exe lint` runs only after clean clone and build steps. When testing an unreleased Regula checkout, skip `git clone` and run the remaining `&&`-chained steps directly from that checkout apart from the project instead of an earlier release tag (a release without `REGULA_PROOF` on the same Lean pin ignores it and audits Regula itself):

```sh
git clone --branch <latest-release-tag> https://github.com/rbeauchamp/regula /path/to/regula &&
  (cd /path/to/regula && lake build lint) &&
  (cd /path/to/project && lake build --wfail) &&
  (cd /path/to/regula && REGULA_PROOF=/path/to/project lake exe lint standard-logical)
```

- **Target admission:** Regula resolves `DIR` via `realPath`, refuses `DIR/lakefile.lean` before loading (`incomplete (RG2001)`, exit `2`), loads only `DIR/lakefile.toml` via `Lake.loadWorkspaceRoot` without writing `DIR/lakefile.toml` or `DIR/lake-manifest.json`, and refuses empty or non-`lean_lib` `defaultTargets` (`incomplete (RG2001)`, exit `2`, while admitting `globs`).
- **Checks and exit codes:** Runs `RG1001`–`RG1006`, `RG1011`–`RG1013`, and `RG2001` kernel replay on the built `.olean` files. Exits `0` with `regula: proof verdict: pass, which says nothing about what ran during the build, on <realDir>` only when all checked rules and kernel replay pass; exits `1` with `regula: proof verdict: fail` on rule violations; exits `2` with `regula: proof verdict: incomplete (RG2001)` otherwise.
- **Scope limits:** Because `DIR` is already built before `REGULA_PROOF` runs, it does not rebuild `DIR`, check stale `.lean` edits, run `RG1010`, or hold if `DIR` placed code or files aimed at the checker or toolchain. Under Lake's default per-package `leanLibDir` layout, packages with imported `[[require]]` dependencies fail closed at import as `incomplete (RG2001)`, whereas path `[[require]]` dependencies configured to share the root package's `buildDir`/`leanLibDir` place their `.olean` files on `root.leanPath` below `rootLib` and lie outside the zero-dependency contract. For standalone library projects needing `RG1010`, see [The full gate](#the-full-gate).

## The checks

Eleven checks ship on Lean `v4.36.0`, covering proof foundations, program totality, compiled code, hidden panics, module files, pre-build source admission, and kernel cone replay, with per-finding `fix:` guidance across all nine registered rules (RG1001 to RG1006 and RG1011 to RG1013). See [the specification](specification/README.md#the-rules) for full edge-case derivations, source citations, and proofs:

| Rule | Area | What it refuses | Specification |
| --- | --- | --- | --- |
| RG1001 | Proofs & axioms | A claimed module declares an `axiom`, even one that nothing uses. | [RG1001–RG1005](specification/README.md#rg1001-to-rg1005-the-foundation-profile) |
| RG1002 | Proofs & axioms | A constant of a claimed module depends on `sorryAx`, directly or through an import. | [RG1001–RG1005](specification/README.md#rg1001-to-rg1005-the-foundation-profile) |
| RG1003 | Proofs & axioms | A constant of a claimed module depends on an axiom other than Lean's `propext`, `Quot.sound` and `Classical.choice`, and RG1002 and RG1004 do not name it. | [RG1001–RG1005](specification/README.md#rg1001-to-rg1005-the-foundation-profile) |
| RG1004 | Proofs & axioms | A constant of a claimed module depends on an axiom with the name form that `native_decide` gives. | [RG1001–RG1005](specification/README.md#rg1001-to-rg1005-the-foundation-profile) |
| RG1005 | Proofs & axioms | A constant of a claimed module depends on an axiom that the project's profile does not admit. | [RG1001–RG1005](specification/README.md#rg1001-to-rg1005-the-foundation-profile) |
| RG1006 | Totality & safety | A claimed constant that is `unsafe`, `partial` or named as a recursion helper without an exempted form; a claimed constant whose value directly mentions `Lean.Loop.mk` or `repeatM` (`while`, `repeat`); or a claimed definition or opaque constant whose value directly mentions `Lean.Order.fix` (`partial_fixpoint`). | [RG1006](specification/README.md#rg1006-unsafe-and-partial-declarations) |
| RG1011 | Compiled code | A claimed constant with unexempted `@[implemented_by]` or `@[extern]`; a claimed definition with an initialization function by `@[init]` or `@[builtin_init]`; or an exported (`global` or `scoped`) `@[csimp]` entry registered in a claimed module whose theorem is not declared in any claimed module. | [RG1011](specification/README.md#rg1011-replaced-compiled-code) |
| RG1012 | Totality & safety | A definition or opaque constant of a claimed module whose value mentions a panic form (`panicCore`, `panic`, `panicWithPos`, `panicWithPosWithDecl`, or a non-theorem constant whose name's last string component contains `!`). | [RG1012](specification/README.md#rg1012-hidden-panics) |
| RG1013 | Module files | A claimed module whose file is not a `module` file, so what an importer of it relies on is not stated. | [RG1013](specification/README.md#rg1013-files-that-are-not-module-files) |
| RG1010 | Language subset | A Lean file of the claim, the Lake configuration or `lean-toolchain` that holds something outside the closed set (full gate only). | [RG1010](specification/README.md#rg1010-the-language-check) |
| RG2001 | Environment & replay | Build load failure, closed-list refusal with exit `2` in the full gate, non-closed input, missing claimed module index for `@[csimp]` or replacement attributes, unshown claimed constant outside safe in-profile theorems/attributes/names, or failed kernel cone replay (`incomplete`). | [RG2001](specification/README.md#rg2001-the-environment) |

- **Claimed modules:** the modules of the root package's default targets plus each root-package module their imports reach (what `lake build` builds; targets that no default target reaches are outside the claim).
- **Profiles (`lintDriverArgs`):** `kernel-only` (no axiom), `choice-free` (`propext` and `Quot.sound`), and `standard-logical` (`propext`, `Quot.sound` and `Classical.choice`).
- **RG1006 exemptions and `Lean.Order.fix` scope:**
  - The two exempted forms—a `partial` recursion helper `b._unsafe_rec` beside its safe definition `b`, or the unsafe half `T.ctorIdx._impl` of a verified compiler-generated `ctorIdx` pair—exempt a constant from the safety/name clause only, never from loop constructs or `Lean.Order.fix`.
  - `Lean.Order.fix` (which `partial_fixpoint` elaborates to at Lean `v4.36.0`, [the source read](specification/README.md#rg1006-unsafe-and-partial-declarations)) is checked only on definitions and opaque constants, not theorems and not `Lean.Order.lfp_monotone` (`inductive_fixpoint`, `coinductive_fixpoint`, `coinductive`), so a mention of `Lean.Order.fix` in a theorem's proof is not refused for it. The other clauses read every claimed constant.
- **RG1011 exemptions and `@[csimp]` scope:**
  - `@[implemented_by]` exempts only the safe half `T.ctorIdx` of a verified compiler-generated `ctorIdx` pair whose structural form matches `T.casesOn` and `getObjTagNat`.
  - An opaque constant with an initialization function, which `initialize` declares, is not refused for it, because Lean's logic states nothing of its value.
  - Exported `@[csimp]` on a theorem declared in a claimed module (including a one-line claimed alias that restates the equality, `@[csimp] public theorem alias : @f = @g := Dep.thm`) is admitted: its attribute checks the equality type `@f = @g`, the kernel replays safe claimed theorems within the profile, and RG1006 refuses `unsafe` and `partial` claimed constants without an exempted form.
  - Under the proof verdict, `attribute [local csimp]` (`.olean`-invisible, never written to `.olean`) and dependency-registered `@[csimp]` (in unclaimed modules, not checked by RG1011) remain outside the rule. Under the full verdict RG1010 refuses `csimp` in each file it reads, a project with a `require` has only the proof verdict, and the toolchain's own `@[csimp]` registrations stay trusted.
- **RG1012 details:** A `!`-named non-theorem constant covers `xs[i]!`, `Option.get!`, `List.head!`, `String.toNat!`, `panic!`, `unreachable!`, and `assert!`. By default a panic returns a default value and the program goes on; `xs[i]?`, `dbg_trace`, and theorems are not refused.
- **RG1013 details:** Adds nothing to what a proof depends on. Each claimed file needs the `module` header, and what a proof of another file unfolds of it needs `@[expose]` or `import all`. Lean refuses a `module` file that imports a file that is not one, so a project whose claimed modules import such a file of a dependency cannot pass.
- **RG2001 details:** Verdict is `incomplete`. Triggered when the checker cannot load the build, the full gate stops on a case of [its closed list](specification/README.md#the-closed-list-of-refusals) with exit `2`, its input does not have the closed form, a claimed module's index is missing when reading its `@[csimp]` entries or its own replacement attributes, a claimed module holds a constant the merged environment does not show to the rules and that is no theorem within the profile, has a recursion helper's name, or has unread or forbidden replacement attributes in its own module, or Lean's kernel does not accept the replay of the claim's cone.

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

Where `lake check` also refuses (as on `sorry` or an axiom in use), `lake lint` reports a rule code. RG1001 to RG1006 and RG1011 to RG1013 read only the loaded build's constants, with the attributes that RG1011 reads (`@[implemented_by]`, `@[extern]`, `@[init]`, `@[builtin_init]`, and exported claimed-module `@[csimp]` entries), its claimed modules, which of its modules Lean read as `module` files, and its profile, so they read no source text, compiled code or build log.

## Before you adopt it

- **Toolchain & release:** Regula reads only `leanprover/lean4:v4.36.0` (enforced by `Regula.Closed.pinnedLean`). Released installs use `<latest-release-tag>` from [GitHub Releases](https://github.com/rbeauchamp/regula/releases/latest) for the current release (or that release's own tag when reading an archived release), while unreleased checkouts test directly against that checkout rather than an earlier release tag; check [all releases](https://github.com/rbeauchamp/regula/releases) for upgrade notes (including breaking changes between releases) and compatibility pins for older Lean toolchains.
- **Named configurations:** The claim holds only for `leanprover/lean4:v4.36.0` on macOS 27.2 (Apple silicon) or Ubuntu 24.04.5 LTS (x86-64), using one published run per route with no option of Lake's:
  - `lake lint` in the project's own directory with `REGULA_FULL` and `REGULA_PROOF` unset;
  - `REGULA_PROOF=DIR lake exe lint PROFILE` from a Regula checkout built apart from the project against an already-built zero-dependency `lakefile.toml` package without `lakefile.lean`, with non-empty `lean_lib` `defaultTargets`, and with no shared-`leanLibDir` `[[require]]`; or
  - `REGULA_FULL=DIR lake exe lint PROFILE` from a Regula checkout built apart from the project.
  - Setting both `REGULA_FULL` and `REGULA_PROOF`, or anything else (Windows, other Linux or macOS versions, `lake -d`, `lake -f`, starting the full gate from a project's Lake, or `lake lint` with `REGULA_FULL` or `REGULA_PROOF` set), is outside the contract ([the trusted base](specification/README.md#the-named-configurations)) and not a defect.
- **No `lake -d` or `lake -f`:** Lake gives a program nothing a project cannot set to identify the selected workspace, so `lake lint` still audits the current directory and can exit `0` naming it rather than the option's target. No argument names a project, and anything in `lintDriverArgs` other than one profile exits `2`, so a project cannot choose what is audited.
- **Dependencies:** Projects with a `require` dependency or Mathlib imports can have only the proof verdict, whose two commands run project and dependency code. RG1013 needs each claimed file to be a `module` file, and the files that `lake new` writes at this release are not. A `module` file can import only `module` files, so a file of a dependency that is not one and that a claimed module imports, directly or through its imports, rules a pass out until it is one: `Mathlib.lean` and each file below `Mathlib/` at Mathlib's tag `v4.35.0` is one.
- **Memory:** Cone replay holds every constant the claim depends on in memory ([measured](specification/README.md#what-a-pass-means) at 4.3 GiB and two minutes importing Mathlib); much larger cones may exceed machine memory, a limit of the named configuration rather than a defect.
- **Full gate table:** Refuses anything outside a closed table (`macro`, `syntax`, `notation`, `lakefile.lean`, default executables, and unlisted harmless constructs included); see [The full gate](#the-full-gate).

## What a pass means

### Proof verdict

- **Guarantee:** Passing `lake build --wfail` and the proof-verdict checker (`lake lint`, or out-of-tree `REGULA_PROOF=DIR lake exe lint PROFILE` from a Regula checkout built apart from the project) on one build means the proofs of the claimed modules are sound and use only axioms the profile allows, for a project that places no file or code aimed at the checker or the toolchain.
- **Module files:** A pass also says that Lean read the file of each claimed module as a `module` file (RG1013), by what its `.olean` states.
- **Kernel cone replay:** The proof-verdict checker (`lake lint`, or `REGULA_PROOF=DIR lake exe lint PROFILE` from a Regula checkout built apart from the project) submits to Lean's `Kernel.Environment.replay`, into an empty environment, each constant of the claimed modules, every constant reached through what each mentions in Lean's data (type, value, inductive block, and `Eq` for a quotient), and the constants the kernel itself builds into a term—except `Quot.mk`, `Quot.lift`, and `Quot.ind`, which the kernel adds with `Quot`—and nothing else. When two modules declare a theorem of one name and type, Lean's import keeps one, and the replay also gets each claimed module's differing copy under a name no constant of the build has, checking every module's proof. An unsound proof in a reached dependency fails it too.
- **Outside its scope:**
  - *Checker-attack routes:* Because `lake build --wfail` and in-tree `lake lint` run in the project's Lake, a project aimed at the checker can forge a pass via build-time code—or, on `lake lint`, via a library loaded from the project's library directory into the checker, a doctored Regula from its configuration or package directory, or a `lakefile.lean` ([the specification](specification/README.md#a-project-aimed-at-the-checker)). On `REGULA_PROOF=DIR`, `lake build --wfail` still runs project build-time code beforehand.
  - *Compiled execution and RG1011:* RG1011 refuses each constant of a claimed module that has `@[implemented_by]` (other than the verified safe half `T.ctorIdx` of a compiler-generated `ctorIdx` pair) or `@[extern]`, each definition of one for which `@[init]` or `@[builtin_init]` names an initialization function, and each exported (`global` or `scoped`) `@[csimp]` entry registered in a claimed module whose theorem is not declared in any claimed module. Beyond that it says nothing about what a compiled program runs ([RG1011](specification/README.md#rg1011-replaced-compiled-code)):
    - Exported `@[csimp]` on a theorem declared in a claimed module passes (its safe proof the kernel checks in the claim's cone within the profile, while RG1006 refuses `unsafe` and `partial` claimed constants without an exempted form).
    - `attribute [local csimp]` (`.olean`-invisible, never written to `.olean`) and dependency-registered `@[csimp]` (in unclaimed modules, not checked by RG1011) stay outside the proof verdict; under the full verdict RG1010 refuses `csimp` in each file it reads, a project with a `require` has only the proof verdict, and the toolchain's own `@[csimp]` registrations stay trusted.
    - A claimed constant that calls a dependency's or the toolchain's constant with `@[implemented_by]`, `@[extern]`, or an initialization function passes.
    - A constant of the exempted recursion-helper form, which names no origin, passes when a module's own code adds it during the build such as via `run_cmd` ([RG1006](specification/README.md#rg1006-unsafe-and-partial-declarations)).
  - *Panics (RG1012):* RG1012 refuses each claimed definition or opaque constant whose value mentions a panic form; a panic that a claimed function reaches through a dependency's or the toolchain's constant whose name has no `!`, such as `outOfBounds`, or in C code behind `@[extern]`, passes, and so does a mention in a theorem's proof ([RG1012](specification/README.md#rg1012-hidden-panics)).
  - *Partial fixpoints (RG1006):* RG1006 refuses each claimed definition or opaque constant whose value directly mentions `Lean.Order.fix`, so a pass says that none does; a `partial_fixpoint` definition of a dependency or the toolchain that a claimed function calls passes, and so does a mention of `Lean.Order.fix` in a theorem's proof ([RG1006](specification/README.md#rg1006-unsafe-and-partial-declarations)).
  - *Stale builds:* Checking without first running `lake build --wfail` reads whatever build is on disk.
- **Noncomputable definitions:** Regula adds no check or profile for `noncomputable` definitions ([2026-11-20](specification/confirmation.md#2026-11-20-noncomputable-definitions), [specification](specification/README.md#noncomputable-definitions)).
  - `∃ y, P y` is a `Prop`, and Lean's compiler erases proofs, so a proof of it gives a running program no `y`: a pass says what is proved of a claimed data-valued definition and does not establish that the definition has executable code.
  - In each body that it compiles, Lean's own compiler rejects a reference to a constant tagged `noncomputable` (or whose `_unsafe_rec` helper is tagged) that is still in a computationally relevant position after its rewriting (`@[csimp]`, `@[macro_inline]`) and erasure, unless the referenced constant is `Quot.mk`, `Quot.lift`, or `withPtrEq`, or has `@[extern]` or `@[implemented_by]`.
  - Lean compiles no code from the body of a definition with `@[extern]`, `@[implemented_by]` or an initialization function, and so checks no reference there; RG1011 (with loader checks under RG2001) refuses unexempted `@[implemented_by]` and `@[extern]` on claimed constants, `@[init]`/`@[builtin_init]` naming an initialization function on claimed definitions, and exported claimed-module `@[csimp]` entries targeting theorems not declared in any claimed module.
  - Beyond erased positions, `@[csimp]` and `@[macro_inline]` rewriting, and dependency or toolchain constants, two cases with no compiled code were measured to pass `lake build --wfail` and `lake lint` under `standard-logical`: (1) uncalled `noncomputable` definitions (which also pass the full gate under `standard-logical`; `choice-free` and `kernel-only` refuse those depending on `Classical.choice` via RG1005), and (2) `noncomputable def main` (or `main` inside a `noncomputable section` calling a `noncomputable` definition) in a default `lean_exe`, where Lean emits no C `main` yet default static linking resolves `_main` from `libLeanExport.a` on macOS arm64 so the built binary runs `lean4export` (observed on macOS arm64; not measured on Ubuntu; the full gate already refuses default `lean_exe` targets).
- **Trusted commands:** `lake build --wfail` and `Kernel.Environment.replay` are Lake's and Lean's own; Regula makes no claim of its own about what they decide, and proves which constants it gives the replay.

### Full verdict

- **Guarantee:** Passing the full gate establishes everything above (closing the four checker-attack routes), plus that while Lake built the files read, no project-written code ran and no file installed anything that replaces what the compiler runs for a definition (apart from Lean's own compiler-generated `T.ctorIdx` / `T.ctorIdx._impl` pair, covered by `ctorIdxTag`).
- **Hypotheses ([H1 to H5](specification/README.md#h1-and-h2), re-read at each Lean upgrade):**
  - H1 and H2 about Lean `v4.36.0`: the tree read is the tree Lean elaborates, and what the closed set admits runs no such code; no proof here can examine Lean's own program, so a route H2 misses would be a false pass.
  - H3 about Lake: its build compiles what the check read.
  - H4 about OS `realpath`: a path crossing a link gets another real path.
  - H5 about Lake: it takes `lakefile.toml` when nothing answers to `lakefile.lean`.
  - Plus the specification's [list of assumptions](specification/README.md#the-trusted-base) about Lean, Lake and the OS.
- **Outside its scope:** What a theorem's statement means to a reader, what another process does, any project with a dependency or Mathlib, and, as under the proof verdict, whether a claimed data-valued definition has executable code. `noncomputable` stays in RG1010's table and no rule reads it, so the gate's rules read an uncalled `noncomputable` definition as they read any claimed constant, and one that uses `Classical.choose` was measured to pass under `standard-logical`; the full gate refuses default `lean_exe` targets.

## The full gate

Build and start the checker from its own checkout apart from the project (a precondition alongside `PATH`, since Lake runs a project's `lakefile.lean` on load and the checker does not test who started it). For a released install, check the latest release tag on [GitHub Releases](https://github.com/rbeauchamp/regula/releases/latest) and replace `<latest-release-tag>` (or use that release's own tag when reading an archived release), chaining with `&&` so `lake exe lint` runs only after a clean clone and build; when testing an unreleased Regula checkout, skip `git clone` and run the remaining `&&`-chained command directly from that checkout apart from the project:

```sh
git clone --branch <latest-release-tag> https://github.com/rbeauchamp/regula /path/to/regula &&
  (cd /path/to/regula && lake build lint && REGULA_FULL=/path/to/project lake exe lint standard-logical)
```

Before any Lake call on the project, the checker reads `lean-toolchain`, `lakefile.lean` by name and `lakefile.toml`. In one process, it runs the check and, if admitted, builds, replays the claim's cone and runs the rules inside a fresh temporary directory holding only the judged files and pinned `lean-toolchain` (asking to remove it afterward); nothing in the project directory is written, and its `.lake`, manifest and other files are unused.

Project requirements (no `require` of Regula needed; nothing of a dependency is fetched or run):

- **Configuration:** `lean-toolchain` says `leanprover/lean4:v4.36.0`, `lakefile.toml` has no `require` and uses only keys in the closed set, and no `lakefile.lean` exists.
- **Closed language ([specification](specification/README.md#the-language-check)):** Each file starts with `module`. Admitted examples: Regula's own core, and library code using `simp`, `omega`, `decide +kernel`, `variable` and `deriving DecidableEq`. Refused examples: `run_cmd`, `#eval`, `#guard`, `run_tac`, `by_elab`, `native_decide`, `decide +native`, `macro`, `syntax`, `notation`, `elab`, `initialize`, `@[local macro k]` and a plugin in `lakefile.toml`, plus anything outside the closed table (even if harmless, or added in a later Lean).
- **Targets & paths:**
  - Default targets are libraries (`lean_lib`; default executables, including `lake new`'s template, are refused here and still get the proof verdict).
  - No target has its own `srcDir`; the package's source directory lies at or below the project, with component names of ASCII letters, digits, `_` and `'` only.
  - Libraries name modules via `roots` or single-module `globs` (not `Data.+` or `Data.*`, which need a directory listing).
  - Each read file's real path is its exact path below the project's real path, so no read file is reached through a symbolic link; any unread file the build needs (such as a data file) is absent, so the build fails and the verdict is `fail`.

For this `Demo.lean`, the checker prints `regula: full verdict: pass, under the hypotheses H1 to H5 and the trusted base of its specification, at Lean 4.36.0, on /path/to/project`:

```lean
module

public section

/-- Addition commutes. -/
theorem swap (a b : Nat) : a + b = b + a := by omega
```

- **Exit codes:**
  - `0` only for a full-verdict `pass` (last line ends with the audited directory).
  - `1` when the language check refuses (compiles nothing) or the verdict is `fail`.
  - `2` when the language check gives `incomplete` (`RG2001`, such as an unreadable module file, compiling nothing) or the post-build verdict is `incomplete`.
  - `3` when `require` in `lakefile.toml` or Mathlib in imports leaves only a proof verdict (builds nothing, says so on the last line, and names the two project commands, which run project and dependency code).
- **No false refusal:** Regula publishes [a closed list of refusals](specification/README.md#the-closed-list-of-refusals), each proved true of what Lean, Lake or the OS answered in that run; a project with no refusal on which the rules hold passes. "No false refusal" means a refusal is never untrue, not that every reasonable project passes.
- **Shell safety:** `lakefile.toml` has no key that sets an environment variable, so `REGULA_FULL` and `REGULA_PROOF` come from whoever started the run. Setting both causes Regula to refuse as `incomplete (RG2001)` (exit `2`), and with either set, `lake lint` dispatches on that directory (outside the contract for `lake lint`). Read a full verdict only from a checker built apart from the project (a planted program can print any line), and check the directory at the end of the last line in case `REGULA_FULL` or `REGULA_PROOF` stayed set in your shell.

## Purpose and constraint

Regula is a checker of Lean builds whose claim is meant to be exact and proved, so that people can trust it, and whose own code is meant to be the example of how Lean 4 code should be written: well factored, well designed, following best practice, and formally proven. Being free of bugs outranks every lint rule and feature, so Regula gives up any rule, feature or package it cannot prove rather than patching it, documenting a limit or keeping a stated gap ([the confirmation record](specification/confirmation.md#2026-10-31)). Only Lean, its kernel and Lake's own behaviour stay trusted, with a short list of behaviours of the operating system, each tied to the platforms on which it was observed; Regula's own code is proved, or so thin that it only calls Lean ([the run of the checker](specification/README.md#the-run-of-the-checker), [the trusted base](specification/README.md#the-trusted-base)).

That floor is a foundation, not a frozen scope ([the direction record](specification/confirmation.md#2026-11-03-regulas-direction-and-the-readme)). Regula's long-term goal is to capture a strict Lean 4 engineering standard and enforce it as a linter across both theorem proving and functional programming, pairing exact diagnostics with actionable fix guidance so coding agents meet both functional and non-functional requirements across soundness, totality, design, refactoring and architecture. Today, Regula ships all eleven proved checks—RG1001 to RG1006, RG1010 to RG1013 and RG2001—on Lean `v4.36.0`, emits proved-safe indented `fix:` guidance beneath every finding of the nine registered rules, and publishes the standalone engineering standard in [`STANDARD.md`](STANDARD.md), separating enforced rules from manual and planned practices. Each new standard item, fix or rule ships only once it is simple enough to specify and prove to the same bar.

Regula aims to be for Lean linters what [seL4](https://sel4.systems/Verification/proofs.html) is for kernels: a tool whose claim is exact and proved, which is what earns trust. That sentence states the aim and does not say it has been reached. Simplicity is how it becomes achievable, as in [LionsOS](https://trustworthy.systems/projects/LionsOS), where each component does only the minimum its use case needs. Six principles govern all work on Regula ([the simplicity constraint](specification/confirmation.md#2026-11-01)):

- **Removal comes first:** before adding or repairing anything, ask whether it can be deleted, or its input narrowed, so the need goes away.
- **Hard proofs are a warning:** a proof far harder than the code it covers means the code should get simpler, not only better proved.
- **Simplicity never replaces proof:** RG1001 to RG1006, the two verdicts and the demand for no bugs all stand.
- **One use case:** one toolchain, one way to run it, a closed input, and a truthful refusal for anything else. Refusing something outside a narrow published contract is not a false refusal.
- **A claim in the style of seL4:** exactly what is proved, for which inputs, under which listed assumptions, with no superlatives in public until the proofs back them.
- **The work follows it too:** use the simplest analysis that answers the question, with no frameworks.

So this rules out adding 1,000 lines to keep an unusual folder layout working, adding a mode to avoid a refusal, or keeping a tool in the repository for one analysis. It still allows a long proof of something truly hard, such as the two-way axiom rules.

Simplicity does not outrank the confirmed full verdict at its built size ([the full-verdict size record](specification/confirmation.md#the-size-of-the-full-verdict)). The full verdict stays, its size remains a warning under the constraint, and work that shrinks it without losing a word the owner confirmed is welcome.

## Read Regula as an example

[`STANDARD.md`](STANDARD.md) sets out the Lean 4 engineering standard across theorem proving and functional programming and maps each practice to its enforcement status in Regula. Five examples across six modules in this repository illustrate those patterns directly:

- [`lean/Regula/Input.lean`](lean/Regula/Input.lean) — proof-bearing boundary admission (`Draft.admit` to `Input`, carrying `Input.closed` and `Input.claims`) and closed sum types (`Safety`, `Profile`).
- [`lean/Regula/Tables.lean`](lean/Regula/Tables.lean) — dependent lookup tables (`Tables i`) carrying proofs of what each table holds of input `i`, alongside `Tables.axiomSet` and `Input.cone`.
- [`lean/Regula/Effect.lean`](lean/Regula/Effect.lean) — pure effect trees (`Prog`) over a closed operation type (`Op`, `Resp`), separated from the thin IO table in [`lean/Regula/Table.lean`](lean/Regula/Table.lean).
- [`lean/Regula/Reach.lean`](lean/Regula/Reach.lean) — total graph search (`reach`, `reachGo`) by structural recursion on fuel, without `partial` or `while`; `mem_reach` proves it sound and complete when a supplied list holds every name with a successor and the fuel's `weight` bounds their total out-degree (the measure of `unseenWeight` and `unseenWeight_insert`), a bound that the callers in `Tables.lean` derive from the input.
- [`specification/RegulaSpecification/Rules/RG1011.lean`](specification/RegulaSpecification/Rules/RG1011.lean) — an independent rule specification (`Violates1011`), non-vacuity witnesses (`Witnesses.w1011`, `rg1011_adequate`, and `rg1011_noisy`, which takes from `t_mem_support` its premise that the admitted subject is a candidate), and a bidirectional proof over the executed check (`Link.rg1011_exact`).

## Work on Regula

Regula is built spec-first in Lean 4: specifications are written and proved non-vacuous before code changes, and every decision-bearing function is proved over the definitions the executable runs.

- **Where to contribute:** Work is welcome across building out [the Lean 4 engineering standard](STANDARD.md), refining proved-safe fix guidance for diagnostics, proposing and proving new checks across functional programming, theorem proving, design, refactoring and architecture (each specified and proved before shipping), and shrinking the full verdict's specification without losing a confirmed guarantee.
- **Layout:** [`lean/Regula/`](lean/Regula/) holds the checker, each rule's check in a module of its own below [`lean/Regula/Rules/`](lean/Regula/Rules/); [`specification/`](specification/) holds the [`lean-intent`](https://github.com/rbeauchamp/lean-intent) specifications, bidirectional proofs, deliverable/implementation/required-theorem declarations ([`RegulaSpecification/Required.lean`](specification/RegulaSpecification/Required.lean), checked by [`RequiredGate.lean`](specification/RequiredGate.lean)), and closed assumption list, each rule's statement and proofs below [`specification/RegulaSpecification/Rules/`](specification/RegulaSpecification/Rules/). Adding a rule is those two modules, a line in each registry, and its entry in `Required.lean` ([how](CONTRIBUTING.md#adding-a-rule)), so that adding or fixing a rule does not break another; the local gate still rebuilds and re-checks every rule on each run.
- **Local gate:** Run `lean --run lean/Regula/DiagnosticsGate.lean local` with Lean `v4.36.0` installed (and GitHub access on first build for `lean-intent` and for downloading/SHA-256-verifying pinned `no-comments` `v0.3.1` into `.cache/no-comments/` unless `NO_COMMENTS_BIN` is set). The gate:
  - runs all Lake build and lint checks (where `ruleDeliverables_cover_registry` statically covers the nine registered rules);
  - verifies via `specification/RequiredGate.lean` (`LeanIntent.Implementation.Read.check` and `LeanIntent.Required.Read.check`) that every discovered `Deliverable`, `Implementation`, and `Required` declaration and its listed theorems reside in Lake's `@/RegulaSpecification:modules` list, that each discovered `Deliverable` has a single `Implementation` naming a constant `subject` (with no awaiting deliverables) and at least one `Required` declaration, and that both read results are non-empty (without enforcing a fixed count if an entire non-rule `Deliverable`/`Implementation`/`Required` triple were deleted); and
  - strictly enforces the monotonic `no-comments check` against the `comment-ratchet.json` at the merge base with `origin/main` (or `main`).
  - Pull requests run the same command on GitHub with `fetch-depth: 0` ([`gate.yml`](.github/workflows/gate.yml)).
- **Contributor docs:** [`STANDARD.md`](STANDARD.md) states the Lean 4 engineering standard and what Regula enforces; [the specification](specification/README.md) states each rule, proof and assumption; [`specification/confirmation.md`](specification/confirmation.md) records the owner's decisions; and [`CONTRIBUTING.md`](CONTRIBUTING.md) gives every rule for changes and reviews.

## License

[MIT](LICENSE).
