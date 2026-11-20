# Lean 4 Engineering Standard

This document sets out a Lean 4 engineering standard for software engineers and coding agents writing verified functional programs and proofs. It covers both practices that [Regula](README.md) checks automatically and practices that stay manual engineering discipline.

In Lean 4, proofs live in `Prop` and are erased at compile time, so compiled binaries execute `Type`-valued definitions directly. Pairing a coding agent that generates code and proofs at build time with Lean's kernel and a proved checker verifies properties over all inputs (`∀ x`) once before the program runs, running the compiled definitions directly with no runtime proof search. That workflow depends on two halves: writing definitions, types, and specifications so illegal states and proof complexity are minimized from the start, and closing the build-time and runtime gaps where a green `lake build` can still diverge from what a proof states.

Regula enforces a proved subset of this standard today—eight checks in `v0.13.0`, plus three more on `main` that are in no release yet—and leaves design, specification, and intent review to engineers and agents. See [Enforcement status](#enforcement-status) for the exact boundary, [`README.md`](README.md) for usage and verdicts, and [`specification/README.md`](specification/README.md) for exact theorem statements and the trusted base.

## 1. Intrinsic typing at boundaries

Prefer types that make illegal states unrepresentable over post-hoc checks or sentinel conventions. Enforce invariants once where state is admitted or written, rather than repeating defensive guards where state is read.

When choosing how to enforce an invariant, prefer in order:

1. A type that makes an illegal state unrepresentable.
2. A relation true by construction.
3. An exhaustive check over a closed finite domain.
4. A machine-checked proof over the actual definition.
5. A runtime guard derived from the invariant.

Concrete Lean 4 practices:

- **Bound indices and preconditions in types:** Use `Fin n` or proof-bearing indexing (`xs[i]` with a bounds proof) instead of panicking operations (`xs[i]!`, `Option.get!`, `List.head!`).
- **Admit untrusted inputs into proof-bearing types:** Validate external data once at the boundary into a `Subtype` (`{ x : α // P x }`), a `Sigma` type, or a proof-bearing admission structure. Downstream functions then take valid inputs by type and carry no dead error branches or external validity hypotheses.
- **Model finite states with closed sum types:** Replace loosely coupled Boolean flags, parallel optional fields, or stringly-typed codes with `inductive` types so impossible combinations cannot be constructed and `match` exhaustiveness catches missing cases at compile time.

### Examples in Regula

- **Proof-bearing admission ([`lean/Regula/Input.lean`](lean/Regula/Input.lean)):** `Regula.Closed.Draft` holds raw loaded environment data together with `Draft.unique` (distinct constant names, constructed by the loader from hash map keys). `Draft.admit : Draft → Except String Input` checks the remaining two invariants once and returns `Regula.Closed.Input`, which carries `Input.closed` (every mentioned constant is held) and `Input.claims` (`modules ≠ []`). [`specification/RegulaSpecification/Proofs/Verdict.lean`](specification/RegulaSpecification/Proofs/Verdict.lean) proves `admit_ok_iff` in both directions. Every rule takes `Tables i` for an admitted `i : Input` and has no case for an empty claim or an open mention.
- **Dependent lookup tables ([`lean/Regula/Tables.lean`](lean/Regula/Tables.lean)):** `Regula.Closed.Tables (i : Input)` bundles lookup structures (`index`, `claimed`, `axiomReach`) with proof fields (`mem_index`, `mem_claimed`, `mem_axiomReach`) indexed by the exact input `i`. A table built for one input cannot be passed for another, and rule exactness proofs carry no separate table-consistency hypothesis.
- **Closed sum types ([`lean/Regula/Input.lean`](lean/Regula/Input.lean), [`lean/Regula/Rule.lean`](lean/Regula/Rule.lean), [`lean/Regula/Verdict.lean`](lean/Regula/Verdict.lean)):**
  - `Regula.Closed.Safety` has constructors `safe`, `unsafe`, and `partial`; it cannot represent a constant that is both unsafe and partial.
  - `Regula.Closed.Report` has constructors `pass`, `fail (first : Finding) (rest : List Finding)`, and `incomplete (why : String)`; it cannot represent a pass with findings, a failure with none, or an incomplete verdict without a reason.
  - `Regula.Closed.Profile` and `Regula.Closed.Verdict` are closed enums with proved injective encodings (`Profile.spelling_injective`, `Profile.ofSpelling?_eq_some`, `Verdict.exitCode_injective`, `Verdict.exitCode_eq_zero_iff`).

**Enforcement status:** Engineering discipline (human and agent review). Regula has no lint rule that judges data-model design.

## 2. Spec-first design, proof economy, and proved refinement

Avoid "program, optimize, then try to prove." Write specifications independently before writing code, keep implementations simple, and optimize only through proved equivalence.

- **Write specifications independently of the code:** State what a function must satisfy in terms other than its body—quantifiers, inductive relations, algebraic equations, or domain predicates—before implementing it. A specification transcribed from an implementation shares the implementation's mistakes.
- **Prove non-vacuity before proving the implementation:** Exhibit concrete positive and negative witnesses (`refused` and `admitted` inputs) and prove that degenerate implementations (such as reporting nothing, reporting everything, or returning a constant) fail the specification.
- **Prove the definition that executes:** Prove behavioral theorems over the exact functions called at runtime, not over a simplified copy written apart from the program.
- **Treat hard proofs as a design warning:** When a proof becomes much harder than the code it covers, simplify the code or narrow its input domain before adding proof machinery. Keep code readable through clear names and composition; reserve comments for what code cannot state (rationale and rejected alternatives, external-system behavior cited by version and source lines, and hypotheses or limits).
- **Optimize via proved refinement, never unproved replacement:** Implement a clear specification or reference definition and prove an optimized version equal to it (`f = g`), or register a proved equality theorem with `@[csimp]` where appropriate under the proof verdict. Do not use `@[implemented_by]`, `@[extern]`, or `@[init]`/`@[builtin_init]` on claimed definitions, where Lean checks only type agreement and not behavioral equivalence.
  - *Exact `@[csimp]` scope:* RG1011 does not refuse `@[csimp]`, because Lean's compiler replaces `f` with `g` only via a theorem stating `@f = @g` (`isConstantReplacement?`, `Lean/Compiler/CSimpAttr.lean:40-55` at `v4.35.0`). Under the proof verdict, kernel cone replay checks every theorem in claimed modules within the profile; however, Lean also accepts `@[csimp]` on a theorem of another module (including `local` and `scoped`), whose proof the replay checks only when it lies in the claim's cone ([`specification/README.md#rg1011-replaced-compiled-code`](specification/README.md#rg1011-replaced-compiled-code)). Under the full gate, RG1010 refuses `@[csimp]`, which is not in `Regula.Language.simpleAttributes` ([`lean/Regula/LanguageSet.lean`](lean/Regula/LanguageSet.lean)).

### Examples in Regula

- **Non-vacuity harness ([`specification/RegulaSpecification/RuleRecord.lean`](specification/RegulaSpecification/RuleRecord.lean)):** `ruleRecord` states that a rule reports a subject iff its violation predicate holds. `Witnessed` supplies a well-formed refused case and a well-formed admitted case, from which `silent_fails`, `noisy_fails`, and `adequate` discharge non-vacuity and uniqueness up to `SameReports`.
- **Independent rule spec and bidirectional proof ([`lean/Regula/Rules/RG1011.lean`](lean/Regula/Rules/RG1011.lean), [`specification/RegulaSpecification/Rules/RG1011.lean`](specification/RegulaSpecification/Rules/RG1011.lean)):** `Violates1011` (with `Replaced` and `Initialized`) states RG1011 independently of `Regula.Rules.RG1011.check`; `Witnesses.w1011`, `rg1011_adequate`, and `rg1011_noisy` prove non-vacuity; `Link.rg1011_exact` proves bidirectional equivalence over the executed `check` function; and `rg1011_admits_neither` and `rg1011_checker_reads_definitions` prove boundary behavior.
- **Modular rule registry ([`lean/Regula/Rules.lean`](lean/Regula/Rules.lean), [`specification/RegulaSpecification/Rules.lean`](specification/RegulaSpecification/Rules.lean)):** Each rule lives in an isolated module pair (check below [`lean/Regula/Rules/`](lean/Regula/Rules/), specification and proofs below [`specification/RegulaSpecification/Rules/`](specification/RegulaSpecification/Rules/)); of the two packages, each rule imports only its shared core (`Regula.Rule` / `RegulaSpecification.Rule`) and its own check, and no rule imports another rule. `Regula.Closed.registry` with `spellings_nodup` and `report_pass_iff` proves once that a run passes iff no registered rule reports a subject; `registry_rules` proves the specification registry equal to the checker's, linking directly to `AllHold` (`findings_nil_iff`, `report_complete`).

**Enforcement status:** `@[implemented_by]`, `@[extern]`, and `@[init]`/`@[builtin_init]` on claimed definitions are refused by **RG1011** (on `main`; not in `v0.13.0`). Spec-first development, non-vacuity proofs, proof economy, and reading theorem statements remain engineering discipline.

## 3. Certifying algorithms, total search, pure effects, and module boundaries

Structure algorithms, proof automation, side effects, and module interfaces so the trusted and proof-heavy surfaces stay small.

- **Use certifying algorithms when checking is simpler than finding:** When proving a complex search, solver, or optimizer directly is harder than verifying its output, split it into a witness producer and a small, total, formally proved checker (`check x w = true → Spec x w`). Only the checker needs a correctness proof.
- **Use total exhaustive search for universal negative properties:** A single positive witness cannot prove the absence of violations (such as proving no constant in a build reaches a disallowed axiom). Implement those checks as total functions over closed finite domains using structural recursion or a derived termination measure—never `partial`, `while`, or an arbitrary fuel guess—and prove both soundness and completeness.
- **Use kernel-checked automation instead of native evaluation:** Rely on tactics that produce kernel-checked proof terms (`simp`, `omega`, `decide +kernel`, structural induction). Avoid `native_decide`, `decide +native`, and `bv_decide`, which add axioms trusting the compiler rather than Lean's kernel.
- **Separate pure effect programs from thin IO interpreters:** Represent effectful workflows as pure trees over a closed set of operations with explicit error responses (`Except`), rather than mixing decision logic directly into `IO`. Prove behavioral properties of the pure program across all possible responses—including failures and external mutations—keep the runtime interpreter a straight-line dispatch table with no branching, and record every reliance on Lean, Lake, or the OS in one exhaustive list.
- **Keep module boundaries explicit with `module` files:** Start every Lean file with `module` so callers depend only on `public` declarations and explicitly exposed bodies (`@[expose]`, `abbrev`, or instances). Keep implementation bodies unexposed in library modules; when a separate proof package must unfold unexposed bodies, use `import all` in the proof package rather than widening the library's public surface.

### Examples in Regula

- **Total reachability with a derived termination measure ([`lean/Regula/Reach.lean`](lean/Regula/Reach.lean), [`lean/Regula/Tables.lean`](lean/Regula/Tables.lean)):** `reach` and `reachGo` traverse finite name graphs without `partial` or `while`. Fuel is derived from the graph's total out-degree rather than guessed: `unseenWeight_insert` proves that inserting an unseen node `n` drops `unseenWeight` by at least `(next n).length` (so `work.length + unseenWeight` decreases by at least one on each step in `reachGo_closed`), and `mem_reach` proves soundness and completeness against the inductive `Reach` relation. `Tables.lean` uses `reach` for backwards axiom reachability (`Input.axiomReach`, `mem_axiomReach`, `Tables.mem_axiomSet`) and forward kernel-replay cone construction (`Input.cone`).
- **Pure effect tree and straight-line interpreter ([`lean/Regula/Effect.lean`](lean/Regula/Effect.lean), [`lean/Regula/Table.lean`](lean/Regula/Table.lean), [`specification/RegulaSpecification/Proofs/Program.lean`](specification/RegulaSpecification/Proofs/Program.lean)):** `Regula.Effect.Op` lists the closed set of external operations, `Resp` types each response (representing failures as `Except` values), `Prog` builds pure decision trees, and `Prog.interpret` executes them in `BaseIO` through `Regula.Effect.table` and `LakeCalls`. `table_rows` proves each table entry is a straight-line call with no branching, `executed_meets` links `Prog.interpret` to the trace specification, and [`specification/RegulaSpecification/Assumptions.lean`](specification/RegulaSpecification/Assumptions.lean) maps every `Op` constructor exhaustively to named assumptions (`Assumption.ofOp`, `readAt_pinned`).
- **Explicit `module` boundaries ([`specification/README.md#module-files`](specification/README.md#module-files)):** Every Lean file in `lean/Regula/` and `specification/` starts with `module`. Root modules keep rule `check` bodies unexposed and apply `@[expose]` only where callers or registry proofs need definitional unfolding (such as `Regula.Effect.Resp`, each rule's `rule`, `Report.verdict`, and `Report.findings`), while the specification package unfolds checker bodies through `import all`.

**Enforcement status:** Native-proof axioms are refused by **RG1004** (and by **RG1010** under the full gate); `unsafe`, `partial`, and `while`/`repeat` loops are refused by **RG1006**; non-`module` claimed files are refused by **RG1013** (on `main`; not in `v0.13.0`, and by **RG1010** under the full gate). Certifying-algorithm factoring, termination-measure design, and pure-effect architecture remain engineering discipline.

## 4. Closing the compile-time erasure, `Prop`-vs.-`Type`, and runtime gap

A green `lake build` does not by itself establish that proofs are complete, sound within an intended axiom profile, or faithful to compiled execution.

### `Prop` erasure vs. `Type`-level computational witnesses

- **`Prop` terms erase at compile time:** Proofs add zero runtime overhead, and Lean's compiler generates no executable code for `theorem` declarations.
- **Carry runtime data in `Type`, invariants in `Prop`:** A `Subtype` value `{ y : β // P x y }` lives in `Type`: its payload `y` survives compilation while `P x y` is erased. An existential proposition `∃ y, P x y` lives in `Prop`: extracting `y` into `Type` requires classical choice (`Classical.choose`), making the definition `noncomputable` so Lean generates no code for it.
- **Keep executable surfaces computable and state foundation strength accurately:** Keep `noncomputable` definitions confined to specification and proof surfaces. Report exact axiom foundations (`kernel-only`: no axioms; `choice-free`: `propext` and `Quot.sound`; `standard-logical`: `propext`, `Quot.sound`, and `Classical.choice`) without treating foundation strength as a general ranking of software assurance.

### Failure classes and the Regula checks that close them

Each failure class below can slip past a plain `lake build` (or invalidate what a build establishes) unless closed by Lean flags and Regula's proved checks. All rules RG1001–RG1006 and RG1011–RG1013 are proved exact over the closed input (`rg1001_exact`–`rg1006_exact`, `rg1011_exact`–`rg1013_exact`) and linked to the loaded Lean environment (`pass_iff`, `pass_held` in [`specification/RegulaSpecification/Proofs/Load.lean`](specification/RegulaSpecification/Proofs/Load.lean)):

- **Proof holes (`sorry`):** A plain `lake build` only warns on `sorry`. Pair `lake build --wfail` with **RG1002** (`v0.13.0` and `main`), which refuses any claimed constant depending on `sorryAx` directly or through an import.
- **Project and unknown axioms:** `lake check` ignores unused axioms. **RG1001** (`v0.13.0` and `main`) refuses any `axiom` declared in a claimed module even if unused; **RG1003** (`v0.13.0` and `main`) refuses transitive dependence on any unknown axiom outside Lean's `propext`, `Quot.sound`, and `Classical.choice` not named by RG1002 or RG1004.
- **Compiler-trusted proofs (`native_decide`, `decide +native`, `bv_decide`):** **RG1004** (`v0.13.0` and `main`) refuses transitive dependence on native-proof axioms (`<declaration>._native.<tactic>.<suffix>`) and compiler-trust axioms (none declared in `v4.35.0`).
- **Axiom-profile creep:** **RG1005** (`v0.13.0` and `main`) refuses any claimed constant depending on an axiom outside the project's declared profile (`kernel-only`, `choice-free`, or `standard-logical`). Every axiom caught by RG1002, RG1003, or RG1004 also violates RG1005.
- **Bypassed kernel checks and malformed builds (RG2001):** `debug.skipKernelTC` can accept an unsound theorem during `lake build`. Before giving a pass (`v0.13.0` and `main`), the checker replays every claimed constant, its transitive dependency cone, differing claimed-module copies of merged theorems under fresh names, and the constants Lean's kernel builds into a term (`Input.kernelNames`) into an empty kernel environment via `Kernel.Environment.replay`; a failed replay, an unreadable build, an empty claim, an open mention, an unshown constant that fails the loader's checks, a wrong toolchain, or (in the full gate) a case of [the closed list of refusals](specification/README.md#the-closed-list-of-refusals) with exit 2 produces `incomplete` (RG2001, exit 2).
- **Non-termination and unsafe escapes:** **RG1006** (`v0.13.0` and `main`) refuses claimed constants that are `unsafe`, `partial`, or named as a recursion helper (`b._unsafe_rec` via `Lean.Compiler.isUnsafeRecName?`) without the exempted form (a `partial` helper with neither `@[implemented_by]` nor `@[extern]` beside a safe total definition in the same module with neither), or whose value directly mentions `Lean.Loop.mk` or `repeatM` (`while`, `repeat`, `repeat ... until`). *Limits:* `termination_by`, `partial_fixpoint`, `for` over a list, loops inside dependencies or the toolchain (such as `IO.iterate`), and mentions only in types are not refused by RG1006; under the proof verdict, project build-time code could synthesize a constant of the exempted form (closed by RG1010 under the full gate).
- **Unproved replacement of compiled code:** **RG1011** (`main`; in no release yet) refuses any claimed constant with `@[implemented_by]` or `@[extern]`, and any claimed *definition* for which `@[init]` or `@[builtin_init]` names an initialization function, checking both the merged environment and each claimed module's own attribute entries. *Limits:* `opaque` constants with an initialization function (`initialize x : T ← act`) are admitted because Lean's logic states nothing of their value; startup hooks (`@[init]`/`@[builtin_init]` naming no function) are not read; `@[csimp]` is admitted under RG1011 with the cone-replay caveat above (and refused by RG1010 under the full gate); calls into dependency or toolchain constants with those attributes pass.
- **Hidden runtime panics:** In Lean's logic `panicCore` equals `default`, and at runtime it prints a message and returns `default` unless `LEAN_ABORT_ON_PANIC` is set or the program asked to exit on a panic—letting a proved function continue with a value its proofs never considered. **RG1012** (`main`; in no release yet) refuses any claimed definition or opaque constant whose value directly mentions Lean's four panic functions (`panicCore`, `panic`, `panicWithPos`, `panicWithPosWithDecl`) or any non-theorem constant whose macro-erased last string component contains `!` (covering `xs[i]!`, `Option.get!`, `List.head!`, `String.toNat!`, `Array.back!`, `Array.set!`, `panic!`, `unreachable!`, and `assert!`). *Limits:* `xs[i]?`, `dbg_trace`, and theorems are not refused; panics inside dependencies or the toolchain reached through constants without `!` (such as `outOfBounds`), C panics behind `@[extern]` without `!`, and mentions only in types stay outside RG1012.
- **Unencapsulated non-`module` files:** **RG1013** (`main`; in no release yet) refuses any claimed module whose `.olean` does not record it as a `module` file. It adds nothing to what a proof depends on. *Limits:* RG1013 reports claimed modules only; Lean itself refuses a `module` file that imports a non-`module` file, so dependencies imported by claimed modules must also be `module` files (all files of Mathlib at tag `v4.35.0` were measured as `module` files).
- **Build-time code execution and metaprogramming escapes:** Under the proof verdict, `lake build` and `lake lint` run in the project's Lake and execute project and dependency build-time code. **RG1010** (`v0.13.0` and `main`, full verdict only) reads `lean-toolchain`, `lakefile.toml`, and every reached Lean source file *before* anything compiles, admitting only a closed language subset (`lean/Regula/LanguageSet.lean`) and refusing `run_cmd`, `#eval`, `#guard`, `run_tac`, `by_elab`, `native_decide`, `decide +native`, `macro`, `syntax`, `notation`, `elab`, `initialize`, `lakefile.lean`, plugins, and any unlisted construct (`decision_admitted_iff`, `build_only_after_check`). Applies only to standalone library projects with no `require` and no Mathlib imports, under hypotheses H1–H5 and the [trusted base](specification/README.md#the-trusted-base) at Lean `v4.35.0`.

## Enforcement status

Each item in this standard falls into one of four categories: enforced in `v0.13.0` and `main`, enforced on `main` (in no release yet), planned, or manual engineering discipline.

| Practice or requirement | Status | Check or mechanism | Scope and limits |
| --- | --- | --- | --- |
| No declared project axioms | Enforced (`v0.13.0` & `main`) | RG1001 | Claimed modules, including unused axioms. |
| No `sorry` / `sorryAx` dependencies | Enforced (`v0.13.0` & `main`) | RG1002 + `lake build --wfail` | Direct or transitive through imports. |
| No unknown axioms | Enforced (`v0.13.0` & `main`) | RG1003 | Outside toolchain `propext`, `Quot.sound`, `Classical.choice`, RG1002, RG1004. |
| No native-proof or compiler-trust axioms | Enforced (`v0.13.0` & `main`) | RG1004 (and RG1010 in full gate) | Catches `native_decide`, `decide +native`, `bv_decide`. |
| Axioms restricted to declared profile | Enforced (`v0.13.0` & `main`) | RG1005 | `kernel-only`, `choice-free`, or `standard-logical`. |
| No `unsafe`, `partial`, forged `._unsafe_rec`, or `while`/`repeat` | Enforced (`v0.13.0` & `main`) | RG1006 | Exempted recursion-helper form, `partial_fixpoint`, and dependency loops stay outside RG1006. |
| Pre-build closed language subset (no build-time code) | Enforced (`v0.13.0` & `main`) | RG1010 (full verdict only) | Standalone library projects with no `require` and no Mathlib; under H1–H5 and trusted base. |
| Kernel cone replay and closed-form build loading | Enforced (`v0.13.0` & `main`) | RG2001 | Exits 2 (`incomplete`) on failed replay, missing claim, open mention, or unread/wrong build. |
| No `@[implemented_by]`, `@[extern]`, or `@[init]`/`@[builtin_init]` on claimed `def`s | Enforced on `main` (unreleased) | RG1011 | `initialize` (`opaque`) and `@[csimp]` pass RG1011 (see cone caveat; RG1010 refuses both in full gate). Dependency/toolchain constants pass. |
| No direct panic forms in claimed `def` / `opaque` values | Enforced on `main` (unreleased) | RG1012 | Theorems, `xs[i]?`, `dbg_trace`, and non-`!`-named dependency panics stay outside RG1012. |
| Claimed files are `module` files | Enforced on `main` (unreleased) | RG1013 (and RG1010 in full gate) | Claimed modules only; Lean refuses `module` files importing non-`module` dependencies. |
| Actionable fix guidance in diagnostics | Planned | None yet | Ships only once specified and proved under Regula's proof and simplicity bar. |
| Additional design, refactoring, and architecture checks | Planned | None yet | Same specification, proof, and simplicity admission bar. |
| Theorem statements match human intent | Engineering discipline | Human review | No checker can validate unformalized intent. |
| Intrinsic typing at boundaries (`Fin`, `Subtype`, closed sums) | Engineering discipline | Code review | Exemplars: `Input.lean`, `Tables.lean`, `Rule.lean`. |
| Spec-first workflow, non-vacuity, proving executed definitions, proof economy | Engineering discipline | Code and proof review | Exemplars: `RuleRecord.lean`, `Rules/RG1011.lean`. |
| Certifying algorithms vs. total search with derived termination | Engineering discipline | Code and proof review | Exemplar: `Reach.lean`. |
| Pure effect trees, thin IO tables, exhaustive assumption lists | Engineering discipline | Code and proof review | Exemplars: `Effect.lean`, `Table.lean`, `Assumptions.lean`. |
| `Prop`-vs.-`Type` witnesses and computable executable surfaces | Engineering discipline | Code review | Keep `noncomputable` off executable surfaces; report exact axiom profiles. |
| Auditing dependencies, toolchain code, and out-of-cone `@[csimp]` | Engineering discipline | Manual audit | Outside Regula's proof-verdict and full-verdict contracts. |

## Applying this standard with coding agents

When using coding agents on a Lean 4 codebase:

1. **Start files with `module` and keep interfaces narrow:** Export only the types, statements, and `@[expose]` bodies callers need; keep implementation bodies unexposed.
2. **Validate at boundaries into proof-bearing types:** Replace repeated guards and `!` operations with `Fin`, `Subtype`, closed sum types, or explicit `Option`/`Except` results.
3. **Write specs before code and watch proof complexity:** Prove non-vacuity and prove the actual executed definition; when a proof grows much harder than the code, simplify the code or factor out a small proved checker.
4. **Run Regula on the pinned toolchain (`leanprover/lean4:v4.35.0`):** Use `lake build --wfail` and `lake lint` for the proof verdict, or the standalone full gate for standalone library projects ([`README.md#use-it`](README.md#use-it), [`README.md#the-full-gate`](README.md#the-full-gate)).
5. **Read every claimed theorem statement by hand:** Regula's verdicts hold only for [the named configurations](specification/README.md#the-named-configurations) under [the trusted base](specification/README.md#the-trusted-base), and no pass checks that a theorem states what you meant.

For rules that govern changes to Regula itself, see [`CONTRIBUTING.md`](CONTRIBUTING.md).
