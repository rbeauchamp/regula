# Specification of Regula

Regula exists to be trusted, and to be the example of how Lean 4 code should be written: well factored, well designed, following best practice, and formally proven. Its owner decided on 2026-10-31 that being free of bugs outranks every lint rule and feature, so Regula gives up any rule, feature or package it cannot prove rather than patching it, documenting a limit or keeping a stated gap. Only Lean, its kernel and Lake's own behaviour are meant to stay trusted; Regula's own code is meant to be proved, or so thin that it only calls Lean. That is the aim and not a claim about this revision: [the trusted base](#the-trusted-base) lists what is not yet proved.

This document states what Regula's checks are, what each is proved to do, and what stays assumed. It is the first step of the order that the owner chose: first a small proved core, then a check that reads each source file and refuses anything outside a fixed set of allowed constructs. That check does not exist yet. [The confirmation record](confirmation.md) holds the owner's words.

## How to read this document

Each claim about Lean, Lake or the theorems of this package has one of four marks:

- **Proved**: Lean checks a theorem of the Lean package in this directory. The theorem name follows the mark.
- **Measured**: an observation on the pinned toolchain, with its procedure.
- **Assumed**: a statement about Lean, Lake or the operating system that no proof here examines.
- **Open**: an obligation that this document does not discharge.

A statement of what a rule or the checker must do is specification, and it has no mark. A citation such as `Lean/Meta/Native.lean:45` is a path below `src/` of the tag `v4.35.0` of Lean, the toolchain that `lean-toolchain` pins, and one that starts with `Lake/` is a path below `src/lake/` of that tag. To check all statements and theorems, run `lake build --wfail` in this directory. The Lean library `RegulaSpecification` requires lean-intent at the commit that `lakefile.toml` names, and the root package.

## What the owner's intent requires

Each row is a requirement of the owner's confirmed intent, and the formal claim that carries it.

| Requirement | Formal claim |
| --- | --- |
| Regula's checks are exactly RG1001 to RG1006 and RG2001. | **Proved**: `rule_spellings`, and `Regula.RuleId.mem_all` for each constructor of the closed type. |
| It refuses a project whose declarations depend on `sorry`. | **Proved**: `rg1002_exact`, `rg1002_cases`. |
| It refuses a project axiom. | **Proved**: `rg1001_exact`, `rg1001_cases`, and `rg1003_exact` for its use. |
| It refuses `native_decide`. | **Proved**: `rg1004_exact`, `rg1004_cases`. |
| It refuses an axiom outside the allowed profile. | **Proved**: `rg1005_exact`, `rg1005_cases`. |
| It refuses an `unsafe` or `partial` declaration other than Lean's recursion helper. | **Proved**: `rg1006_exact`, `rg1006_cases`, against the helper's form (see [RG1006](#rg1006-unsafe-and-partial-declarations)). |
| It refuses an input it cannot load. | **Proved**: `refusal_none_iff`, `run_refused`, for the input, and `decision_failed`, `decision_pass` for a failed load. |
| Each rule refuses every violation and only violations, over Regula's input. | **Proved**: each `rgN_exact` is an equivalence, and `rgN_meets` states it as the rule's intent record. |
| It refuses a claimed constant whose value directly mentions `Lean.Loop.mk` or `repeatM`, so `while` and `repeat` in claimed code. | **Proved**: `rg1006_exact`, `rg1006_checker_refuses_loop`. |
| A checker that refuses nothing does not satisfy this. | **Proved**: `silent_fails`, `noisy_fails` and each `rgN_noisy`; `always_pass_fails`, `always_incomplete_fails`. |
| A pass is the verdict of the rules. | **Proved**: `run_complete`, `run_pass_iff`, `run_meets`. |
| A pass is a statement about the environment that Lean loaded, not only about the input. | **Proved**: `pass_iff`, `pass_floor`, `pass_held`, see [from a build to the input](#from-a-build-to-the-input). |

The rest of this document follows from those requirements, or is marked as decided on the owner's behalf.

## The shape of a rule

Each rule is a pure function from the closed input to the constants that it reports. Its formal statement is a lean-intent intent record (`LeanIntent.IntentRecord`), built by `ruleRecord` in [`RegulaSpecification/RuleRecord.lean`](RegulaSpecification/RuleRecord.lean). The record has one property: on each well-formed input, the function reports a subject exactly when the subject violates the rule. Thus the meaning of a rule is all in its violation predicate, for example `Violates1005`.

For each rule, the package gives a case that the rule must refuse and a case that it must admit (`Witnessed`). From them, it proves that the record meets lean-intent's obligations O2 (at confirmation and before a run), O3, O4, and O5 with the freedom `SameReports`, which is the order and the repetition of the reported subjects, and the result on an input that the admission refuses. **Proved**: `adequate`, applied in `rg1001_adequate` and the theorems that follow it. O1 holds for each record. **Proved** by lean-intent: `LeanIntent.o1_wellTyped`.

Each rule function that the checker runs is proved against its record in [`RegulaSpecification/Proofs/`](RegulaSpecification/Proofs/). The functions run over `Regula.Closed.Input`, so the proofs are about the executed definitions, not about a copy of them.

These theorems assume one thing of an input where a rule needs it: it has the closed form (`Input.WellFormed`). A rule computes an axiom set from the input itself, by a search backwards from each axiom through the constants that each constant mentions (`Tables.axiomSet`), and that set is exactly what `Input.AxiomOf` states, with no hypothesis (**proved**: `axiomSet_iff`, with `mem_reach`). The checker no longer calls `Lean.collectAxioms`, so nothing about that function is assumed.

## The closed input

The closed input is the type `Input` in [`RegulaSpecification/Input.lean`](RegulaSpecification/Input.lean):

| Field | Owner and interface |
| --- | --- |
| `profile`, the profile that the project states | The one argument of the lint driver, `lintDriverArgs` of the project's Lake configuration |
| `modules`, the claimed modules | Lake's load gives the modules of the default targets of the root package; each loaded module whose `.olean` lies in the root package's library directory is claimed |
| `decls`, each constant of the environment | `Lean.importModules` with `loadExts := false` |
| `loads`, the modules that the environment imports | The header of that environment |

The input has no source text, message, compiled code, option or build log. A rule does not decide what it cannot read in this input.

The admission refuses an input that does not have the closed form (`Input.WellFormed`). Each name is the name of one constant. Each constant that a constant mentions is held. At least one module is claimed, so a claim of nothing is not read as a pass (**proved**: `no_claim_refused`). Each claimed module is loaded (**proved**: `unloaded_refused`). **Proved**: `refusal_none_iff`.

The shell has three effects: it loads the build, it prints its report, and it sets its exit code. It writes no file. It runs no initializer of the loaded modules, because it loads them without extension states. Lake's own load of the workspace runs Git in the environment of the caller. This is read from the code, and no theorem states these effects.

## From a build to the input

`Regula.Load.Facts.input` is the pure function that fills the input from an environment, and [`RegulaSpecification/Proofs/Load.lean`](RegulaSpecification/Proofs/Load.lean) states what it gives. So a later change to the loader that drops a constant, a field or a mention fails the gate's build of this package.

- **Proved**: `pass_iff`. For every environment, every `Facts` and every profile, when the loader gives an input, the checker passes on it exactly when the environment has `EnvForm` and `EnvFloor`. These two statements name no field of the input. `EnvForm` is the closed form. `EnvFloor` states RG1001 to RG1006 of each constant of `Environment.constants.map₁` in a claimed module, and each mention is read from the fields of its `ConstantInfo` (`Mentions`, `mem_usesOf`).
- **Proved**: `pass_floor`, the same on the path that the shell decides (`Regula.Shell.decision`). A pass also states that each module of a default target is claimed and that each constant of the environment has a module.
- **Proved**: `pass_held`. A pass holds of each constant of a claimed module as that module's own `.olean` states it, also when Lean's import replaced it (below).
- **Proved**: `decision_pass`, `decision_failed`, `profileOfRun_ok` and `profileOf_eq_some`, for the shell's pure decisions. `mem_claimed_ofPlaces`, `toolchain_ofPlaces` and `below_iff`, for what the places of the modules decide. `dispatchedFrom_iff`, for the workspace that Lake dispatched.

Each field of the input, with the rules that read it, its statement against the environment, and what that leaves about Lean or Lake:

| Field | Read by | Statement | Left assumed |
| --- | --- | --- | --- |
| `profile` | RG1005 | `Loaded.profile`, `profileOfRun_ok`, `profileOf_eq_some` | Lake passes `lintDriverArgs` as the arguments |
| `modules` | each rule, the admission | `Loaded.modules`, `Loaded.roots`, `mem_claimed_ofPlaces`, `below_iff` | Lake names the modules of the default targets and the root package's library directory; `findOLean` finds each `.olean` on Lake's search path |
| `decls`, and each `name` | each rule, the admission | `Loaded.sound`, `Loaded.whole`, `Loaded.unique` | `map₁` holds the constants that the import keeps |
| `module` | each rule | `Loaded.sound`, through `Facts.moduleOf` | `getModuleIdxFor?` and `header.moduleNames` name a module that holds the constant |
| `kind` | RG1001, RG1002 to RG1005, RG1006 | `kind_axiom`, `kind_definition`, `isAxiom_env` | the `ConstantInfo` that the `.olean` holds |
| `isUnsafe`, `isPartial` | RG1006 | `pass_iff`, through `EnvFloor` | as for `kind` |
| `uses` | RG1002 to RG1005, the admission | `mem_usesOf`, `reaches_env` | `Expr.getUsedConstants` lists each constant of an expression |
| `valueUses` | RG1006 | `mem_valueUsesOf` | as for `uses` |
| `implementedBy`, `isExtern` | RG1006 | `helper_env` | `getImplementedBy?` and `isExtern` read the module entries under `loadExts := false` |
| `inToolchain` | RG1003, RG1005 | `known_env`, `toolchain_ofPlaces`, `below_iff` | Lean finds the toolchain's library only below its `lib/lean` directory |
| `loads` | the admission | `Loaded.loads` | the header lists the loaded modules |

No field is left for removal: each has a statement against the environment, and what remains assumed is Lean's or Lake's behaviour.

**The constants that Lean's import replaces.** Lean refuses two imported modules that declare one name with different values, with one exception. It merges two theorems of one name and type, a theorem with an axiom of that name and type, and two such axioms, and it keeps one constant under the name of the first module that holds it (`subsumesInfo` and `finalizeImport`, `Lean/Environment.lean:2269` and `2336-2345`). So a claimed module can hold a constant that no rule reads. **Measured** on 2026-10-31 at the previous revision, on a project of `kernel-only`: a module whose theorem `shared` used `Classical.choice`, beside a module whose theorem `shared` had the same type and a proof with no axiom, passed `lake build --wfail`, `lake check` and `lake lint`. Lean regenerates a definition's equation lemmas in each module that needs them, so refusing each such constant would refuse ordinary projects (**measured**: `f.eq_def` in two modules). So the loader reads each claimed module's own constants from the header of the environment (`Facts.claimedConstants`). A constant that the environment does not show to the rules must be a theorem, with neither flag, whose value mentions no loop construct, and whose mentions reach only axioms that the profile admits, or the run is `incomplete` (`Facts.unread?`). **Measured** on 2026-10-31 at this revision: the project above gives `incomplete` or `fail` by the order of its imports, and passes under `standard-logical`, and the two modules with `f.eq_def` pass.

## The rules

### RG1001 to RG1005: the foundation profile

Each reads a constant of a claimed module. RG1002 to RG1005 read its transitive axiom set `Input.AxiomOf`, which the rules compute from the input (`axiomSet_iff`). The four refine one refusal: each axiom that RG1002, RG1003 or RG1004 names also violates RG1005 for each profile. Thus a wrong choice between these rules changes the rule of a finding, but not the verdict. **Proved**: `rg1005_of_hole`, `rg1005_of_unknown` and `rg1005_of_compiler`. The formal statements are in [`RegulaSpecification/Foundation.lean`](RegulaSpecification/Foundation.lean).

- **RG1001: project axioms.** A constant of a claimed module has the kind `axiom`. An assumption is a hypothesis or a field of a structure, so that each theorem that uses it shows it in its type. `lake check` refuses an axiom only when a constant mentions it, so it does not do the work of this rule. `Violates1001`.
- **RG1002: proof holes.** A constant depends on `sorryAx`, directly or through an import. `Violates1002`.
- **RG1003: unknown axioms.** A constant depends on an axiom other than `propext`, `Quot.sound` and `Classical.choice` of the toolchain, and RG1002 and RG1004 do not name it. `Violates1003`, with `Input.Known`. **Assumed**: Lean finds the library of the toolchain only below the `lib/lean` directory of the pinned toolchain, which the shell reads to say that a module is in that library.
- **RG1004: native proofs.** A constant depends on an axiom with the name form `<declaration>._native.<tactic>.<suffix>` that `native_decide`, `decide +native` and `bv_decide` add (`Lean/Meta/Native.lean:45` and `75-82`), or on an axiom by which the kernel trusts the compiler, of which `v4.35.0` declares none. `Violates1004`, with `NativeProofAxiom` and `compilerAxioms`. **Measured**: `native_decide` gave `n._native.native_decide.ax_1_1`. The rule identifies the axiom by its name, so an author can give an axiom that name. Then RG1004 reports it in place of RG1003, and the verdict is the same.
- **RG1005: the profile.** A constant depends on an axiom that the project's profile does not admit. Kernel-only admits no axiom. Choice-free admits `propext` and `Quot.sound`. Standard-logical also admits `Classical.choice`. Each admitted axiom is the toolchain's own. `Violates1005`, with `Input.Admits`.

### RG1006: `unsafe` and `partial` declarations

The rule refuses two things in a claimed module: an `unsafe` or `partial` constant without the form of Lean's recursion helper, and a constant whose value directly mentions a loop construct of Lean. `Violates1006`, with `Input.RecursionHelper` and `MentionsLoop`, in [`RegulaSpecification/Safety.lean`](RegulaSpecification/Safety.lean). **Proved**: `rg1006_exact` in both directions, and `rg1006_checker_refuses_loop` for each construct.

**The loop constructs.** The class comes from Lean's `Init/While.lean`. A `while`, `repeat` or `repeat ... until` needs no `partial` of the module that uses it, because it compiles through `Lean.Loop.forIn` to `repeatM`, whose body is a private `partial` of that file. So the flags alone do not show a loop that does not end. The rule reads the value of each claimed constant for the one value of the type `Lean.Loop`, `Lean.Loop.mk`, and for `repeatM` (`loopConstructs`). `termination_by` and `partial_fixpoint` stay allowed, and so does `for` over a list. The owner's delegated agent added this on 2026-10-31, after `while true` passed all three commands while a `partial def` of the same loop failed.

**Measured** on 2026-10-31 on a disposable project: `while`, `repeat`, `repeat ... until`, a direct `repeatM`, a direct `Lean.Loop.forIn ⟨⟩`, `forIn Lean.Loop.mk` and an `Inhabited Lean.Loop` instance were each refused; `termination_by`, `partial_fixpoint` and `for` over a list passed.

What this leaves out, as accepted risk under the owner's trust in dependencies:

- A loop inside a dependency or the toolchain, such as `IO.iterate` (`Init/System/IO.lean:780`), which is a `partial def` that a claimed constant can call. **Measured**: it passes.
- A claimed function that takes a value of `Lean.Loop` as an argument mentions neither construct, and it passes (**measured**). Running it needs that value, which claimed code can make only through `Lean.Loop.mk`, so only a dependency's value runs it.
- A mention only in a constant's type, which runs nothing. **Proved**: `rg1006_admits_type_mention`.
- A loop that a claimed module's own code adds during the build, with the forged helper below.

**The recursion helper.** The form is a partial constant `f._unsafe_rec`, not unsafe, with no `implemented_by` and no `extern`, in the module of a safe, total definition `f` with neither. Lean makes the base of a `partial def` an opaque constant, so the rule reports the helper of a `partial def`.

The rule checks that form and nothing about what the helper computes. **Known gap**: a claimed module can forge a helper through its own code during the build. The compiler reads `f._unsafe_rec` in place of `f` by name (`getDeclInfo?`, `Lean/Compiler/LCNF/ToDecl.lean:25-27`). **Measured** on 2026-10-31 with this revision of the checker, on a project of one module:

```lean
import Lean
open Lean Elab Command
run_cmd liftCoreM do
  let ty := mkForall `n .default (mkConst ``Nat) (mkConst ``Nat)
  let val := mkLambda `n .default (mkConst ``Nat) (mkApp (mkConst ``Nat.succ) (mkBVar 0))
  addDecl (.defnDecl { name := `g._unsafe_rec, levelParams := [], type := ty, value := val,
                       hints := .opaque, safety := .partial, all := [`g._unsafe_rec] })
def g (n : Nat) : Nat := n
theorem g_one : g 1 = 1 := rfl
#eval g 1
```

The `#eval` printed `2` while `g_one` holds, and `lake check` and `lake lint` both passed. The gap is about what a compiled program runs, not about a proof: a helper is not logical evidence, because Lean's kernel refuses a safe constant that mentions a partial one (`src/kernel/type_checker.cpp:114-117` at `v4.35.0`). The check that the owner chose as the next step is what can close it.

### RG2001: the environment

A run that cannot load the build gives `incomplete`. So does an input that the admission refuses, a constant of a claimed module that the loader refuses (`Facts.unread?`), any argument list other than one profile, and any Lean other than the one this revision reads (`Regula.Shell.supportsLean`). `gateRecord` in [`RegulaSpecification/Gate.lean`](RegulaSpecification/Gate.lean) states the verdict. **Proved**: `gate_o5`, so the record leaves nothing unsaid about the verdict, and `gate_adequate`.

**Proved** of `Regula.Closed.run`, the function that the checker runs, in [`RegulaSpecification/Proofs/Verdict.lean`](RegulaSpecification/Proofs/Verdict.lean):

- `refusal_none_iff`: its admission refuses exactly an input without `Input.WellFormed`.
- `run_refused`: a refused input is `incomplete`.
- `run_complete`: an admitted input is not `incomplete`, and it is `pass` exactly when every rule holds of it.
- `run_meets`: the verdict meets `gateRecord`, with `none` for a build that the shell cannot load.

The exit code of `pass` is 0, and no other verdict has it (**proved**: `Regula.Closed.Verdict.exitCode_eq_zero_iff`). `fail` is 1 and `incomplete` is 2. A process that dies ends with a code of its own, which no theorem relates to a verdict, so only exit 0 reads as a pass.

**Measured** on 2026-10-31 on a disposable project that requires this revision. Each case ran `lake build` and then `lake lint`: a `sorry` and a theorem that uses it (RG1002 and RG1005 on each, exit 1); an unused axiom (RG1001, RG1003, RG1005, exit 1); `native_decide` (RG1001, RG1004, RG1005, exit 1); a `partial def` and a `while` (RG1006, exit 1); an `unsafe def` (RG1003, RG1005, RG1006, exit 1); `Classical.em` under `choice-free` (RG1005, exit 1); `propext` under `kernel-only` (RG1005, exit 1); no profile or a wrong profile (exit 2); no default target (exit 2); no build (exit 2); a run from another directory than the workspace (exit 2); a non-default module with a `sorry` that a default module imports (RG1002, RG1005, exit 1); and a compliant module with a structural recursive definition (exit 0).

## What a pass means

A pass of the project's gate is the result of three commands of the pinned toolchain on one finished build, in this order:

1. `lake build --wfail`.
2. `lake check`. On macOS it is `lake check --inadvisably-no-sandbox`, and it prints that the run is not trustworthy.
3. `lake lint`, Regula's checker.

The first two are Lean's own, and Regula makes no claim of its own about what they decide. **Assumed** from the source: `lake check` builds the default targets, exports them and replays the export with `leanchecker` in a process that loads no `.olean` file of the project (`Lake/CLI/Main.lean:1218-1226`, `Lake/CLI/Check.lean`), and it refuses each axiom other than the three that a constant of the export mentions (`Lake/CLI/Check.lean:662-675`, `Lake/Check/Axioms.lean:57-71`).

Such a pass means that the proofs of the claimed modules are sound and use only axioms that the profile allows. It says nothing about what a compiled program runs. Code of a claimed module can change that with `@[implemented_by]`, `@[extern]`, `@[csimp]` or a forged helper, and no rule reads it. **Measured** on 2026-10-31: a module with each of the first three passed all three commands.

The checker alone means less, because it reads what the build holds and replays nothing. **Measured** on 2026-10-31: a module that added a theorem of `False` with `set_option debug.skipKernelTC true` passed `lake build` and `lake lint`, and `lake check` refused it.

`lake check` imports the modules of the default targets into one environment, and the checker does too. So a project of two default executables that each declare `main` fails both commands. Lean refuses two imported modules that declare one name with different values (`Lean/Environment.lean:2336-2344`), with the exception that [the section on the loader](#from-a-build-to-the-input) states.

## Decisions of this specification

Each of these was decided on the owner's behalf by the owner's delegated agents, because the owner's intent asks for the smallest core that does the job. None is the owner's confirmation.

- The claim is the default targets of the root package, with each module of the root package that their imports reach. That is the set `lake check` replays, so a project cannot claim a target that `lake check` skips, and it needs no file of its own that classifies its targets. A target that is not a default target and that no default target imports is outside the claim, as it is for `lake build` and `lake check`. **Measured**: such a module with a `sorry` passes, and it fails once a default module imports it.
- A project states one profile, for all of its claimed modules, and no profile is `incomplete`. A library that needs a stricter profile than another is a project of its own.
- The input is one environment, because `lake check` already needs one, and it holds each constant of that environment, so the loader walks no graph and has no loop.
- The rules compute each axiom set from the input, so a set cannot be missing or differ from `Input.AxiomOf`, and the trusted base loses `Lean.collectAxioms`. **Measured** once on 2026-10-31 by `lake lint`, against the previous revision: on the root package 5.2 s real and 3.7 s user, against 4.2 s and 11.4 s, with a largest resident set of 0.75 GiB against 0.74 GiB; on this package 3.9 s and 3.5 s, against 4.6 s and 19.2 s, with 0.75 GiB against 0.69 GiB. Each is one run on a shared machine, and this package grew by this change.
- A constant of a claimed module that Lean's import replaced is checked by the loader, not reported by a rule, because the input holds one constant of each name. A violation of this kind gives `incomplete`, so it never passes, and it names no rule.
- The shell reads one Lean release, by its version and commit, and refuses any other, because RG1004 and RG1006 read forms that a release gives.
- `Regula.Contract` and `Regula.Decision` stay as a library that gives no verdict, because another project of the owner's still imports them. They go when it moves them.
- The gate has no time limit, because a wall-clock limit has no proof, and on a slow or sleeping machine it refuses a change for no fault of the change. A gate that does not end is a matter for whatever runs it.
- The gate removes each earlier build output first, with `lake clean`. **Measured** on 2026-10-31: after a library left the configuration, a module that imported it still built from the `.olean` left in Lake's build directory, and the checker read that module as claimed. After `lake clean`, the build failed.
- The gate runs the checker on the specification too, with `lake build --wfail` and `lake check` before it. So each theorem here depends on no axiom beyond the three. The path that step takes through `lintDriver` is also the one that a project that requires Regula takes.

## The trusted base

These stay assumed. Each is a statement about a system or a step that no proof of Regula examines.

- Lean's kernel, elaborator and runtime, and Lake's load and build. The owner trusts Lean and its kernel.
- **What Lean's interfaces report of a build.** `Lean.importModules` with `loadExts := false` loads the `.olean` files of the build, and `Environment.constants.map₁` holds the constants that the import keeps. `header.moduleData` holds each module's own constants, and `header.moduleNames`, `getModuleIdxFor?`, `getImplementedBy?`, `isExtern` and `Expr.getUsedConstants` report what their names say. Lean refuses an `.olean` file of a different Lean version. **Measured** once on 2026-10-31, as a search for a counterexample with a limit of one hour that stops at the first: the axiom set of `Tables.axiomSet` equals that of `Lean.collectAxioms` on each constant of Regula's modules in three runs, of this package's environment (1,216 constants), the root package's (484) and a disposable project that violates each rule (19). It found none, and it says nothing about another build.
- **What Lake reports of a workspace.** Lake's load gives the modules of the default targets, the root package's library directory and the toolchain's, and passes `lintDriverArgs`. `Lean.findOLean` finds the toolchain's library only below the pinned toolchain.
- **The thin effects of Regula's own code.** `Regula.Load.places`, `lakeEnvironment`, `loadWorkspace`, `defaultModules`, `loadInput`, `Regula.Shell.report`, `Regula.Shell.run` and the `lint` executable call Lean and Lake, pass the results to the pure functions above, print and set the exit code. No theorem states these effects: that `places` gives one place for each module in header order, that `loadInput` gives what `Facts.input` gives, and that the exit code is that of the verdict are read from the code. The compiled program runs these definitions by Lean's compiler, which the first statement trusts.
- **No process changes the build between the gate's commands.** `lake check` replays what the build holds when it runs, and the checker reads what the build holds when it runs. On macOS `lake check` runs without its sandbox, so the code of the project runs outside a sandbox, as it does in `lake build`.
- The code of a claimed module runs during its build, and no rule reads it. It can forge a recursion helper, it can remove messages, so that `lake build --wfail` sees no warning, and it can have other effects. **Measured** on 2026-10-31: a `run_cmd` wrote a file during the build, and the module passed all three commands. The check that the owner chose as the next step is what can narrow this.
- The meta-code of a dependency runs during the build too, and it is trusted in the same way.
- `lake` and `lean` are the programs that `PATH` selects.

The rules and the kernel replay read only the constants of the build. So the code of a claimed module can make a claim about a compiled program false, and it can hide a warning. Under the statements above, it cannot make an unsound proof of a claimed module pass all three commands, because `lake check` replays each constant in scope from its export and refuses each axiom beyond the three.

**Open**: a theorem about the thin effects above. No theorem here reaches `IO`, so only reading stands behind them.
