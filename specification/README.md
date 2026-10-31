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
| It refuses a constant of a claimed module that has a recursion helper's name and is not Lean's helper, in any spelling that declares it. A genuine recursive definition still passes. | **Proved**: `rg1006_exact`, `rg1006_reports_named_not_partial`, `rg1006_checker_refuses_forged_name`, and `rg1006_admits_helper` for a constant of the helper's form. A helper of the true form that code adds during the build stays the known gap (see [RG1006](#rg1006-unsafe-and-partial-declarations)). |
| It refuses an input it cannot load. | **Proved**: `refusal_none_iff`, `run_refused`, for the input. The shell's refusal of a failed load has no theorem (`Regula.Shell.run`). |
| Each rule refuses every violation and only violations, over Regula's input. | **Proved**: each `rgN_exact` is an equivalence, and `rgN_meets` states it as the rule's intent record. |
| It refuses a claimed constant whose value directly mentions `Lean.Loop.mk` or `repeatM`, so `while` and `repeat` in claimed code. | **Proved**: `rg1006_exact`, `rg1006_checker_refuses_loop`. |
| A checker that refuses nothing does not satisfy this. | **Proved**: `silent_fails`, `noisy_fails` and each `rgN_noisy`; `always_pass_fails`, `always_incomplete_fails`. |
| A pass is the verdict of the rules. | **Proved**: `run_complete`, `run_pass_holds`, `run_meets`. |

The rest of this document follows from those requirements, or is marked as decided on the owner's behalf.

## The shape of a rule

Each rule is a pure function from the closed input to the constants that it reports. Its formal statement is a lean-intent intent record (`LeanIntent.IntentRecord`), built by `ruleRecord` in [`RegulaSpecification/RuleRecord.lean`](RegulaSpecification/RuleRecord.lean). The record has one property: on each well-formed input, the function reports a subject exactly when the subject violates the rule. Thus the meaning of a rule is all in its violation predicate, for example `Violates1005`.

For each rule, the package gives a case that the rule must refuse and a case that it must admit (`Witnessed`). From them, it proves that the record meets lean-intent's obligations O2 (at confirmation and before a run), O3, O4, and O5 with the freedom `SameReports`, which is the order and the repetition of the reported subjects, and the result on an input that the admission refuses. **Proved**: `adequate`, applied in `rg1001_adequate` and the theorems that follow it. O1 holds for each record. **Proved** by lean-intent: `LeanIntent.o1_wellTyped`.

Each rule function that the checker runs is proved against its record in [`RegulaSpecification/Proofs/`](RegulaSpecification/Proofs/). The functions run over `Regula.Closed.Input`, so the proofs are about the executed definitions, not about a copy of them.

These theorems assume two things of an input. It has the closed form (`Input.WellFormed`). Each axiom set that a rule reads is the one that `Input.AxiomOf` states (`Link.AxiomsRead`). The loader computes these sets with `Lean.collectAxioms`, and no proof examines it, so that is a hypothesis of each theorem that reads a set.

## The closed input

The closed input is the type `Input` in [`RegulaSpecification/Input.lean`](RegulaSpecification/Input.lean):

| Field | Owner and interface |
| --- | --- |
| `profile`, the profile that the project states | The one argument of the lint driver, `lintDriverArgs` of the project's Lake configuration |
| `modules`, the claimed modules | Lake's load gives the modules of the default targets of the root package; each loaded module whose `.olean` lies in the root package's library directory is claimed |
| `decls`, each constant of the environment | `Lean.importModules` with `loadExts := false` |
| `loads`, the modules that the environment imports | The header of that environment |

The input has no source text, message, compiled code, option or build log. A rule does not decide what it cannot read in this input.

The admission refuses an input that does not have the closed form (`Input.WellFormed`). Each name is the name of one constant. Each constant that a constant mentions is held. At least one module is claimed, so a claim of nothing is not read as a pass (**proved**: `no_claim_refused`). Each claimed module is loaded (**proved**: `unloaded_refused`). The admission that the checker runs also refuses a claimed constant without its axiom set. **Proved**: `refusal_none_iff`.

The shell has three effects: it loads the build, it prints its report, and it sets its exit code. It writes no file. It runs no initializer of the loaded modules, because it loads them without extension states. Lake's own load of the workspace runs Git in the environment of the caller. This is read from the code, and no theorem states these effects.

## The rules

### RG1001 to RG1005: the foundation profile

Each reads a constant of a claimed module. RG1002 to RG1005 read its transitive axiom set `Input.AxiomOf`, computed from the loaded constants. The four refine one refusal: each axiom that RG1002, RG1003 or RG1004 names also violates RG1005 for each profile. Thus a wrong choice between these rules changes the rule of a finding, but not the verdict. **Proved**: `rg1005_of_hole`, `rg1005_of_unknown` and `rg1005_of_compiler`. The formal statements are in [`RegulaSpecification/Foundation.lean`](RegulaSpecification/Foundation.lean).

- **RG1001: project axioms.** A constant of a claimed module has the kind `axiom`. An assumption is a hypothesis or a field of a structure, so that each theorem that uses it shows it in its type. `lake check` refuses an axiom only when a constant mentions it, so it does not do the work of this rule. `Violates1001`.
- **RG1002: proof holes.** A constant depends on `sorryAx`, directly or through an import. `Violates1002`.
- **RG1003: unknown axioms.** A constant depends on an axiom other than `propext`, `Quot.sound` and `Classical.choice` of the toolchain, and RG1002 and RG1004 do not name it. `Violates1003`, with `Input.Known`. **Assumed**: Lean finds the library of the toolchain only below the `lib/lean` directory of the pinned toolchain, which the shell reads to say that a module is in that library.
- **RG1004: native proofs.** A constant depends on an axiom with the name form `<declaration>._native.<tactic>.<suffix>` that `native_decide`, `decide +native` and `bv_decide` add (`Lean/Meta/Native.lean:45` and `75-82`), or on an axiom by which the kernel trusts the compiler, of which `v4.35.0` declares none. `Violates1004`, with `NativeProofAxiom` and `compilerAxioms`. **Measured**: `native_decide` gave `n._native.native_decide.ax_1_1`. The rule identifies the axiom by its name, so an author can give an axiom that name. Then RG1004 reports it in place of RG1003, and the verdict is the same.
- **RG1005: the profile.** A constant depends on an axiom that the project's profile does not admit. Kernel-only admits no axiom. Choice-free admits `propext` and `Quot.sound`. Standard-logical also admits `Classical.choice`. Each admitted axiom is the toolchain's own. `Violates1005`, with `Input.Admits`.

### RG1006: `unsafe` and `partial` declarations

The rule refuses three things in a claimed module: an `unsafe` or `partial` constant without the form of Lean's recursion helper, a constant with a helper's name without that form, and a constant whose value directly mentions a loop construct of Lean. `Violates1006`, with `Input.RecursionHelper`, `HelperNamed` and `MentionsLoop`, in [`RegulaSpecification/Safety.lean`](RegulaSpecification/Safety.lean). **Proved**: `rg1006_exact` in both directions, `rg1006_checker_refuses_loop` for each construct, and `rg1006_checker_refuses_forged_name` for a plain definition with a helper's name.

**The loop constructs.** The class comes from Lean's `Init/While.lean`. A `while`, `repeat` or `repeat ... until` needs no `partial` of the module that uses it, because it compiles through `Lean.Loop.forIn` to `repeatM`, whose body is a private `partial` of that file. So the flags alone do not show a loop that does not end. The rule reads the value of each claimed constant for the one value of the type `Lean.Loop`, `Lean.Loop.mk`, and for `repeatM` (`loopConstructs`). `termination_by` and `partial_fixpoint` stay allowed, and so does `for` over a list. The owner's delegated agent added this on 2026-10-31, after `while true` passed all three commands while a `partial def` of the same loop failed.

**Measured** on 2026-10-31 on a disposable project: `while`, `repeat`, `repeat ... until`, a direct `repeatM`, a direct `Lean.Loop.forIn ⟨⟩`, `forIn Lean.Loop.mk` and an `Inhabited Lean.Loop` instance were each refused; `termination_by`, `partial_fixpoint` and `for` over a list passed.

What this leaves out, as accepted risk under the owner's trust in dependencies:

- A loop inside a dependency or the toolchain, such as `IO.iterate` (`Init/System/IO.lean:780`), which is a `partial def` that a claimed constant can call. **Measured**: it passes.
- A claimed function that takes a value of `Lean.Loop` as an argument mentions neither construct, and it passes (**measured**). Running it needs that value, which claimed code can make only through `Lean.Loop.mk`, so only a dependency's value runs it.
- A mention only in a constant's type, which runs nothing. **Proved**: `rg1006_admits_type_mention`.
- A loop that a claimed module's own code adds during the build, with the forged helper below.

**The recursion helper.** The form is a partial constant `f._unsafe_rec`, not unsafe, with no `implemented_by` and no `extern`, in the module of a safe, total definition `f` with neither. Lean makes the base of a `partial def` an opaque constant, so the rule reports the helper of a `partial def`.

**A helper's name.** The compiler reads `f._unsafe_rec` in place of `f` by its name alone, whatever its kind and flags (`getDeclInfo?`, `Lean/Compiler/LCNF/ToDecl.lean:25-27`). So the rule refuses each constant of a claimed module with a name of the form `b._unsafe_rec` that has not the helper's form, and each such constant that is not partial in particular, for each kind and however it was declared. **Proved**: `rg1006_reports_named_not_partial`, on an input whose names are unique, which the admission ensures. Only a definition can be partial (`ConstantInfo.isPartial`, `Lean/Declaration.lean:463-465`), so each constant of another kind with that name is refused. The checker runs the compiler's own test, `Lean.Compiler.isUnsafeRecName?`, in place of a copy of it. **Proved**: `isUnsafeRecName_eq` states that test against `HelperNamed`, and `mkUnsafeRecName_eq` states the name that `getDeclInfo?` looks up, so a toolchain with another form fails these proofs. **Assumed** from the source: the compiler's only readers of a helper by its name are `getDeclInfo?`, `declIsNotUnsafe` and `toDecl` (`Lean/Compiler/LCNF/ToDecl.lean:27`, `37` and `51`), with `toLCNF`'s check of `isNoncomputable` and its `replaceUnsafeRecName` (`Lean/Compiler/LCNF/ToLCNF.lean:448` and `525`). The owner's delegated agent added this on 2026-10-31, after an audit found that the plain definition below passed the rule.

```lean
def g (n : Nat) : Nat := n
def g._unsafe_rec (n : Nat) : Nat := n + 1
theorem g_one : g 1 = 1 := rfl
```

**Measured** on 2026-10-31. Before this rule, at the commit of the cut, that module passed `lake build --wfail` and `lake lint`, while `#eval g 1` and `lean --run` of `g 1` printed `2`. Lean also panics on this input during a Lake build (`emitCForDecls`), and Lake prints the panic as information and exits 0, so `--wfail` does not catch it. Now `lake build --wfail` and `lake check` still pass it, and `lake lint` reports RG1006 and exits 1. On a disposable project, RG1006 reported the helper's name in each of these forms: `def`, `abbrev`, `opaque`, `instance`, `theorem`, `axiom`, `inductive`, `structure`, `class`, a constructor, a structure field, `where`, `let rec`, `namespace`, a quoted name, `private`, `protected`, `noncomputable`, `@[reducible, inline]`, `@[extern]`, `@[implemented_by]`, a `macro` that expands to a `def`, a `mutual` block, a recursive `def`, a top-level `_unsafe_rec`, a `partial def` with and without recursion, an `unsafe def`, and a `module` file with `public` and `private` declarations. Lean itself refused `initialize` and `syntax (name := ...)` with that name, and a `mutual` block of a `def` and a `partial def`.

**Measured** on the same day: structural and well-founded recursion, each in a `mutual` block too, nested recursion through `where`, `let rec`, `private`, `protected`, an `abbrev`, a method of an instance, `partial_fixpoint`, `@[specialize]`, universe polymorphism, a `module` file, and the functions that `deriving Repr, BEq, Hashable, DecidableEq` writes for a recursive type all gave a helper that passed `lake lint`, and that project passed `lake build --wfail` and `lake check`. The rule still reports the helper of what `deriving` writes as a `partial def`, as it did before, because the base is an opaque constant (`usePartial`, `Lean/Elab/Deriving/Util.lean:116`). **Measured**: `Repr` and `BEq` on a nested inductive type and `Ord` on a recursive type.

The rule checks the helper's form and nothing about what the helper computes. **Known gap**: a claimed module can forge a helper of the true form through its own code during the build, such as `run_cmd`, until the check that the owner chose as the next step. Lean's declaration forms give a partial definition only through `addAndCompilePartialRec`, which names the helper after the definition it compiles (`Lean/Elab/PreDefinition/Basic.lean:280-292`), so a form with no code of the project's own gives no such pair. That last sentence is read from the source and has no theorem. **Measured** on 2026-10-31 with this revision of the checker, on a project of one module:

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

A run that cannot load the build gives `incomplete`. So does an input that the admission refuses, any argument list other than one profile, and any Lean other than the one this revision reads (`Regula.Shell.supportsLean`). `gateRecord` in [`RegulaSpecification/Gate.lean`](RegulaSpecification/Gate.lean) states the verdict. **Proved**: `gate_o5`, so the record leaves nothing unsaid about the verdict, and `gate_adequate`.

**Proved** of `Regula.Closed.run`, the function that the checker runs, in [`RegulaSpecification/Proofs/Verdict.lean`](RegulaSpecification/Proofs/Verdict.lean):

- `refusal_none_iff`: its admission refuses exactly an input without `Input.WellFormed`, or without the axiom set of a claimed constant.
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

Such a pass means that the proofs of the claimed modules are sound and use only axioms that the profile allows. It says nothing about what a compiled program runs. A claimed module can change that with `@[implemented_by]`, `@[extern]` or `@[csimp]`, which no rule reads, or with a helper of the true form that its own code adds during the build, whose form RG1006 reads and whose value no rule reads. **Measured** on 2026-10-31: a module with each of the first three passed all three commands.

The checker alone means less, because it reads what the build holds and replays nothing. **Measured** on 2026-10-31: a module that added a theorem of `False` with `set_option debug.skipKernelTC true` passed `lake build` and `lake lint`, and `lake check` refused it.

`lake check` imports the modules of the default targets into one environment, and the checker does too. So a project of two default executables that each declare `main` fails both commands. Lean refuses two imported modules that declare one name with different values (`Lean/Environment.lean:2336-2344`).

## Module files

Each Lean file of the root package is a `module` file. An importer that is a `module` file sees the type of a definition and the statement of a theorem, and it sees a body only where the author chose that: an `abbrev`, an instance or `@[expose]`. So what such a caller relies on is stated. **Measured** on 2026-10-31: Lean's header parser (`Lean.Parser.parseHeader`, `HeaderSyntax.isModule`) reports `module` for each of the 13 tracked Lean files below `lean/`.

The root package has one `@[expose]`, on `Regula.ExecutableContract.run`. The exported theorem `ExecutableContract.run_eq` is proved by `rfl` over that body, and without the attribute it does not build. **Measured** on 2026-10-31. Its other visible bodies are instances: those that `deriving` makes and the loader's local `MonadEnv` instance. It has no `abbrev`.

`Regula.ProgramCheck.TestListing` proves two configurations equal by reduction, so it uses `import all` on the three modules whose unexposed bodies it reads: `Regula.TestListing`, `Lake.CLI.Main` and `Init.System.ST`. `Regula.TestListing` imports Lake a second time with `meta`, because `lean --run` runs it in the process that elaborates it, and only a module imported with `meta` has its initializers run there (`Lean/Compiler/InitAttr.lean:160-168`). **Measured** on 2026-10-31: without `meta`, the process ended with signal 11.

In this package, only `RegulaSpecification.Input` is a `module` file. **The other 14 files cannot be one yet.** A `module` file cannot import a file that is not one (`Lean/Environment.lean:2120`), and no file of lean-intent at the commit that `lakefile.toml` names is one. **Measured** on 2026-10-31 with the same parser, over its tracked files. `RegulaSpecification.RuleRecord` imports three of lean-intent's modules, and each of the other files imports `RuleRecord` directly or through another of them: `Foundation`, `Safety`, `Gate`, `Witnesses`, `CasesDeclarations`, `CasesFoundation`, `CasesGate`, `Proofs.Link`, `Proofs.Tables`, `Proofs.Foundation`, `Proofs.Records`, `Proofs.Verdict` and the root `RegulaSpecification`. They can follow when lean-intent has migrated.

A file that is not a `module` file sees each body of what it imports, whatever the author chose (`Lean/Elab/Import.lean:150-156`, `Lean/Environment.lean:2183`). So the proofs read the executed definitions of `Regula.Rules` as they did before, with no `import all`.

## Decisions of this specification

Each of these was decided on the owner's behalf by the owner's delegated agents, because the owner's intent asks for the smallest core that does the job. None is the owner's confirmation.

- The root package does not set Lake's `requiresModuleSystem`. Lake would then warn on each file that is not a `module` file and imports one (`Lake/Build/Module.lean:416-424`), so the proofs here and another project that imports `Regula.Contract` would need `allowNonModules`, and a file that imports nothing of the package would still not be seen. A `module` file that imports a file that is not one is already refused by Lean, and a file that stops being a `module` file is cheap to correct.
- The root package does not set `allowImportAll`, because no other package's file uses `import all` on one of its modules at this revision.
- The specification's files are not split so that the parts without a lean-intent record could become `module` files now. No importer of those parts is a `module` file, so a split would move each statement and show nothing more, and the whole package can migrate at once.

- The claim is the default targets of the root package, with each module of the root package that their imports reach. That is the set `lake check` replays, so a project cannot claim a target that `lake check` skips, and it needs no file of its own that classifies its targets. A target that is not a default target and that no default target imports is outside the claim, as it is for `lake build` and `lake check`. **Measured**: such a module with a `sorry` passes, and it fails once a default module imports it.
- A project states one profile, for all of its claimed modules, and no profile is `incomplete`. A library that needs a stricter profile than another is a project of its own.
- The input is one environment, because `lake check` already needs one, and it holds each constant of that environment, so the loader walks no graph and has no loop.
- RG1006 refuses a constant with a helper's name whatever its kind, and it does not read what the constant computes, because the compiler reads it by its name alone and a rule over names can be proved. A field or a function of a project with that name is refused too. The checker calls the compiler's own test (`Lean.Compiler.isUnsafeRecName?`, so `Regula.Rules` imports `Lean.Compiler.Old`) instead of holding a copy.
- The shell reads one Lean release, by its version and commit, and refuses any other, because RG1004 and RG1006 read forms that a release gives.
- `Regula.Contract` and `Regula.Decision` stay as a library that gives no verdict, because another project of the owner's still imports them. They go when it moves them.
- The gate has no time limit, because a wall-clock limit has no proof, and on a slow or sleeping machine it refuses a change for no fault of the change. A gate that does not end is a matter for whatever runs it.
- The gate removes each earlier build output first, with `lake clean`. **Measured** on 2026-10-31: after a library left the configuration, a module that imported it still built from the `.olean` left in Lake's build directory, and the checker read that module as claimed. After `lake clean`, the build failed.
- The gate runs the checker on the specification too, with `lake build --wfail` and `lake check` before it. So each theorem here depends on no axiom beyond the three. The path that step takes through `lintDriver` is also the one that a project that requires Regula takes.

## The trusted base

These stay assumed. Each is a statement about a system or a step that no proof of Regula examines.

- Lean's kernel, elaborator and runtime, and Lake's load and build. The owner trusts Lean and its kernel.
- **The step from a real build to Regula's input is not yet proved.** `Regula.Load`, `Regula.Workspace` and the shell fill the input. In particular: `Lean.importModules` with `loadExts := false` loads exactly the constants of the `.olean` files, `collectAxioms` then walks their bodies, Lake's load gives the modules of the default targets, `Lean.findOLean` finds the toolchain's library only below the pinned toolchain, and Lean refuses an `.olean` file of a different Lean version.
- **`Lean.importModules` at the level `.private` gives each constant of a `module` file with its body, exposed or not** (`Lean/Environment.lean:1871`, `Lean/Environment.lean:2183`). An unexposed definition is therefore read as a definition and walked, and not read as an axiom with no value. `Regula.Workspace` names that level. **Measured** on 2026-10-31: a `module` file with `sorry`, a project axiom, `native_decide`, `partial` and `while` in unexposed bodies gave the same 16 findings as before Regula's own files became modules. A file like it with none of those passed.
- **`import all` of a module of another Lake package.** No file of this repository does that at this revision: the proofs here see the bodies of `Regula.*` because they are not `module` files, and `Regula.ProgramCheck.TestListing` uses `import all` on a module of its own package and on two of the toolchain, which belong to no package of the workspace (`Lake/Config/Workspace.lean:283-284`). When lean-intent has migrated and the proofs become `module` files, they will need it across packages. Lake's check of that is disabled with the remark "We've decided to disable this check for now" (`Lake/Build/Module.lean:430-434`), and the field that allows it is `allowImportAll` (`Lake/Config/PackageConfig.lean:314-324`), so a later toolchain can refuse those imports until the root package sets it.
- **No process changes the build between the gate's commands.** `lake check` replays what the build holds when it runs, and the checker reads what the build holds when it runs. On macOS `lake check` runs without its sandbox, so the code of the project runs outside a sandbox, as it does in `lake build`.
- The code of a claimed module runs during its build, and no rule reads it. It can forge a recursion helper of the true form, it can remove messages, so that `lake build --wfail` sees no warning, and it can have other effects. **Measured** on 2026-10-31: a `run_cmd` wrote a file during the build, and the module passed all three commands. The check that the owner chose as the next step is what can narrow this.
- The meta-code of a dependency runs during the build too, and it is trusted in the same way.
- `lake` and `lean` are the programs that `PATH` selects.

The axiom sets and the kernel replay read only the constants of the build. So the code of a claimed module can make a claim about a compiled program false, and it can hide a warning. Under the statements above, it cannot make an unsound proof of a claimed module pass all three commands, because `lake check` replays each constant in scope from its export and refuses each axiom beyond the three.

**Open**: a theorem that the loader states each constant's kind and axiom set as the environment holds them. That would shrink the second statement above.
