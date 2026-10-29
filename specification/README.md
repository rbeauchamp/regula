# Specification of the smaller Regula

This document specifies the smaller, stricter Regula that the epic [#480] asks for. Issue [#481] asks for it before any code changes. For each rule of Regula's registry, it gives one fate: kept, handed to Lean, or retired. It also specifies two new rules and the one input that all rules read. It gives the fate of each open issue that the epic lists, and how Regula checks its own library.

The owner confirmed the plain-word consequences of this document on 2026-10-29 ([the confirmation record](confirmation.md)). The leaves [#482] to [#488] start after this document merges. Until a leaf changes it, the [standard](https://rbeauchamp.github.io/regula/dev/standard/) keeps its present text, and the present checker keeps its present behaviour. This document changes no rule.

## How to read this document

Each claim has one of four marks:

- **Proved**: Lean checks a theorem of the Lean package in this directory. The theorem name follows the mark.
- **Measured**: an observation on the pinned toolchain. The procedure follows the mark, so that a reader can do it again.
- **Assumed**: a statement about Lean, Lake or the operating system that no proof here examines. The leaf that builds on it must prove it or keep it as a named assumption.
- **Open**: an obligation that this document does not discharge, with the work that discharges it.

A statement of what a rule or the checker must do is specification, and it has no mark. The marks are for claims about Lean, Lake, the build and the theorems of the package.

Regula pins `leanprover/lean4:v4.35.0` (`lean-toolchain`), and so does this package. Most observations and citations of this document were made at `v4.34.1`, the toolchain that Regula pinned before. A citation such as `Lean/Util/CollectAxioms.lean:146-151` is a path below `src/lean/` of the tag `v4.34.1`, with its lines. A citation that starts with `src/` is a path below the root of that tag. A citation marked `v4.35.0` is a path below `src/lean/` of the tag `v4.35.0`.

The formal statements are in the Lean library `RegulaSpecification` in this directory. The library requires lean-intent at commit `da9cacf377ec681f50d0eb4d5a5bb98fe6de76fe`. That commit on lean-intent's `main` merged [lean-intent pull request 8](https://github.com/rbeauchamp/lean-intent/pull/8), the port of lean-intent to intent records. The library also requires the root package, for the closed rule identity `Regula.RuleId` only. To check all statements and theorems, use `lake build --wfail` in this directory.

## The target toolchain

The smaller Regula targets Lean `v4.35.0`, the stable release of 2026-10-12. Its tools do the work of the rules that go to Lean (see "What Lean v4.35.0's tools do").

- Regula, lean-intent and Acorn move to `v4.35.0` together, because a Lean package and its dependents build with one toolchain. A Regula on a newer toolchain than lean-intent or Acorn cannot be their dependency or their dependent.
- The move is a change of its own in each repository: lean-intent first, then Regula, then Acorn. It lands before the leaves [#482] to [#488] start.
- lean-intent moved in [lean-intent pull request 12](https://github.com/rbeauchamp/lean-intent/pull/12), and Regula in [#494]. This package pins lean-intent at commit `06ae93d6593cacf4285054e1e0f7a75a76edf4d4` of its `main`, on `v4.35.0`.
- At `v4.35.0` the toolchain declares no axiom by which the kernel trusts the compiler, so `compilerAxioms` is empty ([RG1004]).
- **Open**: the observations of "What the input can show" are on `v4.34.1`. The leaf that builds on an observation repeats it on `v4.35.0`.

## The shape of a rule

Each kept or new rule is a pure function from the closed input to the subjects that it reports. Its formal statement is a lean-intent intent record (`LeanIntent.IntentRecord`), built by `ruleRecord` in [`RegulaSpecification/RuleRecord.lean`](RegulaSpecification/RuleRecord.lean). The subject of the record is the function. The record has one property: on each well-formed input, the function reports a subject exactly when the subject violates the rule. Thus the meaning of a rule is all in its violation predicate, for example `Violates1005`.

For each rule, the package gives a case that the rule must refuse and a case that it must admit (`Witnessed`). From them, it proves these facts about the record of the rule:

- lean-intent's obligations O2 (at confirmation and before a run), O3, O4, and O5 with the freedom `SameReports`. **Proved**: `adequate`, applied in `rg1001_adequate` and the theorems that follow it.
- The function that reports nothing does not meet the record. **Proved**: `silent_fails`.
- The function that reports each candidate does not meet the record. **Proved**: `noisy_fails`, applied in `rg1001_noisy` and the theorems that follow it.

The freedom `SameReports` is what each record leaves unsaid. It is the order and the repetition of the reported subjects, and the result on an input that the admission refuses. O1 holds for each record. **Proved** by lean-intent: `LeanIntent.o1_wellTyped`.

lean-intent does not yet state three obligations. These are the cone check ([lean-intent#2]), the consequence ledger ([lean-intent#3]) and the owner's confirmation record ([lean-intent#5]). **Open**: for each record of this document, these three obligations wait for those issues.

## The verdict

A run of the checker gives one of three verdicts: `pass`, `fail` or `incomplete` (`Verdict` in [`RegulaSpecification/Gate.lean`](RegulaSpecification/Gate.lean)). The record `gateRecord` states the verdict:

- A build that Lean could not load is `incomplete`. This is [RG2001].
- An input that the admission refuses is `incomplete`. Missing evidence is not read as an empty set.
- A well-formed input is not `incomplete`. It passes exactly when all kept and new rules hold of each of its environments (`Bundle.AllHold`).

**Proved**: `gate_o5`. Two verdict functions that meet the record are equal, so the record leaves nothing unsaid about the verdict.

A pass of the project's gate is the result of three commands of the target toolchain on one finished build:

1. `lake build --wfail` for the claimed targets.
2. `lake check`. On macOS it is `lake check --inadvisably-no-sandbox` (see [RG2005]).
3. The checker of Regula over the finished build.

The checker starts none of these processes. The project's local gate or its CI runs the three commands in sequence on one checkout. **Assumed**: no process changes the build between the three commands. `lake check` takes no module list. It checks the modules of the default targets of the root package, so [RG2002] refuses a claimed target that is not a default target.

## The closed input

The closed input is the type `Input` in [`RegulaSpecification/Input.lean`](RegulaSpecification/Input.lean). Each field is one of these four parts, and each part comes from the owner of its data:

| Part | Owner and interface |
| --- | --- |
| The root package's targets, with the modules, options and extra Lean arguments of each target | Lake's own load of the workspace |
| The claim: the classification of each target | `foundation_manifest.json`, a closed format that Regula defines |
| Each module of the root package that Lake builds: its imports and the names of the environment extensions with entries in its `.olean` files | `Lean.readModuleDataParts` |
| Each constant of each environment that the shell loads, with the modules it imports | `Lean.importModules` with `loadExts := false` |

The input has no source text, message, info tree, option set in source, build log or list of files. A rule does not decide what it cannot read in this input. This is the boundary of the input.

One environment cannot hold the `main` of two executables, because Lean refuses a constant that two imported modules declare. So the shell loads the libraries in one environment, and the root of each executable with its imports in an environment of its own. The input of a run is that list of environments (`Bundle` in [`RegulaSpecification/Gate.lean`](RegulaSpecification/Gate.lean)). Each environment has the same targets, claim and module records.

The admission refuses an input that does not have the closed form (`Bundle.WellFormed` and `Input.WellFormed`). These are the conditions:

- The input has at least one environment.
- In each environment, each name is the name of one constant, and each constant that a constant mentions is loaded.
- Each module that Lake gives for a target is loaded, in some environment.
- The claim claims at least one target. A claim of nothing is not read as a pass. **Proved**: `no_claim_refused`.

The shell refuses a module if it cannot read the `.olean` files of the module, and the verdict is `incomplete`. A read error is not an absent file ([#441]).

The shell has three effects: it loads the build, it prints its report, and it sets its exit code. It starts no process, it writes no file, and it removes no file. It runs no initializer of the loaded modules, because it loads them without extension states.

### What the input can show

These results settle the questions of feasibility that the new design raises. The observations used small modules, which were compiled with `lean -o` of the pinned toolchain. A Lean program read all parts of each `.olean` file with `Lean.readModuleDataParts`, and listed the names of the extensions with entries.

- Axioms come from the constants themselves.
  - `Lean.collectAxioms` reads a table that the compiling process records for imported constants, at `Lean/Util/CollectAxioms.lean:113-143` and `146-151`.
  - The `addImportedFn` of the extension puts that table in its state, at `Lean/Environment.lean:1988`. Only `finalizePersistentExtensions` runs it, and only with `loadExts`, at `Lean/Environment.lean:2403-2404`.
  - Without `loadExts`, each extension keeps its initial state, at `Lean/Environment.lean:2427-2431`. Then `collectAxioms` walks the bodies of the constants, at `Lean/Util/CollectAxioms.lean:37-74`.
  - **Assumed** from that source. **Measured**: with `loadExts := false`, a theorem that uses `propext` gave `#[propext]`, which agrees with it.
- The recorded table is in the build. **Measured**: each `.olean` file of a module with constants had entries of the extension `_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt`. The present standard already refuses this table as evidence, in §7.4.
- An option that a source file sets leaves no record.
  - **Measured**: a module had `set_option linter.unusedVariables false`, `set_option autoImplicit true` and a `set_option … in` command. It had the same extension names and entry counts as the same module without them, in all three parts.
  - The only difference was one entry of `Lean.Linter.lintLogExt`. That entry is the linter warning that the option turned off.
  - The command `set_option` changes only the options of the scope, at `Lean/Elab/BuiltinCommand.lean:516-520`. **Assumed** from that source.
- A command that runs code leaves no record.
  - **Measured**: a module with `run_cmd Lean.modifyEnv id` had the same entries as an empty module with the same import. The one difference was an entry of `_private.Lean.ExtraModUses.0.Lean.extraModUses`, an extension that modules with no such command also have.
  - The command `#eval` also compiles in a scratch environment, at `Lean/Elab/BuiltinEvalCommand.lean:230-232`. **Assumed** from that source.
- Code that a module registers leaves named entries.
  - **Measured**: a module with `syntax`, `macro_rules`, `macro`, `elab` and `initialize` commands had entries of five extensions. These are `Lean.Parser.parserExtension`, `Lean.Elab.macroAttribute`, `Lean.Elab.Term.termElabAttribute`, `_private.Lean.Compiler.MetaAttr.0.Lean.metaExt` and `Lean.regularInitAttr`. The modules without such commands had none of them.
  - The source declares the command and tactic elaborator extensions with their declaration names, at `Lean/Elab/Command.lean:611` and `Lean/Elab/Tactic/Basic.lean:147`. **Assumed** from that source.
- A structural recursive definition `f` has a recursion helper. **Measured**: Lean added `f._unsafe_rec`, a partial and not unsafe definition in the module of `f`. The definition `f` itself was safe and not partial.
- At `v4.34.1`, kernel replay is the program `leanchecker` with a module list. At the target toolchain, `lake check` replaces it in the gate (see the next section).
  - `leanchecker` replays the new constants of each module that an argument names into the environment of its imports, at `LeanChecker.lean:12-33` and `91-113`.
  - With no argument, it checks only the modules below the package name of `lake-manifest.json` with an uppercase first letter, at `LeanChecker.lean:38-52`. It does not check axioms.
  - **Assumed**: each item about `leanchecker` is from its source, and no proof here examines it.
- A warning fails the build with `--wfail`.
  - The option sets the level that fails the build to `warning`, at `Lake/CLI/Main.lean:288`. A job fails when its log has an entry of that level, at `Lake/Build/Run.lean:125`.
  - A build that Lake does not do again replays its saved log, at `Lake/Build/Common.lean:242-257`. Thus a cached warning also fails the build.
  - Lake sees only a message that Lean logs.
  - **Assumed**: each item about `--wfail` is from the source of Lake, and no proof here examines it.
- `Lean.findSysroot` can find a toolchain that is not the pinned one. **Measured**: a program started with the pinned `lean --run` found the search path of an unpinned toolchain through `findSysroot`. Thus the shell takes the toolchain from Lake's load, not from `findSysroot`.

### What Lean v4.35.0's tools do

These items are read from the source of the tag `v4.35.0`. **Assumed**: each of them is from that source, and no proof here examines it. The release notes of `v4.35.0` are not a source of this document.

- `lake check` builds the default targets of the root package in a `bwrap` sandbox, and then exports them.
  - The build is a `lake check` with no option of its own, so it does not have `--wfail` (`Lake/CLI/Check.lean:338-354`, `Lake/CLI/Main.lean:1218-1226`).
  - The modules are those of the default libraries, and the root of each default executable with its imports in the package (`Lake/Build/Package.lean:40-61`).
- The export holds each constant in scope with a name that is not internal, and the constants that each one mentions (`LeanExport/Basic.lean:458-472`). A name is internal when one of its parts starts with `_` (`Lean/Data/Name.lean:125-128`). Thus the export includes the constants of the dependencies and of the toolchain.
- `lake check` replays the export with `leanchecker --silent --from-export`, after any other kernel that it runs (`Lake/CLI/Check.lean:459-472`). No `.olean` file of the project is loaded into the process that gives the verdict.
- It refuses each axiom other than `propext`, `Classical.choice` and `Quot.sound` that a constant of the export mentions (`Lake/CLI/Check.lean:662-675` and `770`, `Lake/Check/Axioms.lean:57-71`).
  - The list is fixed, and no option changes it.
  - For each axiom, it reports one constant that mentions it, not the axiom set of each constant.
  - An axiom that no constant mentions is not refused.
- `--paranoid` adds five kernels that the toolchain bundles: `leanchecker-paranoid`, `lean4lean`, `nanoda` (the program `nanoda_bin`), `con-leche` and `con-ron` (`Lake/CLI/Check.lean:569-580`). **Measured**: the five programs are in `bin/` of the installed `v4.35.0` toolchain on macOS.
- Outside Linux, `lake check` and `lake comparator` refuse to start without `--inadvisably-no-sandbox`. With it, they print that the run is not trustworthy (`Lake/CLI/Check.lean:599-612`).
- `lake comparator` judges a solution module against a challenge module (`Lake/CLI/Check.lean:515-527`, `Lake/Check/Axioms.lean:73-91`). Each theorem that its configuration names must have the statement of the challenge and use only the axioms that the configuration permits. Then the kernels check the solution.

## The rules

The registry of Regula has 24 rules (`Regula.RuleId`). The function `fate` in [`RegulaSpecification/Fates.lean`](RegulaSpecification/Fates.lean) gives each of them one fate. Lean examines that the match is exhaustive. Thus a rule that the registry adds or removes stops the build of this package until the table changes.

**Proved**: `fate_counts`. Of the 24 rules, 15 are kept, 2 go to Lean and 7 are retired. The two new rules have the proposed identifiers `RG2007` and `RG6001`, which no rule of the registry has (**proved**: `new_not_registered`).

| Rule | Fate | Formal statement |
| --- | --- | --- |
| [RG1001] | Kept | `rg1001`, `Violates1001` |
| [RG1002] | Kept | `rg1002`, `Violates1002` |
| [RG1003] | Kept | `rg1003`, `Violates1003` |
| [RG1004] | Kept | `rg1004`, `Violates1004` |
| [RG1005] | Kept | `rg1005`, `Violates1005` |
| [RG1006] | Kept | `rg1006`, `Violates1006` |
| [RG1007] | Kept | `rg1007`, `Violates1007` |
| [RG1008] | Kept | `rg1008`, `Violates1008` |
| [RG1009] | Kept | `rg1009`, `Violates1009` |
| [RG2001] | Kept, as the refusal of the input | `gateRecord` |
| [RG2002] | Kept | `rg2002`, `Violates2002` |
| [RG2003] | Handed to Lean: `lake build --wfail` | No statement of Regula |
| [RG2004] | Kept | `rg2004`, `Violates2004` |
| [RG2005] | Handed to Lean: `lake check` | No statement of Regula |
| [RG2006] | Kept, with less scope | `rg2006`, `Violates2006` |
| [RG3001] | Kept | `rg3001`, `Violates3001` |
| [RG3002] | Kept | `rg3002`, `Violates3002` |
| [RG4001] to [RG4004] | Retired | No statement |
| [RG5001] to [RG5003] | Retired | No statement |
| `RG2007`, new | New | `rg2007`, `Violates2007` |
| `RG6001`, new | New | `rg6001`, `Violates6001` |

Each entry below has the same fields. The domain is the set of subjects that the rule examines. The input is the part of the closed input that it reads. "Supersedes" names the open issues that the entry replaces, with the leaf that closes each.

### The foundation profile

The rules [RG1001] to [RG1005] read the transitive axiom set `Input.AxiomOf` of each constant, which comes from the loaded constants. The four rules [RG1002] to [RG1005] refine one refusal. **Proved**: `rg1005_of_hole`, `rg1005_of_unknown` and `rg1005_of_compiler`. Each axiom that [RG1002], [RG1003] or [RG1004] names also violates [RG1005] for each profile. Thus a wrong choice between these rules changes the rule of a finding, but not the verdict.

The second command of the gate, `lake check`, also bounds the axioms. It refuses each axiom other than `propext`, `Classical.choice` and `Quot.sound` that a constant in scope mentions, dependencies and toolchain included. So a pass of the gate bounds each constant by the standard-logical profile, and that bound has two independent computations.

But the list of `lake check` is fixed, and it gives no axiom set for each constant. So it cannot decide choice-free or kernel-only, an axiom that no constant uses, or the rule of a finding. Thus the axiom sets of these rules stay Regula's input, computed from the constants that the shell loads. `lake comparator` permits a list that its configuration gives, but only for the theorems of a challenge, and the gate has no challenge.

#### [RG1001]: project axioms

- **Fate**: kept. Leaf: [#487].
- **Intent**: a claimed module declares no logical axiom. An assumption is a hypothesis or a field of a structure, so that each theorem that uses it shows it in its type.
- **Domain**: each constant of a claimed module.
- **Input**: the kind of each constant and its module.
- **Formal statement**: `Violates1001`. A constant of a claimed module with the kind `axiom` violates the rule. The axiom of a native proof is included, and [RG1004] also reports the constants that use it.
- **Accepted risks**: none in addition to the risks of the input. `lake check` refuses an axiom only when a constant mentions it, so it does not do the work of this rule.
- **Supersedes**: none.

#### [RG1002]: proof holes

- **Fate**: kept. Leaf: [#487].
- **Intent**: no constant of a claimed module depends on `sorryAx`, directly or through an import. Thus no `sorry`, `admit` or unfinished proof stays.
- **Domain**: each constant of a claimed module.
- **Input**: the transitive axiom set of each constant.
- **Formal statement**: `Violates1002`. **Proved**: `rg1005_of_hole`.
- **Accepted risks**: none in addition to the risks of the input.
- **Supersedes**: none.

#### [RG1003]: unknown axioms

- **Fate**: kept. Leaf: [#487].
- **Intent**: each transitive axiom of a constant of a claimed module is `propext`, `Quot.sound` or `Classical.choice` of the toolchain. The rule does not name an axiom that [RG1002] or [RG1004] reports.
- **Domain**: each constant of a claimed module.
- **Input**: the transitive axiom set of each constant, and if the module of each axiom is in the toolchain's own library.
- **Formal statement**: `Violates1003`, with `Input.Known`. **Proved**: `rg1005_of_unknown`.
- **Accepted risks**: the shell decides if a module is in the toolchain's library from the place where Lean found its `.olean` file. **Assumed**: Lean finds the library of the toolchain only below the `lib/lean` directory of the pinned toolchain. Leaf [#483] establishes this.
- **Supersedes**: none.

#### [RG1004]: compiler-trusting proofs

- **Fate**: kept. Leaf: [#487].
- **Intent**: no constant of a claimed module depends on the axiom of a native proof. It also depends on no axiom by which the kernel trusts the compiler. Thus no proof rests on compiled code.
- **Domain**: each constant of a claimed module.
- **Input**: the transitive axiom set of each constant, and the names of its axioms.
- **Formal statement**: `Violates1004`, with `NativeProofAxiom` and `compilerAxioms`. At `v4.34.1` and at `v4.35.0`, `native_decide`, `decide +native` and `bv_decide` add an ordinary axiom with the name `<declaration>._native.<tactic>.<suffix>` (`Lean/Meta/Native.lean:37-90`, and `45` and `75-82` at `v4.35.0`). At `v4.35.0`, `compilerAxioms` is empty, because the toolchain declares no axiom by which the kernel trusts the compiler. **Assumed** from that source. **Proved**: `rg1005_of_compiler`.
- **Accepted risks**: the rule identifies the axiom of a native proof by its name. An author can give an axiom that name. Then [RG1004] reports it in place of [RG1003], and the verdict is the same.
- **Supersedes**: none.

#### [RG1005]: the profile of a surface

- **Fate**: kept. Leaf: [#487].
- **Intent**: each constant of a module that the claim gives a profile depends only on axioms that the profile admits. Kernel-only admits no axiom. Choice-free admits `propext` and `Quot.sound`. Standard-logical also admits `Classical.choice`. Each admitted axiom is the toolchain's own.
- **Domain**: each constant of a claimed module, under each profile that a claimed target of its module gives.
- **Input**: the transitive axiom set of each constant, and the claim.
- **Formal statement**: `Violates1005`, with `Input.Admits`. This is the rule that the soundness of a claim rests on.
- **Accepted risks**: none in addition to the risks of the input.
- **Supersedes**: none.

### Escape hatches and execution

#### [RG1006]: unsafe and partial declarations

- **Fate**: kept. Leaf: [#487].
- **Intent**: a claimed module declares nothing that is unsafe or partial. The one exception is the recursion helper that Lean adds for a safe recursive definition.
- **Domain**: each constant of a claimed module.
- **Input**: the flags `isUnsafe` and `isPartial`, the names, the modules, and the runtime replacement and `extern` marks of the constants.
- **Formal statement**: `Violates1006`, with `Input.RecursionHelper`. A helper is a partial constant `f._unsafe_rec`, not unsafe, with no replacement. It is in the module of a safe, total `f` with no replacement.
- **Accepted risks**: the rule identifies a helper by its form, not by what it computes. A helper is not logical evidence, because Lean's kernel refuses a safe constant that mentions a partial one, at `src/kernel/type_checker.cpp:114-115`. What a helper computes is a question of execution, which [RG3002] decides under a checked execution claim. The regeneration of the base that the present standard requires, in §7.4, goes away with its code in [#486].
- **Supersedes**: none.

#### [RG3001]: the execution closure resolves

- **Fate**: kept. Leaf: [#487].
- **Intent**: the execution closure of each claimed executable contains only constants of the input, and no cycle of runtime replacements. Thus no account of execution leaves out a path, and each path ends in a definition.
- **Domain**: each name in the execution closure of the `main` of a claimed executable.
- **Input**: the constants, their runtime replacements and the recursion helpers.
- **Formal statement**: `Violates3001`, with `Input.Executes` and `Input.Replaces`. Compiled code runs the replacement of a constant if it has one. Else it runs the helper if there is one, else the constants that the value mentions. A constant on a cycle of replacements violates the rule, because the cycle runs no definition. **Proved**: `rg3001_refuses_cycle`.
- **Accepted risks**: the admission already requires each mentioned constant to be loaded. Thus the rule can fail only for a replacement that names an absent constant. **Assumed**: compiled code follows the kernel value of a constant, except at a replacement or a helper. Leaf [#487] keeps this as a named assumption.
- **Supersedes**: none.

#### [RG3002]: execution boundaries

- **Fate**: kept. Leaf: [#487].
- **Intent**: under a checked execution claim, each boundary that the closure reaches has a theorem of a claimed module that states its correspondence. A boundary is a runtime replacement, a recursion helper or code that no theorem can bind, outside the toolchain.
- **Domain**: each boundary in the execution closure of a claimed executable with the execution mode `checked`.
- **Input**: the closure, the boundaries and the statements that theorems of claimed modules prove.
- **Formal statement**: `Violates3002`, with `Input.Boundary`, `Input.Unbindable` and `Goal.corresponds`. Code that no theorem can bind fails the rule with any theorem. It is an `extern` constant, a partial definition that is not a recursion helper, or a value that `initialize` sets. A theorem of Lean speaks of a kernel value, and such code runs something else. **Proved**: `rg3002_refuses_extern`.
- **Accepted risks**: the rule reads compiled code from the kernel values, not from the compiled code in the build. **Open**: the exact correspondence statement for each kind of boundary, for example the recursion equation of a helper. Leaf [#487] gives these statements.
- **Supersedes**: none.

### Contracts

#### [RG1007]: executable contracts

- **Fate**: kept. Leaf: [#487].
- **Intent**: each `ExecutableContract f R` of a claimed module constrains the code that callers run. It fixes no argument of `f`, and `f` is safe, total and computable. A decision contract states its specification without `f`.
- **Domain**: each executable contract of a claimed module.
- **Input**: the contract, read from the type of its theorem (`Contract`), and the constants.
- **Formal statement**: `Violates1007`, with `Input.SafeComputable` and `Input.SpecReachesImpl`.
- **Accepted risks**: "without `f`" means that the specification does not reach `f` through the constants that it mentions. A specification can restate the body of `f` without its name. The cone check of [lean-intent#2] is stronger, and `RG6001` uses it.
- **Supersedes**: none.

#### [RG1008]: decision contracts

- **Fate**: kept. Leaf: [#487].
- **Intent**: each function that a claimed module registers as a decision function has a decision contract in a claimed module, or a `Decidable` result type. If the contract is removed and the registration stays, the check fails.
- **Domain**: each registered decision function of a claimed module.
- **Input**: the registrations, the contracts and the result types.
- **Formal statement**: `Violates1008`.
- **Accepted risks**: a registration that the author removes removes the requirement with it, as it does now.
- **Decision**: a registration becomes a declaration of a type of Regula's interface, read as a constant. The present attribute `@[regula_decision]` is code that a tool module defines. `RG2007` and [#484] do not let a claimed module import a tool module or have entries of an extension that Lean does not define. Leaf [#487] gives the declaration its form.
- **Supersedes**: none.

#### [RG1009]: shared Boolean tests

- **Fate**: kept. Leaf: [#487].
- **Intent**: the specification of a decision contract states its meaning in other terms than the code. Thus it reaches no Boolean test outside the toolchain that the implementation or the acceptance predicate also reaches.
- **Domain**: each decision contract of a claimed module.
- **Input**: the contract, the constants that each constant mentions, and the result type of each constant.
- **Formal statement**: `Violates1009`, with `Input.ProjectTest`.
- **Accepted risks**: none in addition to the risks of the input.
- **Supersedes**: none.

### The project

#### [RG2001]: the environment

- **Fate**: kept, as the refusal of the input. Leaf: [#483].
- **Intent**: a run that cannot load the build with the pinned toolchain gives `incomplete`. An input that is not in the closed form also gives `incomplete`, not a pass.
- **Domain**: the run.
- **Input**: the result of the load of the build.
- **Formal statement**: the first two properties of `gateRecord`. **Proved**: `gate_o5`, `gate_adequate`, `always_pass_fails` and `always_incomplete_fails`.
- **Accepted risks**: **Assumed**: Lean refuses an `.olean` file that a different Lean version wrote (`Lean.readModuleData`). Leaf [#483] establishes this, or keeps it as a named assumption.
- **Supersedes**: [#441], for the reads of the loader. It closes with [#483].

#### [RG2002]: the classification of the targets

- **Fate**: kept. Leaf: [#487].
- **Intent**: the claim classifies each target of the root package exactly one time and names no target that Lake does not have. It classifies an executable as each library that contains its root module. Each claimed target is a default target of the root package, because `lake check` checks only the modules of the default targets ([RG2005]).
- **Domain**: each target that Lake gives or that the claim names.
- **Input**: Lake's targets, with the default targets of its load, and the claim.
- **Formal statement**: `Violates2002`. **Proved**: `rg2002_refuses_nondefault`. A claimed executable that is not a default target violates the rule.
- **Accepted risks**: **Open**: the reader of `foundation_manifest.json` accepts only the text that its writer gives for a claim. Leaf [#487] proves this of the reader, as for the present format.
- **Supersedes**: none.

#### [RG2003]: a warning-free build

- **Fate**: handed to Lean, as `lake build --wfail` of the target toolchain for the claimed targets. Leaf: [#482]. `lake check` does not do the work of this rule, because its build does not have `--wfail`. At `v4.35.0`, the option sets the level that fails the build at `Lake/CLI/Main.lean:307`, and the job fails at `Lake/Build/Run.lean:118`.
- **Intent**: each claimed module elaborates from source with no error and no warning.
- **Domain**: each module of a claimed target.
- **Input**: none of Regula. Lake decides from the messages that Lean logs (see "What the input can show").
- **Formal statement**: none of Regula. The property is Lake's: the build fails when a job logs a message of the level `warning` or higher.
- **Accepted risks**: Lake sees only a message that Lean logs. Lean itself drops some messages, as [#469] and [#471] show. Code that a claimed module runs can remove messages, as in [#472]. An option in source can turn a linter off, as in [#422]. Such a gap can hide a warning. It does not change what the kernel checks or what the axiom sets are.
- **Supersedes**: [#472], [#471] and [#469] close with [#482]. Issues [#477], [#475], [#473], [#359] and [#425] close with [#483], which removes the observation of elaboration.

#### [RG2004]: coverage

- **Fate**: kept. Leaf: [#487].
- **Intent**: each module of the root package that Lake builds is in exactly one library, or in no library and the root of an executable. No claimed module imports a module of an excluded target.
- **Domain**: each module of the root package that Lake builds.
- **Input**: Lake's targets and modules, and the imports of each module.
- **Formal statement**: `Violates2004`, with `Input.Covered`.
- **Accepted risks**: **Assumed**: Lake's load gives each module that it builds for the root package, the modules that only an import adds included. Leaf [#483] establishes this through Lake's own interface.
- **Supersedes**: none.

#### [RG2005]: kernel admission

- **Fate**: handed to Lean, as `lake check` of the target toolchain. Leaf: [#482].
- **Intent**: Lean's kernel checks each constant of each claimed module again, from an export of the build. The process that checks it loads no `.olean` file of the project. Thus no code can add a constant that the kernel did not check.
- **Domain**: each module of a default target of the root package, and each constant in its scope. Each claimed target is a default target ([RG2002]).
- **Input**: none of Regula.
- **Formal statement**: none of Regula. The property is that of `lake check` (see "What Lean v4.35.0's tools do").
- **Decision**: `--paranoid` is optional. The owner trusts Lean's kernel, and the gate requires that kernel. A project can add the five other kernels. **Open**: the cost of `--paranoid` is not measured. The export of a module that imports Lean holds all of Lean, as Regula's does. Leaf [#482] measures it, and the owner can then make it required.
- **Accepted risks**: on macOS the gate runs `lake check --inadvisably-no-sandbox`, because the sandbox requires Linux. Then the build and the export run outside the sandbox, as `lake build` does. The trusted base already holds that code honest, so the soundness argument does not change. On Linux, the sandbox runs. A constant with an internal name that no exported constant mentions is not replayed, and it is part of no proof of an exported constant. **Assumed**: the build of `lake check` gives the modules that the first command built.
- **Supersedes**: [#309]. Its recommendation goes to `lake check` of `v4.35.0`. It closes with [#482].

#### [RG2006]: the configuration of claimed targets

- **Fate**: kept, with less scope. Leaf: [#484].
- **Intent**: each claimed target turns automatic implicits off and sets only options of a closed allowlist. It loads no plugin and no dynamic library, and it gives Lean no other argument.
- **Domain**: each claimed target.
- **Input**: the options and the extra Lean arguments that Lake gives for each target.
- **Formal statement**: `Violates2006`, for the allowlist `allowed`. **Proved**: `rg2006_adequate`, for each allowlist that contains the two options of automatic implicits.
- **Accepted risks**: an option that a source file sets leaves no record (**measured**), so the rule does not read it. The present rule also requires `linter.missingDocs` and Mathlib's standard linters. These requirements go to written guidance with the documentation rules. **Open**: [#484] fixes the members of the allowlist. It contains no option that can stop a default warning or a check of Lean.
- **Supersedes**: [#295] closes with [#484], because the rule refuses plugins and dynamic libraries. Issues [#474], [#422], [#464] and [#411] close with [#483], because no rule reads options in source.

### Documentation

The seven documentation rules are retired to written guidance. A broken documentation example or a missing docstring is cheap to see and cheap to correct by hand. Under the owner's rule of cost, such a rule stays a written instruction and accepted risk, not a check. Leaf [#488] removes their checks and changes the standard's §7.7 and its rule pages. The `lean` blocks of the standard itself are still elaborated when the rule-reference site builds.

| Rule | Intent, now written guidance |
| --- | --- |
| [RG4001] | A marker of a documentation fence is in its place, each fence is closed, and Lean code is only in a `lean` fence. |
| [RG4002] | A `lean` fence of the checked documentation elaborates with no warning, and passes the declaration and axiom rules. |
| [RG4003] | A `lean-fail` fence fails with one error that matches its pattern. |
| [RG4004] | A `lean-trusted-compiler` fence elaborates with no warning and contains a compiler-trusting declaration. |
| [RG5001] | A claimed module has a module docstring as its first command after the imports, and it imports no module two times. |
| [RG5002] | Each public `@[regula_material]` declaration has a docstring. |
| [RG5003] | Each public `@[regula_material]` docstring has a section `# Intent` that is not empty. |

For each of the seven rules: the fate is retired, with leaf [#488]. There is no domain, no input and no formal statement after the leaf. The accepted risk is the failure that the rule found. The rules supersede the campaigns of documentation fences in [#391], which closes when [#486] and [#488] have landed.

### New rules

#### `RG2007`: a closed subset of the language

- **Fate**: new. Leaf: [#484].
- **Intent**: a claimed module registers no code that Lean runs while it elaborates. Thus it has no macro, elaborator, syntax, initializer, `meta` declaration or attribute that Lean does not define.
- **Domain**: each claimed module.
- **Input**: the names of the environment extensions that have entries in the `.olean` files of the module.
- **Formal statement**: `Violates2007`, for the allowlist `declarative`. `ClosedAllowlist` requires that the allowlist admits none of `metaExtensions`. **Proved**: `rg2007_refuses_meta`, and `rg2007_adequate` for each closed allowlist that admits `Lean.declRangeExt`.
- **Feasibility**: settled. The registrations leave named entries (**measured**), and a name outside the allowlist is refused, an unknown name included.
- **Accepted risks**: a command that runs code (`#eval`, `run_cmd`, `run_elab`, `run_meta`) leaves no record (**measured**), so the rule cannot see it. If such code changes constants, `lake check` and the axiom sets find it. If it removes messages, `--wfail` does not see them. If it changes entries of an admitted extension, such as compiled code, a claim of execution can be false.
- **Open**: the owner can ask to close this gap. Then the checker reads the commands of each claimed module with Lean's parser, and refuses a command outside a closed set. That is a second input, which this design leaves out.
- **Supersedes**: [#468] and [#462] close with [#484], because a claimed module can no longer declare their macros.

#### `RG6001`: the obligations of each deliverable

- **Fate**: new. Leaf: [#485].
- **Intent**: the owner's committed confirmation record names the deliverables, not the project's code. For each one, theorems of claimed modules prove these things. The implementation and the intent record exist. lean-intent's obligations O1 to O5, O2 before a run and its degenerate check hold of the record. It does not reach its implementation, and it keeps each consequence that the owner answered. The implementation fulfils it.
- **Domain**: each deliverable that the owner's record names: an implementation and its intent record. A project with no such record fails, so an empty inventory passes only when the record says so.
- **Input**: the owner's confirmation record, the statements that theorems of claimed modules prove, and the constants.
- **Formal statement**: `Violates6001`, with `IntentPart.Fails`. A finding names the deliverable and the part that fails. **Proved**: `rg6001_refuses_no_record` and `rg6001_refuses_missing`.
- **Accepted risks**: lean-intent does not yet state three parts. Here the independence is the approximation "the record does not reach the implementation". `Goal.keeps` and the field `confirmed` stand for what [lean-intent#3] and [lean-intent#5] define. **Open**: [#485] uses lean-intent's own statements when they exist, and the owner's record takes the form that lean-intent gives. That record also carries the order of the confirmation and the implementation, and the owner's act, which no build shows.
- **Supersedes**: none.

## The rules that apply to a declaration

For a constant of a claimed module, this table gives the rules that examine it and the input that decides each rule.

| Subject | Rules | Input that decides |
| --- | --- | --- |
| Each constant of a claimed module | [RG1002], [RG1003], [RG1004], [RG1005], [RG1006], and [RG1001] if its kind is `axiom` | Its kind, its transitive axiom set, the profile of its module, its flags and its marks |
| A theorem with the type `ExecutableContract f R` | [RG1007], and [RG1009] for a decision kind | The contract in its type, the constants that each constant mentions, and the Boolean tests |
| A registered decision function | [RG1008] | The registrations, the contracts and the result type |
| A constant in the execution closure of a claimed executable | [RG3001], and [RG3002] under a checked execution claim | The closure, the boundaries and the statements that theorems prove |
| The implementation of a declared deliverable | `RG6001` | The deliverables, the statements that theorems prove, and the owner's answers |
| Each claimed module | [RG2004], `RG2007`, and Lean's [RG2003] and [RG2005] | Lake's modules, the imports, the extension names, and Lean's own tools |
| Each target | [RG2002], and [RG2006] if it is claimed | Lake's targets and the claim |
| The run | [RG2001] | The result of the load |

## The open issues of the epic

None of these issues closes before the change that replaces it lands. The rule entries above give the issues that a rule supersedes. This table gives each issue that the epic lists.

| Issue | Fate |
| --- | --- |
| [#477], [#475], [#474], [#473], [#464], [#422], [#411], [#359], [#425] | Superseded by [#483], which removes the observation of elaboration, options and messages. A gap that no input can show is an accepted risk of [RG2003] or [RG2006]. |
| [#472], [#471], [#469] | Superseded by [#482]. [RG2003] goes to `lake build --wfail`, and its entry records the messages that Lean or code drops. |
| [#468], [#462] | Superseded by [#484]. `RG2007` refuses the macros of a claimed module. |
| [#295] | Superseded by [#484]. [RG2006] refuses plugins and dynamic libraries on a claimed target. |
| [#441] | Superseded by [#483]. The loader refuses a read that fails, as [RG2001] states. |
| [#281] | Superseded by [#483] for initializers, because the shell loads no extension state. Lake's load still elaborates a `lakefile.lean`, which is project code. That part stays an accepted risk. |
| [#478], [#455], [#394], [#461] | Superseded by [#486], which removes the result files, the worker processes and the filesystem code. The closed types of [#487] carry the difference between absence and failure. |
| [#388] | Partly superseded by [#486], which removes the process starts of the checker. The part about the scripts of acceptance stays open in [#388]. |
| [#447] | Partly superseded by [#486], which removes the campaigns. The part about the drivers of acceptance stays open in [#447]. |
| [#434] | Not superseded. It is about the builder of the rule-reference site, which the epic does not change. It stays open as its own work. |
| [#391], [#380] | Superseded by [#486] and [#488], which remove the campaigns. The margin of each check that remains stays a criterion. |
| [#381] | Not superseded. The 420-second limit of each acceptance step stays, and the self-check makes the first step longer. It stays open until acceptance is in its limit after [#487]. |
| [#309] | Superseded by [#482]. `lake check` of `v4.35.0` takes its role in the gate, and `--paranoid` stays optional. |

## Regula's check of its own library

The self-check runs inside local acceptance, the gate before each merge. It is not a separate diagnostic that no gate runs. Since 2026-10-28, the owner's decision makes the local validation, not CI, the merge gate of Regula. The test step of that validation runs the local gate, `lean --run lean/Regula/DiagnosticsGate.lean local`, and its steps include the two acceptance commands of [`AGENTS.md`](../AGENTS.md).

- Regula's manifest claims each library of its root package, except a library that it excludes with a reason. The core and the shell of the checker are claimed.
- Regula registers its own admission decisions with two-way contracts. [RG1008] keeps the one-way kinds for adopters.
- The first acceptance command, `./scripts/verify.sh`, runs the three commands of the gate on Regula's own package. It refuses the change when a command fails or the checker gives a finding.
- Each claimed library of Regula is a default target of its root package ([RG2002]). Today plain `lake build` there builds no `Regula` library, so that list changes.
- This step is in the 420-second limit of the first command. **Open**: Regula's modules import Lean, so the export of `lake check` holds all of Lean. Its cost is not measured. Leaf [#482] measures it against the limit.

This placement removes the cause of [#489]. There, a refusal of the self-audit reached `main`, because no gate ran the self-audit for a pull request after the CI and Diagnostics workflows stopped. **Open**: until [#487] lands, the present self-audit must run inside acceptance in the same way. That is the change that the fix of [#489] makes.

The first acceptance command also builds the Lean package of this specification with warnings as errors. Thus the merge gate checks its statements before each merge.

- Default provisioning keeps a full Git clone of lean-intent in `.lake/regula-provision/lean-intent` (`RegulaProvision.provisionSpecification`). It reads the source and the commit from `lake-manifest.json` with Lake's own reader. The repository of lean-intent is public, so the clone uses no credentials under Regula's Git isolation.
- The clone is not the checkout in Lake's packages directory. Lake `v4.35.0` makes that one a partial clone with `--filter=tree:0` (`Lake/Util/Git.lean:160-170` at `v4.35.0`), and a partial clone cannot give its commits to a further fetch.
- The first step builds the package in its copy of the project (`RegulaVerification.specificationBuild`). Lake fetches the pinned commit from the provisioned clone, so the step reads no network. The theorem `ordinary_builds_specification` places the build among the commands that run in order. A failure of one of them fails the step.
- **Measured** on `v4.35.0`, with each Git protocol but `file` refused: the fetch from a full clone gave the pinned commit. The fetch from Lake's partial checkout failed with `bad tree object`.

## The Mathlib integration package

Regula's own package uses no Mathlib. Only the package in `integration/mathlib/`, a Mathlib adopter that the gate's Mathlib step builds, requires Mathlib. It ties each move of the toolchain to a Mathlib release. Today it is the only check of three behaviours. These are the Mathlib linter set that [RG2006] requires, foundation labels through Mathlib's constants, and the observation of Mathlib's syntax and tactics.

- **Fate**: retired with leaf [#484], which removes the last rule with behaviour of its own for Mathlib.
- After the leaves, no kept rule has a branch for Mathlib. [RG1001] to [RG1005] read the axiom sets of loaded constants, and the constants of Mathlib are constants like the others. Leaf [#483] removes the observation of elaboration. The Mathlib linter requirement of [RG2006] goes to written guidance.
- The members of the two allowlists of [#484] stay related to Mathlib. `RG2007` refuses an extension that its list does not name, and [RG2006] refuses an option that its list does not name. So a Mathlib attribute such as `to_additive`, or a Mathlib option such as `weak.linter.mathlibStandardSet`, is usable in claimed code only if the list names it. That is data, not a branch of a rule. **Open**: [#484] fixes those members from an observation of a real Mathlib project, and records it.
- Acorn is a Mathlib project, and its gate runs Regula. Thus Acorn then checks the same integration on real code. **Accepted risk**: a change of Regula that breaks a Mathlib project fails Acorn's gate when Acorn takes the change, not Regula's merge gate.
- **Open**: the cost of `lake check` on an export that holds Mathlib is not measured. Leaf [#482] measures it on Acorn.

## Decisions of this specification

These decisions change what the leaves build. Each has its reason.

- [RG1001] also reports the axiom of a native proof. A name-based exception would let an author name an axiom so that no rule reports it.
- Axioms come from the constants, not from the recorded table. The present standard already refuses that table (§7.4), and the input loads no extension state.
- A recursion helper is identified by its form, and the regeneration of its base goes away. A helper is not logical evidence. Its behaviour is a question of execution, which [RG3002] decides when a claim asks for it.
- [RG2006] reads only Lake's configuration. No record of an option in source exists (**measured**).
- The input is a list of environments, one for the libraries and one for each executable root. A single environment would refuse each project with two executables.
- An input with no claimed target is `incomplete`. Only a nonempty claim can pass.
- Under a checked execution claim, code that no theorem can bind fails [RG3002]. A theorem cannot discharge it, as the present standard says of `extern` in §7.6.
- The requirements of `linter.missingDocs` and of Mathlib's standard linters go to written guidance with the documentation rules. They guard failures that are cheap to see and correct.
- A decision registration becomes a declaration, so that a claimed module uses no tool module and no attribute that Lean does not define.
- The target toolchain is `v4.35.0`, and Regula moved to it in [#494], before the leaves. Its `lake check` replays each constant in scope from an export, in a process that loads no `.olean` file of the project. It also bounds each axiom by the standard three. The `leanchecker` of `v4.34.1` with a module list did less.
- Each claimed target is a default target, because `lake check` takes no module list and checks the default targets.
- `--paranoid` is optional, because the owner trusts Lean's kernel and its cost is not measured.
- On macOS, the gate runs `lake check --inadvisably-no-sandbox`. The sandbox requires Linux, and a virtual machine on the owner's Mac is a service of the machine that no task starts.
- `lake comparator` has no role in the gate, because the gate has no challenge. **Open**: it can serve the check of `RG6001` that a project proves each consequence that the owner confirmed. Leaf [#485] and [lean-intent#5] decide.

## The trusted base

These statements stay assumed after the leaves. Each is a statement about a system that no proof of Regula examines.

- Lean's kernel, elaborator, compiler and runtime, and Lake's load and build. The owner trusts Lean and its kernel.
- `Lean.importModules` with `loadExts := false` loads exactly the constants of the `.olean` files, and `collectAxioms` then walks their bodies.
- `lake check` exports and replays the modules that the first command built, and no process changes the build between the commands of the gate. On macOS, `lake check` runs without its sandbox.
- The shell finds the toolchain's own library only below the pinned toolchain, and Lean refuses an `.olean` file of a different Lean version.
- Compiled code follows the kernel value of a constant, except at a runtime replacement or a recursion helper.
- Lake's load gives each module that it builds, and its elaboration of a `lakefile.lean` is honest code.
- The code of a claimed module is honest code: it runs no command that changes messages, options or entries of an admitted extension. `RG2007` cannot see such a command.
- The meta-code of a dependency is honest code, as the present standard states.

The axiom sets and the kernel replay read only the constants of the build. Thus the statement about the code of a claimed module can make a hygiene check wrong, or a claim of execution false. It cannot make an unsound proof of a claimed module pass. The cause is that `lake check` replays each constant in scope from its export, and refuses each axiom beyond the standard three. The other statements stay part of the trusted base of soundness.

## Consequences for the owner's confirmation

The owner confirmed each consequence below on 2026-10-29, with each recommendation of the review ([the confirmation record](confirmation.md)). Each answer becomes a requirement that later revisions of this document keep.

What the specification requires:

- Each claimed theorem depends only on the axioms of its profile. Under choice-free, a theorem proved with `propext` passes, and a theorem proved with `Classical.em` fails [RG1005].
- A claimed module declares no `axiom`, also one that nothing uses [RG1001]. No claimed proof uses `sorry` [RG1002] or `native_decide` [RG1004].
- A claimed module declares nothing unsafe or partial. A `partial def loop` fails [RG1006]. A structural recursive definition passes, with the helper that Lean adds.
- A claimed module has no macro, `notation`, `syntax`, `elab`, `initialize` or attribute of its own (`RG2007`). Such code can be in an excluded library, but a claimed module cannot import that library [RG2004]. Thus a project cannot use its own notation in claimed code. Notation of a dependency, such as Mathlib's, stays usable.
- A claimed target sets `autoImplicit` and `relaxedAutoImplicit` to `false`, sets only options of the allowlist, and loads no plugin [RG2006].
- A decision function is registered by a declaration, not by `@[regula_decision]`. This changes the interface for adopters.
- The owner's committed confirmation record names the deliverables of a project. Each has an intent record and the proofs of `RG6001`, among them lean-intent's O2 before a run and its degenerate check. A deliverable that the record names and the project lacks fails, and so does a project with no record.
- The record does not reach its implementation. The owner's record, not the build, carries the order of confirmation and implementation.
- A cycle of runtime replacements, such as `f` replaced by `g` and `g` by `f`, fails [RG3001].
- A pass of the gate requires all three commands of Lean `v4.35.0`: `lake build --wfail`, `lake check`, and the checker.
- Each claimed target is a default target of the root package [RG2002]. A claimed library that plain `lake build` does not build fails.
- A claim of no target gives `incomplete`, not a pass.
- Under `execution: checked`, an executable that reaches `@[extern]` code, a `partial def` that is not a recursion helper, or a value that `initialize` sets fails [RG3002]. No theorem changes that.
- Regula, lean-intent and Acorn move to Lean `v4.35.0` before the leaves start, each in a change of its own. The moves of lean-intent and Regula have landed, and Acorn moves next.
- Regula passes its own check inside its first acceptance command.

What it allows:

- `set_option maxHeartbeats 400000 in` before a claimed theorem passes, because no rule reads options in source. `set_option linter.unusedVariables false` in source also passes, and its warnings do not appear.
- `#eval` and `run_cmd` in a claimed module pass, and no rule sees them. This is an accepted risk. Its refusal would require a second input, which reads the commands with Lean's parser.
- Tactics and notation of dependencies, and attributes on the allowlist such as `@[simp]`, pass.
- A claimed declaration with no docstring passes, and a broken Lean example in Markdown documentation passes. These are written guidance now.
- On macOS, `lake check` runs with `--inadvisably-no-sandbox` and prints that the run is not trustworthy. The code of the project then runs outside a sandbox, as it does in `lake build`.
- A gate with only Lean's own kernel passes. `--paranoid`, which adds five more kernels, is optional.

What it rules out:

- The observation of elaboration, messages, info trees and options in source.
- Worker processes, result files, scratch copies and removal of files by the checker.
- The regeneration of the base of a recursion helper with Lean's compiler.
- The qualification campaigns of the present checker. Each rule has proved cases in their place.

What it leaves unsaid:

- The members of the two allowlists, which [#484] fixes.
- The exact correspondence statement of each kind of execution boundary, which [#487] fixes.
- How a project declares a deliverable, and how the owner's confirmation record is made: [#485], [lean-intent#3] and [lean-intent#5].
- The cost of `lake check` and of `--paranoid` on an export that holds all of Lean, which [#482] measures.

[#281]: https://github.com/rbeauchamp/regula/issues/281
[#295]: https://github.com/rbeauchamp/regula/issues/295
[#309]: https://github.com/rbeauchamp/regula/issues/309
[#359]: https://github.com/rbeauchamp/regula/issues/359
[#380]: https://github.com/rbeauchamp/regula/issues/380
[#381]: https://github.com/rbeauchamp/regula/issues/381
[#388]: https://github.com/rbeauchamp/regula/issues/388
[#391]: https://github.com/rbeauchamp/regula/issues/391
[#394]: https://github.com/rbeauchamp/regula/issues/394
[#411]: https://github.com/rbeauchamp/regula/issues/411
[#422]: https://github.com/rbeauchamp/regula/issues/422
[#425]: https://github.com/rbeauchamp/regula/issues/425
[#434]: https://github.com/rbeauchamp/regula/issues/434
[#441]: https://github.com/rbeauchamp/regula/issues/441
[#447]: https://github.com/rbeauchamp/regula/issues/447
[#455]: https://github.com/rbeauchamp/regula/issues/455
[#461]: https://github.com/rbeauchamp/regula/issues/461
[#462]: https://github.com/rbeauchamp/regula/issues/462
[#464]: https://github.com/rbeauchamp/regula/issues/464
[#468]: https://github.com/rbeauchamp/regula/issues/468
[#469]: https://github.com/rbeauchamp/regula/issues/469
[#471]: https://github.com/rbeauchamp/regula/issues/471
[#472]: https://github.com/rbeauchamp/regula/issues/472
[#473]: https://github.com/rbeauchamp/regula/issues/473
[#474]: https://github.com/rbeauchamp/regula/issues/474
[#475]: https://github.com/rbeauchamp/regula/issues/475
[#477]: https://github.com/rbeauchamp/regula/issues/477
[#478]: https://github.com/rbeauchamp/regula/issues/478
[#480]: https://github.com/rbeauchamp/regula/issues/480
[#481]: https://github.com/rbeauchamp/regula/issues/481
[#482]: https://github.com/rbeauchamp/regula/issues/482
[#483]: https://github.com/rbeauchamp/regula/issues/483
[#484]: https://github.com/rbeauchamp/regula/issues/484
[#485]: https://github.com/rbeauchamp/regula/issues/485
[#486]: https://github.com/rbeauchamp/regula/issues/486
[#487]: https://github.com/rbeauchamp/regula/issues/487
[#488]: https://github.com/rbeauchamp/regula/issues/488
[#489]: https://github.com/rbeauchamp/regula/issues/489
[#494]: https://github.com/rbeauchamp/regula/pull/494
[lean-intent#2]: https://github.com/rbeauchamp/lean-intent/issues/2
[lean-intent#3]: https://github.com/rbeauchamp/lean-intent/issues/3
[lean-intent#5]: https://github.com/rbeauchamp/lean-intent/issues/5
[RG1001]: https://rbeauchamp.github.io/regula/dev/rules/RG1001/
[RG1002]: https://rbeauchamp.github.io/regula/dev/rules/RG1002/
[RG1003]: https://rbeauchamp.github.io/regula/dev/rules/RG1003/
[RG1004]: https://rbeauchamp.github.io/regula/dev/rules/RG1004/
[RG1005]: https://rbeauchamp.github.io/regula/dev/rules/RG1005/
[RG1006]: https://rbeauchamp.github.io/regula/dev/rules/RG1006/
[RG1007]: https://rbeauchamp.github.io/regula/dev/rules/RG1007/
[RG1008]: https://rbeauchamp.github.io/regula/dev/rules/RG1008/
[RG1009]: https://rbeauchamp.github.io/regula/dev/rules/RG1009/
[RG2001]: https://rbeauchamp.github.io/regula/dev/rules/RG2001/
[RG2002]: https://rbeauchamp.github.io/regula/dev/rules/RG2002/
[RG2003]: https://rbeauchamp.github.io/regula/dev/rules/RG2003/
[RG2004]: https://rbeauchamp.github.io/regula/dev/rules/RG2004/
[RG2005]: https://rbeauchamp.github.io/regula/dev/rules/RG2005/
[RG2006]: https://rbeauchamp.github.io/regula/dev/rules/RG2006/
[RG3001]: https://rbeauchamp.github.io/regula/dev/rules/RG3001/
[RG3002]: https://rbeauchamp.github.io/regula/dev/rules/RG3002/
[RG4001]: https://rbeauchamp.github.io/regula/dev/rules/RG4001/
[RG4002]: https://rbeauchamp.github.io/regula/dev/rules/RG4002/
[RG4003]: https://rbeauchamp.github.io/regula/dev/rules/RG4003/
[RG4004]: https://rbeauchamp.github.io/regula/dev/rules/RG4004/
[RG5001]: https://rbeauchamp.github.io/regula/dev/rules/RG5001/
[RG5002]: https://rbeauchamp.github.io/regula/dev/rules/RG5002/
[RG5003]: https://rbeauchamp.github.io/regula/dev/rules/RG5003/
