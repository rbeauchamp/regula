# Specification of the smaller Regula

This document specifies the smaller, stricter Regula that the epic [#480] asks for. Issue [#481] asks for it before any code changes. For each rule of Regula's registry, it gives one fate: kept, handed to Lean, or retired. It also specifies two new rules and the one input that all rules read. It gives the fate of each open issue that the epic lists, and how Regula checks its own library.

The owner confirms the plain-word consequences of this document before the leaves [#482] to [#488] start. Until a leaf changes it, the [standard](https://rbeauchamp.github.io/regula/dev/standard/) keeps its present text, and the present checker keeps its present behaviour. This document changes no rule.

## How to read this document

Each claim has one of four marks:

- **Proved**: Lean checks a theorem of the Lean package in this directory. The theorem name follows the mark.
- **Measured**: an observation on the pinned toolchain. The procedure follows the mark, so that a reader can do it again.
- **Assumed**: a statement about Lean, Lake or the operating system that no proof here examines. The leaf that builds on it must prove it or keep it as a named assumption.
- **Open**: an obligation that this document does not discharge, with the work that discharges it.

A statement of what a rule or the checker must do is specification, and it has no mark. The marks are for claims about Lean, Lake, the build and the theorems of the package.

The pinned toolchain is `leanprover/lean4:v4.34.1` (`lean-toolchain`). A citation such as `Lean/Util/CollectAxioms.lean:146-151` is a path below `src/lean/` of that tag, with its lines. A citation that starts with `src/` is a path below the root of that tag.

The formal statements are in the Lean library `RegulaSpecification` in this directory. The library requires the port of lean-intent at commit `61faee20a441894cce5420850796ee355c3c53b1`, which is the head of [lean-intent pull request 8](https://github.com/rbeauchamp/lean-intent/pull/8). That pull request is not merged. The library also requires the root package, for the closed rule identity `Regula.RuleId` only. To check all statements and theorems, use `lake build` in this directory.

## The shape of a rule

Each kept or new rule is a pure function from the closed input to the subjects that it reports. Its formal statement is a lean-intent intent record (`LeanIntent.IntentRecord`), built by `ruleRecord` in [`RegulaSpecification/RuleRecord.lean`](RegulaSpecification/RuleRecord.lean). The subject of the record is the function. The record has one property: on each well-formed input, the function reports a subject exactly when the subject violates the rule. Thus the meaning of a rule is all in its violation predicate, for example `Violates1005`.

For each rule, the package gives a case that the rule must refuse and a case that it must admit (`Witnessed`). From them, it proves these facts about the record of the rule:

- lean-intent's obligations O2 (at confirmation and before a run), O3, O4, and O5 with the freedom `SameReports`. **Proved**: `adequate`, applied in `rg1001_adequate` and the theorems that follow it.
- The function that reports nothing does not meet the record. **Proved**: `silent_fails`.
- The function that reports each candidate does not meet the record. **Proved**: `noisy_fails`, applied in `rg1001_noisy` and the theorems that follow it.

The freedom `SameReports` is what each record leaves unsaid. It is the order and the repetition of the reported subjects, and the result on an input that the admission refuses. O1 holds for each record. **Proved** by lean-intent: `LeanIntent.o1_wellTyped`.

The lean-intent port does not yet state three obligations. These are the cone check ([lean-intent#2]), the consequence ledger ([lean-intent#3]) and the owner's confirmation record ([lean-intent#5]). **Open**: for each record of this document, these three obligations wait for those issues.

## The verdict

A run of the checker gives one of three verdicts: `pass`, `fail` or `incomplete` (`Verdict` in [`RegulaSpecification/Gate.lean`](RegulaSpecification/Gate.lean)). The record `gateRecord` states the verdict:

- A build that Lean could not load is `incomplete`. This is [RG2001].
- An input that the admission refuses is `incomplete`. Missing evidence is not read as an empty set.
- A well-formed input is not `incomplete`. It passes exactly when all kept and new rules hold of it (`AllHold`).

**Proved**: `gate_o5`. Two verdict functions that meet the record are equal, so the record leaves nothing unsaid about the verdict.

A pass of the project's gate is the result of three commands on one finished build:

1. `lake build --wfail` for the claimed targets.
2. `lake env leanchecker` with each claimed module as an argument.
3. The checker of Regula over the finished build.

The checker starts none of these processes. The project's local gate or its CI runs the three commands in sequence on one checkout. **Assumed**: no process changes the build between the three commands. The checker gives the list of claimed modules for the second command, so that no module list is written by hand.

## The closed input

The closed input is the type `Input` in [`RegulaSpecification/Input.lean`](RegulaSpecification/Input.lean). Each field is one of these four parts, and each part comes from the owner of its data:

| Part | Owner and interface |
| --- | --- |
| The root package's targets, with the modules, options and extra Lean arguments of each target | Lake's own load of the workspace |
| The claim: the classification of each target | `foundation_manifest.json`, a closed format that Regula defines |
| Each module of the root package that Lake builds: its imports and the names of the environment extensions with entries in its `.olean` files | `Lean.readModuleDataParts` |
| Each constant of the environment that the import of these modules loads | `Lean.importModules` with `loadExts := false` |

The input has no source text, message, info tree, option set in source, build log or list of files. A rule does not decide what it cannot read in this input. This is the boundary of the input.

The admission refuses an input that does not have the closed form (`Input.WellFormed`). These are the conditions:

- Each name is the name of one constant.
- Each constant that a constant mentions is loaded.
- Each module that Lake gives for a target is loaded.

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
- Kernel replay is a tool of the toolchain.
  - `leanchecker` is in `bin/` of the toolchain, and its source is `LeanChecker.lean`.
  - It replays the new constants of each module that an argument names into the environment of its imports, at `LeanChecker.lean:12-33` and `91-113`. An argument also selects each module that has it as a prefix.
  - With no argument, it checks only the modules below the package name of `lake-manifest.json` with an uppercase first letter, at `LeanChecker.lean:38-52`. Thus the gate gives each claimed module as an argument.
  - It does not check axioms.
  - **Assumed**: each item about `leanchecker` is from its source, and no proof here examines it.
- A warning fails the build with `--wfail`.
  - The option sets the level that fails the build to `warning`, at `Lake/CLI/Main.lean:288`. A job fails when its log has an entry of that level, at `Lake/Build/Run.lean:125`.
  - A build that Lake does not do again replays its saved log, at `Lake/Build/Common.lean:242-257`. Thus a cached warning also fails the build.
  - Lake sees only a message that Lean logs.
  - **Assumed**: each item about `--wfail` is from the source of Lake, and no proof here examines it.
- `Lean.findSysroot` can find a toolchain that is not the pinned one. **Measured**: a program started with the pinned `lean --run` found the search path of an unpinned toolchain through `findSysroot`. Thus the shell takes the toolchain from Lake's load, not from `findSysroot`.

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
| [RG2005] | Handed to Lean: `lake env leanchecker` | No statement of Regula |
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

#### [RG1001]: project axioms

- **Fate**: kept. Leaf: [#487].
- **Intent**: a claimed module declares no logical axiom. An assumption is a hypothesis or a field of a structure, so that each theorem that uses it shows it in its type.
- **Domain**: each constant of a claimed module.
- **Input**: the kind of each constant and its module.
- **Formal statement**: `Violates1001`. A constant of a claimed module with the kind `axiom` violates the rule. The axiom of a native proof is included, and [RG1004] also reports the constants that use it.
- **Accepted risks**: none in addition to the risks of the input.
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
- **Formal statement**: `Violates1004`, with `NativeProofAxiom` and `compilerAxioms`. At the pinned toolchain, `native_decide`, `decide +native` and `bv_decide` add an ordinary axiom with the name `<declaration>._native.<tactic>.<suffix>` (`Lean/Meta/Native.lean:37-90`). **Assumed** from that source. **Proved**: `rg1005_of_compiler`.
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
- **Intent**: the execution closure of each claimed executable contains only constants of the input. Thus no account of execution leaves out a path.
- **Domain**: each name in the execution closure of the `main` of a claimed executable.
- **Input**: the constants, their runtime replacements and the recursion helpers.
- **Formal statement**: `Violates3001`, with `Input.Executes`. Compiled code runs the replacement of a constant if it has one. Else it runs the helper if there is one, else the constants that the value mentions.
- **Accepted risks**: the admission already requires each mentioned constant to be loaded. Thus the rule can fail only for a replacement that names an absent constant. **Assumed**: compiled code follows the kernel value of a constant, except at a replacement or a helper. Leaf [#487] keeps this as a named assumption.
- **Supersedes**: none.

#### [RG3002]: execution boundaries

- **Fate**: kept. Leaf: [#487].
- **Intent**: under a checked execution claim, each boundary that the closure reaches has a theorem of a claimed module that states its correspondence. A boundary is a runtime replacement, an `extern` constant or a recursion helper outside the toolchain.
- **Domain**: each boundary in the execution closure of a claimed executable with the execution mode `checked`.
- **Input**: the closure, the boundaries and the statements that theorems of claimed modules prove.
- **Formal statement**: `Violates3002`, with `Input.Boundary` and `Goal.corresponds`.
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
- **Intent**: the claim classifies each target of the root package exactly one time and names no target that Lake does not have. It classifies an executable as each library that contains its root module.
- **Domain**: each target that Lake gives or that the claim names.
- **Input**: Lake's targets and the claim.
- **Formal statement**: `Violates2002`.
- **Accepted risks**: **Open**: the reader of `foundation_manifest.json` accepts only the text that its writer gives for a claim. Leaf [#487] proves this of the reader, as for the present format.
- **Supersedes**: none.

#### [RG2003]: a warning-free build

- **Fate**: handed to Lean, as `lake build --wfail` for the claimed targets. Leaf: [#482].
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

- **Fate**: handed to Lean, as `lake env leanchecker` with each claimed module as an argument. Leaf: [#482].
- **Intent**: Lean's kernel checks each constant of each claimed module again from the build. Thus no code can add a constant that the kernel did not check.
- **Domain**: each claimed module.
- **Input**: none of Regula. The checker gives the list of claimed modules for the command.
- **Formal statement**: none of Regula. The property is `leanchecker`'s (see "What the input can show").
- **Accepted risks**: the modules of dependencies are not replayed. Their own builds checked them. The pinned Lake has no `check` command, and `Lake/CLI/` has no `Check.lean`. Issue [#309] records that Lean 4.35 adds `lake check --paranoid`, which replays with more kernels and stays optional. **Assumed**: `leanchecker` reads the same `.olean` files as the checker.
- **Supersedes**: [#309]. Its recommendation goes to Lean's own replay and axiom tools. It closes with [#482].

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
- **Accepted risks**: a command that runs code (`#eval`, `run_cmd`, `run_elab`, `run_meta`) leaves no record (**measured**), so the rule cannot see it. If such code changes constants, `leanchecker` and the axiom sets find it. If it removes messages, `--wfail` does not see them. If it changes entries of an admitted extension, such as compiled code, a claim of execution can be false. 
- **Open**: the owner can ask to close this gap. Then the checker reads the commands of each claimed module with Lean's parser, and refuses a command outside a closed set. That is a second input, which this design leaves out.
- **Supersedes**: [#468] and [#462] close with [#484], because a claimed module can no longer declare their macros.

#### `RG6001`: the obligations of each deliverable

- **Fate**: new. Leaf: [#485].
- **Intent**: for each deliverable that a project declares, theorems of claimed modules prove five things. The intent record exists, and lean-intent's obligations O1 to O5 hold of it. It does not reach its implementation, and it keeps each consequence that the owner answered. The implementation fulfils it.
- **Domain**: each declared deliverable: an implementation and its intent record.
- **Input**: the declared deliverables, the statements that theorems of claimed modules prove, and the owner's confirmation record.
- **Formal statement**: `Violates6001`, with `IntentPart.Fails`. A finding names the deliverable and the part that fails.
- **Accepted risks**: lean-intent does not yet state three parts. Here the independence is the approximation "the record does not reach the implementation". `Goal.keeps` and the field `confirmed` stand for what [lean-intent#3] and [lean-intent#5] define. **Open**: [#485] uses lean-intent's own statements when they exist, and a project declares a deliverable in the form that lean-intent gives.
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
| [#309] | Superseded by [#482]. Lean's own replay and axiom tools take its role, and `lake check` stays optional. |

## Regula's check of its own library

The self-check runs inside local acceptance, the gate before each merge. It is not a separate diagnostic that no gate runs. Since 2026-10-28, the owner's decision makes the local validation, not CI, the merge gate of Regula. The test step of that validation runs the two acceptance commands of [`AGENTS.md`](../AGENTS.md).

- Regula's manifest claims each library of its root package, except a library that it excludes with a reason. The core and the shell of the checker are claimed.
- The first acceptance command, `./scripts/verify.sh`, runs the three commands of the gate on Regula's own package. It refuses the change when a command fails or the checker gives a finding.
- This step is in the 420-second limit of the first command.

This placement removes the cause of [#489]. There, a refusal of the self-audit reached `main`, because no gate ran the self-audit for a pull request after the CI and Diagnostics workflows stopped. **Open**: until [#487] lands, the present self-audit must run inside acceptance in the same way. That is the change that the fix of [#489] makes.

The Lean package of this specification is not yet in acceptance, because it requires a commit of lean-intent that is not on lean-intent's `main`. **Open**: when the port of lean-intent merges, a change moves the pin to that merge. The same change adds `lake build` of this package to the first acceptance command.

## Decisions of this specification

These decisions change what the leaves build. Each has its reason.

- [RG1001] also reports the axiom of a native proof. A name-based exception would let an author name an axiom so that no rule reports it.
- Axioms come from the constants, not from the recorded table. The present standard already refuses that table (§7.4), and the input loads no extension state.
- A recursion helper is identified by its form, and the regeneration of its base goes away. A helper is not logical evidence. Its behaviour is a question of execution, which [RG3002] decides when a claim asks for it.
- [RG2006] reads only Lake's configuration. No record of an option in source exists (**measured**).
- The requirements of `linter.missingDocs` and of Mathlib's standard linters go to written guidance with the documentation rules. They guard failures that are cheap to see and correct.
- A decision registration becomes a declaration, so that a claimed module uses no tool module and no attribute that Lean does not define.
- The checker gives the list of claimed modules for `leanchecker`, because `leanchecker` with no argument checks only the modules below the package name.

## The trusted base

These statements stay assumed after the leaves. Each is a statement about a system that no proof of Regula examines.

- Lean's kernel, elaborator, compiler and runtime, and Lake's load and build. The owner trusts Lean and its kernel.
- `Lean.importModules` with `loadExts := false` loads exactly the constants of the `.olean` files, and `collectAxioms` then walks their bodies.
- `leanchecker` reads the same `.olean` files as the checker, and no process changes the build between the commands of the gate.
- The shell finds the toolchain's own library only below the pinned toolchain, and Lean refuses an `.olean` file of a different Lean version.
- Compiled code follows the kernel value of a constant, except at a runtime replacement or a recursion helper.
- Lake's load gives each module that it builds, and its elaboration of a `lakefile.lean` is honest code.
- The code of a claimed module is honest code: it runs no command that changes messages, options or entries of an admitted extension. `RG2007` cannot see such a command.
- The meta-code of a dependency is honest code, as the present standard states.

The axiom sets and the kernel replay read only the constants of the build. Thus the statement about the code of a claimed module can make a hygiene check wrong, or a claim of execution false. It cannot make an unsound proof of a claimed module pass. The cause is that `leanchecker` replays each constant of that module against the `.olean` files of its imports. The other statements stay part of the trusted base of soundness.

## Consequences for the owner's confirmation

The owner confirms or declines each consequence below before the leaves start. Each answer becomes a requirement that later revisions of this document keep.

What the specification requires:

- Each claimed theorem depends only on the axioms of its profile. Under choice-free, a theorem proved with `propext` passes, and a theorem proved with `Classical.em` fails [RG1005].
- A claimed module declares no `axiom`, also one that nothing uses [RG1001]. No claimed proof uses `sorry` [RG1002] or `native_decide` [RG1004].
- A claimed module declares nothing unsafe or partial. A `partial def loop` fails [RG1006]. A structural recursive definition passes, with the helper that Lean adds.
- A claimed module has no macro, `notation`, `syntax`, `elab`, `initialize` or attribute of its own (`RG2007`). Such code can be in an excluded library, but a claimed module cannot import that library [RG2004]. Thus a project cannot use its own notation in claimed code. Notation of a dependency, such as Mathlib's, stays usable.
- A claimed target sets `autoImplicit` and `relaxedAutoImplicit` to `false`, sets only options of the allowlist, and loads no plugin [RG2006].
- A decision function is registered by a declaration, not by `@[regula_decision]`. This changes the interface for adopters.
- Each declared deliverable has an intent record and the proofs of `RG6001`.
- A pass of the gate requires all three commands: `lake build --wfail`, `lake env leanchecker` with each claimed module, and the checker.
- Regula passes its own check inside its first acceptance command.

What it allows:

- `set_option maxHeartbeats 400000 in` before a claimed theorem passes, because no rule reads options in source. `set_option linter.unusedVariables false` in source also passes, and its warnings do not appear.
- `#eval` and `run_cmd` in a claimed module pass, and no rule sees them.
- Tactics and notation of dependencies, and attributes on the allowlist such as `@[simp]`, pass.
- A claimed declaration with no docstring passes, and a broken Lean example in Markdown documentation passes. These are written guidance now.

What it rules out:

- The observation of elaboration, messages, info trees and options in source.
- Worker processes, result files, scratch copies and removal of files by the checker.
- The regeneration of the base of a recursion helper with Lean's compiler.
- The qualification campaigns of the present checker. Each rule has proved cases in their place.

What it leaves unsaid:

- The members of the two allowlists, which [#484] fixes.
- The exact correspondence statement of each kind of execution boundary, which [#487] fixes.
- How a project declares a deliverable, and how the owner's confirmation record is made: [#485], [lean-intent#3] and [lean-intent#5].
- If the commands that run code in a claimed module must be refused too. That requires a second input, which reads the commands with Lean's parser.

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
