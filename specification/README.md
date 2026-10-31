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

The formal statements are in the Lean library `RegulaSpecification` in this directory. The library requires lean-intent at commit `30fe70d3bdeec8875eab718f38374a76a1df63c4` on lean-intent's `main`. That commit comes after [lean-intent pull request 8](https://github.com/rbeauchamp/lean-intent/pull/8), the port of lean-intent to intent records. The library also requires the root package, for the closed rule identity `Regula.RuleId` only. To check all statements and theorems, use `lake build --wfail` in this directory.

## The target toolchain

The smaller Regula targets Lean `v4.35.0`, the stable release of 2026-10-12. Its tools do the work of the rules that go to Lean (see "What Lean v4.35.0's tools do").

- Regula, lean-intent and Acorn move to `v4.35.0` together, because a Lean package and its dependents build with one toolchain. A Regula on a newer toolchain than lean-intent or Acorn cannot be their dependency or their dependent.
- The move is a change of its own in each repository: lean-intent first, then Regula, then Acorn. It lands before the leaves [#482] to [#488] start.
- lean-intent moved in [lean-intent pull request 12](https://github.com/rbeauchamp/lean-intent/pull/12), and Regula in [#494]. This package pins lean-intent at commit `30fe70d3bdeec8875eab718f38374a76a1df63c4` of its `main`, on `v4.35.0`.
- At `v4.35.0` the toolchain declares no axiom by which the kernel trusts the compiler, so `compilerAxioms` is empty ([RG1004]).
- **Open**: the observations of "What the input can show" are on `v4.34.1`. The leaf that builds on an observation repeats it on `v4.35.0`.

## The shape of a rule

Each kept or new rule is a pure function from the closed input to the subjects that it reports. Its formal statement is a lean-intent intent record (`LeanIntent.IntentRecord`), built by `ruleRecord` in [`RegulaSpecification/RuleRecord.lean`](RegulaSpecification/RuleRecord.lean). The subject of the record is the function. The record has one property: on each well-formed input, the function reports a subject exactly when the subject violates the rule. Thus the meaning of a rule is all in its violation predicate, for example `Violates1005`.

For each rule, the package gives a case that the rule must refuse and a case that it must admit (`Witnessed`). From them, it proves these facts about the record of the rule:

- lean-intent's obligations O2 (at confirmation and before a run), O3, O4, and O5 with the freedom `SameReports`. **Proved**: `adequate`, applied in `rg1001_adequate` and the theorems that follow it.
- The function that reports nothing does not meet the record. **Proved**: `silent_fails`.
- The function that reports each candidate does not meet the record. **Proved**: `noisy_fails`, applied in `rg1001_noisy` and the theorems that follow it.

The freedom `SameReports` is what each record leaves unsaid. It is the order and the repetition of the reported subjects, and the result on an input that the admission refuses. O1 holds for each record. **Proved** by lean-intent: `LeanIntent.o1_wellTyped`.

lean-intent now provides the cone check (`LeanIntent.Cone`) and the consequence answers (`LeanIntent.Answers`). **Open**: the records of this document do not yet use them. **Open**: the link to the owner's confirmation record ([lean-intent#5]) stays open for [#485].

## The verdict

A run of the checker gives one of three verdicts: `pass`, `fail` or `incomplete` (`Verdict` in [`RegulaSpecification/Gate.lean`](RegulaSpecification/Gate.lean)). The record `gateRecord` states the verdict:

- A build that Lean could not load is `incomplete`. This is [RG2001].
- An input that the admission refuses is `incomplete`. Missing evidence is not read as an empty set.
- A well-formed input is not `incomplete`. It passes exactly when all kept rules and [RG2007] hold of each of its environments, and `RG6001` holds of the bundle (`Bundle.AllHold`).

**Proved**: `gate_o5`. Two verdict functions that meet the record are equal, so the record leaves nothing unsaid about the verdict.

A pass of the project's gate is the result of three commands of the target toolchain on one finished build:

1. `lake build --wfail` for the claimed targets.
2. `lake check`. On macOS it is `lake check --inadvisably-no-sandbox` (see [RG2005]).
3. The checker of Regula over the finished build.

The checker starts none of these processes. The project's local gate or its CI runs the three commands in sequence on one checkout. **Assumed**: no process changes the build between the three commands. `lake check` takes no module list. It checks the modules of the default targets of the root package, so [RG2002] refuses a claimed target that is not a default target.

`lake check` imports those modules into one environment, at `Lake/CLI/Main.lean:1218-1226` of `v4.35.0`. Lean refuses two imported modules that declare one name with different values, at `Lean/Environment.lean:2336-2344` of `v4.35.0`. So a project fails `lake check` when its default targets declare one name two times, such as the `main` of two programs. With [RG2002], a project can thus claim at most one module that declares a top-level `main`. This limit holds until Lake loads each executable root in an environment of its own, as the shell does. It was decided on the owner's behalf in [#482].

**Measured** at `v4.35.0` with `lake check --inadvisably-no-sandbox`:

- A package of two default libraries that each declare `main` stopped with `import B failed, environment already contains 'main' from A`.
- Regula before [#482] stopped with `import RegulaProvision failed, environment already contains 'main' from RegulaVerification`.

## The closed input

The closed input is the type `Input` in [`RegulaSpecification/Input.lean`](RegulaSpecification/Input.lean). Each field is one of these five parts, and each part comes from the owner of its data:

| Part | Owner and interface |
| --- | --- |
| The root package's targets, with the modules, options and extra Lean arguments of each target | Lake's own load of the workspace |
| The claim: the classification of each target | `foundation_manifest.json`, a closed format that Regula defines |
| Each module of the root package that Lake builds: its imports and the names of the environment extensions with entries in its `.olean` files | `Lean.readModuleDataParts` |
| Each constant of each environment that the shell loads, with the modules it imports | `Lean.importModules` with `loadExts := false` |
| The compiled code of each constant: the constants that it runs, and the points where it departs from the kernel value | The build's compiled code. **Open**: leaf [#487] gives the mechanism that reads it, and leaf [#483] the input that carries it. |

The input has no source text, message, info tree, option set in source, build log or list of files. A rule does not decide what it cannot read in this input. This is the boundary of the input.

One environment cannot hold the `main` of two executables, because Lean refuses a constant that two imported modules declare. So the shell loads the libraries in one environment, and the root of each executable with its imports in an environment of its own. The input of a run is that list of environments (`Bundle` in [`RegulaSpecification/Gate.lean`](RegulaSpecification/Gate.lean)). Each environment has the same targets, claim, module records and owner's record.

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
  - At `v4.35.0` the same holds. Only `finalizePersistentExtensions` builds the state of an extension, and only with `loadExts`, at `Lean/Environment.lean:2404` and `2428-2433` of `v4.35.0`. `collectAxioms` reads the recorded table only through that state, at `Lean/Util/CollectAxioms.lean` of `v4.35.0`.
  - **Measured** in [#482]. On Regula's build, `collectAxioms` and a walk of the mentioned constants gave the same axiom set to each constant that the rules read. This held for all 61,476 such constants in 9 environments.
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

The registry of Regula has 25 rules (`Regula.RuleId`). The function `fate` in [`RegulaSpecification/Fates.lean`](RegulaSpecification/Fates.lean) gives each of them one fate. Lean examines that the match is exhaustive. Thus a rule that the registry adds or removes stops the build of this package until the table changes.

**Proved**: `fate_counts`. Of the 25 rules, 16 are kept, 2 go to Lean and 7 are retired. [RG2007] entered the registry with [#484]. The other new rule has the proposed identifier `RG6001`, which no rule of the registry has (**proved**: `new_not_registered`).

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
| [RG2007] | New, in the registry since [#484] | `rg2007`, `Violates2007` |
| [RG3001] | Kept | `rg3001`, `Violates3001` |
| [RG3002] | Kept | `rg3002`, `Violates3002` |
| [RG4001] to [RG4004] | Retired | No statement |
| [RG5001] to [RG5003] | Retired | No statement |
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
- **Input**: the flags `isUnsafe` and `isPartial`, the kinds, the names, the modules, and the runtime replacement and `extern` marks of the constants.
- **Formal statement**: `Violates1006`, with `Input.RecursionHelper`. A helper is a partial constant `f._unsafe_rec`, not unsafe, with no `implemented_by` replacement. It is in the module of a safe, total definition `f` with no `implemented_by` replacement. Lean makes the base of a `partial def` an opaque constant, so the rule reports the helper of a `partial def`.
- **Accepted risks**: the rule identifies a helper by its form, not by what it computes. A helper is not logical evidence, because Lean's kernel refuses a safe constant that mentions a partial one, at `src/kernel/type_checker.cpp:114-115`. What a helper computes is a question of execution, which [RG3002] decides under a checked execution claim. The regeneration of the base that the present standard requires, in §7.4, goes away with its code in [#486].
- **Supersedes**: none.

#### [RG3001]: the execution closure resolves

- **Fate**: kept. Leaf: [#487].
- **Intent**: the execution closure of each claimed executable contains only constants of the input, and no cycle of departures. Thus no account of execution leaves out a path, and each path ends in a definition.
- **Domain**: each name in the execution closure of the `main` of a claimed executable.
- **Input**: the constants, and the compiled code of each: the constants that it runs and its departures.
- **Formal statement**: `Violates3001`, with `Input.Executes` and `Input.DepartsTo`. The closure follows the constants that the build's compiled code runs (`Decl.compiled`), not the kernel values. A departure (`Departure`) is a point where compiled code runs a constant in place of the constant that the kernel value has.

  A runtime replacement, a `@[csimp]` rewrite at a call site, local or global, and a recursion helper each give one. A constant on a cycle of departures to different constants violates the rule, because the cycle runs no definition. **Proved**: `rg3001_refuses_cycle`.
- **Accepted risks**: the admission requires each constant that a kernel value mentions to be loaded, but not each constant that compiled code runs. So the rule fails for compiled code that runs an absent constant. **Assumed**: the executable runs the code compiled from the code that the build records. **Open**: leaf [#487] gives the mechanism that reads compiled code, and leaf [#483] the input that carries it. **Open**: the compiler adds auxiliary definitions, such as specializations, that are not constants of the environment. Leaf [#487] counts their code as code of the constant that they serve.
- **Supersedes**: none.

#### [RG3002]: execution boundaries

- **Fate**: kept. Leaf: [#487].
- **Intent**: under a checked execution claim, each boundary that the closure reaches has a correspondence. A boundary is a departure that no module of the toolchain makes, or code outside the toolchain that no theorem can bind. A correspondence counts only when its theorem is safe and the profile of the claim admits each axiom of the theorem.
- **Domain**: each constant in the execution closure of a claimed executable with the execution mode `checked`.
- **Input**: the closure, the departures and flags of each constant, and each statement that a theorem proves, with the theorem and its axioms.
- **Formal statement**: `Violates3002`, with `Input.BoundaryAt`, `Input.Corresponds`, `Input.AdmittedProof` and `Input.Unbindable`. A `@[csimp]` lemma states `@f = @g`, which is the correspondence of the departure that it makes. Code that no theorem can bind fails the rule with any theorem. It is an `extern` constant, a partial definition that is not a recursion helper, or a value that `initialize` sets. **Proved**: `rg3002_refuses_extern`, `rg3002_refuses_csimp_extern`, `rg3002_refuses_unsafe_proof` and `rg3002_refuses_unadmitted_proof`.
- **Accepted risks**: an unsafe theorem is not evidence, because the exporter of `lake check` skips unsafe constants (`LeanExport/Basic.lean:59` and `255` at `v4.35.0`). Lean registers an unsafe `@[csimp]` lemma too (`Lean/Compiler/CSimpAttr.lean:68` at `v4.35.0`), so the rule requires a safe theorem. **Assumed** from those sources.

  **Assumed**: the executable runs the code compiled from the code that the build records, as for [RG3001]. **Open**: the exact correspondence statement for each kind of departure, for example the recursion equation of a helper. Leaf [#487] gives these statements.
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
- **Decision**: a registration is a declaration of a type of Regula's interface, read as a constant. An attribute is code that a tool module defines, and [RG2007] and [RG2004] do not let a claimed module use one. So [#484] gives the declaration its form: `theorem f_registered : Regula.RegisteredDecision @f := ⟨⟩`, read from its type (`Regula.Load.registrationOf`).
- **Supersedes**: none.

#### [RG1009]: shared Boolean tests

- **Fate**: kept. Leaf: [#487].
- **Intent**: the specification of a decision contract states its meaning in other terms than the code. Thus it reaches no Boolean test outside the toolchain that the implementation or the acceptance predicate also reaches.
- **Domain**: each decision contract of a claimed module.
- **Input**: the contract, the constants that each constant mentions, the result type of each constant, and if it is a field's projection function.
- **Formal statement**: `Violates1009`, with `Input.ProjectTest`. A field's projection function is not a Boolean test: it reads a field of data, which no definition computes.
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
- **Decision**: `--paranoid` is optional. The owner trusts Lean's kernel, and the gate requires that kernel. A project can add the five other kernels. The export of a module that imports Lean holds all of Lean, as Regula's does.
- **Measured** in [#482] on 2026-10-29, one run on the owner's Mac. `lake check --paranoid --inadvisably-no-sandbox` did not finish in 45 minutes for a package of one module that imports Lean. `leanchecker-paranoid` and `lean4lean` accepted the 164,014 declarations of the export. `nanoda` was still running when the limit stopped it. The process tree held at most 14.0 GB resident. So `--paranoid` cannot be a required part of a 420-second acceptance step.
- **Accepted risks**: Regula's acceptance runs `lake check --inadvisably-no-sandbox` on each platform, as the decision below records. The build and the export run outside a sandbox, as `lake build` does. The trusted base already holds that code honest, so the soundness argument does not change. A constant with an internal name that no exported constant mentions is not replayed, and it is part of no proof of an exported constant. **Assumed**: the build of `lake check` gives the modules that the first command built.
- **Supersedes**: [#309]. Its recommendation goes to `lake check` of `v4.35.0`. It closes with [#482].

#### [RG2006]: the configuration of claimed targets

- **Fate**: kept, with less scope. Leaf: [#484].
- **Intent**: each claimed target turns automatic implicits off and sets only options of a closed allowlist. It loads no plugin and no dynamic library, and it gives Lean no other argument.
- **Domain**: each claimed target.
- **Input**: the options and the extra Lean arguments that Lake gives for each target.
- **Formal statement**: `Violates2006`, for the allowlist `allowed`. **Proved**: `rg2006_adequate`, for each allowlist that contains the two options of automatic implicits. The rule also refuses each entry of `autoImplicit` or `relaxedAutoImplicit` with a value other than `false`, at any position. **Proved**: `rg2006_refuses_override`. The strict options followed by `autoImplicit` set to `true` violate the rule.
- **The executed rule**: `Regula.Closed.Input.optionFindings`. These theorems are **proved** in [`RegulaSpecification/ClosedSubset.lean`](RegulaSpecification/ClosedSubset.lean):
  - `rg2006_exact`: it reports a target exactly when `Violates2006` holds of it, for each allowlist.
  - `rg2006_meets`: it meets the record `rg2006` at the members that the checker runs with.
  - `rg2006_allowlist_adequate`: the obligations of that record.
  - `run_pass_holds`: a pass of `Regula.Closed.run` holds the rule of each environment.
  - `rg2006_refuses_extras`: it reports a claimed target with an extra argument, a plugin or a dynamic library.
- **The members**: `Regula.Allowlist.options`, which names each option with its reason. The list holds no option that can stop a default warning or a check of Lean at any value.
- **Decided on the owner's behalf** in [#484]: the allowlist checks a name and no value. Thus an option that one value turns off is refused at each value. So `linter.unusedVariables` is refused at `true` as well, which is its default and adds nothing. The same reason leaves out `exponentiation.threshold`, which the rule before this one accepted. Raising it stops a default warning.
- **Measured** on 2026-10-30, by reading Acorn's `lean/lakefile.lean` at `718d1d0`, a real Mathlib project. Acorn also sets some others, which it must remove to take this Regula. These are `linter.unusedVariables`, `linter.unnecessarySimpa` and `linter.deprecated`, each at its default `true`, and the extra argument `-j2` in `weakLeanArgs`.
- **Accepted risks**: an option that a source file sets leaves no record (**measured**), so the rule does not read it. A requirement of `linter.missingDocs` and of Mathlib's standard linters goes to written guidance with the documentation rules.
- **The read of the options**: that Lake's load gives each option and argument that Lake passes is **assumed** (`Regula.Load.targets`, `lean/Regula/Load.lean`). Lake `v4.35.0` merges the options of the build type, the package and the library, and the later value wins. The places are `Lean/Util/LeanOptions.lean:91-92` and `Lake/Config/LeanLib.lean:208-209`. The rule reads that merged map, the value that Lean receives.
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
| [RG5002] | Each public declaration that states a material claim has a docstring. Review selects these declarations. |
| [RG5003] | The docstring of each such declaration has a section `# Intent` that is not empty. Review checks this section. |

For each of the seven rules: the fate is retired, with leaf [#488]. There is no domain, no input and no formal statement after the leaf. The accepted risk is the failure that the rule found. The rules supersede the campaigns of documentation fences in [#391], which closes when [#486] and [#488] have landed.

### New rules

#### [RG2007]: a closed subset of the language

- **Fate**: new. Leaf: [#484].
- **Intent**: a claimed module registers no code that Lean runs while it elaborates. Thus it has no macro, elaborator, syntax, initializer, `meta` declaration or attribute that Lean does not define.
- **Domain**: each claimed module.
- **Input**: the names of the environment extensions that have entries in the `.olean` files of the module.
- **Formal statement**: `Violates2007`, for the allowlist `declarative`. `ClosedAllowlist` requires that the allowlist admits none of `metaExtensions`. **Proved**: `rg2007_refuses_meta`, and `rg2007_adequate` for each closed allowlist that admits `Lean.declRangeExt`.
- **The executed rule**: `Regula.Closed.Input.extensionFindings`. These theorems are **proved** in [`RegulaSpecification/ClosedSubset.lean`](RegulaSpecification/ClosedSubset.lean):
  - `rg2007_exact`: it reports a module exactly when `Violates2007` holds of it, for each allowlist.
  - `rg2007_meets`: it meets the record `rg2007` at the members that the checker runs with.
  - `allowlist_closed`: those members admit none of `metaExtensions`.
  - `rg2007_allowlist_adequate`: the obligations of that record.
  - `rg2007_checker_refuses_meta`: the checker refuses a claimed module with an entry of `metaExtensions`.
  - `coverage_refuses_tool_import`: it refuses a claimed module that imports a module of an excluded target, a tool module ([RG2004]).
- **The members**: `Regula.Allowlist.extensions`, which groups them with a reason for each group. A name that it does not name is refused, whatever it registers. So a Lean or Lake version with a different record is refused when the names differ. A version with the admitted names and a different meaning is stopped by the compiler guard of `lakefile.lean`. That guard refuses each Lean but the one this revision supports (`RegulaPolicy.Compiler`).
- **An empty record**: the shell refuses a module with no extension in its `.olean` files, and the verdict is `incomplete` (`Regula.Load.readModule`). **Measured**: each of the 9,019 modules below has entries of `Lean.deprecatedModuleExt` and of `Lean.modPkgExt`. So an empty record is a record of a different form, not a clean module.
- **Measured** on 2026-10-30 at `v4.35.0`. A Lean program read all parts of each `.olean` file with `Lean.readModuleDataParts`, and listed the names of the extensions with entries. It read 81 modules of Regula's build before this leaf, and 295 of Acorn's at `718d1d0`, a real Mathlib project. It also read 8,643 of Mathlib at `56a00585`, the commit that Acorn pins.
  - Regula had 54 names, Acorn 49 and Mathlib 202.
  - Each name of Acorn's outside Lean itself is of a Regula attribute that this leaf removes. These are `Regula.decisionExtension`, and `RegulaObserver.records` of the observer plugin that [#483] retired.
  - The five extensions of the observation at `v4.34.1` have these names at `v4.35.0`, and so do the ones of the command and tactic elaborators.
  - One module for each form showed its record. `notation`, `simproc` and a `meta def` each had an entry of `metaExt`. So did `local notation`, `local macro`, `local syntax`, `local macro_rules` and `local elab_rules`. `initialize` had an entry of `Lean.regularInitAttr`. So the rule refuses them.
  - A default of the form `:= by tactic`, on a binder or a field, also has an entry of `metaExt` (`Lean/Elab/Binders.lean:101` at `v4.35.0`). Lean runs that tactic at each use. So the rule refuses it, and Regula's own modules lost theirs.
  - Each member of the list was read at its declaration in that release's source. Its entries are data, and they name no code for Lean to run. The members for Mathlib and Batteries are data attributes that Acorn does not use and Mathlib's ordinary modules do. Each of them was read at its declaration at `56a00585`.
- **Feasibility**: settled. The registrations leave named entries (**measured**), and a name outside the allowlist is refused, an unknown name included. No claimed module can bring in an extension of its own. An extension exists only through an `initialize`, which the rule refuses, and [RG2004] refuses the import of a tool module.
- **Accepted risks**: two things leave no record, so the rule cannot see them.
  - A command that runs code (`#eval`, `run_cmd`, `run_elab`, `run_meta`) leaves no record (**measured**).
  - An attribute of local scope on an ordinary definition leaves no record: `@[local macro k]`, `@[local term_elab k]` or `@[local tactic k]` (**measured** on 2026-10-30). The first one changed what a term of its module elaborates to, in a file with no `import Lean`. The module had the entries of an ordinary one.
  - If such code changes constants, `lake check` and the axiom sets find it. If it removes messages, `--wfail` does not see them. If it changes entries of an admitted extension, such as compiled code, a claim of execution can be false.
- **Open**: the owner can ask to close this gap. Then the checker reads the commands of each claimed module with Lean's parser, and refuses a command outside a closed set. That is a second input, which this design leaves out.
- **Supersedes**: none. Each of [#468] and [#462] stays open. [RG2007] refuses the macros that they report (**measured**), but a local macro attribute on an ordinary definition reaches the same failure (**measured** on 2026-10-30). The module builds with no message about the redundant alternative, and no rule reports it.

#### `RG6001`: the obligations of each deliverable

- **Fate**: new. Leaf: [#485].
- **Intent**: the owner's committed confirmation record names the deliverables, not the project's code. For each one, theorems of claimed modules prove these things. The implementation and the intent record exist. The record meets lean-intent's obligations O1 to O5, O2 before a run and its degenerate check. It does not reach its implementation, and it keeps each consequence that the owner answered. The implementation fulfils it.
- **Domain**: each deliverable that the owner's record names: an implementation and its intent record, each by its module and its name. A project with no such record fails, so an empty inventory passes only when the record says so.
- **Input**: the owner's confirmation record, the statements that theorems of claimed modules prove, and the constants with their modules, in all environments of the bundle.
- **Formal statement**: `Violates6001`, with `IntentPart.Fails`. The rule checks the inventory over the bundle, and a part holds when an environment with the implementation in its named, claimed module satisfies it. Goals and consequences name constants by module and name too (`QualName`). A finding names the deliverable and the part that fails.

  **Proved**: `rg6001_refuses_no_record`, `rg6001_refuses_missing`, `rg6001_admits_split` and `rg6001_refuses_bare_evidence`. In the last two, two executables each have a `main`, and only the environment of each `main` gives its evidence.
- **Accepted risks**: lean-intent now provides the cone check (`LeanIntent.Cone`) and the consequence answers (`LeanIntent.Answers`), but the records of this document do not yet use them. Here the independence is the approximation "the record does not reach the implementation".

  `Goal.keeps` and the field `confirmed` stand for the consequence answers and the owner's confirmation record. **Open**: [#485] uses lean-intent's own statements, and the link to the owner's confirmation record ([lean-intent#5]) stays open for [#485]. That record also carries the order of the confirmation and the implementation, and the owner's act, which no build shows.
- **Supersedes**: none.

## The rules that apply to a declaration

For a constant of a claimed module, this table gives the rules that examine it and the input that decides each rule.

| Subject | Rules | Input that decides |
| --- | --- | --- |
| Each constant of a claimed module | [RG1002], [RG1003], [RG1004], [RG1005], [RG1006], and [RG1001] if its kind is `axiom` | Its kind, its transitive axiom set, the profile of its module, its flags and its marks |
| A theorem with the type `ExecutableContract f R` | [RG1007], and [RG1009] for a decision kind | The contract in its type, the constants that each constant mentions, and the Boolean tests |
| A registered decision function | [RG1008] | The registrations, the contracts and the result type |
| A constant in the execution closure of a claimed executable | [RG3001], and [RG3002] under a checked execution claim | The compiled code, its departures, and the theorems that prove each correspondence |
| The implementation of a declared deliverable | `RG6001` | The deliverables, the statements that theorems prove, and the owner's answers |
| Each claimed module | [RG2004], [RG2007], and Lean's [RG2003] and [RG2005] | Lake's modules, the imports, the extension names, and Lean's own tools |
| Each target | [RG2002], and [RG2006] if it is claimed | Lake's targets and the claim |
| The run | [RG2001] | The result of the load |

## The open issues of the epic

None of these issues closes before the change that replaces it lands. The rule entries above give the issues that a rule supersedes. This table gives each issue that the epic lists.

| Issue | Fate |
| --- | --- |
| [#477], [#475], [#474], [#473], [#464], [#422], [#411], [#359], [#425] | Superseded by [#483], which removes the observation of elaboration, options and messages. A gap that no input can show is an accepted risk of [RG2003] or [RG2006]. |
| [#472], [#471], [#469] | Superseded by [#482]. [RG2003] goes to `lake build --wfail`, and its entry records the messages that Lean or code drops. |
| [#468], [#462] | Not superseded. [RG2007] refuses the macros that they report, but a local macro attribute on an ordinary definition reaches the same failure, an accepted risk of [RG2007]. |
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
- This step is in the 420-second limit of the first command. Regula's modules import Lean, so the export of `lake check` holds all of Lean.
- **Measured** on 2026-10-29 on the owner's Mac with 14 cores, one run each, not a bound. `lake check --inadvisably-no-sandbox` took 97.5 s for a package of one module that imports Lean. The export of that package was 742 MB. It took 119 s for Regula's own package. Without it, the commands of the first step took 87 s on `main` at `98a0f9c`.
- Regula's default targets declare one `main`, that of `auditApp`. The two programs that run before the package is built are the acceptance driver and the provisioning driver. They are the modules `RegulaVerification.Driver` and `RegulaProvision.Driver` of claimed libraries, each with a namespaced entry. The files `lean/RegulaVerification.lean` and `lean/RegulaProvision.lean` are in no target. Each runs the source of its driver with `main` bound to its entry.

This placement removes the cause of [#489]. There, a refusal of the self-audit reached `main`, because no gate ran the self-audit for a pull request after the CI and Diagnostics workflows stopped. **Open**: until [#487] lands, the present self-audit must run inside acceptance in the same way. That is the change that the fix of [#489] makes.

The first acceptance command also builds the Lean package of this specification with warnings as errors. Thus the merge gate checks its statements before each merge.

- Default provisioning keeps a full Git clone of lean-intent in `.lake/regula-provision/lean-intent` (`RegulaProvision.provisionSpecification`). It reads the source and the commit from `lake-manifest.json` with Lake's own reader. The repository of lean-intent is public, so the clone uses no credentials under Regula's Git isolation.
- The clone is not the checkout in Lake's packages directory. Lake `v4.35.0` makes that one a partial clone with `--filter=tree:0` (`Lake/Util/Git.lean:160-170` at `v4.35.0`), and a partial clone cannot give its commits to a further fetch.
- The first step builds the package in its copy of the project (`RegulaVerification.specificationBuild`). Lake fetches the pinned commit from the provisioned clone, so the step reads no network. The theorem `ordinary_builds_specification` places the build among the commands that run in order. A failure of one of them fails the step.
- **Measured** on `v4.35.0`, with each Git protocol but `file` refused: the fetch from a full clone gave the pinned commit. The fetch from Lake's partial checkout failed with `bad tree object`.

## The Mathlib integration package

Regula's own package uses no Mathlib. Before [#484], the package in `integration/mathlib/`, a Mathlib adopter that the gate's Mathlib step built, required Mathlib. It tied each move of the toolchain to a Mathlib release. It was also the only check of three behaviours. These were the Mathlib linter set that [RG2006] required, foundation labels through Mathlib's constants, and the observation of Mathlib's syntax and tactics.

- **Fate**: retired by [#484], which removed the package, its command, its gate step, its CI job and its provisioning. No rule has behaviour of its own for Mathlib.
- After the leaves, no kept rule has a branch for Mathlib. [RG1001] to [RG1005] read the axiom sets of loaded constants, and the constants of Mathlib are constants like the others. Leaf [#483] removes the observation of elaboration. The Mathlib linter requirement of [RG2006] goes to written guidance.
- The members of the two allowlists stay related to Mathlib. [RG2007] refuses an extension that its list does not name, and [RG2006] refuses an option that its list does not name. So a Mathlib attribute such as `to_additive`, or a Mathlib option such as `weak.linter.mathlibStandardSet`, is usable in claimed code only if the list names it. That is data, not a branch of a rule. The members and the observation of a real Mathlib project are recorded in the entries of [RG2006] and [RG2007].
- Acorn is a Mathlib project, and its gate runs Regula. Thus Acorn then checks the same integration on real code. **Accepted risk**: a change of Regula that breaks a Mathlib project fails Acorn's gate when Acorn takes the change, not Regula's merge gate.
- **Measured** in [#482] on 2026-10-29, one run on the owner's Mac, not a bound. The modules of the Mathlib integration package import Mathlib's real analysis and topology, at the Mathlib revision that Acorn pins. `lake check --inadvisably-no-sandbox` of that package passed in 229 s. Its process tree held at most 4.1 GB resident. Acorn itself was not measured. Before it can take this Regula, it must remove the observer plugin, make each claimed target a default target and claim one program at most.

## Decisions of this specification

These decisions change what the leaves build. Each has its reason.

- [RG1001] also reports the axiom of a native proof. A name-based exception would let an author name an axiom so that no rule reports it.
- Axioms come from the constants, not from the recorded table. The present standard already refuses that table (§7.4), and the input loads no extension state.
- A recursion helper is identified by its form, and the regeneration of its base goes away. A helper is not logical evidence. Its behaviour is a question of execution, which [RG3002] decides when a claim asks for it.
- [RG2006] reads only Lake's configuration. No record of an option in source exists (**measured**).
- The input is a list of environments, one for the libraries and one for each executable root. A single environment would refuse each project with two executables.
- An input with no claimed target is `incomplete`. Only a nonempty claim can pass.
- Under a checked execution claim, code that no theorem can bind fails [RG3002]. A theorem cannot discharge it, as the present standard says of `extern` in §7.6.
- The execution closure comes from the build's compiled code, not from kernel values and attributes. A local `@[csimp]` lemma changes the compiled code that follows it, but the build exports no entry of it (`Lean/ScopedEnvExtension.lean:96-104` and `191-198` at `v4.35.0`). **Assumed** from that source.
- A correspondence counts only when its theorem is safe and the profile of the claim admits its axioms. Lean registers an unsafe `@[csimp]` lemma too, as [RG3002] records.
- The requirements of `linter.missingDocs` and of Mathlib's standard linters go to written guidance with the documentation rules. They guard failures that are cheap to see and correct.
- A decision registration becomes a declaration, so that a claimed module uses no tool module and no attribute that Lean does not define.
- The target toolchain is `v4.35.0`, and Regula moved to it in [#494], before the leaves. Its `lake check` replays each constant in scope from an export, in a process that loads no `.olean` file of the project. It also bounds each axiom by the standard three. The `leanchecker` of `v4.34.1` with a module list did less.
- Each claimed target is a default target, because `lake check` takes no module list and checks the default targets.
- `--paranoid` is optional because the owner trusts Lean's kernel. The measurement in [RG2005] exceeded the acceptance deadline.
- On macOS, the gate runs `lake check --inadvisably-no-sandbox`. The sandbox requires Linux, and a virtual machine on the owner's Mac is a service of the machine that no task starts.
- A project can claim at most one module that declares a top-level `main`. The cause is that `lake check` imports the modules of the default targets into one environment, and [RG2002] makes each claimed target a default target. This keeps `lake check` in the gate and each claim, as the owner confirmed. Regula's two programs that run before its package is built keep their logic in claimed library modules, and files in no target launch them. Decided on the owner's behalf in [#482], 2026-10-29.
- Regula's first acceptance step runs `lake check --inadvisably-no-sandbox` on each platform. Outside Linux, `lake check` does not start without it. The CI provisioning of the step installs no `bwrap`, and the operator-approved bootstrap of CI does not cover it. The build and the export run outside a sandbox there, as the step's `lake build` does. Decided on the owner's behalf in [#482], 2026-10-29.
- `lake comparator` has no role in the gate, because the gate has no challenge. **Open**: it can serve the check of `RG6001` that a project proves each consequence that the owner confirmed. Leaf [#485] and [lean-intent#5] decide.

## The trusted base

These statements stay assumed after the leaves. Each is a statement about a system that no proof of Regula examines.

- Lean's kernel, elaborator, compiler and runtime, and Lake's load and build. The owner trusts Lean and its kernel.
- `Lean.importModules` with `loadExts := false` loads exactly the constants of the `.olean` files, and `collectAxioms` then walks their bodies.
- `lake check` exports and replays the modules that the first command built, and no process changes the build between the commands of the gate. On macOS, and in Regula's own acceptance on each platform, `lake check` runs without its sandbox.
- The shell finds the toolchain's own library only below the pinned toolchain, and Lean refuses an `.olean` file of a different Lean version.
- The executable runs the code compiled from the code that the build records.
- A departure that a module of the toolchain makes computes what the kernel value computes.
- Lake's load gives each module that it builds, and its elaboration of a `lakefile.lean` is honest code.
- The code of a claimed module is honest code. It runs no command that changes messages, options or entries of an admitted extension. It gives no local attribute that registers code. [RG2007] cannot see them.
- The meta-code of a dependency is honest code, as the present standard states.

The axiom sets and the kernel replay read only the constants of the build. Thus the statement about the code of a claimed module can make a hygiene check wrong, or a claim of execution false. It cannot make an unsound proof of a claimed module pass. The cause is that `lake check` replays each constant in scope from its export, and refuses each axiom beyond the standard three. The other statements stay part of the trusted base of soundness.

## Consequences for the owner's confirmation

The owner confirmed each consequence below on 2026-10-29, with each recommendation of the review ([the confirmation record](confirmation.md)). Each answer becomes a requirement that later revisions of this document keep.

What the specification requires:

- Each claimed theorem depends only on the axioms of its profile. Under choice-free, a theorem proved with `propext` passes, and a theorem proved with `Classical.em` fails [RG1005].
- A claimed module declares no `axiom`, also one that nothing uses [RG1001]. No claimed proof uses `sorry` [RG1002] or `native_decide` [RG1004].
- A claimed module declares nothing unsafe or partial. A `partial def loop` fails [RG1006]. A structural recursive definition passes, with the helper that Lean adds.
- A claimed module has no macro, `notation`, `syntax`, `elab`, `initialize` or attribute of its own ([RG2007]). Such code can be in an excluded library, but a claimed module cannot import that library [RG2004]. Thus a project cannot use its own notation in claimed code. Notation of a dependency, such as Mathlib's, stays usable.
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

- The members of the two allowlists, which `Regula.Allowlist` holds. [#484] fixed them, with the observation that the entries of [RG2006] and [RG2007] record. The owner's confirmation did not cover them.
- Two results of [RG2007] that [#484] measured, which the owner's confirmation did not cover. A local attribute that registers code on an ordinary definition passes, as `run_cmd` does. A default of the form `:= by tactic` in a claimed module fails.
- The exact correspondence statement of each kind of execution boundary, which [#487] fixes.
- How a project declares a deliverable, and how the owner's confirmation record is made: [#485], [lean-intent#3] and [lean-intent#5].
- The cost of `lake check` and of `--paranoid` on a machine other than the owner's Mac: [#482] measured each one time there.

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
[RG2007]: https://rbeauchamp.github.io/regula/dev/rules/RG2007/
[RG3001]: https://rbeauchamp.github.io/regula/dev/rules/RG3001/
[RG3002]: https://rbeauchamp.github.io/regula/dev/rules/RG3002/
[RG4001]: https://rbeauchamp.github.io/regula/dev/rules/RG4001/
[RG4002]: https://rbeauchamp.github.io/regula/dev/rules/RG4002/
[RG4003]: https://rbeauchamp.github.io/regula/dev/rules/RG4003/
[RG4004]: https://rbeauchamp.github.io/regula/dev/rules/RG4004/
[RG5001]: https://rbeauchamp.github.io/regula/dev/rules/RG5001/
[RG5002]: https://rbeauchamp.github.io/regula/dev/rules/RG5002/
[RG5003]: https://rbeauchamp.github.io/regula/dev/rules/RG5003/
