import VersoManual
import RegulaExample

open Verso.Genre Manual RegulaExample

#doc (Manual) "7. Tooling and Machine Audit" =>
%%%
tag := "7-tooling-and-machine-audit"
file := "7-tooling-and-machine-audit"
number := false
%%%

{pageAnchor}

# Overview
%%%
tag := "7-overview"
number := false
%%%

Modules 0–6 define the Lean properties a conforming development must have. This module defines the Lean-specific evidence needed to establish those properties: an exact elaboration environment, complete Lake module coverage, environment-level declaration inspection, exact axiom sets, and documentation examples that elaborate as printed (§7.7, which is written guidance). It also states what the commands of the gate and Regula's checker decide of that evidence. Semantic review remains necessary to establish that the checked statements express the intended claims.

A successful command establishes only the property it checks. In particular, an unextended `lake build` elaborates configured targets; it does not establish complete module coverage, absence of project axioms, a claimed foundation profile, or correctness of Markdown examples by itself.

*The gate.* A pass of a project's gate is the result of three commands of the pinned toolchain on one finished build, run in this order: `lake build --wfail` for the claimed targets ({rule}[RG2003]), `lake check` ({rule}[RG2005]) and Regula's checker, `lake lint`. The checker starts neither of the other two: the project's local gate or its CI runs the three in sequence on one checkout. That no process changes the build between them is assumed. On macOS the second command is `lake check --inadvisably-no-sandbox`, because `lake check` refuses to start there without it.

*The checker.* Regula's checker reads one closed input: the constants that Lean loads from the finished build, the targets and modules of Lake, and the claim ({repo "specification/README.md"}[the specification of the smaller Regula]). It has no source text, message, info tree, option set in source, build log or list of files, so no rule decides what only those show. Each rule that the specification keeps is a pure function of that input. The specification's package proves of each function that it reports a subject exactly when the subject violates the rule, under two hypotheses: the input has the closed form, and each axiom set that a rule reads is the one that the specification's `Input.AxiomOf` states. That the loader fills the input correctly from Lean and Lake is trusted.

A run gives one of three verdicts. It is `incomplete` (exit 2) when the build cannot be loaded or the input does not have the closed form ({rule}[RG2001]), so missing evidence is never read as an empty set. Otherwise it is `pass` (exit 0) when no rule reports a subject and `fail` (exit 1) when a rule does. The checker prints one line for each finding, with a link to its rule page, one line that counts what it read when it could load the build, and the verdict. Apart from Lake's own load of the workspace, which can run Git and write Lake's configuration directory for a `lakefile.lean`, it starts no process and writes or removes no file. It runs no initializer of the modules it loads, because it loads them without extension state.

# 7.1 Declare the Elaboration Environment
%%%
tag := "71-declare-the-elaboration-environment"
number := false
%%%

*Requirement*: Every conformance claim MUST name the exact Lean toolchain and exact dependency source state under which its source was elaborated.

* `lean-toolchain` MUST identify one exact Lean toolchain.
* Git dependencies MUST resolve to exact revisions in `lake-manifest.json`. For path dependencies or locally modified checkouts, the claim MUST also identify the source state used; a directory path or nominal Git revision alone does not identify modified contents.
* The reported environment MUST include `lean --version`, the claimed Lake library and executable targets, and the resolved Mathlib revision when Mathlib is present.
* A result obtained under another Lean or Mathlib revision is a result about that other elaboration environment. It MUST NOT be silently reused.

Parsing, elaboration, generated declarations, tactics, theorem names, and reduction behavior can change with the toolchain or dependencies. The checker reads the build that Lake's load gives with the toolchain of the Lake that runs it, and it prints no account of that environment, so whoever states the claim records it. Its results do not prove that a dependency checkout matches its recorded revision.

*Requirement*: Every claimed library and claimed executable MUST elaborate with the options `autoImplicit` and `relaxedAutoImplicit` set to `false`, as Mathlib's own build does, set in its Lake `leanOptions`. Its extra `lean` arguments (`moreLeanArgs` and `weakLeanArgs`) MUST NOT set either option to another value with `-D name=value`, which can override `leanOptions`. Each other option, in `leanOptions` or set by a `-D`, MUST be on the closed allowlist of {rule}[RG2006]. A claimed target MUST have no other extra argument, no plugin and no dynamic library, because each changes Lean's process. With automatic implicits, an unbound identifier in a declaration's signature becomes a universally quantified implicit argument that the source does not show. A misspelled name can then add a binder and change the quantifiers that a reviewer compares with the intent ({ref "52-faithful-explanation-of-formal-claims"}[module 5 §5.2]). With both options off, such an identifier is an elaboration error. {rule}[RG2006] checks both options, the allowlist, every extra argument, plugin and dynamic library, in Lake's resolved configuration of every claimed target; a `set_option autoImplicit true` command in source is outside that configuration, and review checks it (`DECL-01`). The elaborated declaration remains authoritative under either setting.

*Requirement*: A claimed module MUST register no code that Lean runs while it elaborates. It has no macro, syntax, elaborator, initializer, `meta` declaration or attribute of its own: {rule}[RG2007] reads the names of the environment extensions with entries in the module's `.olean` files, and refuses each name outside its closed allowlist. A module that defines such code is a tool module: its target is excluded from the claim, and a claimed module MUST NOT import it ({rule}[RG2004]).

Meta-code of a project can change what Lean elaborates and what it reports. Refusing what lies outside a closed set stops that where detecting it never converges. The meta-code of a dependency stays trusted, and its notation, tactics and data attributes stay usable. A default of the form `:= by tactic` is a `meta` declaration, because Lean runs that tactic at each use, so the rule refuses it too. A command that runs code, such as `#eval` or `run_cmd`, leaves no record, and neither does an attribute of local scope on an ordinary definition, such as `@[local macro k]`, so the rule cannot see them. If such code changes constants, kernel replay and the axiom sets find it; if it removes messages, the warning-free build does not see them.

# 7.2 Define Surfaces Through Lake Semantics
%%%
tag := "72-define-surfaces-through-lake-semantics"
number := false
%%%

*Requirement*: Claimed surfaces MUST be identified through Lake targets. Each surface of the manifest names one `lean_lib` in the root package and MAY claim `lean_exe` targets by target name. An executable claim includes its exact Lake-resolved root module, a standalone module such as `Main` or a module of the surface's own library such as `Lib.Cli`. The module inventory MUST come from Lake's load of the project, not a separately maintained file list or namespace-prefix search. Each surface names a library, so an executable-only package can be a valid Lean project but has no claim under this schema.

The checker loads the project's workspace through Lake's loader (`Lake.loadWorkspace`) and reads the root package's model directly: every `lean_lib` with its module array, every `lean_exe` with its root module, the Lean options, arguments, plugins and dynamic libraries of each, and which of them are default targets. Because the elaborated model is the same object Lake builds from, `lakefile.lean` and `lakefile.toml` projects take the identical discovery path, and no custom Lake facets or lakefile edits are required from an adopter beyond the lint driver (§7.8). To those modules the loader adds each module of the root package that their imports reach. A module belongs to the root package when its `.olean` file lies below the root package's library directory.

For a library `Lib`, Lake's built-in `modules` facet exposes a related view: it adds transitive imports that Lake assigns to that library. It equals the configured module array only when those imports are already covered. Do not treat the two views as interchangeable. The facet can be queried with:

```sh
lake query Lib:modules --json
```

Regula's checker decides these conditions:

1. A run is `incomplete` when the Lake workspace load or the manifest cannot be read or is malformed, when the claim claims no target, when a module of a target has no readable `.olean` file or is loaded in no environment, and when a constant mentions a constant that its environment does not hold ({rule}[RG2001]).
2. The claim classifies every root-package `lean_lib` and `lean_exe` exactly once, names no target that Lake does not have, classifies an executable as each library that contains its root module, and claims only default targets of the root package ({rule}[RG2002]).
3. Each module of the root package that Lake builds is in exactly one library, or in no library and the root of an executable, and no claimed module imports a module of an excluded target ({rule}[RG2004]).

Intentionally invalid fixtures MUST stay outside every positive library surface: a module of a claimed target is a claimed module.

A claimed target must be a default target because `lake check` checks only the modules of the default targets. `lake check` imports those modules into one environment, and Lean refuses two imported modules that declare one name. So a project whose default targets declare a name twice, such as the `main` of two programs, fails `lake check`, and a project can claim at most one module that declares a top-level `main`.

The surface manifest is JSON with exactly four top-level keys: `schema-version` (equal to `2`), `surfaces`, `excluded-libraries`, and `excluded-executables`. It lives at the checked project's root as `foundation_manifest.json`. The checker reads the workspace of its working directory, which must be the one Lake dispatched, or of the one directory given as its argument.

Each surface names one `library`, a foundation `claim`, and a `rationale`, MAY list claimed `executables` by `lean_exe` target name, and MAY set `execution` to `report` (the default) or `checked` (§7.6); each exclusion entry names the target and its `rationale`. The reader also accepts a `decides` list of the library names of other claimed surfaces and checks its form, and no rule reads it. Unknown keys, duplicates, a wrong schema version, an unknown `execution` value, an empty `surfaces` array, a blank rationale and a `decides` entry that names the surface itself or no claimed surface fail closed. A claim of `compiler-trusting` is not one of the closed input's profiles and makes the run `incomplete`. Empty exclusion arrays are valid for an adopter with nothing to exclude.

An executable's root module MAY belong to a library only when the manifest classifies the two alike: both are claimed with one profile and one execution mode, or both are excluded. Every other case is a {rule}[RG2002] finding: a claimed executable whose root belongs to an excluded library or to a library with another profile or mode, and an excluded executable whose root belongs to a claimed library.

Library globs are therefore load-bearing. If a project intends every module below `Lib` to be in scope, its Lake configuration must use a glob with that meaning, such as ``.andSubmodules `Lib``. An umbrella import alone is insufficient: a valid but unimported source file can otherwise be absent from both `lake build` and the declaration inventory.

Declaration ownership is the exact module index Lean records. A declaration name that begins with `Lib`, a module named `LibLookalike`, or a private/internal-looking name does not establish or remove ownership. A module is claimed when Lake lists it for a claimed target, whatever its name. A root-package module that a claimed module imports and no target lists is reported under {rule}[RG2004]. Exclusion records classify targets; they do not permit a claimed module to import an excluded module.

Declaration names are unique within one Lean environment; distinct environments may legitimately contain different declarations with the same name, including `main`. Lean refuses to import two modules that declare the same name. So the input of a run is a list of environments, each with its own constants. The loader imports the root of each executable, with that root's import closure, in an environment of its own, and the other library modules in as few environments as hold them, so that no environment imports two modules that declare one name. Each rule reads one environment at a time. Each environment has the same targets, claim and module records, and the admission requires each module of each target to be loaded in some environment.

# 7.3 Clean Elaboration and Diagnostics
%%%
tag := "73-clean-elaboration-and-diagnostics"
number := false
%%%

*Requirement*: Every module of a claimed target MUST elaborate from source with no error and no warning. Lean's own tool decides this: `lake build --wfail` for the claimed targets ({rule}[RG2003]). Regula's checker does not report the rule, and it reads no message of the build.

* The option sets the level that fails the build to `warning`, and a job fails when its log has an entry of that level. A build that Lake does not do again replays its saved log, so a cached warning also fails the build. Each statement of this item is read from Lake's source at the pinned toolchain. A build that reuses root-package artifacts therefore rests on Lake's traces; this standard requires no empty build directory.
* A source file cannot make its own warning disappear from `--wfail` by setting `warningAsError := false` locally, because the option sets the level that fails the build. Turning a linter off stops it from logging, which the build cannot see, and it does not discharge the semantic property the linter was intended to check. Lean's default warnings are never disabled on a claimed surface; a community linter, whether a dependency or the project enables it, may be disabled for a single declaration only as {ref "62-module-purpose-and-linter-discipline"}[module 6 §6.2] describes. The build's output does not show a disabled linter, so review checks the disables.
* Lake sees only a message that Lean logs. Lean itself drops some messages, and code that a claimed module runs can remove messages. Such a gap is an accepted risk of the {repo "specification/README.md"}[specification of the smaller Regula]: it can hide a warning, and it does not change what the kernel checks or what the axiom sets are.
* A claimed module MUST NOT run `#guard_msgs` or `#guard_panic`, whether its source, a macro or an elaborator produced the command: each drops, checks or replaces the messages of the command it runs, so a warning it handles never reaches the build's output, and Lean runs no linter on a command that contains `#guard_msgs`. Show an expected message in documentation or a test outside the claimed surface. No check of Regula reads this, because a command leaves no record in the input; review checks it.

{rule}[RG2006] refuses plugins and dynamic libraries in a claimed target's resolved Lake configuration. Its complete mechanical scope is the target configuration described in {ref "62-module-purpose-and-linter-discipline"}[§6.2]. It reads no source command, source option or message record. Review checks source options and the required community-linter settings.

*Assumes*: Lake's resolved configuration supplies the options and arguments that it passes to Lean. An option set in source, by `set_option`, `unlock_limits` or an elaborator's local scope, is outside that configuration and is not read by {rule}[RG2006]. The closed-subset checks of §7.1 refuse recorded meta-code; they do not establish that no unrecorded code changed elaboration or suppressed a message.

`lake build` remains necessary to elaborate source, run command elaborators and linters, and produce the `.olean` files used by later checks. Successful elaboration alone does not establish checked admission: metaprogramming APIs and local options can store unchecked declarations.

*Requirement*: Lean's kernel MUST check each constant of each claimed module again, from an export of the build, in a process that loads no `.olean` file of the project. Lean's own tool decides this: `lake check` ({rule}[RG2005]), and Regula's checker does not report the rule. Each claimed target is a default target (§7.2), and `lake check` covers the default targets. As read from Lake's source at the pinned toolchain, it builds them, exports each constant in scope whose name is not internal with the constants each one mentions, the dependencies' and the toolchain's included, and replays the export with `leanchecker --silent --from-export`. A constant with an internal name that no exported constant mentions is not replayed, and it is part of no proof of an exported constant. It also refuses each axiom other than `propext`, `Classical.choice` and `Quot.sound` that a constant of the export mentions. That list is fixed, and `lake check` gives no axiom set for each constant, so it decides no foundation profile and no rule of a finding (§7.5). That its build gives the modules the first command built is assumed.

`lake check --paranoid` adds the other kernels that the toolchain bundles. It is optional: a gate with only Lean's own kernel passes. With `--inadvisably-no-sandbox`, `lake check` runs its build and its export outside the sandbox it uses on Linux, as `lake build` does, and it prints that the run is not trustworthy. Neither command rechecks a dependency's source from nothing: dependency artifacts may be reused, and the export's replay is what checks their constants. This does not establish the semantic adequacy of any statement.

# 7.4 Inventory Every Owned Declaration
%%%
tag := "74-inventory-every-owned-declaration"
number := false
%%%

*Requirement*: A check of a declaration MUST read Lean's elaborated `Environment`, not source text. Regula's checker imports each environment with `Lean.importModules` and `loadExts := false`, and it holds one record for each constant that a rule can reach: every constant attributed to a claimed module, the `main` of each executable root, each theorem that states a correspondence (§7.6), and every constant that these mention or run. That the rules decide the same on this list as on every constant of the environment is argued, with no theorem. The checker prints findings, not this inventory.

Each record holds:

* exact declaration name and exact owning module, from Lean's module index;
* exhaustive `ConstantInfo` kind (`axiom`, theorem, definition, opaque definition, inductive, constructor, recursor, or quotient declaration), in a closed type with one constructor for each;
* the constants that its type and value mention;
* `noncomputable` metadata;
* `ConstantInfo.isUnsafe` and `ConstantInfo.isPartial` information;
* runtime replacement and external-code metadata (`@[implemented_by]`, `@[extern]`), and whether an initializer sets its value;
* the constants that its compiled code runs, with each point where that code departs from its kernel value (§7.6);
* whether its type's result is `Bool` or `BEq _` and it is no field's projection function, read from its kernel-checked value;
* whether its module's `.olean` file lies below the pinned toolchain's library directory; and
* for each constant of a claimed module and each theorem that states a correspondence, the exact transitive axiom set.

The checker computes each axiom set with `Lean.collectAxioms`. Lean's recorded table of each module's axioms (`exportedAxiomsExt`) is an extension's state, which `loadExts := false` leaves empty, so `collectAxioms` walks the types and values of the constants. That is read from Lean's source at the pinned toolchain, and on Regula's own build the sets agreed with a separate walk of the mentioned constants, one measurement that the specification records. A set that the loader did not compute makes the run `incomplete`, and it is never read as empty. `propext`, `Quot.sound` and `Classical.choice` name the toolchain's axioms only: a constant of one of those names from a module outside the toolchain's library is an unknown axiom ({rule}[RG1003]).

The policy applies to public, protected, private, internal-looking, authored, and generated declarations. A record's flags come from Lean's own constant data and attributes, which public metaprogramming APIs can synthesize. So an elaborator that writes them can change what a rule that reads them decides; the constants themselves are checked by `lake check` (§7.3).

Lean adds a partial code-generation helper `f._unsafe_rec` for a safe recursive `def` `f`. {rule}[RG1006] identifies it by its form: a partial, not unsafe constant named `f._unsafe_rec` with no runtime replacement or external marker, in the module of a safe, total definition `f` that has no runtime replacement or external marker. Every other unsafe or partial constant of a claimed module is reported. The rule does not establish what the helper computes. A helper is not logical evidence, because Lean's kernel refuses a safe constant that mentions a partial one. What it computes is a question of execution, which {rule}[RG3002] decides under a checked claim (§7.6). A metaprogram can add a constant of the helper's form; the kernel checks the definition of the base, and the helper's code is what runs.

A `partial def`, written by the author or generated by a deriving handler, is an opaque constant that Lean compiles through its partial helper. Its base is no definition, so its helper is no exception, and {rule}[RG1006] reports the helper. An unsafe `T.ctorIdx._impl` of a claimed module is an unsafe declaration like any other.

Missing evidence fails: a constant that the input does not hold and a constant mentions, a module of a target with no record, and a missing axiom set each make the run `incomplete` (§7.2). The names `f._unsafe_rec` and `._native.` select what {rule}[RG1006] and {rule}[RG1004] exempt or name, as those rules state; no other name, range or metadata waives a rule.

# 7.5 Proof Completeness and Foundation Strength
%%%
tag := "75-proof-completeness-and-foundation-strength"
number := false
%%%

*Requirement*: Every owned declaration MUST be checked for forbidden assumptions, and every declaration MUST stay within its surface's selected profile. Forbidden or compiler-trusting sets are rejected from conforming positive surfaces.

Each declaration has the least permissive of the labels Kernel-only, Choice-Free, and Standard-Logical ({ref "45-foundation-strength-kernel-only-choice-free-standard-logical"}[module 4 §4.5]) containing its exact axiom set. A surface’s selected profile is an upper bound and does not replace the per-declaration label. The checker decides the bound and prints no label; `#print axioms` shows a declaration's set.

Regula's checker reports, for each constant of a claimed module:

* a logical `axiom` declaration, whether or not another declaration depends on it ({rule}[RG1001], §3.4);
* `sorryAx` anywhere in a transitive axiom set, including uses introduced by `sorry` or `admit` ({rule}[RG1002]);
* an axiom outside `propext`, `Quot.sound` and `Classical.choice` of the toolchain that {rule}[RG1002] and {rule}[RG1004] do not name ({rule}[RG1003]);
* an axiom of a native proof ({rule}[RG1004]); and
* an axiom that a profile of its module does not admit ({rule}[RG1005]).

Each axiom that {rule}[RG1002], {rule}[RG1003] or {rule}[RG1004] names also violates {rule}[RG1005] for each profile, as the specification proves, so a wrong choice between those rules changes the rule of a finding and not the verdict.

The proof surface includes theorems and every definition or instance whose elaborated type is a proposition. A declaration of a proposition (`P : Prop`) defines a statement; a declaration whose type is `P` supplies evidence of it. Ordinary data and function definitions read the same rules and may not conceal project axioms, holes, unknown axioms, or forbidden computational mechanisms.

On the supported toolchain, `native_decide`, `decide +native`, and the `bv_decide` tactics (`bv_decide`, `bv_decide?`, `bv_check`, also in `grind =>` and `sym =>` mode) add an ordinary axiom through `Lean.Meta.nativeEqTrue`, named `<declaration>._native.<tactic>.<suffix>`. {rule}[RG1004] identifies such an axiom by that name form and reports each constant that depends on it, so a declaration of that kind is *compiler-trusting*. Compiler-trusting is not one of the three logical labels and is nonconforming on a kernel-checked positive surface. In a claimed module, {rule}[RG1001] also reports the axiom itself, and no name exempts it. An author can give an axiom that name; {rule}[RG1004] then reports it in place of {rule}[RG1003], and the verdict is the same. The rule also names each axiom of the toolchain by which the kernel trusts the compiler: the pinned toolchain declares none.

The trusted base of this boundary is listed in the {repo "specification/README.md#the-trusted-base"}[specification]. It assumes the pinned Lean process, Lake's load and build, and explicitly imported trusted libraries are not compromised. Arbitrary hostile trusted plugins or process compromise are out of scope. It holds the code of a claimed module to be honest code: a claimed module runs no command that changes messages, options or entries of an admitted extension, and it gives no local attribute that registers code, because {rule}[RG2007] cannot see them. Breaking that statement can make a hygiene check wrong or a claim of execution false. It cannot make an unsound proof of a claimed module pass, because the axiom sets and the kernel replay read only the constants of the build: `lake check` replays each constant in scope from its export and refuses each axiom beyond the standard three, and it refuses a declaration added with `debug.skipKernelTC` that the kernel does not accept. Compiler passes (`@[cpass]`), direct writes that store a compiled body Lean's compiler did not make, and native build settings (`extern_lib`, `moreLinkArgs`, `moreLeancArgs`) change compiled code that no step checks, so they remain trusted boundaries of the execution account (§7.6). Ordinary declarations, attributes such as `implemented_by`, `extern` and `csimp`, and `initialize` are in scope: §7.6 states how the execution account treats each of them.

## Explicit application contracts
%%%
tag := "explicit-application-contracts"
number := false
%%%

A complete executable component MUST encode its required behavioral propositions as proof requirements tied to the actual definitions through dependent result types, proof-bearing interfaces consumed by the application, or semantic checks against explicit expected propositions. Removing evidence while its requirement remains MUST fail elaboration or the gate. A trivial or weaker proposition cannot discharge the unchanged obligation. Existing construction, library proofs, and composition MAY discharge these requirements without a redundant theorem for every helper. A registered contract that no caller consumes through its proof-requiring interface is evidence whose requirement would disappear with it; a function the project registers as a decision keeps the requirement at the function, so removing its decision contract fails the gate ({ref "79-executable-contracts-and-decision-registrations"}[§7.9], {rule}[RG1008]).

The gate's build checks these explicit proof obligations and its checker rejects holes and forbidden axioms. It does not infer missing specifications from names, counts, or digests. Semantic review MUST still establish adequacy and completeness: all relevant roots and boundaries are covered, and the required propositions express the intended behavior, including admission, success and refusal, update, frame, and composition where those are part of the claim. Deleting or weakening the requirement itself, or changing the caller to bypass its interface, changes the specification or its application linkage and requires that review. A gate pass alone is not a contract-completeness verdict.

# 7.6 Classify Lean Computation Mechanisms Exactly
%%%
tag := "76-classify-lean-computation-mechanisms-exactly"
number := false
%%%

These mechanisms affect different Lean claims and MUST NOT be conflated:

:::table +header
*
  * Mechanism
  * Exact Lean consequence
  * Positive proof surface
*
  * ordinary terminating `def`
  * Lean accepts a kernel definition, with structural or well-founded termination justification when recursion requires it; code generation may add the internal helper described in §7.4
  * permitted, subject to its axioms and profile
*
  * `opaque` with a body
  * the body is kernel-checked but is not available to ordinary client reduction; it is not a logical axiom
  * permitted when the API claim matches that reduction boundary
*
  * `noncomputable`
  * records that Lean need not generate executable code for the declaration; it introduces no logical axiom by itself
  * permitted; an executable contract cannot name it ({rule}[RG1007])
*
  * `decide p` / `by decide`
  * `decide p` returns a `Bool` from a `Decidable p` instance; the tactic `by decide` constructs a proof when the decision reduces appropriately, without adding a native-proof axiom
  * permitted, subject to transitive axioms
*
  * `native_decide`, `decide +native`, `bv_decide` / native proof
  * executes compiled code and adds a generated axiom asserting the result used by the proof
  * compiler-trusting; banned ({rule}[RG1004])
*
  * `partial def`
  * supplies executable recursion without a kernel termination proof; the logical-facing declaration is an opaque constant whose compiled execution runs the generated partial helper
  * authored `partial` declarations are escape hatches: banned ({rule}[RG1006]); under a checked claim, partial computation outside the toolchain that `main` runs fails ({rule}[RG3002])
*
  * `unsafe def` / unsafe declaration
  * excluded from safe kernel definitions and checked proof terms; intended for compiled execution
  * authored unsafe declarations are escape hatches: banned ({rule}[RG1006])
*
  * `@[implemented_by]`
  * kernel reasoning uses the reference definition while compiled execution uses a different definition
  * permitted as an execution boundary: never an unconditional one-definition execution claim; under a checked claim, one outside the toolchain needs its correspondence ({rule}[RG3002])
*
  * `@[csimp]`
  * the pinned compiler substitutes a constant using an unconditional constant-equality declaration; kernel reduction is unchanged
  * prefer when this proof-backed form fits: the lemma is the correspondence of the departure it makes; every further execution boundary still counts
*
  * `@[extern]` / FFI
  * compiled execution calls external or runtime code whose behavior is not established by the Lean declaration alone
  * permitted as an execution boundary: an extern of a module of the toolchain's library, such as `Nat`/`Float32` arithmetic, is the toolchain's trusted base; under a checked claim, any other extern that `main` runs fails, whatever theorem exists ({rule}[RG3002])
*
  * `#eval` or native execution output
  * an observation from evaluation, not a proof term
  * never proof evidence
:::

*The toolchain's trusted base.* Lean's own libraries implement ordinary operations through these mechanisms: `Array.foldlM` runs an `unsafe` implementation through `@[implemented_by]`, `Nat.repr` runs `Nat.reprFast`, and `Std.BaseMutex.lock` is an extern. Such a boundary is the toolchain's, not the project's: the pinned toolchain installation and Lean process are already trusted under §7.5, and the checker attempts no proof that relates it to its reference. A constant is the toolchain's when the `.olean` file of its module, as Lean's search path finds it, lies below the pinned toolchain's library directory. A project or dependency module named `Init.Adopter` or `Lean.Adopter` does not become toolchain code by its name. A departure is the toolchain's when a module of that library makes it: any module can register a `@[csimp]` equality for a toolchain constant, and that departure is the module's. That Lean finds the toolchain's library only below that directory is assumed, and this check establishes nothing about the toolchain's own code.

The execution account, and so every execution claim, is the static closure below: the code `main` runs through compiled code. Code a program selects at runtime is data to that closure, not part of it: a constant it evaluates by name (`Lean.Environment.evalConst`, `Lean.Environment.evalConstCheck`), a dynamic library or plugin it loads, or a process it spawns (`IO.Process.spawn`). An `initialize` action that the code of `main` does not reach is outside it too. The toolchain primitive that runs such code is part of the toolchain's trusted base, so a checked claim establishes nothing about the code it runs.

Logical decidability, executable decidability, kernel reduction, code generation, and native execution are separate questions. Transfer of a property from a reference definition to a replacement requires the relevant relation, established by reduction or a checked proof. A theorem relating Lean definitions does not establish the behavior of external machine code; that boundary needs its own account.

## Execution roots and the closure
%%%
tag := "execution-roots-and-the-closure"
number := false
%%%

*Execution coverage is a distinct account from the logical audit.* The foundation labels of §7.5 are purely logical: a Standard-Logical pass never asserts execution correspondence. The root of a claimed executable is the `main` that Lake links, read in the environment that loads the executable's root module; a module that the root imports can declare it. An environment that loads a claimed executable's root and holds no `main` violates {rule}[RG3001]. That includes an executable whose `@[export main]` gives the symbol to a declaration of another name.

The closure of a claimed executable is the least set that contains `main` and the constants that the build's compiled code of each of its members runs, as Lean's store of compiled code gives them (`Lean.IR.findEnvDecl`, `Lean.IR.collectUsedDecls`). The closure follows compiled code, not kernel values. The compiler's auxiliary definitions, which are no constants of the environment, count as code of the constant they serve. A constant of the closure with no entry in that store, or whose entry is a stub of code that was not read, makes the run `incomplete`, and it is never read as a constant that runs nothing. That the executable runs the code compiled from the code that the build records is assumed.

A *departure* is a point where compiled code runs one constant in place of the constant that the kernel value has. The build records one as a constant's `@[implemented_by]`, its helper `f._unsafe_rec`, or a `@[csimp]` or `@[implemented_by]` entry with a target in the code that it runs. {rule}[RG3001] reports a name of the closure that is no constant of the input, and a constant on a cycle of departures to different constants, because such a cycle runs no definition. The rule applies under every execution mode.

## Boundaries and correspondence
%%%
tag := "boundaries-and-correspondence"
number := false
%%%

The compiler can inline, specialize or erase a call, so no read of compiled code shows that departure while the kernel values still mention the reference. Under a checked claim, the loader therefore records more departures on `main`: each replacement that a module outside the toolchain registers, and each recursion helper of a constant outside the toolchain, whose reference lies in the closure of `main` through the constants each constant mentions, the compiled code runs or a departure runs. A reference that only a proof mentions then also asks for a correspondence: a false refusal under a checked claim only, which a theorem discharges. A lemma with `attribute [local csimp]` has no entry in the build, so its rewrite lies in the closure as the code that runs and no departure asks for its correspondence.

A *boundary* is a departure that no module of the toolchain makes, or code outside the toolchain that no theorem can bind. Code that no theorem can bind is an `extern` constant, a partial definition that is not a recursion helper, or a value that `initialize` sets. Under a checked claim, {rule}[RG3002] reports the second kind with any theorem, and the first until it has a correspondence. An unsafe constant of a dependency that compiled code calls directly is neither: the trusted base holds a dependency's code honest, and an unsafe constant of a claimed module is {rule}[RG1006]'s.

A correspondence counts only when its theorem is safe and the profile of the claim admits each of its axioms, and it must be in a module that the environment of the executable loads, so the root must import it. It also holds at each instantiation of the constants that it relates:

* A runtime replacement `f` by `g`, or a global `@[csimp]` rewrite of `f` to `g`: a theorem `@f = @g`, whose two sides are constants with equal universe arguments that are distinct universe parameters. This is Lean's own condition for a constant replacement. `@ref.{u} = @fast.{u}` counts and `@ref.{0} = @fast.{0}` does not. A `@[csimp]` lemma is such a theorem.
* A recursion helper `f._unsafe_rec`: the recursion equation of `f`, a theorem `∀ xs, f xs = B`, where the value of the helper is `fun xs => B'` and `B` is `B'` with each helper replaced by its base. The universe arguments of `f` are exactly the level parameters of the helper, in order, and each binder of the helper's value has a binder of the statement, so a specialized or narrowed equation does not count. Lean's `f.eq_def` has this type, so a project states it by `theorem f_rec : type_of% @f.eq_def := @f.eq_def`. No theorem can state `@f = @f._unsafe_rec`, because the kernel refuses a safe constant that mentions a partial one. That the compiled code of `f` computes what `f` computes rests on the compiler.

A departure that a module of the toolchain makes is part of the toolchain's trusted base, and it needs no correspondence. Equality between Lean definitions does not discharge any extern reached through the replacement.

## Execution modes
%%%
tag := "execution-modes"
number := false
%%%

The execution claim of a surface has two modes:

* `report` (the default): the checker does not check boundaries. Only {rule}[RG3001] reads the closure. The checker prints no account of the boundaries, so this mode claims nothing about them.
* `checked` (a per-surface `"execution": "checked"` manifest key): every boundary that the closure of `main` reaches, in the environment of that executable, MUST have a correspondence that the claim's profile admits, and no constant of the closure outside the toolchain may be code that no theorem can bind ({rule}[RG3002]). Boundaries of the toolchain's trusted base remain permitted. They are the toolchain execution substrate under the §7.5 assurance boundary, not correspondence a source-level audit can discharge.

An unknown `execution` value makes the run `incomplete` (§7.2).

# 7.7 Check Lean Documentation Verbatim
%%%
tag := "77-check-lean-documentation-verbatim"
number := false
%%%

*Requirement*: Every Lean fence in a Markdown document of the normative documentation tree, including nested directories, MUST be classified by the fence protocol below and MUST behave as its class states when it is elaborated on the declared toolchain.

This requirement is written guidance. The {repo "specification/README.md"}[specification of the smaller Regula] retires the rules that checked it, {rule}[RG4001] to {rule}[RG4004], because a broken documentation example is cheap to see and cheap to correct by hand. No check of Regula reads a project's documentation. Review checks each fence, and a fence that breaks the protocol is an accepted risk, not a refusal of the checker.

The fence protocol is:

* an unmarked `lean` fence is a positive example. It elaborates exactly as printed, with its own imports and with no checker import or wrapper inserted, with no error and no warning, and its declarations meet the declaration and axiom rules of this module under Standard-Logical ({rule}[RG4002]);
* an immediately adjacent `<!-- lean-fail: PATTERN -->` marker makes the next `lean` fence a negative example. It fails with one error message that matches the whole nonempty pattern ({rule}[RG4003]). The pattern grammar is small and Lean-native: `|` separates alternatives, `.*` separates ordered literal fragments, and an optional leading `(?s)` changes nothing. Each alternative and each fragment is nonempty. Every other character is literal, except that `[](){}?+^$`, backslash, and a `*` outside `.*` are not part of the grammar. A pattern matches within one error message, including its multiline continuation, never across messages and never against informational output;
* an immediately adjacent `<!-- lean-trusted-compiler -->` marker identifies a teaching example of a compiler-trusting mechanism, such as `native_decide`, `decide +native` or `bv_decide`. It elaborates with no warning, contains a compiler-trusting declaration, and never counts as a conforming positive proof surface ({rule}[RG4004]). It imports the smallest module that states its mechanism: `import Init` for `native_decide` and `decide +native`, and `import Std.Tactic.BVDecide` for `bv_decide`; and
* a non-Lean sketch uses another fence language and is never described as compiling Lean.

Each marker sits directly before the fence it classifies, and an HTML comment that begins with `lean` is one of the two exact markers, so that a misspelled marker cannot turn a negative example into a positive one. Every fence is closed. Each Lean fence opens and closes with a run in the first column, outside block quotes, list items and other fences, and spells its language `lean` ({rule}[RG4001]). A Markdown reader renders a Lean block in a block quote, in a list item, behind another spelling of the language or in a raw HTML `pre` or `code` element, and a check of the examples that reads first-column fences misses each of them.

A fence that elaborates establishes its elaboration on the toolchain and with the imports it ran with. A narrower foundation claim or an execution-correspondence claim in the surrounding prose needs its own evidence.

This standard is itself Verso source, and its `lean` blocks follow the same three kinds ({ref "lean-example-convention"}[example convention]). When the rule-reference site builds, each block is elaborated where it is written, in a fresh environment of its own imports. A positive or teaching block must elaborate with no error and no warning, and a `fails` block must report an error that matches its pattern and no warning. That build does not classify the declarations of a block or read their axioms, and it reads no project's documentation.

# 7.8 Adopting the Checker in Another Project
%%%
tag := "78-adopting-the-checker-in-another-project"
number := false
%%%

The checker package is self-contained: an external Lean project adopts it by requiring the package, setting its lint driver and adding a surface manifest at its own root, with no Lake facets, module names, or fixture layout borrowed from this repository.

* The adopting project MAY use an ordinary `lakefile.lean` or `lakefile.toml`; both load through the same Lake workspace discovery (§7.2). Its `lintDriver` is `regula/lint`, so that `lake lint` runs the checker.
* The adopter classifies every root-package `lean_lib` and `lean_exe` in `foundation_manifest.json` at its project root, with empty exclusion arrays when nothing is excluded, and makes each claimed target a default target (§7.2).
* A claimed module may import the published interfaces `Regula.Contract` (the executable-contract API of §7.9), `Regula.Decision` (the `RegisteredDecision` registration that selects the {rule}[RG1008] obligation of §7.9) and `Regula.Assumption` (the `Assumed` record of an assumption about an external system). Each is an ordinary type, so it registers no code ({rule}[RG2007]). Regula's checker classifies a module by Lake's targets of the root package, so these modules of a dependency belong to no claimed surface.
* The checker package requires nothing beyond the Lean toolchain, and its libraries and executables import no Mathlib modules. Requiring it adds only the checker package to the adopter's `lake-manifest.json`, so an adopter with or without Mathlib keeps its own dependency revisions; a Core/Std-only adopter compiles only its own claimed surface plus the checker.
* Runs execute from the adopter's project root, in the order of the gate (§7 overview): the checker does not build, and a module without its `.olean` file makes its run `incomplete`.

An adopter also enables the community linters that {ref "67-community-conventions-and-linters"}[module 6 §6.7] requires and runs the recommended ones beside the checker:

* In the Lake `leanOptions` of every claimed library and executable, `linter.missingDocs` set to `true`, `autoImplicit` and `relaxedAutoImplicit` set to `false` (§7.1) and, in a surface that imports Mathlib, `weak.linter.mathlibStandardSet` set to `true` with the Mathlib-repository linters that §6.7 lists turned off (the header linter may instead be set to `true` with its license line configured). Their warnings are build warnings, so `lake build --wfail` rejects them ({rule}[RG2003]). {rule}[RG2006] checks values only for the two automatic-implicit options and admits the other options by name. Review checks the required linter settings (§6.7).
* Batteries' environment linters run as a separate command, `lake exe runLinter`. It lints the built modules and builds only a module that has no build output, so a stale build is linted as it is: run `lake build --wfail` first on either route. Lake has one `lintDriver` per package: a project that keeps `batteries/runLinter` as its driver runs `lake lint` for those linters and the checker with `lake exe lint`, and a project whose driver is `regula/lint` runs `lake lint` and, separately, `lake exe runLinter`. Each command's success establishes only its own checks.

The exact adapter steps, including glob syntax in both lakefile formats, a minimal manifest, and the community linter configuration, are in this repository's {repo "docs/guides/adoption.md"}[adoption guide].

# 7.9 Executable Contracts and Decision Registrations
%%%
tag := "79-executable-contracts-and-decision-registrations"
number := false
%%%

The public proof API is `ExecutableContract implementation condition : Prop`, with a field `evidence : condition implementation`. A theorem of this type is an executable contract: the loader reads it from the theorem's type, under its binders. Its elaborated predicate is applied to the actual constant by the type, so unrelated or weakened evidence cannot inhabit the unchanged requirement. `contract.run` returns that constant and requires the contract during elaboration ({ref "38-delivering-executable-witnesses-with-required-evidence"}[module 3 §3.8]). The proof is erased at runtime; this API does not perform a runtime validation. Application-specific proof interfaces remain valid, and callers that bypass a proof-requiring interface need separate review.

{rule}[RG1007] reports an executable contract of a claimed module in three cases. The first is an implementation applied to an argument: the contract fixes it, so the requirement covers only that instance. The second is an implementation whose head is not a safe, total, computable constant of the input: unsafe, partial and noncomputable constants fail, and universe-polymorphic constants are permitted. The third applies to a decision contract, and is a specification that reaches the implementation through the constants that each constant mentions: the type and value of a definition, theorem or opaque constant, and the type and constructors of an inductive type. That excludes the specification `fun x => f x = true`, for which both directions hold of every `f`. A specification can restate the body of the implementation without its name, so review checks independence in substance. Lean checks the evidence; {rule}[RG1005] checks its transitive axioms against the selected surface policy, as it does for every other owned declaration.

A contract is a *decision contract* when its condition is a decision kind ({ref "decision-kinds"}[module 3 §3.8]). The loader reads the kind from the head constant of the condition's body, under its function binders and without unfolding: `Regula.DecidesSoundly`, `Regula.DecidesCompletely`, `Regula.Decides`, or none of them. A definition that stands for a kind is read as no kind, and the contract is then an ordinary one. A condition that holds a kind inside a larger proposition, such as a conjunction, has no kind. `Regula.DecisionEquivalence` is a law and no kind, so it discharges no {rule}[RG1008] requirement.

The rule reads the implementation from the contract's first argument, not from the condition. So no check of Regula decides that the function a kind states is the implementation on its whole domain and at its own universe parameters. {ref "decision-kinds"}[Module 3 §3.8] states which forms have that property, and review checks them.

{rule}[RG1009] reports a decision contract of a claimed module when the constants that its specification reaches, and those that its implementation or acceptance predicate reach, hold one Boolean test outside the toolchain. A Boolean test is a constant whose type's result is `Bool` or `BEq _` and that is no field's projection function, which the loader reads from the kernel-checked value: a projection reads a field of data, which no definition computes. The constants of a form of the implementation in the condition, such as `Function.uncurry check`, count as the acceptance predicate's. Each search follows the mentions above, so it reads the value of each definition it reaches, a `Decidable` instance's and a theorem's included, and the constructors of each inductive type, the input type's included. A test that a proof in the specification names, or that an invariant of the input type names, is therefore shared when the implementation reaches it too, which refuses more and is the safe side. The search compares names, so a copy of a function under a second name is not found, and a proposition that copies the expression of a test is not refused. A shared function with another result type is not reported, and neither is a test of Lean's own library. This check is exact for what it reads and is not a verdict on the specification. Whether the specification is the intended one, whether it restates the implementation under another name, whether every function that acts as a checker is registered, and whether callers act on the verdict remain semantic review.

A project declares that a function is a decision by registering it with `RegisteredDecision`, which `Regula.Decision` provides (`import Regula.Decision`, or `public import Regula.Decision` in a file that is a `module`). A registration is a declaration of that type, such as `theorem f_registered : Regula.RegisteredDecision @f := ⟨⟩`, in a module that imports the function: where the function is declared, or in another module, for a function whose own module cannot import `Regula.Decision`. The loader reads it from the type of each constant of a claimed module. The registration is a requirement. A registered function of a claimed module MUST be the implementation of a decision contract of a claimed module in the same environment, or have a result type of the form `Decidable p` ({rule}[RG1008]). So deleting a decision contract while its function stays registered fails the gate, which is the rule of §7.5 for removed evidence made mechanical for these functions. The rule reads each environment apart: a contract in a module that an environment of the registration does not load does not count there, so put the registration beside the contract.

A result type has the form `Decidable p` when the function's type, under its binders and without unfolding, ends in an application of `Decidable`. A type written as `DecidablePred p` does not: state it as `∀ x, Decidable (p x)`. That form states both directions by construction ({ref "324-decidability-logical-vs-executable"}[module 3 §3.2.4]); it carries no witness that both outcomes occur, and it does not make the decided proposition the intended one. A registration adds a requirement and waives none, and removing it removes the requirement: which functions a project registers remains semantic review. Review also selects the public declarations that state material claims for the documentation requirements of §5.1–§5.2; those declarations need no registration.

The checker reads the manifest and the finished build on each run and keeps no verdict, so a changed profile or execution mode cannot inherit an old one. Removing or narrowing requirements, intentionally changing library globs or exclusions, and bypassing proof-requiring callers change the claim itself. Semantic review MUST establish intended coverage and contract adequacy. A pass of the gate alone establishes neither intended coverage nor full-standard conformance.
