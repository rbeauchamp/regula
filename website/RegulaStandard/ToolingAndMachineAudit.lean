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

Modules 0–6 define the Lean properties a conforming development must have. This module defines the Lean-specific evidence needed to establish those properties: an exact elaboration environment, complete Lake module coverage, environment-level declaration inspection, exact axiom sets, and checked documentation examples. It separately defines qualification rules for projects implementing a checker and an optional serialized-declaration-graph check. Those conditional activities are not part of every adopter's ordinary conformance run. Semantic review remains necessary to establish that the checked statements express the intended claims.

A successful command establishes only the property it checks. In particular, an unextended `lake build` elaborates configured targets; it does not establish complete module coverage, absence of project axioms, a claimed foundation profile, or correctness of Markdown examples by itself.

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

Parsing, elaboration, generated declarations, tactics, theorem names, and reduction behavior can change with the toolchain or dependencies. The gate reports the environment it loads. Its declaration results do not prove that a dependency checkout matches its recorded revision.

*Requirement*: Every claimed library and claimed executable MUST elaborate with the options `autoImplicit` and `relaxedAutoImplicit` set to `false`, as Mathlib's own build does, set in its Lake `leanOptions`. Its extra `lean` arguments (`moreLeanArgs` and `weakLeanArgs`) MUST NOT set either option to another value with `-D name=value`, which can override `leanOptions`; other extra arguments are allowed. With automatic implicits, an unbound identifier in a declaration's signature becomes a universally quantified implicit argument that the source does not show. A misspelled name can then add a binder and change the quantifiers that a reviewer compares with the intent ({ref "52-faithful-explanation-of-formal-claims"}[module 5 §5.2]). With both options off, such an identifier is an elaboration error. RG2006 checks both options, and every `-D` among the extra arguments, in Lake's resolved configuration of every claimed target; a `set_option autoImplicit true` command in source is outside that configuration, and review checks it (`DECL-01`). The elaborated declaration remains authoritative under either setting.

# 7.2 Define Surfaces Through Lake Semantics
%%%
tag := "72-define-surfaces-through-lake-semantics"
number := false
%%%

*Requirement*: Claimed surfaces MUST be identified through Lake targets. Under the shipped manifest schema, each surface names one `lean_lib` in the root package and MAY claim standalone `lean_exe` roots by target name. An executable claim includes its exact Lake-resolved root module, such as `Main`. The module inventory MUST come from Lake's elaborated configuration, not a separately maintained file list or namespace-prefix search. The current checker requires at least one nonempty library surface. Executable-only packages can be valid Lean projects, but this schema does not support them.

The shipped checkers load the checked project's workspace through Lake's loader and read the elaborated root-package model directly: every `lean_lib` name, each library's exact module array and each module's Lake-resolved source file, every `lean_exe` name with its exact root module and source, and the root package's compiled-module directory. Because the elaborated model is the same object Lake builds from, `lakefile.lean` and `lakefile.toml` projects take the identical discovery path, and no custom Lake facets or lakefile edits are required from an adopter.

For a library `Lib`, Lake's built-in `modules` facet exposes a related view: it adds transitive imports that Lake assigns to that library. It equals the configured module array only when those imports are already covered. Use the configured array for the manifest inventory and reconcile any additional imported modules. Do not treat the two views as interchangeable. The facet can be queried with:

```sh
lake query Lib:modules --json
```

The audit MUST:

1. fail if the Lake workspace load, configuration, or surface manifest is missing or malformed, and reconcile every root-package Lean library and every root-package `lean_exe` target with exactly one positive or excluded manifest entry;
2. import and inspect every exact module returned for the claimed library and the exact root module of every claimed executable;
3. reconcile that exact set with the module attribution recorded in the elaborated environment;
4. fail on an omitted configured module or claimed executable root, an unexpected project module, or a module whose ownership cannot be determined; and
5. keep intentionally invalid fixtures outside every positive library surface.

The surface manifest is JSON with exactly four top-level keys: `schema-version` (equal to `2`), `surfaces`, `excluded-libraries`, and `excluded-executables`. It lives at the checked project's root as `foundation_manifest.json` unless an explicit `--manifest PATH` is given, and the checkers audit the project found from the current directory unless an explicit `--project DIR` is given.

Each surface names one `library`, a foundation `claim`, and a `rationale`, MAY list claimed `executables` by `lean_exe` target name, and MAY set `execution` to `report` (the default) or `checked` for the §7.6 execution-coverage claim; each exclusion entry names the target and its `rationale`. Unknown keys, duplicates, a wrong schema version, an unknown `execution` value, an empty `surfaces` array, or a target Lake does not elaborate fail closed. Empty exclusion arrays are valid for an adopter with nothing to exclude.

Claiming an executable whose root module already belongs to a manifested library, or excluding an executable whose root module belongs to a claimed library, is a manifest conflict and fails: a claimed executable root must be a standalone root module such as `Main`.

Library globs are therefore load-bearing. If a project intends every module below `Lib` to be in scope, its Lake configuration must use a glob with that meaning, such as ``.andSubmodules `Lib``. An umbrella import alone is insufficient: a valid but unimported source file can otherwise be absent from both `lake build` and the declaration inventory.

Declaration ownership is the exact module index Lean records. A declaration name that begins with `Lib`, a module named `LibLookalike`, or a private/internal-looking name does not establish or remove ownership. To catch a root-package module imported outside every configured library, the audit resolves each imported module's `.olean` through Lean and compares its origin with Lake's root-package output directory. A root-owned import absent from the claimed library modules and claimed standalone executable roots fails before its declarations can escape classification. Exclusion records classify targets for inventory purposes; they do not permit a claimed module to import an excluded module.

When a claim inspects independently loaded Lean environments, the audit MUST retain each requested environment's identity and exact module assignment. Declaration names are unique within one Lean environment; distinct environments may legitimately contain different declarations with the same name, including `main`. Their inventories MUST NOT be treated as one loaded environment. Declaration policies, generated-role evidence, execution requests, replay, transcripts, histories and origins MUST be resolved in the environment of the requested observation. The complete claim still requires every positively assigned module and the global target-classification checks above. The shipped project audit loads each surface's library modules in one environment and each claimed executable's root module in an environment of its own: every executable root declares its `main`, and Lean refuses to import two modules that declare the same name.

# 7.3 Clean Elaboration and Diagnostics
%%%
tag := "73-clean-elaboration-and-diagnostics"
number := false
%%%

*Requirement*: Every module in a positive surface MUST elaborate successfully from source in a fresh Lean/Lake build state, and the audit MUST reject every emitted warning.

* The audit build MUST use empty root-package build output or an isolated disposable copy. Pre-existing or fixture-produced root-package `.olean` files MUST NOT satisfy a fresh conformance claim. Dependencies may use existing artifacts under the declared environment; this is not a clean rebuild of the entire dependency graph.
* Warning rejection MUST be enforced by the audit driver from Lean/Lake diagnostics. A source file cannot make its own warning disappear from conformance by setting `warningAsError := false` locally.
* The build output and exit status MUST both be checked. A zero exit with a warning is not a warning-free result.
* For the checker qualification in §7.8, re-establish the positive control after a negative mutation (§7.8 states when a separate fresh workspace satisfies this). The qualification harness must keep the mutation’s artifacts from satisfying that control.

The shipped declaration gate uses an isolated copy under the checked project's `tmp/`. It omits VCS data, Lake build state, and artifact caches; shares dependency checkouts through `.lake/packages`; and re-anchors relative path dependencies recorded in the manifest to their original directories. A missing relative dependency fails as `lake-workspace-load-failed`. The copy starts with empty root-package output and is removed afterward. Lake can reuse existing dependency artifacts and may rebuild missing or invalidated dependencies. This establishes fresh source elaboration for the claimed root-package surface, not fresh checking of every imported dependency. Disabling a linter can prevent it from emitting a warning but does not discharge the semantic property the linter was intended to check. Lean's default warnings are never disabled on a claimed surface; a community linter, whether a dependency or the project enables it, may be disabled for a single declaration only as {ref "62-module-purpose-and-linter-discipline"}[module 6 §6.2] describes. The audit cannot see a disabled linter, so review checks the disables.

`lake build` remains necessary to elaborate source, run command elaborators and linters, and produce the `.olean` files used by later checks. Successful elaboration alone does not establish checked admission: metaprogramming APIs and local options can store unchecked declarations. Before accepting proof, positive-fence, or correspondence evidence, the gate MUST complete kernel checking of every owned logical declaration and its owned dependencies, including mutual inductive groups and their generated constructors and recursors. Imported dependencies outside the owned inventory remain the declared trusted base. Authored unsafe/partial declarations remain forbidden; generated helpers require §7.4's separate authentication and cannot supply logical evidence. Unsupported or incomplete admission fails the affected claim. The shipped project, file, fence, and build-linter paths share `Admission.validate`. It forces the completed environment, excludes owned declarations from the imported replay base, replays safe non-partial declarations with pinned `Lean.Kernel.Environment.replay`, and checks coverage before report construction. It reads each replayed module's own constants: Lean realizes a lemma such as an equation lemma in every module that needs it, two modules that do not import each other can each contain it, and Lean's import keeps one copy of the name while `collectAxioms` reports the axioms the module the name is attributed to computed for its own copy. Under each such name the replay base lacks, it replays the copy the audited environment returns. Every other copy of a name that the base or another replayed module also declares is admitted only when it and the constant the replayed kernel holds are theorems of the same statement, universe parameters and mutual block (the only such pair Lean's import accepts that involves no axiom) and, unless it is identical to that replayed or trusted constant, the kernel accepts its own proof under a fresh name and that proof does not reach its own name and reaches exactly the held constant's axioms; where the audited environment keeps an owned copy over a different base constant, that kept copy must meet these conditions there too. No other environment reuses the admission of a module holding such a copy, and an executable's environment reuses a module only when no module it loads declares a different copy of one of that module's names. Any other shared name leaves the claim incomplete. The project audit checks each library's environment first; an executable's environment then keeps in its base, instead of replaying again, an owned module a library's environment of the same audit replayed over the identical import closure, when every owned module of that closure has every `.olean` part Lean reads (including `.olean.server` and `.olean.private`) frozen and byte-identical and every declaration of those modules refers only to constants of the closure. Library environments still replay every owned module they load. Source option restoration or checking a new reference to a stored theorem cannot substitute for this dependency admission. This does not recheck the whole imported dependency graph or establish the optional §7.9 claim.

# 7.4 Inventory Every Owned Declaration
%%%
tag := "74-inventory-every-owned-declaration"
number := false
%%%

*Requirement*: The gate MUST inspect Lean's elaborated `Environment` and emit one record for every constant attributed to every exact owned module.

Each record MUST include at least:

* exact declaration name and exact owning module;
* exhaustive `ConstantInfo` kind (`axiom`, theorem, definition, opaque definition, inductive, constructor, recursor, or quotient declaration);
* whether the elaborated type is a proposition, so proof-valued definitions and instances cannot hide outside a theorem-only scan;
* instance and `noncomputable` metadata;
* `ConstantInfo.isUnsafe` and `ConstantInfo.isPartial` information;
* runtime replacement and external-code metadata (`@[implemented_by]`, `@[extern]`);
* the exact transitive axiom set from `Lean.collectAxioms`; and
* Lean-native generated-role metadata, such as projection, matcher, recursor, or compiler-generated partial helper.

The policy applies to public, protected, private, internal-looking, authored, and generated declarations. Final-`Environment` role metadata is descriptive: public metaprogramming APIs can synthesize names, ranges, declarations, and extension tags. Such metadata may explain a declaration; it MUST NOT by itself waive a project axiom, `sorryAx`, unknown axiom, or authored unsafe/partial declaration, and it MUST NOT hide a runtime replacement or external declaration from the §7.6 execution account.

Lean may emit a range-less internal `isPartial` code-generation helper for a safe, termination-checked recursive `def`. Lean links the helper to its base only by name (its code generator runs `f._unsafe_rec` in place of `f`), so the checker takes the base from that link. The helper is permitted only when Lean's own recursion compiler, run on the recursion the helper executes, regenerates its base, decided on the final declarations alone, whatever code added them:

* its final declaration is an opaque-hinted partial definition with no range, unsafe flag, runtime replacement, external marker, or axioms beyond the base;
* the linked base is present in the same module, safe, non-partial, with no runtime replacement or external marker, with the same elaborated type and level parameters, and with every axiom within Standard-Logical (`propext`, `Quot.sound`, `Classical.choice`), and the base/helper mutual-group lists map exactly through Lean's `._unsafe_rec` transformation; and
* rerunning Lean 4.34.0's own recursion compiler on the helper's group, each helper's value becoming the body of a fresh definition whose recursive calls are the group's helpers, regenerates the observed base and every auxiliary definition it produces, up to compilation erasure: the two values are the same once every proof and every type of each, decided in that value's own context, is erased and each well-founded fixpoint (`WellFounded.fix`, `WellFounded.Nat.fix`) is taken without its relation, measure, or well-foundedness proof. Structural recursion is tried first, with no hint; then well-founded recursion with Lean's measure inference and every decreasing proof elided. The compiler runs with only the toolchain's own `wf_preprocess` rules and only the syntax handlers built into the checker executable, so no rule, macro, tactic, or elaborator of the audited modules or their dependencies takes part; an audited module's initializer, which the report worker runs, could register a built-in handler, but that changes the checker process, outside this standard's boundary. The fresh definitions generate no code, and every change the run makes is undone before the comparison, which reads the observed definitions and decides erasure in the inspected environment.

Admission therefore establishes that the helper is Lean's compilation of the safe definition: the base is what Lean's recursion compiler, with the toolchain's own preprocessing rules, produces from the helper's recursion, up to erasure, and it is kernel-checked with every axiom within Standard-Logical. Because that preprocessing rewrites the body only by proved equations, a well-founded fixpoint unfolds to its functional for any relation or measure (a structural base unfolds definitionally), and the comparison otherwise erases only proofs and types, which compiled code does not compute, the observed base satisfies the helper's recursion equation: whenever the helper returns, it returns the base's value. Admission does not establish that the helper terminates whenever the base does. Lean compiles the base from the preprocessed body while the helper keeps the original, and Lean's own `wf_preprocess` documentation warns that a rewrite can remove a subterm the compiled code still evaluates or delay one under a binder, so that a definition that diverges as compiled is accepted; a toolchain rule can do so when it matches through a reducible definition that ignores an argument. The helper's termination therefore also trusts Lean's well-founded preprocessing to preserve its recursive calls and when they are evaluated, as every well-founded definition Lean accepts does. A rule the audited source or a dependency adds is left out of the regeneration: such a rule rewriting `keep a b` to `a` lets Lean accept a base that never recurses while its helper recurses without bound. A helper that code in the audited module forged or rewrote passes only when it is such a helper, so the decision needs no record of which elaborators ran. The regeneration and its comparison are the checker's observations, not proved facts, and the correspondence between a helper's value and its compiled code is the trusted compiler, as for every definition.

A `partial def`, written by the author or generated by a deriving handler (Lean 4.34.0's `BEq`, `Hashable`, `Repr`, and `Ord` handlers do so for a nested or mutual inductive, and the `Ord` handler for any recursive one), is an opaque constant that Lean compiles through its partial helper. That helper is never permitted, and the gate reports it under the opaque declaration's name and source range, the declaration the author wrote or derived.

As a checker limit, not a property of Lean, a helper is not permitted where the regeneration does not reproduce its base: a structural recursion on an argument other than the first one Lean's automatic choice accepts, which a `termination_by structural` clause can select, a `partial_fixpoint` definition, a base compiled through another fixpoint combinator, a base whose compilation used a `wf_preprocess` rule registered outside the Lean toolchain, or one elaborated with `set_option wf.preprocess false` or with a toolchain rule removed by `attribute [-wf_preprocess]` when a rule so disabled would have rewritten its body. Such a definition is rejected even though Lean accepts it.

Missing, ambiguous, imported-only, or semantically mismatched evidence fails. Name suffixes and strings such as `._native.`, `_private`, `.rec`, or `_unsafe_rec` are never authority by themselves: the helper's name only selects the base, and the regeneration decides.

If a `ConstantInfo` variant or relevant metadata cannot be classified, the affected claim is incomplete and cannot support conformance.

# 7.5 Proof Completeness and Foundation Strength
%%%
tag := "75-proof-completeness-and-foundation-strength"
number := false
%%%

*Requirement*: Every owned declaration MUST be checked for forbidden assumptions, and every declaration with an admissible logical axiom set MUST receive its least permissive foundation label. Forbidden or compiler-trusting sets are classified separately and rejected from conforming positive surfaces.

Assign the least permissive of the labels Kernel-only, Choice-Free, and Standard-Logical ({ref "45-foundation-strength-kernel-only-choice-free-standard-logical"}[module 4 §4.5]) containing the declaration’s exact axiom set. A surface’s selected profile is an upper bound and does not replace the per-declaration label.

The gate MUST reject:

* every owned logical `axiom` declaration, whether or not another declaration depends on it (§3.4);
* `sorryAx` anywhere in a transitive axiom set, including uses introduced by `sorry` or `admit`;
* every unknown axiom;
* every declaration that exceeds its surface's claimed profile; and
* every omitted or unclassified declaration.

The proof surface includes theorems and every definition or instance whose elaborated type is a proposition. A declaration of a proposition (`P : Prop`) defines a statement; a declaration whose type is `P` supplies evidence of it. Ordinary data and function definitions are still inventoried and may not conceal project axioms, holes, unknown axioms, or forbidden computational mechanisms.

A compiler-generated native-proof axiom is not accepted because its name, internal bit, or range appears native. On the supported toolchain, `native_decide`, `decide +native`, and the `bv_decide` tactics (`bv_decide`, `bv_decide?`, `bv_check`, also in `grind =>` and `sym =>` mode) add their axiom through `Lean.Meta.nativeEqTrue`, which names it after the tactic name it is passed: `parent._native.native_decide.ax_…`, `parent._native.decide.ax_…`, or `parent._native.bv_decide.ax_…`, with `parent` in its module-private form when a `module` file elaborates the proof without exporting. The gate must establish three conditions. First, the name is exactly one this scheme generates for one of these tactic names under the name of a declaration of the axiom's module or that name's module-private form. Second, the axiom is a safe proposition axiom of type `e = true`, with `e` in that tactic's exact asserted shape (`@decide P inst`, or for `bv_decide` `verifyBVExpr expr cert` over the same run's generated expression and certificate definitions), depending on no other non-logical axiom, and an independent native replay of `e` returns `true`. Third, fresh re-elaboration of the exact source shows that the one command introducing that declaration is the one command adding an axiom of the same generated origin and asserted statement, and that no `axiom` declaration node occurs in that command's syntax, in a command its elaboration records, or in a macro expansion there, quoted syntax included. This is read from syntax, which Lean records whether or not elaborating that declaration succeeds, and it matches no names, so a command that both declares an axiom and uses a native tactic has no native axiom classified. Only then is the axiom classified as *compiler-trusting*, with every declaration that depends on it. Compiler-trusting is not one of the three logical labels and is nonconforming on a kernel-checked positive surface.

The second condition makes this classification sound whatever code added the axiom: the axiom asserts only a closed Boolean fact that compiled evaluation confirms, so relying on it is exactly relying on the compiler. The third condition keeps an authored `axiom` declaration a project axiom. Neither condition depends on the surrounding syntax, so namespaced names, attributes, `set_option … in`, `where` clauses, parameters, and `grind =>` or `sym =>` blocks are classified alike. A custom tactic, elaborator, or metaprogram, including `run_tac` and `by_elab`, that adds such an axiom without declaring it is classified compiler-trusting by the second condition; it never obtains a logical label.

This authorization boundary assumes the pinned Lean process and explicitly imported trusted libraries are not compromised. Arbitrary hostile trusted plugins or process compromise are out of scope. Audited-source custom or ambiguous evaluator paths remain in scope: a recursion helper they add or rewrite is permitted only when Lean's own recursion compiler regenerates its base from it, up to compilation erasure (§7.4), and a native-proof axiom they add is classified only through the conditions above.

## Explicit application contracts
%%%
tag := "explicit-application-contracts"
number := false
%%%

A complete executable component MUST encode its required behavioral propositions as proof requirements tied to the actual definitions through dependent result types, proof-bearing interfaces consumed by the application, or semantic checks against explicit expected propositions. Removing evidence while its requirement remains MUST fail elaboration or the gate. A trivial or weaker proposition cannot discharge the unchanged obligation. Existing construction, library proofs, and composition MAY discharge these requirements without a redundant theorem for every helper.

The gate's fresh elaboration checks these explicit proof obligations and its declaration policy rejects holes and forbidden axioms. It inventories remaining declarations and does not infer missing specifications from names, counts, or digests. Semantic review MUST still establish adequacy and completeness: all relevant roots and boundaries are covered, and the required propositions express the intended behavior, including admission, success and refusal, update, frame, and composition where those are part of the claim. Deleting or weakening the requirement itself, or changing the caller to bypass its interface, changes the specification or its application linkage and requires that review. A gate PASS alone is not a contract-completeness verdict.

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
  * Lean accepts a kernel definition, with structural or well-founded termination justification when recursion requires it; code generation may add the narrowly authenticated internal helper described in §7.4
  * permitted, subject to its axioms and profile
*
  * `opaque` with a body
  * the body is kernel-checked but is not available to ordinary client reduction; it is not a logical axiom
  * permitted when the API claim matches that reduction boundary
*
  * `noncomputable`
  * records that Lean need not generate executable code for the declaration; it introduces no logical axiom by itself
  * permitted and reported
*
  * `decide p` / `by decide`
  * `decide p` returns a `Bool` from a `Decidable p` instance; the tactic `by decide` constructs a proof when the decision reduces appropriately, without adding a native-proof axiom
  * permitted, subject to transitive axioms
*
  * `native_decide`, `decide +native`, `bv_decide` / native proof
  * executes compiled code and adds a generated axiom asserting the result used by the proof
  * compiler-trusting; banned
*
  * `partial def`
  * supplies executable recursion without a kernel termination proof; the logical-facing declaration is an opaque constant whose compiled execution runs the generated partial helper
  * authored `partial` declarations are escape hatches: banned; partial computation reached from an executable root is reported as a trusted execution boundary
*
  * `unsafe def` / unsafe declaration
  * excluded from safe kernel definitions and checked proof terms; intended for compiled execution
  * authored unsafe declarations are escape hatches: banned; unsafe computation reached from an executable root is reported as a trusted execution boundary
*
  * `@[implemented_by]`
  * kernel reasoning uses the reference definition while compiled execution uses a different definition
  * permitted only as a reported execution boundary: trusted unless checked correspondence evidence relates the replacement to the reference; never an unconditional one-definition execution claim
*
  * `@[csimp]`
  * the pinned compiler substitutes a constant using an unconditional constant-equality declaration; kernel reduction is unchanged
  * prefer when this proof-backed form fits; the exact equality and every further execution boundary still require classification
*
  * `@[extern]` / FFI
  * compiled execution calls external or runtime code whose behavior is not established by the Lean declaration alone
  * permitted only as a reported execution boundary: toolchain runtime primitives (origin-checked `Init` modules, such as `Nat`/`Float32` arithmetic) are trusted native-runtime substrate; any other extern is trusted external code; neither is ever checked correspondence
*
  * `#eval` or native execution output
  * an observation from evaluation, not a proof term
  * never proof evidence
:::

The native-runtime exception requires module-origin evidence: the owning module is `Init` or a submodule, and Lean's resolved `.olean` path, after resolving symbolic links, equals that module's corresponding path in the pinned toolchain's library directory. A project or dependency module named `Init.Adopter` does not become toolchain substrate by its name. Missing origin evidence cannot authorize the exception. This check assumes the pinned toolchain installation and Lean process are trusted under §7.5.

Logical decidability, executable decidability, kernel reduction, code generation, and native execution are separate questions. Transfer of a property from a reference definition to a replacement requires the relevant relation, established by reduction or a checked proof. A theorem relating Lean definitions does not establish the behavior of external machine code; that boundary needs its own account.

## Execution roots and conservative coverage
%%%
tag := "execution-roots-and-conservative-coverage"
number := false
%%%

*Execution coverage is a distinct account from the logical audit.* The foundation labels of §7.5 are purely logical: a Standard-Logical PASS never asserts execution correspondence. For each owned executable root — a computable, safe, non-partial, non-internal, non-proposition definition or opaque constant whose result is not a `Sort`, including the `main` of a claimed executable and eligible eliminator/matcher machinery, even when unused — the gate MUST account for supported compiler transformations and logical value dependencies. Logical expressions alone do not establish execution coverage. On Lean `4.34.0` (`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`), `CSimp.replaceConstant` performs one lookup per invocation: `ToDecl.replaceLogicConstants` invokes it before macro inlining, and `ToLCNF` invokes it again during conversion; `implemented_by` is applied during later simplification, and inlining or specialization can erase intermediate calls. A later attribute assignment can change the final environment without changing already compiled code. These facts preclude reconstructing every replacement choice from the final attribute map or optimized code alone.

The checker's finite, conservative closure is the least set containing the executable root and closed under retained compiler calls, closures, initializers, constants in the logical values of unreplaced non-proof definitions, constant-equality replacement candidates in the pinned `csimp` form, observed `implemented_by` choices, and partial helpers' bodies. `@[extern]` declarations are boundary leaves for their Lean bodies. `implemented_by` reference bodies are likewise not descended, while their replacement targets are expanded. Imported declarations remain unowned. Retained compiled edges come from the pinned compiler IR; the {repo "docs/guides/proofs-and-boundaries.md#producers"}[producer account] identifies the collector API and its treatment of recursive calls. Private module data and full IR are loaded through Lean's import semantics. A compiler-only generated node need not have a kernel declaration, but its compiled body MUST be available. A missing retained dependency or an opaque export placeholder is unresolved, not an empty body. The logical-value scan is conservative: it can include constants in erased proof or type arguments within a data-producing definition. It does not descend into separate theorem bodies or proof-valued definitions merely to reconstruct native execution.

Auxiliary-recursor, no-confusion and matcher metadata MUST NOT remove an otherwise eligible root from that account. Such logical/compiler machinery, projections, macro-inline definitions and the pinned generated `brecOn` helper can lack standalone IR. This exception relaxes only the initial root's standalone-IR obligation; its actual values, runtime attributes and every available compiled body remain inspected. Every dependency actually retained in IR still requires its compiled body, even if it carries one of these tags. Tags do not authenticate generation. The conservative account does not establish that each logical machinery root independently compiles into a callable function.

Equality candidates include proof-valued definitions and theorems with exactly the constant heads and matching distinct universe parameters that the pinned `csimp` attribute accepts. This overapproximation retains possible local or overwritten simplifications even when the final scoped attribute state has lost their registration. A candidate does not assert that compilation selected it. Each candidate's correspondence must pass the kernel admission below before it can be reported as checked. Following candidate targets to a fixed point conservatively accounts for chains and does not claim the compiler recursively rewrites one constant to that fixed point.

For a reached `implemented_by` reference, an isolated fresh frontend re-elaborates its Lean-resolved source and records the implementation maps in nested command contexts, preserving earlier targets overwritten by later attributes. A completed result is shared, within one audit and across its surface workers, only when the module, its source path and bytes, the effective search path and the checker binary are identical. Source is compared byte-for-byte before and after this inspection. Missing source, failed replay, a current target absent from the history, or an unsupported source evaluator leaves the path unresolved. Source metaprograms such as `run_cmd`, `run_meta`, `run_elab`, `run_tac`, `by_elab`, and module-local or ambiguous elaborators cannot authorize history from command snapshots because they can change and restore a mapping within a command. This uses the §7.5 supported process and imported-library trust boundary. It is not a claim against compromised processes or arbitrary trusted plugins. Other compiler pins are unsupported until their semantics are qualified.

Ordinary recursive call graphs use a visited-set fixed point. A cycle consisting solely of active `csimp` or observed `implemented_by` edges is explicitly unresolved and is not silently discarded as a completed traversal. Conservative candidates and historical choices can reject a program whose particular compiled path is safe. The report MUST distinguish this candidate account from the retained compiled edges rather than describe it as a minimal runtime call graph.

## Boundary kinds and evidence
%%%
tag := "boundary-kinds-and-evidence"
number := false
%%%

Each reported boundary entry has a kind and correspondence state. A declaration may have several entries, such as multiple replacement candidates:

* kinds: `runtime-replacement` (`@[implemented_by]`), `compiler-simplification` (a possible constant-equality replacement, not necessarily an active registration), `native-runtime` (an extern resolved from the pinned toolchain's `Init` modules), `external` (any other extern/FFI), `unsafe-computation`, `partial-computation` (including a partial definition's erased opaque constant, detected through its generated partial helper), `opaque-computation`, and `compiler-trusted-proof` (native-proof or `trustCompiler`-family axioms in the closure);
* *checked*: kernel-verified correspondence — a closed proof inhabits the exact proposition `∀ xs, f.{us} xs = g.{us} xs`, where `us` are the reference's universally quantified level parameters and `xs` is its complete elaborated dependent domain (including implicit, typeclass, and proof parameters), with the replacement instantiated at the compiler's same positional levels. The proof and its owned logical dependencies MUST pass checked admission before the proof is accepted against that proposition and have only standard-logical transitive axioms. Definitional equality, whole-function equality, and pointwise equality are possible proof sources, not alternative admission criteria. No expression or universe metavariables, free term variables, or additional undischarged theorem-only hypotheses may remain. An actual domain hypothesis is legitimate; an extra premise such as `False` cannot justify unconditional agreement unless discharged. For `opaque-computation`, *checked* instead records that the opaque constant has a kernel-checked body. It does not establish a separate compiler-correctness theorem; reached execution boundaries still require classification;
* *trusted*: the analyzed path has a boundary without the required kernel evidence — native-runtime primitives, external/FFI code, unproven replacements, unsafe/partial computation, and compiler-trusting proof axioms;
* *unresolved*: the analysis could not resolve or classify the path — a constant missing from the environment, unavailable module attribution, an unexpected compiled-helper shape, or a comparison that could not complete. A completed negative definitional comparison does not refute propositional equality; without another admitted proof, a replacement remains trusted.

## Reports and execution modes
%%%
tag := "reports-and-execution-modes"
number := false
%%%

Gate output reports per-surface and per-file execution coverage: roots, each boundary’s kind, correspondence, replacement, evidence, and every unresolved path, so a proved property and a trusted boundary are never conflated. `--json-out` always carries the complete account. File-mode text lists it too; project-mode text prints each surface’s coverage counts and lists every root and boundary with `--verbose`. Replacement evidence identifies conservative equality candidates. `compilerEdges` records retained IR edges separately, and `compilerCallers` identifies compiled calls to a reported boundary wherever that boundary is listed. Replacement evidence reports the selected instantiated proof term and its exact required type, with universes and implicit arguments shown. The checker constructs this obligation in `Regula.Probe.replacementCorrespondence` and admits evidence only through `checkCorrespondenceProof`. Its theorem search supports equality in either direction at any prefix of the actual domain, applying remaining arguments by congruence. Search is deliberately incomplete: a candidate whose remaining premises cannot be instantiated supplies no evidence; a replacement without an admitted proof stays trusted, and an unsupported obligation shape is unresolved. Equality between Lean definitions does not discharge any extern or native boundary reached through the replacement. The execution claim has two modes:

* `report` (the default): trusted boundaries are reported but do not fail. Unresolved paths always block the affected execution claim (`execution-unresolved`).
* `checked` (a per-surface `"execution": "checked"` manifest key or `--execution checked` for single-file audits): every non-native-runtime boundary MUST be checked. A trusted replacement, external, unsafe, partial, or compiler-trusting boundary fails with `execution-trusted-boundary`. Native-runtime primitives remain permitted but reported. They are the toolchain execution substrate under the §7.5 assurance boundary, not correspondence a source-level audit can discharge.

An unknown `execution` value and any boundary the classification cannot account for fail closed.

# 7.7 Check Lean Documentation Verbatim
%%%
tag := "77-check-lean-documentation-verbatim"
number := false
%%%

*Requirement*: Every Markdown file in the normative documentation tree, including nested directories, MUST have every Lean fence classified and checked on the declared toolchain.

The shipped fence audit reads the project's `docs/` directory unless `--docs-root PATH` names another tree, and `--verso` (below) adds a Verso library; a result identifies the scope it covers.

The fence protocol is:

* an unmarked `lean` fence is positive and MUST first elaborate exactly as printed, with no checker imports or wrappers inserted into the source being tested;
* an immediately adjacent `<!-- lean-fail: PATTERN -->` marker makes the next `lean` fence a negative example; the non-empty diagnostic pattern MUST be valid, the frontend worker MUST complete with a source rejection, and one effective-error diagnostic MUST match the entire pattern. The pattern grammar is intentionally small and Lean-native: `|` separates alternatives, `.*` separates ordered literal fragments, an optional leading `(?s)` is accepted for compatibility. Each alternative and ordered fragment must be nonempty. Matching searches one typed error message, including its multiline continuation; it never joins messages or matches informational output. `(?s)` does not change that behavior. A worker crash, missing completion record, setup failure, or timeout is not an expected source rejection. Remaining characters are literal, except that `[](){}?+^$`, backslash, and a `*` outside `.*` are rejected as unsupported regex syntax;
* an immediately adjacent `<!-- lean-trusted-compiler -->` marker identifies a teaching example that intentionally demonstrates a compiler-trusting mechanism; it MUST elaborate and be classified, but it MUST NOT count as a conforming positive proof surface; and
* non-Lean sketches use another fence language and MUST NOT be described as compiling Lean.

After a positive fence elaborates verbatim, the checker MUST complete the shared admission checks for the fence and its owned imports, then inspect its resulting module environment and apply the declaration and axiom rules above. The shipped fence audit admits positives under Standard-Logical; a narrower foundation claim or an execution-correspondence claim in the surrounding prose needs its own evidence. Fence success alone establishes neither. Instrumentation may inspect a compiled temporary module; it may not change the imports or elaboration context of the source whose success is claimed.

Fences routinely import the checked project's own modules. Before elaborating any fence, the shipped fence audit builds the manifest's claimed libraries and executable roots in an isolated disposable copy (the §7.3 mechanism), requires that build to succeed warning-free, and elaborates and inspects every fence against the copy's exact Lake search path. It never relies on a prior `lake build` in the main checkout. An owned module that is missing, stale, or warning-producing fails the audit rather than silently resolving from pre-existing build output. The copy's build and every fence worker run with the invoking process's inherited `LEAN_PATH` and `LEAN_SRC_PATH` removed (`lake exe` exports the main checkout's search path, and `lake env` would append it after the workspace's own entries). So a fence import that the fresh claimed-surface build did not produce fails instead of resolving from pre-existing build output. The public §7.8 control injects such a stale search-path entry and requires that failure.

This standard is itself Verso source. With `--verso DIR:LIBRARY:RENDER`, the shipped fence audit also reads every code block of that Verso library under the closed block grammar of the standard's {ref "lean-example-convention"}[example convention] and audits each `lean` block exactly as a fence of the same kind. It first builds that library fresh in the same copy, where each `lean` block is elaborated where it is written in a fresh environment of its own imports; every fence is then elaborated and inspected against that Verso package's exact Lake search path, because the package requires the checked project and every other package the standard's examples import (here the Mathlib-dependent `audit/` package), whose library modules are then owned alongside the claimed surface. It finally renders the library, which resolves every cross-reference; any failure fails the audit.

Trusted-compiler fences are re-elaborated by the fresh-frontend transcript inside an isolated inspection worker for native-proof evidence (§7.5), so their imports are paid twice: once in the fence compilation worker and once in the inspection worker. A trusted fence SHOULD import the smallest module that states its mechanism. `import Init` suffices for `native_decide` and `decide +native` examples, and `import Std.Tactic.BVDecide` for `bv_decide`, not `Mathlib.Tactic`. The audit prints and flushes a progress line at each phase (fence inventory, fresh claimed-surface build, fence compilation, each inspection group), so a killed or resource-exhausted run names the phase it died in rather than exiting silently.

The scanner MUST fail on unclosed fences, invalid or empty diagnostic patterns, orphan markers, markers followed by a non-Lean fence, multiple markers targeting one fence, a marker left at end of file, and any HTML comment beginning with `lean` that is not an exact marker. A misspelled marker must not silently demote its fence to a positive example. For positive and trusted-compiler fences, the audit MUST reject warnings from the actual Lean diagnostics even if the example locally disables `warningAsError`, in both the `warning:` and the named `warning(name):` rendering.

# 7.8 Qualify Checker Implementations with Independent Mutations
%%%
tag := "78-qualify-checker-implementations-with-independent-mutations"
number := false
%%%

*Conditional requirement*: A claimed checker detection capability MUST have qualification evidence for its supported Lean toolchain and actual detection implementation. When implementation or configuration changes, identify which capabilities and invocation paths the change can affect and obtain focused evidence for those capabilities. Existing evidence remains usable for behavior whose implementation, dependencies, and invocation contract are unchanged. A new checker version or an unrelated fixture edit does not by itself require repeating the complete qualification suite. Qualification observations establish the exercised detector behavior, not universal checker correctness.

Each mutation MUST introduce one intended defect into an otherwise passing disposable surface. The run must establish the intended failure reason and a green control that the mutation’s artifacts cannot satisfy. When the mutation shares a workspace with its control, the run must remove the mutation and all generated Lean artifacts and re-establish the green control afterwards. A mutation run in its own fresh disposable workspace, with the green control established in a separate fresh workspace independently of the mutation, satisfies this requirement without a restored rerun. Compound fixtures that fail first for an unrelated reason do not validate later checks.

Qualification MUST exercise the checker's actual detection implementation, through its public entrypoint or the same implementation functions. It MUST NOT substitute independently reimplemented detection logic. A changed public invocation, transport, or integration path requires an end-to-end control through that path; otherwise applicable existing integration evidence may be reused. An in-process control establishes only the path it exercises.

Share an unchanged workspace, baseline, and loaded environment where the control remains valid. Keep mutation artifacts separate from restored controls. Clean-checkout, packaging, adopter, and build-integration diagnostics apply when those mechanisms change or their qualification is explicitly claimed. The complete diagnostic campaign remains available for broad qualification; it is not a mandatory gate for every checker change.

The following catalogue describes the shipped diagnostic campaign. Select controls by the affected capability; the catalogue is not a per-change execution checklist. A report claiming complete campaign coverage must establish every listed applicable result:

* Kernel-only, Choice-Free, and Standard-Logical positive declarations;
* unchecked declarations admitted by local options, restored options, or direct APIs; forged correspondence dependencies; valid checked and preliminary-then-checked controls;
* a lemma Lean realizes in a claimed module and in the toolchain, imported in both orders, as positive controls; as mutations, an unchecked copy of a checked theorem imported first or last, ill-typed, circular or proved by `sorry`, and two unchecked copies of toolchain lemmas proving each other that the audited environment keeps;
* negative diagnostics occurring only in non-error output, patterns split across errors, legitimate multiline errors, and abnormal worker termination;
* direct and transitive project axioms;
* `sorry`, attributed theorems, proof-valued definitions, and proof-valued instances;
* direct and transitive `Classical.choice` against a Choice-Free claim;
* project axioms imitating a native generated name, including an authored `axiom` declaration with a native name and a natively true statement, and a custom-frontend forgery of the complete final semantic shape of a native proof, which is classified compiler-trusting;
* user declarations with private/internal/auxiliary-looking names;
* native proofs, regenerated safe-recursion controls (among them recursion through the toolchain's `attach` and `forIn'` rewrites, and a module whose macros override the tactics and the term the regeneration would otherwise dispatch), an authored unsafe-recursion-name spoof, a custom-command forgery of the complete helper metadata shape, a `run_tac` forgery nested in an ordinary built-in declaration, custom tactic-, term-, match-, and command-elaborator forgeries of the same helper evidence, including elaborators installed before the forged declaration, a `by_elab` forgery, a forged helper that calls the audited module's own constant under the name root the regeneration uses in place of its base's callee, a base whose decreasing proof rests on a project axiom, a project `wf_preprocess` rule that removes the helper's recursive call from its base, a derived `partial` `BEq`, and `partial`, ordinary, and opaque `unsafe` declarations as escape hatches;
* an owned `@[implemented_by]` replacement and an owned `@[extern]` declaration as permitted-but-reported trusted execution boundaries, an unmarked `Float32` wrapper whose passing standard-logical label coexists with a trusted native-runtime boundary, a proved replacement correspondence passing a checked-correspondence execution claim, legitimate dependent/proof domains and general universes, and independent conditional-premise, specialized-universe, and restricted-input equalities that cannot establish the full correspondence. Exercise whole-function and partial/pointwise proofs as controls, with repeated or omitted input arguments unable to weaken the required proposition. The same replacement shape without evidence must fail the checked claim, and unresolved execution paths block the execution claim in every mode. A real toolchain runtime primitive remains reported and permitted in checked mode; an extern in a project or dependency module with an `Init` name must remain external and fail that mode;
* imported `csimp` controls in legacy and module-system Lean files, chained and both-order `csimp`/`implemented_by` interactions, reachable extern/unsafe/partial targets, expired local and overwritten simplifications, proof-valued simplification evidence, and overwritten inlined implementations. Each gets an independent passing control, intended-reason mutation, and fresh restored control through the public file entrypoint; imported extern controls also exercise the project entrypoint. Require explicit cycle/unsupported-history failures. Inspect emitted code for a diagnostic external target without linking or executing it; that observation qualifies discovery and does not prove compiler correctness or external implementation equality;
* a new module discovered through the Lake library glob, an exact module-name lookalike, and a root-owned module outside every library, plus a negative-fixture import into the positive surface;
* an audited-module command registration that collides with the interactive probe token while the trusted runner still inventories and rejects a seeded project axiom;
* missing, malformed, or semantically incomplete surface manifests, including an unclassified root-package Lean library or `lean_exe` target, a claimed executable root whose source is removed, and a claimed executable root importing an excluded fixture module;
* for the complete-application control, an omitted executable classification, a deleted required update proof, an unrelated trivial proof, an extra-premise weakened proof, a missing proof field, and a weakened admission guard. Each fails for its own missing obligation or coverage diagnostic, not an injected axiom;
* warning suppression, holes, and forbidden axioms in documentation fences; and
* every malformed marker/fence state listed in §7.7.

The qualification harness MUST use unique temporary paths. It MUST NOT overwrite fixed positive-source files in place or leave `.olean` files that could satisfy a later control. These tests qualify a checker implementation and do not add a second proof obligation to each theorem in a project that uses the checker.

# 7.9 Optional Fresh Serialized-Graph Checking
%%%
tag := "79-optional-fresh-serialized-graph-checking"
number := false
%%%

*Optional additional claim*: The ordinary conformance gate combines fresh warning-free elaboration with completed owned logical admission under §7.3. A project MAY additionally claim that its serialized `.olean` graph was rechecked in a separate compatible checker state. That additional claim is not required for ordinary conformance to the proof, declaration, or axiom rules.

For toolchains that provide Lean's bundled checker, the shipped `freshChecker` implements the additional check:

```sh
lake exe freshChecker --verbose
```

`leanchecker --fresh` reads produced `.olean` files and rechecks serialized declarations in a fresh checker state. It does not prove a stronger theorem than the fresh source build, and it does not replace source elaboration, warning checking, module discovery, foundation classification, or documentation checks.

The driver derives transitive imports through Lake's module facets, selects every maximal claimed module as a fresh root, intersects each root's closure with the exact claimed inventory, and requires the union to equal that inventory. A claimed standalone executable root that no other claimed module imports is maximal and appears as its own fresh root. If one umbrella root does not cover every module, the driver invokes `leanchecker --fresh` on the additional roots. Because `leanchecker` reads the produced `.olean` files, the driver first builds the manifest's claimed libraries and executable roots and requires that build to succeed warning-free. The rechecked graph is therefore up to date according to Lake’s dependency traces for that build. This build is incremental and can reuse existing artifacts. “Fresh” describes the separate checker state, not a rebuild from empty output. This driver does not establish §7.3’s fresh-source evidence. A project that makes this optional serialized-graph claim MUST reject unsupported, skipped, timed-out, or partially covered runs; otherwise the additional claim is unverified. Omitting the additional claim does not weaken or change the foundation label of a kernel-checked declaration.

# 7.10 Adopting the Checker in Another Project
%%%
tag := "710-adopting-the-checker-in-another-project"
number := false
%%%

The checker package is self-contained: an external Lean project adopts it by requiring the package and adding a surface manifest at its own root, with no Lake facets, module names, or fixture layout borrowed from this repository.

* The adopting project MAY use an ordinary `lakefile.lean` or `lakefile.toml`; both load through the same Lake workspace discovery (§7.2). A project providing both files is ambiguous and fails closed.
* The adopter classifies every root-package `lean_lib` and `lean_exe` in `foundation_manifest.json` at its project root (or at an explicit `--manifest PATH`), with empty exclusion arrays when nothing is excluded.
* The trusted environment probe (`Regula.Probe`) and its typed records (`Regula.Report`) ship inside the checker library. Modules resolving from the checker package's own compiled-module directory are tooling infrastructure and are never attributed to an adopter's surface. A claimed module may import the published interfaces `Regula.Contract` (the executable-contract API of §7.11) and `Regula.MaterialClaim` (the `@[regula_material]` registration that selects the RG5002/RG5003 obligations of {ref "52-faithful-explanation-of-formal-claims"}[module 5 §5.2]); the probe force-loads both, so their declarations belong to no claimed surface and, like the probe, resolve from the checker's own compiled-module overlay. Any other module in the audited import environment that directly imports `Regula.Probe` or `Regula.Report`, in whatever package, fails as `unexpected-project-module` (a §7.8 structural control; Lake resolves imports workspace-wide, so the scan covers every module's recorded direct imports).
* The checker package requires nothing beyond the Lean toolchain, and its libraries and executables import no Mathlib modules. Requiring it adds only the checker package to the adopter's `lake-manifest.json`, so an adopter with or without Mathlib keeps its own dependency revisions; a Core/Std-only adopter compiles only its own claimed surface plus the checker.
* Runs execute from the adopter's project root or an explicit `--project DIR`. Scratch work, including the §7.3 isolated disposable copy, uses a temporary directory under the checked project's `tmp/` and is removed afterward.
* The normal project-wide gate builds in its own isolated copy (§7.3), so it does not need a preliminary build of the claimed surface in the main checkout. Single-file audits and the enforcing build linter use incremental builds in the target checkout. Establish a shared baseline before concurrent qualification runs, and avoid concurrent builds writing the same workspace output. Separate audit copies still share dependency checkouts, whose missing artifacts may need building.

An adopter also enables the community linters that {ref "67-community-conventions-and-linters"}[module 6 §6.7] requires and runs the recommended ones beside the checker:

* In the Lake `leanOptions` of every claimed library and executable, `linter.missingDocs` set to `true`, `autoImplicit` and `relaxedAutoImplicit` set to `false` (§7.1) and, in a surface that imports Mathlib, `weak.linter.mathlibStandardSet` set to `true` with the Mathlib-repository linters that §6.7 lists turned off (the header linter may instead be set to `true` with its license line configured). Their warnings are build warnings, so the checker's warning-free build rejects them (RG2003). RG2006 checks every one of these options.
* Batteries' environment linters run as a separate command, `lake exe runLinter`. It lints the built modules and builds only a module that has no build output, so a stale build is linted as it is: run `lake build` first on either route. Lake has one `lintDriver` per package: a project that keeps `batteries/runLinter` as its driver runs `lake build && lake lint` and the checker with `lake exe lint`, and a project whose driver is `regula/lint` runs `lake lint` and, separately, `lake build && lake exe runLinter`. Each command's success establishes only its own checks.

The exact adapter steps, including glob syntax in both lakefile formats, a minimal manifest, and the community linter configuration, are in this repository's {repo "docs/guides/adoption.md"}[adoption guide].

# 7.11 Opt-in Enforcing Build Linter
%%%
tag := "711-opt-in-enforcing-build-linter"
number := false
%%%

An adopter MAY enable the shipped whole-surface Lean build linter. Once enabled, it MUST enforce its selected foundation and execution requirements: an emitted source warning, a policy violation, or an unresolved claimed path fails the build. This mode is not advisory: no source-local option authorizes an exception to its foundation or execution policy. A declaration-scoped disable of a community linter ({ref "62-module-purpose-and-linter-discipline"}[module 6 §6.2]) stops only that linter's warning and changes no policy result.

The {repo "examples/build-lint/"}[complete minimal adopter] contains the public recipe:

1. Require the pinned checker package in `lakefile.lean`, set the linter options of {ref "67-community-conventions-and-linters"}[module 6 §6.7] and the options of §7.1 in its `leanOptions`, and import `Regula.Contract` where executable contracts are declared.
2. Classify every root-package library and executable in `foundation_manifest.json` (§7.2). Select `kernel-only`, `choice-free`, or `standard-logical` and `report` or `checked`.
3. Copy the sample's `policy` target and make it the *sole default target*. It obtains `axiomGate` from the `regula` package through Lake, then invokes its `--build-lint` mode for the consuming package.
4. Run ordinary `lake build`. The target builds the linter, then the linter builds the exact manifest-derived library/executable targets incrementally and inspects the completed environments. It never recursively invokes the default target.

This uses Lake's native custom-target/job API. A per-declaration linter alone does not establish this complete project claim. The build target instead reuses the existing `Admission.validate`, `Probe.environmentReport`, `Policy.ruleForMember` (equal to `Policy.ruleFor` on every inventory member), `Policy.executionFailures`, Lake discovery, and fresh evaluator attribution. It adds no second foundation or execution policy.

The same audit is also available as Lake's lint driver, in either lakefile format: set `lintDriver` to `"regula/lint"` and run `lake lint`. The driver runs the identical `axiomGate` project audit, incrementally or with `--fresh`, and adds no policy. Its exit code is 0 only when that audit exited zero and recorded a completed accepted result. Otherwise it is 1 for completed violations, 2 for configuration-only rejections, an invalid driver argument, or a working directory that is not the workspace `lake lint` was dispatched from (`lake -d`/`--dir` from another project), and 3 when any finding is incomplete, the driver's build of the audit's `regula/axiomGate` worker in the invoking workspace fails, the working directory is outside any Lean project or its workspace fails to load, or an error escapes the audit. `--help` and `--explain-config` run no audit and exit 2, so a `lintDriverArgs` entry cannot turn `lake lint` into a success. The driver's audit builds the claimed targets with the root package's audit-build marker (`Lake.auditLeanOptions`, the unregistered `weak.regula.auditBuild`: every command scope ignores it and elaborates exactly as without it), an option in Lake's module trace. `Regula.Linter` reads the marker only from a module's import-time options, which no source command can change, and under it emits no local finding whatever a command scope sets `linter.regula` to (`RegulaCore.EditorPolicy.liveFeedback_auditBuild`), so the audit's warning-free build check measures only non-Regula warnings, and neither a live finding nor a log replayed from a build with live feedback stops it as incomplete. Lake scopes Lean options by package and library, not by module, so this trace change rebuilds every root-package module last built with ordinary options; `axiomGate` and the build-lint target therefore keep ordinary options, and there a live finding stops the warning-free build check as incomplete. No live rule is lost: a RG1001–RG1007 rule the editor renders is the project `ruleForMember` rule for the same member and request (`Regula.Checker.Policy.editor_decision_rule`), RG5001–RG5003 use the `Regula.Linter.Documentation` predicates (`moduleObservation` with `RegulaPolicy.ModuleHeader.failures`, `selected`, `RegulaPolicy.materialDocumentationFailure`) that the audit's documentation-presence stage also runs, and an editor RG2002 refuses only the local option, whose project counterpart is the manifest; RG2005 is editor-only deferral to this audit. A source `set_option linter.regula false` or `true` changes only local feedback: the audit's policy stages still reject, and under the driver's audit a re-enabled live finding is not a build warning. Lean's own warnings are unaffected by this option: by default (Lean's `warn.sorry`) an owned `sorry` still emits Lean's `declaration uses 'sorry'` warning, so the driver's audit stops at its warning-free build check as incomplete before its RG1002 stage; with `warn.sorry` off, the RG1002 stage rejects it. `lake lint --builtin-only` skips the driver and establishes nothing under this section.

## Exact contract and coverage scope
%%%
tag := "exact-contract-and-coverage-scope"
number := false
%%%

The public proof API is `ExecutableContract implementation condition : Prop`, with a field `evidence : condition implementation`. A *closed declaration* of this type registers a promised executable. Its elaborated predicate is applied to the actual constant by the type, so unrelated or weakened evidence cannot inhabit the unchanged requirement. `contract.run` returns that constant and requires the contract during elaboration ({ref "38-delivering-executable-witnesses-with-required-evidence"}[module 3 §3.8]). The proof is erased at runtime; this API does not perform a runtime validation. Application-specific proof interfaces remain valid, and callers that bypass a proof-requiring interface need separate review.

For this registration API, the implementation must be a named `def` or body-bearing `opaque` producing runtime data, with its entire argument domain inside the predicate. The linter rejects noncomputable, unsafe, partial, proof-valued, or type-producing roots, partial applications, and parameterized registrations. Universe-polymorphic constants are permitted; term parameters outside the predicate are unsupported. The report prints the registered root and its required proposition. Lean checks the evidence; the gate checks its transitive axioms against the selected surface policy, as it does for every other owned declaration.

The tool inspects all exact Lake-owned declarations, including private, generated, and unused declarations. The ordinary executable roots of §7.6 remain covered; explicitly registered private or imported roots additionally receive the same conservative execution closure. Imported roots remain unowned, but their reached boundaries and transitive logical dependencies do not disappear. An erased classical correctness proof is permitted under Standard-Logical; it does not by itself make its function noncomputable. `extern`, `implemented_by`, `csimp`, unsafe/partial targets, and unresolved paths retain the exact §7.6 policy and supported-process boundary.

## Build and cache semantics
%%%
tag := "build-and-cache-semantics"
number := false
%%%

* The `policy` job has no cached success artifact. Every enabled default build reloads the manifest and Lake inventory and reinspects the completed module environments, even if all `.olean` files were reused. A changed profile or execution policy therefore cannot inherit an old linter verdict. Added glob-discovered modules are inspected without umbrella imports.
* Source and imported-dependency invalidation use Lake's ordinary dependency traces. The claimed modules finish building before policy inspection; no per-declaration hook launches a build. Generated-role and replacement-history checks still require the existing fresh, exact-source frontend attribution where applicable, shared only under the identical-input condition of §7.6.
* This is *incremental elaboration plus current policy inspection*, not §7.3's fresh-source conformance evidence. It trusts Lake's build cache and the pinned supported process. The ordinary fresh `axiomGate` remains available and required for that conformance claim; documentation and semantic matrix rows remain separate.
* The supported enforcing paths are the sample's `lakefile.lean` default target with plain `lake build` (or explicit `lake build policy`), and `lake lint` with the `lint` driver in either lakefile format. Direct `lean`, editor elaboration, `lake build Widget`, another default target, `lake lint --builtin-only`, and a `lakefile.toml` build without the lint driver do not invoke this audit and MUST NOT be reported as enforced. Native editor diagnostics from `Regula.Linter` are local feedback over one snapshot; they never establish this section's project result, and local options that silence them do not change it. Do not install it as a library/package `extraDepTargets` prerequisite, which would create a cycle with the modules it builds, or combine it with concurrent builds of those modules.
* Removing the default target disables policy enforcement; ordinary Lean typing still checks explicit evidence arguments. Removing or narrowing requirements, intentionally changing library globs or exclusions, and bypassing proof-requiring callers change the claim itself. Semantic review MUST establish intended coverage and contract adequacy. A linter PASS alone establishes neither intended coverage nor full-standard conformance.

## Qualification
%%%
tag := "qualification"
number := false
%%%

The build-bound `checkerSelftest` suite copies the public sample into isolated standalone adopters. It drives actual `lake build`: all three profiles, direct/transitive choice, classical erased evidence, missing/unrelated/weakened evidence, noncomputable witnesses, unsupported registrations, private and imported executable boundaries, unimported configured modules, unclassified libraries, configuration changes, cached failures, disabled/reenabled behavior, and fresh restoration. The same tier's external-adopter phase runs `axiomGate` from scratch adopters that require the checker by absolute path in both lakefile formats and by relative path (the nested-repository form), so an actual gate run exercises the §7.3 copy's re-anchoring of relative `path` dependencies, and the tier's structural warning-suppression control requires a warning's continuation text in the gate transcript. Unchanged compiler-path controls additionally qualify the shared §7.6 machinery; they are not rerun from each adopter build. The `lint-driver` partition drives actual `lake lint` in disposable copies of both shipped adopters (`lakefile.lean` and `lakefile.toml`): accepted, violation, repeated cached violation, configuration, invalid-argument and incomplete exit classes, builtin-only and combined builtin/driver dispatch, a read-only configuration explanation, a violation hidden from the editor by `set_option linter.regula false`, a violation whose live feedback the source re-enables with `set_option linter.regula true`, fresh restoration, acceptance after the checker's `axiomGate` worker binary is removed, which the driver itself must rebuild, and refusal of `lake lint -d` dispatched from another project root. These controls establish diagnostic qualification, not a universal proof of the linter implementation.
