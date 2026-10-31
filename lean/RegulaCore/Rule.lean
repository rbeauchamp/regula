module

public import RegulaCore.RuleId
public import RegulaCore.Edition
public import RegulaCore.Standard

/-! # Rule registry

Shared metadata of every rule. See RuleId for con-leche attribution.

The registry is the one source of each rule's agent-facing guidance: its one-line
`requirement`, short `rationale`, imperative `remedy`, common compliant `rewrites` and
`examples` pair are required `RuleDescriptor` fields, so a rule without them does not compile.
The `regula` command and agent briefing (`RegulaCore.Guidance`) and the website are generated from
them. `checkOf` states what checks each rule.

Each position of a rule's `lifecycle` (its introduction and, once retired, its retirement) is a
`Build`: `.unreleased` until the next release, whose release pull request (the Release workflow's
`open` step) stamps it on `main`. `lifecycle` has no default, so every rule states it.
`release_attributes_rules` proves that when `Regula.installed` is a release, which only the release
commit CI creates is, no lifecycle position of any rule is `.unreleased`, so a release commit that
still has one does not build and nothing is published, `lifecycle_listed` that every release a
lifecycle names is in `Regula.versions`, and `introduced_startsLine` that no patch release
introduces a rule. -/

@[expose] public section

namespace Regula

/-- Retired IDs remain descriptors; replacement cannot be the retired ID itself. -/
inductive Lifecycle (id : RuleId) where
  /-- The rule is in force; `introduced` names the release that added it. -/
  | active (introduced : Build)
  /-- The rule was added in release `introduced` and retired in `version`; `replacement` is the
  rule that takes over its checks, if any, and cannot be `id` itself. -/
  | retired (introduced version : Build) (replacement : Option { other : RuleId // other ≠ id })

/-- The release that introduced the rule, as its lifecycle records it. -/
def Lifecycle.introduced {id : RuleId} : Lifecycle id → Build
  | .active introduced => introduced
  | .retired introduced _ _ => introduced

/-- Every position of the lifecycle: the introduction and, when retired, the retirement. -/
def Lifecycle.builds {id : RuleId} : Lifecycle id → List Build
  | .active introduced => [introduced]
  | .retired introduced version _ => [introduced, version]

/-- Whether the rule is retired: written guidance that no check reports. -/
def Lifecycle.isRetired {id : RuleId} : Lifecycle id → Bool
  | .active _ => false
  | .retired .. => true

/-- The kind of property a rule checks; the rule index groups and filters rules by it. -/
inductive RuleCategory where
  /-- The logical foundation of declarations: axioms, proof holes, compiler trust and the
  surface profile (RG1001–RG1005). -/
  | foundation
  /-- The form of a declaration itself, such as `unsafe` or `partial` (RG1006). -/
  | declaration
  /-- Executable contracts, decision contracts and the execution closure of executable roots
  (RG1007–RG1009, RG3001, RG3002). -/
  | execution
  /-- Availability of the declared Lean environment (RG2001). -/
  | environment
  /-- The surface manifest and the Lake build configuration (RG2002, RG2006). -/
  | configuration
  /-- Warning-free elaboration of claimed source (RG2003). -/
  | elaboration
  /-- Attribution of owned modules to classified targets (RG2004). -/
  | coverage
  /-- Kernel-replay admission and source evidence (RG2005). -/
  | admission
  /-- Documentation fences, module headers and docstrings (RG4001–RG4004, RG5001–RG5003). -/
  | documentation
  deriving Repr, BEq, DecidableEq

/-- The severity of a rule's findings under a strict claim. -/
inductive Severity where
  /-- The highest level; `RuleDescriptor.defaultStrictSeverity` defaults to it. -/
  | error
  /-- Below `error`. No registered rule defaults to it. -/
  | warning
  /-- The lowest level. No registered rule defaults to it. -/
  | information
  deriving Repr, BEq, DecidableEq

/-- The severity names used by the registry and diagnostics. -/
def Severity.spelling : Severity → String
  | .error => "error" | .warning => "warning" | .information => "information"

/-- Whether a finding shows the rule violated or leaves the check incomplete. Display severity
cannot change it. -/
inductive Impact where
  /-- The checked source or configuration violates the rule. -/
  | violation
  /-- Evidence the rule needs is missing or could not be obtained, so the check did not
  complete. -/
  | incomplete
  deriving Repr, DecidableEq

/-- What one finding of a rule is about. -/
inductive RuleScope where
  /-- One owned declaration. -/
  | declaration
  /-- The project: its environment, configuration, build, inventory or admission. -/
  | project
  /-- One executable root and its execution closure. -/
  | executionRoot
  /-- One Lean fence of the checked documentation. -/
  | documentationFence
  /-- One claimed module. -/
  | module
  /-- One declaration that states a material claim. -/
  | materialDeclaration
  deriving Repr, BEq, DecidableEq

/-- The evidence a rule's decision reads. -/
inductive EvidenceKind where
  /-- The transitive axiom sets of declarations. -/
  | kernelAxioms
  /-- The authenticated role of a generated declaration, such as the axiom of a native proof
  (`native_decide`, `decide +native` or `bv_decide`) or the helper of an `unsafe` or `partial`
  definition. -/
  | generatedRole
  /-- `ExecutableContract` registrations and `Regula.RegisteredDecision` registrations. -/
  | contractEvidence
  /-- The loaded Lake workspace, toolchain and dependencies. -/
  | environment
  /-- The surface manifest or Lake's resolved build configuration. -/
  | configuration
  /-- Elaboration messages of the claimed source. -/
  | compilation
  /-- The Lake module inventory and module attribution. -/
  | inventory
  /-- Kernel-replay admission and source-identity evidence. -/
  | admission
  /-- The execution closure of executable roots. -/
  | executionClosure
  /-- The marker and fence structure of documentation. -/
  | fenceGrammar
  /-- The outcome of elaborating a documentation example. -/
  | checkedExample
  /-- The presence of module and declaration docstrings. -/
  | metadataPresence
  deriving Repr, BEq, DecidableEq

/-- The scope of each rule's findings; `RuleDescriptor.scope` defaults to it. -/
def scopeFor : RuleId → RuleScope
  | .projectAxiom | .proofHole | .unknownAxiom | .compilerTrusting | .profileExceeded
  | .escapeHatch | .executableContract | .decisionContract | .sharedTest => .declaration
  | .environment | .configuration | .sourceBuild | .coverage | .admission
  | .communityConfiguration => .project
  | .executionUnresolved | .executionBoundary => .executionRoot
  | .fenceStructure | .positiveExample | .negativeExample | .trustedExample => .documentationFence
  | .moduleDocumentation | .closedSubset => .module
  | .materialDocumentation | .materialIntent => .materialDeclaration

/-- The type whose declarations select the functions a rule checks, for a rule whose subjects the
project selects; `none` for a rule that checks every member of its scope. Removing such a
registration removes the rule's requirement from that function, so the rule's text does not say
that no declaration changes its result (`Guidance.explain`). -/
def registrationFor : RuleId → Option String
  | .decisionContract => some "Regula.RegisteredDecision"
  | .projectAxiom | .proofHole | .unknownAxiom | .compilerTrusting | .profileExceeded
  | .escapeHatch | .executableContract | .sharedTest | .environment | .configuration
  | .sourceBuild | .coverage | .admission | .communityConfiguration | .closedSubset
  | .executionUnresolved | .executionBoundary | .fenceStructure | .positiveExample
  | .negativeExample | .trustedExample | .moduleDocumentation | .materialDocumentation
  | .materialIntent => none

/-- The evidence each rule's decision reads; `RuleDescriptor.evidenceKind` defaults to it. -/
def evidenceFor : RuleId → EvidenceKind
  | .projectAxiom | .proofHole | .unknownAxiom | .profileExceeded => .kernelAxioms
  | .compilerTrusting | .escapeHatch => .generatedRole
  | .executableContract | .decisionContract | .sharedTest => .contractEvidence
  | .environment => .environment
  | .configuration | .communityConfiguration => .configuration
  | .sourceBuild => .compilation
  | .coverage | .closedSubset => .inventory
  | .admission => .admission
  | .executionUnresolved | .executionBoundary => .executionClosure
  | .fenceStructure => .fenceGrammar
  | .positiveExample | .negativeExample | .trustedExample => .checkedExample
  | .moduleDocumentation | .materialDocumentation | .materialIntent => .metadataPresence

/-- Source language of a rule's example files. -/
inductive ExampleLanguage where
  /-- Lean source, including a `lakefile.lean`. -/
  | lean
  /-- JSON, such as a `foundation_manifest.json`. -/
  | json
  /-- Markdown documentation. -/
  | markdown
  deriving Repr, BEq, DecidableEq

/-- File extension of the example files, as in `examples/rules/<ID>/Fixed.<ext>`. -/
def ExampleLanguage.extension : ExampleLanguage → String
  | .lean => "lean" | .json => "json" | .markdown => "md"

/-- Markdown info string of a fence that shows the example. -/
def ExampleLanguage.fence : ExampleLanguage → String
  | .lean => "lean" | .json => "json" | .markdown => "markdown"

/-- A rule's example pair: the exact bytes of `examples/rules/<ID>/Fixed.<ext>`
(compliant) and `Violation.<ext>` (noncompliant), embedded with `include_str`. No run of the
checker reads them: the registry checks compare them with the files (`Regula.RegistryChecks`), and
the rule's page and `regula explain` show them. `correction` states what the correction changes
and preserves. -/
structure ExamplePair where
  /-- The language of both files, which fixes their extension. -/
  language : ExampleLanguage
  /-- The bytes of `Fixed.<ext>`, the compliant file. -/
  compliant : String
  /-- The bytes of `Violation.<ext>`, the noncompliant file. -/
  noncompliant : String
  /-- What the correction from the noncompliant to the compliant file changes and preserves. -/
  correction : String

/-- Repository path of the compliant example of rule `id`, derived from its identity. -/
def ExamplePair.compliantPath (id : RuleId) (p : ExamplePair) : String :=
  "examples/rules/" ++ id.spelling ++ "/Fixed." ++ p.language.extension

/-- Repository path of the noncompliant example of rule `id`, derived from its identity. -/
def ExamplePair.noncompliantPath (id : RuleId) (p : ExamplePair) : String :=
  "examples/rules/" ++ id.spelling ++ "/Violation." ++ p.language.extension

/-- Identity and route are projections of the index, never independent fields.
The agent-facing fields `requirement`, `rationale`, `remedy`, `rewrites` and `examples` have
no defaults: omitting one from a rule is a compile error, and `RuleDescriptor.wellFormed`
(checked for every rule when `RegulaCore.Guidance` is built) rejects an empty or oversized
one. The `regula` command, the agent guide and the website are generated from these fields. -/
structure RuleDescriptor (id : RuleId) where
  /-- The rule's short name, stated as the property it demands. -/
  title : String
  /-- The kind of property the rule checks. -/
  category : RuleCategory
  /-- The sections of the standard the rule enforces. -/
  normativeClauses : List Clause
  /-- What the rule demands, in one line. -/
  requirement : String
  /-- Why the rule exists, in one short paragraph. -/
  rationale : String
  /-- The imperative action that complies, in one line. -/
  remedy : String
  /-- The common compliant rewrites, most common first. -/
  rewrites : List String
  /-- The checked compliant and noncompliant examples. -/
  examples : ExamplePair
  /-- Whether the rule is active or retired, and since which release: `.active .unreleased`
  until a release introduces it. No default, so every rule states it on the `lifecycle :=` line
  the release step stamps. -/
  lifecycle : Lifecycle id
  /-- The severity of the rule's findings under a strict claim. -/
  defaultStrictSeverity : Severity := .error
  /-- What one finding is about, derived from the ID by default. -/
  scope : RuleScope := scopeFor id
  /-- The evidence the rule's decision reads, derived from the ID by default. -/
  evidenceKind : EvidenceKind := evidenceFor id

namespace RuleDescriptor
/-- The ID the descriptor is indexed by. -/
def identity {id : RuleId} (_ : RuleDescriptor id) : RuleId := id
/-- The rule page's route, `rules/<ID>/`, derived from the ID. -/
def helpRoute {id : RuleId} (_ : RuleDescriptor id) : String := id.route
end RuleDescriptor

/-- Size budgets, in UTF-8 bytes, that keep the agent-facing fields and the agent guide compact. -/
def requirementBudget : Nat := 200
/-- The largest `rationale`, in UTF-8 bytes. -/
def rationaleBudget : Nat := 480
/-- The largest `remedy`, in UTF-8 bytes. -/
def remedyBudget : Nat := 300
/-- The largest single entry of `rewrites`, in UTF-8 bytes. -/
def rewriteBudget : Nat := 480
/-- The most entries `rewrites` may have. -/
def rewriteCountBudget : Nat := 4
/-- The largest compliant or noncompliant example file, in UTF-8 bytes. -/
def exampleBudget : Nat := 512
/-- The Lean community's line limit (Mathlib's `linter.style.longLine`), for example files, whose
lines every rule page, finding and agent briefing shows verbatim. -/
def exampleLineBudget : Nat := 100

/-- Every line of `text` has at most `exampleLineBudget` characters. -/
def linesWithin (text : String) : Bool :=
  (text.splitOn "\n").all (·.length ≤ exampleLineBudget)

/-- Nonempty text of at most `budget` UTF-8 bytes. -/
def withinBudget (text : String) (budget : Nat) : Bool :=
  0 < text.utf8ByteSize && text.utf8ByteSize ≤ budget

/-- Every agent-facing field has content within its budget, the one-line fields contain no
line break, every example line fits the community's 100-character limit and the two examples
differ. The registry checks this for every rule when `RegulaCore.Guidance` is built (`#guard` over
the complete `RuleId.all`): evaluation, because kernel reduction of these long string literals
costs seconds per field. -/
def RuleDescriptor.wellFormed {id : RuleId} (d : RuleDescriptor id) : Bool :=
  withinBudget d.requirement requirementBudget && !d.requirement.contains '\n' &&
  withinBudget d.rationale rationaleBudget &&
  withinBudget d.remedy remedyBudget && !d.remedy.contains '\n' &&
  d.rewrites.length ≤ rewriteCountBudget &&
  d.rewrites.all (fun r => withinBudget r rewriteBudget && !r.contains '\n') &&
  withinBudget d.examples.compliant exampleBudget &&
  withinBudget d.examples.noncompliant exampleBudget &&
  linesWithin d.examples.compliant && linesWithin d.examples.noncompliant &&
  d.examples.compliant != d.examples.noncompliant &&
  0 < d.examples.correction.utf8ByteSize

/-- Total metadata for the rule vocabulary. An active rule is enforced by the checker, or, for
RG2003 and RG2005, by the Lean tool that the specification hands it to; a retired rule is written
guidance that no check reports (`Lifecycle.retired`, `checkOf`).
Example bytes are embedded from `examples/rules/<ID>/`; the `RegulaCore` library `needs` that
directory as a Lake input, so editing an example rebuilds this module. -/
def descriptor : (id : RuleId) → RuleDescriptor id
  | .projectAxiom => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Project logical axioms are forbidden", category := .foundation
      normativeClauses := [.proofCompleteness]
      requirement := "A claimed module declares no logical `axiom`: every assumption is a \
        hypothesis or a proof-bearing field."
      rationale := "An axiom extends Lean's logic for everything that imports it. An assumption \
        that is false, or inconsistent with other axioms, makes every downstream theorem vacuous, \
        and the kernel cannot tell. A hypothesis keeps the assumption visible in each theorem's \
        type, so every use must supply it."
      remedy := "Turn the assumption into a hypothesis (a binder or a proof-bearing structure \
        field) of the results that need it, or replace the axiom with a proof."
      rewrites := [
        "If the statement is provable, prove it: replace `axiom name : P` by `theorem name : P := \
          proof`.",
        "If it is a genuine assumption of a model, make it a parameter: `theorem result (h : P) : \
          Q`, or a field of a structure that bundles the model and its laws.",
        "If it states an open research target, define it as a `Prop` (`def Target : Prop := P`) \
          and state results conditionally on it; do not assert it."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG1001/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG1001/Violation.lean"
        correction := "The correction proves the same `∀ n : Nat, n = n` by `rfl` instead of \
          assuming it, under the unchanged Kernel-only claim." } }
  | .proofHole => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Proof holes are forbidden", category := .foundation
      normativeClauses := [.proofCompleteness]
      requirement := "No owned declaration depends on `sorryAx`: no `sorry`, `admit` or unfinished \
        proof, directly or through an import."
      rationale := "`sorryAx` proves every proposition. A declaration that depends on it has no \
        evidence, even if Lean elaborated the file, and every theorem that uses it inherits the \
        gap."
      remedy := "Complete the proof. If the statement is an open problem, define it as a `Prop` \
        and state results conditionally on it instead of asserting it."
      rewrites := [
        "Replace the `sorry` or `admit` with a complete proof.",
        "If the hole comes from an imported declaration, fix or replace that dependency; imported \
          holes are not exempt.",
        "For an open target, write `def Target : Prop := …` and prove `Target → Result`, which \
          states exactly what is established."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG1002/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG1002/Violation.lean"
        correction := "The correction fills the same reflexivity proof with `rfl`. The checked \
          violation records Lean's original `sorry` warning as well; the corrected file passes the \
          ordinary warning-rejecting gate." } }
  | .unknownAxiom => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Unknown transitive axioms are forbidden", category := .foundation
      normativeClauses := [.proofCompleteness]
      requirement := "Every transitive axiom of an owned declaration, including one from an \
        import, is `propext`, `Quot.sound` or `Classical.choice`."
      rationale := "A foundation label summarizes exactly which assumptions a result rests on. An \
        unclassified axiom has no label, so no profile claim about the declaration can be true."
      remedy := "Find where the axiom enters (often an imported dependency), and replace that \
        dependency or its axiom with a proof or a hypothesis."
      rewrites := [
        "Inspect the declaration's axiom list in the diagnostic or with `#print axioms`, and \
          follow it to the declaration that introduces the axiom.",
        "Replace the axiom in the dependency with a proof, or make it a hypothesis of the results \
          that need it.",
        "If the dependency cannot change, do not claim the affected declarations on a conforming \
          surface."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG1003/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG1003/Violation.lean"
        correction := "The examples are the imported dependency. It proves the same reflexivity \
          statement instead of declaring it as an axiom, and the file that imports it is \
          unchanged." } }
  | .compilerTrusting => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Compiler-trusting proofs require separate classification", category := .foundation
      normativeClauses := [.proofCompleteness]
      requirement := "Claimed declarations use no compiler-trusting proof: no native proof or \
        legacy compiler-trust axiom declared by the selected compiler."
      rationale := "Compiled evaluation is outside the kernel's checking. A compiler or runtime \
        defect could make a false proposition \"proved\". Compiler-trusting is therefore not one \
        of the three logical labels and never counts as conforming evidence."
      remedy := "Prove the same statement with a kernel-checked proof, for example `decide` \
        (kernel reduction), `rfl` or an ordinary proof."
      rewrites := [
        "Replace `by native_decide` or `by decide +native` with `by decide` when kernel \
          reduction of the decision procedure is feasible.",
        "Replace `by bv_decide` with a proof from `BitVec` library lemmas, or with `bv_normalize` \
          when normalization alone closes the goal.",
        "Otherwise give a structural proof, or prove a smaller lemma that `decide` can handle and \
          combine the pieces.",
        "If the example exists only to teach the mechanism, keep it in documentation as a \
          trusted-compiler teaching fence (RG4004), never on a claimed surface."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG1004/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG1004/Violation.lean"
        correction := "The correction proves the same three facts by kernel-checked proofs: `rfl`, \
          `decide` by kernel reduction, and the library lemma `BitVec.mul_comm`. The violation \
          reports each generated axiom and its parent theorem." } }
  | .profileExceeded => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Transitive axioms must fit the selected profile", category := .foundation
      normativeClauses := [.proofCompleteness]
      requirement := "Each declaration's exact transitive axiom set fits the `claim` of its \
        surface in `foundation_manifest.json`."
      rationale := "A profile claim tells readers which logical principles every result on the \
        surface may use. One declaration above the bound makes the claim false for the whole \
        surface."
      remedy := "Prove the same statement with fewer axioms, or deliberately raise the surface's \
        claim in `foundation_manifest.json` and update its rationale."
      rewrites := [
        "Find the axiom that raises the label in the diagnostic's axiom list, then find the lemma \
          or tactic that introduces it (for example `simp` lemmas using `propext`, or classical \
          reasoning using `Classical.choice`).",
        "Prove the statement constructively or with a narrower lemma so the exact set fits the \
          claim.",
        "If the stronger foundation is intended, change the surface's `claim` and rationale \
          explicitly; this changes the published claim and needs review.",
        "A finding names the constant and its module, also a constant that Lean generated, such \
          as an equation lemma or an auxiliary definition. Fix the declaration it came from, or \
          a definition it uses that adds the axiom."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG1005/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG1005/Violation.lean"
        correction := "The correction proves the same universally quantified reflexivity with an \
          empty axiom set, under the unchanged Kernel-only claim, instead of routing through \
          `propext`." } }
  | .escapeHatch => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Unsafe and partial declarations are refused, except a recursion helper", category :=
          .declaration
      normativeClauses := [.declarationInventory]
      requirement := "Claimed modules declare nothing `unsafe` or `partial`, authored or \
        generated, except the recursion helper `f._unsafe_rec` of a safe definition `f` in the \
        same module, admitted by its form."
      rationale := "A positive proof surface must consist of kernel-checked definitions. Unsafe \
        and partial code can be executed, but it cannot serve as logical evidence, and reasoning \
        about it silently depends on its runtime behavior."
      remedy := "Write a safe, terminating definition (structural recursion or `termination_by`), \
        or move the unsafe/partial code out of the claimed surface."
      rewrites := [
        "Remove an unnecessary `unsafe` marker.",
        "Replace `partial def` by a definition with structural recursion or a `termination_by` \
          measure and `decreasing_by` proof. Lean makes a `partial def f` an opaque constant `f` \
          and a partial helper `f._unsafe_rec`, so the finding names the helper.",
        "Deriving `BEq`, `Hashable`, `Repr` or `Ord` on a nested or mutual inductive (`Ord` on \
          any recursive one) generates a `partial def`, reported under its generated name (such \
          as `instBEqT.beq`); write that instance by structural recursion instead.",
        "If the computation must stay unsafe or partial, move it to a separate, unclaimed \
          dependency package; a claimed module cannot import an excluded module of its own package \
          (RG2004). Where a claimed executable runs it, RG3002 reports it as code that no \
          theorem can bind."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG1006/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG1006/Violation.lean"
        correction := "The correction keeps identity's domain and body and removes the unnecessary \
          `unsafe` marker." } }
  | .executableContract => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Executable contracts require supported closed evidence", category := .execution
      normativeClauses := [.executableContracts, .proofCompleteness]
      requirement := "Each `ExecutableContract f R` is closed and names a safe, computable \
        implementation `f`, with its complete domain inside `R`; a decision kind decides `f` \
        against a specification stated without `f`."
      rationale := "A contract is useful only if it constrains the code callers run. A \
        registration over `f n` for a fixed parameter, or over an ineligible constant, says \
        nothing about the executable definition across its domain; a specification that \
        mentions `f` can restate `f`."
      remedy := "Register the named implementation itself and put its complete domain inside the \
        predicate: `theorem c : ExecutableContract f (fun g => ∀ x, P x (g x))`."
      rewrites := [
        "Move the quantified parameters into the predicate: replace `theorem c (n : Nat) : \
          ExecutableContract (f n) (fun v => v = n)` by `theorem c : ExecutableContract f (fun g \
          => ∀ n, g n = n)`.",
        "Name the computable, safe, non-partial definition that callers use; route callers through \
          `c.run`.",
        "Universe-polymorphic implementations are supported; explicit universe instantiation is \
          recorded. State a decision kind about such an implementation at its own universe \
          parameters. State a decision kind about an implementation applied to every argument: a \
          kind whose result is still a function is refused.",
        "For a checker, state the direction with a kind: `ExecutableContract check (Decides (· = \
          true) Spec)`, or `DecidesSoundly` or `DecidesCompletely` for a one-way guarantee, with \
          `Spec` stated without `check`. Decide several arguments through `Function.uncurry`, or \
          on a structure whose fields are the arguments: `fun g => Decides accepts Spec (fun x : \
          Input => g x.a x.b)`. For a result type that depends on the arguments, decide \
          `Regula.Dependent.isSome g` or `isOk g`."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG1007/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG1007/Violation.lean"
        correction := "The correction moves the complete natural-number domain inside the identity \
          contract's predicate, retaining the same pointwise equality." } }
  | .decisionContract => {
      lifecycle := .active (.release ⟨0, 7, 0⟩)
      title := "Registered decision functions require a decision contract", category := .execution
      normativeClauses := [.executableContracts, .proofCompleteness]
      requirement := "Each function that a `RegisteredDecision` declaration names has a `Decides`, \
        `DecidesSoundly` or `DecidesCompletely` contract in a claimed module, or a `Decidable` \
        result type."
      rationale := "A checker with no stated direction can refuse every input or accept every \
        input, and an unstated one-way guarantee cannot be told from an omission. The registration \
        makes the contract a requirement of the function itself, so deleting the contract while \
        the registration stays fails the gate instead of removing the requirement with it."
      remedy := "Register `theorem c : ExecutableContract f (Decides accepts Spec)` in the \
        function's library or in a surface whose `decides` names that library, with \
        `DecidesSoundly` or `DecidesCompletely` for a one-way guarantee, or return \
        `Decidable (Spec x)`."
      rewrites := [
        "Prove both directions and a witness of each outcome: `ExecutableContract f (Decides (· = \
          true) Spec)`, from an existing equivalence by `Decides.of_iff`. A law \
          `DecisionEquivalence accepts Spec f` alone does not discharge the registration: add the \
          witness it lacks with `law.toSoundly` or `law.toCompletely`.",
        "State a deliberate one-way guarantee with `DecidesSoundly` (may refuse inputs that \
          satisfy `Spec`) or `DecidesCompletely` (may accept inputs that do not).",
        "Decide several arguments on their product, `ExecutableContract f (fun g => Decides \
          accepts Spec (Function.uncurry g))`, or on a structure whose fields are the arguments; \
          for a result type that depends on the arguments, decide `Regula.Dependent.isSome g` \
          or `isOk g` (RG1007).",
        "Return the proof with the verdict: `def f (x : α) : Decidable (Spec x)`. Each result \
          then carries a proof of `Spec x` or of its negation, and no contract is needed."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG1008/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG1008/Violation.lean"
        correction := "The correction registers the two-way contract of the unchanged zero \
          test: it accepts exactly zero, with zero as the accepted input and one as the refused \
          input." } }
  | .sharedTest => {
      lifecycle := .active (.release ⟨0, 10, 0⟩)
      title := "Decision specifications share no Boolean test with the implementation"
      category := .execution
      normativeClauses := [.executableContracts, .proofCompleteness]
      requirement := "The specification of a decision contract reaches no function with a \
        result of `Bool` or `BEq`, outside Lean's own library, that the implementation or the \
        acceptance predicate also reaches."
      rationale := "A kind is a theorem about the present definitions. When the specification \
        and the implementation call one test, a change of that test changes the two together, \
        and a proof that goes through the test on the two sides can stay valid although the \
        meaning changed. A proposition in the place of the test states the meaning a second \
        time, in other terms."
      remedy := "State the condition as a proposition in the specification and let the function \
        decide it: `if P x then … else …` with a `Decidable (P x)` instance, or keep the test \
        in the function with a theorem `test x = true ↔ P x`."
      rewrites := [
        "Replace `def small (n : Nat) : Bool := n < 4` in the specification by `def Small (n : \
          Nat) : Prop := n < 4` with `instance (n : Nat) : Decidable (Small n) := by unfold \
          Small; infer_instance`, and write `decide (Small n)` or `if Small n then … else …` in \
          the function.",
        "Where a function that the two sides share calls the test, change that function: it \
          decides the proposition, and the specification then reaches the proposition and not \
          the test.",
        "For a type with a derived `BEq` that the two sides compare, derive `DecidableEq` and \
          state the specification with `=`. Lean's own `BEq` of a type with `DecidableEq` is \
          not counted.",
        "Use a test of Lean's own library directly, such as `Char.isWhitespace` or `Nat.ble`: \
          the rule does not count a function of that library."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG1009/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG1009/Violation.lean"
        correction := "The correction states the bound as the proposition `Small`, which the \
          function decides, so the specification names no test that the function runs." } }
  | .environment => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "The declared Lean environment must be available", category := .environment
      normativeClauses := [.elaborationEnvironment]
      requirement := "The audit runs in the declared environment: Lake loads the workspace with \
        the pinned toolchain and resolves every dependency."
      rationale := "Every conformance claim is about one exact elaboration environment: toolchain, \
        dependency revisions and source state. A result under an unknown or different environment \
        is not evidence for the declared one."
      remedy := "Repair the workspace so Lake can load it with its exact toolchain and \
        dependencies, then rerun the same command."
      rewrites := [
        "Read the original setup error in the diagnostic detail and fix it: a missing path \
          dependency, an unresolvable Git revision, or a toolchain that does not match \
          `lean-toolchain`.",
        "Provision pinned dependencies (for example `lake exe cache get` for Mathlib) before \
          auditing; provisioning is setup, not verification.",
        "Rerun the audit; a new run produces new, complete evidence."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG2001/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG2001/Violation.lean"
        correction := "The examples are the project's `lakefile.lean`. The correction removes a \
          Lake dependency that cannot be resolved (`require unavailable from \"./missing\"`); the \
          rest of the file is unchanged." } }
  | .configuration => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Configuration must classify the complete Lake surface", category := .configuration
      normativeClauses := [.lakeSurfaces]
      requirement := "`foundation_manifest.json` is valid schema 2 and classifies every root \
        `lean_lib` and `lean_exe` exactly once, each executable alike with any library that \
        contains its root module."
      rationale := "Coverage is only meaningful against a complete, exact classification. Silently \
        ignoring an unknown key or an unclassified target would let modules escape the audit or \
        let a typo change the claim."
      remedy := "Fix the manifest: exactly the four top-level keys, one entry per root `lean_lib` \
        and `lean_exe` (claimed or excluded with a rationale), valid `claim` and `execution` \
        values, and an executable whose root belongs to a library classified with that library: \
        in its surface, or excluded with it."
      rewrites := [
        "Remove or correct unknown keys and invalid values; the diagnostic names them.",
        "Add each root library and executable to `surfaces` or to the matching exclusion array, \
          with a rationale.",
        "An executable whose root module belongs to a library is classified with it: list it in \
          the `executables` of that library's surface, where its root keeps the library's claim \
          and is inspected in the executable's own environment with its import closure. Its root \
          in an excluded library, or in the library of another surface, and an excluded \
          executable whose root is in a claimed library, are manifest conflicts.",
        "Run `lake lint -- --explain-config` to see the manifest, scope, profiles and stages the \
          driver would use, without auditing."]
      examples := {
        language := .json
        compliant := include_str "../../examples/rules/RG2002/Fixed.json"
        noncompliant := include_str "../../examples/rules/RG2002/Violation.json"
        correction := "The examples are `foundation_manifest.json` files for one layout: library \
          `Example` globs its submodules (``globs := #[.andSubmodules `Example]``), among them \
          `Example.Cli`, the root of `lean_exe cli`. Excluding the executable conflicts \
          with the claimed library that contains its root; the correction claims it with that \
          library's surface instead, without changing the library, profile or execution \
          requirement." } }
  | .sourceBuild => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Claimed source must elaborate warning-free", category := .elaboration
      normativeClauses := [.cleanElaboration]
      requirement := "Every claimed module elaborates from source without errors or warnings; \
        Lean's default warnings stay enabled, and disabling a linter never discharges what it \
        checks."
      rationale := "Warnings often mark real defects (unused hypotheses, deprecated semantics, \
        unreachable cases). Treating them as failures keeps the elaborated statements exactly \
        those the author intended, and prevents a local option from changing what conformance \
        means."
      remedy := "Fix the compiler diagnostic at its source. Never disable a Lean default warning; \
        disable a community linter only for one declaration, where its guidance allows, with the \
        reason."
      rewrites := [
        "Read the preserved compiler message, fix the cause and rebuild.",
        "Remove dead bindings or rename intentionally unused ones only when the name was genuinely \
          unused; do not rename a variable that should have been used.",
        "Do not add `set_option linter.… false` for a Lean default warning such as \
          `linter.unusedVariables`: the linter then logs nothing, which `lake build --wfail` \
          cannot see, and no rule reads an option set in source. A declaration-scoped \
          `set_option linter.NAME false in` is only for a community linter, enabled by a \
          dependency or the project, where its guidance allows, and establishes nothing the \
          linter checks.",
        "Move a `#guard_msgs` or `#guard_panic` check out of the claimed modules, into a test or \
          documentation module outside the claimed surface: in a claimed module it hides the \
          messages that `lake build --wfail` reads."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG2003/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG2003/Violation.lean"
        correction := "The correction removes a dead lambda binding while preserving identity's \
          complete natural-number behavior. No warning or linter is disabled." } }
  | .coverage => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Owned coverage must match the exact Lake inventory", category := .coverage
      normativeClauses := [.lakeSurfaces]
      requirement := "Every module of the root package that Lake builds belongs to exactly one \
        library, or to none and is the root of an executable, and no claimed module imports a \
        module of an excluded target."
      rationale := "A conformance claim covers an exact set of modules. A module imported into a \
        claimed library but outside every surface would contribute declarations nobody classified, \
        and an umbrella import alone does not define that set."
      remedy := "Remove the forbidden import, or add the module to the intended claimed library's \
        globs, so every owned module belongs to exactly one classified target."
      rewrites := [
        "Delete imports of modules of excluded targets (for example test or fixture libraries) \
          from claimed code.",
        "Use a glob with the intended meaning, such as ``.andSubmodules `Lib`` in `lakefile.lean` \
          or `[\"Lib\", \"Lib.+\"]` in `lakefile.toml`, so every intended module is in the \
          library.",
        "Classify any new root library or executable in the manifest (RG2002)."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG2004/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG2004/Violation.lean"
        correction := "The manifest excludes the `Fixtures` library. The correction removes the \
          claimed module's unused import of its module `Fixtures.Cases`; the reflexivity statement \
          and its assumptions are unchanged." } }
  | .admission => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Required admission and source evidence must be complete", category := .admission
      normativeClauses := [.cleanElaboration]
      requirement := "Lean's kernel replays each constant of each claimed module from an export of \
        the build (`lake check`); no metaprogram adds unchecked declarations."
      rationale := "Successful elaboration alone is not checked admission: metaprograms and debug \
        options can store declarations the kernel never checked. `lake check` replays the export of \
        the build in a process that loads no `.olean` file of the project."
      remedy := "Remove the construction that bypasses kernel checking, then run `lake check` \
        again."
      rewrites := [
        "Remove uses of `debug.skipKernelTC`, `addDecl` with unchecked values, or other \
          metaprograms that add unchecked declarations; state and prove the theorem normally.",
        "`lake check` decides this rule, as the specification hands it to Lean. Regula's checker \
          does not report it."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG2005/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG2005/Violation.lean"
        correction := "The correction replaces ill-typed unchecked evidence with a checked proof \
          of the same reflexivity statement." } }
  | .communityConfiguration => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Claimed targets must set only allowlisted options"
      category := .configuration
      normativeClauses := [.elaborationEnvironment]
      requirement := "Each claimed target sets `autoImplicit` and `relaxedAutoImplicit` to `false`, \
        sets only options of the closed allowlist, and has no plugin, dynamic library or other \
        Lean argument."
      rationale := "An automatic implicit adds a binder the source does not show, so the \
        elaborated statement can quantify over more than the text a reviewer compares with the \
        intent. A target-wide option can turn a default warning off, so the warning-free build \
        (RG2003) never sees it. The allowlist names no such option. A plugin runs code inside \
        Lean's process. A name that the allowlist does not name is refused, an unknown one too."
      remedy := "Set `autoImplicit` and `relaxedAutoImplicit` to `false` in `leanOptions`, and \
        delete each option outside `Regula.Allowlist.options`, each plugin, dynamic library and \
        other extra Lean argument."
      rewrites := [
        "Add ``⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩`` to `leanOptions` (the same \
          keys under `[leanOptions]` in `lakefile.toml`), then declare each universe and implicit \
          the build reports as unknown.",
        "Delete a target-wide option outside the allowlist, such as ``⟨`warn.sorry, false⟩`` or \
          ``⟨`linter.unusedVariables, false⟩``. The rule reads the name alone, so an option whose \
          value can stop a default warning is refused at every value, the default included.",
        "Replace a target-wide ``⟨`linter.X, false⟩`` with `set_option linter.X false in` on the \
          one declaration the community's guidance allows, with a comment (§6.2): the rule does \
          not read an option that a source file sets.",
        "Delete each plugin, dynamic library and non-option argument, such as `-j2` in \
          `weakLeanArgs`, and put a tool that needs one in an excluded target (RG2002)."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG2006/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG2006/Violation.lean"
        correction := "The examples are the package's `lakefile.lean` (a project adds its \
          `require regula` line). The correction turns automatic implicits off, without changing \
          the library or its source." } }
  | .closedSubset => {
      lifecycle := .active .unreleased
      title := "Claimed modules must register no code that Lean runs"
      category := .configuration
      normativeClauses := [.elaborationEnvironment]
      requirement := "A claimed module has entries only of the environment extensions of the closed \
        allowlist, so its build records no macro, syntax, elaborator, initializer, `meta` declaration \
        or attribute of its own."
      rationale := "Meta-code in a project can change what Lean elaborates and what it reports, \
        which made passes false. Refusing what lies outside a closed set stops that where \
        detecting it never converges. The rule reads the names that Lean records in the build, and \
        refuses a name it does not know, so a new kind of registration is refused and not missed. A \
        command that runs code and an attribute of local scope leave no record, so it cannot see \
        them."
      remedy := "Remove the macro, syntax, elaborator, initializer, `meta` declaration or attribute \
        from the claimed module, or move it to a tool module, a module of an excluded target, \
        which no claimed module may import (RG2004)."
      rewrites := [
        "Write the term the macro or notation expands to, or a definition that states it.",
        "Move a tool that needs metaprogramming to a library that `foundation_manifest.json` \
          excludes. A claimed module cannot import it, so run it apart from claimed code.",
        "Replace a project attribute that records a fact with a declaration of a type that states \
          it, as `Regula.RegisteredDecision` does for a decision."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG2007/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG2007/Violation.lean"
        correction := "The correction writes `0`, the term the macro expands to, so the module \
          registers no syntax and no macro. The statement is unchanged." } }
  | .executionUnresolved => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Execution closure must have no unresolved paths", category := .execution
      normativeClauses := [.computationMechanisms]
      requirement := "Every name in an executable root's execution closure resolves, and no \
        runtime replacement runs itself again through a cycle of replacements."
      rationale := "An execution account that silently skipped an unresolved path would overstate \
        what the compiled program is known to run."
      remedy := "Make the missing compiled code available, or break the cycle of runtime \
        replacements, then build again and rerun `lake lint`."
      rewrites := [
        "Remove metaprogramming commands from modules whose `implemented_by` history must be \
          authenticated, or move them elsewhere.",
        "Ensure every dependency's compiled code is available in the build.",
        "Break cycles consisting only of replacement edges."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG3001/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG3001/Violation.lean"
        correction := "The correction removes a no-effect `run_cmd` metaprogramming command that \
          prevents history authentication; the reference, replacement and correspondence theorem \
          are unchanged." } }
  | .executionBoundary => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Checked execution requires admitted correspondence", category := .execution
      normativeClauses := [.computationMechanisms]
      requirement := "Under `\"execution\": \"checked\"`, every reachable replacement or recursion \
        helper outside the toolchain has an admitted correspondence, and no reachable code outside \
        it is unbindable, such as `extern`."
      rationale := "`@[implemented_by g] def f` makes the kernel reason about `f` while compiled \
        code runs `g`. Without a proof relating them, theorems about `f` say nothing about the \
        program's behavior."
      remedy := "Prove the replacement equal to its reference on the complete domain, or remove \
        the trusted boundary, or claim `report` execution instead and keep the boundary reported."
      rewrites := [
        "State and prove the closed theorem `@f = @g`, with the same distinct universe parameters \
          on both sides, by `funext` for the full domain.",
        "For a recursive definition `f`, state its recursion equation: \
          `theorem f_rec : type_of% @f.eq_def := @f.eq_def`.",
        "Replace `implemented_by` with a proof-backed `@[csimp]` equality where it fits.",
        "If an external boundary is intended (an `extern` implementation, or unsafe or partial \
          code in an unclaimed dependency), claim `report` execution, where it is reported as \
          trusted and not failed. An owned `unsafe` or `partial` declaration on a claimed surface \
          still fails RG1006 in either mode."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG3002/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG3002/Violation.lean"
        correction := "The correction adds the missing equality between the reference and its \
          replacement on the full natural-number domain, keeping the checked execution claim and \
          both implementations. In both, `spell` runs `Nat.repr`, whose replacement is the Lean \
          toolchain's own: it passes as the toolchain's trusted base, reported once." } }
  | .fenceStructure => {
      lifecycle := .retired (.release ⟨4, 34, 0⟩) .unreleased none
      title := "Documentation fences must have a valid classification", category := .documentation
      normativeClauses := [.documentationChecks]
      requirement := "Each `lean-fail` or `lean-trusted-compiler` marker sits immediately before \
        its `lean` fence, every fence is closed, and Lean code is shown only as a `lean` fence in \
        the first column."
      rationale := "A misspelled or misplaced marker turns a negative example into a positive \
        one, or hides a fence from the project's own check of its examples. A Lean block in a \
        quotation, in a list item, behind a different spelling of the language or in raw HTML is \
        rendered, and a check that reads fences from the first column misses it. Plain structure \
        keeps every documented Lean claim in a fence that can be checked."
      remedy := "Put each marker immediately before the `lean` fence it classifies, with a valid \
        pattern, and close every fence. Write each Lean example as a `lean` fence that opens and \
        closes in the first column, outside quotations, list items and other fences."
      rewrites := [
        "Move the marker so no blank line or other content separates it from its fence; delete \
          an orphan marker, or add the fence it was meant to classify.",
        "Use the exact marker spelling; write non-Lean sketches with another fence language.",
        "Move a Lean fence out of a quotation, a list item or another fence, remove the \
          indentation before its opening run and its closing run, and write the language as \
          `lean`, not `Lean`, `lean4` or `{.lean}`.",
        "Show a raw HTML code tag with a character reference (`&lt;pre>`) or name it in prose."]
      examples := {
        language := .markdown
        compliant := include_str "../../examples/rules/RG4001/Fixed.md"
        noncompliant := include_str "../../examples/rules/RG4001/Violation.md"
        correction :=
            "The correction removes the orphan marker; the positive reflexivity fence is \
              unchanged." } }
  | .positiveExample => {
      lifecycle := .retired (.release ⟨4, 34, 0⟩) .unreleased none
      title := "Positive examples require warning-free elaboration and admission", category :=
          .documentation
      normativeClauses := [.documentationChecks]
      requirement := "An unmarked `lean` fence in the checked docs elaborates verbatim and \
        warning-free and passes the declaration and axiom rules."
      rationale := "Readers copy documented examples and trust them. A positive example that does \
        not elaborate, or that proves its claim with an axiom, teaches a false claim."
      remedy := "Make the example correct as printed: fix its errors or warnings, and make its \
        declarations satisfy the same rules as project code."
      rewrites := [
        "Fix what makes the example fail, for example prove the statement instead of declaring \
          an axiom.",
        "If the example is meant to fail, mark it with an exact `lean-fail` marker instead \
          (RG4003).",
        "Import what the example needs inside the fence, so that it elaborates as printed."]
      examples := {
        language := .markdown
        compliant := include_str "../../examples/rules/RG4002/Fixed.md"
        noncompliant := include_str "../../examples/rules/RG4002/Violation.md"
        correction := "The correction proves the same reflexivity claim in the positive fence; the \
          violation states it as an `axiom`, which RG1001 refuses in claimed code." } }
  | .negativeExample => {
      lifecycle := .retired (.release ⟨4, 34, 0⟩) .unreleased none
      title := "Negative examples require completed intended rejection", category := .documentation
      normativeClauses := [.documentationChecks]
      requirement := "A `lean-fail` fence fails to elaborate with one error message that matches \
        its whole pattern."
      rationale := "A negative example documents what Lean rejects. If it stops failing, or fails \
        for another reason, the documentation claims a rejection that no longer holds."
      remedy := "Make the example fail for exactly the documented reason, adjust the pattern to \
        match one real error message, or remove the marker if the example is valid."
      rewrites := [
        "If the example is actually valid, remove the `lean-fail` marker so that it is a \
          positive example.",
        "If it should fail, edit the example so it fails for the documented reason, and write a \
          pattern that matches that one error message.",
        "Keep patterns to literal fragments joined by `.*` and alternatives separated by `|`."]
      examples := {
        language := .markdown
        compliant := include_str "../../examples/rules/RG4003/Fixed.md"
        noncompliant := include_str "../../examples/rules/RG4003/Violation.md"
        correction := "The correction labels an already valid reflexivity proof as a positive \
          example instead of inventing a compiler failure." } }
  | .trustedExample => {
      lifecycle := .retired (.release ⟨4, 34, 0⟩) .unreleased none
      title := "Teaching examples require authenticated compiler classification", category :=
          .documentation
      normativeClauses := [.documentationChecks]
      requirement := "A `lean-trusted-compiler` fence elaborates warning-free and contains a \
        compiler-trusting declaration."
      rationale := "Conforming claims reject compiler-trusting proofs (RG1004). A teaching fence \
        is how the documentation shows one: it is marked and never counts as a conforming \
        positive. A marker on an ordinary example would present it as compiler-trusting."
      remedy := "Use the marker only for an example that demonstrates `native_decide`, \
        `decide +native` or `bv_decide` (or another authenticated compiler-trusting mechanism); \
        otherwise remove it."
      rewrites := [
        "Remove the marker from an example that is an ordinary kernel proof; it is then a \
          positive example.",
        "For a genuine teaching example, keep the native proof and import only the module that \
          provides its tactic (for example `import Init`, or `import Std.Tactic.BVDecide` for \
          `bv_decide`)."]
      examples := {
        language := .markdown
        compliant := include_str "../../examples/rules/RG4004/Fixed.md"
        noncompliant := include_str "../../examples/rules/RG4004/Violation.md"
        correction := "The correction labels the same kernel proof as a positive example rather \
          than as native teaching." } }
  | .moduleDocumentation => {
      lifecycle := .retired (.release ⟨4, 34, 0⟩) .unreleased none
      title := "Claimed modules need a leading module docstring and no repeated import"
      category := .documentation
      normativeClauses := [.moduleDocumentation, .importDiscipline]
      requirement := "Every claimed module has a module docstring (`/-! … -/`) as its first \
        command \
        after the imports, and its header repeats no import with the same modifiers."
      rationale := "Module documentation tells a reader which declarations carry the module's \
        claims and under which assumptions, so the claims can be reviewed without reading every \
        proof. The Lean community puts it first, where readers and tools look. A repeated import \
        adds nothing and obscures which dependencies a module declares."
      remedy := "Add a module docstring that identifies the module's material declarations and \
        assumptions, directly after the imports and before any `public section`, and delete \
        repeated imports."
      rewrites := [
        "Add `/-! # Title … -/` as the first command after the imports.",
        "In a `module` file, move the module docstring above `@[expose] public section` or \
          `public section`.",
        "Delete the second copy of a repeated import; `public import A` and `import all A` are \
          different imports.",
        "Follow the template in standard §5.3: a `#` title and summary, main declarations with \
          their results and hypotheses, assumptions and dependencies, design notes. Keep only \
          sections that help."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG5001/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG5001/Violation.lean"
        correction :=
            "The correction adds module documentation to the unchanged reflexivity evidence." } }
  | .materialDocumentation => {
      lifecycle := .retired (.release ⟨4, 34, 0⟩) .unreleased none
      title := "Public material declarations require docstrings", category :=
          .documentation
      normativeClauses := [.inlineDocumentation]
      requirement := "Every public declaration that states a material claim has a docstring stating \
        its purpose, hypotheses, result and boundary. Review selects these declarations."
      rationale := "A material claim must be readable without reconstructing it from the proof: \
        the docstring states what the declaration establishes and under which assumptions, and \
        binds the written intent to that exact declaration."
      remedy := "Add a docstring stating the declaration's formal purpose, domain and hypotheses, \
        result and boundary, with a labelled `# Intent` section (RG5003)."
      rewrites := [
        "Add `/-- … -/` immediately before the declaration, stating purpose, domain and \
          hypotheses, result and boundary (standard §5.1).",
        "Include a `# Intent` section with the requirement the claim must meet (standard §5.2); a \
          missing Intent section is RG5003."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG5002/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG5002/Violation.lean"
        correction := "The correction adds the theorem's docstring, including its `# Intent` \
          section; proposition and proof are unchanged." } }
  | .materialIntent => {
      lifecycle := .retired (.release ⟨4, 34, 0⟩) .unreleased none
      title := "Public material declarations require an Intent section", category :=
          .documentation
      normativeClauses := [.faithfulExplanation]
      requirement := "The docstring of every public declaration that states a material claim has \
        a nonempty `# Intent` section stating the requirement the claim must meet. Review selects \
        these declarations."
      rationale := "The explanation states what the formal statement says; the intent states what \
        it is required to say. Comparing the two, and both with the declaration, exposes \
        statements that are faithfully explained but wrong (standard §5.2)."
      remedy := "Add a heading whose text is exactly `Intent` to the docstring, followed by the \
        requirement the claim must meet, stated from the source mathematics or specification."
      rewrites := [
        "Add `# Intent` with the requirement in your own words, derived from the source \
          mathematics or program specification, not from the Lean statement.",
        "Prefer a level-one heading; a top-level Verso docstring header must be `#`."]
      examples := {
        language := .lean
        compliant := include_str "../../examples/rules/RG5003/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG5003/Violation.lean"
        correction := "The correction adds a nonempty `# Intent` section, structured with a `## \
          Requirement` subsection, to the theorem's existing docstring; the explanation, \
          proposition and proof are unchanged." } }

/-- Every rule names at least one compliant rewrite, checked exhaustively over the closed
registry by kernel evaluation (list shape only, so no string literal is reduced). Field
presence is the structure type itself; content and size budgets are
`RuleDescriptor.wellFormed`. -/
theorem descriptor_rewrites_nonempty : ∀ id, (descriptor id).rewrites ≠ [] := by
  intro id; cases id <;> decide

/-- When `installed` is a release, no lifecycle position of any rule is `.unreleased`: neither an
introduction nor a retirement. The release pull request (the Release workflow's `open` step)
stamps those on `lifecycle :=` lines on `main`, and the release commit CI creates on the head of
`main` changes only `installed`; if any position, however written, is still unreleased there, the
release commit fails to prove this, does not build, and CI publishes nothing. On `main` and every
pull request the build is unreleased and the hypothesis is false. -/
theorem release_attributes_rules (id : RuleId) :
    installed ≠ .unreleased → .unreleased ∉ (descriptor id).lifecycle.builds := by
  cases id <;> decide

/-- Every release a rule's lifecycle names is in `versions`. -/
theorem lifecycle_listed (id : RuleId) :
    ∀ b ∈ (descriptor id).lifecycle.builds, b.listedIn versions := by
  cases id <;> decide

/-- No rule is introduced by a patch release: the release that introduces a rule has patch version
`0` (`Build.startsLine`), which, for a release that follows its predecessor, holds exactly when it
starts a new line (`follows_startsLine_iff`). A release that adds a rule is therefore a minor or
major release; a patch release whose release pull request stamps a new rule does not build, so it
is not published. -/
theorem introduced_startsLine (id : RuleId) :
    (descriptor id).lifecycle.introduced.startsLine = true := by
  cases id <;> decide

/-- What checks a rule. -/
inductive RuleCheck where
  /-- `lake lint`: Regula's checker, over the finished build. -/
  | lakeLint
  /-- `lake build --wfail`, the Lean tool that the specification hands RG2003 to. -/
  | lakeBuild
  /-- `lake check`, the Lean tool that the specification hands RG2005 to. -/
  | lakeCheck
  /-- No check: the rule is retired to written guidance. -/
  | retired
  deriving Repr, BEq, DecidableEq

/-- The name of each check: its command, or `no check`. -/
def RuleCheck.label : RuleCheck → String
  | .lakeLint => "lake lint"
  | .lakeBuild => "lake build --wfail"
  | .lakeCheck => "lake check"
  | .retired => "no check"

/-- What checks rule `id` now: no check for a rule whose lifecycle in the registry is retired, which
is read from the lifecycle, so no table can disagree with it, the Lean tool for RG2003 and RG2005,
and `lake lint` for each other rule. `RegulaSpecification.Link.checkOf_fate` proves that this is
the specification's `fate` of every rule. -/
def checkOf (id : RuleId) : RuleCheck :=
  if (descriptor id).lifecycle.isRetired then .retired else
    match id with
    | .sourceBuild => .lakeBuild
    | .admission => .lakeCheck
    | _ => .lakeLint

end Regula
