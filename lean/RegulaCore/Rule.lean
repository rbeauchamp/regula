module

public import RegulaCore.RuleId
public import RegulaCore.Edition
public import RegulaCore.Standard
public import RegulaPolicy.Foundation
public import RegulaPolicy.Intent
public import RegulaPolicy.GeneratedFamily

/-! # Rule registry

Shared metadata of every rule. See RuleId for con-leche attribution.

The registry is the one source of each rule's agent-facing guidance: its one-line
`requirement`, short `rationale`, imperative `remedy`, common compliant `rewrites` and checked
`examples` pair are required `RuleDescriptor` fields, so a rule without them does not compile.
Findings (`RegulaCore.Feedback`), the `regula` command and agent briefing
(`RegulaCore.Guidance`), the registry and result exports and the website are generated from
them.

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

/-- How an audit collected its evidence (editor snapshot, incremental or fresh project, fresh
file, documentation example or serialized graph): the policy's `RegulaPolicy.EvidenceMode`. -/
abbrev EvidenceMode := RegulaPolicy.EvidenceMode
/-- The stable text of an evidence mode, as `RegulaPolicy.EvidenceMode.spelling` gives it. -/
abbrev EvidenceMode.spelling (mode : EvidenceMode) : String :=
    RegulaPolicy.EvidenceMode.spelling mode

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

/-- The kind of property a rule checks; the rule index groups and filters rules by it. -/
inductive RuleCategory where
  /-- The logical foundation of declarations: axioms, proof holes, compiler trust and the
  surface profile (RG1001–RG1005). -/
  | foundation
  /-- The form of a declaration itself, such as `unsafe` or `partial` (RG1006). -/
  | declaration
  /-- Executable contracts, decision contracts and the execution closure of executable roots
  (RG1007, RG1008, RG3001, RG3002). -/
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
  deriving Repr, BEq, DecidableEq

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
  /-- One declaration registered with `@[regula_material]`. -/
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
  /-- `ExecutableContract` registrations and `@[regula_decision]` registrations. -/
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
  | .escapeHatch | .executableContract | .decisionContract => .declaration
  | .environment | .configuration | .sourceBuild | .coverage | .admission
  | .communityConfiguration => .project
  | .executionUnresolved | .executionBoundary => .executionRoot
  | .fenceStructure | .positiveExample | .negativeExample | .trustedExample => .documentationFence
  | .moduleDocumentation => .module
  | .materialDocumentation | .materialIntent => .materialDeclaration

/-- The evidence each rule's decision reads; `RuleDescriptor.evidenceKind` defaults to it. -/
def evidenceFor : RuleId → EvidenceKind
  | .projectAxiom | .proofHole | .unknownAxiom | .profileExceeded => .kernelAxioms
  | .compilerTrusting | .escapeHatch => .generatedRole
  | .executableContract | .decisionContract => .contractEvidence
  | .environment => .environment
  | .configuration | .communityConfiguration => .configuration
  | .sourceBuild => .compilation
  | .coverage => .inventory
  | .admission => .admission
  | .executionUnresolved | .executionBoundary => .executionClosure
  | .fenceStructure => .fenceGrammar
  | .positiveExample | .negativeExample | .trustedExample => .checkedExample
  | .moduleDocumentation | .materialDocumentation | .materialIntent => .metadataPresence

/-- The first line of a diagnostic whose rule ID is written `rule`: what is wrong and where. -/
def messageShape (rule impact mode claim location subject detail : String) : String :=
  rule ++ " [" ++ impact ++ "; " ++ mode ++ "; claim=" ++ claim ++ "; " ++ location ++ "]: " ++
    subject ++ ": " ++ detail

/-- The first line of every rendered diagnostic of `id`: what is wrong and where.
`RegulaCore.Feedback` adds the rule's remedy and guidance below it. A detail can itself span
several lines. -/
def messageLine (id : RuleId) (impact mode claim location subject detail : String) : String :=
  messageShape id.spelling impact mode claim location subject detail

/-- The published message form: `messageLine` applied to placeholder names, so the registry
and site show the same definition the checker renders. -/
def messageForm (id : RuleId) : String :=
  messageLine id "{impact}" "{mode}" "{claim}" "{location}" "{subject}" "{detail}"

/-- The message form shared by every rule, with its ID as the placeholder `{rule}`. -/
def sharedMessageForm : String :=
  messageShape "{rule}" "{impact}" "{mode}" "{claim}" "{location}" "{subject}" "{detail}"

/-- Source language of a rule's example files. -/
inductive ExampleLanguage where
  /-- Lean source, including a `lakefile.lean`. -/
  | lean
  /-- JSON, such as a `foundation_manifest.json` or a qualification runner request. -/
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

/-- Who can apply a rule's checked example files as shown. -/
inductive ExampleAudience where
  /-- The compliant file is Lean, configuration or Markdown an adopting project writes as shown. -/
  | adopter
  /-- The files are qualification inputs, such as a runner request or a stand-in dependency of
  the audited file; `files` says what they are. Agent guidance states `correction` instead of
  showing either file. -/
  | qualification (files : String)
  deriving Repr, BEq, DecidableEq

/-- A rule's checked example pair: the exact bytes of `examples/rules/<ID>/Fixed.<ext>`
(compliant) and `Violation.<ext>` (noncompliant), embedded with `include_str`. These are the
corpus sources that the rule-example qualification runs (docs/guides/architecture.md): the
fixed phase passes a completed positive check, and the violating phase produces this rule's
findings. `correction` states what the correction changes and preserves; for qualification
inputs it is the adopter-facing form of the fix. -/
structure ExamplePair where
  /-- The language of both files, which fixes their extension. -/
  language : ExampleLanguage
  /-- Whether an adopter can apply the files as shown, or they are qualification inputs. -/
  audience : ExampleAudience
  /-- The bytes of `Fixed.<ext>`, the compliant file. -/
  compliant : String
  /-- The bytes of `Violation.<ext>`, the noncompliant file. -/
  noncompliant : String
  /-- What the correction from the noncompliant to the compliant file changes and preserves. -/
  correction : String

/-- The compliant file an agent can apply as shown; none for qualification inputs. -/
def ExamplePair.adopterExample (p : ExamplePair) : Option String :=
  match p.audience with
  | .adopter => some p.compliant
  | .qualification _ => none

/-- The caption beside both files where they are shown: what qualification files are, then
the correction. -/
def ExamplePair.caption (p : ExamplePair) : String :=
  match p.audience with
  | .adopter => p.correction
  | .qualification files => files ++ " " ++ p.correction

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
one. Every diagnostic, the `regula` command, the agent guide, the registry export and the
website are generated from these fields. -/
structure RuleDescriptor (id : RuleId) where
  /-- The rule's short name, stated as the property it demands. -/
  title : String
  /-- The kind of property the rule checks. -/
  category : RuleCategory
  /-- The sections of the standard the rule enforces. -/
  normativeClauses : List Clause
  /-- The subreason every finding of the rule carries, such as `project-axiom` for RG1001. -/
  applicability : String
  /-- The evidence modes whose runs report the rule's findings. -/
  evidenceModes : List EvidenceMode
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
/-- The message form is derived from the index, never an independent field. -/
def messageTemplate {id : RuleId} (_ : RuleDescriptor id) : String := messageForm id
end RuleDescriptor

/-- Size budgets, in UTF-8 bytes, that keep inline feedback and the agent guide compact. -/
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
line break, every example line fits the community's 100-character limit, the two examples differ,
and qualification inputs say what they are. The registry
checks this for every rule when `RegulaCore.Guidance` is built (`#guard` over the complete
`RuleId.all`): evaluation, because kernel reduction of these long string literals costs seconds
per field. -/
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
  0 < d.examples.correction.utf8ByteSize &&
  (match d.examples.audience with
    | .adopter => true
    | .qualification files => 0 < files.utf8ByteSize)

/-- The modes that audit declarations outside the editor: incremental and fresh project,
fresh file and documentation example. A rule that also reports in the editor adds
`.editorSnapshot` to them. -/
def declarationModes : List EvidenceMode :=
  [.incrementalProject, .freshProject, .freshFile, .documentationExample]

/-- The modes of the completed-module documentation rules: the editor and whole-project audits.
Single-file and documentation-example audits have no documentation-presence stage. -/
def projectModes : List EvidenceMode := [.editorSnapshot, .incrementalProject, .freshProject]

/-- Total bridge from the executed policy decision to the single rule registry. -/
def ruleForFailure : RegulaPolicy.DeclarationFailure → RuleId
  | .projectAxiom => .projectAxiom | .proofHole => .proofHole
  | .unknownAxiom => .unknownAxiom | .escapeHatch => .escapeHatch
  | .compilerTrusting => .compilerTrusting | .executableContract => .executableContract
  | .profileExceeded => .profileExceeded | .decisionContract => .decisionContract
  | .invalidInventory => .coverage

/-- Distinct policy failures reach distinct rules, so the rule preserves the failure category. -/
theorem ruleForFailure_injective : Function.Injective ruleForFailure := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

/-- Total bridge from the executed material-documentation classification
(`RegulaPolicy.materialDocumentationFailure`) to the single rule registry. -/
def ruleForMaterialDocumentation : RegulaPolicy.MaterialDocumentationFailure → RuleId
  | .missingDocstring => .materialDocumentation
  | .missingIntent => .materialIntent

/-- The two material-documentation failures reach distinct rules. -/
theorem ruleForMaterialDocumentation_injective :
    Function.Injective ruleForMaterialDocumentation := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

/-- Finding detail for each material-documentation failure, prefixed by its rule's applicability. -/
def materialDocumentationDetail : RegulaPolicy.MaterialDocumentationFailure → String
  | .missingDocstring =>
      "material-documentation: document the claim, assumptions and evidence at this declaration"
  | .missingIntent => "material-intent: add a nonempty `# Intent` section stating the requirement \
    this claim must meet"

/-- Total metadata for the rule vocabulary; every registered rule is enforced by the checker.
Example bytes are embedded from `examples/rules/<ID>/`; the `RegulaCore` library `needs` that
directory as a Lake input, so editing an example rebuilds this module. -/
def descriptor : (id : RuleId) → RuleDescriptor id
  | .projectAxiom => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Project logical axioms are forbidden", category := .foundation
      normativeClauses := [.proofCompleteness]
      applicability := "project-axiom"
      evidenceModes := .editorSnapshot :: declarationModes
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
        audience := .adopter
        compliant := include_str "../../examples/rules/RG1001/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG1001/Violation.lean"
        correction := "The correction proves the same `∀ n : Nat, n = n` by `rfl` instead of \
          assuming it, under the unchanged Kernel-only claim." } }
  | .proofHole => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Proof holes are forbidden", category := .foundation
      normativeClauses := [.proofCompleteness]
      applicability := "hole"
      evidenceModes := .editorSnapshot :: declarationModes
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
        audience := .adopter
        compliant := include_str "../../examples/rules/RG1002/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG1002/Violation.lean"
        correction := "The correction fills the same reflexivity proof with `rfl`. The checked \
          violation records Lean's original `sorry` warning as well; the corrected file passes the \
          ordinary warning-rejecting gate." } }
  | .unknownAxiom => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Unknown transitive axioms are forbidden", category := .foundation
      normativeClauses := [.proofCompleteness]
      applicability := "unknown-axiom"
      evidenceModes := .editorSnapshot :: declarationModes
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
        audience := .qualification "The examples are the imported dependency."
        compliant := include_str "../../examples/rules/RG1003/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG1003/Violation.lean"
        correction := "The dependency proves the same reflexivity statement instead of declaring \
          it as an axiom, and the file that imports it is unchanged." } }
  | .compilerTrusting => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Compiler-trusting proofs require separate classification", category := .foundation
      normativeClauses := [.proofCompleteness]
      applicability := "compiler-trusting"
      evidenceModes := .editorSnapshot :: declarationModes
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
        audience := .adopter
        compliant := include_str "../../examples/rules/RG1004/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG1004/Violation.lean"
        correction := "The correction proves the same three facts by kernel-checked proofs: `rfl`, \
          `decide` by kernel reduction, and the library lemma `BitVec.mul_comm`. The violation \
          reports each generated axiom and its parent theorem." } }
  | .profileExceeded => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Transitive axioms must fit the selected profile", category := .foundation
      normativeClauses := [.proofCompleteness]
      applicability := "label-exceeds-claim"
      evidenceModes := [.editorSnapshot, .incrementalProject, .freshProject, .freshFile]
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
        "`lake lint` groups a declaration Lean generated under the one it came from if it is a " ++
          "; ".intercalate (GeneratedFamily.all.map (·.text)) ++ ". Other declarations keep their \
          own location. Fix the one reported or a definition it uses that adds the axiom."]
      examples := {
        language := .lean
        audience := .adopter
        compliant := include_str "../../examples/rules/RG1005/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG1005/Violation.lean"
        correction := "The correction proves the same universally quantified reflexivity with an \
          empty axiom set, under the unchanged Kernel-only claim, instead of routing through \
          `propext`." } }
  | .escapeHatch => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Unsafe and partial declarations require exact helper authentication", category :=
          .declaration
      normativeClauses := [.declarationInventory]
      applicability := "escape-hatch"
      evidenceModes := .editorSnapshot :: declarationModes
      requirement := "Claimed modules declare nothing `unsafe` or `partial`, authored or \
        generated, except a generated recursion or constructor-index helper passing its exact \
        §7.4 authentication."
      rationale := "A positive proof surface must consist of kernel-checked definitions. Unsafe \
        and partial code can be executed, but it cannot serve as logical evidence, and reasoning \
        about it silently depends on its runtime behavior."
      remedy := "Write a safe, terminating definition (structural recursion or `termination_by`), \
        or move the unsafe/partial code out of the claimed surface."
      rewrites := [
        "Remove an unnecessary `unsafe` marker.",
        "Replace `partial def` by a definition with structural recursion or a `termination_by` \
          measure and `decreasing_by` proof; the finding names the `partial def` itself. A \
          finding naming the `._unsafe_rec` helper of a safe definition means the checker did not \
          regenerate its base or check its recursion equation (standard §7.4 lists the \
          unsupported forms, such as a `wf_preprocess` rule registered outside the Lean \
          toolchain); restate its recursion without that form.",
        "Deriving `BEq`, `Hashable`, `Repr` or `Ord` on a nested or mutual inductive (`Ord` on \
          any recursive one) generates a `partial def`, reported under its generated name (such \
          as `instBEqT.beq`); write that instance by structural recursion instead.",
        "If the computation must stay unsafe or partial, move it to a separate, unclaimed \
          dependency package; a claimed module cannot import an excluded module of its own package \
          (RG2004). Where a claimed executable reaches it, it is reported as a trusted \
          `unsafe-computation` or `partial-computation` boundary, which fails under checked \
          execution (RG3002)."]
      examples := {
        language := .lean
        audience := .adopter
        compliant := include_str "../../examples/rules/RG1006/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG1006/Violation.lean"
        correction := "The correction keeps identity's domain and body and removes the unnecessary \
          `unsafe` marker." } }
  | .executableContract => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Executable contracts require supported closed evidence", category := .execution
      normativeClauses := [.enforcingBuildLinter, .proofCompleteness]
      applicability := "executable-contract"
      evidenceModes := .editorSnapshot :: declarationModes
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
          recorded.",
        "For a checker, state the direction with a kind: `ExecutableContract check (Decides (· = \
          true) Spec)`, or `DecidesSoundly` or `DecidesCompletely` for a one-way guarantee. \
          Decide several arguments through `fun g => Decides accepts Spec (Function.uncurry g)`, \
          and state `Spec` without `check`."]
      examples := {
        language := .lean
        audience := .adopter
        compliant := include_str "../../examples/rules/RG1007/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG1007/Violation.lean"
        correction := "The correction moves the complete natural-number domain inside the identity \
          contract's predicate, retaining the same pointwise equality." } }
  | .decisionContract => {
      lifecycle := .active .unreleased
      title := "Registered decision functions require a decision contract", category := .execution
      normativeClauses := [.enforcingBuildLinter, .proofCompleteness]
      applicability := "decision-contract"
      evidenceModes := declarationModes
      requirement := "Each `@[regula_decision]` function has a decision contract in its \
        inventory (`DecidesSoundly`, `DecidesCompletely` or `Decides`) or a `Decidable` result \
        type."
      rationale := "A checker with no stated direction can refuse every input or accept every \
        input, and an unstated one-way guarantee cannot be told from an omission. The tag makes \
        the contract a requirement of the function itself, so deleting the contract while the \
        function stays tagged fails the gate instead of removing the requirement with it."
      remedy := "Register `theorem c : ExecutableContract f (Decides accepts Spec)` in the \
        function's library, with `DecidesSoundly` or `DecidesCompletely` for a one-way guarantee, \
        or return `Decidable (Spec x)`."
      rewrites := [
        "Prove both directions and a witness of each outcome: `ExecutableContract f (Decides (· = \
          true) Spec)`, from an existing equivalence by `Decides.of_iff`.",
        "State a deliberate one-way guarantee with `DecidesSoundly` (may refuse inputs that \
          satisfy `Spec`) or `DecidesCompletely` (may accept inputs that do not).",
        "Decide several arguments on their product: `ExecutableContract f (fun g => Decides \
          accepts Spec (Function.uncurry g))`.",
        "Return the proof with the verdict: `def f (x : α) : Decidable (Spec x)`. Each result \
          then carries a proof of `Spec x` or of its negation, and no contract is needed."]
      examples := {
        language := .lean
        audience := .adopter
        compliant := include_str "../../examples/rules/RG1008/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG1008/Violation.lean"
        correction := "The correction registers the two-way contract of the unchanged zero \
          test: it accepts exactly zero, with zero as the accepted input and one as the refused \
          input." } }
  | .environment => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "The declared Lean environment must be available", category := .environment
      normativeClauses := [.elaborationEnvironment]
      applicability := "environment"
      evidenceModes := [.incrementalProject, .freshProject, .freshFile]
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
        language := .json
        audience :=
            .qualification
                "The examples are the qualification runner's requests for the same `Example.lean`."
        compliant := include_str "../../examples/rules/RG2001/Fixed.json"
        noncompliant := include_str "../../examples/rules/RG2001/Violation.json"
        correction := "The correction removes a Lake dependency that cannot be resolved (the \
          violating workspace adds `require unavailable from \"./missing\"`); the Lean source is \
          unchanged." } }
  | .configuration => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Configuration must classify the complete Lake surface", category := .configuration
      normativeClauses := [.lakeSurfaces]
      applicability := "configuration"
      evidenceModes := [.editorSnapshot, .incrementalProject, .freshProject, .freshFile]
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
        audience := .adopter
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
      applicability := "source-build"
      evidenceModes := [.incrementalProject, .freshProject, .freshFile]
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
          `linter.unusedVariables`. A declaration-scoped `set_option linter.NAME false in` or \
          `@[nolint NAME]` is only for a community linter, enabled by a dependency or the project, \
          where its guidance allows, and establishes nothing the linter checks."]
      examples := {
        language := .lean
        audience := .adopter
        compliant := include_str "../../examples/rules/RG2003/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG2003/Violation.lean"
        correction := "The correction removes a dead lambda binding while preserving identity's \
          complete natural-number behavior. No warning or linter is disabled." } }
  | .coverage => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Owned coverage must match the exact Lake inventory", category := .coverage
      normativeClauses := [.lakeSurfaces]
      applicability := "coverage"
      evidenceModes := [.incrementalProject, .freshProject, .freshFile]
      requirement := "Every owned module belongs to exactly one manifested library, and no claimed \
        module imports an excluded or checker-probe module."
      rationale := "A conformance claim covers an exact set of modules. A module imported into a \
        claimed library but outside every surface would contribute declarations nobody classified, \
        and an umbrella import alone does not define that set."
      remedy := "Remove the forbidden import, or add the module to the intended claimed library's \
        globs, so every owned module belongs to exactly one classified target."
      rewrites := [
        "Delete imports of excluded modules (for example checker or fixture modules) from claimed \
          code.",
        "Use a glob with the intended meaning, such as ``.andSubmodules `Lib`` in `lakefile.lean` \
          or `[\"Lib\", \"Lib.+\"]` in `lakefile.toml`, so every intended module is in the \
          library.",
        "Classify any new root library or executable in the manifest (RG2002)."]
      examples := {
        language := .lean
        audience := .adopter
        compliant := include_str "../../examples/rules/RG2004/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG2004/Violation.lean"
        correction := "The correction removes an unused forbidden reporter import; the reflexivity \
          statement and its assumptions are unchanged." } }
  | .admission => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Required admission and source evidence must be complete", category := .admission
      normativeClauses := [.cleanElaboration]
      applicability := "admission"
      evidenceModes := .editorSnapshot :: declarationModes
      requirement := "Owned declarations pass kernel replay from the exact frozen sources; no \
        metaprogram adds unchecked declarations."
      rationale := "Successful elaboration alone is not checked admission: metaprograms and debug \
        options can store declarations the kernel never checked. An accepted result must rest on \
        kernel-checked evidence for the exact frozen sources."
      remedy := "Remove the construction that bypasses kernel checking (or the source change \
        during the run), then run the project command that collects the missing evidence."
      rewrites := [
        "Remove uses of `debug.skipKernelTC`, `addDecl` with unchecked values, or other \
          metaprograms that add unchecked declarations; state and prove the theorem normally.",
        "Do not edit sources while an audit runs; rerun it.",
        "For an editor pending result, run `lake lint` (or `lake lint -- --fresh`).",
        "Rename an owned declaration that shares its name with another module's constant unless \
          both are theorems of the same statement, universe parameters and mutual block, such as \
          an equation lemma Lean realizes in each module that needs it; admission checks each \
          owned copy that is not identical to the replayed or trusted one."]
      examples := {
        language := .lean
        audience := .adopter
        compliant := include_str "../../examples/rules/RG2005/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG2005/Violation.lean"
        correction := "The correction replaces ill-typed unchecked evidence with a checked proof \
          of the same reflexivity statement." } }
  | .communityConfiguration => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Claimed targets must build with the community configuration"
      category := .configuration
      normativeClauses := [.elaborationEnvironment, .communityConventions, .linterDiscipline]
      applicability := "community-configuration"
      evidenceModes := [.incrementalProject, .freshProject]
      requirement := "Claimed targets' `leanOptions` set auto-implicits off, `linter.missingDocs` on, no \
        linter off past §6.7 exclusions, with Mathlib its standard set on, header linter off or \
        licensed; no `-D` undoes it."
      rationale := "An automatic implicit adds a binder the source does not show, so the \
        elaborated \
        statement can quantify over more than the text a reviewer compares with the intent. A \
        linter reports only where it is on: without `linter.missingDocs`, or with a linter off \
        for a whole target, the warning-free build (RG2003) never sees those warnings. A `-D` \
        extra `lean` argument can override `leanOptions`, where the audit reads these options."
      remedy := "Set the target's Lake `leanOptions`: `autoImplicit` and `relaxedAutoImplicit` \
        false, `linter.missingDocs` true and, with Mathlib, the standard set and its three §6.7 \
        exclusions; remove other linter disables and each `-D` extra `lean` argument that \
        overrides these options."
      rewrites := [
        "Add ``⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, \
          ⟨`linter.missingDocs, true⟩`` to `leanOptions` (the same keys under `[leanOptions]` in \
          `lakefile.toml`), then declare each universe and implicit the build reports as unknown \
          and document each declaration it reports.",
        "With Mathlib, also set `weak.linter.mathlibStandardSet` to true, `weak.linter.hashCommand` \
          false, `weak.linter.style.longFile` 0 and `weak.linter.style.header` false, or true \
          with `weak.linter.style.header.license` set to your license line.",
        "Replace a target-wide ``⟨`linter.X, false⟩`` with `set_option linter.X false in` on the \
          one declaration the community's guidance allows, with a comment (§6.2).",
        "Delete each `-D name=value` in `moreLeanArgs` or `weakLeanArgs` that gives one of these \
          options a value the rule does not admit or turns off another linter; other extra \
          arguments may stay."]
      examples := {
        language := .lean
        audience := .adopter
        compliant := include_str "../../examples/rules/RG2006/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG2006/Violation.lean"
        correction := "The examples are the package's `lakefile.lean` (the corpus run adds its \
          `require regula` line). The correction adds the three options every claimed target \
          sets, automatic implicits off and `linter.missingDocs` on, without changing the \
          library or its source." } }
  | .executionUnresolved => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Execution closure must have no unresolved paths", category := .execution
      normativeClauses := [.computationMechanisms]
      applicability := "execution-unresolved"
      evidenceModes := [.incrementalProject, .freshProject, .freshFile]
      requirement := "Every path in an executable root's execution closure resolves; no \
        metaprogram hides replacement history."
      rationale := "An execution account that silently skipped an unresolved path would overstate \
        what the compiled program is known to run."
      remedy := "Remove the construction that prevents the analysis (for example a metaprogramming \
        command such as `run_cmd` in the module), or make the missing compiled code available, \
        then rerun."
      rewrites := [
        "Remove metaprogramming commands from modules whose `implemented_by` history must be \
          authenticated, or move them elsewhere.",
        "Ensure every dependency's compiled code is available in the build.",
        "Break cycles consisting only of replacement edges."]
      examples := {
        language := .lean
        audience := .adopter
        compliant := include_str "../../examples/rules/RG3001/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG3001/Violation.lean"
        correction := "The correction removes a no-effect `run_cmd` metaprogramming command that \
          prevents history authentication; the reference, replacement and correspondence theorem \
          are unchanged." } }
  | .executionBoundary => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Checked execution requires admitted correspondence", category := .execution
      normativeClauses := [.computationMechanisms]
      applicability := "execution-trusted-boundary"
      evidenceModes := [.incrementalProject, .freshProject, .freshFile]
      requirement := "Under `\"execution\": \"checked\"`, every reachable replacement or `extern` \
        boundary outside the Lean toolchain's own trusted base has a kernel-checked equality with \
        its reference."
      rationale := "`@[implemented_by g] def f` makes the kernel reason about `f` while compiled \
        code runs `g`. Without a proof relating them, theorems about `f` say nothing about the \
        program's behavior."
      remedy := "Prove the replacement equal to its reference on the complete domain, or remove \
        the trusted boundary, or claim `report` execution instead and keep the boundary reported."
      rewrites := [
        "State and prove `theorem f_eq (x) : f x = g x` (either direction, any prefix of the \
          domain with congruence) for the full domain, including implicit and instance arguments.",
        "Replace `implemented_by` with a proof-backed `@[csimp]` equality where it fits.",
        "If an external boundary is intended (an `extern` implementation, or unsafe or partial \
          code in an unclaimed dependency), claim `report` execution, where it is reported as \
          trusted and not failed. An owned `unsafe` or `partial` declaration on a claimed surface \
          still fails RG1006 in either mode."]
      examples := {
        language := .lean
        audience := .adopter
        compliant := include_str "../../examples/rules/RG3002/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG3002/Violation.lean"
        correction := "The correction adds the missing equality between the reference and its \
          replacement on the full natural-number domain, keeping the checked execution claim and \
          both implementations. In both, `spell` runs `Nat.repr`, whose replacement is the Lean \
          toolchain's own: it passes as the toolchain's trusted base, reported once." } }
  | .fenceStructure => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Documentation fences must have a valid classification", category := .documentation
      normativeClauses := [.documentationChecks]
      applicability := "fence-structure"
      evidenceModes := [.documentationExample]
      requirement := "Each `lean-fail` or `lean-trusted-compiler` marker sits immediately before \
        the `lean` fence it classifies, and every fence is closed."
      rationale := "A misspelled or misplaced marker must not silently turn a negative example \
        into a positive one or hide a fence from checking. Fail-closed structure keeps every \
        documented Lean claim checked as intended."
      remedy := "Put each `lean-fail` or `lean-trusted-compiler` marker immediately before the \
        `lean` fence it classifies, with a valid pattern, and close every fence."
      rewrites := [
        "Move the marker so no blank line or other content separates it from its fence.",
        "Delete orphan markers, or add the fence they were meant to classify.",
        "Use the exact marker spelling; write non-Lean sketches with another fence language."]
      examples := {
        language := .markdown
        audience := .adopter
        compliant := include_str "../../examples/rules/RG4001/Fixed.md"
        noncompliant := include_str "../../examples/rules/RG4001/Violation.md"
        correction :=
            "The correction removes the orphan marker; the positive reflexivity fence is \
              unchanged." } }
  | .positiveExample => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Positive examples require warning-free elaboration and admission", category :=
          .documentation
      normativeClauses := [.documentationChecks]
      applicability := "positive-example"
      evidenceModes := [.documentationExample]
      requirement := "An unmarked `lean` fence in the checked docs elaborates verbatim and \
        warning-free and passes the declaration and axiom rules."
      rationale := "Readers copy documented examples and trust them. A positive example that does \
        not elaborate, or that proves its claim with an axiom, teaches a false claim."
      remedy := "Make the example correct as printed: fix its errors or warnings, and make its \
        declarations satisfy the same rules as project code."
      rewrites := [
        "Fix the underlying finding shown with this diagnostic (for example prove the statement \
          instead of declaring an axiom).",
        "If the example is meant to fail, mark it with an exact `lean-fail` marker instead \
          (RG4003).",
        "Import what the example needs inside the fence; the checker inserts nothing."]
      examples := {
        language := .markdown
        audience := .adopter
        compliant := include_str "../../examples/rules/RG4002/Fixed.md"
        noncompliant := include_str "../../examples/rules/RG4002/Violation.md"
        correction := "The correction proves the same reflexivity claim in the positive fence; the \
          violation reports the RG1001 underlying rejection alongside RG4002." } }
  | .negativeExample => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Negative examples require completed intended rejection", category := .documentation
      normativeClauses := [.documentationChecks]
      applicability := "negative-example"
      evidenceModes := [.documentationExample]
      requirement := "A `lean-fail` fence fails to elaborate with one error message that matches \
        its whole pattern."
      rationale := "A negative example documents what Lean rejects. If it stops failing, or fails \
        for another reason, the documentation claims a rejection that no longer holds."
      remedy := "Make the example fail for exactly the documented reason, adjust the pattern to \
        match one real error message, or remove the marker if the example is valid."
      rewrites := [
        "If the example is actually valid, remove the `lean-fail` marker so it is checked as \
          positive.",
        "If it should fail, edit the example so it fails for the documented reason, and write a \
          pattern that matches that one error message.",
        "Keep patterns to literal fragments joined by `.*` and alternatives separated by `|`."]
      examples := {
        language := .markdown
        audience := .adopter
        compliant := include_str "../../examples/rules/RG4003/Fixed.md"
        noncompliant := include_str "../../examples/rules/RG4003/Violation.md"
        correction := "The correction labels an already valid reflexivity proof as a positive \
          example instead of inventing a compiler failure." } }
  | .trustedExample => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Teaching examples require authenticated compiler classification", category :=
          .documentation
      normativeClauses := [.documentationChecks]
      applicability := "trusted-example"
      evidenceModes := [.documentationExample]
      requirement := "A `lean-trusted-compiler` fence elaborates warning-free and contains an \
        authenticated compiler-trusting declaration."
      rationale := "Conforming claims reject compiler-trusting proofs (RG1004). A teaching fence \
        is how the documentation shows one: it is classified and never counts as a conforming \
        positive. A marker on an ordinary example would hide it from positive checking."
      remedy := "Use the marker only for an example that demonstrates `native_decide`, \
        `decide +native` or `bv_decide` (or another authenticated compiler-trusting mechanism); \
        otherwise remove it."
      rewrites := [
        "Remove the marker from an example that is an ordinary kernel proof; it is then checked as \
          a positive example.",
        "For a genuine teaching example, keep the native proof and import only the module that \
          provides its tactic (for example `import Init`, or `import Std.Tactic.BVDecide` for \
          `bv_decide`)."]
      examples := {
        language := .markdown
        audience := .adopter
        compliant := include_str "../../examples/rules/RG4004/Fixed.md"
        noncompliant := include_str "../../examples/rules/RG4004/Violation.md"
        correction := "The correction labels the same kernel proof as a positive example rather \
          than as native teaching." } }
  | .moduleDocumentation => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Claimed modules need a leading module docstring and no repeated import"
      category := .documentation
      normativeClauses := [.moduleDocumentation, .importDiscipline]
      applicability := "module-documentation"
      evidenceModes := projectModes
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
        audience := .adopter
        compliant := include_str "../../examples/rules/RG5001/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG5001/Violation.lean"
        correction :=
            "The correction adds module documentation to the unchanged reflexivity evidence." } }
  | .materialDocumentation => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Registered public material declarations require docstrings", category :=
          .documentation
      normativeClauses := [.inlineDocumentation]
      applicability := "material-documentation"
      evidenceModes := projectModes
      requirement := "Every public `@[regula_material]` declaration has a docstring stating its \
        purpose, hypotheses, result and boundary."
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
        audience := .adopter
        compliant := include_str "../../examples/rules/RG5002/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG5002/Violation.lean"
        correction := "The correction adds the registered theorem's docstring, including its `# \
          Intent` section; registration, proposition and proof are unchanged." } }
  | .materialIntent => {
      lifecycle := .active (.release ⟨4, 34, 0⟩)
      title := "Registered public material declarations require an Intent section", category :=
          .documentation
      normativeClauses := [.faithfulExplanation]
      applicability := "material-intent"
      evidenceModes := projectModes
      requirement := "Every public `@[regula_material]` docstring has a nonempty `# Intent` \
        section stating the requirement the claim must meet."
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
        audience := .adopter
        compliant := include_str "../../examples/rules/RG5003/Fixed.lean"
        noncompliant := include_str "../../examples/rules/RG5003/Violation.lean"
        correction := "The correction adds a nonempty `# Intent` section, structured with a `## \
          Requirement` subsection, to the registered theorem's existing docstring; the \
          explanation, registration, proposition and proof are unchanged." } }

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

end Regula
