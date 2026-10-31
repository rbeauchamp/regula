import RegulaCore.Residual
import RegulaCore.Rule

/-! # Rule explanations for the rule-reference site

`guide` is the explanatory prose for every rule, as one exhaustive definition over the closed
`RuleId`: adding a rule without its explanation is a compile error, and the site generator
renders a page from `guide id` together with the registry descriptor `descriptor id` and
the example pair of that rule. Nothing here is a second rule vocabulary: rule identity, title,
category, clauses and routes come from `descriptor`, and so do the agent-facing
requirement, short rationale, remedy, rewrites and example pair that the `regula` command also
prints. This module holds only the longer site and `regula explain` prose.

## Main declarations

- `NonemptyText`: text that has no empty value, written as its first character and the rest.
- `Guide`: the required sections of a rule explanation.
- `guide`: the explanation of each registered rule.
- `Guide.WellFormed`, `guide_wellFormed`: every required field of every rule is a nonempty
  text or list, and each rule names at least one residual obligation, one source and its
  proved linkage. The proof shape and configuration may be empty, and the page then omits them.
  Content adequacy is review.

## Boundaries

The prose is original Lean-specific explanation written against the standard
(`website/RegulaStandard`) and the
checker sources it names. Its fidelity to the standard and to the detectors is semantic
review (R-DOC, R-INTENT); nonemptiness is the only mechanical property checked here. The problem
and the linkage are nonempty by their type, and the kernel decides only whether each list section
is empty, so no proof here reduces a string and no section has a length limit. Text
uses Verso inline markup. A link target `@repo/PATH` denotes `PATH` in this repository at the
revision the site is built from; the generator requires each such file to exist.
Presentation structure follows Microsoft's CA1416 page as one illustrative reference
(cause, rationale, fix, configuration, examples); no content is copied from it.
-/

namespace Regula.Site

open Regula.Review (Residual)

/-- Text with at least one character, held as its first character and the rest. The type has no
empty value, so a section of this type is nonempty however long it is
(`NonemptyText.toString_ne_empty`), and no proof of that reads the text. A proof that decides
whether a string literal is empty reduces the literal in the kernel, at a cost that grows with its
length: on Lean v4.35.0 the kernel turns a literal into `String.ofList` of its characters
(`string_lit_to_constructor`, `src/kernel/inductive.cpp`), and its bytes are
`List.toByteArray`, whose loop pushes every byte before it returns any
(`Init/Prelude.lean`). Write one as `.mk 'A' " rule"`, whose first character is outside the string. -/
structure NonemptyText where
  /-- The first character. -/
  head : Char
  /-- The characters after the first. -/
  tail : String

namespace NonemptyText

/-- The text as a string: its first character followed by the rest. -/
def toString (t : NonemptyText) : String := String.singleton t.head ++ t.tail

/-- Every text has at least one byte: its first character's UTF-8 encoding is never empty. -/
theorem utf8ByteSize_pos (t : NonemptyText) : 0 < t.toString.utf8ByteSize := by
  rw [toString, String.utf8ByteSize_append, ← String.size_toByteArray, String.singleton,
    String.toByteArray_push, ByteArray.size_append, List.utf8Encode_singleton,
    List.size_toByteArray]
  exact Nat.lt_of_lt_of_le (List.length_pos_iff.mpr String.utf8EncodeChar_ne_nil)
    (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _))

/-- No text is empty. The proof goes through the size (`utf8ByteSize_pos`), which needs only
`propext` and `Quot.sound`; core's `String.singleton_ne_empty` also needs `Classical.choice`. -/
theorem toString_ne_empty (t : NonemptyText) : t.toString ≠ "" := fun empty => by
  have pos := t.utf8ByteSize_pos
  rw [empty, String.utf8ByteSize_empty] at pos
  exact Nat.lt_irrefl 0 pos

/-- The text followed by a string, whose rendering `toString_append` gives. -/
instance : HAppend NonemptyText String NonemptyText := ⟨fun t s => ⟨t.head, t.tail ++ s⟩⟩

/-- Appending a string to a text appends it to the text's rendering. -/
theorem toString_append (t : NonemptyText) (s : String) : (t ++ s).toString = t.toString ++ s :=
  String.append_assoc.symm

end NonemptyText

/-- The explanation sections of one rule page, in page order. `residuals` are the review
obligations a result of this rule never discharges; `checklist` names the module 8 checklist rows
the rule contributes to; `sources` are repository paths of its detector, policy and proof
modules. -/
structure Guide where
  /-- What goes wrong in a violating project: the page's lead paragraph and the *Problem*
  section of `regula explain`. -/
  problem : NonemptyText
  /-- How the detector decides the rule, one paragraph each (*What triggers it*). -/
  trigger : List String
  /-- Rationale beyond the registry's short `rationale` (`descriptor id`); may be empty. -/
  rationaleDetail : List String
  /-- The proof or statement a corrected project supplies (*Required proof shape*); empty when the
  rule asks for none. -/
  proofShape : List String
  /-- What a passing result of this rule establishes. -/
  established : List String
  /-- What a passing result does not establish, listed under *It does not establish*. -/
  notEstablished : List String
  /-- The options, commands and flags that affect this rule (*Configuration and exceptions*);
  empty when only those shared by every rule do. -/
  configuration : List String
  /-- Unsupported cases and limits of the detector (*Limitations and unsupported cases*). -/
  limitations : List String
  /-- The review obligations that a result of this rule leaves open. -/
  residuals : List Residual
  /-- The module 8 checklist row IDs the rule contributes to, such as `DECL-01`. -/
  checklist : List String
  /-- Repository paths of the rule's detector, policy and proof modules. -/
  sources : List String
  /-- Which steps of the rule's decision are kernel-checked theorems about the executed code and
  which stay operational (*Proved linkage*). -/
  linkage : NonemptyText

/-- The list sections every page fills: what triggers the rule, what a pass establishes and does
not establish, the limitations, the open obligations, the checklist rows and the sources. Deciding
it reads only whether each list is empty, never a string in one. -/
def Guide.ListsNonempty (g : Guide) : Prop :=
  g.trigger ≠ [] ∧ g.established ≠ [] ∧ g.notEstablished ≠ [] ∧ g.limitations ≠ [] ∧
  g.residuals ≠ [] ∧ g.checklist ≠ [] ∧ g.sources ≠ []

instance (g : Guide) : Decidable g.ListsNonempty := by
  unfold Guide.ListsNonempty; infer_instance

/-- Every required section has content and the page names its open obligations, sources and
proved linkage: the problem and the linkage render as nonempty strings, and every required list
section is nonempty. -/
def Guide.WellFormed (g : Guide) : Prop :=
  g.problem.toString ≠ "" ∧ g.ListsNonempty ∧ g.linkage.toString ≠ ""

/-- A guide is well formed exactly when its required list sections are nonempty: its problem and
linkage are nonempty by their type (`NonemptyText.toString_ne_empty`). -/
theorem Guide.wellFormed_iff_listsNonempty (g : Guide) : g.WellFormed ↔ g.ListsNonempty :=
  ⟨fun wellFormed => wellFormed.2.1,
    fun lists => ⟨g.problem.toString_ne_empty, lists, g.linkage.toString_ne_empty⟩⟩

/-- Shared statement: the linkage of a kept rule, whose subjects the function `function` reports
against the predicate `predicate` of the specification module `file`. -/
private def keptLinkage (function predicate file : String) : NonemptyText :=
  (NonemptyText.mk 'T' "he function `") ++ (function ++ "` reports exactly the subjects of \
    `RegulaSpecification." ++ predicate ++ "`, which `specification/RegulaSpecification/" ++ file ++
    "` states. The theorems of `specification/RegulaSpecification/Proofs/` prove it of each input \
    that has the closed form, with each axiom set that the rule reads the one the statement \
    gives. The shell's read of the build through Lake's load and Lean's import of the `.olean` \
    files (`Regula.Load.loadBundle`) is trusted, not proved, and so is `Lean.collectAxioms`.")

/-- Shared statement: the first trigger item of a documentation rule that is retired. -/
private def retiredTrigger : String :=
  "No check reports this rule. The specification retires it to written guidance (issue #488): \
    its intent stays a written instruction for the project, and review checks it. The standard \
    states it in §5.1 to §5.3 and §7.7."

/-- Shared statement: why the documentation rules are retired. -/
private def retiredRationale : String :=
  "A broken documentation example or a missing docstring is cheap to see and cheap to correct by \
    hand. Under the owner's rule of cost, such a rule stays a written instruction and an accepted \
    risk, not a check."

/-- Shared statement: what a pass establishes of a rule that Regula's checker does not report. -/
private def notReported : String :=
  "Nothing: a pass of `lake lint` says nothing about this rule."

/-- Shared statement: the linkage of a documentation rule that is retired. -/
private def retiredLinkage : NonemptyText :=
  .mk 'N' "one. No check reports this rule. The specification gives it the fate retired \
    (`RegulaSpecification.fate`), and the registry records the retirement in its lifecycle."

/-- Shared statement: foundation labels. -/
private def foundationTable : String :=
  "The three logical labels are Kernel-only (no axioms), Choice-Free (a subset of `propext` and \
    `Quot.sound`) and Standard-Logical (additionally `Classical.choice`). A surface's `claim` in \
    `foundation_manifest.json` is the upper bound for each constant of its modules."

/-- Shared statement: how the axiom set of a constant is computed. -/
private def axiomSet : String :=
  "The transitive axiom set of a constant is each axiom that it reaches through the constants \
    that each constant mentions, as `Lean.collectAxioms` walks them: the type and value of a \
    definition, theorem or opaque constant, the type of an axiom, constructor or recursor, and \
    the type and constructors of an inductive type. Imported constants are included. The loader \
    computes it with `Lean.collectAxioms` over the constants that Lean loads from the `.olean` \
    files of the build, without the table of axioms that Lean records for each module."

/-- The explanation of each rule. -/
def guide : RuleId → Guide
  | .projectAxiom => {
      problem := .mk 'A' " declaration owned by a claimed module is a logical `axiom`. Lean accepts \
        an axiom without evidence, so every theorem that uses it is only conditional on an \
        assumption that no proof discharges."
      trigger := [
        "`Regula.Closed.Tables.rg1001` reads each constant of a claimed module from \
          the environments that the shell loads from the build. It reports the constant when its \
          kind is `axiom` (`ConstantInfo.axiomInfo`).",
        "The rule applies whether or not a declaration uses the axiom. Private, protected and \
          generated names count alike, and a name or a namespace exempts nothing. The axiom that a \
          native proof adds is a constant of its module too, so this rule reports it, and RG1004 \
          reports the constants that use it."]
      rationaleDetail := [
        "Lean 4 has no `constant` command; an `opaque` definition with a body is kernel-checked \
          and is classified separately, not as an axiom."]
      proofShape := [
        "A conditional result must carry the assumption in its type, for example `∀ (h : P), Q`, \
          so the exact theorem statement shows what it depends on. Its transitive axiom set must \
          then fit the surface's foundation profile."]
      established := [
        "No constant of a claimed module is an axiom, in the environments that the shell loaded. \
          RG2004 decides which modules the build holds and which of them are claimed.",
        "The rule reads the declarations that Lean loads from the `.olean` files of the build, \
          not the source text."]
      notEstablished := [
        "That the hypotheses replacing an axiom are satisfiable or appropriate: that is the \
          claim's intent and non-vacuity review.",
        "Anything about axioms of imported dependencies. The transitive axiom sets of RG1003 and \
          RG1005 report those."]
      configuration := []
      limitations := [
        "A metaprogram that adds declarations still adds constants of its module. The rule reads \
          them like written ones.",
        "The rule reads the constants of the claimed modules that the build holds. A module that \
          Lake does not build for a target is no input (RG2004)."]
      residuals := [.intent, .nonvacuity]
      checklist := ["FOUND-01", "TYPE-04", "THEOREM-09", "THEOREM-01", "DECL-03", "BUILD-01"]
      linkage := keptLinkage "Regula.Closed.Tables.rg1001" "Violates1001"
        "Foundation.lean"
      sources := ["lean/Regula/Rules.lean", "lean/Regula/Load.lean",
        "specification/RegulaSpecification/Foundation.lean",
        "website/RegulaStandard/LogicProofPatterns.lean"] }
  | .proofHole => {
      problem := .mk 'T' "he declaration depends on `sorryAx`: a `sorry`, an `admit`, an unfinished \
        tactic proof, or an imported declaration with such a hole occurs in its transitive axiom \
        set. The proposition is not proved."
      trigger := [
        axiomSet,
        "`Regula.Closed.Tables.rg1002` reports a constant of a claimed module when \
          `sorryAx` is in its transitive axiom set. A `sorry`, an `admit`, an unfinished tactic \
          proof and a hole of an imported declaration all put `sorryAx` in the kernel term.",
        "Lean itself warns `declaration uses 'sorry'` by default, so `lake build --wfail` fails \
          first on a hole in a claimed module (RG2003). This rule also reports a hole that the \
          warning does not show, such as one inherited from an import or one under \
          `set_option warn.sorry false`."]
      rationaleDetail := []
      proofShape := [
        "The completed declaration keeps the same statement. Weakening the proposition until it is \
          easy to prove changes the requirement and is a semantic review failure, even though this \
          rule then passes."]
      established := [
        "No constant of a claimed module has `sorryAx` in its transitive axiom set, computed from \
          the constants that the shell loaded."]
      notEstablished := [
        "That the completed proof proves the intended statement; the proposition itself is \
          reviewed against its intent.",
        "Lean's own warning for `sorry` is a build warning (RG2003). This rule does not depend on \
          it, and turning the warning off does not waive this rule."]
      configuration := []
      limitations := [
        "The axiom set comes from the constants as Lean loaded them from the `.olean` files. \
          Lean's kernel did not check them again in this run: `lake check` does that (RG2005).",
        "A constant of a claimed module for which the loader computed no axiom set makes the run \
          INCOMPLETE (RG2001), not a pass."]
      residuals := [.invocation, .intent]
      checklist := ["FOUND-02", "THEOREM-06", "TYPE-04", "THEOREM-01", "THEOREM-09", "BUILD-01"]
      linkage := keptLinkage "Regula.Closed.Tables.rg1002" "Violates1002"
        "Foundation.lean"
      sources := ["lean/Regula/Rules.lean", "lean/Regula/Load.lean",
        "specification/RegulaSpecification/Foundation.lean"] }
  | .unknownAxiom => {
      problem := .mk 'A' " declaration's transitive axiom set contains an axiom outside Lean's \
        standard logical foundation (`propext`, `Quot.sound` and `Classical.choice` of the \
        toolchain) that is neither `sorryAx` (RG1002) nor the axiom of a native proof (RG1004)."
      trigger := [
        axiomSet,
        "`Regula.Closed.Tables.rg1003` reports a constant of a claimed module when its \
          transitive axiom set has an axiom that is not known, not `sorryAx` and not the axiom of \
          a native proof. A known axiom is `propext`, `Quot.sound` or `Classical.choice`, declared \
          in a module of the toolchain's own library.",
        "Imported axioms are not exempt: a constant that uses an axiom of a dependency is \
          reported, though the axiom is declared elsewhere. An axiom named `propext` that a module \
          of the project declares is not known."]
      rationaleDetail := [
        foundationTable]
      proofShape := [
        "After the fix, the transitive axiom set is a subset of `propext`, `Quot.sound` and \
          `Classical.choice` and fits the surface claim (RG1005)."]
      established := [
        "Each axiom in the transitive set of each constant of a claimed module is a known axiom, \
          `sorryAx` or the axiom of a native proof. RG1002 and RG1004 report the last two."]
      notEstablished := [
        "Anything about an imported dependency beyond its axioms. Imported declarations are a \
          trusted boundary."]
      configuration := []
      limitations := [
        "The loader decides that a module is in the toolchain's library from the place of its \
          `.olean` file: below the library directory of the toolchain that `LEAN_SYSROOT` names. \
          That Lean finds the toolchain's library only there is an assumption, as the \
          specification states.",
        "The axiom of a native proof is recognized by its name form \
          `<declaration>._native.<tactic>.<suffix>`. An axiom with that name form is reported as \
          RG1004 in place of RG1003, with the same verdict."]
      residuals := [.invocation]
      checklist := ["FOUND-03", "TYPE-04", "THEOREM-01", "THEOREM-09", "BUILD-01"]
      linkage := keptLinkage "Regula.Closed.Tables.rg1003" "Violates1003"
        "Foundation.lean"
      sources := ["lean/Regula/Rules.lean", "lean/Regula/Load.lean",
        "specification/RegulaSpecification/Foundation.lean"] }
  | .compilerTrusting => {
      problem := .mk 'A' " declaration of a claimed module depends on the axiom that a native proof \
        adds. `native_decide`, `decide +native` and `bv_decide` evaluate with compiled code and \
        add an axiom that asserts the result. The proof then trusts compiled code and the Lean \
        compiler, not the kernel."
      trigger := [
        "At Lean v4.35.0, `native_decide`, `decide +native` and `bv_decide` add an ordinary axiom \
          named `<declaration>._native.<tactic>.<suffix>` (`Lean/Meta/Native.lean`). \
          `Regula.Closed.Tables.rg1004` reports a constant of a claimed module when \
          its transitive axiom set has an axiom of that name form \
          (`Regula.Closed.nativeProofAxiom`).",
        "It also reports an axiom of `Regula.Closed.compilerAxioms`, the axioms by which the \
          kernel trusts the compiler. At v4.35.0 the toolchain declares none, so the list is \
          empty.",
        "The axiom itself is a constant of its module. RG1001 reports it, and this rule reports \
          it too, since its own axiom set holds it."]
      rationaleDetail := []
      proofShape := [
        "The replacement proof proves the same proposition. Kernel reduction (`decide`, `rfl`) is \
          permitted, subject to the surface's foundation profile."]
      established := [
        "No constant of a claimed module has, in its transitive axiom set, an axiom with the name \
          form of a native proof or an axiom of `compilerAxioms`."]
      notEstablished := [
        "Performance of the kernel replacement proof; cost claims are separate (R-COST).",
        "That an axiom with that name form came from a native proof: the rule reads the name \
          only."]
      configuration := []
      limitations := [
        "The rule identifies the axiom of a native proof by its name. An author can give an \
          axiom that name. This rule then reports it in place of RG1003, and the verdict is the \
          same.",
        "The name form is that of Lean v4.35.0. A different release of Lean can name these \
          axioms in a different form. The rule then reports them as RG1003."]
      residuals := [.invocation, .cost]
      checklist :=
          ["FOUND-05", "FOUND-03", "THEOREM-10", "THEOREM-01", "THEOREM-06", "DECL-03", "COMP-01",
              "BUILD-01"]
      linkage := keptLinkage "Regula.Closed.Tables.rg1004" "Violates1004"
        "Foundation.lean"
      sources := ["lean/Regula/Rules.lean", "lean/Regula/Load.lean",
        "specification/RegulaSpecification/Foundation.lean"] }
  | .profileExceeded => {
      problem := .mk 'A' " declaration's transitive axiom set has an axiom that the profile of its \
        surface does not admit: its least foundation label is stronger than the claim of the \
        surface it belongs to."
      trigger := [
        "Each claimed target gives its modules the profile of its surface in \
          `foundation_manifest.json`. `Regula.Closed.Tables.rg1005` reports a \
          constant of a claimed module when its transitive axiom set has an axiom that a profile \
          of its module does not admit.",
        "Kernel-only admits no axiom. Choice-free admits `propext` and `Quot.sound`. \
          Standard-logical also admits `Classical.choice`. Each admitted axiom is the toolchain's \
          own constant.",
        "Each axiom that RG1002, RG1003 or RG1004 names is outside each profile, so this rule \
          reports it as well. A wrong choice between those rules changes the rule of a finding, \
          but not the verdict.",
        foundationTable]
      rationaleDetail := []
      proofShape := [
        "The replacement proves the same proposition. Classical, erased proofs are permitted when \
          the surface claims Standard-Logical; executable behavior is a separate account (RG1007, \
          RG3001, RG3002)."]
      established := [
        "Each constant's transitive axiom set is within the profile of each claimed target of its \
          module."]
      notEstablished := [
        "Which label a declaration should have: the claim is a project decision, reviewed with its \
          rationale."]
      configuration := [
        "The profile is the `claim` of the surface in `foundation_manifest.json`: `kernel-only`, \
          `choice-free` or `standard-logical`. A claim of `compiler-trusting` makes the run \
          INCOMPLETE (RG2001): the checker checks no such profile."]
      limitations := [
        axiomSet,
        "The table of axioms that Lean records for a module is not read. That table can omit an \
          axiom: Lean 4.35.0 records none for `Float`, whose constructor's type reaches `propext` \
          and `Quot.sound`. `#print axioms` can then show a smaller set than this rule.",
        "A proof that could avoid an axiom still carries it until it is rewritten."]
      residuals := [.invocation]
      checklist := ["FOUND-03", "FOUND-04", "BUILD-02", "THEOREM-01", "THEOREM-10", "BUILD-01"]
      linkage := keptLinkage "Regula.Closed.Tables.rg1005" "Violates1005"
        "Foundation.lean"
      sources := ["lean/Regula/Rules.lean", "lean/Regula/Load.lean",
        "specification/RegulaSpecification/Foundation.lean",
        "website/RegulaStandard/MathematicalFoundations.lean"] }
  | .escapeHatch => {
      problem := .mk 'A' " declaration of a claimed module is `unsafe` or `partial`, and it is not \
        the recursion helper that Lean adds for a safe recursive definition."
      trigger := [
        "`Regula.Closed.Tables.rg1006` reports a constant of a claimed module that \
          Lean marks unsafe (`ConstantInfo.isUnsafe`) or partial (`ConstantInfo.isPartial`). An \
          unsafe declaration is checked only in Lean's unsafe mode and is no logical evidence. A \
          partial definition has no termination proof.",
        "The one exception is a recursion helper (`Regula.Closed.Input.recursionHelper`): a \
          partial constant `f._unsafe_rec`, not unsafe, not `extern` and with no `implemented_by` \
          replacement. It is in the module of a safe, total definition `f` that is not `extern` \
          and has no replacement.",
        "At Lean v4.35.0 a `partial def f` is an opaque constant `f` with a partial helper \
          `f._unsafe_rec`. The base `f` is no definition, so its helper is no exception. The \
          finding names the helper `f._unsafe_rec`, not the `partial def`."]
      rationaleDetail := [
        "A helper is no logical evidence: Lean's kernel refuses a safe constant that mentions a \
          partial one (`src/kernel/type_checker.cpp`). What a helper computes is a question of \
          execution, which RG3002 decides under a checked execution claim."]
      proofShape := [
        "A total replacement keeps the same domain and result type; if it changes behavior, state \
          and prove the relation to the intended function."]
      established := [
        "No constant of a claimed module is unsafe or partial, apart from a recursion helper of a \
          safe definition of the same module, by the form above."]
      notEstablished := [
        "That unsafe or partial code elsewhere is logically unsound; the rule concerns evidence, \
          not a claim that such code is wrong.",
        "What a recursion helper computes: the rule identifies a helper by its form. Under a \
          checked execution claim, RG3002 decides the code that runs.",
        "Termination proofs' adequacy for cost claims."]
      configuration := []
      limitations := [
        "A metaprogram can add a constant of the helper's form. The kernel checks the base's \
          definition, and the helper's code is what runs.",
        "What a helper computes is not read: the rule reads its form (standard §7.4)."]
      residuals := [.invocation, .cost, .intent]
      checklist := ["COMP-02", "THEOREM-05", "THEOREM-01", "DECL-03", "BUILD-01"]
      linkage := keptLinkage "Regula.Closed.Tables.rg1006" "Violates1006"
        "Execution.lean"
      sources := ["lean/Regula/Rules.lean", "lean/Regula/Load.lean",
        "specification/RegulaSpecification/Execution.lean"] }
  | .executableContract => {
      problem := .mk 'A' "n `ExecutableContract f R` of a claimed module does not constrain the \
        code that callers run: it applies its implementation to arguments, the implementation is \
        not safe, total and computable, or a decision contract states its specification through \
        the implementation."
      trigger := [
        "The loader reads each theorem whose type, under its binders, is \
          `Regula.ExecutableContract f R` (`Regula.Load.contractOf`). The implementation is the \
          head constant of `f`, and the arguments that `f` applies it to are the arguments it \
          fixes.",
        "The condition `R` is a decision contract when its body, under a function binder, is an \
          application of `Regula.Decides`, `Regula.DecidesSoundly` or `Regula.DecidesCompletely` \
          (`Regula.Load.decisionOf`). The constants of its specification argument are the \
          specification. Those of its acceptance predicate and of the decided function are the \
          acceptance predicate's.",
        "`Regula.Closed.Tables.rg1007` reports the theorem when `f` fixes an argument, \
          when the implementation is unsafe, partial or noncomputable, or when the contract is a \
          decision contract whose specification reaches the implementation through the constants \
          that each constant mentions.",
        "Lean's type checker separately checks the supplied proof of `R f`."]
      rationaleDetail := [
        "A checker with only a soundness theorem can refuse every input, and one with only a \
          completeness theorem can accept every input. A one-way guarantee is often the right \
          choice, as for a refusal that fails closed, but an unstated one cannot be told from an \
          omission. A kind states the direction in the registration's type.",
        "Each kind carries a witness about `f` itself: `DecidesSoundly` requires an input `f` \
          accepts and `DecidesCompletely` an input it refuses. So the function that refuses \
          every input has no sound kind and the function that accepts every input has no \
          complete kind (`Regula.DecidesSoundly.not_of_refuses_all`, \
          `Regula.DecidesCompletely.not_of_accepts_all`)."]
      proofShape := [
        "`ExecutableContract f R` for a named constant `f` with `R : type-of-f → Prop` stating the \
          full-domain requirement. The proof inhabits exactly `R f`; a weaker `R` changes the \
          requirement and is a review failure.",
        "For a function that acts as a checker, `R` is a decision kind over an acceptance \
          predicate and a specification: `Regula.Decides accepts spec` for both directions, \
          `Regula.DecidesSoundly accepts spec` when a refusal may be wrong, \
          `Regula.DecidesCompletely accepts spec` when an acceptance may be. A function of several \
          arguments is decided on their product: `fun g => Regula.Decides accepts spec \
          (Function.uncurry g)` for two arguments, with `spec` over the pairs.",
        "Where the type of an argument depends on an earlier argument, state the kind about `f` \
          applied to the fields of one structure whose fields are the arguments \
          (`Regula.Decides.of_packing`). Where the result type depends on the arguments, state it \
          about an erasure of the result: `Regula.Dependent.isSome g` for an `Option` of a \
          payload and `Regula.Dependent.isOk g` for an `Except` of one."]
      established := [
        "The contract fixes no argument of its implementation, and the implementation is safe, \
          total and computable. Lean checked a proof of the stated condition, as for each \
          theorem.",
        "For a decision contract: the specification does not reach the implementation through \
          the constants that each constant mentions."]
      notEstablished := [
        "That `R` expresses the intended behavior (R-INTENT) and that each caller uses the \
          contracted implementation (R-INVARIANT).",
        "That a function acting as a checker is registered: RG1008 requires a decision contract \
          only of a function that the project registers with `Regula.RegisteredDecision`.",
        "For a decision contract: that the specification is independent of the implementation in \
          substance. A specification can restate the body of `f` without its name, and a copy of \
          `f` under a different name passes. Shared Boolean tests are RG1009.",
        "That the decided function in the condition is `f` on its whole domain: the rule reads the \
          implementation from the contract's first argument, not from the condition.",
        "For a law (`Regula.DecisionEquivalence`): any outcome. A law holds on an empty domain, \
          where `f` neither accepts nor refuses an input (`Regula.DecisionEquivalence.of_empty`).",
        "Behavior of compiled code beyond the Lean definition; execution boundaries are RG3001 and \
          RG3002."]
      configuration := []
      limitations := [
        "The kind is read from the head constant of the condition's body, without unfolding. A \
          definition that stands for a kind is read as no kind, and the contract is then an \
          ordinary one.",
        "A condition that holds a kind inside a larger proposition, such as a conjunction, has no \
          kind. Register the further clauses separately.",
        "`Regula.DecisionEquivalence`, a law of the two directions with no outcome, is no decision \
          kind."]
      residuals := [.intent, .invariant, .invocation]
      checklist :=
          ["BUILD-03", "THEOREM-07", "SCOPE-02", "SCOPE-03", "TYPE-01", "THEOREM-01",
              "THEOREM-03", "COMP-01", "BUILD-01", "BUILD-02"]
      linkage := keptLinkage "Regula.Closed.Tables.rg1007" "Violates1007"
        "Contracts.lean" ++ " The reading of a contract from its theorem's type \
        (`Regula.Load.contractOf`, `Regula.Load.decisionOf`) is operational."
      sources := ["lean/Regula/Contract.lean", "lean/Regula/Rules.lean", "lean/Regula/Load.lean",
        "specification/RegulaSpecification/Contracts.lean"] }
  | .decisionContract => {
      problem := .mk 'A' " function of a claimed module registered as a decision with `Regula.RegisteredDecision` has no \
        decision contract in a claimed module, and its result type is not `Decidable _`. Nothing \
        then states whether the function accepts only what its specification allows, everything \
        its specification allows, or both."
      trigger := [
        "The loader reads the registrations from the types of the constants of claimed modules \
          (`Regula.Load.registrationOf`): a constant of type `Regula.RegisteredDecision f` \
          registers the function `f`. A registration counts in each environment that loads its \
          module.",
        "`Regula.Closed.Tables.rg1008` reports a registered function of a claimed module \
          when its result type is not `Decidable _` and no theorem of a claimed module in the \
          same environment is a decision contract (RG1007) about it.",
        "The rule reads each environment apart, and a contract counts only where its module is \
          loaded. So write the registration where the contract's environment loads it, such as \
          with `theorem f_registered : Regula.RegisteredDecision @f := ⟨⟩` beside the contract."]
      rationaleDetail := [
        "Standard §7.5 requires that removing evidence while its requirement remains fails the \
          gate. For a contract no caller consumes through `ExecutableContract.run`, deleting the \
          theorem would delete the requirement with it. The registration keeps the requirement at \
          the function: deleting the contract while the registration stays is this rule's finding.",
        "A `Decidable p` result needs no contract: its accepting value carries a proof of `p` and \
          its refusing value a proof of `¬p`, so both directions hold by construction (standard \
          §3.2.4). It carries no witness that both outcomes occur: `Decidable True` qualifies."]
      proofShape := [
        "`ExecutableContract f (Regula.Decides accepts spec)`, or `Regula.DecidesSoundly` or \
          `Regula.DecidesCompletely` for a declared one-way guarantee, in a claimed module that \
          each environment of the registration loads. RG1007 gives the shape of the contract.",
        "Or a result type written `Decidable (spec x)`: the loader reads it without unfolding, so \
          a type written `DecidablePred spec` is not read as one."]
      established := [
        "Each function of a claimed module that a claimed module registers with `Regula.RegisteredDecision`, and whose result \
          type is not `Decidable _`, is the implementation of a decision contract of a claimed \
          module in each environment that holds the registration.",
        "Removing that contract while the registration stays is reported."]
      notEstablished := [
        "That each function that acts as a checker is registered: the registration is the \
          project's own declaration, and removing it removes the requirement (R-INVARIANT).",
        "That the contract's specification is the intended one (R-INTENT), that a one-way kind \
          should have been two-way, or which value an accepting result carries.",
        "For a `Decidable` result: that the decided proposition is the intended one, that both \
          outcomes occur, or that the instance is computable.",
        "That callers act on the function's verdict (R-INVARIANT)."]
      configuration := [
        "`Regula.RegisteredDecision` is declared in `Regula.Decision`, a published checker interface \
          a claimed module may import: `import Regula.Decision`, or `public import \
          Regula.Decision` in a file that is a `module`. Write `theorem f_registered : \
          Regula.RegisteredDecision @f := ⟨⟩` in a module that imports `f`."]
      limitations := [
        "A contract in a module that an environment of the registration does not load does not \
          count there. Put the registration beside the contract, or the contract beside the \
          function.",
        "A function whose result type depends on its arguments in a way neither erasure removes, \
          or for which no accepted or refused input can be given with a proof, has no decision \
          kind (RG1007). Return `Decidable _`, or leave the function unregistered and record why.",
        "A function in `IO`, `MetaM` or a different monad comes into scope through the pure \
          decision it runs: register that decision.",
        "The registration is environment state that a claimed module writes. It only adds a \
          requirement; no registration or option waives one. The specification makes a \
          registration a declaration of a type of Regula's interface, whose form is `Regula.RegisteredDecision`."]
      residuals := [.intent, .invariant, .invocation]
      checklist := ["THEOREM-07", "BUILD-03"]
      linkage := keptLinkage "Regula.Closed.Tables.rg1008" "Violates1008"
        "Contracts.lean"
      sources := ["lean/Regula/Decision.lean", "lean/Regula/Rules.lean", "lean/Regula/Load.lean",
        "specification/RegulaSpecification/Contracts.lean"] }
  | .sharedTest => {
      problem := .mk 'T' "he specification of a decision contract and its implementation, or its \
        acceptance predicate, both reach one function with a result of `Bool` or `BEq`. The \
        specification then states the condition with the test that the function runs. The kind \
        is a theorem that compares the test with itself at that point, so it does not state \
        the condition a second time."
      trigger := [
        "For each decision contract of a claimed module, `Regula.Closed.Tables.rg1009` \
          searches the constants that the specification reaches, and those that the \
          implementation and the acceptance predicate reach. Each search follows the constants \
          that each constant mentions: the type and value of a definition, theorem or opaque \
          constant, and the type and constructors of an inductive type.",
        "It reports the contract when the two searches reach one Boolean test outside the \
          toolchain: a constant whose type's result is `Bool` or `BEq _`, whose module is not in \
          the toolchain's library, and that is no field's projection function. The finding names \
          each shared test.",
        "A field's projection function reads a field of data, which no definition computes, so \
          the two sides may both read a field of the input. The loader reads whether a constant \
          is a projection from its kernel-checked value (`Regula.Load.projectionValue`), not from \
          Lean's record of projection functions."]
      rationaleDetail := [
        "A kind is a theorem about the present definitions. When the specification and the \
          implementation both call `test`, a change of `test` changes the two together. Each \
          direction then holds or fails as its proof does, and a proof that goes through \
          `test` on the two sides stays valid although the meaning changed. In the smallest \
          case the specification is `test x = true`, the function is `test`, and the proof of \
          the two directions is `Iff.rfl`.",
        "A proposition in the place of the test is a second statement, in other terms: a \
          quantifier, an order relation or an equation in place of a fold, a comparison \
          function or a `BEq`. The theorem that the test decides the proposition is then a proof \
          that connects two statements."]
      proofShape := [
        "`def P (x : α) : Prop := …`, `instance (x : α) : Decidable (P x) := …`, a function \
          that runs `decide (P x)` or `if P x then … else …`, and `ExecutableContract f \
          (Regula.Decides accepts P)`.",
        "Or a function that keeps its test, a theorem `test x = true ↔ P x`, and an instance \
          `decidable_of_iff _ (test_iff x)` that the function runs. The specification names `P` \
          and not the instance: the search follows the value of each constant that it reaches, \
          an instance's too.",
        "For a comparison of values of a type with a derived `BEq`: `deriving DecidableEq`, and \
          `=` in the specification."]
      established := [
        "The specification of each decision contract of a claimed module and its implementation \
          or acceptance predicate reach no shared Boolean test outside the toolchain, through the \
          constants that each constant mentions."]
      notEstablished := [
        "That the specification is the intended one (R-INTENT). The rule compares names. A \
          copy of a test under a different name is a different constant and passes, and so does \
          a proposition that copies the expression of the test with `= true`.",
        "Anything about a shared function of a different result type, such as a function that \
          returns a list or a record. Whether the specification is about that function remains \
          review (R-INTENT).",
        "Anything about a test of Lean's own library, which the two sides can both call.",
        "A test that only a runtime replacement runs (`implemented_by`, `extern`, `csimp`): the \
          search reads kernel-checked values. RG3001 and RG3002 account for the replacement."]
      configuration := []
      limitations := [
        "The search follows the value of each definition that it reaches, a `Decidable` \
          instance's included, and the constructors of each inductive type, the input type's \
          included. So a test that an instance of the specification runs, or that an invariant of \
          the input type names, is shared when the implementation reaches it too.",
        "The search reads the value of a theorem that it reaches, so a test that a proof in the \
          specification names is shared too. That refuses more, which is the safe side.",
        "A constant of type `Bool` that takes no argument is a Boolean test too: its type's result \
          is `Bool`.",
        "The rule searches each decision contract, also one that RG1007 reports."]
      residuals := [.intent, .invocation]
      checklist := ["THEOREM-07", "BUILD-03"]
      linkage := keptLinkage "Regula.Closed.Tables.rg1009" "Violates1009"
        "Contracts.lean"
      sources := ["lean/Regula/Rules.lean", "lean/Regula/Load.lean",
        "specification/RegulaSpecification/Contracts.lean", "lean/Regula/Contract.lean"] }
  | .environment => {
      problem := .mk 'T' "he shell could not load the finished build, or the input it loaded does \
        not have the closed form. The run cannot decide the rules, so the result is INCOMPLETE, \
        not a violation of the source."
      trigger := [
        "`Regula.Load.loadBundle` loads the workspace with Lake under the toolchain that \
          `LEAN_SYSROOT` names, and reads `foundation_manifest.json` with \
          `Regula.Checker.Manifest.parse`. It reads the `.olean` files of each module of the root \
          package that Lake builds, and imports the modules with `Lean.importModules`.",
        "A read that fails refuses the input. Examples are a missing `.olean` file, a module of a \
          target whose `.olean` file is outside the root package's build, a manifest that the \
          parser refuses, and a claim of `compiler-trusting`.",
        "`Regula.Closed.Bundle.refusal?` then refuses an input without the closed form: a name \
          declared twice in one environment, a constant that mentions a name that the \
          environment does not hold, a module of a target with no record or loaded in no \
          environment, environments that do not carry one project, or a claim of no target.",
        "The admission also refuses a constant of a claimed module or a correspondence theorem for \
          which the loader computed no axiom set, and the loader refuses a constant of the \
          execution closure whose compiled code it could not read. The last line of the run names \
          the reason, and `lake lint` exits 2."]
      rationaleDetail := []
      proofShape := []
      established := [
        "A passing result read the build that Lake's load of the workspace names, with the \
          toolchain that runs `lake lint`, and the input had the closed form. A build that \
          cannot be loaded, and an input without the closed form, are INCOMPLETE and never a \
          pass."]
      notEstablished := [
        "That a dependency checkout matches its recorded revision: Lake's acquisition of \
          dependencies is trusted.",
        "That the build is current with the source: `lake lint` reads the `.olean` files that the \
          build left, and it builds nothing. Run `lake build --wfail` first (RG2003)."]
      configuration := [
        "There is no configuration that turns an incomplete run into a pass."]
      limitations := [
        "That Lean refuses an `.olean` file that a different Lean version wrote \
          (`Lean.readModuleData`) is an assumption, as the specification states."]
      residuals := [.invocation]
      checklist := ["DECL-01", "DECL-04"]
      linkage := .mk 'N' "one for the read of the build: `Regula.Load.loadBundle` reads it through \
        Lake's and Lean's own interfaces, which are trusted. `Regula.Closed.run` gives INCOMPLETE \
        exactly when `Regula.Closed.Bundle.refusal?` refuses the bundle (`run_refused`, \
        `run_complete`), and `refusal_none_iff` proves that it refuses exactly a bundle without \
        the specification's `Bundle.WellFormed` or without an axiom set that a rule reads \
        (`specification/RegulaSpecification/Proofs/Verdict.lean`)."
      sources := ["lean/Regula/Load.lean", "lean/Regula/Workspace.lean", "lean/Regula/Input.lean",
        "lean/Regula/Shell.lean",
        "specification/RegulaSpecification/Gate.lean"] }
  | .configuration => {
      problem := .mk 'T' "he claim in `foundation_manifest.json` does not classify each library \
        and executable of the root package exactly once, names a target that Lake does not have, \
        classifies an executable differently from a library that contains its root module, or \
        claims a target that is not a default target."
      trigger := [
        "`Regula.Closed.Input.manifestFindings` reads Lake's targets of the root package, \
          with the default targets of its load, and the claim. It reports a target that the claim \
          classifies zero times or more than once, and an entry of the claim that names no target \
          of Lake.",
        "It reports an executable that the claim classifies differently from a library that \
          contains its root module, and a claimed target that is not a default target. A claimed \
          target must be a default target because `lake check` checks only the modules of the \
          default targets (RG2005).",
        "A manifest that `Regula.Checker.Manifest.parse` refuses, such as one with an unknown key, \
          a wrong schema version or a missing rationale, makes the run INCOMPLETE (RG2001): the \
          input then has no claim to check."]
      rationaleDetail := []
      proofShape := []
      established := [
        "The claim classifies each library and executable of the root package exactly once, names \
          no target that Lake does not have, classifies each executable as each library that \
          contains its root module, and claims only default targets."]
      notEstablished := [
        "That the chosen claims and exclusions are appropriate for the project; that is reviewed \
          with each rationale.",
        "Exclusions do not permit a claimed module to import an excluded one (RG2004)."]
      configuration := [
        "The manifest is the configuration; there is no flag that accepts an invalid manifest.",
        "`lake exe regula doctor` reports this rule's findings from Lake's load and the claim, \
          without a build."]
      limitations := [
        "`Regula.Checker.Manifest.parse_ok` and `parseValue_ok` state that the reader of \
          `foundation_manifest.json` accepts a text exactly when the text parser's value encodes a \
          valid claim, and `parseValue_toJson` that the writer's value of a valid claim reads back \
          as that claim. White space and the order of keys are free. No theorem relates the text \
          parser `PolicyCodec.parse` to the JSON grammar: that is an accepted risk, because a \
          wrong parse of a hand-written file names no target or the wrong one, which RG2002 \
          reports."]
      residuals := [.invocation, .intent, .invariant]
      checklist := ["DECL-04", "SCOPE-05", "BUILD-04", "DECL-01", "BUILD-01"]
      linkage := keptLinkage "Regula.Closed.Input.manifestFindings" "Violates2002"
        "Project.lean"
      sources := ["lean/Regula/Checker/Manifest.lean", "lean/Regula/Rules.lean",
        "lean/Regula/Load.lean", "specification/RegulaSpecification/Project.lean"] }
  | .sourceBuild => {
      problem := .mk 'T' "he claimed source did not elaborate warning-free: its build failed or \
        logged a warning."
      trigger := [
        "Regula's checker does not report this rule. The specification hands it to Lake: \
          `lake build --wfail` of the claimed targets fails when a job logs a warning or an \
          error. The project's gate runs it before `lake check` and `lake lint`.",
        "Run `lake build --wfail` before `lake lint`. `lake lint` reads the `.olean` files that \
          the build left, and it does not see the messages of the build."]
      rationaleDetail := []
      proofShape := [
        "The fix must not change the proposition or behavior being claimed; if it does, review the \
          statement again."]
      established := [
        notReported,
        "A pass of `lake build --wfail` establishes that no job of the build logged a warning or \
          an error."]
      notEstablished := [
        "That no linter was turned off: a linter that is off logs nothing. An option that a \
          source file sets leaves no record, and no rule reads it.",
        "That no message was removed: code that runs while Lean elaborates a module can remove a \
          message (standard §7)."]
      configuration := [
        "`warningAsError := false` in a source file cannot hide a warning from `--wfail`, which \
          sets the level that fails the build. Turning a linter off stops it from logging, which \
          the build cannot see.",
        "`@[nolint NAME]` is not read: Batteries' `#lint` command reads it, and it turns off no \
          linter that reports through a build warning."]
      limitations := [
        "Lake sees only a message that Lean logs. Lean drops some messages itself, and code that \
          a claimed module runs can remove one. Such a gap can hide a warning. It does not change \
          what the kernel checks or the axiom sets, as the specification states."]
      residuals := [.invocation]
      checklist := ["DECL-01", "BUILD-01", "DOC-01"]
      linkage := .mk 'N' "one of Regula. The property is Lake's: at v4.35.0 `--wfail` sets the \
        level that fails the build (`Lake/CLI/Main.lean`), and a job that logs a message at that \
        level fails (`Lake/Build/Run.lean`). Regula's checker does not observe the elaboration."
      sources := ["specification/README.md", "specification/RegulaSpecification/Fates.lean"] }
  | .coverage => {
      problem := .mk 'A' " module of the root package that Lake builds is in no library and is not \
        the root of an executable, or it is in more than one library, or a claimed module imports \
        a module of an excluded target."
      trigger := [
        "The loader takes the modules of each target from Lake (`LeanLib.getModuleArray`, and the \
          root of each executable). It adds each module of the root package that their imports \
          reach. A module of the root package is one whose `.olean` file lies below the root \
          package's build directory.",
        "`Regula.Closed.Input.coverageFindings` reports a module that is in no library and is \
          the root of no executable, a module that is in more than one library, and a claimed \
          module that imports a module of an excluded target."]
      rationaleDetail := []
      proofShape := [
        "The removed import must not have supplied evidence the claim still relies on."]
      established := [
        "Each module of the root package that Lake builds is in exactly one library, or in none \
          and the root of an executable, and no claimed module imports a module of an excluded \
          target."]
      notEstablished := [
        "That the chosen library boundaries are the ones the project intends to claim; that is \
          reviewed with the manifest rationale."]
      configuration := [
        "An exclusion in the manifest never permits a claimed module to import the excluded \
          one."]
      limitations := [
        "That Lake's load gives each module that it builds for the root package, the modules that \
          only an import adds included, is an assumption about Lake's interface, as the \
          specification states.",
        "A module that the globs of a library leave out, but that a claimed module imports, is in \
          no library. Add it to the globs of a library, for example with `.andSubmodules`."]
      residuals := [.invocation]
      checklist :=
          ["DECL-02", "DECL-03", "SCOPE-05", "DECL-01", "DECL-04", "BUILD-01",
              "BUILD-03", "BUILD-04"]
      linkage := keptLinkage "Regula.Closed.Input.coverageFindings" "Violates2004"
        "Project.lean"
      sources := ["lean/Regula/Rules.lean", "lean/Regula/Load.lean",
        "specification/RegulaSpecification/Project.lean"] }
  | .admission => {
      problem := .mk 'A' " constant of a claimed module was not checked again by Lean's kernel from \
        an export of the build. Without that check, code that runs while Lean elaborates a module \
        could add a constant that the kernel did not check."
      trigger := [
        "Regula's checker does not report this rule. The specification hands it to `lake check` \
          of the toolchain. It checks each constant of the modules of the default targets again \
          in Lean's kernel, from an export of the build, in a process that loads no `.olean` file \
          of the project. The project's gate runs it after `lake build --wfail`.",
        "RG2002 requires each claimed target to be a default target, so `lake check` covers each \
          claimed module."]
      rationaleDetail := []
      proofShape := [
        "The replayed declaration must type-check in the kernel with exactly its stated type and \
          value."]
      established := [
        notReported,
        "A pass of `lake check` establishes that Lean's kernel checked each constant in its scope \
          again."]
      notEstablished := [
        "Anything that Regula's rules decide: `lake check` checks constants again, and it decides \
          no profile and no rule of a finding."]
      configuration := [
        "`lake check --paranoid` adds the other kernels. The specification makes it optional."]
      limitations := [
        "On macOS the gate runs `lake check --inadvisably-no-sandbox`, because the sandbox \
          requires Linux. The build and the export then run outside the sandbox, as `lake build` \
          does. The first acceptance step of this repository runs it so on every platform.",
        "`lake check` imports every module of the default targets into one environment, and Lean \
          refuses two imported modules that declare one name. So a project whose default targets \
          declare a name twice, such as the `main` of two programs, fails `lake check`. With \
          RG2002, a project can claim at most one module that declares a top-level `main`, until \
          Lake loads each executable root in an environment of its own. A program that must not \
          be the claimed one can declare its entry in a namespace and be started by a root that \
          no default target holds."]
      residuals := [.invocation]
      checklist :=
          ["DECL-01", "DECL-02", "FOUND-05", "SCOPE-02", "TYPE-01", "THEOREM-01", "THEOREM-03",
              "THEOREM-07", "DECL-03", "DECL-04", "COMP-02", "COMP-04", "BUILD-01", "BUILD-04"]
      linkage := .mk 'N' "one of Regula. The property is that of `lake check` of Lean v4.35.0, as \
        the specification describes it. The first acceptance step of this repository runs it on \
        the copy's build (`RegulaVerification.kernelReplay`)."
      sources := ["specification/README.md", "specification/RegulaSpecification/Fates.lean",
        "lean/RegulaVerification/Driver.lean"] }
  | .communityConfiguration => {
      problem := .mk 'A' " claimed library or executable leaves automatic implicits on, sets an \
        option outside RG2006's allowlist, or changes Lean's process with a plugin, a dynamic \
        library or a different Lean argument."
      trigger := [
        "`Regula.Closed.Input.optionFindings` reads the options that Lake gives each claimed \
          target: its `leanOptions`, and each `-D` argument of its `weakLeanArgs` and `leanArgs`. \
          Each other Lean argument, plugin and dynamic library is an extra.",
        "It reports a claimed target that does not set `autoImplicit` and `relaxedAutoImplicit` to \
          `false`, that sets either to a different value at any position, that sets an option \
          outside the allowlist, or that has an extra.",
        "The allowlist is `Regula.Allowlist.options`, and the rule reads an option by its name \
          alone, as Lake gives it. So `weak.linter.hashCommand` and `linter.hashCommand` are two \
          names, and an option that a value of can stop a default warning is on no allowlist."]
      rationaleDetail := [
        "Standard §7.1 requires the options because they decide which binders a declaration's \
          elaborated type has. A closed allowlist refuses each option that it does not name, so \
          an unknown option is refused too."]
      proofShape := []
      established := [
        "Each claimed target sets `autoImplicit` and `relaxedAutoImplicit` to `false` and to no \
          other value, sets only options of the allowlist, and has no plugin, no dynamic library \
          and no Lean argument other than a `-D` option."]
      notEstablished := [
        "That an option set in a source file is admitted: such an option leaves no record, so the \
          rule does not read it.",
        "That `linter.missingDocs` or Mathlib's standard linters are on: the rule does not \
          require them. That requirement goes to written guidance (standard §6.7).",
        "That the community linters' own checks pass, such as a docstring on each public \
          declaration; their warnings fail `lake build --wfail` (RG2003)."]
      configuration := [
        "The Lake configuration is the input; no manifest field, source option or command-line \
          flag exempts a claimed target.",
        "A new member of the allowlist is a change of Regula, with its reason in \
          `Regula.Allowlist`."]
      limitations := [
        "Options given on `lake`'s own command line are not read; the rule reads what Lake's load \
          of the workspace gives."]
      residuals := [.invocation, .intent]
      checklist := ["DECL-01", "DOC-01"]
      linkage := .mk 'T' "he theorem `RegulaSpecification.rg2006_exact` proves that \
        `Regula.Closed.Input.optionFindings` reports a target exactly when \
        `RegulaSpecification.Violates2006` holds of it, and `rg2006_meets` that the function meets \
        the intent record `rg2006`, at the members of `Regula.Allowlist.options`. The shell's read \
        of Lake's load (`Regula.Load.targets`) is trusted, not proved."
      sources := ["lean/Regula/Rules.lean", "lean/Regula/Load.lean", "lean/RegulaCore/Allowlist.lean",
        "specification/RegulaSpecification/Project.lean",
        "specification/RegulaSpecification/ClosedSubset.lean",
        "website/RegulaStandard/ToolingAndMachineAudit.lean"] }
  | .closedSubset => {
      problem := .mk 'A' " claimed module has entries of an environment extension outside the \
        closed allowlist: it registers code that Lean runs while it elaborates, or a record that \
        this revision of Regula does not recognize."
      trigger := [
        "The loader reads the names of the environment extensions with entries in each part of \
          each module's `.olean` files (`Lean.readModuleDataParts`, `Regula.Load.readModule`). \
          A module that declares constants and records no extension is refused, and the run is \
          INCOMPLETE (RG2001): an empty record is not a clean module.",
        "`Regula.Closed.Input.extensionFindings` reports a claimed module for each name outside \
          `Regula.Allowlist.extensions`, an unknown name included. Names are compared whole, so an \
          extension of another namespace is not the allowlisted one that it resembles."]
      rationaleDetail := [
        "A macro, a `syntax` command, an elaborator, an initializer and a `meta` declaration each \
          leave a named entry, and so does a use of an attribute that a project defines. A module \
          that defines such code is a tool module, in a target that the claim excludes; a claimed \
          module cannot import it (RG2004).",
        "Notation and tactics of a dependency stay usable, because using them leaves no entry of a \
          refused extension. The meta-code of a dependency is trusted."]
      proofShape := []
      established := [
        "No claimed module has entries of an environment extension outside the allowlist, so none \
          registers a macro, syntax, an elaborator, an initializer, a `meta` declaration or an \
          attribute that the allowlist does not name."]
      notEstablished := [
        "That no claimed module runs code: `#eval`, `run_cmd`, `run_elab` and `run_meta` leave no \
          record, so the rule cannot see them. If such code changes constants, `lake check` and the \
          axiom sets find it. If it removes messages, `--wfail` does not see them. If it changes \
          entries of an admitted extension, such as compiled code, a claim of execution can be \
          false.",
        "That the meta-code of a dependency is honest: it is trusted."]
      configuration := [
        "The record in the build is the input; no manifest field, source option or command-line \
          flag exempts a claimed module.",
        "A new member of the allowlist is a change of Regula, with its reason in \
          `Regula.Allowlist`."]
      limitations := [
        "The allowlist holds the names observed on Regula's build, on a Mathlib project and on \
          Mathlib at the pinned toolchain, each read for what it registers. A declarative \
          attribute that none of them uses is refused until the list names it."]
      residuals := [.invocation, .intent]
      checklist := ["DECL-01", "DECL-04"]
      linkage := .mk 'T' "he theorem `RegulaSpecification.rg2007_exact` proves that \
        `Regula.Closed.Input.extensionFindings` reports a module exactly when \
        `RegulaSpecification.Violates2007` holds of it, `rg2007_meets` that the function meets the \
        intent record `rg2007`, and `allowlist_closed` that `Regula.Allowlist.extensions` admits \
        none of `metaExtensions`. The loader's read of the `.olean` files through \
        `Lean.readModuleDataParts` is trusted, not proved."
      sources := ["lean/Regula/Rules.lean", "lean/Regula/Load.lean", "lean/RegulaCore/Allowlist.lean",
        "specification/RegulaSpecification/Project.lean",
        "specification/RegulaSpecification/ClosedSubset.lean",
        "website/RegulaStandard/ToolingAndMachineAudit.lean"] }
  | .executionUnresolved => {
      problem := .mk 'T' "he execution closure of a claimed executable runs a name that is no \
        constant of the input, or a constant on a cycle of departures, which runs no definition. \
        An account of execution would then leave out a path."
      trigger := [
        "For the `main` of each claimed executable, `Regula.Closed.Input.rg3001` \
          follows the constants that the build's compiled code runs, from the code of `main`. \
          The loader reads that code with `Lean.IR.findEnvDecl` (`Regula.Load.codeOf`). It counts \
          the code of each auxiliary definition that the compiler adds as code of the constant \
          that it serves. A constant of the closure whose code it cannot read makes the run \
          INCOMPLETE.",
        "It reports a name in that closure that is no constant of the input, and a constant on a \
          cycle of departures. A departure is a point where compiled code runs a constant in \
          place of the constant that the kernel value has: a runtime replacement, a global \
          `@[csimp]` rewrite or a recursion helper. Under a checked claim the input also records \
          on `main` each such departure outside the toolchain whose reference the closure of `main` \
          reaches, whatever survives in compiled code (RG3002).",
        "It reports a claimed executable whose environment loads its root module and holds no \
          `main`. The `main` is the one that Lake links: it can be declared in a module that the \
          root imports.",
        "The rule applies in the `report` and `checked` execution modes."]
      rationaleDetail := []
      proofShape := []
      established := [
        "Each name that the compiled code of a claimed executable's `main` runs, through the code \
          of each constant that it reaches, is a constant of the input, and none is on a cycle of \
          departures."]
      notEstablished := [
        "That the executable runs the code that the build records: that is an assumption, as the \
          specification states.",
        "That the closure is the program's call graph at run time: code that the program selects \
          by name at run time, such as with `evalConst`, is data to it."]
      configuration := [
        "No execution mode waives this rule."]
      limitations := [
        "The loader's reading of compiled code is trusted, not proved: it is what \
          `Lean.IR.findEnvDecl` and `Lean.IR.collectUsedDecls` give at the pinned toolchain.",
        "The closure starts at `main`. An `initialize` action that the code of `main` does not \
          reach is outside it."]
      residuals := [.invocation, .invariant, .intent]
      checklist := ["COMP-03", "SCOPE-05", "SCOPE-03", "THEOREM-05", "BUILD-01", "BUILD-03"]
      linkage := keptLinkage "Regula.Closed.Input.rg3001" "Violates3001"
        "Execution.lean" ++ " The reading of compiled code (`Regula.Load.codeOf`) is trusted."
      sources := ["lean/Regula/Rules.lean", "lean/Regula/Load.lean",
        "specification/RegulaSpecification/Execution.lean"] }
  | .executionBoundary => {
      problem := .mk 'O' "n a surface claiming `\"execution\": \"checked\"`, a boundary that the \
        execution closure reaches has no correspondence: a departure outside the toolchain that \
        no admitted theorem proves, or code outside the toolchain that no theorem can bind, such \
        as an `extern` constant."
      trigger := [
        "For the `main` of each executable claimed with `\"execution\": \"checked\"`, \
          `Regula.Closed.Input.rg3002` reads each constant of the execution closure \
          (RG3001).",
        "It reports a constant outside the toolchain whose code no theorem can bind: an `extern` \
          constant, a partial constant that is not a recursion helper, or a value that \
          `initialize` sets.",
        "It reports a departure that no module of the toolchain makes and that has no \
          correspondence. A correspondence is a theorem `@f = @g`, with `f` the constant of the \
          kernel value and `g` the constant that runs, at every instantiation of the two: their \
          universe arguments are equal, and are distinct universe parameters. It counts when the \
          theorem is not unsafe or partial and the claim's profile admits each of its axioms. A \
          `@[csimp]` lemma is such a theorem for the departure that it makes.",
        "For a recursion helper `f._unsafe_rec`, the correspondence is the recursion equation of \
          `f`: a theorem whose type is that of `f.eq_def`, such as \
          `theorem f_rec : type_of% @f.eq_def := @f.eq_def`. The kernel refuses a safe theorem \
          that mentions the helper, so `@f = @f._unsafe_rec` cannot be stated. A specialized or \
          narrowed equation does not count.",
        "The compiler can inline, specialize or erase a call, so the compiled code need not show a \
          departure. So each `@[implemented_by]` or `@[csimp]` replacement that a module outside \
          the toolchain registers, and each recursion helper of a constant outside the toolchain, \
          is a boundary of `main` when the closure of `main` through the constants each constant \
          mentions, the compiled code runs or a departure runs reaches its reference."]
      rationaleDetail := []
      proofShape := [
        "`@f = @g` for the constant `f` of the kernel value and the constant `g` that runs, closed, \
          with the same distinct universe parameters on both sides, and with axioms that the \
          claim's profile admits.",
        "`theorem f_rec : type_of% @f.eq_def := @f.eq_def` for a recursion helper of `f`."]
      established := [
        "Under a checked claim, each departure outside the toolchain that the closure reaches has \
          a correspondence that the profile admits, each replacement and recursion helper outside \
          the toolchain whose reference `main` reaches has one whether or not its target survives \
          in compiled code, and the closure reaches no code outside the toolchain that no theorem \
          can bind."]
      notEstablished := [
        "Correctness of the toolchain's own replacements, `extern` code and native primitives, or \
          of the compiler. A Lean equality does not prove external machine code.",
        "Anything about code that the program selects at run time, such as a constant it \
          evaluates by name, a dynamic library it loads or a process it starts.",
        "That the compiled code of a recursive definition computes what its base computes: the \
          recursion equation states that the base satisfies the body of the helper, and the step \
          from there to the compiled code rests on the compiler, which is trusted.",
        "A rewrite by a lemma that `attribute [local csimp]` registers: the build holds no entry \
          of it, so it is no departure of the input. Its lemma is a constant of its module, which \
          RG1005 and RG1006 read when that module is claimed."]
      configuration := [
        "`execution` in the surface of `foundation_manifest.json` (`report` or `checked`) selects \
          the mode. `report` mode does not apply this rule; it is not a fix for a checked claim."]
      limitations := [
        "An unsafe theorem is no evidence, so a correspondence counts only from a theorem that is \
          not unsafe or partial.",
        "A reference that only a proof mentions also asks for a correspondence: a false refusal \
          under a checked claim, which a theorem discharges.",
        "A correspondence must be in a module that the environment of the executable loads, so its \
          root imports it.",
        "That the executable runs the code that the build records is an assumption, as for \
          RG3001."]
      residuals := [.intent, .invariant, .invocation]
      checklist :=
          ["COMP-03", "COMP-04", "SCOPE-03", "SCOPE-05", "THEOREM-05", "BUILD-01", "BUILD-03"]
      linkage := keptLinkage "Regula.Closed.Input.rg3002" "Violates3002"
        "Execution.lean"
      sources := ["lean/Regula/Rules.lean", "lean/Regula/Load.lean",
        "specification/RegulaSpecification/Execution.lean",
        "website/RegulaStandard/ToolingAndMachineAudit.lean"] }
  | .fenceStructure => {
      problem := .mk 'A' " Markdown file in the documentation has a malformed Lean fence \
        classification: an orphan, misplaced, duplicated or misspelled marker, an invalid \
        expected-error pattern, or an unclosed fence. Or it has a line that can show Lean code \
        at a place that no check reads."
      trigger := [
        retiredTrigger,
        "The intent: a marker of a documentation fence is in its place, each fence is closed, \
          and Lean code is only in a `lean` fence."]
      rationaleDetail := [retiredRationale]
      proofShape := []
      established := [notReported]
      notEstablished := [
        "That the documentation meets the intent above; that is review (R-DOC)."]
      configuration := []
      limitations := [
        "The `lean` blocks of Regula's own standard are still elaborated when the rule-reference \
          site builds. That build checks no project's documentation."]
      residuals := [.doc]
      checklist := ["DOC-03"]
      linkage := retiredLinkage
      sources := ["specification/README.md", "specification/RegulaSpecification/Fates.lean"] }
  | .positiveExample => {
      problem := .mk 'A' " positive Lean fence in the documentation does not elaborate verbatim and \
        warning-free, or it does and then fails the declaration and axiom rules."
      trigger := [
        retiredTrigger,
        "The intent: a `lean` fence of the documentation elaborates with no warning, and passes \
          the declaration and axiom rules."]
      rationaleDetail := [retiredRationale]
      proofShape := [
        "The fence proves exactly the claim the surrounding prose states."]
      established := [notReported]
      notEstablished := [
        "That each `lean` fence elaborates, and that the prose describes it faithfully (R-DOC, \
          R-INTENT)."]
      configuration := []
      limitations := [
        "The `lean` blocks of Regula's own standard are still elaborated when the rule-reference \
          site builds. That build checks no project's documentation."]
      residuals := [.intent, .doc]
      checklist := ["DOC-04"]
      linkage := retiredLinkage
      sources := ["specification/README.md", "specification/RegulaSpecification/Fates.lean"] }
  | .negativeExample => {
      problem := .mk 'A' " fence marked `lean-fail` does not fail as specified: it elaborates \
        successfully, or it fails for a different reason."
      trigger := [
        retiredTrigger,
        "The intent: a `lean-fail` fence fails with one error that matches its pattern."]
      rationaleDetail := [retiredRationale]
      proofShape := [
        "The pattern is part of the documented claim and is reviewed with the prose."]
      established := [notReported]
      notEstablished := [
        "That each `lean-fail` fence fails for the reason the prose explains; that is review \
          (R-DOC)."]
      configuration := []
      limitations := [
        "No check of a project's documentation runs the fences."]
      residuals := [.doc]
      checklist := ["DOC-05"]
      linkage := retiredLinkage
      sources := ["specification/README.md", "specification/RegulaSpecification/Fates.lean"] }
  | .trustedExample => {
      problem := .mk 'A' " fence marked `lean-trusted-compiler` does not elaborate warning-free \
        with a compiler-trusting declaration: it contains no native proof."
      trigger := [
        retiredTrigger,
        "The intent: a `lean-trusted-compiler` fence elaborates with no warning and contains a \
          compiler-trusting declaration."]
      rationaleDetail := [retiredRationale]
      proofShape := []
      established := [notReported]
      notEstablished := [
        "That a teaching fence shows what its prose says; that is review (R-DOC)."]
      configuration := []
      limitations := [
        "No check of a project's documentation runs the fences."]
      residuals := [.doc]
      checklist := ["DOC-05"]
      linkage := retiredLinkage
      sources := ["specification/README.md", "specification/RegulaSpecification/Fates.lean"] }
  | .moduleDocumentation => {
      problem := .mk 'A' " module in a claimed surface has no module docstring (`/-! … -/` or \
        Verso module documentation), has one that is not the first command after its imports, or \
        repeats an import with the same modifiers."
      trigger := [
        retiredTrigger,
        "The intent: a claimed module has a module docstring as its first command after the \
          imports, and it imports no module two times."]
      rationaleDetail := [retiredRationale]
      proofShape := []
      established := [notReported]
      notEstablished := [
        "That each claimed module has module documentation that describes it faithfully (R-DOC). \
          Presence and position say nothing about content."]
      configuration := []
      limitations := [
        "No check reads the position of a module docstring or a repeated import."]
      residuals := [.doc]
      checklist := ["DOC-01", "DECL-01"]
      linkage := retiredLinkage
      sources := ["specification/README.md", "specification/RegulaSpecification/Fates.lean",
        "website/RegulaStandard/DocumentationStandards.lean"] }
  | .materialDocumentation => {
      problem := .mk 'A' " public declaration that states a material normative claim has no \
        docstring."
      trigger := [
        retiredTrigger,
        "The intent: each public declaration that states a material claim has a docstring."]
      rationaleDetail := [retiredRationale]
      proofShape := [
        "The docstring describes the elaborated statement faithfully."]
      established := [notReported]
      notEstablished := [
        "That each material declaration has a faithful and adequate docstring (R-DOC)."]
      configuration := [
        "No registration selects a material declaration: review decides which public declarations \
          state a material claim."]
      limitations := [
        "Lean's `linter.missingDocs` reports a public declaration without a docstring where a \
          target turns it on, and `lake build --wfail` then fails (RG2003)."]
      residuals := [.doc]
      checklist := ["DOC-01"]
      linkage := retiredLinkage
      sources := ["specification/README.md",
        "specification/RegulaSpecification/Fates.lean"] }
  | .materialIntent => {
      problem := .mk 'A' " public material declaration has a docstring without a \
        nonempty labelled Intent section."
      trigger := [
        retiredTrigger,
        "The intent: the docstring of each public material declaration has a section `# Intent` \
          that is not empty."]
      rationaleDetail := [retiredRationale]
      proofShape := [
        "The Intent section states the requirement the declaration must meet; review compares \
          the two."]
      established := [notReported]
      notEstablished := [
        "That the intent states what the requirement owner needs, or that the declaration meets it \
          (R-INTENT, R-DOC)."]
      configuration := [
        "No registration selects a material declaration: review decides which public declarations \
          state a material claim."]
      limitations := [
        "No check reads the Intent section of a docstring."]
      residuals := [.intent, .doc]
      checklist := ["DOC-02"]
      linkage := retiredLinkage
      sources := ["specification/README.md",
        "specification/RegulaSpecification/Fates.lean"] }

/-- Every rule's explanation has all required sections. The problem and the linkage are nonempty
by their type, however long they are (`Guide.wellFormed_iff_listsNonempty`); that every required
list section is nonempty is checked exhaustively over the closed registry by kernel evaluation of
the lists' shape alone, which reduces no string, so the proof's cost does not depend on the length
of any text. -/
theorem guide_wellFormed : ∀ id, (guide id).WellFormed := fun id =>
  (Guide.wellFormed_iff_listsNonempty _).mpr (by cases id <;> decide)

end Regula.Site
