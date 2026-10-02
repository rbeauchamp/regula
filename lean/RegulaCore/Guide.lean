import RegulaCore.Account

/-! # Rule explanations for the rule-reference site

`guide` is the explanatory prose for every rule, as one exhaustive definition over the closed
`RuleId`: adding a rule without its explanation is a compile error, and the site generator
renders a page from `guide id` together with the registry descriptor `descriptor id` and
the checked example evidence of that rule. Nothing here is a second rule vocabulary: rule
identity, title, category, clauses, modes and routes come from `descriptor`, and so do the
agent-facing requirement, short rationale, remedy, rewrites and example pair that every
diagnostic and the `regula` command also print. This module holds only the longer site and
`regula explain` prose.

## Main declarations

- `Guide`: the required sections of a rule explanation.
- `guide`: the explanation of each registered rule.
- `Guide.WellFormed`, `guide_wellFormed`: every required field of every rule is a nonempty
  string or list, and each rule names at least one residual obligation, one source and its
  proved linkage. The proof shape and configuration may be empty, and the page then omits them.
  Content adequacy is review.

## Boundaries

The prose is original Lean-specific explanation written against the standard
(`website/RegulaStandard`) and the
checker sources it names. Its fidelity to the standard and to the detectors is semantic
review (R-DOC, R-INTENT); nonemptiness is the only mechanical property checked here. Text
uses Verso inline markup. A link target `@repo/PATH` denotes `PATH` in this repository at the
revision the site is built from; the generator requires each such file to exist.
Presentation structure follows Microsoft's CA1416 page as one illustrative reference
(cause, rationale, fix, configuration, examples); no content is copied from it.
-/

namespace Regula.Site

open Regula.Checker.Account (Residual)

/-- The explanation sections of one rule page, in page order. `residuals` are the review
obligations a result of this rule never discharges; `checklist` names the module 8 checklist rows
the rule contributes to; `sources` are repository paths of its detector, policy and proof
modules. -/
structure Guide where
  /-- What goes wrong in a violating project: the page's lead paragraph and the *Problem*
  section of `regula explain`. -/
  problem : String
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
  linkage : String

/-- Every required section has content and the page names its open obligations, sources and
proved linkage. -/
def Guide.WellFormed (g : Guide) : Prop :=
  g.problem ≠ "" ∧ g.trigger ≠ [] ∧ g.established ≠ [] ∧ g.notEstablished ≠ [] ∧
  g.limitations ≠ [] ∧ g.residuals ≠ [] ∧ g.checklist ≠ [] ∧ g.sources ≠ [] ∧ g.linkage ≠ ""

instance (g : Guide) : Decidable g.WellFormed := by
  unfold Guide.WellFormed; infer_instance

/-- Shared statement: the proved linkage of the rules that the declaration decision decides. -/
private def declarationLinkage : String :=
  "The shared declaration decision `RegulaPolicy.declarationFailure` (its first failed \
    requirement, `declarationFailure_ordered`) is mapped to a rule by the injective \
    `Regula.ruleForFailure`. Project, file and documentation audits run it through \
    `Regula.Checker.Policy.checked_memberRule` (`ruleForMember_eq`); the editor runs \
    `Regula.Linter.checked_editorDecision`. For the same member and request, the editor passes \
    exactly when the project decision selects no rule \
    (`Regula.Checker.Policy.editor_decision_none_iff`), a rule it renders is the project \
    decision's rule (`editor_decision_rule`), and a pending result withholds a project rule whose \
    failure needs generated-role evidence (`editor_decision_pending`). The editor's request \
    domain is the project's without teaching (`editor_request_sound`, \
    `editor_request_complete`). The observed declaration fields and generated-role evidence are \
    hypotheses of these theorems."

/-- Shared statement: foundation labels. -/
private def foundationTable : String :=
  "The three logical labels are Kernel-only (no axioms), Choice-Free (a subset of `propext` and \
    `Quot.sound`) and Standard-Logical (additionally `Classical.choice`). A surface's `claim` in \
    `foundation_manifest.json` is the upper bound; each declaration is labeled from its own exact \
    axiom set."

/-- The explanation of each rule. -/
def guide : RuleId → Guide
  | .projectAxiom => {
      problem := "A declaration owned by a claimed module is a logical `axiom`. Lean accepts an \
        axiom without evidence, so every theorem that uses it is only conditional on an assumption \
        that no proof discharges."
      trigger := [
        "The checker inspects every constant attributed to an owned module in the completed Lean \
          environment. A `ConstantInfo.axiomInfo` there is rejected with applicability \
          `project-axiom`.",
        "The rule applies whether or not any other declaration uses the axiom, and to private, \
          protected, internal-looking and generated names alike. A name or namespace never exempts \
          it."]
      rationaleDetail := [
        "Lean 4 has no `constant` command; an `opaque` definition with a body is kernel-checked \
          and is classified separately, not as an axiom."]
      proofShape := [
        "A conditional result must carry the assumption in its type, for example `∀ (h : P), Q`, \
          so the exact theorem statement shows what it depends on. Its transitive axiom set must \
          then fit the surface's foundation profile."]
      established := [
        "No owned constant of the checked modules is a logical axiom (the complete inventory \
          itself is RG2004).",
        "The rule is evaluated from Lean's elaborated environment after checked admission, not \
          from source text."]
      notEstablished := [
        "That the hypotheses replacing an axiom are satisfiable or appropriate: that is the \
          claim's intent and non-vacuity review.",
        "Anything about axioms of imported, unowned dependencies; those are reported through the \
          transitive axiom sets of RG1003 and RG1005."]
      configuration := [
        "Authenticated native-proof axioms generated by `native_decide`, `decide +native`, \
          `bv_decide`, `bv_decide?` or `bv_check` are not project axioms: they are classified as \
          compiler-trusting and rejected by RG1004 instead."]
      limitations := [
        "The editor linter reports this rule for completed declarations of the current file \
          (`editorSnapshot`); a clean editor buffer is not a project result.",
        "A metaprogram that adds declarations still produces owned constants; they are inspected \
          like authored ones."]
      residuals := [.intent, .nonvacuity]
      checklist := ["FOUND-01", "TYPE-04", "THEOREM-09", "THEOREM-01", "DECL-03", "BUILD-01"]
      linkage := declarationLinkage
      sources :=
          ["lean/RegulaCore/Policy.lean", "lean/RegulaPolicy/Decision.lean",
              "lean/Regula/Findings.lean", "website/RegulaStandard/LogicProofPatterns.lean"] }
  | .proofHole => {
      problem := "The declaration depends on `sorryAx`: a `sorry`, an `admit`, an unfinished \
        tactic proof, or an imported declaration with such a hole occurs in its transitive axiom \
        set. The proposition is not proved."
      trigger := [
        "The checker computes the exact transitive axiom set of every owned declaration with \
          Lean's `collectAxioms`. If `sorryAx` belongs to it, the declaration is rejected with \
          applicability `hole`.",
        "Theorems, proof-valued definitions and instances, and data definitions are all inspected; \
          alternate syntax (`admit`, a tactic `sorry`) is caught because the kernel term contains \
          `sorryAx`.",
        "Lean itself warns `declaration uses 'sorry'` by default, and an elaboration error \
          recovered as `sorry` is an error. In `lake lint`, `axiomGate` and the build-lint \
          `policy` target that warning or error stops the audit at the warning-free build check \
          before policy inspection, so an owned `sorry` in a claimed module is reported as RG2003 \
          and the result is INCOMPLETE (`lake lint` exit 3); a single-file `axiomGate --file F \
          --claim P` audit reports it as a RG2003 violation. This rule's own finding appears in \
          the editor, in a file audit without `--claim` (which does not reject warnings), and in \
          project and claimed-file audits when no warning was emitted (for example a hole \
          inherited from an imported declaration, or `set_option warn.sorry false`, which does not \
          waive the rule)."]
      rationaleDetail := []
      proofShape := [
        "The completed declaration keeps the same statement. Weakening the proposition until it is \
          easy to prove changes the requirement and is a semantic review failure, even though this \
          rule then passes."]
      established := [
        "No owned declaration of the checked scope has `sorryAx` in its exact transitive axiom \
          set."]
      notEstablished := [
        "That the completed proof proves the intended statement; the proposition itself is \
          reviewed against its intent.",
        "Lean's own warning for `sorry` is a separate compiler diagnostic (RG2003); this rule does \
          not depend on it, and disabling that warning does not waive this rule."]
      configuration := []
      limitations := [
        "In the editor the rule is reported for completed declarations of the current snapshot. A \
          cancelled collection reports nothing for that declaration; a failed one is reported as \
          RG2005 (incomplete), never as an invented RG1002.",
        "The checked example comes from a diagnostic single-file inspection that keeps Lean's \
          `sorry` warning as related evidence and continues to policy inspection; the ordinary \
          project commands stop earlier with RG2003, as described above."]
      residuals := [.qualify, .intent]
      checklist := ["FOUND-02", "THEOREM-06", "TYPE-04", "THEOREM-01", "THEOREM-09", "BUILD-01"]
      linkage := declarationLinkage
      sources :=
          ["lean/RegulaCore/Policy.lean", "lean/RegulaPolicy/Decision.lean",
              "lean/Regula/Findings.lean"] }
  | .unknownAxiom => {
      problem := "A declaration's exact transitive axiom set contains an axiom outside Lean's \
        standard logical foundation (`propext`, `Quot.sound`, `Classical.choice`) that is neither \
        `sorryAx` nor a compiler-trusting axiom (the `Lean.trustCompiler`, `Lean.ofReduceBool` \
        and `Lean.ofReduceNat` family when the selected compiler declares it, or an authenticated native-proof axiom of \
        `native_decide`, `decide +native`, `bv_decide`, `bv_decide?` or `bv_check`)."
      trigger := [
        "Each axiom in the transitive set is classified. One that is not a standard logical axiom, \
          `sorryAx` (RG1002) or a compiler-trusting axiom (RG1004) is unknown, and the declaration \
          is rejected with applicability `unknown-axiom`.",
        "Imported axioms are not exempt: an owned theorem that uses a dependency's axiom is \
          rejected even though the axiom is declared elsewhere."]
      rationaleDetail := [
        foundationTable]
      proofShape := [
        "After the fix, the exact transitive axiom set is a subset of `propext`, `Quot.sound` and \
          `Classical.choice` and fits the surface claim (RG1005)."]
      established := [
        "Every axiom in the transitive set of each owned declaration is either a standard logical \
          axiom or rejected by a more specific rule."]
      notEstablished := [
        "Anything about the unowned dependency beyond its axioms; imported declarations are a \
          declared trust boundary, identified by the exact dependency state (RG2001)."]
      configuration := []
      limitations := [
        "Classification uses exact constant names and authenticated compiler evidence, not name \
          patterns; a lookalike name gets no special treatment."]
      residuals := [.qualify]
      checklist := ["FOUND-03", "TYPE-04", "THEOREM-01", "THEOREM-09", "BUILD-01"]
      linkage := declarationLinkage
      sources :=
          ["lean/RegulaCore/Policy.lean", "lean/RegulaPolicy/Foundation.lean",
              "lean/RegulaPolicy/Decision.lean"] }
  | .compilerTrusting => {
      problem := "A declaration on a positive surface depends on a compiler-trusting axiom: a \
        native-proof axiom generated by `native_decide`, `decide +native`, `bv_decide`, \
        `bv_decide?` or `bv_check`, or a member of the `Lean.trustCompiler`, `Lean.ofReduceBool` \
        and `Lean.ofReduceNat` family declared by the selected compiler. Its proof trusts compiled code and the Lean compiler, not the \
        kernel."
      trigger := [
        "`native_decide` and `decide +native` evaluate a decision procedure with compiled code, \
          and `bv_decide`, `bv_decide?` and `bv_check` check a SAT certificate with compiled \
          code; each adds an axiom asserting the result through `Lean.Meta.nativeEqTrue`, named \
          after the tactic name it passes (`._native.native_decide.ax_…`, \
          `._native.decide.ax_…`, `._native.bv_decide.ax_…`), and private to the module when a \
          `module` file elaborates the proof without exporting. The checker authenticates such an \
          axiom from three observations: its name is one the scheme generates under the name of \
          a declaration of its module; it asserts `e = true` with `e` in the tactic's exact \
          shape, and an independent native replay of `e` returns `true`; and a fresh \
          re-elaboration shows that the command introducing that declaration adds an axiom of \
          the same origin and statement, and that no `axiom` declaration occurs in that \
          command's syntax or macro expansions. The axiom and every declaration depending on it \
          are then classified compiler-trusting and rejected with applicability \
          `compiler-trusting`. The legacy `Lean.trustCompiler`, `Lean.ofReduceBool` \
          and `Lean.ofReduceNat` names are compiler-trusting only when an isolated, origin-checked \
          Core observation confirms the complete family and matches the compiled policy. If the \
          compiler has removed them, project or dependency axioms with those names receive no \
          compiler exception.",
        "Final environment metadata cannot authorize a generated native-proof axiom; fresh \
          re-elaboration of the exact source establishes it. An unauthenticated axiom that only \
          looks native is not compiler-trusting."]
      rationaleDetail := []
      proofShape := [
        "The replacement proof proves the same proposition. Kernel reduction (`decide`, `rfl`) is \
          permitted, subject to the surface's foundation profile."]
      established := [
        "No positive declaration depends on a compiler-trusting axiom: an authenticated \
          native-proof axiom or a member of the legacy compiler-trust family declared by that compiler."]
      notEstablished := [
        "Performance of the kernel replacement proof; cost claims are separate (R-COST)."]
      configuration := [
        "Authenticated native proofs are reported separately in documentation teaching mode \
          (`lean-trusted-compiler` fences) and remain excluded from conforming positives."]
      limitations := [
        "The editor may defer authentication and report a pending result; the project command \
          completes it.",
        "An unauthenticated axiom that merely looks native is not compiler-trusting; it is \
          rejected as an unknown axiom (RG1003) or project axiom (RG1001).",
        "Authentication does not depend on the surrounding syntax: a native tactic anywhere in a \
          declaration's elaboration is covered, in a tactic sequence or combinator, a nested \
          `by` block, a `grind =>` or `sym =>` block, a `where` clause, a declaration with \
          parameters (`+revert`), attributes or a namespaced, public or private name, under \
          `set_option … in`, in ordinary and `module` files.",
        "An axiom with a native name and a natively true statement stays a project axiom \
          (RG1001) when the source declares it, as an `axiom` command written directly or \
          produced by a macro, even one whose elaboration fails after adding it, or when a \
          different command adds it than the one introducing the declaration its name belongs \
          to. The declaration check reads syntax, quoted syntax included, and matches no names, \
          so a command that both contains `axiom` syntax and uses a native tactic has no native \
          axiom authenticated; its native axioms fail closed as RG1001 and RG1003. A custom \
          tactic, elaborator or metaprogram that adds such an axiom without declaring it is \
          classified compiler-trusting: the axiom asserts only what native evaluation confirmed.",
        "The build is matched to the fresh re-elaboration by generated origin and asserted \
          statement. When two commands add axioms of the same origin and statement, for \
          example an authored spoof beside the genuine proof, neither is authenticated and both \
          fail closed as RG1001 and RG1003."]
      residuals := [.qualify, .cost]
      checklist :=
          ["FOUND-05", "FOUND-03", "THEOREM-10", "THEOREM-01", "THEOREM-06", "DECL-03", "COMP-01",
              "BUILD-01"]
      linkage := declarationLinkage ++ " The compiler-trusting and native role sets come from \
        `RegulaPolicy.authorize`. `RegulaPolicy.authorizedNativeAxioms_iff` characterizes the \
        authenticated native roles, and `native_generated` shows that each is a name Lean's \
        `nativeEqTrue` scheme generates for `native_decide`, `decide +native` or `bv_decide` \
        under a prefix related to an inventory declaration by `GeneratedPrefix`, and \
        `native_provenance` that its statement was natively replayed and that a command of its \
        module's fresh transcript adds an axiom of the same origin and statement while its \
        recorded syntax declares no axiom. `generatedPrefix_iff` shows that, for a declaration \
        name without macro scopes, these are exactly the names the generator gives that \
        declaration in its own module in either privacy mode. The execution probe classifies by \
        `RegulaPolicy.compilerTrustingAxiomName`, which `compilerTrustingAxiomName_iff` \
        characterizes as exactly those generated names and the enabled legacy compiler axioms. Both \
        characterizations assume the runtime string append `RuntimeStringAppend`."
      sources :=
          ["lean/RegulaPolicy/Decision.lean", "lean/RegulaPolicy/NativeAxiom.lean",
              "lean/Regula/Checker/Frontend.lean", "lean/RegulaCore/Policy.lean"] }
  | .profileExceeded => {
      problem := "A declaration's exact transitive axiom set is admissible, but its least \
        foundation label is stronger than the claim of the surface it belongs to."
      trigger := [
        "Each declaration receives the least label containing its exact axiom set. If that label \
          exceeds the surface maximum, the declaration is rejected with applicability \
          `label-exceeds-claim`.",
        foundationTable]
      rationaleDetail := []
      proofShape := [
        "The replacement proves the same proposition. Classical, erased proofs are permitted when \
          the surface claims Standard-Logical; executable behavior is a separate account (RG1007, \
          RG3001, RG3002)."]
      established := [
        "Every declaration's exact axiom set is within the selected surface maximum."]
      notEstablished := [
        "Which label a declaration should have: the claim is a project decision, reviewed with its \
          rationale."]
      configuration := [
        "The surface maximum is the `claim` of its entry in `foundation_manifest.json`; `axiomGate \
          --file F --claim PROFILE` audits one file under an explicit profile. In the editor, \
          `regula.localFoundation` selects local feedback only."]
      limitations := [
        "The label is computed from the exact transitive set; a proof that merely could avoid an \
          axiom still carries it until rewritten."]
      residuals := [.qualify]
      checklist := ["FOUND-03", "FOUND-04", "BUILD-02", "THEOREM-01", "THEOREM-10", "BUILD-01"]
      linkage := declarationLinkage
      sources :=
          ["lean/RegulaPolicy/Foundation.lean", "lean/RegulaCore/Policy.lean",
              "website/RegulaStandard/MathematicalFoundations.lean"] }
  | .escapeHatch => {
      problem := "An owned declaration is marked `unsafe` or `partial` and is not the \
        code-generation helper of a safe recursive definition that Lean's own recursion compiler \
        regenerates from the helper, up to compilation erasure, and whose recursion equation for \
        that definition Lean's kernel checks."
      trigger := [
        "Authored `unsafe` and `partial` declarations are escape hatches: an unsafe declaration is \
          checked only in Lean's unsafe mode, cannot be used by safe declarations or proofs and is \
          not replayed as logical evidence, and a partial definition has no termination proof. \
          They are rejected with applicability `escape-hatch`.",
        "The only exception is the range-less partial helper Lean generates for a safe, \
          termination-checked recursive `def` (structural or well-founded recursion, a `where` \
          or `mutual` definition, a recursive `abbrev`, or a derived `DecidableEq`, `BEq`, \
          `Hashable` or `Repr` function on a recursive inductive that is neither nested nor \
          mutual). It is admitted by exact match (standard §7.4): rerunning Lean's recursion \
          compiler on the helper's recursion, with only the toolchain's own preprocessing rules \
          and the checker's built-in syntax handlers, regenerates the observed base, up to \
          compilation erasure, the base's axioms are within Standard-Logical, and Lean's kernel \
          checks the recursion equation of each helper of the group: with the helper's value \
          `fun xs => body` and every helper of the group replaced by its base `f`, the theorem \
          `∀ xs, f xs = body`, in the inspected environment, by a proof that uses no axiom \
          outside Standard-Logical. The checker builds that statement from the helper's value \
          and gives it to the kernel itself. A proof to try is taken from a constant named \
          `f.eq_def`, whoever declared it, from the theorem Lean realizes for `f` or for the \
          regenerated definition, or from reflexivity where the result is a proof, with every \
          constant the search adds put back as its value; the kernel checks it against the \
          checker's statement, and nothing else about it is consulted. The regeneration selects \
          what is compared and no longer carries the claim about values: a base that the \
          regeneration reproduces through matcher metadata or \
          through `below` and `brecOn` declarations the audited module wrote is rejected where \
          it does not satisfy the equation. Which code added the helper does not matter, and \
          neither do declaration order, a nested proof shared with \
          an earlier declaration, a proof written as a tactic block or as a term, or whether a \
          `public` definition of a `module` file is exposed: the comparison uses no name of a \
          theorem Lean abstracts from a nested proof. Nor, for the forms standard §7.4 lists, \
          does it matter which definitions were irreducible where the definition was elaborated \
          (`attribute [local irreducible]`, `attribute [irreducible]` afterwards, `unseal`): the \
          regeneration runs a second time with no definition irreducible (each given the status \
          its declaration shows), and the comparison \
          takes a `match` that passes a variable through as the `match` that uses it directly, \
          where Lean's kernel checks that the two are equal for that matcher. Nor does a global \
          reducibility attribute given after the definition (`attribute [reducible]`, \
          `[instance_reducible]`, `[implicit_reducible]`, or `[irreducible]` after one of those) \
          matter when it is given to a function of the helper's own module that is not an \
          `abbrev`, the change is one the search covers (from a status on which Lean's \
          validation admits that attribute, or from `reducible` to irreducible), and the \
          definitions the helper reaches allow at most 63 assignments of an earlier status: \
          where neither regeneration reproduces the base, the checker searches the statuses \
          such an attribute can have replaced, for the definitions of the helper's module that \
          the helper reaches, and an assignment only selects which regeneration runs. The \
          limitations below list the forms outside this. The regeneration and the comparison \
          run with Lean's smart unfolding off, so no declaration named `g._sunfold` is read for \
          the unfolding of `g`.",
        "A `partial def` is an opaque declaration that Lean runs through its generated helper. \
          The finding names the `partial def`, at its source range, not the helper; this includes \
          the `partial def` functions that deriving `BEq`, `Hashable`, `Repr` or `Ord` generates \
          for a nested or mutual inductive (and deriving `Ord` for any recursive one).",
        "A helper of a safe definition that the regeneration does not reproduce, or for whose \
          recursion equation the checker finds no proof the kernel accepts, is reported under \
          the helper's name (see the limitations below); its definition may be correct."]
      rationaleDetail := []
      proofShape := [
        "A total replacement keeps the same domain and result type; if it changes behavior, state \
          and prove the relation to the intended function."]
      established := [
        "No authored unsafe or partial declaration is on the claimed surface. Every admitted \
          generated helper is Lean's compilation of a safe definition: its base, of the same \
          module and type, is what Lean's own recursion compiler regenerates from the helper's \
          recursion, up to compilation erasure, and is kernel-checked with Standard-Logical \
          axioms. Lean's kernel has checked, with Standard-Logical axioms, that the base \
          satisfies the recursion equation of each helper of the group, whatever matcher \
          metadata, `below` and `brecOn` declarations, `_sunfold` declarations or reducibility \
          statuses the audited module wrote. From that equation it is argued, not \
          kernel-checked, that whenever the helper returns, it returns the base's value: by \
          induction on the helper's evaluation, each recursive call that returns having \
          returned the base's value."]
      notEstablished := [
        "That unsafe or partial code elsewhere is logically unsound; the rule concerns evidence, \
          not a claim that such code is wrong.",
        "That the helper terminates whenever the base does. Lean compiles the base from a body \
          its `wf_preprocess` rules rewrote and the helper from the original, and Lean documents \
          that a rewrite can remove a subterm the compiled code still evaluates or delay one \
          under a binder; a toolchain rule can, through a reducible definition that ignores an \
          argument. The helper's termination trusts that preprocessing, as every well-founded \
          definition Lean accepts does.",
        "That the regeneration observation is truthful or that a helper's compiled code matches \
          its value; these rest on the pinned Lean toolchain and on Regula's own unproved \
          regeneration comparison. The claim about values does not rest on the regeneration: \
          it rests on the kernel-checked recursion equation, on the compiled code running the \
          helper's value, and on the argument from the equation to the values, for which there \
          is no theorem.",
        "Termination proofs' adequacy for cost claims."]
      configuration := [
        "`partial_fixpoint` helpers are not covered by the recursive-helper exception."]
      limitations := [
        "A helper is not admitted where the regeneration does not reproduce its base. The \
          regeneration is given the helper's value and its base's termination argument, and it \
          reruns Lean's structural and well-founded compilers in the environment the audit \
          inspects (at the end of the audit), and there again with no definition irreducible, \
          and in both under the reducibility assignments it searches, \
          with Lean's default options and the toolchain's own rules, not with the options, rules \
          and attributes in force where the definition was compiled. The forms known to fall \
          outside are a `partial_fixpoint` definition, a base compiled through a fixpoint \
          combinator other \
          than `WellFounded.fix` and `WellFounded.Nat.fix`, a base whose compilation used a \
          `wf_preprocess` rule registered outside the Lean toolchain, one elaborated with \
          `set_option wf.preprocess false` or with a toolchain rule removed by \
          `attribute [-wf_preprocess]` when a rule so disabled would have rewritten its body, or \
          one that calls a function whose status where the definition was compiled the search \
          does not try, where that changes which parameters Lean finds fixed or which \
          `wf_preprocess` rule of the toolchain applies: a status that holds only where the \
          definition is compiled (`attribute [local reducible]` or a `reducible` function made \
          semireducible afterwards, under `set_option allowUnsafeReducibility true`; \
          `attribute [local instance_reducible]` or `[local implicit_reducible]`), an `abbrev` \
          that is not `reducible` where the definition is compiled, a function of another \
          module whose status changes afterwards, or a change Lean's validation does not admit, \
          such as `reducible` given to an `instance_reducible` function (all under that option). \
          These are limits of this release, which issue #196 keeps open \
          (`Fixtures.Mutations.KnownLimitReducibleWhereCompiled`). Give such a function \
          its reducibility where it is declared. Otherwise a definition for which the only \
          difference is that ordinary (semireducible) definitions are irreducible at one of the \
          two points \
          (`attribute [local irreducible]`, `attribute [irreducible]` after the definition, \
          `unseal`), or that an `abbrev` is irreducible at the end of the audit, is admitted.",
        "A helper whose reached definitions allow more than 63 assignments of an earlier \
          reducibility status is searched over the first 63 single changes only, each giving one \
          definition one earlier status. If none reproduces its base the helper is undecided, \
          neither admitted nor rejected: the checker stops with an error that names it, and the \
          audit is incomplete, not a violation of this rule. A helper no attempt within the bound \
          reproduces may still be what Lean generated, so a violation would assert what the \
          checker has not established, and the helper is not admitted either way. A forged \
          helper over the bound ends the same way. \
          `Fixtures.Mutations.KnownLimitReducibilitySearchBound` shows the outcome for a helper \
          Lean generated. The bound of 63 is a limit of this release, which issue #196 keeps \
          open.",
        "A helper is not admitted where the checker finds no proof of its recursion equation \
          that the kernel accepts. It looks for one only in a constant named `f.eq_def`, which \
          Lean adds with a well-founded definition, in the theorem Lean realizes for a \
          structural definition or for the regenerated one, and in reflexivity for a definition \
          whose type is a proposition. Who declared a candidate is not checked, only that the \
          kernel accepts it as a proof of the checker's statement. A well-founded definition \
          and helper that a metaprogram adds with no theorem of that name are therefore \
          rejected although the helper computes the base \
          (`fixtures_forged_measured_bare` of `Fixtures.Mutations.MeasuredMatchUnsafeRecForge`); \
          such a metaprogram adds `f.eq_def` too, copied from Lean's theorem or proved itself.",
        "Editor feedback may be pending until the project command completes the regeneration."]
      residuals := [.qualify, .cost, .intent]
      checklist := ["COMP-02", "THEOREM-05", "THEOREM-01", "DECL-03", "BUILD-01"]
      linkage := declarationLinkage ++ " `RegulaPolicy.authorizedUnsafeRecHelpers_iff` \
        characterizes the admitted recursion helpers, `authorizedUnsafeRecHelpers_base` gives \
        each a recorded observation (the regeneration together with the kernel-checked \
        recursion equation) and a safe base with Standard-Logical axioms \
        (neither proves the observation truthful), and \
        `Regula.Checker.Policy.partialParent_rule` with `subject_contract` reports a \
        `partial def`'s helper under the `partial def`."
      sources :=
          ["lean/RegulaPolicy/Decision.lean", "lean/Regula/Collect.lean",
              "lean/RegulaCore/Policy.lean"] }
  | .executableContract => {
      problem := "A closed `ExecutableContract f R` registration does not have the supported \
        shape: it is not closed, it names no complete implementation constant, or the \
        implementation is not an eligible executable definition."
      trigger := [
        "The checker recognizes declarations of type `Regula.ExecutableContract f R` as executable \
          promises about `f`. It rejects, with applicability `executable-contract`, a registration \
          with free parameters, a partially applied or term-parameterized implementation, or an \
          implementation that is missing, noncomputable, unsafe, partial, proposition-valued, \
          type-producing or not an executable definition.",
        "Lean's type checker separately checks the supplied proof of `R f`."]
      rationaleDetail := []
      proofShape := [
        "`ExecutableContract f R` for a named constant `f` with `R : type-of-f → Prop` stating the \
          full-domain requirement. The proof inhabits exactly `R f`; a weaker `R` changes the \
          requirement and is a review failure."]
      established := [
        "The registration is closed, names an eligible executable constant, and Lean checked a \
          proof of the stated predicate about it."]
      notEstablished := [
        "That `R` expresses the intended behavior (R-INTENT) and that every caller uses the \
          contracted implementation (R-INVARIANT). Every accepted account lists these as open for \
          each reported contract.",
        "Behavior of compiled code beyond the Lean definition; execution boundaries are RG3001 and \
          RG3002."]
      configuration := []
      limitations := [
        "Term-parameterized and partial-application registrations are unsupported shapes, not \
          proofs of incorrectness; restate them as closed full-domain contracts."]
      residuals := [.intent, .invariant, .qualify]
      checklist :=
          ["BUILD-03", "THEOREM-07", "SCOPE-02", "SCOPE-03", "TYPE-01", "THEOREM-01",
              "THEOREM-03", "COMP-01", "BUILD-01", "BUILD-02"]
      linkage := declarationLinkage ++ " Extracting the contract observation (`Regula.Collect`) \
        is operational."
      sources :=
          ["lean/Regula/Contract.lean", "lean/Regula/Probe.lean", "lean/RegulaCore/Policy.lean"] }
  | .environment => {
      problem := "The declared Lean environment could not be loaded or identified, so the \
        requested audit could not run. The result is INCOMPLETE, not a violation of the source."
      trigger := [
        "Setup checks load the Lake workspace, resolve dependencies to exact source states, and \
          establish the compiler assumptions the audit needs. A failure (for example \
          `lake-workspace-load-failed` when a required package directory is missing) is reported \
          with impact `incomplete`.",
        "RG2001 is also the finding for any other error that escapes the audit before a more \
          specific rule classifies it (for example a malformed Lake query result). Read the \
          detail: it names the failing step. Such an error is INCOMPLETE, never a pass.",
        "A checker worker that loads a built environment for inspection and fails (for example \
          an import conflict, or Lean's maximum recursion depth) is RG2001 too: the detail names \
          the environment it was inspecting and carries the worker's own error text, and the \
          result lists the stages that completed before it."]
      rationaleDetail := []
      proofShape := []
      established := [
        "A passing result was produced in the declared environment: Lake loaded the workspace with \
          the exact toolchain and resolved dependency state the result reports. An unavailable or \
          unidentified environment is incomplete and never accepted."]
      notEstablished := [
        "That a dependency checkout matches its recorded revision's content: dependency \
          acquisition is a trusted mechanism.",
        "Anything about the source; no declaration was inspected."]
      configuration := [
        "There is no configuration that turns an incomplete setup into a pass."]
      limitations := [
        "This page's example is a diagnostic demonstration: the violating run is INCOMPLETE by \
          design and is not accepted negative evidence. Its corrected counterpart passed a \
          completed positive check."]
      residuals := [.qualify]
      checklist := ["DECL-01", "DECL-04"]
      linkage := "None. Setup failures and escaped audit errors reach this rule by their error \
        message prefix, failing closed to INCOMPLETE; that classification is not proved."
      sources :=
          ["lean/Regula/Checker/Workspace.lean", "lean/Regula/Checker/Lake.lean",
              "lean/Regula/Checker/ResultProtocol.lean"] }
  | .configuration => {
      problem := "The surface manifest (`foundation_manifest.json`, schema 2) is invalid or does \
        not classify every root-package library and executable exactly once."
      trigger := [
        "The checker parses the manifest and reconciles it with Lake's elaborated root package. \
          Unknown keys, duplicates, a wrong schema version, an unknown `execution` value, an empty \
          `surfaces` array, a missing rationale, an unclassified or unknown target, and an \
          executable whose root module belongs to a library classified differently (claimed in \
          another surface, or claimed where the library is excluded, or the reverse) are \
          rejected (`manifest-schema`, `manifest-incomplete`, `manifest-conflict` and related \
          subreasons). A claimed executable whose root belongs to its own surface's library is \
          accepted unless every module of that library is such a root; the root is then \
          inspected once, in the executable's environment.",
        "In the editor, an invalid local request (for example an unknown `regula.localFoundation` \
          value) is reported under this rule for the current file only."]
      rationaleDetail := []
      proofShape := []
      established := [
        "The manifest has the exact schema and classifies every root-package library and \
          executable exactly once, each executable alike with every library that contains its \
          root module."]
      notEstablished := [
        "That the chosen claims and exclusions are appropriate for the project; that is reviewed \
          with each rationale.",
        "Exclusions do not permit a claimed module to import an excluded one (RG2004)."]
      configuration := [
        "The manifest is the configuration; there is no flag that accepts an invalid manifest, and \
          the schema requires at least one nonempty library surface. \
          `--manifest PATH` and `--project DIR` select which files are audited, not how strictly.",
        "`lake lint` exits 2 (INVALID CONFIGURATION) when only this rule rejects."]
      limitations := [
        "Executable-only packages are valid Lean projects but unsupported by manifest schema 2.",
        "A claimed library needs a module besides its claimed executables' roots: its own \
          environment would otherwise be empty, which the checker does not support.",
        "The editor never guesses an omitted project scope."]
      residuals := [.qualify, .intent, .invariant]
      checklist := ["DECL-04", "SCOPE-05", "BUILD-04", "DECL-01", "BUILD-01"]
      linkage := "`Regula.Checker.Manifest.parse_sound` and `parseValue_complete` for the \
        manifest (kernel-checked in the excluded `Regula` library) and \
        `Regula.Linter.checked_editorRequest` for the editor's request. An executable root's \
        classification is `RegulaPolicy.RootsClassifiedAlike`: `AxiomGate.checkClassification` \
        decides it before the build of the project audit, `lake lint` and the build linter, and \
        in `doctor` and `--explain-config`, and every accepted project claim decides it again in \
        `TargetPartitionOK`; the nonempty-library check decides `ClaimCandidate.Valid`'s \
        condition over the executed surface assignment. Routing a failure to this rule by its \
        `manifest-` prefix is not proved."
      sources :=
          ["lean/Regula/Checker/Manifest.lean", "lean/Regula/Checker/Lake.lean",
              "lean/Regula/Checker/AxiomGate.lean", "lean/RegulaPolicy/Plan.lean",
              "lean/Regula/Findings.lean"] }
  | .sourceBuild => {
      problem := "The claimed source did not elaborate warning-free under the audit's build: the \
        build failed or emitted a warning."
      trigger := [
        "The audit builds the claimed targets itself and checks both the exit status and every \
          emitted diagnostic. Any warning fails, including when the source sets `warningAsError` \
          to false locally (for a single-file audit, when any `--claim` is requested). The \
          original compiler message is preserved in the finding.",
        "In project runs (`lake lint`, `axiomGate`, the build-lint `policy` target) a warning or \
          failed build stops the audit before policy inspection, so the finding is incomplete and \
          the result INCOMPLETE (`lake lint` exit 3). A single-file `axiomGate --file F --claim P` \
          audit reports a completed source rejection as a violation, as in the checked example; \
          without `--claim` warnings do not fail a file audit (an elaboration error is still a \
          RG2003 violation), a file that elaborates and passes the declaration rules is CLASSIFIED \
          rather than accepted, and a failed build of the manifest's claimed targets it depends on \
          is INCOMPLETE."]
      rationaleDetail := []
      proofShape := [
        "The fix must not change the proposition or behavior being claimed; if it does, review the \
          statement again."]
      established := [
        "Every claimed module elaborated from source without errors or warnings under the audit's \
          build."]
      notEstablished := [
        "Fresh source elaboration unless the run is fresh: `lake lint` without `--fresh` is \
          incremental and trusts Lake's build cache.",
        "That no linter was disabled: a disabled linter emits nothing for this rule to reject."]
      configuration := [
        "`warningAsError := false` in the source cannot hide a warning from the audit. Disabling a \
          linter stops it from emitting, which makes this rule pass without establishing the \
          property the linter checks. Never disable Lean's default warnings, such as \
          `linter.unusedVariables` (for example with `set_option linter.unusedVariables false`).",
        "A community linter reports through build warnings, so this rule rejects its findings, \
          whether a dependency turns it on for every importer (such as Mathlib's \
          `linter.unusedTactic`) or the project enables it (such as `linter.missingDocs` and \
          Mathlib's `weak.linter.mathlibStandardSet`, which standard §6.7 requires). Where the \
          community's guidance allows an exception, disable that linter for one declaration \
          (`set_option linter.NAME false in` or `@[nolint NAME]`) with a comment giving the reason \
          (standard §6.2). The detector sees only emitted warnings, so it cannot tell such a \
          disable from a forbidden one; review checks them."]
      limitations := [
        "`lake lint` builds with Regula's audit-build marker, which turns the local linter off \
          whatever the source sets `linter.regula` to, so Regula's own local findings are not \
          build warnings there and its policy stages report those rules. `axiomGate` and the \
          build-lint `policy` target keep ordinary options, so in a module that imports \
          `Regula.Linter` a local Regula finding is a build warning and makes the result \
          INCOMPLETE under this rule."]
      residuals := [.qualify]
      checklist := ["DECL-01", "BUILD-01", "DOC-01"]
      linkage := "Acceptance side only: an accepted run satisfies `RegulaPolicy.BuildOK`. Reading \
        Lake's build result is operational."
      sources :=
          ["lean/Regula/Checker/Lake.lean", "lean/Regula/Checker/Diagnostics.lean",
              "lean/Regula/Checker/ResultProtocol.lean"] }
  | .coverage => {
      problem := "The exact module and declaration inventory from Lake does not match the owned \
        coverage: a claimed library imports an excluded or checker-probe module, a module is \
        outside every manifested library, or ownership cannot be determined."
      trigger := [
        "Module inventory comes from Lake's elaborated configuration and Lean's recorded module \
          indices, not from file lists or name prefixes. The checker resolves each imported \
          root-package module's origin and rejects unexpected project modules, imports of excluded \
          modules into claimed ones, and unknown ownership (`unexpected-project-module` and \
          related subreasons).",
        "A root-package module outside every manifested library that a claimed module imports \
          stops that environment's inspection, since kernel admission cannot classify it: the \
          finding names the module and the modules that import it. The single-file audit \
          (`axiomGate --file`) reports such an import the same way, naming the audited file by \
          its path where it is an importer.",
        "The impact depends on the subreason. A forbidden import or a module outside every \
          manifested library (`unexpected-project-module`) is a violation (`lake lint` exit 1 \
          unless the same run also has an incomplete finding). A configured module that was \
          omitted or not freshly built, or a declaration attributed outside the claimed surface, \
          is incomplete evidence (INCOMPLETE, `lake lint` exit 3)."]
      rationaleDetail := []
      proofShape := [
        "The removed import must not have supplied evidence the claim still relies on."]
      established := [
        "For a project audit, the claimed modules are exactly Lake's configured modules for the \
          claimed targets, and every owned constant is attributed to one of them.",
        "For a single-file audit, every module the file loads from the root package's build \
          output is a module of one of the package's Lake libraries or an executable's root."]
      notEstablished := [
        "That the chosen library boundaries are the ones the project intends to claim; that is \
          reviewed with the manifest rationale."]
      configuration := [
        "An exclusion in the manifest never permits a claimed module to import the excluded \
          one."]
      limitations := [
        "The editor is explicitly partial and does not report this rule. A single-file audit \
          reports only a module outside every Lake library that the file imports, not the whole \
          project's inventory coverage."]
      residuals := [.qualify]
      checklist :=
          ["DECL-02", "DECL-03", "SCOPE-05", "DECL-01", "DECL-04", "BUILD-01",
              "BUILD-03", "BUILD-04"]
      linkage := "Acceptance side only: an accepted run satisfies `RegulaPolicy.ScopeOK`, over \
        the surface assignments of `Regula.Checker.Acceptance.checked_surfaceAssignments`, and \
        `RegulaPolicy.census_covers_claimed_targets` shows that every module of a claimed Lake \
        target is a positive module of the accepted census. The inventory checks are \
        operational."
      sources :=
          ["lean/Regula/Checker/Lake.lean", "lean/Regula/Probe.lean",
              "lean/Regula/Checker/AxiomGate.lean", "lean/RegulaPolicy/Plan.lean"] }
  | .admission => {
      problem := "Required evidence is missing, incomplete, unsupported or invalid: owned \
        declarations did not pass kernel admission, a frozen source or `.olean` file changed \
        during the audit, or authentication the result needs could not complete. The result is \
        INCOMPLETE."
      trigger := [
        "Before accepting proof evidence the checker replays every owned logical declaration and \
          its owned dependencies through Lean's kernel (`Admission.validate`); an environment \
          reuses, instead of repeating, an earlier environment's replay of a claimed library \
          module over the identical import closure and frozen `.olean` parts (including \
          `.olean.private`). Each replayed module's own copy of a name is checked: a lemma \
          Lean realizes in two modules, such as an equation lemma, is admitted when the copies \
          are theorems of the same statement, universe parameters and mutual block and each \
          owned copy that is not identical to the replayed or trusted one passes the kernel \
          with a proof that does not reach its own name and reaches the same axioms. A \
          declaration that fails replay, source or `.olean` bytes that changed after they were \
          frozen, or a required authentication that failed is reported here with impact \
          `incomplete`.",
        "In the editor, this rule marks results that need fresh evidence only the project command \
          collects, and those messages name `lake lint`. The editor also reports it, as \
          incomplete, when its own analysis of a declaration fails or the module has elaboration \
          errors."]
      rationaleDetail := []
      proofShape := [
        "The replayed declaration must type-check in the kernel with exactly its stated type and \
          value."]
      established := [
        "Every owned logical declaration and its owned dependencies passed kernel replay (every \
          other copy of a theorem that another loaded module also declares is identical to the \
          replayed or trusted one, or passed the kernel's check under a fresh name with a \
          proof that does not reach its own name and reaches the same axioms), and the frozen \
          sources were unchanged during the audit. A failed admission or changed source is \
          incomplete and never accepted."]
      notEstablished := [
        "Imported, unowned dependencies are not replayed; they remain the declared trusted base.",
        "Incremental admission does not establish fresh source elaboration."]
      configuration := [
        "No option waives admission. A failed generated-role authentication cannot waive RG1001 or \
          RG1006."]
      limitations := [
        "This page's example is a diagnostic demonstration: the violating run is INCOMPLETE by \
          design and is not accepted negative evidence. Its corrected counterpart passed a \
          completed positive check."]
      residuals := [.qualify]
      checklist :=
          ["DECL-01", "DECL-02", "FOUND-05", "SCOPE-02", "TYPE-01", "THEOREM-01", "THEOREM-03",
              "THEOREM-07", "DECL-03", "DECL-04", "COMP-02", "COMP-04", "BUILD-01", "BUILD-04"]
      linkage := "Acceptance side only: an accepted run satisfies `RegulaPolicy.AdmissionOK`. \
        The editor's deferral to the project audit is \
        `Regula.Checker.Policy.editor_decision_pending`."
      sources :=
          ["lean/Regula/Checker/Admission.lean", "lean/Regula/Checker/SourceAudit.lean",
              "lean/Regula/Checker/SourceBinding.lean"] }
  | .communityConfiguration => {
      problem := "A claimed library or executable is built with automatic implicits on or \
        without Lean's `linter.missingDocs`, turns off a linter for all its modules beyond the \
        three Mathlib-repository linters that standard §6.7 excludes, overrides these options \
        with a `-D` extra `lean` argument, or, in a surface that imports Mathlib, leaves Mathlib's \
        standard linter set or its exclusions unset."
      trigger := [
        "After the claimed surfaces build, the checker reads Lake's resolved configuration of \
          every claimed library and executable: its `leanOptions` (build type, package, then \
          target, a later entry replacing an earlier one) and its `weakLeanArgs` and \
          `moreLeanArgs`. The proved decision `RegulaPolicy.Community.failures` rejects the \
          target, with applicability `community-configuration`, when `autoImplicit` or \
          `relaxedAutoImplicit` is not set to `false` or `linter.missingDocs` is not set to \
          `true`, when any other `linter.…` option than \
          `linter.style.header`, `linter.hashCommand` and `linter.style.longFile` is set to \
          `false`, or when a `-D name=value` among the extra arguments gives a required option \
          a value the rule does not admit or sets such a linter to `false`.",
        "A target of a surface whose loaded environments contain a Mathlib module must also set \
          `weak.linter.mathlibStandardSet` to `true`, `weak.linter.hashCommand` to `false` and \
          `weak.linter.style.longFile` to `0`, and `weak.linter.style.header` to `false`, or to \
          `true` when the target also gives `weak.linter.style.header.license` the license line \
          Mathlib's header linter expects in `leanOptions`, with every value that `leanOptions` or \
          any `-D` gives it a nonempty string; a `-D` alone does not configure the license line.",
        "A key's leading `weak.` component is read as the option it sets; a target that gives one \
          option under both spellings must give a value the rule admits under each. A string value \
          counts as Lean parses it for the option: `\"false\"` is `false` and `\"0\"` is `0`. \
          One finding per target lists every failure.",
        "Every `-D` that `lean` reads starts at the first `D` of an argument that begins with a \
          single `-` (`-D`, or after flags as in `-qD`), with its value after the `D` or in the \
          next argument; the rule reads every such candidate, so it can also reject one that \
          `lean` does not read as a `-D`, such as the value of `-o`. Any other extra argument is \
          allowed."]
      rationaleDetail := [
        "Standard §7.1 requires the options because they decide which binders a declaration's \
          elaborated type has. Standard §6.7 adopts the community's linters as its conventions \
          baseline, and a linter enforces its convention only where it is on: RG2003 rejects \
          warnings, not a missing linter."]
      proofShape := []
      established := [
        "Every claimed library and executable is built through Lake with automatic implicits \
          off and `linter.missingDocs` on, turns off no linter target-wide beyond the §6.7 \
          exclusions and, in a Mathlib surface, enables the standard set with exactly those \
          exclusions, or with the header linter on and its license line configured; no `-D` \
          extra `lean` argument overrides these options."]
      notEstablished := [
        "That no module sets an option back in source, such as `set_option autoImplicit true` or \
          a linter disable; review checks source options (§6.2).",
        "That the community linters' own checks pass, such as a docstring on every public \
          declaration; their warnings are RG2003's.",
        "That extra `lean` arguments other than `-D`, such as `--plugin` or `--setup`, leave the \
          options unchanged."]
      configuration := [
        "The Lake configuration is the input; no manifest field, source option or command-line \
          flag exempts a claimed target.",
        "A Mathlib target that keeps the header linter on names its license line in `leanOptions`: \
          ``⟨`weak.linter.style.header, true⟩, ⟨`weak.linter.style.header.license, \
          \"Released under the MIT license as described in the repository LICENSE.\"⟩``; a \
          `lakefile.toml` gives both in the array form of `leanOptions`, since its \
          `[leanOptions]` table cannot hold both keys. Without the license option the target \
          must set the header linter to `false`."]
      limitations := [
        "Options given on `lake`'s own command line are not read; the rule reads what Lake \
          resolves for the workspace the audit loads.",
        "Whether a surface imports Mathlib is read from all of its loaded environments, so every \
          claimed target of such a surface, including an executable whose own root does not \
          import Mathlib, needs the Mathlib options.",
        "The `-D` reading is assumed to cover the command-line parser of the Lean executable, \
          as read from Lean's `Lean.Shell` source and its getopt handling; that correspondence \
          is neither proved nor observed.",
        "That Mathlib's header linter compares the second header line with \
          `linter.style.header.license` is read from its source at the pinned release and \
          assumed; the rule checks that the license option is configured, not that the modules' \
          header lines match it.",
        "The rule runs in project audits only; editor feedback does not read Lake configuration."]
      residuals := [.qualify, .intent]
      checklist := ["DECL-01", "DOC-01"]
      linkage := "`RegulaPolicy.Community.failures_eq_nil_iff`, `conforming_of_mathlib`, \
        `conforming_missingDocs`, `conforming_header`, `header_on_unlicensed_fails`, \
        `licensed_iff`, `licensed_header_passes`, `unlicensed_header_fails`, \
        `leanArgument_mem_failures_iff` and `missingDocs_unset_fails`. Reading Lake's target \
        configuration is operational."
      sources := ["lean/RegulaPolicy/Community.lean", "lean/Regula/Checker/Lake.lean",
        "lean/Regula/Checker/AxiomGate.lean", "website/RegulaStandard/CodeOrganization.lean"] }
  | .executionUnresolved => {
      problem := "The conservative execution closure of an executable root has a path the checker \
        could not resolve: a missing compiled body, unavailable replacement history, an \
        unsupported evaluator, or a cycle of replacement edges. The execution claim is INCOMPLETE."
      trigger := [
        "For every owned executable root the checker follows retained compiler edges, logical \
          value dependencies, `csimp` candidates, observed `implemented_by` choices and partial \
          helpers. Anything it cannot resolve or classify is reported with applicability \
          `execution-unresolved` and impact `incomplete`, in both `report` and `checked` execution \
          modes.",
        "Replacement history is reconstructed by fresh re-elaboration; metaprogramming commands \
          such as `run_cmd`, `run_elab` or module-local elaborators make it unavailable.",
        "A path through the Lean toolchain's own origin-checked `Init`, `Std` or `Lean` modules \
          does not need that history: a toolchain replacement is followed through the current \
          target its compiled module records, as part of the toolchain's trusted base, so no \
          toolchain replacement is reported as unresolved for missing history."]
      rationaleDetail := []
      proofShape := []
      established := [
        "Every path in each owned executable root's conservative closure was resolved and \
          classified; an unresolved path is incomplete and never accepted."]
      notEstablished := [
        "That the conservative closure is the program's actual runtime call graph: candidates and \
          historical choices overapproximate it, and a safe program can be rejected."]
      configuration := [
        "No execution mode waives an unresolved path."]
      limitations := [
        "This page's example is a diagnostic demonstration: the violating run is INCOMPLETE by \
          design and is not accepted negative evidence. Its corrected counterpart passed a \
          completed positive check.",
        "The editor does not analyze execution: it reports neither this rule nor a pending notice \
          for it. Only `lake lint`, `axiomGate` (including `--file`) and the build-lint `policy` \
          target do."]
      residuals := [.qualify, .invariant, .intent]
      checklist := ["COMP-03", "SCOPE-05", "SCOPE-03", "THEOREM-05", "BUILD-01", "BUILD-03"]
      linkage := "`RegulaPolicy.executionFailureRecords_empty_iff`, \
        `RegulaPolicy.executionFindings_empty_iff`, `RegulaPolicy.unresolved_reported`, \
        `Regula.Checker.Policy.checked_executionFailures` and `executionRule_injective`. \
        Extracting the execution closure from compiler IR is operational."
      sources :=
          ["lean/Regula/Probe.lean", "lean/RegulaCore/Policy.lean",
              "lean/Regula/Checker/RuleDiagnostics.lean"] }
  | .executionBoundary => {
      problem := "On a surface claiming `\"execution\": \"checked\"`, a reachable boundary the \
        project or a dependency owns lacks kernel-checked correspondence: for example an \
        `implemented_by` replacement without an admitted equality proof, an external `extern`, or \
        unsafe or partial computation."
      trigger := [
        "Each reached boundary gets a kind and a correspondence state. Under checked execution, a \
          boundary that is `trusted` rather than `checked` is rejected with applicability \
          `execution-trusted-boundary` in every root that reaches it, unless the boundary itself \
          carries an admitted toolchain origin. Only a replacement, `extern`, or unsafe or partial \
          computation can: a `csimp` simplification or a compiler-trusting proof axiom never \
          does, even on a constant declared in `Init`.",
        "The toolchain owns a replacement, `extern`, or unsafe or partial computation declared in \
          one of its own `Init`, `Std` or `Lean` modules, decided by where Lean loaded that module \
          from (the pinned toolchain's library, an observation of the probe), not by its name. \
          Such a boundary is the toolchain's trusted base: it passes and is reported once for the \
          whole audit, with every environment and root that reaches it, in the audit's toolchain \
          trusted base.",
        "A `partial` implementation that a trusted boundary names as the code run in its place \
          is reported with that boundary where both are trusted and neither is the toolchain's, \
          as one finding that names both and one counted boundary. A `partial` implementation is \
          a constant of `partial` definition safety: the implementation a metaprogram such as \
          Mathlib's `compile_inductive%` adds for a recursor, named as the target of a `csimp` \
          candidate or of an `implemented_by` replacement, or the `_unsafe_rec` helper Lean \
          generates for a `partial def`, named by that `partial def`'s own boundary. A \
          `partial def` named as the target of a candidate or replacement is not one: it is an \
          opaque constant compiled through that helper, so it keeps its own finding and count, \
          and only its helper is reported with it. A second record of one trusted boundary (the \
          same constant, kind, replacement and toolchain origin, as two constants of one \
          equality's type give a `csimp` candidate) is reported and counted with the first in \
          the same way. The account in `--json-out` keeps every record, and `--verbose` lists \
          the implementation under its boundary as its `implementation` and a later record as \
          `restated`.",
        "A correspondence is checked only when a closed proof of `∀ xs, f xs = g xs` over the \
          reference's complete elaborated domain passes kernel admission, with only standard \
          logical axioms and no extra premises."]
      rationaleDetail := []
      proofShape := [
        "`∀ xs, f.{us} xs = g.{us} xs` over the reference's complete dependent domain, closed, \
          with no additional hypotheses, admitted by the kernel. An actual domain hypothesis is \
          legitimate; an extra premise such as `False` is not."]
      established := [
        "Every reached boundary of a checked surface without an admitted toolchain origin has \
          kernel-admitted correspondence; each one without it has a failure record in every root \
          whose account contains it (`RegulaPolicy.project_boundary_reported`).",
        "Every such failure record is reported: as its boundary's own finding, or, for a \
          `partial` implementation reported with the boundary that runs it, in that boundary's \
          finding, which names it, or, for a later record of a trusted boundary, in the finding \
          that reports the first record (`RegulaPolicy.failure_reported`). Every finding is a \
          record (`RegulaPolicy.executionFindings_sound`), and the findings are empty exactly \
          when the records are (`RegulaPolicy.executionFindings_empty_iff`).",
        "Each toolchain-owned boundary of every environment an audit inspects is in exactly one \
          entry of the audit's toolchain trusted base, which lists exactly the environments and \
          roots that reach it (`RegulaPolicy.checked_toolchainBase`)."]
      notEstablished := [
        "Correctness of the toolchain's own replacements, unsafe code and native primitives, the \
          compiler or external code; a Lean equality does not prove external machine code. These \
          stay trusted and reported.",
        "Anything about code the program selects at runtime rather than references: a constant \
          it evaluates by name (`Lean.Environment.evalConst`, `Lean.Meta.reduceBoolNative`), a \
          dynamic library or plugin it loads, or a process it spawns. The account is the static \
          closure; such code is data to it, and the toolchain primitive that runs it is trusted \
          base. The `initialize` and `[init]` actions of imported modules, static or at runtime, \
          are likewise outside the account.",
        "That the executable roots are the ones the project intends to cover (R-INVARIANT)."]
      configuration := [
        "`execution` in the surface manifest (`report` or `checked`), or `--execution checked` for \
          a single-file audit, selects the mode. `report` mode reports trusted boundaries without \
          failing them; it is not a fix for a checked claim."]
      limitations := [
        "Proof search is deliberately incomplete: a candidate whose remaining premises cannot be \
          instantiated supplies no evidence, and the boundary stays trusted."]
      residuals := [.intent, .invariant, .qualify]
      checklist :=
          ["COMP-03", "COMP-04", "SCOPE-03", "SCOPE-05", "THEOREM-05", "BUILD-01", "BUILD-03"]
      linkage := "`RegulaPolicy.executionFailureRecords_empty_iff`, \
        `RegulaPolicy.executionFindings_empty_iff`, \
        `Regula.Checker.Policy.checked_executionFailures`, `executionRule_injective`, \
        `RegulaPolicy.boundaryFailures_toolchain`, `RegulaPolicy.project_boundary_reported`, \
        `RegulaPolicy.failure_reported`, `RegulaPolicy.executionFindings_sound` and \
        `RegulaPolicy.checked_toolchainBase`; an accepted run satisfies `RegulaPolicy.BoundaryOK`. \
        Extracting the execution closure from compiler IR and observing module origins are \
        operational."
      sources :=
          ["lean/Regula/Probe.lean", "lean/RegulaCore/Policy.lean",
              "website/RegulaStandard/ToolingAndMachineAudit.lean"] }
  | .fenceStructure => {
      problem := "A Markdown file in the checked documentation tree has a malformed Lean fence \
        classification: an orphan, misplaced, duplicated or misspelled marker, an invalid \
        expected-error pattern, or an unclosed fence."
      trigger := [
        "The documentation scanner classifies every Lean fence in every Markdown file of the \
          selected tree. An unmarked `lean` fence is positive; an immediately adjacent `<!-- \
          lean-fail: PATTERN -->` makes the next fence negative; `<!-- lean-trusted-compiler -->` \
          marks a teaching example. Anything else that looks like a marker, or a structural error, \
          is rejected with applicability `fence-structure`.",
        "The pattern grammar is small: `|` separates alternatives, `.*` separates ordered literal \
          fragments, and an optional leading `(?s)` is accepted for compatibility; other regex \
          syntax is rejected."]
      rationaleDetail := []
      proofShape := []
      established := [
        "Every Lean fence in the checked tree has exactly one valid classification."]
      notEstablished := [
        "That the prose around a fence describes it faithfully (R-DOC)."]
      configuration := [
        "The checked tree is the documentation tree the audit selects (`docs/` for `lake exe \
          docFenceAudit`). There is no per-fence opt-out.",
        "This rule is a documentation-mode rule; it is not reported by the per-declaration editor \
          linter."]
      limitations := [
        "Only Markdown structure is checked here; elaboration results belong to RG4002–RG4004."]
      residuals := [.qualify, .doc]
      checklist := ["DOC-03"]
      linkage := "Acceptance side only: an accepted run satisfies `RegulaPolicy.DocumentOK`. The \
        fence scanner is not proved."
      sources := ["lean/Regula/Checker/Documentation.lean", "lean/Regula/Checker/Diagnostics.lean",
          "lean/RegulaPolicy/Pattern.lean"] }
  | .positiveExample => {
      problem := "A positive Lean fence in the documentation did not elaborate verbatim and \
        warning-free, or it did and then failed admission or the declaration and axiom rules."
      trigger := [
        "Each positive fence is elaborated exactly as printed, with no inserted imports or \
          wrappers, against a fresh build of the claimed libraries. It must be warning-free, pass \
          checked admission, and pass the declaration and axiom rules under Standard-Logical. The \
          fence failure is reported here together with the underlying finding (for example RG1001 \
          for an axiom in the example).",
        "A fence that fails without a source diagnostic (for example a worker that stopped before \
          completing) is reported as INCOMPLETE, not as a violation."]
      rationaleDetail := []
      proofShape := [
        "The fence proves exactly the claim the surrounding prose states. A narrower foundation or \
          an execution claim in the prose needs its own evidence; fence success establishes only \
          Standard-Logical admission."]
      established := [
        "The positive fence elaborated verbatim, warning-free, passed owned admission and the \
          declaration and axiom rules."]
      notEstablished := [
        "That the prose describes the fence faithfully (R-DOC, R-INTENT), or any narrower \
          foundation claim."]
      configuration := [
        "No marker makes a failing positive example acceptable; changing it to `lean-fail` changes \
          what the documentation claims.",
        "Run `lake exe docFenceAudit`."]
      limitations := [
        "Examples are checked under the declared toolchain only."]
      residuals := [.intent, .qualify]
      checklist := ["DOC-04"]
      linkage := declarationLinkage ++ " An accepted run satisfies \
        `RegulaPolicy.ExampleExpectationOK`, and `incomplete_example_refused` refuses an \
        incomplete example."
      sources := ["lean/Regula/Checker/Documentation.lean", "lean/Regula/Checker/SourceAudit.lean",
          "lean/Regula/Checker/Admission.lean"] }
  | .negativeExample => {
      problem := "A fence marked `lean-fail` did not fail as specified: it elaborated \
        successfully, failed for a different reason, or the worker crashed or timed out."
      trigger := [
        "A negative fence must complete with a source rejection, and one effective error message \
          must match the entire expected pattern. Informational output, a pattern matched across \
          several messages, a crash, a timeout or a successful elaboration does not pass.",
        "An example that elaborated successfully or failed with a non-matching message is a \
          violation; a worker that crashed, timed out or did not complete is INCOMPLETE."]
      rationaleDetail := []
      proofShape := [
        "The pattern is part of the documented claim and is reviewed with the prose."]
      established := [
        "The negative fence completed with a source rejection whose single error message matches \
          the whole pattern."]
      notEstablished := [
        "That the rejection happens for the conceptual reason the prose explains beyond the \
          matched message text."]
      configuration := [
        "The marker and its pattern are the configuration; there is no option that accepts a \
          non-failing negative example."]
      limitations := [
        "Regula policy rejections of documentation examples can follow successful elaboration; \
          this rule concerns compiler rejection patterns of `lean-fail` fences."]
      residuals := [.qualify, .doc]
      checklist := ["DOC-05"]
      linkage := "`RegulaPolicy.matchesPattern_iff` characterizes the executed matcher."
      sources :=
          ["lean/Regula/Checker/Diagnostics.lean", "lean/RegulaPolicy/Pattern.lean",
              "lean/Regula/Website.lean"] }
  | .trustedExample => {
      problem := "A fence marked `lean-trusted-compiler` did not elaborate warning-free with an \
        authenticated compiler-trusting declaration: it contains no native proof, or \
        authentication failed."
      trigger := [
        "A teaching fence must elaborate warning-free and the checker must authenticate at least \
          one compiler-trusting declaration in it, using the same fresh-frontend evidence as \
          RG1004. If none is found, or authentication fails, the fence is rejected with \
          applicability `trusted-example`.",
        "The fence is also rejected, with the underlying finding, when any declaration in it fails \
          the declaration rules under the teaching request (for example RG1001 for an axiom or \
          RG1006 for an unsafe or partial declaration)."]
      rationaleDetail := []
      proofShape := []
      established := [
        "The teaching fence elaborated warning-free and contains an authenticated \
          compiler-trusting declaration."]
      notEstablished := [
        "Any conformance of the teaching example; it is classified, never counted as a positive \
          proof."]
      configuration := [
        "There is no name-based allowlist for native proofs; authentication is required for every \
          teaching fence."]
      limitations := [
        "Teaching fences are re-elaborated for authentication, so their imports are paid twice; \
          keep them small."]
      residuals := [.qualify]
      checklist := ["DOC-05"]
      linkage := "`RegulaPolicy.checked_memberFoundation` and \
        `Regula.Checker.Policy.labelOf_member`."
      sources := ["lean/Regula/Checker/Documentation.lean", "lean/Regula/Checker/Frontend.lean",
          "lean/RegulaPolicy/Decision.lean"] }
  | .moduleDocumentation => {
      problem := "A module in a claimed surface has no module docstring (`/-! … -/` or Verso \
        module documentation), has one that is not the first command after its imports, or \
        repeats an import with the same modifiers."
      trigger := [
        "When a claimed module finishes elaborating, the checker asks Lean for its module \
          documentation and parses the module's header and first command from its source with \
          Lean's own parser. The proved decision `RegulaPolicy.ModuleHeader.failures` then \
          rejects, with applicability `module-documentation`, a module without module \
          documentation; a module whose first command after the imports is not a module \
          docstring (for example `@[expose] public section` or a declaration; a \
          `set_option … in` prefix, the community's form for a Verso module docstring, is read \
          through); and each import that occurs twice with the same `public`, `meta` and `all` \
          modifiers. Empty modules are included."]
      rationaleDetail := []
      proofShape := []
      established := [
        "Every claimed module has module documentation, its first command after the imports is \
          a module docstring, and its header repeats no import."]
      notEstablished := [
        "That the documentation identifies all material declarations and assumptions, or \
          describes them faithfully (R-DOC). Presence and position say nothing about content; no \
          section layout is imposed.",
        "Import minimality: an unused or transitively redundant import that is not repeated is \
          not reported."]
      configuration := []
      limitations := [
        "The editor reports this rule only when the module has finished elaborating without \
          errors; a module with elaboration errors gets RG2005 (incomplete) instead."]
      residuals := [.doc]
      checklist := ["DOC-01", "DECL-01"]
      linkage := "`RegulaPolicy.ModuleHeader.failures_eq_nil_iff` and `mem_repeated_iff`, and \
        `Regula.Checker.Acceptance.modulePresence_iff` and `documentationPresence_modes`. \
        Parsing the module header is operational."
      sources := ["lean/RegulaPolicy/ModuleHeader.lean", "lean/Regula/Linter/Documentation.lean",
        "lean/Regula/Checker/AxiomGate.lean",
            "website/RegulaStandard/DocumentationStandards.lean"] }
  | .materialDocumentation => {
      problem := "A public declaration registered with `@[regula_material]` as evidence for a \
        material normative claim has no docstring."
      trigger := [
        "The checker selects public declarations carrying the persistent `@[regula_material]` \
          registration and asks Lean for their docstrings (`findDocString?`, which includes \
          inherited documentation). A registered declaration without one is rejected with \
          applicability `material-documentation`.",
        "Unregistered declarations are not selected; there is no name heuristic."]
      rationaleDetail := []
      proofShape := [
        "The docstring describes the elaborated statement faithfully."]
      established := [
        "Every registered public material declaration has a docstring."]
      notEstablished := [
        "That every material declaration is registered, or that the docstring is faithful and \
          adequate (R-DOC); registration completeness is semantic review.",
        "Docstrings of unregistered declarations. Standard §6.7 requires claimed libraries to \
          enable `linter.missingDocs`, whose reports RG2003 rejects; RG2006, not this rule, checks \
          that option."]
      configuration := [
        "Registration is `@[regula_material]` from `Regula.MaterialClaim`. Removing a registration \
          from a material declaration changes the reviewed claim, not only this rule's result."]
      limitations := [
        "Lean's broader `linter.missingDocs` reports public declarations without a docstring only \
          where it is enabled; this rule covers registered material evidence whatever the options.",
        "The editor reports this rule only when the module has finished elaborating without \
          errors; a module with elaboration errors gets RG2005 (incomplete) instead."]
      residuals := [.doc]
      checklist := ["DOC-01"]
      linkage := "`RegulaPolicy.materialDocumentationFailure_eq_none_iff`, \
        `materialDocumentationFailure_eq_missingDocstring_iff` and \
        `Regula.ruleForMaterialDocumentation_injective`."
      sources :=
          ["lean/Regula/MaterialClaim.lean", "lean/RegulaPolicy/Intent.lean",
              "lean/Regula/Linter/Documentation.lean"] }
  | .materialIntent => {
      problem := "A registered public material declaration has a docstring without a nonempty \
        labelled Intent section."
      trigger := [
        "An Intent section is an ATX heading line whose text is exactly `Intent` (one to six `#`, \
          no closing sequence), followed before the next heading of equal or higher level by at \
          least one non-heading line with text. Text under deeper subsection headings counts. A \
          registered docstring without such a section is rejected with applicability \
          `material-intent`.",
        "A declaration with no docstring at all is RG5002 only; the two rules partition the \
          failures."]
      rationaleDetail := []
      proofShape := [
        "The Intent section states the requirement the declaration must meet; review compares \
          the two."]
      established := [
        "Every registered public material declaration's docstring has a nonempty labelled Intent \
          section, decided by the proved classifier `RegulaPolicy.materialDocumentationFailure`."]
      notEstablished := [
        "That the intent states what the requirement owner needs, or that the declaration meets it \
          (R-INTENT, R-DOC). There is no intent detector, length threshold or similarity check.",
        "Code fences in the docstring are not tracked: a `# Intent` line inside a fenced block \
          counts as an Intent heading."]
      configuration := [
        "The rule checks only declarations registered with `@[regula_material]` from \
          `Regula.MaterialClaim`. Removing a registration from a material declaration changes the \
          reviewed claim, not only this rule's result."]
      limitations := [
        "Setext headings and closing sequences such as `# Intent #` are not recognized as Intent \
          headings.",
        "The editor reports this rule only when the module has finished elaborating without \
          errors; a module with elaboration errors gets RG2005 (incomplete) instead."]
      residuals := [.intent, .doc]
      checklist := ["DOC-02"]
      linkage := "`RegulaPolicy.materialDocumentationFailure_eq_missingIntent_iff` and \
        `RegulaPolicy.Intent.hasIntentSection_iff`."
      sources :=
          ["lean/RegulaPolicy/Intent.lean", "lean/Regula/MaterialClaim.lean",
              "lean/Regula/Linter/Documentation.lean"] }

/-- Every rule's explanation has all required sections, checked exhaustively over the closed
registry by kernel evaluation. -/
theorem guide_wellFormed : ∀ id, (guide id).WellFormed := by
  intro id; cases id <;> decide +kernel

end Regula.Site
