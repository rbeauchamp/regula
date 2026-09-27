import VersoManual
import RegulaExample

open Verso.Genre Manual RegulaExample

#doc (Manual) "5. Documentation Standards" =>
%%%
tag := "5-documentation-standards"
file := "5-documentation-standards"
number := false
%%%

{pageAnchor}

# Overview
%%%
tag := "5-overview"
number := false
%%%

Documentation states the purpose and meaning of Lean definitions and proofs, including their assumptions and limits. It helps readers assess whether a checked statement expresses the intended claim. This module covers declaration docstrings (§5.1), faithful explanation and written intent (§5.2), module documentation (§5.3), and proof readability (§5.4).

# 5.1 Inline Documentation Requirements
%%%
tag := "51-inline-documentation-requirements"
number := false
%%%

*Requirement*: Every public declaration used as evidence for a material normative claim MUST have a docstring identifying its formal purpose and accurately stating the claim it supports. Describe the relevant domain, hypotheses, result, and invariant boundary. Claims must follow from the elaborated type, the definition, or a proved contract about that definition.

*Community baseline*: Every public definition in a claimed library MUST also have a docstring, as the Lean community requires. {ref "67-community-conventions-and-linters"}[Section 6.7] makes every claimed library enable Lean's `linter.missingDocs`, which reports each public definition, structure, class, inductive type, constructor, and field without one, and the warning-free elaboration of §8.3 (RG2003) rejects each report. Documenting every major theorem, which Mathlib's [documentation requirements](https://leanprover-community.github.io/contribute/doc.html) also ask for and no enabled linter checks, is RECOMMENDED. The material requirement above is stricter than this baseline: RG5002 checks that each registered material declaration has a docstring and RG5003 that it has an Intent section, whatever linter options are set. One community allowance does not apply to those docstrings: Mathlib's guide lets a docstring "lie slightly" about the actual implementation, while a docstring supporting a material claim states the claim exactly (§5.2).

A function's type may constrain its inputs and outputs without specifying their relationship. For example, `Probability → Probability` ensures the output is a probability but does not specify which probability is returned. Document the defining operation or cite the theorem that establishes the promised relationship.

*Documentation Components*:

* *Purpose*: The declaration's role in the mathematical development or program.
* *Domain and hypotheses*: The inputs, assumptions, and relevant instance laws, including restrictions carried by the types.
* *Result*: The exact conclusion or defined behavior and the supporting type, definition, or theorem.
* *Boundary*: Limits that affect the interpretation, such as an abstract model's relationship to execution.

Use these components as prompts, with detail proportionate to the claim. A short declaration may need only one sentence.

*Example - Documentation That Matches the Formal Claim*:

```lean
import Mathlib.Topology.UnitInterval

/-- A real value in `[0, 1]`, reusing Mathlib's closed unit interval.
This type represents a scalar probability, not a probability distribution. -/
abbrev Probability : Type := unitInterval

/-- Unit-interval complement: the underlying value is `1 - p.val`.
Mathlib's `unitInterval.symm` constructs the result with its bound proof.
This wrapper preserves the example's vocabulary for that operation. -/
def Probability.complement (p : Probability) : Probability :=
  unitInterval.symm p

/-- For every probability, complement has underlying real value `1 - p.val`.

# Intent
Complementing a probability must yield the probability of the complementary event:
its value is one minus the original value. -/
theorem Probability.complement_val (p : Probability) :
    p.complement.val = 1 - p.val :=
  unitInterval.coe_symm_eq p
```

The result type supplies the bound. `Probability.complement_val` states the defining equation by reusing Mathlib's theorem. Neither the type alias nor the equation asserts a probability distribution or any property of an external random process.

# 5.2 Faithful Explanation of Formal Claims
%%%
tag := "52-faithful-explanation-of-formal-claims"
number := false
%%%

*Requirement*: Every mathematical expression carrying a normative claim MUST have a plain English explanation that faithfully conveys its quantifiers, hypotheses, conclusion, relevant definitions, and limitations. The explanation MUST name or link the authoritative Lean declaration. For a declaration docstring, the attached declaration supplies that reference.

Express mathematical statements in precise English. State the claim and its significance, and keep the checked declaration available for exact details. Refer to previously introduced definitions to keep the explanation concise, but do not omit any condition that changes the result. Prefer mathematical meaning over copying Lean syntax into prose.

*Fidelity Test*: Reading the explanation with its referenced definitions, a reader should be able to:

1. Identify the quantified objects, their domains, and the order and dependence of quantifiers.
2. State the hypotheses and conclusion without changing their strength.
3. Recognize limitations that affect the intended interpretation, including any unproved connection to execution or an external system.
4. Locate the Lean declaration and distinguish a result proved without additional hypotheses, a result proved under explicit hypotheses, and an open target, retaining the stated domain and foundations in either proved case. A conditional theorem does not by itself establish that its hypotheses are satisfiable or that its conclusion holds without them ({ref "310-research-statements-adequacy-conditional-completeness-and-open-targets"}[module 3 §3.10]).

For `Probability.complement_val` above, the English is: “For every real value `p` in `[0, 1]`, the underlying value of `p.complement` is `1 - p`.” Membership in `[0, 1]` is carried by `Probability`. There is no additional hypothesis. The return type supplies the result's bound, while the theorem identifies its value. These are different guarantees even though this definition supplies both.

*Intent Statement*: Every public declaration used as evidence for a material normative claim MUST carry, in its declaration docstring, a labelled Intent section: an ATX heading whose text is exactly `Intent` (for example `# Intent`; one to six `#`, no closing sequence), followed by nonempty text before the next heading of equal or higher level (at most as many `#`). Deeper subsection headings stay inside the section, so text under them counts; a heading line itself is not text. The intent statement records what the claim must establish and why, stated from the source mathematics or program specification rather than derived from the elaborated declaration, including deliberate exclusions and limits. The explanation states what the formal statement says. The intent states what the formal statement is required to say. Because the intent is not derived from the declaration, comparing the two is not circular. Placing it in the attached docstring binds it to that exact declaration through Lean's documentation metadata. Prefer a level-one heading: a top-level Verso docstring header must be `#`.

Check fidelity in both directions. Compare the explanation with the elaborated declaration. Then compare the declaration and its explanation with the intent statement, which is the source mathematics or program specification side of the comparison. A checked proof establishes its formal proposition. Semantic review determines whether the proposition expresses the intended problem as the intent statement records it. Resolve disagreements by correcting the prose, the statement, or both. Changing the intent changes the requirement; do not weaken it merely to match the formal statement.

A faithful explanation of a wrong statement faithfully restates the wrong statement. For `sort_correct : ∀ l, Sorted (sort l)`, the explanation "for every list, `sort l` is sorted" passes the fidelity test against the declaration. An intent statement requiring that sorting return a sorted permutation of its input exposes the omission: `fun _ => []` satisfies the declaration. Presence of an Intent section is mechanically checkable; whether it says what the requirement owner needs, and whether the declaration meets it, remain semantic review. A clause stated in Lean and proved to follow from the declaration is checked for that formal statement; whether the formal statement says what the English clause says is still semantic review. A probabilistic screen of the comparison can direct review to likely mismatches, but its result is neither proof nor a completed review.

# 5.3 Module Documentation
%%%
tag := "53-module-documentation"
number := false
%%%

*Requirement*: Every module in a claimed surface MUST have a module docstring identifying the material declarations and assumptions relevant to that surface. Explain the module's role and any dependencies needed to understand those claims. Hierarchical grouping is a navigation recommendation. Actual module dependencies come from imports, with Lake defining build targets and discovered surfaces.

Use `/-- ... -/` for a declaration docstring and `/-! ... -/` for module documentation. The module docstring MUST come directly after the imports, as the Lean community requires (in a file with a `module` header, before any `public section`; RG5001 checks this). Follow the form of Mathlib's [documentation requirements](https://leanprover-community.github.io/contribute/doc.html): start it with a first-level `#` title followed by a summary, and use the community's section names. Regula adds one section, *Assumptions and dependencies*, which carries the assumptions this requirement asks for. Adapt the following template to the actual module. Keep the sections that help readers understand it, and replace the placeholders with its declarations and claims.

```lean
/-!
# Module title

Summary: the purpose and scope of this module.

## Main definitions

- `definitionName`: the object or operation defined.

## Main statements

- `theorem_name`: its exact result and material hypotheses.

## Assumptions and dependencies

Definitions or interfaces needed to interpret the results, and any relevant
foundation or execution boundary. Link to the declarations that supply them.

## Notation

Notation the module introduces, if any.

## Implementation notes

Reasons for non-obvious choices.

## References

Sources needed to understand the mathematics.

## Tags

Search keywords.
-/
```

For examples from this repository, see {repo "lean/Audit/DocClaims.lean"}[`Audit.DocClaims`] and {repo "lean/Audit/DocPrelude.lean"}[`Audit.DocPrelude`]. The former lists its mathematical objects and results and distinguishes its existence and joint-satisfiability witnesses from external-system claims. The latter describes the shared types imported by documentation examples and the operations their APIs expose.

Module documentation can summarize shared assumptions and link to declaration details. Omit repeated signatures or lists of transitive imports when they add no explanatory value. Any reported foundation strength must match the exact dependencies described in {ref "45-foundation-strength-kernel-only-choice-free-standard-logical"}[module 4 §4.5].

# 5.4 Proof Readability
%%%
tag := "54-proof-readability"
number := false
%%%

*Recommendation*: Decompose complex proofs into well-named lemmas when this makes their mathematical argument easier to follow or reuse. Add comments for reasoning that statements and proof steps do not make clear. A short proof using a matching library theorem may need no comment.

The kernel checks the elaborated proof term, not the explanation of its strategy. Review comments against the proof. They must describe the argument accurately. Any additional material mathematical claim presented as established requires formal support. Design rationale and teaching notes need not be recast as theorem statements.

*Example - Explaining an Induction Invariant*:

The helper below states that union folding preserves membership in its initial accumulator. Generalizing the accumulator makes the induction hypothesis apply after each update. The second theorem uses that helper when an element comes from the head set and induction when it comes from the tail. The proof illustrates this decomposition. Here `Set α` represents sets by predicates. Union membership is logical disjunction, and the proof needs no equality decision procedure on the element type.

```lean
import Mathlib.Data.Set.Basic

/-- Union folding preserves every member of the initial accumulator. -/
theorem mem_foldl_union_of_mem {α : Type} {x : α} (l : List (Set α)) (acc : Set α)
    (hx : x ∈ acc) : x ∈ l.foldl (· ∪ ·) acc := by
  -- The next step uses acc ∪ hd, so induction must allow a new accumulator.
  induction l generalizing acc with
  | nil => exact hx
  | cons hd tl ih =>
    rw [List.foldl_cons]
    exact ih (acc ∪ hd) (Set.mem_union_left hd hx)

/-- Every member of every input set belongs to the union-fold result,
for any initial accumulator. -/
theorem mem_foldl_union_of_mem_of_mem {α : Type} {x : α} {s : Set α} {l : List (Set α)}
    (init : Set α) (hs : s ∈ l) (hx : x ∈ s) : x ∈ l.foldl (· ∪ ·) init := by
  induction l generalizing init with
  | nil => simp at hs
  | cons hd tl ih =>
    rcases List.mem_cons.mp hs with rfl | h_tail
    · exact mem_foldl_union_of_mem tl _ (Set.mem_union_right init hx)
    · exact ih (init ∪ hd) h_tail
```

The theorems establish membership preservation for arbitrary initial sets. Exact contents additionally requires the converse: every result member belongs to the initial accumulator or an input set. Establish that direction from the actual fold definition or a suitable checked theorem.

*Example - Reusing a Library Result*:

Core's `String.append_eq_left_iff` states that appending a suffix leaves a string unchanged exactly when the suffix is empty. It provides the entire argument here:

```lean
import Init.Data.String.Lemmas.Basic

/-- Appending a nonempty suffix changes every string. -/
theorem String.self_ne_append_of_ne_empty (s suffix : String) (h : suffix ≠ "") :
    s ≠ s ++ suffix := by
  intro h_eq
  exact h (String.append_eq_left_iff.mp h_eq.symm)
```

Use comments to explain a mathematical choice, a strengthened induction hypothesis, or a necessary case distinction. Prefer names and proof structure when they convey the point. Remove comments that only repeat the adjacent tactic.

# Summary of Documentation Standards
%%%
tag := "summary-of-documentation-standards"
number := false
%%%

* Public declarations supporting material normative claims have accurate docstrings.
* Explanations preserve the claim's quantifiers, assumptions, conclusion, and relevant limits, and identify its formal source.
* Each material claim's docstring carries a written Intent section, the requirement-side target its explanation and declaration are compared against.
* Module documentation identifies the material declarations, assumptions, and relationships readers need.
* Proof structure and comments make the mathematical argument easier to follow without adding unsupported claims.

Documentation supports semantic review. Assess its accuracy using the checked definitions and proofs.
