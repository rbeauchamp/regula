# Lean Review Lens Contracts

Select materially relevant sections; independence follows AGENTS.md for delivery reviews, while the
number of assignments follows distinct risks. Combine compatible questions without merging
the author and reviewer roles. In full-compliance mode reconcile assignments against every
current standard module 8 ID and the repository's `DOGFOOD-*` rows
(`docs/guides/contributing.md`): these focus lists are navigation, not an alternate checklist.
A reviewer inspects one frozen subject and returns findings with coverage evidence or `CLEAN`;
it does not edit shared files, launch duplicate reviewers, or silently claim uninspected rows.

Specification/refinement reasoning usually combines lenses 1–2; Lean/kernel/compiler reasoning
usually combines 3–5. Assign them independently when both risks are material. Include lens 6 and
the closure questions in those assignments as relevant. For skills/handoff-only changes, review
their actual routing, permissions, consistency, and completion effects; Lean-specific lenses
apply only to Lean claims actually changed. Missing Lean scope is not missing independence.

For a **Lean Semantic Fidelity and Design Economy** review, combine the relevant questions
from lenses 1–3 with closure question D. Apply them within the requested review scope and
existing assignments; a named perspective does not require an additional reviewer.

## Primary lenses

### 1. Claim Strength and Normative Scope

Matrix: `SCOPE-01`–`SCOPE-05`, `THEOREM-01`, `THEOREM-05`–`THEOREM-10`, `DOC-01`, `DOC-02`.

Compare prose with exact elaborated theorem types, quantifiers, hypotheses, definitions, and
transitive dependencies. Attack external-system promotion, termination/complexity conflation,
testing-as-proof, arbitrary universal policy, and documentation stronger than Lean.
Derive required proof obligations from the exact claim: initialization, preservation, and
composition are not universal prerequisites for every relation or cost theorem. Distinguish
Lean's guarantees from policies this standard chooses to impose, and require a Lean-specific
rationale for the latter.

Review input–output meaning, success/refusal and frame conditions, composition, and links to
the actual executable definitions. For refinement, examine initialization, simulation,
observation relations, and finite-prefix transfer; distinguish stuttering safety from
progress/fairness/liveness. For research, compare the elaborated statement with the intended
mathematics and preserve the difference between a complete conditional result and an unproved
unconditional target. Apply the governing issue's acceptance, when present, without treating proposed rules as
already-adopted normative text.

### 2. Dependent Types, Lawful APIs, and Non-Vacuity

Matrix: `TYPE-01`–`TYPE-06`, `THEOREM-02`–`THEOREM-04`, `DOGFOOD-04`.

Try to construct excluded values, swap semantic types, violate class laws, call restricted
domains, bypass smart constructors, observe abstract representations, and satisfy statements
vacuously. Compare every custom structure, class, theorem, or alias with pinned Core/Mathlib.
Check explanations of requiring evidence, constructing evidence, deciding a predicate, and
establishing an invariant; these are distinct operations. Identify what evidence is supplied,
what must be computed, and what downstream use actually requires.

Distinguish unary admitted-value invariants from reachability/history relations; inspect every
admission and write boundary. Proof-producing validation can establish a type invariant, but
that invariant alone need not establish functional completeness. Demand inhabitance or
reachability only at the strength claimed; a deliberately conditional lemma need not prove
its own antecedent. Inspect the actual law-bearing class/mixin and selected instances rather
than relying on class names or an example that never synthesizes its advertised interface.

### 3. Foundations, Declarations, and Computation

Matrix: `FOUND-01`–`FOUND-05`, `DECL-02`–`DECL-04`, `COMP-01`–`COMP-04`, `BUILD-02`, `BUILD-03`, `DOC-02`.

Inspect exact `ConstantInfo`, proposition-valued definitions/instances, transitive axiom sets,
foundation profiles, noncomputability, opacity, unsafe/partial forms, native proof axioms,
runtime replacements, extern/FFI, private/internal-looking declarations, and spoofed generated
names. Names alone never authorize an exemption.
Review the explanation as well as the metadata: distinguish elaboration and tactic execution,
kernel checking, compilation, and runtime behavior. Account for proof erasure and computational
relevance. Locate noncomputability in the relevant definition or operation rather than treating
a type's name as a blanket classification of every function over it.

Separate logical dependencies from the pinned compiler's reachable execution graph, including
proof-backed simplifications, replacements, and their imported/chained targets. A checked
correspondence must inhabit the exact required equality with its real dependent domain and
universes; extra theorem-only hypotheses are not discharged by binder counting. Logical
equality does not prove a native extern implementation. Preserve the supported built-in
evaluator/semantic-attribution boundary; do not expand into arbitrary process compromise.

### 4. Lake Surface, Elaboration, and Fresh Kernel Coverage

Matrix: `DECL-01`, `DECL-03`, `DECL-04`, applicable `MUT-03`–`MUT-05`, `DOGFOOD-01`,
`DOGFOOD-02`, `DOGFOOD-05`, `BUILD-01`, `BUILD-04`.

Derive modules from Lake configuration, not filesystem/name guesses. Attack unimported modules,
lookalike prefixes, contamination, stale `.olean` reuse, incomplete roots, warnings disabled by
source, and, only when separately claimed, differences between `lake build` and
`leanchecker --fresh` serialized-graph coverage.

For complete applications, inspect required executable roots and explicit proof-requiring
contracts. Discovering every declaration that remains is not detection of a deleted required
contract; a name/count match alone is not verification of its exact expected proposition.

### 5. Documentation Checker and Mutation Sensitivity

Matrix: `DOC-03`–`DOC-05`, applicable checker-qualification rows `MUT-01`–`MUT-04`,
`DOGFOOD-03`, `DOGFOOD-05`.

Verify raw fences compile before instrumentation, nested docs are scanned, markers fail closed,
warnings/holes/axioms cannot be suppressed, trusted examples are not conforming, and every
advertised checker behavior has one positive control plus an independent single-fault mutation
through the public entrypoint.

Require intended-reason detection: a missing-contract mutation masked by an injected axiom
does not qualify contract completeness. Exercise the semantic claim surrounding a fence,
including instance synthesis and actual foundation output, rather than equating compilation
with truth of its prose. Qualification controls are diagnostics, not universal soundness proofs.

### 6. Dogfooding, Modules, Namespaces, and Reuse

Matrix: `TYPE-05`, `DOC-01`, `DECL-01`, `DOGFOOD-01`–`DOGFOOD-05`.

Audit the repository as an ordinary consumer: module docstrings, namespaces, exact visibility,
Core/Std/Mathlib reuse, consistency among prose/fixtures/diagnostics/status, positive/negative
isolation, and no exemptions created only to make the standard's own examples pass.

## Focused closure questions

Apply these once to the substantive changed surface. They may be handled in one combined pass;
use separate reviewers only when the change or risk justifies them.

### A. Core/Mathlib Reuse and Statement Economy

Find reimplemented types, classes, functions, theorems, or proof steps already available in the
pinned Lean/Mathlib environment; unnecessary wrappers; and statements made more complex than the
claim requires. Return only high-confidence replacements that preserve exact semantics, or
`CLEAN`.

### B. Proof and Checker Quality

Find masked mutations, compound fixtures, fail-open branches, unclassified metadata, diagnostics
stronger than detection, brittle source/name heuristics, duplicated normative rules, and proofs
whose structure obscures the exact claim. Return concrete repairs or `CLEAN`.

### C. Audit Efficiency Without Coverage Loss

Find repeated elaborations, avoidable full-environment allocations, serial independent checks,
or qualification work incorrectly placed in every adopter's conformance loop. Reduce redundant
work without weakening fresh-state, declaration, axiom, diagnostic, or applicable mutation
coverage. Do not trade semantic coverage for speed. Return concrete repairs or `CLEAN`.

Distinguish elaboration/search, proof construction, kernel replay/reduction, and native runtime
costs. Prefer structural arguments and reusable proofs; measure an irreducibly empirical cost
only with a smallest informative comparison, decision criterion, uncertainty, and budget.

### D. Semantic Fidelity and Explanatory Economy

Ask: could a technically competent reader follow this explanation and still acquire an
incorrect understanding of what Lean proves, checks, erases, or executes? Identify the passage
causing that misunderstanding and the smallest correction. Examine material implications and
omitted distinctions as well as literal assertions; ground technical findings in the pinned
semantics, declarations, or an appropriate checked example.

Read the conceptual progression as a whole. Does each example illustrate its surrounding
principle, and does the explanation use the simplest faithful abstraction? Move detail or
simplify only when doing so improves understanding without losing a required distinction.
Classify an optional teaching improvement as `LEAN QUALITY`; a missing explanatory sentence
is not automatically a normative violation. Return concrete findings or `CLEAN`, with the
scope inspected. This supplements the assigned lenses rather than creating another audit round.

## Finding format

```text
[P1|P2|P3] STANDARD NONCONFORMANCE — MATRIX-ID[, ...]
Location: exact file:line or declaration/module
Lean fact: exact elaborated type, metadata, axiom set, diagnostic, or module result
Failure: why the normative claim does not follow
Reproduction: minimal command or independent mutation
Repair criterion: observable condition that closes the finding
```

Use `LEAN QUALITY` or `REPOSITORY QUALITY` instead of `STANDARD NONCONFORMANCE` when the matrix
does not make the item normative. An issue acceptance defect can block delivery without being a
Lean-standard violation. Include coverage and unverified claims with CLEAN; do not turn absence
of findings into a claim of coverage that was never inspected.
