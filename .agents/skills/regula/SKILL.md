---
name: regula
description: Regula, the strict standard that this project's Lean code and proofs must meet. Use before writing or changing Lean definitions, theorems, proofs, lakefile or foundation_manifest.json, or Lean examples in Markdown, and when `lake lint` reports an RG rule ID.
---

# Regula agent briefing

This project's Lean code and proofs must meet the Regula standard. Apply these rules while writing Lean, not only after the linter runs. This is the complete mechanical rule set of the installed Regula version, ordered for writing code.

- Check with `lake lint` (`lake lint -- --fresh` for a fresh-source audit). Exit codes: 0 ACCEPTED, 1 VIOLATION, 2 INVALID CONFIGURATION, 3 INCOMPLETE.
- `lake lint -- --json-out tmp/regula.json` also writes every finding with its location, remedy and rule guidance (result schema 4). When a stage did not complete, `complete` is false and `stagesNotRun` names the stages, so fixing these findings can reveal more.
- A finding names its rule ID, what is wrong and where, and the fix. The first finding of each rule adds why, common rewrites and a compliant example (or, where the checked files are qualification inputs, the correction). `lake exe regula explain <ID>` prints the full rule offline; `lake exe regula rules` lists all rules.
- No option, attribute or flag waives a rule on a claimed surface. Do not disable a Lean warning, weaken a statement, or drop a registration to pass.
- Follow the Lean community's style, naming and documentation conventions (standard §6.7). Every claimed target enables `linter.missingDocs` (document every definition) in its `leanOptions`, with the other options RG2006 checks; `lake lint` rejects their warnings. Run Batteries' linters with `lake build && lake exe runLinter`. Disable a community linter only for a single declaration, where its guidance allows, with the reason; that never discharges a rule.
- Passing is mechanical: a theorem must still state the intended claim, with its hypotheses and limits, which review checks.

## Every declaration

Applies to each definition, theorem and instance in a claimed module.

### RG1002 Proof holes are forbidden

No owned declaration depends on `sorryAx`: no `sorry`, `admit` or unfinished proof, directly or through an import.
Fix: Complete the proof. If the statement is an open problem, define it as a `Prop` and state results conditionally on it instead of asserting it.

```lean
/-! # Reflexivity

Reflexivity for every natural number. -/
theorem reflexive (n : Nat) : n = n := rfl
```

### RG1001 Project logical axioms are forbidden

A claimed module declares no logical `axiom`: every assumption is a hypothesis or a proof-bearing field.
Fix: Turn the assumption into a hypothesis (a binder or a proof-bearing structure field) of the results that need it, or replace the axiom with a proof.

Compliant example: as RG1002.

### RG1004 Compiler-trusting proofs require separate classification

Claimed declarations use no compiler-trusting proof: no `native_decide`, `decide +native`, `bv_decide`, `Lean.trustCompiler`, `Lean.ofReduceBool` or `Lean.ofReduceNat`.
Fix: Prove the same statement with a kernel-checked proof, for example `decide` (kernel reduction), `rfl` or an ordinary proof.

```lean
import Init
/-! # Concrete facts

The same concrete facts have kernel proofs. -/
theorem equal : (2 : Nat) = 2 := rfl
theorem gcdValue : Nat.gcd 1071 462 = 21 := by decide
theorem commute (x y : BitVec 8) : x * y = y * x := BitVec.mul_comm x y
```

### RG1006 Unsafe and partial declarations require exact helper authentication

Claimed modules declare nothing `unsafe` or `partial`; recursion is structural or proved terminating.
Fix: Write a safe, terminating definition (structural recursion or `termination_by`), or move the unsafe/partial code out of the claimed surface.

```lean
/-! # Identity

Identity on natural numbers. -/
/-- The identity function on natural numbers. -/
def identity (n : Nat) : Nat := n
```

### RG1005 Transitive axioms must fit the selected profile

Each declaration's exact transitive axiom set fits the `claim` of its surface in `foundation_manifest.json`.
Fix: Prove the same statement with fewer axioms, or deliberately raise the surface's claim in `foundation_manifest.json` and update its rationale.

```lean
/-! # Reflexivity

The same universally quantified reflexivity with an empty axiom set. -/
theorem reflexive (n : Nat) : n = n := rfl
```

### RG1003 Unknown transitive axioms are forbidden

Every transitive axiom of an owned declaration, including one from an import, is `propext`, `Quot.sound` or `Classical.choice`.
Fix: Find where the axiom enters (often an imported dependency), and replace that dependency or its axiom with a proof or a hypothesis.

Compliant form: The dependency proves the same reflexivity statement instead of declaring it as an axiom, and the file that imports it is unchanged.

### RG2003 Claimed source must elaborate warning-free

Every claimed module elaborates from source without errors or warnings; Lean's default warnings stay enabled, and disabling a linter never discharges what it checks.
Fix: Fix the compiler diagnostic at its source. Never disable a Lean default warning; disable a community linter only for one declaration, where its guidance allows, with the reason.

Compliant example: as RG1006.

### RG2005 Required admission and source evidence must be complete

Owned declarations pass kernel replay from the exact frozen sources; no metaprogram adds unchecked declarations.
Fix: Remove the construction that bypasses kernel checking (or the source change during the run), then run the project command that collects the missing evidence.

Compliant example: as RG1002.

## Documentation in Lean sources

Applies to claimed modules and `@[regula_material]` declarations.

### RG5001 Claimed modules need a leading module docstring and no repeated import

Every claimed module has a module docstring (`/-! … -/`) as its first command after the imports, and its header repeats no import with the same modifiers.
Fix: Add a module docstring that identifies the module's material declarations and assumptions, directly after the imports and before any `public section`, and delete repeated imports.

```lean
/-! # Reflexivity

Reflexivity for every natural number; no additional assumptions. -/
theorem reflexive (n : Nat) : n = n := rfl
```

### RG5002 Registered public material declarations require docstrings

Every public `@[regula_material]` declaration has a docstring stating its purpose, hypotheses, result and boundary.
Fix: Add a docstring stating the declaration's formal purpose, domain and hypotheses, result and boundary, with a labelled `# Intent` section (RG5003).

```lean
import Regula.MaterialClaim
/-! # Reflexivity

Reflexivity for every natural number; `reflexive` supplies its evidence. -/
/-- Every natural number equals itself, without additional hypotheses.

# Intent
Equality on natural numbers must be reflexive for every value, with no side condition. -/
@[regula_material] theorem reflexive (n : Nat) : n = n := rfl
```

### RG5003 Registered public material declarations require an Intent section

Every public `@[regula_material]` docstring has a nonempty `# Intent` section stating the requirement the claim must meet.
Fix: Add a heading whose text is exactly `Intent` to the docstring, followed by the requirement the claim must meet, stated from the source mathematics or specification.

```lean
import Regula.MaterialClaim
/-! # Reflexivity

Reflexivity for every natural number; `reflexive` supplies its evidence. -/
/-- Every natural number equals itself, without additional hypotheses.

# Intent
## Requirement
Equality on natural numbers must be reflexive for every value, with no side condition. -/
@[regula_material] theorem reflexive (n : Nat) : n = n := rfl
```

## Executable code

Applies to `ExecutableContract` registrations and code reached from executable roots.

### RG1007 Executable contracts require supported closed evidence

Each `ExecutableContract f R` is closed and names a safe, computable implementation `f`, with its complete domain inside `R`.
Fix: Register the named implementation itself and put its complete domain inside the predicate: `theorem c : ExecutableContract f (fun g => ∀ x, P x (g x))`.

```lean
import Regula.Contract
/-! # Identity

Identity on natural numbers, with its full-domain contract. -/
/-- The identity function on natural numbers. -/
def identity (n : Nat) : Nat := n
theorem contract : Regula.ExecutableContract identity (fun f => ∀ n, f n = n) :=
  ⟨fun _ => rfl⟩
```

### RG3002 Checked execution requires admitted correspondence

Under `"execution": "checked"`, every reachable replacement or `extern` boundary has a kernel-checked equality with its reference.
Fix: Prove the replacement equal to its reference on the complete domain, or remove the trusted boundary, or claim `report` execution instead and keep the boundary reported.

```lean
/-! # Identity

The identity specification and replacement agree on every input. -/
/-- The replacement code for `identity`: it computes `0 + n`. -/
def alternative (n : Nat) : Nat := 0 + n
/-- The identity on natural numbers; compiled code runs `alternative` instead. -/
@[implemented_by alternative] def identity (n : Nat) : Nat := n
theorem correspondence (n : Nat) : identity n = alternative n := (Nat.zero_add n).symm
```

### RG3001 Execution closure must have no unresolved paths

Every path in an executable root's execution closure resolves; no metaprogram hides replacement history.
Fix: Remove the construction that prevents the analysis (for example a metaprogramming command such as `run_cmd` in the module), or make the missing compiled code available, then rerun.

```lean
import Lean
/-! # Identity

Identity and its extensionally equal replacement. -/
/-- The replacement code for `identity`: it computes `0 + n`. -/
def alternative (n : Nat) : Nat := 0 + n
/-- The identity on natural numbers; compiled code runs `alternative` instead. -/
@[implemented_by alternative] def identity (n : Nat) : Nat := n
theorem correspondence (n : Nat) : identity n = alternative n := (Nat.zero_add n).symm
```

## Project configuration

Applies to `foundation_manifest.json`, the Lake options of claimed targets and the build environment.

### RG2002 Configuration must classify the complete Lake surface

`foundation_manifest.json` is valid schema 2 and classifies every root `lean_lib` and `lean_exe` exactly once, each executable alike with any library that contains its root module.
Fix: Fix the manifest: exactly the four top-level keys, one entry per root `lean_lib` and `lean_exe` (claimed or excluded with a rationale), valid `claim` and `execution` values, and an executable whose root belongs to a library classified with that library: in its surface, or excluded with it.

```json
{
  "schema-version": 2,
  "surfaces": [
    {
      "library": "Example",
      "executables": ["cli"],
      "claim": "standard-logical",
      "execution": "report",
      "rationale": "Exact fixture claim, with the executable whose root the library contains."
    }
  ],
  "excluded-libraries": [],
  "excluded-executables": []
}
```

### RG2006 Claimed targets must build with the community configuration

Claimed targets' `leanOptions` set auto-implicits off, `linter.missingDocs` on, no linter off past §6.7 exclusions, with Mathlib its standard set on, header linter off or licensed; no `-D` undoes it.
Fix: Set the target's Lake `leanOptions`: `autoImplicit` and `relaxedAutoImplicit` false, `linter.missingDocs` true and, with Mathlib, the standard set and its three §6.7 exclusions; remove other linter disables and each `-D` extra `lean` argument that overrides these options.

```lean
import Lake
open Lake DSL

package rule_examples where
  leanOptions := #[⟨`linter.missingDocs, true⟩, ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Example
```

### RG2004 Owned coverage must match the exact Lake inventory

Every owned module belongs to exactly one manifested library, and no claimed module imports an excluded or checker-probe module.
Fix: Remove the forbidden import, or add the module to the intended claimed library's globs, so every owned module belongs to exactly one classified target.

Compliant example: as RG1002.

### RG2001 The declared Lean environment must be available

The audit runs in the declared environment: Lake loads the workspace with the pinned toolchain and resolves every dependency.
Fix: Repair the workspace so Lake can load it with its exact toolchain and dependencies, then rerun the same command.

Compliant form: The correction removes a Lake dependency that cannot be resolved (the violating workspace adds `require unavailable from "./missing"`); the Lean source is unchanged.

## Lean examples in Markdown

Applies to `lean` fences in the checked documentation tree.

### RG4002 Positive examples require warning-free elaboration and admission

An unmarked `lean` fence in the checked docs elaborates verbatim and warning-free and passes the declaration and axiom rules.
Fix: Make the example correct as printed: fix its errors or warnings, and make its declarations satisfy the same rules as project code.

````markdown
```lean
/-! # Reflexivity

Reflexivity for every natural number. -/
theorem reflexive (n : Nat) : n = n := rfl
```
````

### RG4003 Negative examples require completed intended rejection

A `lean-fail` fence fails to elaborate with one error message that matches its whole pattern.
Fix: Make the example fail for exactly the documented reason, adjust the pattern to match one real error message, or remove the marker if the example is valid.

Compliant example: as RG4002.

### RG4004 Teaching examples require authenticated compiler classification

A `lean-trusted-compiler` fence elaborates warning-free and contains an authenticated compiler-trusting declaration.
Fix: Use the marker only for an example that demonstrates `native_decide`, `decide +native` or `bv_decide` (or another authenticated compiler-trusting mechanism); otherwise remove it.

Compliant example: as RG4002.

### RG4001 Documentation fences must have a valid classification

Each `lean-fail` or `lean-trusted-compiler` marker sits immediately before the `lean` fence it classifies, and every fence is closed.
Fix: Put each `lean-fail` or `lean-trusted-compiler` marker immediately before the `lean` fence it classifies, with a valid pattern, and close every fence.

Compliant example: as RG4002.

