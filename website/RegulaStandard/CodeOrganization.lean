import VersoManual
import RegulaExample

open Verso.Genre Manual RegulaExample

#doc (Manual) "6. Code Organization" =>
%%%
tag := "6-code-organization"
file := "6-code-organization"
number := false
%%%

{pageAnchor}

# Overview
%%%
tag := "6-overview"
number := false
%%%

Lean code organization determines import dependencies, name resolution, and client-accessible information. This module separates these language features from guidance on layering, naming, and file structure. The rules enforce documented Lean boundaries. Design guidelines clarify those boundaries for readers. For style, naming, and documentation form, the standard adopts the Lean community's conventions and requires the community's own linters to enforce them (§6.7).

# 6.1 Dependency Structure
%%%
tag := "61-dependency-structure"
number := false
%%%

*Requirement*: Module imports MUST be acyclic. A project may use layers to organize dependencies, but this standard prescribes no layer hierarchy. Layer names do not themselves restrict imports.

*Rationale*: A fresh Lake build cannot resolve an import cycle. This restricts module dependencies, not mutually recursive definitions within a module.

*Import Cycle* (two files):

```leanSketch
-- A.lean
import B

-- B.lean
import A
```

If both modules require a common interface, define it in a third module and import that module from each. The following sketch illustrates the structure.

```leanSketch
-- Common.lean
structure AInterface where ...
structure BInterface where ...

-- A.lean
import Common
structure A where
  base : AInterface
  peer : BInterface

-- B.lean
import Common
structure B where
  base : BInterface
  peer : AInterface
```

Refactor to a shared interface when it provides the required functionality for each module. Replacing a concrete peer value with an interface can change the model's meaning. Declare mutually dependent inductive definitions together using `mutual` in a single file, subject to Lean's inductive-declaration rules.

# 6.2 Module Purpose and Linter Discipline
%%%
tag := "62-module-purpose-and-linter-discipline"
number := false
%%%

*Requirement*: Every module in a claimed surface MUST have a module docstring identifying its material declarations and assumptions, as specified in {ref "53-module-documentation"}[module 5 §5.3]. A single purpose is a useful design heuristic, not a kernel-checkable property.

*Linter discipline*: Every warning emitted while elaborating a conforming surface is an error under {ref "73-clean-elaboration-and-diagnostics"}[module 7 §7.3]. Setting `warningAsError := false` does not bypass audit checks. Turning off a linter can prevent its diagnostic but does not establish the underlying property. Applicable semantic matrix rows still require their own evidence.

Lean's default warnings, those Lean emits under its default options (including the core linters enabled by default, such as `linter.unusedVariables`), MUST NOT be disabled in a claimed module. Every other linter is a community linter here, however it came to run: a Lean core linter that is off by default and that the project enables (such as `linter.missingDocs`, §6.7), a linter that a dependency turns on for every importer (such as Mathlib's `linter.unusedTactic`), or one that the project enables from a dependency (such as Mathlib's standard set, §6.7). The Mathlib-repository linters that §6.7 turns off are outside the required baseline, so the project-wide setting §6.7 gives them is not a disable in this sense. Any other Lake option that turns a linter off for a claimed library or executable disables it in every module of that target, which neither kind of linter permits; {rule}[RG2006] rejects such an option. A community linter MAY be disabled for a single declaration where the community's own guidance allows that, with `set_option linter.NAME false in` before the declaration or `@[nolint NAME]` on it and a comment stating why. Such a disable removes that linter's finding for that declaration only. It establishes nothing about the property the linter checks and never discharges a requirement of this standard. The audit sees only emitted warnings, so review checks which linters a module disables.

# 6.3 Naming Conventions
%%%
tag := "63-naming-conventions"
number := false
%%%

*Recommendation*: Name declarations by the Lean community's naming conventions: Mathlib's [naming conventions](https://leanprover-community.github.io/contribute/naming.html) for code that depends on Mathlib, and Lean's [standard library naming conventions](https://github.com/leanprover/lean4/blob/master/doc/std/naming.md) for code that depends only on Lean core. Both use the same case rules:

:::table +header
*
  * Declaration
  * Case
  * Example
*
  * Proof: a theorem, or any term whose type is a proposition
  * `snake_case`
  * `quorum_of_consensus`, `successor_contract`
*
  * Proposition or type: a structure, class, inductive type, or `Prop`- or `Type`-valued definition
  * `UpperCamelCase`
  * `ProposalVote`, `HasQuorum`
*
  * Other term, such as a function or value
  * `lowerCamelCase`
  * `score`, `votingPower`
:::

A theorem's name describes its conclusion, and hypotheses follow `_of_`: `quorum_of_consensus : Consensus v → Quorum v`. Symbols take the dictionary spellings the Mathlib guide lists, such as `le`, `lt`, `mem`, `eq`, and `ne`. Name a function after the value it returns (`score`, not `calculateScore`). A contract registration such as `ExecutableContract` evidence is a proof, so its name is `snake_case`.

Naming is a readability convention, not a proof obligation, and no rule of this standard checks it. When extending an existing library, follow its conventions; renaming its public declarations is a separate compatibility decision.

Namespace placement affects name resolution. A file named `Project/Core/Entity.lean` does not automatically place its declarations in `Project.Core.Entity`. Use an explicit `namespace` when that prefix is intended. One namespace may span several files, and one file may contribute to several namespaces. Opening a namespace makes eligible names available without their prefix but does not grant access to hidden declarations. The `protected` keyword excludes a visible declaration from blanket `open Namespace`; explicit `open Namespace (name)` or renaming can still introduce an unqualified name. Its qualified name remains available.

# 6.4 Import Discipline
%%%
tag := "64-import-discipline"
number := false
%%%

*Requirement*: Every claimed module MUST elaborate in the environment supplied by its imports and language settings on the declared toolchain. The audit MUST discover it through the claimed Lake targets, including any claimed standalone executable roots, as specified in {ref "72-define-surfaces-through-lake-semantics"}[module 7 §7.2].

Use imports to make significant dependencies explicit. Import minimality, direct versus transitive spelling, sorting, and grouping are recommendations, not requirements. The one exception is the community convention that a claimed module MUST NOT repeat an import with the same modifiers (§6.7; {rule}[RG5001] checks it). Choose a consistent arrangement that fits the project. Mathlib and project imports do not require a particular order.

Imports supply declarations, instances, syntax, and elaboration extensions. Changing imports can change how the same source text elaborates. An unused import does not add an axiom to every declaration by itself. Each declaration's elaborated logical dependencies determine the exact transitive axiom set ({ref "75-proof-completeness-and-foundation-strength"}[module 7 §7.5]).

On the pinned Lean toolchain, a leading `module` header enables explicit public and private module scopes, and such a file can import only module-system files. A normal `import` makes imported public information available locally; `public import` also re-exports it to module-system clients. Files without the header use legacy behavior and load transitive private information. State both producer and client modes when claiming import availability or body exposure.

# 6.5 Visibility and Encapsulation
%%%
tag := "65-visibility-and-encapsulation"
number := false
%%%

*Requirement*: Every claimed abstraction or visibility boundary MUST match the mechanism Lean enforces. State the client context and test exclusions from a separate importing module with a successful control using the intended API. This rule does not prescribe which declarations an API should expose.

Distinguish three questions: whether a client can resolve a name, unfold a definition, or construct or observe a representation. A failed probe only shows that the attempted use fails. Inspect exported constructors, recursors, projections, coercions, operations, and equations before asserting a broader boundary.

The examples below use files without the `module` header. In that setting, an ordinary declaration is public by default while `private` hides its source-level name from importing modules. The private declaration remains usable elsewhere in its defining file after its declaration, even outside the namespace block. Its body can still affect reduction via a public definition.

```lean
import Mathlib.Data.Rat.Defs

namespace Project.Core

/-- A participant with a reputation, a stake, and an activity flag. -/
structure Entity where
  /-- The participant's reputation score. -/
  reputation : Rat
  /-- The amount the participant has staked. -/
  stake : Rat
  /-- Whether the participant is active. -/
  isActive : Bool

/- This implementation detail is declared `private`; an external module cannot
resolve the source-level name `Project.Core.weight`. The body can still
participate in reduction through the public definition. Representation
abstraction is a separate boundary. -/
private def weight (e : Entity) : Rat :=
  (e.reputation * e.stake) / 100

/-- Public API: visible outside the namespace. -/
def votingPower (e : Entity) : Rat :=
  if e.isActive then weight e else weight e / 2

end Project.Core
```

In files with a `module` header, declarations are private by default. Use `public` or `public section` to export names. For ordinary module-system clients, a public `def` does not necessarily expose its body; `@[expose]` makes the body available to unfold, and exported theorems may provide equations without exposing it. Explicit `import all` supplies private source names and unexposed definition bodies. Cross-package rejection of this import is disabled on Lean 4.34.0, so package membership alone does not enforce the exclusion. Legacy clients can also unfold otherwise unexposed definitions, although their private source-name resolution differs. Neither access mode makes an `opaque` body definitionally reducible. State the exact client context of a verified boundary. See [Lean's module documentation](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/) for general import and exposure rules; the supported toolchain remains authoritative.

*Opaque Carriers Need an API:*

An isolated opaque carrier hides its defining type even from subsequent declarations in the same file. Its declaration alone supplies no conversion from the defining type:

```lean (fails := "(?s)Type mismatch.*String.*HiddenString")
/-- A carrier whose defining type is hidden. -/
opaque HiddenString : Type := String

/-- Attempt to convert a string to the hidden carrier. -/
def hide (s : String) : HiddenString := s
```

Use parameters to represent a universally abstract model ({ref "24-abstract-mathematical-models"}[module 2 §2.4]). When a concrete implementation must support an abstract API, initialize the carrier and its operations together.

## 6.5.1 Opaque Packages
%%%
tag := "651-opaque-packages"
number := false
%%%

An opaque package can enforce a representation boundary without a logical axiom. It exposes a carrier and selected operations through the package's fields, while an implemented `opaque` definition prevents reduction to the concrete package. Unlike a public inductive wrapper, this carrier has no generated recursor revealing a payload. Use the pattern when the claim requires that abstraction; it is not a universal replacement for concrete types.

The following pattern is mirrored in {repo "audit/Audit/DocPrelude.lean"}[`Audit.DocPrelude`]:

```lean
/- This fence restates `Audit.DocPrelude` under a local namespace so it
elaborates standalone. -/
namespace AbstractData

/-- The public package exposes a carrier and a construction operation. -/
structure OpaqueDataPackage where
  /-- The abstract carrier type. -/
  Carrier : Type
  /-- Construct a carrier value from a string. -/
  wrap : String → Carrier

private def implementation : OpaqueDataPackage where
  Carrier := String
  wrap := id

/-- This is an implemented definition, not a logical axiom. Its body is not
kernel-reducible by clients. -/
opaque opaqueDataPackage : OpaqueDataPackage := implementation

/-- Clients see a type, not its implementation representation. -/
abbrev OpaqueData : Type := opaqueDataPackage.Carrier

/-- Documented constructor for the abstract carrier. -/
def OpaqueData.seal : String → OpaqueData := opaqueDataPackage.wrap

end AbstractData
```

Ordinary reduction does not identify `AbstractData.OpaqueData` with `String`. The package exports construction through `wrap` and the `OpaqueData.seal` convenience wrapper but no payload observer. The following independent clients use the corresponding package from `Audit.DocPrelude`.

The private implementation's source-level name is unavailable:

```lean (fails := "(?s)Unknown identifier.*Glossary.opaqueDataImplementation")
import Audit.DocPrelude

#check Glossary.opaqueDataImplementation
```

Direct construction and direct payload recovery also fail because the abstract carrier is not definitionally equal to `String`:

```lean (fails := "Type mismatch")
import Audit.DocPrelude

/-- Attack 1: direct construction contrary to the documented package operation. -/
def forged : Glossary.OpaqueData := "attacker"
```

```lean (fails := "Type mismatch")
import Audit.DocPrelude

/-- Attack 2: direct payload recovery contrary to the documented API. -/
def steal (x : Glossary.OpaqueData) : String := x
```

Construction through the exported operation succeeds:

```lean
import Audit.DocPrelude

/-- Example: a message with abstract content for which this model has no
observer (`Glossary.OpaqueData`, pattern shown above). -/
structure Message where
  /-- When the message was sent. -/
  timestamp : Glossary.Time
  /-- The message content, as an abstract carrier value. -/
  content : Glossary.OpaqueData

/-- Construct a message through the exported abstract-data operation. -/
def Message.ofString (timestamp : Glossary.Time) (payload : String) : Message :=
  ⟨timestamp, Glossary.OpaqueData.seal payload⟩
```

*Exact boundary*: Clients can construct, pass, and store carrier values, form equality propositions about them, and define constant functions on them. The package provides no proof that `wrap` is injective or any operation to recover a payload or decide equality. Provide or derive any additional operation or law the claim requires. Distinguish logical decidability from executable decision procedures.

This abstraction boundary applies to Lean's logical reasoning. It does not guarantee confidentiality for memory or generated code. An `opaque` definition with a computable body can execute. Logical irreducibility does not imply noncomputability. Accessing private module information or selecting an inhabitant does not make an opaque body definitionally reducible.

# 6.6 File Organization
%%%
tag := "66-file-organization"
number := false
%%%

*Recommendation*: Group declarations around a clear mathematical or program interface. Match namespaces to module names when it aids navigation, but do not treat the match as a language requirement. Apply the module documentation requirements in §6.2. No fixed section layout is required.

A `section … end` scopes variables, options, and other scoped commands. It does not create a namespace or hide the declarations inside it. Definitions remain available after the section ends, with the parameters Lean included during elaboration. A section variable that is not used or otherwise included need not become a parameter of every declaration.

# 6.7 Community Conventions and Linters
%%%
tag := "67-community-conventions-and-linters"
number := false
%%%

*Requirement*: A claimed surface MUST follow the Lean community's conventions for style, formatting, naming, and documentation form as the community's own linters enforce them. Every claimed library and claimed executable MUST enable these linters in its Lake `leanOptions`:

* *Lean's `linter.missingDocs`*, with value `true`. It reports every public definition, structure, class, inductive type, constructor, field, and syntax extension that has no docstring, the community's rule that every definition is documented.
* *Mathlib's standard linter set*, for a library that imports Mathlib: `weak.linter.mathlibStandardSet` with value `true`, the syntax linters Mathlib itself builds with (line length, tactic style, whitespace, and others).

A few linters of that set enforce policies of the Mathlib repository itself. A library that enables the set MUST turn them off in the same `leanOptions`, except that it MAY instead set the header linter to `true` there when it also names that linter's license line there (below); at the pinned Mathlib they are exactly these. An explicitly set linter option takes precedence over the set, and the `weak.` prefix lets Lake accept an option that Mathlib rather than Lean declares.

:::table +header
*
  * Option
  * Value
  * Why it is not adopted as it stands
*
  * `weak.linter.style.header`
  * `false`, or `true` with `weak.linter.style.header.license` set to the library's license line
  * It requires Mathlib's contribution header, a copyright line, a license line, and an authors line, in every module that the library root imports. The copyright and authors lines are the Mathlib repository's attribution policy. The license line defaults to the Mathlib repository's Apache 2.0 statement, and the option `linter.style.header.license` replaces it, so a library that keeps the linter on states its own license there, and otherwise turns the linter off.
*
  * `weak.linter.hashCommand`
  * `false`
  * It reports every `#` command that prints nothing, such as a passing `#guard`, as "not allowed in 'Mathlib'"; outside Mathlib a `#guard` is a checked build-time assertion.
*
  * `weak.linter.style.longFile`
  * `0`
  * Its 1500-line file limit is the Mathlib repository's file-size policy, and Mathlib documents no limit for downstream projects; `0` keeps it off.
:::

A library that keeps the header linter on names its own license line in the same `leanOptions`, for example:

```leanSketch
leanOptions := #[
  ⟨`weak.linter.mathlibStandardSet, true⟩,
  ⟨`weak.linter.style.header, true⟩,
  ⟨`weak.linter.style.header.license,
    "Released under the MIT license as described in the repository LICENSE."⟩,
  ⟨`weak.linter.hashCommand, false⟩,
  ⟨`weak.linter.style.longFile, .ofNat 0⟩]
```

A `lakefile.toml` cannot write that option beside the header linter in its `[leanOptions]` table, since a TOML key cannot both hold a value and have sub-keys. Such a library writes `leanOptions` as an array of `{name, value}` entries instead, which holds both options.

Turning off `linter.style.header` also turns off two community checks that the same linter makes: that the module docstring is the first command after the imports, on every module, and that no import is repeated with the same modifiers, on the modules that the library root imports. A library that leaves it on keeps both checks in the linter. Both remain requirements ({ref "53-module-documentation"}[module 5 §5.3], {ref "64-import-discipline"}[§6.4]), and {rule}[RG5001] checks both on every claimed module: its module docstring is the first command after the imports, and its header repeats no import with the same modifiers.

Two linters of the set whose messages mention Mathlib stay in the baseline. `linter.style.native` reports `native_decide` and `decide +native`, which conforming proof surfaces already exclude as compiler-trusting ({ref "34-foundation-strength-axioms-are-reported-never-assumed"}[module 3 §3.4], {ref "75-proof-completeness-and-foundation-strength"}[module 7 §7.5]). `linter.style.setOption` reports the development-only `debug`, `pp`, `profiler`, and `trace` options and an unscoped `maxHeartbeats` setting; a deliberate use takes the declaration-scoped disable of §6.2.

Their findings are ordinary build warnings, so the warning-free elaboration of {ref "73-clean-elaboration-and-diagnostics"}[§7.3] ({rule}[RG2003]) rejects every one of them. The standard enforces this community baseline by composing the community's linters with that rule; it restates none of their checks. Its own universal rules stay technical Lean rules (`SCOPE-04` in {ref "8-compliance-and-quality-audit"}[module 8]), and they are stricter where they apply: a registered material declaration needs a docstring that states its claim exactly ({ref "51-inline-documentation-requirements"}[module 5 §5.1–§5.2]; {rule}[RG5002], {rule}[RG5003]). {rule}[RG2006] checks the options from Lake's resolved configuration of every claimed library and executable: every target enables `linter.missingDocs`, a target of a surface that imports Mathlib enables the standard set with exactly the exclusions above, or with the header linter on and its license option set to a nonempty string in `leanOptions`, and no target turns off any other linter for all its modules (§6.2). {rule}[RG2006] does not read `set_option` commands in source, whose disables review checks as §6.2 describes.

The conventions are written in these guides:

* For code that depends on Mathlib, Mathlib's [library style guidelines](https://leanprover-community.github.io/contribute/style.html), [naming conventions](https://leanprover-community.github.io/contribute/naming.html), and [documentation requirements](https://leanprover-community.github.io/contribute/doc.html). The [contribution guide](https://leanprover-community.github.io/contribute/index.html) links them all.
* For code that depends only on Lean core, Lean's [standard library style guide](https://github.com/leanprover/lean4/blob/master/doc/std/style.md) and [naming conventions](https://github.com/leanprover/lean4/blob/master/doc/std/naming.md).

Where the two differ, for example `fun x ↦` against `fun x =>` or the capitalization of acronyms, follow the convention of the library the code builds on and apply it consistently. Following the guides where no enabled linter checks them, such as naming (§6.3), is RECOMMENDED.

Running *Batteries' environment linters* (`docBlame`, `simpNF`, `synTaut`, and others) is RECOMMENDED. They report through their own command (`#lint` or `lake exe runLinter`), not through build warnings, so {rule}[RG2003] does not see them; run them as a separate check beside `lake lint` ({ref "710-adopting-the-checker-in-another-project"}[§7.10]).

The community applies its linters with judgment. Where its guidance allows an exception, disable the linter for that one declaration as §6.2 describes; Lean's default warnings are never disabled. A community linter's pass establishes only what that linter checks: no property that another requirement of this standard needs, and a Regula rule never replaces the community's review of style.
