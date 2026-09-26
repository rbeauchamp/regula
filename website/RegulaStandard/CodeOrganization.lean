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

Lean code organization determines import dependencies, name resolution, and client-accessible information. This module separates these language features from guidance on layering, naming, and file structure. The rules enforce documented Lean boundaries. Design guidelines clarify those boundaries for readers.

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

*Linter discipline*: Every warning emitted while elaborating a conforming surface is an error under {ref "83-clean-elaboration-and-diagnostics"}[module 8 §8.3]. Setting `warningAsError := false` does not bypass audit checks. Turning off a linter can prevent its diagnostic but does not establish the underlying property. Applicable semantic matrix rows still require their own evidence.

# 6.3 Naming Conventions
%%%
tag := "63-naming-conventions"
number := false
%%%

*Recommendation*: Use descriptive names consistent with the surrounding Lean library. Common Mathlib conventions include:

:::table +header
*
  * Declaration
  * Example naming style
*
  * Type or class
  * `ProposalVote`, `ConsentState`
*
  * Function or value
  * `calculateScore`, `votingPower`
*
  * Theorem
  * `vote_count_bounded`, `consensus_implies_quorum`
:::

These styles are readability conventions. Capitalization is not a proof obligation. Existing library names do not need to be changed to match a single convention.

Namespace placement affects name resolution. A file named `Project/Core/Entity.lean` does not automatically place its declarations in `Project.Core.Entity`. Use an explicit `namespace` when that prefix is intended. One namespace may span several files, and one file may contribute to several namespaces. Opening a namespace makes eligible names available without their prefix but does not grant access to hidden declarations. The `protected` keyword excludes a visible declaration from blanket `open Namespace`; explicit `open Namespace (name)` or renaming can still introduce an unqualified name. Its qualified name remains available.

# 6.4 Import Discipline
%%%
tag := "64-import-discipline"
number := false
%%%

*Requirement*: Every claimed module MUST elaborate in the environment supplied by its imports and language settings on the declared toolchain. The audit MUST discover it through the claimed Lake targets, including any claimed standalone executable roots, as specified in {ref "82-define-surfaces-through-lake-semantics"}[module 8 §8.2].

Use imports to make significant dependencies explicit. Import minimality, direct versus transitive spelling, sorting, and grouping are recommendations, not requirements. Choose a consistent arrangement that fits the project. Mathlib and project imports do not require a particular order.

Imports supply declarations, instances, syntax, and elaboration extensions. Changing imports can change how the same source text elaborates. An unused import does not add an axiom to every declaration by itself. Each declaration's elaborated logical dependencies determine the exact transitive axiom set ({ref "85-proof-completeness-and-foundation-strength"}[module 8 §8.5]).

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

structure Entity where
  reputation : Rat
  stake : Rat
  isActive : Bool

/- This implementation detail is declared `private`; an external module cannot
   resolve the source-level name `Project.Core.calculateWeight`. The body can
   still participate in reduction through the public definition. Representation
   abstraction is a separate boundary. -/
private def calculateWeight (e : Entity) : Rat :=
  (e.reputation * e.stake) / 100

/-- Public API: visible outside the namespace. -/
def votingPower (e : Entity) : Rat :=
  if e.isActive then calculateWeight e else calculateWeight e / 2

end Project.Core
```

In files with a `module` header, declarations are private by default. Use `public` or `public section` to export names. For ordinary module-system clients, a public `def` does not necessarily expose its body; `@[expose]` makes the body available to unfold, and exported theorems may provide equations without exposing it. Explicit `import all` supplies private source names and unexposed definition bodies. Cross-package rejection of this import is disabled on Lean 4.34.0, so package membership alone does not enforce the exclusion. Legacy clients can also unfold otherwise unexposed definitions, although their private source-name resolution differs. Neither access mode makes an `opaque` body definitionally reducible. State the exact client context of a verified boundary. See [Lean's module documentation](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/) for general import and exposure rules; the supported toolchain remains authoritative.

*Opaque Carriers Need an API:*

An isolated opaque carrier hides its defining type even from subsequent declarations in the same file. Its declaration alone supplies no conversion from the defining type:

```lean (fails := "(?s)Type mismatch.*String.*HiddenString")
opaque HiddenString : Type := String

def hide (s : String) : HiddenString := s
```

Use parameters to represent a universally abstract model ({ref "24-abstract-mathematical-models"}[module 2 §2.4]). When a concrete implementation must support an abstract API, initialize the carrier and its operations together.

## 6.5.1 Opaque Packages
%%%
tag := "651-opaque-packages"
number := false
%%%

An opaque package can enforce a representation boundary without a logical axiom. It exposes a carrier and selected operations through the package's fields, while an implemented `opaque` definition prevents reduction to the concrete package. Unlike a public inductive wrapper, this carrier has no generated recursor revealing a payload. Use the pattern when the claim requires that abstraction; it is not a universal replacement for concrete types.

The following pattern is mirrored in {repo "lean/Audit/DocPrelude.lean"}[`Audit.DocPrelude`]:

```lean
/- This fence restates `Audit.DocPrelude` under a local namespace so it
   elaborates standalone. -/
namespace AbstractData

/-- The public package exposes a carrier and a construction operation. -/
structure OpaqueDataPackage where
  Carrier : Type
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

-- Attack 1: direct construction contrary to the documented package operation.
def forged : Glossary.OpaqueData := "attacker"
```

```lean (fails := "Type mismatch")
import Audit.DocPrelude

-- Attack 2: direct payload recovery contrary to the documented API.
def steal (x : Glossary.OpaqueData) : String := x
```

The corresponding repository fixtures are {repo "lean/Fixtures/Mutations/OpaquePrivateAccess.lean"}[`OpaquePrivateAccess`], {repo "lean/Fixtures/Mutations/OpaqueConstruct.lean"}[`OpaqueConstruct`], and {repo "lean/Fixtures/Mutations/OpaqueObserve.lean"}[`OpaqueObserve`].

Construction through the exported operation succeeds:

```lean
import Audit.DocPrelude

/-- Example: a message with abstract content for which this model has no
    observer (`Glossary.OpaqueData`, pattern shown above). -/
structure Message where
  timestamp : Glossary.Time
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

# Summary of Code Organization
%%%
tag := "summary-of-code-organization"
number := false
%%%

* Imports form an acyclic graph; optional layers guide its design.
* Claimed Lake targets determine audit coverage, including declared executable roots.
* Module documentation explains material declarations and assumptions; naming and layout conventions aid navigation.
* Namespaces, private names, body exposure, and opaque representations provide different boundaries. State and check the boundary actually claimed.
