module

@[expose] public section

/-! # Sections of the standard that rules cite

The standard's only source is the Verso library `RegulaStandard` of the package in `website/`;
it is published under `standard/` of every edition of the rule reference. `Clause` names each
section a registry entry cites, with its number, heading, chapter and source file fixed here.

## Main declarations

- `Clause`, `Clause.all`, `Clause.mem_all`: the closed set of cited sections.
- `Clause.anchor`: the section's stable anchor, the heading's GitHub-style slug, which the
  Verso source gives the section as its tag.
- `Clause.route`, `Clause.url`: its path below an edition root and its development URL.

## Boundaries

The documentation acceptance step (`lake exe docFenceAudit --verso`) checks each clause against
the standard: its render executable (`website/StandardMain.lean`) requires a part of the
elaborated standard with the clause's tag and exactly its heading inside the chapter whose
`file` is the clause's chapter; the rendered chapter page must define the anchor
(`Regula.Site.standardAnchors`); and the source must be a module of the standard. That the
chapter is written in that module is by inspection. The published site's links are the site
build's link check. Nothing here reads the standard.
-/

namespace Regula

/-- A section of the standard cited by the rule registry. -/
inductive Clause where
  | inlineDocumentation
  | faithfulExplanation
  | moduleDocumentation
  | elaborationEnvironment
  | lakeSurfaces
  | cleanElaboration
  | declarationInventory
  | proofCompleteness
  | computationMechanisms
  | documentationChecks
  | enforcingBuildLinter
  deriving DecidableEq, Repr

namespace Clause

/-- Every cited section, once. -/
def all : List Clause := [.inlineDocumentation, .faithfulExplanation, .moduleDocumentation,
  .elaborationEnvironment, .lakeSurfaces, .cleanElaboration, .declarationInventory,
  .proofCompleteness, .computationMechanisms, .documentationChecks, .enforcingBuildLinter]

/-- `all` is exhaustive. -/
theorem mem_all (c : Clause) : c ∈ all := by cases c <;> simp [all]

/-- The section number, as printed in its heading. -/
def number : Clause → String
  | .inlineDocumentation => "5.1" | .faithfulExplanation => "5.2" | .moduleDocumentation => "5.3"
  | .elaborationEnvironment => "8.1" | .lakeSurfaces => "8.2" | .cleanElaboration => "8.3"
  | .declarationInventory => "8.4" | .proofCompleteness => "8.5"
  | .computationMechanisms => "8.6" | .documentationChecks => "8.7"
  | .enforcingBuildLinter => "8.12"

/-- The heading after the section number. -/
def title : Clause → String
  | .inlineDocumentation => "Inline Documentation Requirements"
  | .faithfulExplanation => "Faithful Explanation of Formal Claims"
  | .moduleDocumentation => "Module Documentation"
  | .elaborationEnvironment => "Declare the Elaboration Environment"
  | .lakeSurfaces => "Define Surfaces Through Lake Semantics"
  | .cleanElaboration => "Clean Elaboration and Diagnostics"
  | .declarationInventory => "Inventory Every Owned Declaration"
  | .proofCompleteness => "Proof Completeness and Foundation Strength"
  | .computationMechanisms => "Classify Lean Computation Mechanisms Exactly"
  | .documentationChecks => "Check Lean Documentation Verbatim"
  | .enforcingBuildLinter => "Opt-in Enforcing Build Linter"

/-- The chapter's route below `standard/`, which is also its Verso part's `file`. -/
def chapter : Clause → String
  | .inlineDocumentation | .faithfulExplanation | .moduleDocumentation => "5-documentation-standards"
  | _ => "8-tooling-and-machine-audit"

/-- The chapter's Verso source, relative to the Regula package root. -/
def source : Clause → String
  | .inlineDocumentation | .faithfulExplanation | .moduleDocumentation =>
    "website/RegulaStandard/DocumentationStandards.lean"
  | _ => "website/RegulaStandard/ToolingAndMachineAudit.lean"

/-- The full heading. -/
def heading (c : Clause) : String := c.number ++ " " ++ c.title

/-- GitHub-style heading slug: lowercase; letters, digits, `-`, `_` and spaces kept; spaces
become hyphens. -/
def slug (heading : String) : String :=
  String.ofList <| (heading.toLower.toList.filter fun c =>
    c.isAlphanum || c == '-' || c == '_' || c == ' ').map fun c => if c == ' ' then '-' else c

/-- The section's stable anchor on its chapter page: the slug of its heading. -/
def anchor (c : Clause) : String := slug c.heading

/-- The section's path below an edition root of the rule reference. -/
def route (c : Clause) : String := "standard/" ++ c.chapter ++ "/#" ++ c.anchor

/-- The section in the development edition. Development routes are explicit; this does not
claim that a page is deployed. -/
def url (c : Clause) : String := "https://rbeauchamp.github.io/regula/dev/" ++ c.route

/-- The citation shown with a rule. -/
def label (c : Clause) : String := "standard §" ++ c.heading

end Clause

end Regula

namespace Regula

/-- The route of the compliance checklist (module 9) below `standard/`. -/
def checklistChapter : String := "9-compliance-audit"

/-- The path of a compliance-checklist row below an edition root: the row identifier is its
anchor on the checklist page. -/
def checklistRoute (row : String) : String := "standard/" ++ checklistChapter ++ "/#" ++ row

end Regula
