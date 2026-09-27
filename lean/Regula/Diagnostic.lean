module

public import RegulaCore.Rule
public import RegulaCore.Feedback
public import RegulaCore.Source
public import Lean.Data.Lsp.Utf16

/-! # Canonical diagnostic values

Canonical diagnostic values and source conversion. Payloads are indexed by the closed
`RuleId` (design credit in RuleId); source conversion uses pinned Lean FileMap/LSP APIs. -/

@[expose] public section

namespace Regula
open Lean

def SourceLocation.fullLsp (s : SourceLocation) : Lsp.Range :=
  s.val.snapshot.source.toFileMap.utf8RangeToLspRange
    ⟨⟨s.val.full.start⟩, ⟨s.val.full.stop⟩⟩

def SourceLocation.selectionLsp (s : SourceLocation) : Lsp.Range :=
  s.val.snapshot.source.toFileMap.utf8RangeToLspRange
    ⟨⟨s.val.selection.start⟩, ⟨s.val.selection.stop⟩⟩

/-- Lean's LSP UTF-16 column of a position. -/
def lspUtf16Column : Utf16Column := fun fm p => (fm.leanPosToLspPos p).character

/-- A report's codepoint and UTF-16 columns must both agree with the exact source. -/
def sourceFromReport (snapshot : SourceSnapshot) (ranges : RegulaPolicy.Ranges) :
    Except String SourceLocation :=
  sourceFromReportWith lspUtf16Column snapshot ranges

/-- Range-less generated declarations retain honest module attribution. -/
inductive Location where
  | source (value : SourceLocation)
  | module (name : Name)
  | project (identity : String)

inductive Impact where
  | violation | incomplete
  deriving Repr, BEq, DecidableEq

structure DeclarationArguments where
  declaration : Name
  detail : String
  deriving Repr
structure ExecutionArguments where
  root : Name
  detail : String
  deriving Repr
structure ContextArguments where
  subject : String
  detail : String
  deriving Repr

/-- Distinct argument domains prevent constructing a declaration rule with a project payload. -/
def Payload : RuleId → Type
  | .projectAxiom | .proofHole | .unknownAxiom | .compilerTrusting | .profileExceeded
  | .escapeHatch | .executableContract | .materialDocumentation | .materialIntent => DeclarationArguments
  | .executionUnresolved | .executionBoundary => ExecutionArguments
  | .environment | .configuration | .sourceBuild | .coverage | .admission | .communityConfiguration
  | .fenceStructure | .positiveExample | .negativeExample | .trustedExample
  | .moduleDocumentation => ContextArguments

structure RelatedLocation where
  relation : String
  location : Location

/-- Display severity is separate from the mandatory strict impact. -/
structure Diagnostic (id : RuleId) where
  arguments : Payload id
  location : Location
  related : Array RelatedLocation := #[]
  mode : EvidenceMode
  claim : Option String
  impact : Impact
  severity : Severity := .error
  supportedMode : mode ∈ (descriptor id).evidenceModes

/-- Mode admission happens at the construction boundary, not only when displaying a result. -/
def makeDiagnostic (id : RuleId) (arguments : Payload id) (location : Location)
    (mode : EvidenceMode) (claim : Option String) (impact : Impact)
    (severity : Severity := .error) (related : Array RelatedLocation := #[]) :
    Except String (Diagnostic id) :=
  if h : mode ∈ (descriptor id).evidenceModes then
    .ok { arguments, location, mode, claim, impact, severity, related, supportedMode := h }
  else .error s!"unsupported diagnostic mode {mode.spelling} for {id}"

abbrev Finding := (id : RuleId) × Diagnostic id

/-- The subject and detail of a payload, rendered by `messageLine`. -/
def argumentParts : (id : RuleId) → Payload id → String × String
  | .projectAxiom, a | .proofHole, a | .unknownAxiom, a | .compilerTrusting, a
  | .profileExceeded, a | .escapeHatch, a | .executableContract, a
  | .materialDocumentation, a | .materialIntent, a => (toString a.declaration, a.detail)
  | .executionUnresolved, a | .executionBoundary, a => (toString a.root, a.detail)
  | .environment, a | .configuration, a | .sourceBuild, a | .coverage, a
  | .admission, a | .communityConfiguration, a | .fenceStructure, a | .positiveExample, a
  | .negativeExample, a | .trustedExample, a | .moduleDocumentation, a =>
    (toString a.subject, a.detail)

/-- Lean's position (one-based line, codepoint column) of the start of a source selection. -/
def SourceLocation.startPosition (s : SourceLocation) : Position :=
  s.val.snapshot.source.toFileMap.toPosition ⟨s.val.selection.start⟩

/-- Where a finding is, as its message states it: `FILE:LINE:COLUMN` of the selection start
for source (Lean's own message coordinates), otherwise the module or project scope. -/
def Location.text : Location → String
  | .source s => s!"{s.val.snapshot.uri}:{s.startPosition.line}:{s.startPosition.column}"
  | .module n => s!"module {n}"
  | .project p => s!"project/configuration {p}"

/-- The ordering place of a location (`Feedback.Place`). -/
def Location.place : Location → Feedback.Place
  | .source s => .source s.val.snapshot.uri s.val.selection.start
  | .module n => .module n.toString
  | .project p => .project p

/-- What is wrong and where: the finding's `messageLine`. -/
def Diagnostic.message {id : RuleId} (d : Diagnostic id) : String :=
  let impact := if d.impact == .violation then "violation" else "incomplete"
  let (subject, detail) := argumentParts id d.arguments
  messageLine id impact d.mode.spelling (d.claim.getD "classification-only") d.location.text subject detail

/-- A finding's complete text on its own (`Feedback.standalone`): what and where, the rule's
remedy, and the rule page and offline `lake exe regula explain` command. -/
def Diagnostic.text {id : RuleId} (d : Diagnostic id) : String :=
  Feedback.standalone id d.message

/-- The finding as an entry of a run's rendering (`Feedback.render`). -/
def Finding.entry (f : Finding) : Feedback.Entry := ⟨f.1, f.2.location.place, f.2.message⟩

/-- Each finding paired with its entry, so a sort renders every entry once. -/
def keyedFindings (fs : List Finding) : List (Feedback.Entry × Finding) :=
  fs.map fun f => (f.entry, f)

/-- A run's findings in run order: the order `Feedback.sortEntries` gives their entries. -/
def sortFindings (fs : List Finding) : List Finding :=
  ((keyedFindings fs).mergeSort fun a b => Feedback.Entry.le a.1 b.1).map (·.2)

/-- Findings are reported in exactly the order their text is printed. -/
theorem sortFindings_entries (fs : List Finding) :
    (sortFindings fs).map Finding.entry = Feedback.sortEntries (fs.map Finding.entry) := by
  let sorted := (keyedFindings fs).mergeSort fun a b => Feedback.Entry.le a.1 b.1
  have keyed : ∀ p ∈ sorted, Finding.entry p.2 = p.1 := by
    intro p hp
    obtain ⟨f, -, rfl⟩ := List.mem_map.mp ((List.mergeSort_perm _ _).mem_iff.mp hp)
    rfl
  calc (sortFindings fs).map Finding.entry = sorted.map Prod.fst := by
        rw [sortFindings, List.map_map]; exact List.map_congr_left keyed
    _ = ((keyedFindings fs).map Prod.fst).mergeSort Feedback.Entry.le :=
        List.map_mergeSort (fun _ _ _ _ => rfl)
    _ = Feedback.sortEntries (fs.map Finding.entry) := by
        simp [keyedFindings, Feedback.sortEntries, Function.comp_def]

/-- Every finding is reported exactly once. -/
theorem sortFindings_perm (fs : List Finding) : List.Perm (sortFindings fs) fs := by
  have := (List.mergeSort_perm (keyedFindings fs) fun a b => Feedback.Entry.le a.1 b.1).map Prod.snd
  simpa [sortFindings, keyedFindings, Function.comp_def] using this

/-- Native logging consumes the same typed diagnostic and genuine selection span. -/
def Diagnostic.nativeMessage {id : RuleId} (d : Diagnostic id) : Except String Message := do
  let .source source := d.location | throw "native source message requires a source location"
  let fm := source.val.snapshot.source.toFileMap
  return {
    fileName := source.val.snapshot.uri
    pos := fm.toPosition ⟨source.val.selection.start⟩
    endPos := some (fm.toPosition ⟨source.val.selection.stop⟩)
    severity := match d.severity with
      | .error => .error | .warning => .warning | .information => .information
    data := toMessageData d.text }
end Regula
