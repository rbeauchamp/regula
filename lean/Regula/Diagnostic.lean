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

/-- The LSP range (line and UTF-16 character) of the whole reported item. -/
def SourceLocation.fullLsp (s : SourceLocation) : Lsp.Range :=
  s.val.snapshot.source.toFileMap.utf8RangeToLspRange
    ⟨⟨s.val.full.start⟩, ⟨s.val.full.stop⟩⟩

/-- The LSP range (line and UTF-16 character) of the selected part, such as a declaration
name. -/
def SourceLocation.selectionLsp (s : SourceLocation) : Lsp.Range :=
  s.val.snapshot.source.toFileMap.utf8RangeToLspRange
    ⟨⟨s.val.selection.start⟩, ⟨s.val.selection.stop⟩⟩

/-- Lean's LSP UTF-16 column of a position. -/
def lspUtf16Column : Utf16Column := fun fm p => (fm.leanPosToLspPos p).character

/-- A report's codepoint and UTF-16 columns must both agree with the exact source. -/
def sourceFromReport (snapshot : SourceSnapshot) (ranges : RegulaPolicy.Ranges) :
    Except String SourceLocation :=
  sourceFromReportWith lspUtf16Column snapshot ranges

/-- Where a finding is. A declaration Lean generated is located at the range of the declaration
it generated it from (`Regula.Findings.findingLocation`), and a declaration without a range
otherwise keeps honest module attribution. -/
inductive Location where
  /-- A range of an admitted source snapshot. -/
  | source (value : SourceLocation)
  /-- A whole module, for a finding with no source range. -/
  | module (name : Name)
  /-- The project or its configuration, identified by text such as its root path. -/
  | project (identity : String)

/-- The payload of a declaration-scoped rule's finding. -/
structure DeclarationArguments where
  /-- The declaration the finding concerns. -/
  declaration : Name
  /-- The declaration the finding is attributed to (`Regula.Findings.sourceName?`): the end of the
  chain of declarations Lean generated this one from, as the environment records it. `none` when
  Lean did not generate it from another declaration. -/
  sourceDeclaration : Option Name
  /-- What is wrong with it. -/
  detail : String
  deriving Repr
/-- The payload of an execution rule's finding. -/
structure ExecutionArguments where
  /-- The execution root whose closure reaches the unresolved path or boundary. -/
  root : Name
  /-- What was reached and why it fails. -/
  detail : String
  deriving Repr
/-- The payload of a project-, configuration-, module- or documentation-scoped finding. -/
structure ContextArguments where
  /-- What the finding concerns, as text: a project root, a file, a module or a fence origin. -/
  subject : String
  /-- What is wrong with it. -/
  detail : String
  deriving Repr

/-- Distinct argument domains prevent constructing a declaration rule with a project payload. -/
def Payload : RuleId → Type
  | .projectAxiom | .proofHole | .unknownAxiom | .compilerTrusting | .profileExceeded
  | .escapeHatch | .executableContract | .materialDocumentation | .materialIntent =>
                                                                   DeclarationArguments
  | .executionUnresolved | .executionBoundary => ExecutionArguments
  | .environment | .configuration | .sourceBuild | .coverage | .admission | .communityConfiguration
  | .fenceStructure | .positiveExample | .negativeExample | .trustedExample
  | .moduleDocumentation => ContextArguments

/-- Another location a diagnostic refers to, with how it relates to the finding. -/
structure RelatedLocation where
  /-- How the location relates to the finding, as text. -/
  relation : String
  /-- The related location. -/
  location : Location

/-- Display severity is separate from the mandatory strict impact. -/
structure Diagnostic (id : RuleId) where
  /-- The finding's subject and detail, in the argument domain of rule `id` (`Payload id`). -/
  arguments : Payload id
  /-- Where the finding is. -/
  location : Location
  /-- Other locations the finding refers to; empty unless given at construction. -/
  related : Array RelatedLocation := #[]
  /-- The evidence mode of the run that produced the finding. -/
  mode : EvidenceMode
  /-- The claim the subject was checked against, such as a foundation profile or execution
  claim, if any; the message reads `classification-only` without one. -/
  claim : Option String
  /-- Whether the finding is a violation or leaves the run incomplete. -/
  impact : Impact
  /-- The display severity; `error` unless given. -/
  severity : Severity := .error
  /-- `mode` is one of the evidence modes the rule's registry descriptor supports. -/
  supportedMode : mode ∈ (descriptor id).evidenceModes

/-- Mode admission happens at the construction boundary, not only when displaying a result. -/
def makeDiagnostic (id : RuleId) (arguments : Payload id) (location : Location)
    (mode : EvidenceMode) (claim : Option String) (impact : Impact)
    (severity : Severity := .error) (related : Array RelatedLocation := #[]) :
    Except String (Diagnostic id) :=
  if h : mode ∈ (descriptor id).evidenceModes then
    .ok { arguments, location, mode, claim, impact, severity, related, supportedMode := h }
  else .error s!"unsupported diagnostic mode {mode.spelling} for {id}"

/-- A diagnostic together with the rule it belongs to. -/
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
  messageLine id impact d.mode.spelling (d.claim.getD "classification-only") d.location.text
      subject detail

/-- A finding's complete text on its own (`Feedback.standalone`): what and where, the rule's
remedy, and the rule page and offline `lake exe regula explain` command. -/
def Diagnostic.text {id : RuleId} (d : Diagnostic id) : String :=
  Feedback.standalone id d.message

/-- For an RG1005 finding, its subject and the declaration it is attributed to, if any; `none` for
every other rule. -/
def Finding.profileSubject? : Finding → Option (Name × Option Name)
  | ⟨.profileExceeded, d⟩ => some (d.arguments.declaration, d.arguments.sourceDeclaration)
  | _ => none

/-- For an RG1005 finding, the declaration its subject is attributed to, if any. -/
def Finding.sourceDeclaration? (f : Finding) : Option Name := f.profileSubject?.bind (·.2)

/-- The declaration an RG1005 finding is printed under: the declaration its subject is attributed
to, or its subject. Findings of other rules are printed on their own. -/
def Finding.groupUnder? (f : Finding) : Option Name :=
  f.profileSubject?.map fun (subject, source) => source.getD subject

/-- The finding as an entry of a run's rendering (`Feedback.render`). -/
def Finding.entry (f : Finding) : Feedback.Entry :=
  ⟨f.1, f.2.location.place, (f.groupUnder?.map toString).getD "", f.sourceDeclaration?.isSome,
    f.2.message⟩

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

/-- Whether `b` is printed in the same block as `a` when it follows it: both RG1005 findings under
the same declaration (`Finding.groupUnder?`), with the same impact, mode, claim and place. The
block states `a`'s location text once; findings at one place share it whenever each source URI of
a run has one snapshot, as a run's findings do. -/
def Finding.sameGroup (a b : Finding) : Bool :=
  match a.groupUnder?, b.groupUnder? with
  | some x, some y =>
      x == y && a.2.impact == b.2.impact && a.2.mode == b.2.mode && a.2.claim == b.2.claim &&
        a.2.location.place == b.2.location.place
  | _, _ => false

/-- A run's findings in the blocks it prints: the runs (`Feedback.runs`) of `sortFindings` in
which each RG1005 finding follows another under the same declaration (`Finding.sameGroup`). The
order puts those findings next to each other: they share their place, rule and group key. -/
def groupFindings (fs : List Finding) : List (List Finding) :=
  Feedback.runs Finding.sameGroup (sortFindings fs)

/-- Grouping loses no finding: flattened, the groups are exactly the findings in run order, the
order the JSON report lists them in (`ResultProtocol.resultJson`). -/
theorem groupFindings_flatten (fs : List Finding) : (groupFindings fs).flatten = sortFindings fs :=
  Feedback.flatten_runs _ _

/-- The groups hold every finding exactly as often as the run supplied it. -/
theorem groupFindings_perm (fs : List Finding) : List.Perm (groupFindings fs).flatten fs := by
  rw [groupFindings_flatten]
  exact sortFindings_perm fs

/-- One member line of a printed group: the finding's subject and detail, as its message states
them. -/
def Finding.memberLine (f : Finding) : String :=
  let (subject, detail) := argumentParts f.1 f.2.arguments
  "  - " ++ subject ++ ": " ++ detail

/-- The message of a group whose first finding is `f` and whose findings are `members`: `f`'s
message line with the declaration they are under as its subject and their count as its detail,
then every member's subject and detail, then, when some are attributed to that declaration, where
to fix those (`Feedback.attributedLine`). -/
def groupMessage (f : Finding) (members : List Finding) : String :=
  let under := (f.groupUnder?.map toString).getD (argumentParts f.1 f.2.arguments).1
  let attributed := (members.filter (·.sourceDeclaration?.isSome)).length
  let own := members.length - attributed
  let summary :=
    if own == 0 then
      Feedback.countText attributed "declaration" ++ " Lean generated from it " ++
        (if attributed == 1 then "exceeds" else "exceed") ++ " the claim"
    else if attributed == 0 then Feedback.countText own "finding" ++ " exceed the claim"
    else "it and " ++ Feedback.countText attributed "declaration" ++
      " Lean generated from it exceed the claim"
  let impact := if f.2.impact == .violation then "violation" else "incomplete"
  messageLine f.1 impact f.2.mode.spelling (f.2.claim.getD "classification-only")
      f.2.location.text under summary ++ "\n" ++
    "\n".intercalate (members.map Finding.memberLine) ++
    (if attributed == 0 then "" else "\n" ++ Feedback.attributedLine under attributed)

/-- The printed entry of the group of `f` followed by `rest`: `f`'s own entry when it is alone and
its subject is not attributed to another declaration, and otherwise one block with
`groupMessage`. -/
def groupEntry (f : Finding) (rest : List Finding) : Feedback.Entry :=
  if rest.isEmpty && f.sourceDeclaration?.isNone then f.entry
  else { f.entry with message := groupMessage f (f :: rest) }

/-- A finding alone in its group prints exactly its own entry, as before grouping, unless it is an
RG1005 finding attributed to another declaration, which prints as a block under that declaration:
this covers every finding of another rule. -/
theorem groupEntry_alone (f : Finding) (h : f.sourceDeclaration? = none) :
    groupEntry f [] = f.entry := by
  simp [groupEntry, h]

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
