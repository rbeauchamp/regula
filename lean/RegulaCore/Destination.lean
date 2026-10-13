import Lean.Data.Json

/-! # The kinds of document that Regula writes at a destination

A program of Regula marks each file that its arguments name as a destination incomplete before its
run, and later writes its document there. Before it replaces a file, it recognizes the file as a
document of the destination's kind, completed or marked (`Kind.identifies`), so it replaces nothing
else. A kind is recognized by the presence of top-level members, never by their values, so a
document of an earlier version of Regula stays recognized: the members that a kind requires
(`Kind.required`) are present, and the identifying members of the other kinds that its documents
never hold (`Kind.forbidden`) are absent.

Two kinds never recognize one JSON value (`identifies_disjoint`): for each pair of kinds, one
requires a member that the other forbids (`separated_of_ne`), which `decide` checks over the closed
list of kinds, so a new kind whose recognition overlaps another fails to build. -/

namespace Regula.Destination

open Lean

/-- A top-level member whose presence identifies the kind of a document that Regula writes at a
destination. -/
inductive Member where
  /-- The schema version of a result, a link, an identity, an export or a census. -/
  | schemaVersion
  /-- The status of a result, a link, a mark, a census or a receipt. -/
  | status
  /-- The scope of an audit's result. -/
  | scope
  /-- The diagnostics of an audit's result. -/
  | diagnostics
  /-- The mode of an audit's result or of a serialized-graph result. -/
  | mode
  /-- The rules of a registry export, or of an audit's result. -/
  | rules
  /-- The schema of a worker packet. -/
  | schema
  /-- The receipt of a published admission. -/
  | receipt
  /-- The outcome of rule-example evidence or of a launcher report. -/
  | outcome
  /-- The examples of a producer export. -/
  | examples
  /-- The attempt of an environment census or of an acceptance receipt. -/
  | attemptId
  /-- The packets of an environment census. -/
  | packets
  /-- The transport group of an acceptance receipt. -/
  | group
  /-- Whether a launcher report found the two launchers equivalent. -/
  | equivalent
  /-- The documents of a prose baseline. -/
  | documents
  deriving DecidableEq, Repr

/-- The name of the member in a JSON document. -/
def Member.name : Member → String
  | .schemaVersion => "schemaVersion" | .status => "status" | .scope => "scope"
  | .diagnostics => "diagnostics" | .mode => "mode" | .rules => "rules" | .schema => "schema"
  | .receipt => "receipt" | .outcome => "outcome" | .examples => "examples"
  | .attemptId => "attemptId" | .packets => "packets" | .group => "group"
  | .equivalent => "equivalent" | .documents => "documents"

/-- Every identifying member. -/
def Member.all : List Member :=
  [.schemaVersion, .status, .scope, .diagnostics, .mode, .rules, .schema, .receipt, .outcome,
    .examples, .attemptId, .packets, .group, .equivalent, .documents]

/-- The kinds of document that a program of Regula writes at a destination that its arguments, a
request that they name, or a fixed path of the repository give. -/
inductive Kind where
  /-- A result document of `axiomGate`, `lake lint` or `ruleExamples`, or its mark. -/
  | result
  /-- An acceptance link of `axiomGate --acceptance-link` or of the verification driver, or its
  mark. -/
  | acceptanceLink
  /-- The registry export of `axiomGate --registry-out`, or its mark. -/
  | registry
  /-- The packet of a worker of `axiomGate` or `checkerSelftest`, or its mark. -/
  | workerPacket
  /-- The admission that the declaration-report worker publishes, or its mark. -/
  | admission
  /-- The result of `freshChecker --json-out`, or its mark. -/
  | graph
  /-- The evidence of `qualify rule-examples`, or its mark. -/
  | corpus
  /-- The export of `qualify producers --evidence`, or its mark. -/
  | producerExport
  /-- The evidence of `qualify environments`, or its mark. -/
  | census
  /-- The evidence of `qualify acceptance`, or its mark. -/
  | acceptanceReceipt
  /-- The report of `qualify native-launcher`, or its mark. -/
  | launcherReport
  /-- The prose baseline of `regula-markdown`, or its mark. -/
  | proseBaseline
  deriving DecidableEq, Repr

/-- Every kind. -/
def Kind.all : List Kind :=
  [.result, .acceptanceLink, .registry, .workerPacket, .admission, .graph, .corpus,
    .producerExport, .census, .acceptanceReceipt, .launcherReport, .proseBaseline]

/-- `Kind.all` lists every kind. -/
theorem Kind.mem_all (kind : Kind) : kind ∈ Kind.all := by
  cases kind <;> decide

/-- What a document of the kind is, with its article, in a reason to refuse a destination. -/
def Kind.description : Kind → String
  | .result => "a result document"
  | .acceptanceLink => "an acceptance link"
  | .registry => "a registry export"
  | .workerPacket => "a worker packet"
  | .admission => "a published admission"
  | .graph => "a serialized-graph result"
  | .corpus => "rule-example evidence"
  | .producerExport => "a producer export"
  | .census => "an environment census"
  | .acceptanceReceipt => "an acceptance receipt"
  | .launcherReport => "a launcher report"
  | .proseBaseline => "a prose baseline"

/-- The members that every document of the kind holds, completed or marked. A mark that a
completed document's member names holds it with the value `null` (`Kind.mark`). -/
def Kind.required : Kind → List Member
  | .result => [.scope, .diagnostics]
  | .acceptanceLink => [.schemaVersion, .status]
  | .registry => [.rules]
  | .workerPacket => [.schema]
  | .admission => [.receipt]
  | .graph => [.mode, .status]
  | .corpus => [.outcome]
  | .producerExport => [.schemaVersion, .examples]
  | .census => [.attemptId, .packets]
  | .acceptanceReceipt => [.attemptId, .group]
  | .launcherReport => [.outcome, .equivalent]
  | .proseBaseline => [.documents]

/-- The identifying members, beside its own required ones, that a document of the kind may also
hold: a result has a schema version, a status, a mode and rules, and a mark has a status. -/
def Kind.carries : Kind → List Member
  | .result => [.schemaVersion, .status, .mode, .rules]
  | .acceptanceLink | .graph | .launcherReport => []
  | .registry | .workerPacket | .admission | .census => [.schemaVersion, .status]
  | .corpus => [.schemaVersion]
  | .producerExport | .acceptanceReceipt | .proseBaseline => [.status]

/-- The identifying members that no document of the kind holds. -/
def Kind.forbidden (kind : Kind) : List Member :=
  Member.all.filter fun member => !kind.required.contains member && !kind.carries.contains member

/-- Whether `value` is an object with the member `member`, whatever its value. -/
def has (value : Json) (member : Member) : Bool :=
  match value.getObjVal? member.name with
  | .ok _ => true
  | .error _ => false

/-- Whether `value` is a document of the kind, completed or marked: it holds every member that the
kind requires and none that it forbids, whatever their values. -/
def Kind.identifies (kind : Kind) (value : Json) : Bool :=
  kind.required.all (has value) && kind.forbidden.all fun member => !has value member

/-- Whether one of two kinds requires a member that the other forbids. -/
def separated (a b : Kind) : Bool :=
  a.required.any (b.forbidden.contains ·) || b.required.any (a.forbidden.contains ·)

/-- Each pair of distinct kinds is separated: one requires a member that the other forbids. -/
theorem separated_all :
    ∀ a ∈ Kind.all, ∀ b ∈ Kind.all, a ≠ b → separated a b = true := by
  decide

/-- Two distinct kinds are separated (`separated_all`). -/
theorem separated_of_ne {a b : Kind} (distinct : a ≠ b) : separated a b = true :=
  separated_all a (Kind.mem_all a) b (Kind.mem_all b) distinct

/-- A member that one kind requires and another forbids is present for the first and absent for
the second, so no value is a document of both. -/
private theorem not_both {a b : Kind} {value : Json} {member : Member}
    (required : member ∈ a.required) (forbidden : b.forbidden.contains member = true)
    (ofA : a.identifies value = true) (ofB : b.identifies value = true) : False := by
  simp only [Kind.identifies, Bool.and_eq_true, List.all_eq_true] at ofA ofB
  have present := ofA.1 member required
  have absent := ofB.2 member (List.mem_of_elem_eq_true forbidden)
  simp [present] at absent

/-- No JSON value is a document of two distinct kinds: a destination of one kind never replaces a
document of another. -/
theorem identifies_disjoint {a b : Kind} (distinct : a ≠ b) (value : Json)
    (ofA : a.identifies value = true) : b.identifies value = false := by
  cases ofB : b.identifies value
  · rfl
  · exfalso
    have split := separated_of_ne distinct
    simp only [separated, Bool.or_eq_true, List.any_eq_true] at split
    rcases split with ⟨member, required, forbidden⟩ | ⟨member, required, forbidden⟩
    · exact not_both required forbidden ofA ofB
    · exact not_both required forbidden ofB ofA

/-- The mark of a document of the kind: `fields`, with each member that the kind requires and
`fields` lacks added with the value `null`, so the kind identifies it whenever `fields` hold no
member that it forbids. -/
def Kind.mark (kind : Kind) (fields : List (String × Json)) : Json :=
  Json.mkObj (fields ++ (kind.required.filter fun member =>
    !fields.any (·.1 == member.name)).map fun member => (member.name, Json.null))

/-- The file that marks a directory that a build of the site is assembling: the build writes it
first, when it makes the directory, and removes it after it writes `build.json`. A build that stops
in between thus leaves a directory that a later build may replace. -/
def siteAssemblingMarker : String := ".regula-site-assembling"

/-- The members of the `build.json` of a site artifact whose presence identifies it as the
artifact of a build of Regula's site, whatever their values. -/
def siteBuildMembers : List String := ["schemaVersion", "site", "producerVersion"]

/-- Whether `value` is the `build.json` of a site artifact: it holds each member of
`siteBuildMembers`, whatever its value. -/
def identifiesSiteBuild (value : Json) : Bool :=
  siteBuildMembers.all fun name => match value.getObjVal? name with
    | .ok _ => true
    | .error _ => false

end Regula.Destination
