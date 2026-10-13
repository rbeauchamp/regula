import Lean.Data.Json

/-! # The documents that Regula writes at a destination

A program of Regula marks each file that its arguments name as a destination incomplete before its
run, and later writes its document there. Before it replaces a file, it recognizes the file as a
document of Regula (`regulaDocument`), completed or marked, so it replaces nothing else.

A completed document is recognized by its kind's signature (`completedSignatures`): every member
that a reader of its kind requires, or for a kind that no reader of the repository reads, every
member that each of its documents holds. A mark is recognized by a signature of its own
(`markSignatures`): the members that it holds and the value that marks it incomplete. Values are not
read otherwise, except the mode `serializedGraph` of a serialized-graph result, so a document of an
earlier version of Regula with these members stays recognized. A document of any kind is
recognized, not only one of the kind that the destination holds: Regula regenerates each of its
documents, so replacing one loses nothing that a later run cannot make again. -/

namespace Regula.Destination

open Lean

/-- The members that identify a kind of document: the names of members that it holds, whatever
their values, and the members that it holds with a given string value. -/
abbrev Signature := List String × List (String × String)

/-- The signature of each kind of completed document, one entry for each kind:

- a result of `axiomGate`, `lake lint` or `ruleExamples`: `sourceTexts`, which its reader
  (`ResultProtocol.readDocument`) requires, and the members that the reader of its guidance
  (`ResultProtocol.admitGuidance`) requires. A result's mark is a result (`resultJson`), so this
  signature recognizes it too;
- a registry export: the members that its reader (`validateRegistry`) requires;
- an acceptance link: the members that its reader (`AcceptanceLink.require`) requires;
- a worker packet: the members that its reader (`readWorkerPacket`) admits exactly;
- a published admission: the members that its reader admits exactly;
- rule-example evidence: the members that its readers (`Site.Build.admitShard` and the corpus
  qualifier, `RuleExampleQualification`) require;
- a prose baseline: the members that its reader re-prints exactly (`ProseBaseline`);
- a serialized-graph result of `freshChecker --json-out`, which no reader reads: the members that
  each holds, with its mode;
- a producer export, an environment census, an acceptance receipt and a native-launcher report,
  which no reader reads: the members that each holds. A census's and a receipt's mark is a census or
  a receipt with the status `incomplete`, so their signatures recognize it too. -/
def completedSignatures : List Signature :=
  [(["schemaVersion", "status", "mode", "diagnostics", "stages", "stagesCompleted", "complete",
      "stagesNotRun", "rules", "sourceTexts"], []),
    (["schemaVersion", "producerVersion", "toolchain", "sourceRevision", "rules"], []),
    (["schemaVersion", "status", "identity"], []),
    (["schema", "producer", "request", "payload"], []),
    (["receipt", "origins"], []),
    (["outcome", "schemaVersion", "selected", "completeCorpus", "checkerBefore", "checkerAfter",
      "records"], []),
    (["version", "checks", "documents"], []),
    (["status", "moduleSets", "modules", "roots", "coverage", "checks"],
      [("mode", "serializedGraph")]),
    (["schemaVersion", "examples"], []),
    (["attemptId", "schemaVersion", "status", "packets", "controls"], []),
    (["attemptId", "status", "group", "inputs", "records"], []),
    (["outcome", "equivalent", "totalMillis"], [])]

/-- The signature of each kind of mark, the incomplete document that a program writes before its
run, one entry for each form that a writer of Regula writes:

- the mark of a worker packet, a registry export, a published admission or a prose baseline:
  `reason` with the status `incomplete`;
- the mark of an acceptance link, and of a producer export, which holds `attempt` too:
  `schemaVersion` with the status `incomplete`;
- the mark of a serialized-graph result: `unresolved` with the status `incomplete` and its mode;
- the marks of rule-example evidence: `attempt` and `rawDirectory`, which `qualify rule-examples`
  writes, or `phase`, which the verification driver writes, with the outcome `INCOMPLETE`;
- the mark of a native-launcher report: `equivalent` with the outcome `INCOMPLETE`. -/
def markSignatures : List Signature :=
  [(["reason"], [("status", "incomplete")]),
    (["schemaVersion"], [("status", "incomplete")]),
    (["unresolved"], [("status", "incomplete"), ("mode", "serializedGraph")]),
    (["attempt", "rawDirectory"], [("outcome", "INCOMPLETE")]),
    (["phase"], [("outcome", "INCOMPLETE")]),
    (["equivalent"], [("outcome", "INCOMPLETE")])]

/-- Whether `value` is an object with the member `name`, whatever its value. -/
def has (value : Json) (name : String) : Bool :=
  (value.getObjVal? name).isOk

/-- Whether `value` is an object whose member `name` is the string `text`. -/
def holds (value : Json) (name text : String) : Bool :=
  (value.getObjValAs? String name).toOption == some text

/-- Whether `value` has the signature `signature`: it holds each member that the signature names
and each string value that it gives. -/
def hasSignature (value : Json) (signature : Signature) : Bool :=
  signature.1.all (has value) && signature.2.all fun member => holds value member.1 member.2

/-- Whether `value` is a document of Regula of some kind: a completed document, by the signature of
its kind (`completedSignatures`), or a mark (`markSignatures`). -/
def regulaDocument (value : Json) : Bool :=
  completedSignatures.any (hasSignature value) || markSignatures.any (hasSignature value)

/-- The names below the longest present prefix of a destination, as a write makes them: without
`.` and empty names, each of which names the directory that it is in, or `none` when one of them is
`..`. A `..` below an absent directory names a place that depends on what the run makes there, so a
destination with one is refused before anything is made. With plain names, the destination is
exactly the real path of its prefix and these names. -/
def plainNames (names : List String) : Option (List String) :=
  if names.contains ".." then none else some (names.filter fun name => name != "." && name != "")

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
  siteBuildMembers.all (has value)

end Regula.Destination
