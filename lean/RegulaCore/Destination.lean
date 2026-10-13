import Lean.Data.Json

/-! # The documents that Regula writes at a destination

A program of Regula marks each file that its arguments name as a destination incomplete before its
run, and later writes its document there. Before it replaces a file, it recognizes the file as a
document of Regula (`regulaDocument`), completed or marked, so it replaces nothing else.

A document is recognized by the members that one of Regula's readers checks to identify a document
of its kind. A kind that no reader of the repository reads, and each mark, is recognized by members
that each of its documents holds. Values are not read, except the status `incomplete` of a mark and
the mode `serializedGraph` of a serialized-graph result. A document of an earlier version of Regula
thus stays recognized. A document of any kind is recognized, not only one of the kind that the
destination holds: Regula regenerates each of its documents, so replacing one loses nothing that a
later run cannot make again. -/

namespace Regula.Destination

open Lean

/-- The members that identify a document of Regula, one entry for each kind of document or mark: the
names of members that the document holds, whatever their values, and the members that it holds with
a given string value.

- The four identity members of `Regula.RegistryCodec.identityFields`: a result document of
  `axiomGate`, `lake lint` or `ruleExamples` and its mark, and a registry export, whose reader
  (`validateRegistry`) checks these members and `rules`.
- `schemaVersion` and `status`: an acceptance link and its mark, and the mark of a producer export.
- The four members of a worker packet, which its reader (`readWorkerPacket`) admits exactly.
- The two members of a published admission, which its reader admits exactly.
- `status` and the mode `serializedGraph`: the result of `freshChecker --json-out` and its mark.
- `outcome`: rule-example evidence and its marks, which its reader (`admitShard`) identifies by it.
- `schemaVersion` and `examples`: a producer export.
- `attemptId`, `packets` and `controls`: an environment census and its mark.
- `attemptId`, `group` and `records`: an acceptance receipt and its mark.
- `outcome` and `equivalent`: a native-launcher report and its mark.
- `version`, `checks` and `documents`: a prose baseline, which its reader re-prints exactly.
- `reason` and the status `incomplete`: the mark of a worker packet, a registry export, a published
  admission or a prose baseline. -/
def signatures : List (List String × List (String × String)) :=
  [(["schemaVersion", "producerVersion", "toolchain", "sourceRevision"], []),
    (["schemaVersion", "status"], []),
    (["schema", "producer", "request", "payload"], []),
    (["receipt", "origins"], []),
    (["status"], [("mode", "serializedGraph")]),
    (["outcome"], []),
    (["schemaVersion", "examples"], []),
    (["attemptId", "packets", "controls"], []),
    (["attemptId", "group", "records"], []),
    (["outcome", "equivalent"], []),
    (["version", "checks", "documents"], []),
    (["reason"], [("status", "incomplete")])]

/-- Whether `value` is an object with the member `name`, whatever its value. -/
def has (value : Json) (name : String) : Bool :=
  (value.getObjVal? name).isOk

/-- Whether `value` is an object whose member `name` is the string `text`. -/
def holds (value : Json) (name text : String) : Bool :=
  (value.getObjValAs? String name).toOption == some text

/-- Whether `value` is a document of Regula of some kind, completed or marked: for one entry of
`signatures`, it holds each member that the entry names and each string value that the entry
gives. -/
def regulaDocument (value : Json) : Bool :=
  signatures.any fun signature =>
    signature.1.all (has value) && signature.2.all fun member => holds value member.1 member.2

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
