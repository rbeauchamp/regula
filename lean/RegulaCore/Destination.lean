import Lean.Data.Json

/-! # The documents that Regula writes at a destination

A program of Regula marks each file that its arguments name as a destination incomplete before its
run, and later writes its document there. Before it replaces a file, it recognizes the file as a
document of Regula (`regulaDocument`), completed or marked, so it replaces nothing else.

A completed document is recognized by its kind's signature (`completedSignatures`): each member
that a reader of its kind requires and that each document of the kind that Regula writes holds, or
for a kind that no reader of the repository reads, every member that each of its documents holds. A
member that a reader requires only when another member has some value is left out when Regula
writes a document of the kind with that value and without the member: the signature would refuse
Regula's own document. A mark is recognized by a signature of its own
(`markSignatures`): the members that it holds and the value that marks it incomplete. Values are not
read otherwise, except the mode `serializedGraph` of a serialized-graph result, so a document of an
earlier version of Regula with these members stays recognized. A document of any kind is
recognized, not only one of the kind that the destination holds: Regula can make each document
that it wrote again. The recognition reads the members of a file, not who wrote it, so a file in
one of these forms that Regula did not write, such as a tracked fixture of the repository
(`lean/Fixtures/ControlledProse/B1.refuse-entry.json`), is replaced too when a destination names
it. -/

namespace Regula.Destination

open Lean

/-- The members that identify a kind of document: the names of members that it holds, whatever
their values, and the members that it holds with a given string value. -/
abbrev Signature := List String × List (String × String)

/-- The signature of each kind of completed document, one entry for each kind. Two kinds have a
writer in this version of Regula:

- an acceptance link, which the verification driver writes (`RegulaVerification.acceptedValue`)
  and reads (`RegulaVerification.linked`): its members `schemaVersion`, `status` and `identity`;
- a prose baseline, which `regula-markdown` writes: the members that its reader re-prints exactly
  (`ProseBaseline`).

The other kinds are documents that earlier versions of Regula wrote, and no program of this
version writes or reads them. Each signature holds the members that the readers of those versions
required of its kind, or, for a kind that no reader read, the members that each of its documents
held, so such a document at a destination stays replaceable:

- a result of the earlier checker; a result's mark was a result, so this signature recognizes it
  too;
- a registry export;
- a worker packet;
- a published admission;
- rule-example evidence;
- a serialized-graph result, with its mode;
- a producer export, an environment census, an acceptance receipt and a native-launcher report. A
  census's and a receipt's mark is a census or a receipt with the status `incomplete`, so their
  signatures recognize it too. -/
def completedSignatures : List Signature :=
  [(["schemaVersion", "producerVersion", "toolchain", "sourceRevision", "scope", "mode", "status",
      "diagnostics", "unresolved", "sourceTexts", "stages", "stagesCompleted", "complete",
      "stagesNotRun", "rules"], []),
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
run, one entry for each form that a writer of Regula writes or that one of an earlier version
wrote:

- the mark of a prose baseline, which `regula-markdown` writes, and of a worker packet, a registry
  export or a published admission: `reason` with the status `incomplete`;
- the mark of an acceptance link, which the verification driver writes
  (`RegulaVerification.incompleteLink`), and of a producer export, which holds `attempt` too:
  `schemaVersion` with the status `incomplete`;
- the mark of a serialized-graph result: `unresolved` with the status `incomplete` and its mode;
- the marks of rule-example evidence: `attempt` and `rawDirectory`, or `phase`, with the outcome
  `INCOMPLETE`;
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

/-- The name of a kind of entry in a reason to refuse a destination. -/
def entryName : IO.FS.FileType → String
  | .dir => "a directory"
  | .file => "a regular file"
  | .symlink => "a symbolic link"
  | .other => "an entry that is not a directory, a regular file or a symbolic link"

/-- The reason to refuse to write at `path`, if there is one, decided from what the reads of a
writer observe there, each without following a link at `path`: `entry`, the type of the entry or
the error of its read, and `contents`, the bytes of the regular file there or the error of their
read, which a writer reads only for a regular file. It is the reason when something is at `path`
and it is not a regular file that is empty or whose text is a JSON document of Regula
(`regulaDocument`), or when the read of the entry fails other than for its absence. -/
def ownershipDecision (path : System.FilePath) (entry : Except IO.Error IO.FS.FileType)
    (contents : Except IO.Error ByteArray) : Option String :=
  let refuse (what : String) : Option String := some s!"{path} is {what}, not a document that \
    Regula wrote, so the run does not replace it"
  match entry with
  | .error (.noFileOrDirectory ..) => none
  | .error error => some s!"{path} cannot be read without following a link ({error}), so the \
      run does not replace it"
  | .ok type =>
    if type != .file then refuse (entryName type)
    else match contents with
      | .error error => refuse s!"a regular file that cannot be read ({error})"
      | .ok bytes =>
        if bytes.isEmpty then none
        else match String.fromUTF8? bytes with
          | none => refuse "a file that is not UTF-8 text"
          | some text => match Json.parse text with
            | .ok value => if regulaDocument value then none else refuse "a JSON document"
            | .error _ => refuse "a file that is not a JSON document"

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

/-- Whether a directory holds an artifact of a build of the site or one that a build assembles,
decided from what reads that follow no link observe in it: `marker`, whether the marker of an
assembly (`siteAssemblingMarker`) is a regular file there, and `build`, the text of its
`build.json` when that is a regular file that can be read, which identifies a build
(`identifiesSiteBuild`). -/
def holdsSiteArtifact (marker : Bool) (build : Option String) : Bool :=
  marker || build.any fun text => (Json.parse text).toOption.any identifiesSiteBuild

/-- The reason to refuse to replace or remove what is at `out`, the directory of a site artifact,
if there is one, decided from what reads that follow no link at `out` observe: `entry`, the type of
the entry or the error of its read; `holds`, whether the directory there holds an artifact
(`holdsSiteArtifact`); and `empty`, whether it has no entry. It is the reason when something is at
`out` and it is not a directory that holds an artifact or that is empty, or when the read of the
entry fails other than for its absence. `consequence` is what the caller then does not do. -/
def siteArtifactDecision (out : System.FilePath) (consequence : String)
    (entry : Except IO.Error IO.FS.FileType) (holds empty : Bool) : Option String :=
  match entry with
  | .error (.noFileOrDirectory ..) => none
  | .error error => some s!"{out} cannot be read without following a link ({error}), so \
      {consequence}"
  | .ok type =>
    if type != .dir then
      some s!"{out} is not a directory (a file, a symbolic link or a different kind of entry is \
        there), so {consequence}"
    else if holds || empty then none
    else some s!"{out} is not empty and holds neither a build.json of a site that Regula built \
      nor the marker {siteAssemblingMarker} of an assembly, so {consequence}"

end Regula.Destination
