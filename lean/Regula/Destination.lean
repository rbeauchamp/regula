import Lean.Data.Json
import Regula.Filesystem

/-! # The destinations that a run of Regula may replace

A program of Regula marks each result destination that its arguments name before any code of the
run reads an input (`Regula.TaskManager.guard`), so a destination that names one of its inputs
would replace that input before the run reads it. Three rules keep the mark and the run's writes
from losing a file that is not Regula's, whatever files the run reads:

- A write replaces the entry at the destination and never writes into the file that the entry
  names (`Regula.Filesystem.writeReplacing`), so a hard link there keeps the file that it shares.
- A write, and so a mark, stops with nothing written when the destination holds something other
  than nothing, an empty regular file, or a regular file whose text is a document of the
  destination's kind (`write`, `ownershipRefusal`, `Kind.identifies`). A file that holds bytes and
  is not such a document, such as a source, a configuration file or a Markdown document, is thus
  never replaced. The program marks its other destinations, then refuses the run (`refusal`).
- A program refuses an invocation two of whose destinations may be one entry (`sameEntry`), after
  it marks them.

The second rule decides by the members that every producer of a kind writes, not by the values of
an identity, so a document of an earlier version of Regula stays replaceable. It replaces an empty
file: it holds no bytes to lose, and a destination that `mktemp` made is such a file. -/

namespace Regula.Destination

open Lean System

/-- The kinds of document that a program of Regula writes at a destination that its arguments
name: the kind decides which existing file there the program may replace (`Kind.identifies`). -/
inductive Kind where
  /-- A result document of `axiomGate`, `lake lint` or `ruleExamples`
  (`Regula.Checker.ResultProtocol`), or its mark. -/
  | result
  /-- An acceptance link of `axiomGate --acceptance-link` (`Regula.Checker.AcceptanceLink`), or its
  mark. -/
  | acceptanceLink
  /-- The registry export of `axiomGate --registry-out` (`Regula.RegistryCodec.registryJson`), or
  its mark (`Regula.Checker.invalidateOutput`). -/
  | registry
  /-- The output of a worker of `axiomGate` or `checkerSelftest`: a worker packet
  (`Regula.Checker.workerPacket`), an admission that the declaration-report worker publishes, or
  the mark of either (`Regula.Checker.invalidateOutput`). -/
  | workerOutput
  /-- The result of `freshChecker --json-out`, or its mark. -/
  | graph
  /-- The evidence of `qualify rule-examples`, its mark, or the setup mark of
  `scripts/verify.sh`. -/
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

/-- What a document of the kind is, in a reason to refuse a destination. -/
def Kind.description : Kind → String
  | .result => "result document"
  | .acceptanceLink => "acceptance link"
  | .registry => "registry export"
  | .workerOutput => "worker output"
  | .graph => "serialized-graph result"
  | .corpus => "rule-example evidence"
  | .producerExport => "producer export"
  | .census => "environment census"
  | .acceptanceReceipt => "acceptance receipt"
  | .launcherReport => "launcher report"
  | .proseBaseline => "prose baseline"

/-- Whether `value` is an object with a member `name`. -/
private def has (value : Json) (name : String) : Bool :=
  match value.getObjVal? name with
  | .ok _ => true
  | .error _ => false

/-- The members that identify a document of Regula by its producer
(`Regula.RegistryCodec.identityFields`). -/
def identityNames : List String :=
  ["schemaVersion", "producerVersion", "toolchain", "sourceRevision"]

/-- Whether `value` has every member of `identityNames`. -/
def identified (value : Json) : Bool := identityNames.all (has value)

/-- A completed result of an earlier version of Regula: the members of `identityNames`, with
values that no current build writes, and the status `completed`. A control seeds a destination
with it to require that a run replace it. -/
def earlierResult : String :=
  "{\"schemaVersion\":3,\"producerVersion\":\"0.0.0\",\"toolchain\":\"leanprover/lean4:v4.34.0\",\
    \"sourceRevision\":\"0000000\",\"status\":\"completed\"}\n"

/-- Whether `value` is a document of the kind, or its mark, by the members that every writer of
the kind writes, whatever the values of an identity: only a serialized-graph result's `mode` and a
prose baseline mark's `status` are read for a constant value. -/
def Kind.identifies : Kind → Json → Bool
  | .result, value | .registry, value => identified value
  | .acceptanceLink, value => has value "schemaVersion" && has value "status"
  | .workerOutput, value =>
    has value "schema" && has value "payload" || has value "receipt" && has value "origins" ||
      identified value
  | .graph, value => (value.getObjValAs? String "mode").toOption == some "serializedGraph"
  | .corpus, value => (value.getObjValAs? String "outcome").toOption.isSome
  | .producerExport, value =>
    has value "schemaVersion" && (has value "status" || has value "examples")
  | .census, value => has value "attemptId" && has value "packets" && has value "controls"
  | .acceptanceReceipt, value => has value "attemptId" && has value "group" && has value "records"
  | .launcherReport, value => has value "outcome" && has value "equivalent"
  | .proseBaseline, value =>
    has value "version" && has value "documents" ||
      (value.getObjValAs? String "status").toOption == some "incomplete"

/-- The name of a kind of entry in a reason to refuse a destination. -/
private def entryName : IO.FS.FileType → String
  | .dir => "a directory"
  | .file => "a regular file"
  | .symlink => "a symbolic link"
  | .other => "an entry that is not a directory, a regular file or a symbolic link"

/-- The reason to refuse to write a document of `kind` at `path`, if there is one: something is at
`path`, by a read that follows no link (`Regula.Filesystem.observeMetadata`), and it is not a
regular file that is empty or whose text is a JSON document of `kind` (`Kind.identifies`). An
error of that read other than the absence of the entry is a reason too. An empty file holds no
bytes to lose, so a destination that `mktemp` made is replaced; an empty input named as a
destination is replaced as well. -/
def ownershipRefusal (kind : Kind) (path : FilePath) : IO (Option String) := do
  let refuse (what : String) : Option String := some s!"{path} is {what}, not a \
    {kind.description} that Regula wrote, so the run does not replace it"
  match ← (Regula.Filesystem.observeMetadata path).toBaseIO with
  | .error (.noFileOrDirectory ..) => return none
  | .error error => return some s!"{path} cannot be read without following a link ({error}), so \
      the run does not replace it"
  | .ok metadata =>
    unless metadata.type == .file do return refuse (entryName metadata.type)
    match ← (IO.FS.readBinFile path).toBaseIO with
    | .error error => return refuse s!"a regular file that cannot be read ({error})"
    | .ok bytes =>
      if bytes.isEmpty then return none
      let some text := String.fromUTF8? bytes | return refuse "a file that is not UTF-8 text"
      match Json.parse text with
      | .ok value => return if kind.identifies value then none else refuse "a JSON document"
      | .error _ => return refuse "a file that is not a JSON document"

/-- Where the entry that `path` names is: the real path of the nearest present ancestor of its
directory (`Regula.Filesystem.observeRealPath`), with `path` read from the working directory when it
is relative, and the names below that ancestor, the last of them the entry's own. The entry itself
is not resolved, so a link at `path` is a place of its own. -/
def place (path : FilePath) : IO (FilePath × List String) := do
  let path ← if path.isAbsolute then pure path else pure ((← IO.currentDir) / path)
  let components := path.components
  for count in (List.range (components.length - 1)).reverse do
    let ancestor := System.mkFilePath (components.take (count + 1))
    let ancestor : FilePath := if ancestor.toString.isEmpty then ⟨"/"⟩ else ancestor
    if let .ok real ← (Regula.Filesystem.observeRealPath ancestor).toBaseIO then
      return (real, components.drop (count + 1))
  return (⟨"/"⟩, components.drop 1)

/-- `text` with each ASCII letter in lower case. -/
private def fold (text : String) : String := text.map Char.toLower

/-- Whether a name below a place may name something that a file system resolves or folds to a
different name: `.`, `..`, or a name with a character outside ASCII, whose case or Unicode
normalization a file system may fold. -/
private def doubtful (name : String) : Bool :=
  name == "." || name == ".." || name.any fun c : Char => c.toNat ≥ 128

/-- Whether two places (`place`) may be one entry: their real ancestors and the names below them
are one path once each ASCII letter is in lower case, as on a file system that folds case; or a
name below one of them is doubtful (`doubtful`) and their real ancestors are one path. -/
def sameEntry (a b : FilePath × List String) : Bool :=
  if a.2.any doubtful || b.2.any doubtful then fold a.1.toString == fold b.1.toString
  else fold (System.mkFilePath (a.1.toString :: a.2)).toString ==
    fold (System.mkFilePath (b.1.toString :: b.2)).toString

/-- The reason to refuse writing documents of the given kinds at the given paths, if there is
one: a destination that holds a file that the run may not replace (`ownershipRefusal`), or two
destinations that may be one entry (`sameEntry`), whose writes would replace each other. -/
def refusal (destinations : List (Kind × FilePath)) : IO (Option String) := do
  for (kind, path) in destinations do
    if let some reason ← ownershipRefusal kind path then return some reason
  let mut seen : List (FilePath × FilePath × List String) := []
  for (_, path) in destinations do
    let entry ← place path
    if let some (other, _) := seen.find? (sameEntry entry ·.2) then
      return some s!"{other} and {path} may name one entry, so the writes of the run would \
        replace each other"
    seen := (path, entry) :: seen
  return none

/-- Write `contents` at `path` as a document of `kind`: stop with nothing written when a file there
is not one that the run may replace (`ownershipRefusal`), and otherwise replace the entry at
`path` (`Regula.Filesystem.writeReplacing`). -/
def write (kind : Kind) (path : FilePath) (contents : ByteArray) : IO Unit := do
  if let some reason ← ownershipRefusal kind path then throw (IO.userError reason)
  Regula.Filesystem.writeReplacing path contents

end Regula.Destination
