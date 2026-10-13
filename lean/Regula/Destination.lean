import Lean.Data.Json
import RegulaCore.Destination
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
  destination's kind (`Target.ownershipRefusal`, `Kind.identifies`). A file that holds bytes and
  is not such a document, such as a source, a configuration file or a Markdown document, is thus
  never replaced. The program marks its other destinations, then refuses the run (`refusal`).
- A program refuses an invocation two of whose destinations may be one entry (`sameEntry`), after
  it marks them.

A destination is a `Target`, whose path is private to this module: a program writes a destination
only through `Target.writeJson` or `Target.writeText`, which apply the first two rules and write
only a document that the destination's kind identifies, so a later run of the same kind replaces
it and a run of another kind never does (`identifies_disjoint`). An empty file is replaced: it
holds no bytes to lose, and a destination that `mktemp` made is such a file. -/

namespace Regula.Destination

open Lean System

/-- A destination: a file that a program of Regula marks incomplete before its run and later
writes a document of `kind` at. Its path is private to this module, so a program writes it only
through `Target.writeJson` or `Target.writeText`, and reads it through `Target.read`. -/
structure Target where
  private mk ::
  /-- The kind of document that the program writes there. -/
  kind : Kind
  /-- The path that names the destination. -/
  private file : FilePath

/-- The destination of `kind` that `path` names. -/
def target (kind : Kind) (path : FilePath) : Target := ⟨kind, path⟩

instance : ToString Target := ⟨fun target => target.file.toString⟩

/-- The text of the file at the destination. -/
def Target.read (target : Target) : IO String := IO.FS.readFile target.file

/-- Whether an entry is at the destination, following a link. -/
def Target.pathExists (target : Target) : BaseIO Bool := target.file.pathExists

/-- The real path of the destination (`IO.FS.realPath`). -/
def Target.realPath (target : Target) : IO FilePath := IO.FS.realPath target.file

/-- The path of a file beside the destination whose name is the destination's with `suffix`
appended, such as the raw directory of rule-example evidence. It is not a destination. -/
def Target.beside (target : Target) (suffix : String) : FilePath :=
  ⟨target.file.toString ++ suffix⟩

/-- The directory of the destination. -/
def Target.directory (target : Target) : FilePath := target.file.parent.getD ⟨"."⟩

/-- A completed result of an earlier version of Regula: the members that a result requires
(`Kind.required`) with the identity of a release that no current build writes, and the status
`completed`. A control seeds a destination with it to require that a run replace it. -/
def earlierResult : String :=
  "{\"schemaVersion\":3,\"producerVersion\":\"0.0.0\",\"toolchain\":\"leanprover/lean4:v4.34.0\",\
    \"sourceRevision\":\"0000000\",\"scope\":\"file\",\"mode\":\"freshFile\",\
    \"status\":\"completed\",\"diagnostics\":[],\"unresolved\":[]}\n"

/-- The name of a kind of entry in a reason to refuse a destination. -/
private def entryName : IO.FS.FileType → String
  | .dir => "a directory"
  | .file => "a regular file"
  | .symlink => "a symbolic link"
  | .other => "an entry that is not a directory, a regular file or a symbolic link"

/-- The reason to refuse to write at the destination, if there is one: something is there, by a
read that follows no link (`Regula.Filesystem.observeMetadata`), and it is not a regular file that
is empty or whose text is a JSON document of the destination's kind (`Kind.identifies`). An error
of that read other than the absence of the entry is a reason too. An empty file holds no bytes to
lose, so a destination that `mktemp` made is replaced; an empty input named as a destination is
replaced as well. -/
def Target.ownershipRefusal (target : Target) : IO (Option String) := do
  let refuse (what : String) : Option String := some s!"{target} is {what}, not \
    {target.kind.description} that Regula wrote, so the run does not replace it"
  match ← (Regula.Filesystem.observeMetadata target.file).toBaseIO with
  | .error (.noFileOrDirectory ..) => return none
  | .error error => return some s!"{target} cannot be read without following a link ({error}), \
      so the run does not replace it"
  | .ok metadata =>
    unless metadata.type == .file do return refuse (entryName metadata.type)
    match ← (IO.FS.readBinFile target.file).toBaseIO with
    | .error error => return refuse s!"a regular file that cannot be read ({error})"
    | .ok bytes =>
      if bytes.isEmpty then return none
      let some text := String.fromUTF8? bytes | return refuse "a file that is not UTF-8 text"
      match Json.parse text with
      | .ok value => return if target.kind.identifies value then none else refuse "a JSON document"
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

/-- The reason to refuse writing at the given destinations, if there is one: a destination that
holds a file that the run may not replace (`Target.ownershipRefusal`), or two destinations that
may be one entry (`sameEntry`), whose writes would replace each other. -/
def refusal (destinations : List Target) : IO (Option String) := do
  for target in destinations do
    if let some reason ← target.ownershipRefusal then return some reason
  let mut seen : List (Target × FilePath × List String) := []
  for target in destinations do
    let entry ← place target.file
    if let some (other, _) := seen.find? (sameEntry entry ·.2) then
      return some s!"{other} and {target} may name one entry, so the writes of the run would \
        replace each other"
    seen := (target, entry) :: seen
  return none

/-- Write `text`, the encoding of `value`, at the destination: stop with nothing written when
`value` is not a document of the destination's kind, which a later run of that kind could not
replace (`Kind.identifies`), or when a file there is not one that the run may replace
(`Target.ownershipRefusal`); otherwise replace the entry there
(`Regula.Filesystem.writeReplacing`). -/
private def Target.writeChecked (target : Target) (value : Json) (text : String) : IO Unit := do
  unless target.kind.identifies value do
    throw <| IO.userError s!"nothing was written at {target}: the document is not \
      {target.kind.description}, which a later run could not replace"
  if let some reason ← target.ownershipRefusal then throw (IO.userError reason)
  Regula.Filesystem.writeReplacing target.file text.toUTF8

/-- Write `value` at the destination, encoded by `render` (by default compact, with a final
newline), as `Target.writeChecked` does. -/
def Target.writeJson (target : Target) (value : Json)
    (render : Json → String := fun value => value.compress ++ "\n") : IO Unit :=
  target.writeChecked value (render value)

/-- Write `text`, the text of a JSON document, at the destination, as `Target.writeChecked` does;
text that is not JSON stops with nothing written. -/
def Target.writeText (target : Target) (text : String) : IO Unit := do
  match Json.parse text with
  | .ok value => target.writeChecked value text
  | .error error => throw <| IO.userError s!"nothing was written at {target}: the text is not \
      JSON ({error})"

/-- Mark the destination incomplete with `fields`, to which each member that its kind requires
is added with the value `null` (`Kind.mark`), as `Target.writeJson` writes. -/
def Target.mark (target : Target) (fields : List (String × Json)) : IO Unit :=
  target.writeJson (target.kind.mark fields)

end Regula.Destination
