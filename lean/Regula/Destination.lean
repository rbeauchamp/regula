import Lean.Data.Json
import RegulaCore.Destination
import Regula.Filesystem

/-! # The destinations that a run of Regula may replace

A program of Regula marks each result destination that its arguments name before any code of the
run reads an input (`Regula.TaskManager.guard`), so a destination that names one of its inputs
would replace that input before the run reads it. Four rules keep the mark and the run's writes
from losing a file that is not Regula's, whatever files the run reads:

- Each destination is read, before anything is made, as the real path of its longest present
  prefix and the names below it (`place`), and a destination with a `..` among those names is
  refused. So the entry that the rules below read is the one that the write replaces once it
  makes the absent directories.
- A write replaces the entry at the destination and never writes into the file that the entry
  names (`Regula.Filesystem.writeReplacing`), so a hard link there keeps the file that it shares.
- A write, and so a mark, stops with nothing written when the destination holds something other
  than nothing, an empty regular file, or a regular file whose text is a document that one of
  Regula's readers identifies as Regula's (`ownershipRefusal`, `regulaDocument`). A file that holds
  bytes and is not such a document, such as a source, a configuration file or a Markdown document,
  is thus never replaced. A symbolic link there is refused too, so nothing is written through it,
  and a reader that follows it still reads the file at its target, which may be an earlier
  completed result. The program marks its other destinations, then refuses the run (`refusal`).
- A program refuses an invocation two of whose destinations may be one entry (`sameEntry`), after
  it marks them.

A document of Regula of any kind is replaceable, not only one of the kind that the destination
holds: Regula can make each document that it wrote again. The rules read the members of a file,
not who wrote it, so a file in one of Regula's forms that Regula did not write, such as a tracked
fixture of the repository, is replaced too when a destination names it. The last rule keeps the
destinations of one run from replacing each other. An
empty file is replaced: it holds no bytes to lose, and a destination that `mktemp` made is such a
file. -/

namespace Regula.Destination

open Lean System

/-- A completed result of an earlier version of Regula: the identity members of a document of
Regula (`Regula.RegistryCodec.identityFields`) with values that no current build writes, and the
other members that the readers of a result require (`completedSignatures`). A control seeds a
destination with it to require that a run replace it. -/
def earlierResult : String :=
  "{\"schemaVersion\":3,\"producerVersion\":\"0.0.0\",\"toolchain\":\"leanprover/lean4:v4.34.0\",\
    \"sourceRevision\":\"0000000\",\"scope\":\"file\",\"mode\":\"freshFile\",\
    \"status\":\"completed\",\"diagnostics\":[],\"unresolved\":[],\"sourceTexts\":[],\
    \"stages\":[],\"stagesCompleted\":[],\"complete\":true,\"stagesNotRun\":[],\"rules\":[]}\n"

/-- The reason to refuse to write at `path`, if there is one (`ownershipDecision`): something is
there, by a read that follows no link (`Regula.Filesystem.observeMetadata`), and it is not a
regular file that is empty or whose text is a JSON document that one of Regula's readers identifies
as Regula's (`regulaDocument`). An error of that read other than the absence of the entry is a
reason too. It reads the bytes of a regular file alone. An empty file holds no bytes to lose, so a
destination that `mktemp` made is replaced; an empty input named as a destination is replaced as
well. -/
def ownershipRefusal (path : FilePath) : IO (Option String) := do
  let entry ← (IO.FS.Metadata.type <$> Regula.Filesystem.observeMetadata path).toBaseIO
  let contents ←
    (if entry matches .ok .file then IO.FS.readBinFile path else pure .empty).toBaseIO
  return ownershipDecision path entry contents

/-- The entry that a destination names, by `place`: the real path of its longest present prefix and
the names below it. -/
def entryPath (found : FilePath × List String) : FilePath :=
  found.2.foldl (fun directory (name : String) => directory / name) found.1

/-- Where the entry that `path` names is, without making anything: the real path of the longest
prefix of its directory that is present (`Regula.Filesystem.observeRealPath`), with `path` read from
the working directory when it is relative, and the names below that prefix (`plainNames`), the last
of them the entry's own. The entry itself is not resolved, so a link at `path` is a place of its
own. A prefix is absent when neither its real path nor its entry, by a read that follows no link,
is there. It is the reason to refuse `path` when its last component names no file
(`System.FilePath.fileName`), such as `out/`, `out/.` or `out/..`, read before any name is dropped;
when a name below the prefix is `..`; or when a prefix cannot be resolved, with the error of each
read. With plain names, `entryPath` is the entry that a write replaces once it makes the absent
directories, when no process makes an entry there after this read, which is trusted. -/
def place (path : FilePath) : IO (Except String (FilePath × List String)) := do
  if path.fileName.isNone then
    return .error s!"{path} names no file, so the run writes nothing there"
  let path ← if path.isAbsolute then pure path else pure ((← IO.currentDir) / path)
  let components := path.components
  let below (real : FilePath) (names : List String) : Except String (FilePath × List String) :=
    match plainNames names with
    | some names@(_ :: _) => .ok (real, names)
    | some [] => .error s!"{path} names no file, so the run writes nothing there"
    | none => .error s!"{path} has a `..` component below {real}, its longest prefix that is \
        present, so the entry that it names depends on what the run makes; the run writes nothing \
        there"
  for count in (List.range (components.length - 1)).reverse do
    let ancestor := System.mkFilePath (components.take (count + 1))
    let ancestor : FilePath := if ancestor.toString.isEmpty then ⟨"/"⟩ else ancestor
    match ← (Regula.Filesystem.observeRealPath ancestor).toBaseIO with
    | .ok real => return below real (components.drop (count + 1))
    | .error absent@(.noFileOrDirectory ..) =>
      match ← (Regula.Filesystem.observeMetadata ancestor).toBaseIO with
      | .error (.noFileOrDirectory ..) => continue
      | .ok metadata =>
        if metadata.type == .symlink then
          return .error s!"{ancestor}, a prefix of {path}, is a symbolic link whose target is \
            absent ({absent}), so the run writes nothing there"
        return .error s!"{ancestor}, a prefix of {path}, is {entryName metadata.type} that cannot \
          be resolved ({absent}), so the run writes nothing there"
      | .error error => return .error s!"{ancestor}, a prefix of {path}, cannot be resolved \
          ({absent}) and cannot be read without following a link ({error}), so the run writes \
          nothing there"
    | .error error => return .error s!"{ancestor}, a prefix of {path}, cannot be resolved \
        ({error}), so the run writes nothing there"
  return below ⟨"/"⟩ (components.drop 1)

/-- `text` with each ASCII letter in lower case. -/
private def fold (text : String) : String := text.map Char.toLower

/-- Whether a name below a place may name something that a file system folds to a different name:
a name with a character outside ASCII, whose case or Unicode normalization a file system may fold.
-/
private def doubtful (name : String) : Bool :=
  name.any fun c : Char => c.toNat ≥ 128

/-- Whether two places (`place`) may be one entry: their real prefixes and the names below them
are one path once each ASCII letter is in lower case, as on a file system that folds case; or a
name below one of them is doubtful (`doubtful`) and their real prefixes are one path. The names are
plain (`plainNames`), so the comparison is exact up to that folding. -/
def sameEntry (a b : FilePath × List String) : Bool :=
  if a.2.any doubtful || b.2.any doubtful then fold a.1.toString == fold b.1.toString
  else fold (System.mkFilePath (a.1.toString :: a.2)).toString ==
    fold (System.mkFilePath (b.1.toString :: b.2)).toString

/-- The reason to refuse writing at the given destinations, if there is one, decided before
anything is made: a destination that `place` refuses; two destinations that may be one entry
(`sameEntry`), whose writes would replace each other; or else a destination whose entry
(`entryPath`) holds a file that the run may not replace (`ownershipRefusal`). Overlap is decided
before ownership, so a run that names one entry twice gets that reason whatever the entry holds. -/
def refusal (destinations : List FilePath) : IO (Option String) := do
  let mut seen : List (FilePath × FilePath × List String) := []
  for path in destinations do
    match ← place path with
    | .error reason => return some reason
    | .ok entry =>
      if let some (other, _) := seen.find? (sameEntry entry ·.2) then
        return some s!"{other} and {path} may name one entry, so the writes of the run would \
          replace each other"
      seen := seen ++ [(path, entry)]
  for (_, entry) in seen do
    if let some reason ← ownershipRefusal (entryPath entry) then return some reason
  return none

/-- Write `text` at `path`: find its entry without making anything (`place`, `entryPath`), stop with
nothing written when `place` refuses `path` or the entry holds a file that the run may not replace
(`ownershipRefusal`), and otherwise replace the entry (`Regula.Filesystem.writeReplacing`), which
makes its absent directories. The entry that the check reads is the one that the rename replaces:
its names below the present prefix are plain, so the directories made there are the real path of
its directory. -/
def write (path : FilePath) (text : String) : IO Unit := do
  let entry ← match ← place path with
    | .ok found => pure (entryPath found)
    | .error reason => throw (IO.userError reason)
  if let some reason ← ownershipRefusal entry then throw (IO.userError reason)
  Regula.Filesystem.writeReplacing entry text.toUTF8

/-- Write `value` at `path`, encoded by `render` (by default compact, with a final newline), as
`write` does. -/
def writeJson (path : FilePath) (value : Json)
    (render : Json → String := fun value => value.compress ++ "\n") : IO Unit :=
  write path (render value)

end Regula.Destination
