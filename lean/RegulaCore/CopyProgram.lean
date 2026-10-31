import Lean

/-! # Construction of plain filesystem trees

One implementation for source copies and generated workspaces. It captures only directories and
regular files through no-follow metadata, then creates the selected entries. There is no inspection
of a finished copy, no link creator, and no recursive system copy. This module imports only the
toolchain so the cold verification and provisioning drivers can execute its source before the
package has artifacts. `RegulaCore.CopyConstruction` states its filesystem-model contract.

It reads whether a directory is present with its own copy of `Regula.Filesystem.isDirectory`
(`Construction.isDirectory`), since it cannot import `RegulaCore.Presence`.
-/

namespace Regula.Filesystem.Construction

open System

/-- Whether a directory is at `path`, following symbolic links: `true` for a directory, `false` for
another kind of file or when the read fails with `noFileOrDirectory`, and the read's error for each
other error. Lean's `System.FilePath.isDir` returns `false` for every error of `metadata`. This
program cannot import `RegulaCore.Presence`; `Regula.Filesystem.Construction.isDirectory_eq`
proves this equal to `Regula.Filesystem.isDirectory`. -/
def isDirectory (path : FilePath) : IO Bool := do
  match ← path.metadata.toBaseIO with
  | .ok metadata => return metadata.type == .dir
  | .error (.noFileOrDirectory ..) => return false
  | .error error => throw error

/-- The only entries that construction can create. Copied files use 0644; explicitly generated executable files name their required rights. -/
inductive Payload where
  /-- An empty directory, whose children are separate instructions. -/
  | directory
  /-- A regular file, with its complete bytes and its rwx bits. -/
  | file (bytes : ByteArray) (rights : UInt32 := 420)

/-- An instruction relative to the destination root. `constructWith` admits its path before
using it. A symbolic link and a special file have no instruction. -/
structure Item where
  /-- The path components below the constructed root. -/
  relative : List String
  /-- What to create there. -/
  payload : Payload

/-- The entry kind of a construction instruction. -/
def Payload.kind : Payload → IO.FS.FileType
  | .directory => .dir
  | .file .. => .file

instance (payload : Payload) : Decidable (payload.kind = .file) := by
  cases payload with
  | directory => exact isFalse (by intro h; cases h)
  | file bytes rights => exact isTrue rfl

/-- Every consumer-selected path has a regular-file instruction in this captured layout. -/
def Covers (required : List (List String)) (items : List Item) : Prop :=
  ∀ path ∈ required, ∃ item ∈ items, item.relative = path ∧ item.payload.kind = .file

instance (required : List (List String)) (items : List Item) : Decidable (Covers required items) :=
  inferInstanceAs (Decidable (∀ path ∈ required,
    ∃ item ∈ items, item.relative = path ∧ item.payload.kind = .file))

/-- Admit exactly instruction lists that retain the consumer's entire original file domain. -/
def covers (required : List (List String)) (items : List Item) : Bool :=
  decide (Covers required items)

/-- A path component that names one entry and cannot redirect a path join. -/
def Component (name : String) : Prop :=
  name ≠ "" ∧ name ≠ "." ∧ name ≠ ".." ∧
    ∀ c ∈ name.toList, c ≠ '/' ∧ c ≠ '\\' ∧ c ≠ '\x00'

instance (name : String) : Decidable (Component name) := inferInstanceAs
  (Decidable (name ≠ "" ∧ name ≠ "." ∧ name ≠ ".." ∧
    ∀ c ∈ name.toList, c ≠ '/' ∧ c ≠ '\\' ∧ c ≠ '\x00'))

/-- Whether every component of a relative path names one entry. -/
def Relative (path : List String) : Prop := ∀ name ∈ path, Component name

instance (path : List String) : Decidable (Relative path) := inferInstanceAs
  (Decidable (∀ name ∈ path, Component name))

/-- Join admitted relative components to a root. -/
def location (root : FilePath) (relative : List String) : FilePath :=
  relative.foldl (fun path name => path / FilePath.mk name) root

/-- The operations used by the same construction program in IO and in a filesystem model.
Directory and file creation must be exclusive at their exact destinations. -/
structure Ops (m : Type → Type) where
  /-- Read the entry itself, never a final symbolic link's target. -/
  metadata : FilePath → m IO.FS.Metadata
  /-- Enumerate the stored names of immediate directory entries. -/
  names : FilePath → m (List String)
  /-- Resolve a path to its canonical place. -/
  realPath : FilePath → m FilePath
  /-- Read a regular file's bytes, with the rights chosen for its copy. -/
  bytes : FilePath → m (ByteArray × UInt32)
  /-- Create an empty directory exclusively. -/
  directory : FilePath → m Unit
  /-- Create a regular file exclusively, write its bytes, and set its rwx bits. -/
  file : FilePath → ByteArray → UInt32 → m Unit

/-- Read the final entry's kind, distinguishing absence from every other metadata error. -/
def kindWith {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (path : FilePath) : m (Option IO.FS.FileType) :=
  tryCatchThe IO.Error (do return some (← ops.metadata path).type) fun
    | .noFileOrDirectory .. => pure none
    | error => throw error

/-- Establish an empty destination through primitive reads and exclusive mkdir. The target's
existing ancestors must be at their own place; an existing target must be an empty directory.
An absent-target read never grants an overwrite: mkdir itself refuses an occupied destination. -/
def beginWith {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (target : FilePath) : m Unit := do
  let some parent := target.parent | throw <| IO.userError s!"copy root has no parent: {target}"
  unless (← ops.realPath parent) == parent do
    throw <| IO.userError s!"copy parent is not at its own place: {parent}"
  match ← kindWith ops target with
  | none => ops.directory target
  | some .dir =>
    unless (← ops.realPath target) == target do
      throw <| IO.userError s!"copy root is not at its own place: {target}"
    unless (← ops.names target).isEmpty do
      throw <| IO.userError s!"copy root is occupied: {target}"
  | _ => throw <| IO.userError s!"copy root is not a directory: {target}"

/-- Refuse a non-directory/non-file entry before reading its bytes or descending into it.
Selection is closed under descent: an excluded directory is never read. Fuel bounds source
directory depth, not the number of entries; exhaustion fails, never truncates a copy. -/
def captureWith {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (selected : FilePath → Bool) : Nat → FilePath → List String → m (List Item)
  | 0, source, _ => throw <| IO.userError s!"copy source depth exhausted at {source}"
  | depth + 1, source, relative => do
    unless selected source do return []
    unless Relative relative do throw <| IO.userError s!"invalid copy path: {relative}"
    match (← ops.metadata source).type with
    | .file =>
      let (bytes, rights) ← ops.bytes source
      return [⟨relative, .file bytes rights⟩]
    | .dir =>
      let names ← ops.names source
      let children ← names.foldlM (fun items name => do
        unless Component name do throw <| IO.userError s!"invalid directory entry: {name}"
        return items ++ (← captureWith ops selected depth (source / name) (relative ++ [name]))) []
      return ⟨relative, .directory⟩ :: children
    | kind => throw <| IO.userError s!"copy refused {source}: {repr kind} is not a directory or \
        a regular file"

/-- Execute the instructions after the root has been established. Structural recursion exposes
each primitive creation to the construction theorem. -/
def emitWith {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (target : FilePath) : List Item → m Unit
  | [] => pure ()
  | item :: rest => do
    unless Relative item.relative do
      throw <| IO.userError s!"invalid construction path: {item.relative}"
    match item.payload with
    | .directory => unless item.relative.isEmpty do ops.directory (location target item.relative)
    | .file bytes rights =>
      if item.relative.isEmpty then throw <| IO.userError "a construction root must be a directory"
      ops.file (location target item.relative) bytes rights
    emitWith ops target rest

/-- Create the instructions in order after establishing an empty root. There is no primitive
for creating a link or a special entry. Every file is opened with exclusive creation; each
non-root directory is created exclusively. An already occupied destination fails. -/
def constructWith {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (target : FilePath) (items : List Item) : m Unit := do
  beginWith ops target
  emitWith ops target items

/-- Refuse a narrowed consumer domain before the first write, then execute the shared
exclusive constructor. This guard inspects instructions, never a completed filesystem copy. -/
def constructSelectedWith {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (target : FilePath) (required : List (List String)) (items : List Item) : m Unit := do
  unless covers required items do
    throw <| IO.userError "copy instructions omit a selected source file"
  constructWith ops target items

/-- Capture the selected source entries, then construct them, using the same operations that
the filesystem-model theorem names. No destination is written while source entries are captured. -/
def copyWith {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (source target : FilePath) (selected : FilePath → Bool) (depth : Nat := 4096) :
    m (List Item) := do
  let items ← captureWith ops selected depth source []
  constructWith ops target items
  return items

/-! ## Directory enumeration

Lean v4.35.0's `System.FilePath.readDir` cannot tell the end of a directory from a failed read: its
native loop (`runtime/io.cpp:1076-1098`) stops at the first null `readdir` result and returns the
names it has read. Regula lists a directory through an admitted GNU coreutils `ls` instead. A program
is admitted only when its own source, at the release that its identity line names, establishes that
it reads each entry and exits nonzero after a failed read; each admitted release checks `errno`
after every `readdir`. Its listing decodes exactly (`decodeListing_zero` and `decodeListing_gnu` in
`RegulaCore.CopyConstruction`). -/

/-- The byte that ends each name that `ls --zero` writes. -/
def nul : UInt8 := 0

/-- The byte that ends each name of an escaped listing. -/
def newline : UInt8 := 10

/-- The byte that starts an escape of an escaped listing. -/
def backslash : UInt8 := 92

/-- The records of a listing whose records each end with `separator`, the current record held
reversed in `acc`: `none` unless the listing ends with `separator` and no record is empty. -/
def splitRecords (separator : UInt8) : List UInt8 → List UInt8 → Option (List (List UInt8))
  | [], [] => some []
  | [], _ :: _ => none
  | byte :: rest, acc =>
    if byte = separator then
      if acc.isEmpty then none else (splitRecords separator rest []).map (acc.reverse :: ·)
    else splitRecords separator rest (byte :: acc)

/-- A printable ASCII byte other than the backslash, which an escaped listing writes as itself. -/
def literalByte (byte : UInt8) : Bool :=
  decide (32 ≤ byte.toNat ∧ byte.toNat ≤ 126 ∧ byte ≠ backslash)

/-- The value of an octal digit. -/
def octalDigit (byte : UInt8) : Option Nat :=
  if 48 ≤ byte.toNat ∧ byte.toNat ≤ 55 then some (byte.toNat - 48) else none

/-- The byte that a backslash and `letter` stand for, when `letter` is not an octal digit: one of
the seven control characters for its C letter, a printable ASCII byte other than a letter or a
digit for itself, and nothing for any other byte. -/
def escapeMeaning (letter : UInt8) : Option UInt8 :=
  match letter.toNat with
  | 97 => some 7
  | 98 => some 8
  | 102 => some 12
  | 110 => some 10
  | 114 => some 13
  | 116 => some 9
  | 118 => some 11
  | n => if (32 ≤ n ∧ n ≤ 47) ∨ (58 ≤ n ∧ n ≤ 64) ∨ (91 ≤ n ∧ n ≤ 96) ∨ (123 ≤ n ∧ n ≤ 126)
      then some letter else none

/-- The bytes of a name that an escaped listing writes as `line`: a literal byte for itself, a
backslash and three octal digits, the first at most 3, for the byte they give, and a backslash and
another byte for what `escapeMeaning` gives. `none` for every other line. -/
def unescape : List UInt8 → Option (List UInt8)
  | [] => some []
  | byte :: rest =>
    if byte ≠ backslash then
      if literalByte byte then (unescape rest).map (byte :: ·) else none
    else match rest with
      | [] => none
      | letter :: rest =>
        match octalDigit letter with
        | some high =>
          if high ≤ 3 then
            match rest with
            | middle :: low :: rest =>
              match octalDigit middle, octalDigit low with
              | some middle, some low =>
                (unescape rest).map (UInt8.ofNat (64 * high + 8 * middle + low) :: ·)
              | _, _ => none
            | _ => none
          else none
        | none => (escapeMeaning letter).bind fun meaning => (unescape rest).map (meaning :: ·)

/-- How an admitted listing program writes the names of a directory. -/
inductive ListingForm where
  /-- Each name as it is stored, ended by a NUL byte: GNU `ls --zero`. -/
  | zero
  /-- Each name escaped as `unescape` reads it, ended by a newline: GNU `ls --quoting-style=escape`.
  -/
  | escaped
  deriving DecidableEq, Repr

/-- The names of a listing written in `form`: `none` unless every record decodes. -/
def decodeListing : ListingForm → List UInt8 → Option (List (List UInt8))
  | .zero, bytes => splitRecords nul bytes []
  | .escaped, bytes => (splitRecords newline bytes []).bind fun lines => lines.mapM unescape

/-- An admitted directory-listing program. -/
structure Enumerator where
  /-- The program, a name looked up on `PATH` or an absolute path. -/
  program : String
  /-- The options written before `--` and the directory. -/
  options : Array String
  /-- How the program writes names. -/
  form : ListingForm
  /-- What the program identified itself as, for messages. -/
  identity : String

/-- The environment changes of each run of a listing program: the C locale, so every byte outside
printable ASCII is escaped, and none of the variables that change what `ls` writes or how it reads
its options. -/
def listingEnvironment : Array (String × Option String) :=
  #[("LC_ALL", some "C"), ("POSIXLY_CORRECT", none), ("QUOTING_STYLE", none), ("LS_COLORS", none),
    ("CLICOLOR", none), ("CLICOLOR_FORCE", none), ("LSCOLORS", none), ("COLUMNS", none)]

/-- Run a listing program with `args`; its exit code, its complete output as bytes and its error
text.

Assumes: Lean v4.35.0 `Init/System/IO.lean:1002-1003,1544-1557` reads binary stdout, drains stderr
and waits for the process, and `Init/System/IO.lean:1441-1448` applies the environment changes in
order. Process execution is trusted. -/
def listingOutput (program : String) (args : Array String) : IO (UInt32 × ByteArray × String) := do
  let child ← IO.Process.spawn
    { cmd := program, args := args, env := listingEnvironment, stdin := .null, stdout := .piped,
      stderr := .piped }
  let stdout ← IO.asTask child.stdout.readBinToEnd Task.Priority.dedicated
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  let bytes ← IO.ofExcept stdout.get
  return (exitCode, bytes, stderr)

/-- The GNU coreutils releases whose `ls` source Regula has read, as major and minor version: 9.0 to
9.12 and 8.32. Regula refuses any other release until it reads that release's source too. -/
def gnuReleases : List (Nat × Nat) := (List.range 13).map (9, ·) ++ [(8, 32)]

/-- The first line that GNU `ls --version` of `release` writes. -/
def gnuIdentity (release : Nat × Nat) : String := s!"ls (GNU coreutils) {release.1}.{release.2}"

/-- The first line of a program's output. -/
def firstLine (text : String) : String := (text.splitOn "\n").headD ""

/-- The admitted release whose identity line is exactly the first line of `text`, the output of
`ls --version`; `none` for any other line, a later patch release such as `9.12.1` among them. -/
def gnuRelease? (text : String) : Option (Nat × Nat) :=
  gnuReleases.find? (gnuIdentity · == firstLine text)

/-- The enumerator of the admitted GNU release `release` run as `program`: release 9 lists with
`--zero`, which writes each name as stored, and 8.32 with its escape quoting style. -/
def gnuEnumerator (program : String) (release : Nat × Nat) : Enumerator :=
  let identity := s!"{program} ({gnuIdentity release})"
  if release.1 = 9 then ⟨program, #["-A", "-U", "--zero"], .zero, identity⟩
  else ⟨program, #["-1", "-A", "-U", "--quoting-style=escape", "--show-control-chars",
    "--color=never", "--indicator-style=none"], .escaped, identity⟩

/-- The first admitted listing program: an admitted GNU `ls` 9 release as `gls` or `ls` on `PATH`
(`gls` first on macOS, whose `ls` is Apple's), otherwise GNU `ls` 8.32 there. Otherwise it refuses
with the reason for each program it tried, the identity line it refused among them. Apple's `ls` is
not admitted: its listing comes from the fts of the system's C library, whose release its identity
does not name.

Assumes: the program found is the release it identifies as. -/
def locate : IO Enumerator := do
  let mut reasons : Array String := #[]
  let mut escaped : Option Enumerator := none
  let programs := if System.Platform.isOSX then ["gls", "ls"] else ["ls", "gls"]
  for program in programs do
    match ← (listingOutput program #["--version"]).toBaseIO with
    | .error error => reasons := reasons.push s!"{program}: {error}"
    | .ok (exitCode, bytes, _) =>
      let text := (String.fromUTF8? bytes).getD ""
      match (if exitCode == 0 then gnuRelease? text else none) with
      | some release =>
        let enumerator := gnuEnumerator program release
        if enumerator.form == .zero then return enumerator
        if escaped.isNone then escaped := some enumerator
      | none =>
        reasons := reasons.push
          s!"{program}: --version exited with {exitCode} and the first line '{firstLine text}'"
  if let some enumerator := escaped then return enumerator
  throw <| IO.userError s!"no admitted directory-listing program: Regula lists directories through \
    GNU coreutils ls 9.0 to 9.12 or 8.32, as gls or ls on PATH ({"; ".intercalate reasons.toList})"

/-- A stored name that names one entry of its directory: not `.` or `..`, and holding neither `/`
nor NUL. -/
def entryName (name : String) : Bool :=
  name != "." && name != ".." && name.toList.all fun c => c != '/' && c != '\x00'

/-- The stored names of the directory `path`, read through `enumerator`. It refuses unless the
program exits 0 with no error text and its listing decodes to UTF-8 names that each name one entry,
so a failed read of the directory refuses instead of truncating the names. The trailing `/` makes
`ls` list a link's target directory, as `readDir` does, and refuse anything but a directory; an empty
path, which with that `/` would name the root directory, refuses. -/
def Enumerator.names (enumerator : Enumerator) (path : FilePath) : IO (List String) := do
  if path.toString.isEmpty then throw <| IO.userError "listing refused: the directory path is empty"
  let (exitCode, bytes, stderr) ← listingOutput enumerator.program
    (enumerator.options ++ #["--", path.toString ++ "/"])
  unless exitCode == 0 && stderr.isEmpty do
    throw <| IO.userError s!"listing {path} through {enumerator.identity} failed with exit code \
      {exitCode}: {stderr}"
  let some names := decodeListing enumerator.form bytes.toList
    | throw <| IO.userError s!"the listing of {path} by {enumerator.identity} does not decode"
  names.mapM fun name => do
    let some text := String.fromUTF8? (ByteArray.mk name.toArray)
      | throw <| IO.userError s!"a name in {path} is not UTF-8"
    unless entryName text do throw <| IO.userError s!"{path} lists an invalid name: {text}"
    return text

/-- The stored names of the directory `path`, through the program that `locate` admits. -/
def listNames (path : FilePath) : IO (List String) := do
  (← locate).names path

/-- The entries of the directory `path`, in the shape that `System.FilePath.readDir` returns, read
through the program that `locate` admits. -/
def listDirectory (path : FilePath) : IO (Array IO.FS.DirEntry) := do
  return ((← listNames path).map fun name => { root := path, fileName := name }).toArray

/-- Each path below `root`, parents before their children, descending into each directory that
`enter` admits. It is `System.FilePath.walkDir` of Lean v4.35.0 (`Init/System/IO.lean:1174-1200`),
written again here so that each directory is listed through `enumerator`. Like `walkDir`, it
follows links to directories and ignores an entry that vanishes during the walk. Unlike it, `depth`
bounds the nesting and its exhaustion refuses, so a cycle of links fails instead of running
forever. -/
def walkWith (enumerator : Enumerator) (enter : FilePath → IO Bool) :
    Nat → FilePath → Array FilePath → IO (Array FilePath)
  | 0, path, _ => throw <| IO.userError s!"walk depth exhausted at {path}"
  | depth + 1, path, found => do
    unless (← enter path) do return found
    let mut found := found
    for name in ← enumerator.names path do
      let child := path / name
      found := found.push child
      match ← child.metadata.toBaseIO with
      | .ok { type := .dir, .. } => found ← walkWith enumerator enter depth child found
      | .ok _ => pure ()
      | .error (.noFileOrDirectory ..) => pure ()
      | .error error => throw error
    return found

/-- `walkWith` from `root`, through the program that `locate` admits. -/
def walkDirectory (root : FilePath) (enter : FilePath → IO Bool := fun _ => pure true)
    (depth : Nat := 4096) : IO (Array FilePath) := do
  walkWith (← locate) enter depth root #[]

/-- The no-follow observer. Lean 4.35.0 follows links on Windows, so it refuses there.

Assumes: Lean v4.35.0 `Init/System/IO.lean:1151-1156` and `runtime/io.cpp:1160-1179`
call lstat on POSIX and report the final entry itself. No concurrent writer replaces a source
entry between this read and the later byte read; Lean exposes no O_NOFOLLOW file-open mode. -/
@[noinline] def observeMetadata (path : FilePath) : IO IO.FS.Metadata := do
  if System.Platform.isWindows then
    throw <| IO.userError "copy refused on Windows: Lean 4.35.0 symlinkMetadata follows links"
  path.symlinkMetadata

/-- Canonical-path observation, refused on Windows.

Assumes: Lean v4.35.0 `Init/System/IO.lean:873-879` and `runtime/io.cpp:1054-1066` realpath resolve
all present components on POSIX. Source and destination have no concurrent writer. -/
def observeRealPath (target : FilePath) : IO FilePath := do
  if System.Platform.isWindows then throw <| IO.userError "copy refused on Windows"
  IO.FS.realPath target

/-- Exclusive file creation at the exact destination, which never follows a final link.

Assumes: Lean v4.35.0 `Init/System/IO.lean:651-660`, `runtime/io.cpp:409` implement
Mode.writeNew with O_EXCL; `Init/System/IO.lean:1650` sets the new file's permissions.
No concurrent writer replaces a destination ancestor or the new file during construction. -/
def writeNew (target : FilePath) (bytes : ByteArray) (rights : UInt32 := 420) : IO Unit := do
  let handle ← IO.FS.Handle.mk target .writeNew
  handle.write bytes
  handle.flush
  IO.Prim.setAccessRights target (rights % 512)

/-- Exclusive mkdir followed by the fixed directory mode 0755. The destination is privately
owned throughout, with no concurrent writer replacing the new directory.

Assumes: Lean v4.35.0 `Init/System/IO.lean:900,1650` and `runtime/io.cpp:1181-1195`
implement exclusive mkdir and setting access rights. -/
def createDirectory (target : FilePath) : IO Unit := do
  IO.FS.createDir target
  IO.Prim.setAccessRights target 493

/-- The real operations. The modeled code and bootstrap source both use this value. -/
def observer : Ops IO where
  metadata := observeMetadata
  names := listNames
  realPath := observeRealPath
  bytes := fun path => return (← IO.FS.readBinFile path, 420)
  directory := createDirectory
  file := fun target bytes rights => writeNew target bytes rights

/-- `observer`, listing each directory through `enumerator`: the operations of one copy or capture
that locates its listing program once (`locate`) and lists every directory it reads through that
one program. -/
def Enumerator.observer (enumerator : Enumerator) : Ops IO :=
  { Construction.observer with names := enumerator.names }

/-- The shared copy routine, through the observer. It refuses links and special entries at
each selected source entry, and constructs no links. The destination parent exists at its own
place and the destination is absent or privately owned and empty. Source and destination have
no concurrent writer. Modes are not preserved: regular source files use 0644, directories use
0755; sites that execute a copied file explicitly set its required
rights. Lake-built programs receive their modes from Lake. The receipt is the ordered list of entries the routine constructed.
It locates its listing program once and lists each directory it reads, the destination among
them, through that program. -/
def copy (source target : FilePath) (selected : FilePath → Bool := fun _ => true) :
    IO (List Item) := do
  copyWith (← locate).observer source target selected

/-- Construct a generated workspace from directory/file instructions, with no source traversal.
The same destination preconditions as `copy` apply. -/
def construct (target : FilePath) (items : List Item) : IO Unit :=
  constructWith observer target items

/-- Add the directory instructions needed by a list of files and subtrees. Identical directory
instructions are coalesced before creation; files are never coalesced or overwritten, so a second
file at the same place is refused by exclusive creation. Case aliases remain distinct and collide
at the native exclusive creation boundary on a case-folding filesystem. -/
def layout (items : List Item) : List Item := Id.run do
  let mut result : List Item := []
  let mut directories : List (List String) := [[]]
  for item in items do
    let parents := match item.payload with
      | .directory => item.relative
      | .file .. => item.relative.dropLast
    for count in [1:parents.length + 1] do
      let ancestor := parents.take count
      unless directories.contains ancestor do
        directories := ancestor :: directories
        result := ⟨ancestor, .directory⟩ :: result
    match item.payload with
    | .directory => pure ()
    | .file .. => result := item :: result
  return result.reverse

/-- Capture one file or subtree through precisely the shared no-follow capture program. The
relative prefix is admitted by that program before it reads a selected source entry. The capture
of a directory locates its listing program once and lists each directory below it through that
program; the capture of any other entry lists no directory, so it locates none. -/
def capture (source : FilePath) (relative : List String := [])
    (selected : FilePath → Bool := fun _ => true) : IO (List Item) := do
  if (← kindWith observer source) == some .dir then
    captureWith (← locate).observer selected 4096 source relative
  else captureWith observer selected 4096 source relative

/-- The cold project's default source domain: no root tmp or Finder `.DS_Store` entry;
documentation includes cache-named subdirectories; elsewhere VCS, Lake, cache and scratch
components are excluded. Explicitly required files and their ancestors are selected separately. -/
def ProjectRelative (relative : List String) : Prop :=
  relative.getLast? ≠ some ".DS_Store" ∧
  relative.head? ≠ some "tmp" ∧ (relative.head? = some "docs" ∨
    ∀ component ∈ relative, component ≠ ".git" ∧ component ≠ ".lake" ∧
      component ≠ ".cache" ∧ component ≠ ".regula-scratch")

instance (relative : List String) : Decidable (ProjectRelative relative) :=
  inferInstanceAs (Decidable (relative.getLast? ≠ some ".DS_Store" ∧
    relative.head? ≠ some "tmp" ∧ (relative.head? = some "docs" ∨
    ∀ component ∈ relative, component ≠ ".git" ∧ component ≠ ".lake" ∧
      component ≠ ".cache" ∧ component ≠ ".regula-scratch")))

/-- Decide exactly the cold project's source domain. -/
def projectRelative (relative : List String) : Bool := decide (ProjectRelative relative)

/-- An explicit file selection includes every ancestor needed by no-follow capture. -/
def RequiredPath (required : List (List String)) (relative : List String) : Prop :=
  ∃ path ∈ required, relative.IsPrefix path

instance (required : List (List String)) (relative : List String) :
    Decidable (RequiredPath required relative) :=
  inferInstanceAs (Decidable (∃ path ∈ required, relative.IsPrefix path))

/-- Select exactly the named files and their ancestors, without selecting their siblings. -/
def requiredPath (required : List (List String)) (relative : List String) : Bool :=
  decide (RequiredPath required relative)

/-- Observe stored spellings for explicit relative file selections. Every requested ancestor
is admitted as a directory and each leaf as a regular file through no-follow metadata before
canonical observation. The result contains one stored path for each requested file, in request
order. The later shared capture still admits every selected source entry.

Assumes: the same stable source and POSIX metadata/realpath observations as `capture` and
`observeRealPath`. Stored spellings are observations, not consequences of the prefix proofs. -/
def requiredFiles (source : FilePath) (required : List (List String)) : IO (List (List String)) := do
  let mut stored := []
  for relative in required do
    unless !relative.isEmpty && decide (Relative relative) do
      throw <| IO.userError "explicit file selection is not a nonempty relative path"
    let mut path := source
    for name in relative do
      unless (← observeMetadata path).type == .dir do
        throw <| IO.userError s!"copy refused {path}: selected ancestor is not a directory"
      path := path / name
    unless (← observeMetadata path).type == .file do
      throw <| IO.userError s!"copy refused {path}: selected entry is not a regular file"
    let root ← observeRealPath source
    let actual ← observeRealPath path
    unless root.components.isPrefixOf actual.components do
      throw <| IO.userError "explicit file selection is outside its source root"
    stored := actual.components.drop root.components.length :: stored
  return stored.reverse

/-- The documentation consumer's original `.md` discovery domain, in path order. The same
discovery supplies the audit census and cold-copy requirements. It must precede construction.
The walk admits each directory through no-follow metadata before descent, so a directory link
cannot redirect or cycle discovery. `requiredFiles` admits the selected leaves. -/
def markdownPaths (root : FilePath) : IO (Array FilePath) := do
  unless ← isDirectory root do
    throw <| IO.userError s!"documentation root is not a directory: {root}"
  let enter (path : FilePath) : IO Bool := do
    unless (← observeMetadata path).type == .dir do
      throw <| IO.userError s!"copy refused {path}: selected ancestor is not a directory"
    return true
  return ((← walkDirectory root enter).filter (·.extension == some "md")).qsort
    (fun left right => left.toString < right.toString)

/-- Git's repository-local environment names, as the `git` found on this process's `PATH` prints
them. The query itself removes command-configuration injection and performs no repository setup
or repository configuration read. Each name is admitted as `GIT_` followed by ASCII letters,
digits and `_`, so no name is empty or holds `=` or NUL.

Assumes: Git 2.54.0 `builtin/rev-parse.c:757-762` prints `local_repo_env` before any repository
setup, which `git.c:647` does not request for `rev-parse`; `environment.c:109-126` and
`environment.h:7-85` define that list. Command configuration uses GIT_CONFIG_COUNT and
GIT_CONFIG_PARAMETERS (`config.c:711-779`), which are removed before this query. Removing
GIT_CONFIG_COUNT makes its KEY/VALUE variables inert (`config.c:721-758`). `config.c:1498-1512`
skips system config and both global files with the settings of the query. POSIX /dev/null supplies
an empty configuration (trusted OS device). -/
def gitLocalNames : IO (Array String) := do
  let out ← IO.Process.output {
    cmd := "git", args := #["-c", "core.symlinks=false", "rev-parse", "--local-env-vars"]
    env := #[("GIT_CONFIG_COUNT", none), ("GIT_CONFIG_PARAMETERS", none),
      ("GIT_CONFIG_NOSYSTEM", some "1"), ("GIT_CONFIG_GLOBAL", some "/dev/null")]
    stdin := .null }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"Git repository environment unavailable: {out.stderr}"
  let names := out.stdout.splitOn "\n" |>.filter (!·.isEmpty)
  unless !names.isEmpty && names.all (fun name => name.startsWith "GIT_" &&
      name != "GIT_CONFIG_NOSYSTEM" && name != "GIT_CONFIG_GLOBAL" &&
      name.toList.all (fun c => c.toNat < 128 && (c.isAlphanum || c == '_'))) do
    throw <| IO.userError "Git repository environment list is malformed"
  return names.toArray

/-- Remove Git's repository-local names for a child in another repository. System/global
configuration is disabled and namespaces are also removed. The final overrides must follow caller
environment changes.

Assumes: Git 2.54.0 `environment.c:151-187` reads GIT_NAMESPACE as a reference namespace;
`config.c:1498-1512` skips system config and both global files with these settings. Lean v4.35.0
`Init/System/IO.lean:1441-1448` applies env changes in order. -/
def repositoryEnvironment (names : Array String) : Array (String × Option String) :=
  names.map (fun name => (name, none)) ++ #[("GIT_NAMESPACE", none),
    ("GIT_CONFIG_NOSYSTEM", some "1"), ("GIT_CONFIG_GLOBAL", some "/dev/null")]

/-- The removals and settings of `repositoryEnvironment`, from Git's own list (`gitLocalNames`).
It is private to the Git commands of this module (`gitProcessArgs`) and to the Git commands of the
cold drivers that ask `sourceMain` for it (`git-environment`): Git's list names `GIT_CONFIG_COUNT`,
so the array removes the command-scope `core.symlinks=false` that `isolationEnvironment` gives a
process tree. Another child, such as Lake, takes `isolationEnvironment`, and so do the Git commands
of the verification driver (`RegulaVerification.start`). -/
private def gitEnvironment : IO (Array (String × Option String)) :=
  return repositoryEnvironment (← gitLocalNames)

/-- The settings of an isolated process tree: no namespace, no system or global configuration, and
command-scope `core.symlinks=false` carried by Git's environment-carried command configuration.

Assumes: Git 2.54.0 `config.c:711-779` reads GIT_CONFIG_COUNT and each GIT_CONFIG_KEY_n and
GIT_CONFIG_VALUE_n below it in command scope (`config.c:622-628`), and `config.c:1515-1581`
reads command scope after system, global, local and worktree configuration, so this value wins by
Git's own precedence; `environment.c:332-333` consumes core.symlinks. `run-command.c:1979-1994`
keeps GIT_CONFIG_COUNT for the children Git starts in another repository. Git 2.31.0 introduced
these variables and Git 2.32.0 GIT_CONFIG_GLOBAL. -/
def isolationSettings : Array (String × Option String) :=
  #[("GIT_NAMESPACE", none), ("GIT_CONFIG_NOSYSTEM", some "1"),
    ("GIT_CONFIG_GLOBAL", some "/dev/null"), ("GIT_CONFIG_COUNT", some "1"),
    ("GIT_CONFIG_KEY_0", some "core.symlinks"), ("GIT_CONFIG_VALUE_0", some "false")]

/-- The environment of a process tree whose Git commands run isolated, also those that another
program in the tree starts with no environment of its own, as Lake does: Git's repository-local
names removed and `isolationSettings` set, each name once. A Git name that a setting also names
takes the setting (`GIT_CONFIG_COUNT`), so applying the array twice changes nothing.

Assumes: Lake v4.35.0 `Lake/Util/Git.lean:91-109` starts each Git command through
`Lake/Util/Proc.lean:29-34,61-80` with no `env` and the default `inheritEnv := true`
(`Init/System/IO.lean:1434-1450`), so it receives its starter's environment unchanged. -/
def processEnvironment (names : Array String) : Array (String × Option String) :=
  (names.filter fun name => !isolationSettings.any (·.1 == name)).map (fun name => (name, none)) ++
    isolationSettings

/-- `processEnvironment` from Git's own list (`gitLocalNames`). -/
def isolationEnvironment : IO (Array (String × Option String)) :=
  return processEnvironment (← gitLocalNames)

/-- Apply the same Git policy to text and binary process observations. The command name and
launcher stay as the current repository uses them; process-start observation is separate work.

Assumes: Git 2.54.0 `config.c:1515-1581` reads command-scope settings after local/worktree settings;
`environment.c:332-333` consumes core.symlinks. Product callers supply no competing command-scope
core.symlinks setting. Repository-local variables are removed by `gitEnvironment`. -/
def gitProcessArgs (options : IO.Process.SpawnArgs) : IO IO.Process.SpawnArgs := do
  if options.cmd != "git" then return options
  return {options with
    args := #["-c", "core.symlinks=false"] ++ options.args,
    env := options.env ++ (← gitEnvironment)}

/-- Git output with its repository environment and command scope isolated. -/
def gitOutput (root : FilePath) (args : Array String) : IO IO.Process.Output := do
  IO.Process.output (← gitProcessArgs {cmd := "git", args, cwd := some root, stdin := .null})

/-- The cold drivers' source entrypoint. `project` prunes VCS/build/scratch directories and
Finder `.DS_Store` entries, except explicit relative file selections after TARGET, the original
Markdown discovery domain, and the ancestors needed to capture them. The instruction guard
refuses any missing selected file. It prints the regular-file receipt as a JSON array. `list`
prints the names of the directory SOURCE (`listNames`) and `walk` the paths below it
(`walkDirectory`), each as a JSON array; TARGET is unused there. `git-environment` prints the environment of a Regula-authored Git command
(`gitEnvironment`) and `process-environment` the Git isolation of a process tree
(`isolationEnvironment`), each as a JSON array of changes. Lean interprets this same source before
package artifacts exist; it does not use another copy implementation. -/
def sourceMain (args : List String) : IO UInt32 := do
  let domain :: source :: target :: required := args
    | throw <| IO.userError "construction requires DOMAIN SOURCE TARGET"
  unless domain == "project" || required.isEmpty do
    throw <| IO.userError "explicit file selections require the project domain"
  if domain == "git-environment" then
    IO.println (Lean.toJson (← gitEnvironment)).compress
    return 0
  if domain == "process-environment" then
    IO.println (Lean.toJson (← isolationEnvironment)).compress
    return 0
  if domain == "list" then
    IO.println (Lean.toJson (← listNames (FilePath.mk source))).compress
    return 0
  if domain == "walk" then
    IO.println (Lean.toJson ((← walkDirectory (FilePath.mk source)).map (·.toString))).compress
    return 0
  unless domain == "project" do
    throw <| IO.userError s!"unknown construction domain: {domain}"
  let source := FilePath.mk source
  let base := source.components.length
  let documents ← if ← isDirectory (source / "docs") then markdownPaths (source / "docs")
    else pure #[]
  let requested := required.map (FilePath.mk · |>.components) ++
    documents.toList.map (fun path => path.components.drop base)
  let stored ← requiredFiles source requested
  let required := requested ++ stored
  let selected := fun (path : FilePath) =>
    requiredPath required (path.components.drop base) || projectRelative (path.components.drop base)
  let items ← capture source [] selected
  -- Reserve the exact Lake state spelling by exclusive creation. A case-folded source spelling
  -- cannot silently carry old state into an ordinary load: its creation collides and fails.
  let generated := [⟨[".lake"], .directory⟩]
  constructSelectedWith observer target stored (layout (items ++ generated))
  let files := items.filterMap fun item => match item.payload with
    | .directory => none
    | .file .. => some ("/".intercalate item.relative)
  IO.println (Lean.toJson files).compress
  return 0

end Regula.Filesystem.Construction
