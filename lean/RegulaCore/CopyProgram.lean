import Lean

/-! # Construction of plain filesystem trees

One implementation for source copies and generated workspaces. It captures only directories and
regular files through no-follow metadata, then creates the selected entries. There is no inspection
of a finished copy, no link creator, and no recursive system copy. This module imports only the
toolchain so the cold verification and provisioning drivers can execute its source before the
package has artifacts. `RegulaCore.CopyConstruction` states its filesystem-model contract.
-/

namespace Regula.Filesystem.Construction

open System

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

/-- Capture the selected source entries, then construct them, using the same operations that
the filesystem-model theorem names. No destination is written while source entries are captured. -/
def copyWith {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (source target : FilePath) (selected : FilePath → Bool) (depth : Nat := 4096) :
    m (List Item) := do
  let items ← captureWith ops selected depth source []
  constructWith ops target items
  return items

/-- The no-follow observer. Lean 4.34.1 follows links on Windows, so it refuses there.

Assumes: Lean v4.34.1 `Init/System/IO.lean:1151-1156` and `runtime/io.cpp:1160-1179`
call lstat on POSIX and report the final entry itself. No concurrent writer replaces a source
entry between this read and the later byte read; Lean exposes no O_NOFOLLOW file-open mode. -/
@[noinline] def observeMetadata (path : FilePath) : IO IO.FS.Metadata := do
  if System.Platform.isWindows then
    throw <| IO.userError "copy refused on Windows: Lean 4.34.1 symlinkMetadata follows links"
  path.symlinkMetadata

/-- Canonical-path observation, refused on Windows.

Assumes: Lean v4.34.1 `Init/System/IO.lean:873-879` and `runtime/io.cpp:1054-1066` realpath resolve
all present components on POSIX. Source and destination have no concurrent writer. -/
def observeRealPath (target : FilePath) : IO FilePath := do
  if System.Platform.isWindows then throw <| IO.userError "copy refused on Windows"
  IO.FS.realPath target

/-- Exclusive file creation at the exact destination, which never follows a final link.

Assumes: Lean v4.34.1 `Init/System/IO.lean:651-660`, `runtime/io.cpp:409` implement
Mode.writeNew with O_EXCL; `Init/System/IO.lean:1650` sets the new file's permissions.
No concurrent writer replaces a destination ancestor or the new file during construction. -/
def writeNew (target : FilePath) (bytes : ByteArray) (rights : UInt32 := 420) : IO Unit := do
  let handle ← IO.FS.Handle.mk target .writeNew
  handle.write bytes
  handle.flush
  IO.Prim.setAccessRights target (rights % 512)

/-- Exclusive mkdir followed by the fixed directory mode 0755. The destination is privately
owned throughout, with no concurrent writer replacing the new directory.

Assumes: Lean v4.34.1 `Init/System/IO.lean:900,1650` and `runtime/io.cpp:1181-1195`
implement exclusive mkdir and setting access rights. -/
def createDirectory (target : FilePath) : IO Unit := do
  IO.FS.createDir target
  IO.Prim.setAccessRights target 493

/-- The real operations. The modeled code and bootstrap source both use this value. -/
def observer : Ops IO where
  metadata := observeMetadata
  names := fun path => return (← path.readDir).toList.map (·.fileName)
  realPath := observeRealPath
  bytes := fun path => return (← IO.FS.readBinFile path, 420)
  directory := createDirectory
  file := fun target bytes rights => writeNew target bytes rights

/-- The shared copy routine, through the observer. It refuses links and special entries at
each selected source entry, and constructs no links. The destination parent exists at its own
place and the destination is absent or privately owned and empty. Source and destination have
no concurrent writer. Modes are not preserved: regular source files use 0644, directories use
0755; sites that execute a copied file explicitly set its required
rights. Lake-built programs receive their modes from Lake. The receipt is the ordered list of entries the routine constructed. -/
def copy (source target : FilePath) (selected : FilePath → Bool := fun _ => true) :
    IO (List Item) := copyWith observer source target selected

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
relative prefix is admitted by that program before it reads a selected source entry. -/
def capture (source : FilePath) (relative : List String := [])
    (selected : FilePath → Bool := fun _ => true) : IO (List Item) :=
  captureWith observer selected 4096 source relative

/-- Admit an existing directory as a construction ancestor, or create it exclusively. This is
a primitive admission before writing, not a walk of a finished copy. Every ancestor is admitted
at its exact real path; links, aliases of the stored spelling and other entries are refused.
Source and destination have no concurrent writer. -/
def ensureDirectoryWith {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m]
    (ops : Ops m) : Nat → FilePath → m Unit
  | 0, path => throw <| IO.userError s!"construction ancestor depth exhausted: {path}"
  | depth + 1, path => do
    match ← kindWith ops path with
    | some .dir =>
      unless (← ops.realPath path) == path do
        throw <| IO.userError s!"construction ancestor is not at its own place: {path}"
    | none =>
      let some parent := path.parent
        | throw <| IO.userError s!"construction ancestor has no parent: {path}"
      ensureDirectoryWith ops depth parent
      ops.directory path
    | _ => throw <| IO.userError s!"construction ancestor is not a directory: {path}"

/-- Admit or create a destination ancestor through the shared observer. -/
def ensureDirectory (depth : Nat) (path : FilePath) : IO Unit :=
  ensureDirectoryWith observer depth path

/-- Append one generated or captured regular file through the common writer. An established
plain parent retains that tree and gains precisely this instruction (`appendFile_io`). -/
def appendFileWith {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (parent : FilePath) (name : String) (bytes : ByteArray) (rights : UInt32 := 420) : m Unit := do
  ensureDirectoryWith ops 4096 parent
  emitWith ops parent [⟨[name], .file bytes rights⟩]

/-- Append a captured file to a private workspace, through the same exclusive writer as tree
construction. Existing destination entries are refused, including dangling links and FIFOs.
Fixtures which intentionally mutate a generated file do so explicitly after this admission. -/
def copyFile (source target : FilePath) (rights : UInt32 := 420) : IO Unit := do
  let some parent := target.parent
    | throw <| IO.userError s!"construction file has no parent: {target}"
  let some name := target.fileName
    | throw <| IO.userError s!"construction file has no name: {target}"
  let items ← capture source [name]
  let [item] := items
    | throw <| IO.userError s!"construction file source is not one file: {source}"
  let .file bytes _ := item.payload
    | throw <| IO.userError s!"construction file source is a directory: {source}"
  appendFileWith observer parent name bytes rights

/-- The cold project's source domain: no root tmp; documentation includes cache-named
subdirectories; elsewhere VCS, Lake, cache and scratch components are excluded. -/
def ProjectRelative (relative : List String) : Prop :=
  relative.head? ≠ some "tmp" ∧ (relative.head? = some "docs" ∨
    ∀ component ∈ relative, component ≠ ".git" ∧ component ≠ ".lake" ∧
      component ≠ ".cache" ∧ component ≠ ".regula-scratch")

instance (relative : List String) : Decidable (ProjectRelative relative) :=
  inferInstanceAs (Decidable (relative.head? ≠ some "tmp" ∧ (relative.head? = some "docs" ∨
    ∀ component ∈ relative, component ≠ ".git" ∧ component ≠ ".lake" ∧
      component ≠ ".cache" ∧ component ≠ ".regula-scratch")))

/-- Decide exactly the cold project's source domain. -/
def projectRelative (relative : List String) : Bool := decide (ProjectRelative relative)

/-- The cold drivers' source entrypoint. `project` prunes VCS/build/scratch directories; `all`
copies every entry. It prints the regular-file receipt as a JSON array. Lean interprets this
same source before package artifacts exist; it does not use another copy implementation. -/
def sourceMain (args : List String) : IO UInt32 := do
  let [domain, source, target] := args
    | throw <| IO.userError "construction requires DOMAIN SOURCE TARGET"
  if domain == "generated" then
    let captured ← capture source ["instructions"]
    let [⟨_, .file bytes _⟩] := captured
      | throw <| IO.userError "generated instructions are not a regular file"
    let some text := String.fromUTF8? bytes
      | throw <| IO.userError "generated instructions are not UTF-8"
    let json ← IO.ofExcept (Lean.Json.parse text)
    let entries : Array Lean.Json ← IO.ofExcept (Lean.fromJson? json)
    let items ← entries.toList.foldlM (fun items entry => do
      let relative : List String ← IO.ofExcept (entry.getObjValAs? (List String) "relative")
      let extra ← match entry.getObjValAs? String "source" with
        | .ok source => capture source relative
        | .error _ => do
          let text ← IO.ofExcept (entry.getObjValAs? String "text")
          pure [⟨relative, .file text.toUTF8⟩]
      pure (items ++ extra)) []
    construct target (layout items)
    IO.println "[]"
    return 0
  unless domain == "all" || domain == "project" do
    throw <| IO.userError s!"unknown construction domain: {domain}"
  let source := FilePath.mk source
  let base := source.components.length
  let selected := fun (path : FilePath) => domain == "all" ||
    projectRelative (path.components.drop base)
  let items ← capture source [] selected
  -- Reserve the exact Lake state spelling by exclusive creation. A case-folded source spelling
  -- cannot silently carry old state into an ordinary load: its creation collides and fails.
  let generated := if domain == "project" then [⟨[".lake"], .directory⟩] else []
  construct target (layout (items ++ generated))
  let files := items.filterMap fun item => match item.payload with
    | .directory => none
    | .file .. => some ("/".intercalate item.relative)
  IO.println (Lean.toJson files).compress
  return 0

end Regula.Filesystem.Construction
