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

/-- The entry kind of a construction instruction. -/
def Payload.kind : Payload → IO.FS.FileType
  | .directory => .dir
  | .file .. => .file

instance (payload : Payload) : Decidable (payload.kind = .file) := by
  cases payload with
  | directory => exact isFalse (by intro h; cases h)
  | file bytes rights => exact isTrue rfl

/-- Filter regular-file instructions only. Directory traversal and no-follow source admission
have already occurred, so a file-name exclusion cannot remove a directory's descendants. -/
def selectFiles (selected : List String → Bool) (items : List Item) : List Item :=
  items.filter fun item => match item.payload with
    | .directory => true
    | .file .. => selected item.relative

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
The existing walker admits each directory through no-follow metadata before descent, so a
directory link cannot redirect or cycle discovery. `requiredFiles` admits the selected leaves. -/
def markdownPaths (root : FilePath) : IO (Array FilePath) := do
  unless ← root.isDir do throw <| IO.userError s!"documentation root is not a directory: {root}"
  let enter (path : FilePath) : IO Bool := do
    unless (← observeMetadata path).type == .dir do
      throw <| IO.userError s!"copy refused {path}: selected ancestor is not a directory"
    return true
  return ((← root.walkDir enter).filter (·.extension == some "md")).qsort
    (fun left right => left.toString < right.toString)

/-- A package-store entry is source when the current capture root is itself in that store, or
when the entry lies in, or on the way to, one of the owned source paths `sources` that lie in that
store. -/
def PackageSource (source packages : List String) (sources : List (List String))
    (path : List String) : Prop :=
  ¬ packages.IsPrefix path ∨ packages.IsPrefix source ∨
    ∃ owned ∈ sources, packages.IsPrefix owned ∧ (owned.IsPrefix path ∨ path.IsPrefix owned)

instance (source packages : List String) (sources : List (List String)) (path : List String) :
    Decidable (PackageSource source packages sources path) :=
  inferInstanceAs (Decidable (¬ packages.IsPrefix path ∨ packages.IsPrefix source ∨
    ∃ owned ∈ sources, packages.IsPrefix owned ∧ (owned.IsPrefix path ∨ path.IsPrefix owned)))

/-- Prune a packages subtree only from a capture rooted outside that subtree, except for the owned
source paths in it and the directories on the way to them. -/
def packageSource (source packages : List String) (sources : List (List String))
    (path : List String) : Bool :=
  decide (PackageSource source packages sources path)

/-- Observe Git's repository-local environment names, then remove them for a child in another
repository. System/global configuration is disabled and namespaces are also removed. The query
itself removes command-configuration injection and performs no repository setup or repository
configuration read. The final overrides must follow caller environment changes.

Assumes: Git 2.54.0 `builtin/rev-parse.c:717-722,734-740` prints `local_repo_env` without
repository setup or the subsequent repository config read; `environment.c:99-118` and
`environment.h:73-78` define that list. Command configuration uses GIT_CONFIG_COUNT and
GIT_CONFIG_PARAMETERS (`config.c:667-720`), which are removed before this query. Removing
GIT_CONFIG_COUNT makes its KEY/VALUE variables inert (`config.c:676-707`). GIT_NAMESPACE selects
reference namespaces (`environment.c:141-175`). `config.c:1411-1427,1455-1468` skips system config
and both global files with these settings. POSIX /dev/null supplies an empty configuration
(trusted OS device). Lean v4.34.1 `Init/System/IO.lean:1441-1448` applies env changes in order. -/
def gitEnvironment : IO (Array (String × Option String)) := do
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
  return (names.map fun name => (name, none)).toArray ++ #[("GIT_NAMESPACE", none),
    ("GIT_CONFIG_NOSYSTEM", some "1"), ("GIT_CONFIG_GLOBAL", some "/dev/null")]

/-- Apply the same Git policy to text and binary process observations. The command name and
launcher stay as the current repository uses them; process-start observation is separate work.

Assumes: Git 2.54.0 `config.c:1470-1483` reads command-scope settings after local/worktree settings;
`environment.c:313-316` consumes core.symlinks. Product callers supply no competing command-scope
core.symlinks setting. Repository-local variables are removed by `gitEnvironment`. -/
def gitProcessArgs (options : IO.Process.SpawnArgs) : IO IO.Process.SpawnArgs := do
  if options.cmd != "git" then return options
  return {options with
    args := #["-c", "core.symlinks=false"] ++ options.args,
    env := options.env ++ (← gitEnvironment)}

/-- Git output with its repository environment and command scope isolated. -/
def gitOutput (root : FilePath) (args : Array String) : IO IO.Process.Output := do
  IO.Process.output (← gitProcessArgs {cmd := "git", args, cwd := some root, stdin := .null})

/-- Binary Git output through the same isolated process arguments as text observations.

Assumes: Lean v4.34.1 `Init/System/IO.lean:1002-1003,1544-1557` reads binary stdout, drains stderr
and waits for the process. Process and Git output fidelity are trusted. -/
def gitBinaryOutput (root : FilePath) (args : Array String) : IO (UInt32 × ByteArray × String) := do
  let options ← gitProcessArgs {cmd := "git", args, cwd := some root}
  let child ← IO.Process.spawn {options with stdin := .null, stdout := .piped, stderr := .piped}
  let stdout ← IO.asTask child.stdout.readBinToEnd Task.Priority.dedicated
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  let bytes ← IO.ofExcept stdout.get
  return (exitCode, bytes, stderr)

/-- Decode a single absolute path printed by Git without trimming its stored spelling. Path
names containing newline or carriage return are outside this line-oriented metadata protocol. -/
def gitPath (root : FilePath) (args : Array String) : IO FilePath := do
  let out ← gitOutput root args
  unless out.exitCode == 0 && out.stdout.endsWith "\n" do
    throw <| IO.userError s!"Git metadata path unavailable: {out.stderr}"
  let text := (out.stdout.dropEnd 1).toString
  unless !text.isEmpty && text.toList.all (fun c => c != '\n' && c != '\r' && c != '\x00') &&
      (FilePath.mk text).isAbsolute do
    throw <| IO.userError "Git metadata path is not one absolute path"
  return FilePath.mk text

/-- The closed configuration case has no extension, include or worktree-redirection setting.
Git decodes the captured file; Regula does not reproduce Git's precedence or include rules.
Even a disabled extension setting refuses, so the domain does not depend on its value grammar.

Assumes: Git 2.54.0 `builtin/config.c:74-104,487-591,1264-1266` and `config.c:1492-1523`
implement --file, --no-includes, --name-only and --get-regexp through Git's configuration decoder;
absent matches exit 1. Configuration and all
captured metadata have no concurrent writer. -/
def admitGitConfig (root config : FilePath) : IO Unit := do
  let out ← gitOutput root #["config", "--file", config.toString, "--no-includes", "--name-only",
    "--get-regexp", "^(extensions\\.|include\\.|includeif\\.|core\\.worktree$)"]
  if out.exitCode == 0 then
    throw <| IO.userError s!"copy Git configuration is outside the closed case: {out.stdout.trimAscii}"
  unless out.exitCode == 1 do
    throw <| IO.userError s!"copy Git configuration unavailable: {out.stderr}"

/-- Refuse alternate object stores at the path Git itself resolves. The supported qualification
and pinned dependency inputs have a self-contained effective object store. No alternate path is
parsed, copied or rewritten.

Assumes: Git 2.54.0 `builtin/rev-parse.c:752-759,776-785` delegates --git-path to the repository's
path resolver. `path.c:375-376` selects the effective object store; `setup.c:303-324` resolves
commondir. The routine refuses the alternates file without reading its entries. Git metadata has
no writer during this observation. -/
def admitGitObjects (root : FilePath) (gitOptions : Array String := #[]) : IO Unit := do
  let alternates ← gitPath root (gitOptions ++
    #["rev-parse", "--path-format=absolute", "--git-path", "objects/info/alternates"])
  unless (← kindWith observer alternates).isNone do
    throw <| IO.userError s!"copy Git alternates are outside the closed case: {alternates}"

/-- Admit exactly an index component present among the stored names, without case folding. -/
def admitGitName (pair : String × List String) : Except IO.Error Unit :=
  if pair.1 ∈ pair.2 then .ok () else
    .error (IO.userError s!"copy Git index spelling differs from stored entry: {pair.1}")

/-- Match each index path component to the observer's stored directory-entry name before
reading that entry or exempting a tracked link from general capture. Intermediate links refuse.
String equality compares the complete stored UTF-8 spelling; no core.ignoreCase interpretation
participates. Source ancestors and entries have no concurrent writer. -/
def admitGitPath (source : FilePath) (relative : List String) : IO Unit := do
  let mut parent := source
  for name in relative do
    unless (← observeMetadata parent).type == .dir do
      throw <| IO.userError s!"copy Git index ancestor is not a directory: {parent}"
    let names ← observer.names parent
    IO.ofExcept (admitGitName (name, names))
    parent := parent / name

/-- The supported Git index modes. A tracked link has a regular-file representation, never
a link instruction. Its bytes are obtained from the index's Git blob without following it. -/
inductive GitMode where
  /-- Index mode 100644. -/
  | regular
  /-- Index mode 100755. -/
  | executable
  /-- Index mode 120000, represented by its target-text blob. -/
  | link (text : ByteArray)

/-- One resolved index entry, with a relative path and a supported typed mode. -/
structure GitEntry where
  /-- The index's path components. -/
  relative : List String
  /-- The index's regular, executable or target-text mode. -/
  mode : GitMode

/-- Derive one regular-file instruction from an index entry. Ordinary file bytes come from
the no-follow source receipt. A tracked link uses the index blob, not a filesystem target. -/
def gitItem (captured : List Item) (entry : GitEntry) : Except IO.Error Item := do
  match entry.mode with
  | .link text => return ⟨entry.relative, .file text⟩
  | mode =>
    let some item := captured.find? (fun item => item.relative == entry.relative)
      | throw <| IO.userError s!"Git index file is absent from source: {entry.relative}"
    let .file bytes _ := item.payload
      | throw <| IO.userError s!"Git index file is not regular: {entry.relative}"
    let rights := match mode with | .executable => 493 | _ => 420
    return ⟨entry.relative, .file bytes rights⟩

/-- Derive every indexed file instruction, preserving the complete index order. -/
def gitFiles (captured : List Item) : List GitEntry → Except IO.Error (List Item)
  | [] => return []
  | entry :: rest => do
    let item ← gitItem captured entry
    return item :: (← gitFiles captured rest)

/-- Retain captured regular build outputs of this package only. Indexed paths are supplied by
`gitFiles`, so they are not emitted twice. All other untracked files remain excluded. -/
def gitBuildFiles (captured : List Item) (entries : List GitEntry) : List Item :=
  captured.filter fun item => match item.payload with
    | .directory => false
    | .file .. => [".lake", "build"].isPrefixOf item.relative &&
        !entries.any (fun entry => entry.relative == item.relative)

/-- A final local core section selects Git's target-text representation for every tracked link.
Two leading newlines also terminate a trailing config continuation before the new section. -/
def gitConfigBytes (bytes : ByteArray) : ByteArray :=
  bytes ++ "\n\n[core]\n\tsymlinks = false\n".toUTF8

/-- Generate the clone metadata, changing only its regular .git/config instruction. -/
def gitMetadata (metadata : List Item) : List Item := metadata.map fun item =>
  if item.relative == [".git", "config"] then match item.payload with
    | .file bytes rights => {item with payload := .file (gitConfigBytes bytes) rights}
    | .directory => item
  else item

/-- The clone account is the captured Git metadata, indexed worktree and untracked regular
files beneath this package's own `.lake/build`. General no-follow capture admits those build
outputs before this selection. Other untracked files are not emitted; untracked links and
special entries refuse before this function runs. A missing regular Git configuration refuses
rather than omit the target-text setting. -/
def prepareGit (metadata captured : List Item) (entries : List GitEntry) :
    Except IO.Error (List Item) := do
  let some config := metadata.find? (fun item => item.relative == [".git", "config"])
    | throw <| IO.userError "Git source has no configuration"
  let .file .. := config.payload
    | throw <| IO.userError "Git source configuration is not regular"
  let files ← gitFiles captured entries
  return layout (gitMetadata metadata ++ files ++ gitBuildFiles captured entries)

/-- The Git adapter's executed writer, over the same operations as all other copies.
It derives its complete index/build account before creating any destination entry, then uses only
the shared constructor. `gitConstruct_io` states its exact plain-tree contract. -/
def gitConstructWith {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (target : FilePath) (metadata captured : List Item) (entries : List GitEntry) : m (List Item) := do
  match prepareGit metadata captured entries with
  | .error error => throw error
  | .ok items =>
    constructWith ops target items
    return items

/-- Read an index blob as bytes. The command identifies an object, not a filesystem link path.
Neither filters nor textconv nor follow-symlinks is requested.

Assumes: installed Git 2.54.0 git-cat-file(1), SYNOPSIS and DESCRIPTION, returns the exact blob
contents for `cat-file blob OBJECT`. Lean v4.34.1 `Init/System/IO.lean:1002-1003,1544-1557`
reads binary stdout, drains stderr and waits for the process. Process execution and Git object
fidelity are trusted. Git 2.54.0 git(1), --no-lazy-fetch, --no-optional-locks and
--no-replace-objects, prevents lazy fetching, optional lock-taking writes and replacement
object lookup. Source Git metadata has no writer during this observation. -/
def readGitBlob (source : FilePath) (object : String) : IO ByteArray := do
  unless !object.isEmpty && object.toList.all Char.isHexDigit do
    throw <| IO.userError "Git index object is not a hexadecimal identifier"
  let (exitCode, bytes, stderr) ← gitBinaryOutput source
    #["--no-lazy-fetch", "--no-optional-locks", "--no-replace-objects", "cat-file", "blob", object]
  unless exitCode == 0 do throw <| IO.userError s!"Git index blob read failed: {stderr}"
  return bytes

/-- Observe a complete supported index after no-follow admission of its Git metadata.
Tracked links are represented by Git's own blobs. Every other source entry is admitted through
the general capture, so an untracked link or special entry is still refused before construction.
Indexed files, captured Git metadata and admitted untracked regular `.lake/build` files are emitted.
After Git confirms that the common directory is the source's own .git, its captured commondir
instruction is omitted using the observer's stored name, including case-folded spellings.

Assumes: installed Git 2.54.0 git-ls-files(1), --format, -z and FIELD NAMES, reports the complete
index with unquoted paths, object identifiers and modes. The source has no index or worktree
writer. git-cat-file(1) supplies index link blobs without following a source link. git-config(1),
core.symlinks, specifies target-text regular files when false and retained index link types.
The source .git is a plain, self-contained metadata directory, with no extension, include or
worktree-redirection settings and no alternates. Each index path equals the stored names byte
for byte. Git environment/config observations use `gitProcessArgs`, `admitGitConfig` and
`admitGitObjects`; their Assumes entries name the trusted sources. Git status remains trusted.
Lean/Lake v4.34.1
`Lake/Util/Git.lean:198-203` tests cleanliness with `git diff --exit-code HEAD`;
`Lake/Load/Materialize.lean:255-258` warns if a matching-revision checkout has that diff. -/
def copyGit (source target : FilePath) : IO (List Item) := do
  let metadata ← capture (source / ".git") [".git"]
  let ⟨_, .directory⟩ :: _ := metadata
    | throw <| IO.userError "Git source metadata is not a plain directory"
  admitGitConfig source (source / ".git/config")
  let common ← gitPath source #["rev-parse", "--path-format=absolute", "--git-common-dir"]
  unless common == (← observeRealPath (source / ".git")) do
    throw <| IO.userError "copy Git metadata has an external common directory"
  -- Equality establishes that no common-directory instruction is needed in the clone. Observe
  -- its stored name so the same omission covers a case-folded spelling without interpreting it.
  let metadata ← if (← kindWith observer (source / ".git/commondir")).isSome then do
      let some name := (← observeRealPath (source / ".git/commondir")).fileName
        | throw <| IO.userError "copy Git common instruction has no stored name"
      pure (metadata.filter fun item => ![".git", name].isPrefixOf item.relative)
    else pure metadata
  admitGitObjects source
  let (exitCode, indexBytes, stderr) ← gitBinaryOutput source
    #["--no-lazy-fetch", "--no-optional-locks", "--no-replace-objects", "ls-files", "-z",
      "--format=%(objectmode)%x09%(stage)%x09%(objectname)%x09%(path)"]
  unless exitCode == 0 do throw <| IO.userError s!"copy Git index failed: {stderr}"
  let some index := String.fromUTF8? indexBytes
    | throw <| IO.userError "copy Git index names are outside the UTF-8 closed case"
  unless index.isEmpty || index.endsWith "\x00" do
    throw <| IO.userError "copy Git index output is not NUL-terminated"
  let mut entries : List GitEntry := []
  for record in index.splitOn "\x00" do
    if record.isEmpty then continue
    let mode :: stage :: object :: pathParts := record.splitOn "\t"
      | throw <| IO.userError "copy Git index record is malformed"
    unless stage == "0" do throw <| IO.userError "copy Git index has unresolved entries"
    let relative := ("\t".intercalate pathParts).splitOn "/"
    unless Relative relative && relative.head? != some ".git" do
      throw <| IO.userError "copy Git index path is not a worktree-relative path"
    admitGitPath source relative
    let mode ← match mode with
      | "100644" => pure GitMode.regular
      | "100755" => pure GitMode.executable
      | "120000" =>
        let kind := (← observeMetadata (location source relative)).type
        unless kind == .symlink || kind == .file do
          throw <| IO.userError "tracked Git link source is neither a link nor its regular representation"
        pure <| GitMode.link (← readGitBlob source object)
      | _ => throw <| IO.userError s!"copy Git index mode is unsupported: {mode}"
    entries := entries ++ [⟨relative, mode⟩]
  let base := source.components.length
  let selected := fun (path : FilePath) =>
    let relative := path.components.drop base
    relative.head? != some ".git" && !entries.any (fun entry =>
      entry.relative == relative && match entry.mode with | .link _ => true | _ => false)
  let captured ← capture source [] selected
  gitConstructWith observer target metadata captured entries

/-- The cold drivers' source entrypoint. `project` prunes VCS/build/scratch directories, except
explicit relative file selections after TARGET, the original Markdown discovery domain, and
the ancestors needed to capture them. The instruction guard refuses any missing selected file.
`git` uses `copyGit`'s regular-file representation, build outputs and metadata.
It prints the regular-file receipt as a JSON array. Lean interprets this
same source before package artifacts exist; it does not use another copy implementation.

Assumes: `copyGit` names the installed Git 2.54.0 index/blob/config facts, its source stability
and the pinned Lake cleanliness observation. Git parsing and object fidelity remain trusted. -/
def sourceMain (args : List String) : IO UInt32 := do
  let domain :: source :: target :: required := args
    | throw <| IO.userError "construction requires DOMAIN SOURCE TARGET"
  unless domain == "project" || required.isEmpty do
    throw <| IO.userError "explicit file selections require the project domain"
  if domain == "git-environment" then
    IO.println (Lean.toJson (← gitEnvironment)).compress
    return 0
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
  if domain == "git" then
    let items ← copyGit source target
    let files := items.filterMap fun item => match item.payload with
      | .directory => none
      | .file .. => some ("/".intercalate item.relative)
    IO.println (Lean.toJson files).compress
    return 0
  unless domain == "project" do
    throw <| IO.userError s!"unknown construction domain: {domain}"
  let source := FilePath.mk source
  let base := source.components.length
  let documents ← if ← (source / "docs").isDir then markdownPaths (source / "docs") else pure #[]
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
