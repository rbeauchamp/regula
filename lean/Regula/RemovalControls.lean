import Regula.Removal
import Regula.Site.Deployment
import Lean.Elab.Command

/-! # Controls of the removal operations and of the reach check

Planted cases that the operations of `Regula.Filesystem` and the reach check of `Regula.Removal`
must refuse, each a control of one way a removal could escape the decision. The first acceptance
step builds this module, and its build fails when a control does not give the expected result. No
program imports this module, so no planted declaration below is linked into a program, and its
planted initializer never runs. The planted removals below are the calls of a removal primitive in
`lean/Regula` that do not go through the decision, each the subject of its control.

- A symbolic link at a component above the last one: `removeOwn` refuses `linked/out`, where
  `linked` is a link to a directory that has `out`, and removes nothing there. It removes the same
  directory at its own place. A symbolic link at its own place is removed as a link, and its target
  stays; the link is refused as a directory or a file. `replace` moves a file at its own place over
  another and refuses a move through the link, of a directory and onto a directory. These controls
  are about the file system, a trusted boundary: they observe the operations on the toolchain's
  file system calls, and they prove nothing.
- A name that extends the name of an observer of the filesystem: a declaration with that name that
  calls a removal primitive is a raw removal (`rawRemovalsFrom`), so only the declarations with the
  observer's role and the variants that the compiler made of them are admitted
  (`observerVariant`).
- A removal in an initializer: the check starts at each initializer that a program runs
  (`initializersOf`), so it finds a removal that no call from `main` reaches.
- A declaration of another name bound to a C function of the runtime that removes: a call of it is
  a raw removal (`removalSymbols`).
- A rename and the writing of a module, which replace an entry, and a write of a file: each call
  is raw (`primitives`, `writePrimitives`), and a caller that the check names admits its call.
- An opening of a file that writes: the check finds an opening to write, an opening in a mode that
  its caller gives, and the opening of `IO.FS.withFile` to append, and not an opening to read
  (`opensToWrite`). It finds the truncation of a file opened to read. A pair that the check names
  and that admits no call is reported (`Reach.unused`), so a named opening to read is.
- A declaration other than `IO.FS.Handle.mk` bound to its C function: a call of one is a write
  whatever its arguments (`readableOpening`). The check finds an inline binding that gives its own
  mode, called with the literal 0, and a standard binding of another name called to read.
- An absent output below a linked ancestor, and an output with a `.` or `..` component after the
  first: `ownPath` refuses each before anything is made. It drops the leading `.` of a relative
  path.
- A symbolic link, a path through one and a file where a directory is checked:
  `requireOwnDirectory` refuses each, and accepts a directory at its own place and an absent path.
  `requireNoLinkedEntries` refuses a directory with a symbolic link among its entries.
- A directory and a symbolic link moved aside: `moveAside` moves each into a new directory beside
  it, the link itself and not its target. It moves nothing at an absent path or a last component
  `..`, and stops with `ENAMETOOLONG` at the new directory, the entry in place, when that
  directory's name is longer than `NAME_MAX`.
- A URL of `Regula.Site.Deployment.fetch` that starts with `-`: curl does not read it as an
  option.

Assumes, for the control of `NAME_MAX`: POSIX.1-2024: `mkdir()` fails with `ENAMETOOLONG` when a
component of its path is longer than `NAME_MAX`
(https://pubs.opengroup.org/onlinepubs/9799919799/functions/mkdir.html), whatever the privileges
of the process, and `getconf NAME_MAX DIR` gives that limit for the file system of `DIR`
(https://pubs.opengroup.org/onlinepubs/9799919799/utilities/getconf.html). Lean 4.35.0 maps
`ENAMETOOLONG` to libuv's `UV_ENAMETOOLONG` and gives it as `IO.Error.invalidArgument` with the
path and libuv's message for that code (`src/runtime/io.cpp:195, 256-274`). libuv 1.52.1, which
Lean 4.35.0 links (`lib/libuv.a`), gives the message `name too long` for `UV_ENAMETOOLONG` and for
no other code (`UV_ERRNO_MAP` in `include/uv.h`,
https://github.com/libuv/libuv/blob/v1.52.1/include/uv.h).

`Regula.ProgramCheck.Controls` runs the check that each program runs (`checkProgram`) on a planted
program. -/

namespace Regula.RemovalControls

open Lean System

/-- The planted removal of the control of initializers. It removes a directory only when the
variable `REGULA_REMOVAL_CONTROL_PLANTED` is set, and no program runs it. -/
initialize plantedInitializer : Unit ← do
  if (← IO.getEnv "REGULA_REMOVAL_CONTROL_PLANTED").isSome then
    IO.FS.removeDirAll "/regula-removal-control-planted"

-- A symbolic link above the last component: refused, and nothing is removed through the link. A
-- link at its own place is removed as a link. A move of a file, and the moves it refuses.
run_cmd do
  let base ← Regula.Filesystem.ownTempDir
  try
    IO.FS.createDirAll (base / "target" / "out")
    IO.FS.writeFile (base / "target" / "out" / "keep") "keep"
    let linked ← IO.Process.output
      { cmd := "ln", args := #["-s", (base / "target").toString, (base / "linked").toString] }
    unless linked.exitCode == 0 do throwError "ln -s failed: {linked.stderr}"
    let refused ← (Regula.Filesystem.removeOwn .directory (base / "linked" / "out")).toBaseIO
    unless refused matches .error _ do throwError "removeOwn removed through a linked component"
    for kind in [Regula.Removal.Kind.directory, .file] do
      unless (← (Regula.Filesystem.removeOwn kind (base / "linked")).toBaseIO) matches .error _ do
        throwError "removeOwn removed a symbolic link as a {kind.noun}"
    unless (← (Regula.Filesystem.ownPath (base / "linked" / "new")).toBaseIO) matches .error _ do
      throwError "ownPath accepted an absent path below a linked component"
    unless (← Regula.Filesystem.ownPath (base / "target" / "new")) == base / "target" / "new" do
      throwError "ownPath changed a path below its own place"
    unless (← (Regula.Filesystem.ownPath (base / "fresh" / "." / "out")).toBaseIO)
        matches .error _ do
      throwError "ownPath accepted a path with a `.` component"
    unless (← (Regula.Filesystem.ownPath (base / "target" / ".." / "linked")).toBaseIO)
        matches .error _ do
      throwError "ownPath accepted a path with a `..` component"
    let working ← IO.FS.realPath (← IO.currentDir)
    unless (← Regula.Filesystem.ownPath (FilePath.mk "." / "lean")) == working / "lean" do
      throwError "ownPath kept the leading `.` of a relative path"
    for refused in [base / "linked", base / "linked" / "out", base / "target" / "out" / "keep"] do
      unless (← (Regula.Filesystem.requireOwnDirectory refused).toBaseIO) matches .error _ do
        throwError "requireOwnDirectory accepted {refused}"
    Regula.Filesystem.requireOwnDirectory (base / "target" / "out")
    Regula.Filesystem.requireNoLinkedEntries (base / "target" / "out")
    Regula.Filesystem.requireNoLinkedEntries (base / "absent")
    unless (← (Regula.Filesystem.requireNoLinkedEntries base).toBaseIO) matches .error _ do
      throwError "requireNoLinkedEntries accepted a directory with a linked entry"
    let dangling ← IO.Process.output { cmd := "ln", args := #["-s", (base / "missing").toString,
      (base / "target" / "out" / "dangling").toString] }
    unless dangling.exitCode == 0 do throwError "ln -s failed: {dangling.stderr}"
    unless (← (Regula.Filesystem.requireNoLinkedEntries (base / "target" / "out")).toBaseIO)
        matches .error _ do
      throwError "requireNoLinkedEntries accepted a directory with a dangling linked entry"
    Regula.Filesystem.requireOwnDirectory (base / "absent")
    unless ← Regula.Filesystem.isPresent (base / "target" / "out" / "keep") do
      throwError "removeOwn removed an entry below a linked component"
    -- Moves: a file over a file and to an absent path; none through the link, of a directory, or
    -- onto a directory.
    IO.FS.writeFile (base / "staged") "staged"
    IO.FS.writeFile (base / "published") "earlier"
    Regula.Filesystem.replace (base / "staged") (base / "published")
    unless (← IO.FS.readFile (base / "published")) == "staged" &&
        !(← Regula.Filesystem.isPresent (base / "staged")) do
      throwError "replace did not move a file over a file"
    Regula.Filesystem.replace (base / "published") (base / "moved")
    unless (← Regula.Filesystem.isPresent (base / "moved")) &&
        !(← Regula.Filesystem.isPresent (base / "published")) do
      throwError "replace did not move a file to an absent path"
    for (source, destination) in [(base / "moved", base / "linked" / "out" / "moved"),
        (base / "target" / "out", base / "directory"), (base / "moved", base / "target")] do
      unless (← (Regula.Filesystem.replace source destination).toBaseIO) matches .error _ do
        throwError "replace moved {source} to {destination}"
    unless ← Regula.Filesystem.isPresent (base / "moved") do
      throwError "a refused move changed its source"
    Regula.Filesystem.removeOwn .link (base / "linked")
    unless !(← Regula.Filesystem.isPresent (base / "linked")) &&
        (← Regula.Filesystem.isPresent (base / "target" / "out" / "keep")) do
      throwError "removeOwn did not remove a symbolic link at its own place, or removed its target"
    Regula.Filesystem.removeOwn .directory (base / "target" / "out")
    if ← Regula.Filesystem.isPresent (base / "target" / "out") then
      throwError "removeOwn kept a directory at its own place"
    -- Moves aside: a directory and a symbolic link, each into a new directory beside it; nothing
    -- for an absent entry, a last component `..` and an entry whose new directory's name is longer
    -- than the file system's limit.
    IO.FS.createDirAll (base / "pages")
    IO.FS.writeFile (base / "pages" / "index") "index"
    let some pages ← Regula.Filesystem.moveAside (base / "pages")
      | throwError "moveAside did not move a directory"
    unless (← Regula.Filesystem.isPresent (pages / "index")) &&
        !(← Regula.Filesystem.isPresent (base / "pages")) &&
        pages.fileName == some "pages" &&
        (pages.parent.bind (·.parent)) == some base &&
        ((pages.parent.bind (·.fileName)).map (·.startsWith "pages.regula-refused-")) ==
          some true do
      throwError "moveAside did not move a directory into a new directory beside it: {pages}"
    let aliased ← IO.Process.output
      { cmd := "ln", args := #["-s", (base / "target").toString, (base / "alias").toString] }
    unless aliased.exitCode == 0 do throwError "ln -s failed: {aliased.stderr}"
    let some alias ← Regula.Filesystem.moveAside (base / "alias")
      | throwError "moveAside did not move a symbolic link"
    unless (← alias.symlinkMetadata).type == .symlink &&
        (← Regula.Filesystem.isDirectory (base / "target")) &&
        !(← Regula.Filesystem.isPresent (base / "alias")) do
      throwError "moveAside did not move a symbolic link itself"
    if (← Regula.Filesystem.moveAside (base / "absent")).isSome then
      throwError "moveAside moved an absent entry"
    unless (← (Regula.Filesystem.moveAside (base / "target" / "..")).toBaseIO) matches .error _ do
      throwError "moveAside accepted a path whose last component is `..`"
    let limit ← IO.Process.output { cmd := "getconf", args := #["NAME_MAX", base.toString] }
    let some longest := (limit.stdout.splitOn "\n").head?.bind String.toNat?
      | throwError "getconf NAME_MAX {base} gave no number: {limit.stdout}{limit.stderr}"
    let long := base / String.ofList (List.replicate longest 'n')
    IO.FS.writeFile long "long"
    -- `mkdir` refuses the new directory beside `long`, whose name is longer than `NAME_MAX`.
    let made := s!"{long}.regula-refused-"
    match ← (Regula.Filesystem.moveAside long).toBaseIO with
    | .error (.invalidArgument (some file) _ "name too long") =>
      let suffix := file.toList.drop made.length
      unless file.startsWith made && suffix.length == 16 &&
          suffix.all ("0123456789abcdef".toList.contains ·) do
        throwError "moveAside stopped with ENAMETOOLONG at {file}, not at a new directory beside \
          the entry"
    | .error error =>
      throwError "moveAside on an entry whose new directory's name is longer than NAME_MAX did \
        not stop with ENAMETOOLONG at that directory: {error}"
    | .ok moved =>
      throwError "moveAside moved an entry whose new directory's name is longer than NAME_MAX: \
        {moved.map (·.toString)}"
    unless (← IO.FS.readFile long) == "long" do
      throwError "a failed move aside changed its entry"
  finally
    Regula.Filesystem.removeOwn .directory base

-- A declaration whose name extends the name of an observer of the filesystem is not admitted, and
-- the observers are the declarations of `Regula.Filesystem` that call the primitives.
run_cmd do
  let env ← getEnv
  let observers := Regula.Removal.filesystemObservers env
  unless observers.size ≥ 5 && observers.all fun observer =>
      (env.getModuleIdxFor? observer).map (env.header.moduleNames[·.toNat]!) ==
        some `Regula.Filesystem do
    throwError "the observers of the filesystem are not declarations of Regula.Filesystem: \
      {observers}"
  let some observer := observers.find? fun observer =>
      (Regula.Removal.rawRemovalsFrom env #[] #[observer]).raw.any (·.2 == ``IO.FS.removeDirAll)
    | throwError "no observer of the filesystem calls IO.FS.removeDirAll"
  unless (Regula.Removal.rawRemovalsFrom env observers #[observer]).raw.isEmpty do
    throwError "the observer {observer} is not admitted"
  let planted := observer ++ `_redArg
  Elab.Command.liftTermElabM do
    let type := mkForall `path .default (mkConst ``FilePath) (mkApp (mkConst ``IO) (mkConst ``Unit))
    let value := mkLambda `path .default (mkConst ``FilePath)
      (mkApp (mkConst ``IO.FS.removeDirAll) (mkBVar 0))
    addAndCompile (.defnDecl { name := planted, levelParams := [], type, value
                               hints := .opaque, safety := .safe })
  let reach := Regula.Removal.rawRemovalsFrom (← getEnv) observers #[planted]
  unless reach.raw == #[(planted, ``IO.FS.removeDirAll)] && reach.unknown.isEmpty do
    throwError "the planted declaration {planted} is not a raw removal: {reach.raw}, \
      unknown {reach.unknown}"

/-- The planted binding of the control of `extern` declarations: a declaration of another name
bound to the C function of `IO.FS.removeFile`. No program calls it. -/
@[extern "lean_io_remove_file"]
opaque plantedRemoval (path : @& FilePath) : IO Unit

/-- A caller of `plantedRemoval`, the root of its control. -/
def callsPlantedRemoval (path : FilePath) : IO Unit := plantedRemoval path

-- A call of a declaration bound to a removal symbol of the runtime is a raw removal, whatever the
-- declaration's name, and so is the declaration as a root.
run_cmd do
  let env ← getEnv
  let observers := Regula.Removal.filesystemObservers env
  let reach := Regula.Removal.rawRemovalsFrom env observers #[``callsPlantedRemoval]
  unless reach.raw == #[(``callsPlantedRemoval, ``plantedRemoval)] && reach.unknown.isEmpty do
    throwError "the call of the planted binding is not a raw removal: {reach.raw}, unknown \
      {reach.unknown}"
  let reach := Regula.Removal.rawRemovalsFrom env observers #[``plantedRemoval]
  unless reach.raw == #[(``plantedRemoval, `lean_io_remove_file)] do
    throwError "the planted binding is not a raw removal as a root: {reach.raw}"

/-- A caller of the library's operations that replace an entry, a rename and the writing of a
module, and of one that writes a file. No program calls it. -/
def callsReplacements (env : Environment) (source target : FilePath) : IO Unit := do
  IO.FS.rename source target
  Lean.writeModule env target
  IO.FS.writeFile target ""

-- A rename and the writing of a module are removals that the check finds, and the write of a file
-- is a write that it finds. Naming the caller of the write admits it, and only it.
run_cmd do
  let env ← getEnv
  let observers := Regula.Removal.filesystemObservers env
  let write := (``callsReplacements, ``IO.FS.writeFile)
  let reach := Regula.Removal.rawRemovalsFrom env observers #[``callsReplacements]
  let found := [``IO.FS.rename, ``Lean.writeModule, ``IO.FS.writeFile]
  unless reach.raw.size == 3 && found.all (fun primitive => reach.raw.contains
      (``callsReplacements, primitive)) && reach.unknown.isEmpty do
    throwError "the planted replacements and write are not raw: {reach.raw}, unknown \
      {reach.unknown}"
  let named := Regula.Removal.rawRemovalsFrom env observers #[``callsReplacements] [write]
  unless named.raw.size == 2 && !named.raw.contains write && named.unused.isEmpty do
    throwError "the planted write is not admitted by its named caller alone: {named.raw}, \
      unused {named.unused}"

/-- The planted opening of a file to write it. No program calls it. -/
def opensToWrite (path : FilePath) : IO Unit :=
  discard <| IO.FS.Handle.mk path .write

/-- The planted opening of a file in the mode that its caller gives. No program calls it. -/
def opensInGivenMode (path : FilePath) (mode : IO.FS.Mode) : IO Unit :=
  discard <| IO.FS.Handle.mk path mode

/-- The planted opening of a file by `IO.FS.withFile` to append to it. No program calls it. -/
def appendsWithFile (path : FilePath) : IO Unit :=
  IO.FS.withFile path .append fun handle => handle.putStr ""

/-- The planted opening of a file to read it. No program calls it. -/
def opensToRead (path : FilePath) : IO Unit :=
  discard <| IO.FS.Handle.mk path .read

/-- The planted truncation of a file opened to read. No program calls it. -/
def truncates (path : FilePath) : IO Unit := do
  let handle ← IO.FS.Handle.mk path .read
  handle.truncate

-- An opening of a file is a write unless its mode is the literal `IO.FS.Mode.read`: the openings
-- to write, in a given mode and by `IO.FS.withFile` to append are found, and naming each admits it.
-- The opening to read is not found, and a pair that names it is unused. The truncation is found.
run_cmd do
  let env ← getEnv
  let observers := Regula.Removal.filesystemObservers env
  let reachOf (root : Name) (named : List (Name × Name)) :=
    Regula.Removal.rawRemovalsFrom env observers #[root] named
  let sources (reach : Regula.Removal.Reach) :=
    reach.raw.map fun (caller, primitive) =>
      (Regula.Removal.sourceDeclaration env caller, primitive)
  for root in [``opensToWrite, ``opensInGivenMode, ``appendsWithFile] do
    let reach := reachOf root []
    unless sources reach == #[(root, ``IO.FS.Handle.mk)] && reach.unknown.isEmpty do
      throwError "the planted opening {root} is not found as a write: {reach.raw}, unknown \
        {reach.unknown}"
    let named := reachOf root [(root, ``IO.FS.Handle.mk)]
    unless named.raw.isEmpty && named.unused.isEmpty do
      throwError "the planted opening {root} is not admitted by its named caller: {named.raw}, \
        unused {named.unused}"
  let read := reachOf ``opensToRead []
  unless read.raw.isEmpty && read.unknown.isEmpty do
    throwError "the planted opening to read is found as a write: {read.raw}, unknown \
      {read.unknown}"
  let pair := (``opensToRead, ``IO.FS.Handle.mk)
  let unused := reachOf ``opensToRead [pair]
  unless unused.raw.isEmpty && unused.unused == #[pair] do
    throwError "a named opening to read is not reported unused: {unused.unused}"
  let truncated := reachOf ``truncates []
  unless sources truncated == #[(``truncates, ``IO.FS.Handle.truncate)] &&
      truncated.unknown.isEmpty do
    throwError "the planted truncation is not found as the only write: {truncated.raw}, unknown \
      {truncated.unknown}"

/-- The planted binding of the C function of `IO.FS.Handle.mk` with an inline pattern that opens the
file to write it, the mode 1, whatever its second argument. No program calls it. -/
@[extern c inline "lean_io_prim_handle_mk(#1, 1)"]
opaque plantedInlineOpen (path : @& FilePath) (tag : UInt8) : IO IO.FS.Handle

/-- The planted call of `plantedInlineOpen` with the literal 0, the mode of
`IO.FS.Mode.read`. No program calls it. -/
def opensInline (path : FilePath) : IO Unit :=
  discard <| plantedInlineOpen path 0

/-- The planted binding of the C function of `IO.FS.Handle.mk` under another name, with its
arguments. No program calls it. -/
@[extern "lean_io_prim_handle_mk"]
opaque plantedOpen (path : @& FilePath) (mode : IO.FS.Mode) : IO IO.FS.Handle

/-- The planted call of `plantedOpen` to read. No program calls it. -/
def opensThroughBinding (path : FilePath) : IO Unit :=
  discard <| plantedOpen path .read

-- A call of a declaration other than `IO.FS.Handle.mk` that is bound to its C function is a write
-- whatever its arguments: the inline binding called with the literal 0 and the standard binding of
-- another name called to read are each found, by the binding that the caller calls.
run_cmd do
  let env ← getEnv
  let observers := Regula.Removal.filesystemObservers env
  for (root, binding) in [(``opensInline, ``plantedInlineOpen),
      (``opensThroughBinding, ``plantedOpen)] do
    let reach := Regula.Removal.rawRemovalsFrom env observers #[root] []
    let sources := reach.raw.map fun (caller, primitive) =>
      (Regula.Removal.sourceDeclaration env caller, primitive)
    unless sources == #[(root, binding)] && reach.unknown.isEmpty do
      throwError "the planted opening {root} is not found as a write: {reach.raw}, unknown \
        {reach.unknown}"

-- The planted initializer is found, and no other initializer of this module's imports removes.
run_cmd do
  let env ← getEnv
  let reach := Regula.Removal.rawRemovalsFrom env (Regula.Removal.filesystemObservers env)
    (Regula.Removal.initializers env)
  unless reach.unknown.isEmpty do
    throwError "initializers with unknown compiled code: {reach.unknown}"
  unless reach.raw.size == 1 && reach.raw.all fun (caller, primitive) =>
      primitive == ``IO.FS.removeDirAll && (env.getModuleIdxFor? caller).isNone do
    throwError "the planted initializer is not the only raw removal: {reach.raw}"

-- `fetch` runs curl: it reads a planted file through a `file://` URL.
-- A URL that starts with `-` is not an option of curl: `fetch` gives `-K` with a configuration
-- that writes a file, and the file is not written. The configuration is effective: curl writes the
-- file when it is given as an option.
run_cmd do
  let base ← Regula.Filesystem.ownTempDir
  try
    IO.FS.writeFile (base / "body") "body"
    let (_, read) ← Regula.Site.Deployment.fetch s!"file://{base / "body"}"
    unless read == "body".toUTF8 do
      throwError "fetch did not run curl: it read {read.size} bytes of a planted file"
    IO.FS.writeFile (base / "config")
      s!"url = \"file://{base / "body"}\"\noutput = \"{base / "written"}\"\n"
    let _ ← Regula.Site.Deployment.fetch s!"-K{base / "config"}"
    if ← Regula.Filesystem.isPresent (base / "written") then
      throwError "fetch read a URL that starts with `-` as an option of curl"
    let direct ← IO.Process.output
      { cmd := "curl", args := #["--disable", "--silent", s!"-K{base / "config"}"] }
    unless direct.exitCode == 0 && (← Regula.Filesystem.isPresent (base / "written")) do
      throwError "the planted configuration of curl writes no file: {direct.stderr}"
  finally
    Regula.Filesystem.removeOwn .directory base

end Regula.RemovalControls
