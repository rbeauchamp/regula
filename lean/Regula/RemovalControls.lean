import Regula.Removal
import Regula.Process
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
- A rename and the writing of a module, which replace an entry: each call is a raw removal
  (`primitives`). A write of a file is not a removal, and the check does not refuse it.
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
(https://pubs.opengroup.org/onlinepubs/9799919799/utilities/getconf.html). Lean 4.34.1 maps
`ENAMETOOLONG` to libuv's `UV_ENAMETOOLONG` and gives it as `IO.Error.invalidArgument` with the
path and libuv's message for that code (`src/runtime/io.cpp:195, 256-274`). libuv 1.52.1, which
Lean 4.34.1 links (`lib/libuv.a`), gives the message `name too long` for `UV_ENAMETOOLONG` and for
no other code (`UV_ERRNO_MAP` in `include/uv.h`,
https://github.com/libuv/libuv/blob/v1.52.1/include/uv.h).

`Regula.ProgramCheck.Controls` runs the check that each program runs (`checkProgram`) on a planted
program. -/

namespace Regula.RemovalControls

open Lean System

/-- The planted removal of the control of initializers. It removes a directory only when the
variable `REGULA_REMOVAL_CONTROL_PLANTED` is set, and no program runs it. -/
initialize plantedInitializer : Unit ← do
  if (← Regula.Process.readEnv "REGULA_REMOVAL_CONTROL_PLANTED").isSome then
    IO.FS.removeDirAll "/regula-removal-control-planted"

-- A symbolic link above the last component: refused, and nothing is removed through the link. A
-- link at its own place is removed as a link. A move of a file, and the moves it refuses.
run_cmd do
  let base ← Regula.Filesystem.ownTempDir
  try
    IO.FS.createDirAll (base / "target" / "out")
    IO.FS.writeFile (base / "target" / "out" / "keep") "keep"
    let linked ← Regula.Process.output (.stated "ln" "Plant a symbolic-link filesystem control")
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
    let working ← IO.FS.realPath (← Regula.Process.currentDir)
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
    let dangling ← Regula.Process.output (.stated "ln" "Plant a dangling-link filesystem control")
      { cmd := "", args := #["-s", (base / "missing").toString,
      (base / "target" / "out" / "dangling").toString] }
    unless dangling.exitCode == 0 do throwError "ln -s failed: {dangling.stderr}"
    unless (← (Regula.Filesystem.requireNoLinkedEntries (base / "target" / "out")).toBaseIO)
        matches .error _ do
      throwError "requireNoLinkedEntries accepted a directory with a dangling linked entry"
    Regula.Filesystem.requireOwnDirectory (base / "absent")
    unless ← (base / "target" / "out" / "keep").pathExists do
      throwError "removeOwn removed an entry below a linked component"
    -- Moves: a file over a file and to an absent path; none through the link, of a directory, or
    -- onto a directory.
    IO.FS.writeFile (base / "staged") "staged"
    IO.FS.writeFile (base / "published") "earlier"
    Regula.Filesystem.replace (base / "staged") (base / "published")
    unless (← IO.FS.readFile (base / "published")) == "staged" &&
        !(← (base / "staged").pathExists) do
      throwError "replace did not move a file over a file"
    Regula.Filesystem.replace (base / "published") (base / "moved")
    unless (← (base / "moved").pathExists) && !(← (base / "published").pathExists) do
      throwError "replace did not move a file to an absent path"
    for (source, destination) in [(base / "moved", base / "linked" / "out" / "moved"),
        (base / "target" / "out", base / "directory"), (base / "moved", base / "target")] do
      unless (← (Regula.Filesystem.replace source destination).toBaseIO) matches .error _ do
        throwError "replace moved {source} to {destination}"
    unless ← (base / "moved").pathExists do
      throwError "a refused move changed its source"
    Regula.Filesystem.removeOwn .link (base / "linked")
    unless !(← (base / "linked").pathExists) && (← (base / "target" / "out" / "keep").pathExists) do
      throwError "removeOwn did not remove a symbolic link at its own place, or removed its target"
    Regula.Filesystem.removeOwn .directory (base / "target" / "out")
    if ← (base / "target" / "out").pathExists then
      throwError "removeOwn kept a directory at its own place"
    -- Moves aside: a directory and a symbolic link, each into a new directory beside it; nothing
    -- for an absent entry, a last component `..` and an entry whose new directory's name is longer
    -- than the file system's limit.
    IO.FS.createDirAll (base / "pages")
    IO.FS.writeFile (base / "pages" / "index") "index"
    let some pages ← Regula.Filesystem.moveAside (base / "pages")
      | throwError "moveAside did not move a directory"
    unless (← (pages / "index").pathExists) && !(← (base / "pages").pathExists) &&
        pages.fileName == some "pages" &&
        (pages.parent.bind (·.parent)) == some base &&
        ((pages.parent.bind (·.fileName)).map (·.startsWith "pages.regula-refused-")) ==
          some true do
      throwError "moveAside did not move a directory into a new directory beside it: {pages}"
    let aliased ← Regula.Process.output (.stated "ln" "Plant a symbolic link for the move-aside control")
      { cmd := "", args := #["-s", (base / "target").toString, (base / "alias").toString] }
    unless aliased.exitCode == 0 do throwError "ln -s failed: {aliased.stderr}"
    let some alias ← Regula.Filesystem.moveAside (base / "alias")
      | throwError "moveAside did not move a symbolic link"
    unless (← alias.symlinkMetadata).type == .symlink &&
        (← (base / "target").isDir) && !(← (base / "alias").pathExists) do
      throwError "moveAside did not move a symbolic link itself"
    if (← Regula.Filesystem.moveAside (base / "absent")).isSome then
      throwError "moveAside moved an absent entry"
    unless (← (Regula.Filesystem.moveAside (base / "target" / "..")).toBaseIO) matches .error _ do
      throwError "moveAside accepted a path whose last component is `..`"
    let limit ← Regula.Process.output
      (.stated "getconf" "POSIX getconf gives the file system's NAME_MAX for the control")
      { cmd := "", args := #["NAME_MAX", base.toString] }
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

-- A rename and the writing of a module are removals that the check finds; the write is not.
run_cmd do
  let env ← getEnv
  let reach := Regula.Removal.rawRemovalsFrom env (Regula.Removal.filesystemObservers env)
    #[``callsReplacements]
  let replacements := [``IO.FS.rename, ``Lean.writeModule]
  unless reach.raw.size == 2 && replacements.all (fun replacement => reach.raw.contains
      (``callsReplacements, replacement)) && reach.unknown.isEmpty do
    throwError "the planted replacements are not raw removals: {reach.raw}, unknown \
      {reach.unknown}"

-- The planted initializer is found, and no other initializer of this module's imports removes.
run_cmd do
  let env ← getEnv
  let (startup, roots) := Regula.Removal.splitInitializers env (Regula.Removal.initializers env)
  let reach := Regula.Removal.rawRemovalsFrom env (Regula.Removal.filesystemObservers env) roots
    (startup := startup)
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
    if ← (base / "written").pathExists then
      throwError "fetch read a URL that starts with `-` as an option of curl"
    let direct ← Regula.Process.output (.stated "curl" "The negative control proves this curl configuration really writes a file")
      { cmd := "curl", args := #["--disable", "--silent", s!"-K{base / "config"}"] }
    unless direct.exitCode == 0 && (← (base / "written").pathExists) do
      throwError "the planted configuration of curl writes no file: {direct.stderr}"
  finally
    Regula.Filesystem.removeOwn .directory base

end Regula.RemovalControls
