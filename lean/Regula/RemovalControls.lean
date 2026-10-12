import Regula.Removal
import Regula.Checker.Workspace
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
  (`primitives`). A write of a file is counted, not refused (`writePrimitives`).
- An absent output below a linked ancestor, and an output with a `.` or `..` component after the
  first: `ownPath` refuses each before anything is made. It drops the leading `.` of a relative
  path.
- A symbolic link where Lake removes or replaces entries, loaded through the loaders of
  `Regula.Checker.Workspace`: at `.lake/config/1`, the compiled configuration of a dependency; at
  `.lake/build/lib`; below the packages directory of a workspace without a manifest, at the clone
  of a dependency named `foo/sub`, and at `other/sub`, which only a dependency of a dependency
  could name; and at a clone that Lake would update. Each load stops before Lake runs, and the
  link's target keeps its content. A load also stops at a build directory with a `..` component
  after another one. A workspace without them loads, also with its packages directory beside it
  (`../plain-packages`), and so does one whose clone is a link at the manifest's revision, which
  Lake leaves as it is.
- A URL of `Regula.Site.Deployment.fetch` that starts with `-`: curl does not read it as an
  option.

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

/-- The manifest of the control of a clone that Lake would update: one Git entry, `dep`, at a
revision that no clone has. -/
def lockedManifest (name : String) : String :=
  "{\"version\": \"1.2.0\", \"packagesDir\": \".lake/packages\", \"packages\": [{\"url\": \
    \"https://example.invalid/dep.git\", \"type\": \"git\", \"subDir\": null, \"scope\": \"\", \
    \"rev\": \"0000000000000000000000000000000000000000\", \"name\": \"dep\", \"manifestFile\": \
    \"lake-manifest.json\", \"inputRev\": null, \"inherited\": false, \"configFile\": \
    \"lakefile.toml\"}], \"name\": \"" ++ name ++ "\", \"lakeDir\": \".lake\", \
    \"fixedToolchain\": false}"

-- The places where Lake removes or replaces entries (`Regula.Checker.Workspace`): a symbolic link
-- at `.lake/config/1`, at `.lake/build/lib`, below the packages directory of a workspace without
-- a manifest, at a place that the root's dependency names and at one that only a dependency of a
-- dependency could name, and at a clone that Lake would update makes the loaders stop before Lake
-- runs, and the link's target keeps its content; a load also stops at a build directory with a `..`
-- component after another one. A workspace with none of them loads, also with its packages
-- directory beside it, and so does one whose clone is a link at the manifest's revision, which Lake
-- leaves as it is.
run_cmd do
  let base ← Regula.Filesystem.ownTempDir
  try
    let target := base / "target"
    IO.FS.createDirAll target
    IO.FS.writeFile (target / "keep") "keep"
    let link (to place : FilePath) : IO Unit := do
      if let some parent := place.parent then IO.FS.createDirAll parent
      let made ← IO.Process.output { cmd := "ln", args := #["-s", to.toString, place.toString] }
      unless made.exitCode == 0 do throw <| IO.userError s!"ln -s failed: {made.stderr}"
    let workspace (name : String) (rest : String := "") : IO FilePath := do
      IO.FS.createDirAll (base / name)
      IO.FS.writeFile (base / name / "lakefile.toml") s!"name = \"{name}\"\n{rest}"
      return base / name
    let refused (label : String) (load : IO Unit) (reason := "is a symbolic link") :
        Elab.Command.CommandElabM Unit := do
      match ← load.toBaseIO with
      | .ok () => throwError "the loader ran Lake with {label}"
      | .error error =>
        unless (toString error).contains reason do
          throwError "the loader stopped with {label} for another reason: {error}"
    let plain ← workspace "plain" "packagesDir = \"../plain-packages\"\n"
    for directory in [".lake/config/0", ".lake/build/lib", ".lake/packages"] do
      IO.FS.createDirAll (plain / directory)
    unless ← Regula.Checker.Workspace.withRootWorkspace plain fun _ => pure true do
      throwError "the loader did not run the action on a workspace without links"
    let config ← workspace "config"
    link target (config / ".lake" / "config" / "1")
    refused "a link at .lake/config/1"
      (Regula.Checker.Workspace.withRootPackage config fun _ => pure ())
    let build ← workspace "build"
    link target (build / ".lake" / "build" / "lib")
    refused "a link at .lake/build/lib"
      (Regula.Checker.Workspace.withRootPackage build fun _ => pure ())
    let escape ← workspace "escape" "buildDir = \"out/../../escape-build\"\n"
    refused "a build directory that a `..` after another component names"
      (Regula.Checker.Workspace.withRootPackage escape fun _ => pure ()) "is not below"
    let update ← workspace "update"
      "[[require]]\nname = \"foo/sub\"\ngit = \"https://example.invalid/sub.git\"\n"
    link target (update / ".lake" / "packages" / "foo" / "sub")
    refused "a link below the packages directory of a workspace without a manifest"
      (Regula.Checker.Workspace.withRootWorkspace update fun _ => pure ())
    let transitive ← workspace "transitive"
      "[[require]]\nname = \"dep\"\ngit = \"https://example.invalid/dep.git\"\n"
    link target (transitive / ".lake" / "packages" / "other" / "sub")
    refused "a link below the packages directory that only a dependency's dependency names"
      (Regula.Checker.Workspace.withRootWorkspace transitive fun _ => pure ())
    let locked ← workspace "locked"
      "[[require]]\nname = \"dep\"\ngit = \"https://example.invalid/dep.git\"\n"
    IO.FS.writeFile (locked / "lake-manifest.json") (lockedManifest "locked")
    link target (locked / ".lake" / "packages" / "dep")
    refused "a link at a clone that Lake would update"
      (Regula.Checker.Workspace.withRootWorkspace locked fun _ => pure ())
    unless (← target.readDir).map (·.fileName) == #["keep"] &&
        (← IO.FS.readFile (target / "keep")) == "keep" do
      throwError "a refused load changed the target of a link"
    -- A clone that is a link at the manifest's revision: Lake leaves it as it is.
    let clone := base / "clone"
    IO.FS.createDirAll clone
    IO.FS.writeFile (clone / "lakefile.toml") "name = \"dep\"\n"
    let git (args : Array String) : IO String := do
      let out ← IO.Process.output { cmd := "git", args := #["-C", clone.toString] ++ args }
      unless out.exitCode == 0 do throw <| IO.userError s!"git {args} failed: {out.stderr}"
      return out.stdout.trimAscii.toString
    let _ ← git #["init", "--quiet"]
    let _ ← git #["-c", "user.name=control", "-c", "user.email=control@example.invalid",
      "commit", "--quiet", "--allow-empty", "-m", "control"]
    let revision ← git #["rev-parse", "HEAD"]
    let atRevision ← workspace "revision"
      "[[require]]\nname = \"dep\"\ngit = \"https://example.invalid/dep.git\"\n"
    IO.FS.writeFile (atRevision / "lake-manifest.json")
      ((lockedManifest "revision").replace "0000000000000000000000000000000000000000" revision)
    link clone (atRevision / ".lake" / "packages" / "dep")
    unless ← Regula.Checker.Workspace.withRootWorkspace atRevision fun ws =>
        pure (ws.packages.size == 2) do
      throwError "the loader did not load a clone that is a link at the manifest's revision"
  finally
    Regula.Filesystem.removeOwn .directory base

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

-- A rename and the writing of a module are removals that the check finds; the write is counted.
run_cmd do
  let env ← getEnv
  let reach := Regula.Removal.rawRemovalsFrom env (Regula.Removal.filesystemObservers env)
    #[``callsReplacements]
  let replacements := [``IO.FS.rename, ``Lean.writeModule]
  unless reach.raw.size == 2 && replacements.all (fun replacement => reach.raw.contains
      (``callsReplacements, replacement)) && reach.unknown.isEmpty do
    throwError "the planted replacements are not raw removals: {reach.raw}, unknown \
      {reach.unknown}"
  unless reach.writes.contains (``callsReplacements, ``IO.FS.writeFile) do
    throwError "the planted write is not counted: {reach.writes}"

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
    if ← (base / "written").pathExists then
      throwError "fetch read a URL that starts with `-` as an option of curl"
    let direct ← IO.Process.output
      { cmd := "curl", args := #["--disable", "--silent", s!"-K{base / "config"}"] }
    unless direct.exitCode == 0 && (← (base / "written").pathExists) do
      throwError "the planted configuration of curl writes no file: {direct.stderr}"
  finally
    Regula.Filesystem.removeOwn .directory base

end Regula.RemovalControls
