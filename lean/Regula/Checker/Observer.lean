import Lake.CLI.Build
import Lake.Build.Module
import Lake.Build.Common
import RegulaObserver.Record
import RegulaPolicy.Community
import RegulaPolicy.Elaboration

/-! # Regula's elaboration observer in a Lake build

How a Lake build loads Regula's elaboration observer (`RegulaObserver`) into the elaboration of a
module, and how the audit reads the record the observer writes into each claimed module's `.olean`
and turns it into the inputs of the RG2003 and RG2006 decisions
(`RegulaPolicy.Elaboration.failures`, `RegulaPolicy.Community.sourceFailures`).

A target loads the observer through Lake's own `plugins` setting, which names the observer's shared
library: `@regula/RegulaObserver:shared`, or `@/RegulaObserver:shared` in Regula's own
`lakefile.lean`, and RG2006 requires the same key in its `needs`
(`RegulaPolicy.Community.BuildOptions.observerNeed`). Lake's `presetup` facet hands a module's
plugins to Lean (`Lake/Build/Module.lean` lines 545 to 624, 1008 and 1062,
`ModulePreSetup.plugins`). It first awaits the job of the target's `needs`
(`LeanLib.recBuildExtraDepTargets`, `Lake/Build/Library.lean` lines 162 to 169), so a fresh build
builds the observer once, and mixes that job's trace into the module's trace, which Lake compares
to decide whether to replay the module, whatever the target's `platformIndependent`
(`Lake/Build/Module.lean` lines 591 and 600 to 603). A module replayed under that trace was
elaborated with the observer the build has; the trace of the plugins alone is left out when
`platformIndependent` is `true`. Regula declares no `presetup` facet. The
audit's builds run the facet that the workspace configures unchanged and keep each completed
result (`recordingPresetup`), from which the audit reads whether a claimed module's elaboration
loaded the running Regula's observer (`pluginLoaded`). A claimed module whose completed `presetup`
lacks it, such as under a dependency's facet that drops plugins, or whose target does not list the
observer's key in `needs`, has no record the audit reads, and RG2003 refuses it
(`decideRecord`). -/

namespace Regula.Checker.Observer

open Lean System

/-- The library of Regula's elaboration observer, as Regula's `lakefile.lean` declares it. -/
def observerLibrary : Name := `RegulaObserver

/-- The name of Regula's package, as its `lakefile.lean` declares it. -/
def regulaPackage : String := "regula"

/-- Whether the plugin target `key`, which a configuration of the package named `declaring`
declares, names the shared library of Regula's elaboration observer: the `shared` facet of the
`observerLibrary` library of the package `regulaPackage`, written `@regula/RegulaObserver:shared`
in a `lakefile.lean` or a `lakefile.toml` (`Lake/DSL/Key.lean` lines 47 to 62,
`Lake.PartialBuildKey.parse`), or `@/RegulaObserver:shared` in a configuration of that package,
since Lake resolves the elided package of a target to the declaring one (`Target.fetchIn`,
`Lake/Build/Target/Fetch.lean` line 138). That the package `regula` is Regula is the workspace
owner's assertion; whether the library Lake loaded is the running Regula's observer is decided
from the build (`pluginLoaded`). -/
def observerKey (declaring : Name) : _root_.Lake.PartialBuildKey → Bool
  | .facet (.packageTarget owner library) `shared =>
    library == observerLibrary &&
      (if owner.isAnonymous then declaring else owner) == Name.mkSimple regulaPackage
  | _ => false

/-- The directory of the package whose build directory holds the running executable,
`<package>/.lake/build/bin/<executable>`, or none when the path is shorter. -/
def runningPackageDir : IO (Option FilePath) := do
  let app ← IO.FS.realPath (← IO.appPath)
  return (app.parent.bind (·.parent)).bind (·.parent) |>.bind (·.parent)

/-- The completed result of each module's `presetup` facet in one build, by package and module,
whatever Lake stores, from which the audit reads the module's plugins (`presetupPlugins?`) and
source file (`presetupSource?`). -/
structure Presetups where
  /-- The result of each module's completed `presetup`, the latest when the facet ran again. -/
  completed : IO.Ref (Std.HashMap (Name × Name) _root_.Lake.ModulePreSetup)

/-- Empty records for one build. -/
def Presetups.new : BaseIO Presetups :=
  return { completed := ← IO.mkRef {} }

/-- The `presetup` facet `existing` that the workspace configures, with each job's result written
into `records` when it completes, whatever Lake stores. Each fetch of a module runs `existing`, and
the facet keeps whether `existing` is buildable and whether Lake stores its jobs (`memoize`,
`Lake/Build/Index.lean` lines 43 to 49), so each module's `presetup` runs as often, and gives the
same plugins and trace, as in an ordinary build of the workspace. -/
def recordingPresetup (existing : _root_.Lake.ModuleFacetConfig _root_.Lake.Module.presetupFacet)
    (records : Presetups) : _root_.Lake.ModuleFacetConfig _root_.Lake.Module.presetupFacet :=
  _root_.Lake.mkFacetJobConfig (buildable := existing.buildable) (memoize := existing.memoize)
    fun (mod : _root_.Lake.Module) => do
      let key := (mod.pkg.keyName, mod.name)
      let job ← existing.run mod
      job.mapM (sync := true) fun setup => do
        records.completed.modify (·.insert key setup)
        return setup

/-- The observer's shared library that the running Regula's build wrote, which its `Regula`
library needs and its targets load as a plugin: `<package>/.lake/build/lib/<library>` beside the
running executable (`runningPackageDir`). An error when the file is not there. Only `readSnapshot`
reads it, once, before `main` runs. -/
private def observerFile : IO FilePath := do
  let some dir ← runningPackageDir
    | throw <| IO.userError "the running executable is not in a package's build directory"
  let name := mkModuleInitializationStem observerLibrary (some regulaPackage)
  let file := dir / ".lake" / "build" / "lib" / _root_.Lake.nameToSharedLib name
  unless ← file.pathExists do
    throw <| IO.userError s!"the running Regula has not built its elaboration observer: {file}"
  return file

/-- The running Regula's observer library as the process read it at its start: the library's file
name and bytes, and the trace and hash files that Lake wrote beside it, by suffix, those that
exist. -/
structure Snapshot where
  /-- The file name of the library, as Lake names it (`Lake.nameToSharedLib`). -/
  fileName : String
  /-- The bytes of the library. -/
  library : ByteArray
  /-- The bytes of the files `<library>.trace` and `<library>.hash`, by suffix, those that exist. -/
  companions : Array (String × ByteArray)
  deriving Inhabited

/-- Read the running Regula's observer library (`observerFile`), with its trace and hash files, or
the reason that it cannot be read. -/
private def readSnapshot : IO (Except String Snapshot) := do
  try
    let file ← observerFile
    let some fileName := file.fileName
      | return .error s!"the observer library {file} has no file name"
    let library ← IO.FS.readBinFile file
    let mut companions := #[]
    for suffix in [".trace", ".hash"] do
      let companion : FilePath := ⟨file.toString ++ suffix⟩
      if ← companion.pathExists then
        companions := companions.push (suffix, ← IO.FS.readBinFile companion)
    return .ok { fileName, library, companions }
  catch error => return .error error.toString

/-- The running Regula's observer library (`readSnapshot`), read once when the process starts: a
module's `initialize` runs before `main`, so before the audit loads a workspace, copies a project or
runs a build. It is the only source of the observer's identity: the audit admits a loaded plugin
(`pluginLoaded`), places the observer in its copies (`placeRunning`) and loads it into a standalone
compilation (`Snapshot.write`) from it alone, never from the file it was read from, which a later
build can rewrite. -/
initialize runningSnapshot : Except String Snapshot ← readSnapshot

/-- The running Regula's observer library (`runningSnapshot`), or an error when the process could
not read it at its start. -/
def running : IO Snapshot :=
  match runningSnapshot with
  | .ok snapshot => pure snapshot
  | .error reason => throw <| IO.userError reason

/-- The files that `Snapshot.write` writes into the directory `dir`, each with its bytes: the
library under its file name, then its trace and hash files that exist, under that name with their
suffix. -/
def Snapshot.entries (snapshot : Snapshot) (dir : FilePath) : Array (FilePath × ByteArray) :=
  (#[("", snapshot.library)] ++ snapshot.companions).map fun (suffix, bytes) =>
    (dir / (snapshot.fileName ++ suffix), bytes)

/-- Write the snapshot's library and its trace and hash files into the directory `dir`
(`Snapshot.entries`), and return the library's path. -/
def Snapshot.write (snapshot : Snapshot) (dir : FilePath) : IO FilePath := do
  IO.FS.createDirAll dir
  for (destination, bytes) in snapshot.entries dir do
    IO.FS.writeBinFile destination bytes
    IO.setAccessRights destination {
      user := { read := true, write := true, execution := true }
      group := { read := true, execution := true }, other := { read := true, execution := true } }
  return dir / snapshot.fileName

/-- The directory in which `placeRunning` places the observer library in `package`: Lake's default
`sharedLibDir`, where the library's `shared` facet writes it. -/
def placementDir (package : FilePath) : FilePath :=
  package / ".lake" / "build" / "lib"

/-- Place the running Regula's observer library (`running`), with the trace and hash files that
Lake wrote beside it, in the build directory of `package`, a copy of a package `regula` that
declares the observer library under Lake's default layout, where the library's `shared` facet
writes it. Nothing is placed when the process could not read the library at its start.

The copy's build then elaborates the observer's modules itself and compiles them. Lake links the
library again unless the hash of its inputs, the compiled objects and libraries it links, its traced
arguments, the Lean version and the platform, equals the placed trace's, a hash that no path enters
(`LeanLib.recBuildShared`, `Lake/Build/Library.lean` lines 128 to 152; `buildLeanSharedLibSync`
and `buildArtifactUnlessUpToDate`, `Lake/Build/Common.lean` lines 1015 to 1029 and 685 to 726,
which an audit's build reaches with Lake's artifact cache off, through `checkHashUpToDate'`, lines
213 to 222). So a copy
whose observer source compiles to the running Regula's objects loads this file unchanged, and
`pluginLoaded` admits it by its bytes. Otherwise Lake links the library again, the linker writes
the output path into it, and its bytes differ, so it is not admitted. Admission rests on the bytes
alone, whatever Lake decides; that Lake reuses the placed file is trusted for availability only. -/
def placeRunning (package : FilePath) : IO Unit := do
  let .ok snapshot := runningSnapshot | return
  discard <| snapshot.write (placementDir package)

/-- The exact paths that `placeRunning` writes in `package`, none when the process could not read
the library at its start. -/
def placedPaths (package : FilePath) : Array FilePath :=
  match runningSnapshot with
  | .ok snapshot => (snapshot.entries (placementDir package)).map (·.1)
  | .error _ => #[]

/-- The plugins of the completed `presetup` of `module` of `package` in `completed`
(`Presetups.completed`), or none when no such job completed. -/
def presetupPlugins? (completed : Std.HashMap (Name × Name) _root_.Lake.ModulePreSetup)
    (package module : Name) : Option (Array FilePath) :=
  completed[(package, module)]?.map (·.plugins.map (·.path))

/-- The source file of the completed `presetup` of `module` of `package` in `completed`
(`Presetups.completed`), the file that Lake's `leanArts` facet compiles the module from
(`Module.recBuildLean`, `Lake/Build/Module.lean` lines 1006 to 1009), or none when no such job
completed. -/
def presetupSource? (completed : Std.HashMap (Name × Name) _root_.Lake.ModulePreSetup)
    (package module : Name) : Option FilePath :=
  completed[(package, module)]?.map (·.srcFile)

private unsafe def recordEntriesImpl (data : ModuleData) : Array RegulaObserver.Record :=
  match data.entries.find? (·.1 == RegulaObserver.records.name) with
  | some (_, entries) => entries.map unsafeCast
  | none => #[]

/-- The entries of the observer's extension (`RegulaObserver.records`) that the module data
`data` holds. Lean stores each entry as the value the extension exported, and its import casts it
to the extension's entry type the same way (`Lean.setImportedEntries`). The cast is sound only for
data that the running Regula's observer wrote, which `decideRecord` reads alone; an entry another
extension of that name wrote is outside what the record establishes. -/
@[implemented_by recordEntriesImpl]
opaque recordEntries (data : ModuleData) : Array RegulaObserver.Record

/-- The record the observer wrote into the `.olean` file `olean`, or none when the file holds no
entry of the observer's extension or several. The file is read alone (`readModuleData`), so none
of its imports is loaded and nothing of the module runs. The region that holds the file's data
stays mapped for the life of the process, since the record refers into it. -/
private def readRecord (olean : FilePath) : IO (Option RegulaObserver.Record) := do
  let (data, _) ← readModuleData olean
  return match recordEntries data with
    | #[record] => some record
    | _ => none

/-- Whether the plugins of a module's completed `presetup` (`presetupPlugins?`) include the running
Regula's observer `expected` (`running`): a plugin file whose bytes, read now, equal the library's
bytes that the process read at its start. That is the only criterion. A plugin's path proves
nothing, since a build can rewrite the file at a path, the running Regula's own included; a file
with other bytes is refused, whatever its name, path or source. False when there is no completed
`presetup` or a plugin cannot be read.

Assumes: the file that Lean loaded for the module holds, when it is read here, the bytes Lean
loaded. A file changed after Lean loaded it and before this comparison is outside what the
comparison establishes, since Lake reports a plugin by its path, not by the bytes Lean read. -/
def pluginLoaded (expected : Snapshot) (plugins : Option (Array FilePath)) : IO Bool := do
  let some plugins := plugins | return false
  plugins.anyM fun plugin => do
    match ← (IO.FS.readBinFile plugin).toBaseIO with
    | .ok bytes => return bytes.data == expected.library.data
    | .error _ => return false

/-- A position as the RG2003 decision reads it. -/
def location (position : Position) : RegulaPolicy.Elaboration.Location :=
  (position.line, position.column)

/-- A severity as the RG2003 decision reads it. -/
def severity : MessageSeverity → RegulaPolicy.Elaboration.Severity
  | .information => .information
  | .warning => .warning
  | .error => .error

/-- What the RG2003 decision reads of a record: none unless both linters completed. Each distinct
silent message, by severity and position, is listed once, however often the message log held it;
`RegulaPolicy.Elaboration.Complete` reads only which silent messages there are. -/
def observed (record : RegulaObserver.Record) : Option RegulaPolicy.Elaboration.Observed :=
  match record.fold, record.commands with
  | some fold, some commands => some {
      commands := commands.positions.toList.map location
      skipped := commands.skipped.toList.map location
      linted := fold.linted.toList.map location
      guards := fold.guards.toList.map fun g => (g.kind, location g.position)
      silent := (fold.silent.toList.map fun s => (severity s.severity, location s.position)).eraseDups }
  | _, _ => none

/-- An option value as RG2006 reads it, or none for a value of another type. -/
def optionValue : DataValue → Option RegulaPolicy.Community.OptionValue
  | .ofString s => some (.string s)
  | .ofBool b => some (.bool b)
  | .ofNat n => some (.nat n)
  | _ => none

/-- How the source set an option, as RG2006 reads it. -/
def form : RegulaObserver.Form → RegulaPolicy.Community.SourceForm
  | .command => .command
  | .commandIn => .commandIn
  | .term => .term
  | .tactic => .tactic
  | .docComment => .docComment
  | .elaborated => .elaborated

/-- The options a record says the module's source set, as RG2006 reads them. -/
def settings (record : RegulaObserver.Record) : List RegulaPolicy.Community.SourceSetting :=
  match record.fold with
  | none => []
  | some fold => fold.settings.toList.map fun s => ({
      name := s.name
      value := s.value.bind optionValue
      registeredDefault := s.registeredDefault.bind optionValue
      form := form s.form
      wrapped := s.wrapped
      location := location s.position })

/-- One RG2003 failure of a module's record, as a line of the build's report that names the module
`module`: its name, or the file that a standalone compilation compiled. The line of an observer
that Lean did not load, or whose target does not list it in `needs`, names the `plugins` entry
that loads it and the `needs` entry beside it, which RG2006 requires
(`RegulaPolicy.Community.BuildOptions.observerNeed`); an audit stops at this refusal before its
RG2006 stage. -/
def failureLine (module : String) : RegulaPolicy.Elaboration.Failure → String
  | .unloaded => s!"not observed: Regula's elaboration observer was not among the plugins Lean \
      loaded to elaborate {module}, or its target does not list it in needs; its target loads it \
      with plugins := #[`@regula/RegulaObserver:shared] in lakefile.lean, or \
      plugins = [\"@regula/RegulaObserver:shared\"] in lakefile.toml, with the same key in its \
      needs (RG2006)"
  | .absent => s!"not observed: {module} has no complete record of Regula's elaboration observer"
  | .guardMsgs (line, column) =>
    s!"{module}:{line}:{column}: the command contains `#guard_msgs`, which drops or checks the \
      messages of the command it runs"
  | .guard kind (line, column) =>
    s!"{module}:{line}:{column}: `{kind}` ran here, which drops or replaces the messages of the \
      command it runs"
  | .silent sev (line, column) =>
    let kind := match sev with
      | .information => "information message"
      | .warning => "warning"
      | .error => "error"
    s!"{module}:{line}:{column}: a silent {kind} is here, which Lean leaves out of its output"
  | .unobserved (line, column) =>
    s!"{module}:{line}:{column}: Regula's elaboration observer did not run on this command"

/-- The RG2003 failures of the claimed module `module` (`RegulaPolicy.Elaboration.failures`), with
`loaded` whether Lean loaded the observer for it (`pluginLoaded`) and `record` its record
(`readRecord`), as lines of the build's report that name it as `module` (`failureLine`). -/
def elaborationFailures (module : String) (loaded : Bool) (record : Option RegulaObserver.Record) :
    Array String :=
  (RegulaPolicy.Elaboration.failures loaded (record.bind observed)).toArray.map (failureLine module)

/-- The report of RG2003 failures of the observer's records (`elaborationFailures`), `lines`, for a
build that `subject` names: `FAIL[elaboration-hidden]` with the remedy, then each line. -/
def hiddenReport (subject : String) (lines : Array String) : Array String :=
  #[s!"FAIL[elaboration-hidden]: {subject} is not established warning-free (RG2003): Regula's \
    elaboration observer recorded, in a claimed module, a command that drops or replaces the \
    messages of the commands it runs, or a warning or error that Lean keeps out of the build's \
    output, or it did not observe the module's elaboration. Remove `#guard_msgs` and \
    `#guard_panic` from the claimed modules, and fix what the silent message reports."] ++ lines

/-- What the audit decides from the observer's record of one module. Only `decideRecord` makes
one, so a path that reads a record has both decisions: RG2003's failures, and the options the
source set, which RG2006 decides under the options of the target (`Verdict.sourceDetail`). -/
structure Verdict where
  private mk ::
  /-- The RG2003 failures (`elaborationFailures`), as lines of the report. -/
  hidden : Array String
  /-- Whether the module's `.olean` holds a record. -/
  recorded : Bool
  /-- The options the record says the source set (`settings`). -/
  settings : List RegulaPolicy.Community.SourceSetting

/-- The detail of the RG2006 finding for the module that `module` names, under the target options
`options`, with `mathlib` whether its surface imports Mathlib: the options that
`RegulaPolicy.Community.sourceFailures` rejects, or that the options are unknown without a record;
none when RG2006 accepts each. -/
def Verdict.sourceDetail (verdict : Verdict) (module : String)
    (options : RegulaPolicy.Community.BuildOptions) (mathlib : Bool) : Option String :=
  if !verdict.recorded then
    some s!"community-configuration: {module} has no record of Regula's elaboration observer, so \
      the options its source set are unknown"
  else match RegulaPolicy.Community.sourceFailures options mathlib verdict.settings with
    | [] => none
    | failed => some (RegulaPolicy.Community.sourceDetail module failed)

/-- The one decision on the observer's record in the `.olean` file `olean` of the module that
`subject` names, with `loaded` whether the file was written under the running Regula's observer.
Every path of the audit that reads a record calls it: a claimed build and a file audit. The file is
read only when `loaded`, since only that observer's record has the type the read gives it
(`recordEntries`). A file audit's own compilation loads that observer and writes the file. A Lake
build gives `loaded` only when the module's completed `presetup` loaded a library with the running
observer's bytes (`pluginLoaded`) and its target lists the observer's key in `needs`
(`observerKey`): the observer library's job trace is then in the module's trace through the
target's `extraDep` job (`Lake/Build/Library.lean` lines 162 to 169, `Lake/Build/Module.lean`
lines 600 to 603), so an `.olean` Lake replays was built under the library whose bytes
`pluginLoaded` matched. A module without `loaded`, a missing file, or one without exactly one
record gives no record. -/
def decideRecord (subject : String) (loaded : Bool) (olean : FilePath) : IO Verdict := do
  let record ← if loaded && (← olean.pathExists) then
      match ← (readRecord olean).toBaseIO with
      | .ok record => pure record
      | .error _ => pure none
    else pure none
  return ⟨elaborationFailures subject loaded record, record.isSome,
    (record.map settings).getD []⟩

end Regula.Checker.Observer

