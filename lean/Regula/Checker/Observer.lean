import Lake.CLI.Build
import Lake.Build.Module
import Lake.Build.Common
import RegulaObserver.Record
import RegulaPolicy.Community
import RegulaPolicy.Elaboration

/-! # Regula's elaboration observer in a Lake build

How a Lake build loads Regula's elaboration observer (`RegulaObserver`) into the elaboration of
each module of the root package, and how the audit reads the record the observer writes into each
claimed module's `.olean` and turns it into the inputs of the RG2003 and RG2006 decisions
(`RegulaPolicy.Elaboration.failures`, `RegulaPolicy.Community.sourceFailures`).

The `presetup` facet of a module decides the plugins Lean loads while elaborating it
(`Lake/Build/Module.lean` lines 545 to 622, `ModulePreSetup.plugins`), and Lake fetches it
through the workspace's facet table, so a facet that a package declares replaces Lake's own.
`observerPresetup` wraps Lake's own facet: it adds the observer's shared library to the plugins
of each module of the root package outside the observer's own library, and mixes that library's
trace into the module's trace, which Lake compares to decide whether to replay the module
(`Lake/Build/Module.lean` lines 1008 and 1062). A module replayed under that trace was elaborated
with that plugin. Regula's `lakefile.lean` declares the same facet for ordinary builds, and the
audit's builds install it themselves (`Regula.Checker.Lake.Build.runObserved`). -/

namespace Regula.Checker.Observer

open Lean System

/-- The library of Regula's elaboration observer, as Regula's `lakefile.lean` declares it. -/
def observerLibrary : Name := `RegulaObserver

/-- The name of Regula's package, as its `lakefile.lean` declares it. -/
def regulaPackage : String := "regula"

/-- The directory of the package whose build directory holds the running executable,
`<package>/.lake/build/bin/<executable>`, or none when the path is shorter. -/
def runningPackageDir : IO (Option FilePath) := do
  let app ← IO.FS.realPath (← IO.appPath)
  return (app.parent.bind (·.parent)).bind (·.parent) |>.bind (·.parent)

/-- The `presetup` facet of a module with Regula's observer: Lake's own facet
(`Lake.Module.presetupFacetConfig`), and for a module of the root package for which `own` does not
hold, the observer's shared library that `plugin` fetches added to the module's plugins, with that
library's trace mixed into the module's trace. -/
def observerPresetup (plugin : _root_.Lake.FetchM (_root_.Lake.Job _root_.Lake.Dynlib))
    (own : _root_.Lake.Module → Bool) :
    _root_.Lake.ModuleFacetConfig _root_.Lake.Module.presetupFacet :=
  _root_.Lake.mkFacetJobConfig (buildable := false) fun (mod : _root_.Lake.Module) => do
    let job ← _root_.Lake.Module.presetupFacetConfig.run mod
    if !mod.pkg.isRoot || own mod then return job
    let shared ← plugin
    job.bindM (sync := true) fun setup => shared.mapM (sync := true) fun dynlib =>
      return { setup with
        plugins := setup.plugins.push dynlib
        trace := setup.trace.mix (shared.getTrace.withCaption "Regula's elaboration observer") }

/-- Where the audit takes the observer's shared library from in a build of the workspace `ws`:
from the package of `ws` that is the running Regula, through Lake's own job for the observer's
library, so that the build has the trace of an ordinary build of that workspace; otherwise from
the file the running Regula's build wrote, which its `Regula` library needs. Returns the job and
the file. -/
def observerPlugin (ws : _root_.Lake.Workspace) :
    IO (_root_.Lake.FetchM (_root_.Lake.Job _root_.Lake.Dynlib) × FilePath × Option Name) := do
  let some dir ← runningPackageDir
    | throw <| IO.userError "the running executable is not in a package's build directory"
  for pkg in ws.packages do
    if (← IO.FS.realPath pkg.dir) == dir then
      let some lib := pkg.findLeanLib? observerLibrary
        | throw <| IO.userError s!"the running Regula's package has no library {observerLibrary}"
      return (lib.shared.fetch, lib.sharedLibFile, some pkg.keyName)
  let name := mkModuleInitializationStem observerLibrary (some regulaPackage)
  let file := dir / ".lake" / "build" / "lib" / _root_.Lake.nameToSharedLib name
  unless ← file.pathExists do
    throw <| IO.userError s!"the running Regula has not built its elaboration observer: {file}"
  let fetch : _root_.Lake.FetchM (_root_.Lake.Job _root_.Lake.Dynlib) := do
    let job ← _root_.Lake.inputBinFile file
    return job.map fun path => { path, name, plugin := true }
  return (fetch, file, none)

/-- The plugins of the completed `presetup` of `module` of `package` in the build's `store`, or
none when the store holds no completed one. -/
def presetupPlugins? (store : _root_.Lake.BuildStore) (package module : Name) :
    Option (Array FilePath) :=
  let job? : Option (_root_.Lake.Job (_root_.Lake.FacetOut _root_.Lake.Module.presetupFacet)) :=
    store.get? (_root_.Lake.BuildKey.packageModuleFacet package module
      _root_.Lake.Module.presetupFacet)
  job?.bind fun job => job.task.get.result?.map fun data =>
    (_root_.Lake.ofFamily data : _root_.Lake.ModulePreSetup).plugins.map (·.path)

private unsafe def recordEntriesImpl (data : ModuleData) : Array RegulaObserver.Record :=
  match data.entries.find? (·.1 == RegulaObserver.records.name) with
  | some (_, entries) => entries.map unsafeCast
  | none => #[]

/-- The entries of the observer's extension (`RegulaObserver.records`) that the module data
`data` holds. Lean stores each entry as the value the extension exported, and its import casts it
to the extension's entry type the same way (`Lean.setImportedEntries`); an entry another
extension of that name wrote is outside what the record establishes. -/
@[implemented_by recordEntriesImpl]
opaque recordEntries (data : ModuleData) : Array RegulaObserver.Record

/-- The record the observer wrote into the `.olean` file `olean`, or none when the file holds no
entry of the observer's extension or several. The file is read alone (`readModuleData`), so none
of its imports is loaded and nothing of the module runs. The region that holds the file's data
stays mapped for the life of the process, since the record refers into it. -/
def readRecord (olean : FilePath) : IO (Option RegulaObserver.Record) := do
  let (data, _) ← readModuleData olean
  return match recordEntries data with
    | #[record] => some record
    | _ => none

/-- Whether the plugins of a module's completed `presetup` (`presetupPlugins?`) include the
observer's shared library `expected`, compared by real path; false when there is no completed
`presetup`. -/
def pluginLoaded (expected : FilePath) (plugins : Option (Array FilePath)) : IO Bool := do
  let some plugins := plugins | return false
  let real (path : FilePath) : IO FilePath := do
    match ← (IO.FS.realPath path).toBaseIO with
    | .ok path => return path
    | .error _ => return path
  let expected ← real expected
  plugins.anyM fun plugin => return (← real plugin) == expected

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
      origin := s.origin.map (·.«module»)
      location := location s.position })

/-- One RG2003 failure of a module's record, as a line of the build's report. -/
def failureLine (module : Name) : RegulaPolicy.Elaboration.Failure → String
  | .unloaded => s!"not observed: Regula's elaboration observer was not among the plugins Lean \
      loaded to elaborate {module}"
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
(`readRecord`), as lines of the build's report. -/
def elaborationFailures (module : Name) (loaded : Bool) (record : Option RegulaObserver.Record) :
    Array String :=
  (RegulaPolicy.Elaboration.failures loaded (record.bind observed)).toArray.map (failureLine module)

end Regula.Checker.Observer
