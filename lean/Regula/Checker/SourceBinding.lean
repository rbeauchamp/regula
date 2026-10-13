import Regula.Checker.ProducerReport
import Regula.Checker.Common
import Regula.Filesystem

/-! # Source and configuration binding

Exact source/configuration snapshots at operational boundaries. Equality guards
detect observed changes; filesystem reads, Lake/compiler correspondence and the absence
of an undetected change-and-restore race remain trusted operational assumptions. -/
namespace Regula.Checker.SourceBinding
open Lean System
open ProducerReport

/-- Freeze a Lake/Lean-resolved source map, refusing conflicting module identities. -/
def capture (sources : Array (Name × FilePath))
    (observe : Array ProducerReport.SourceBinding → IO Unit := fun _ => pure ()) :
    IO (Array ProducerReport.SourceBinding) := do
  let mut bindings := #[]
  for (moduleName, path) in sources do
    if let some previous := bindings.find?
        (fun (s : ProducerReport.SourceBinding) => s.moduleName == moduleName) then
      unless previous.path == path.toString do
        throw <| IO.userError "producer-source: conflicting module source paths"
      continue
    if moduleName.isAnonymous then throw <| IO.userError "producer-source: anonymous source module"
    bindings := bindings.push
        { moduleName, path := path.toString, content := ← IO.FS.readFile path }
    observe bindings
  return bindings

/-- Compare exact text at each IO boundary; never recapture changed text as the claim. -/
def checkSources (sources : Array ProducerReport.SourceBinding) : IO
    (Except AdmissionFailure Unit) := do
  for source in sources do
    let current ← (IO.FS.readFile source.path).toBaseIO
    match current with
    | .error error =>
        return .error
            ⟨s!"producer-source: source snapshot unavailable: {source.moduleName} \
              ({source.path}): {error}"⟩
    | .ok current =>
      unless current == source.content do
        return .error ⟨s!"producer-source: source snapshot changed: {source.moduleName}"⟩
  return .ok ()

/-- Throw an error when `checkSources` finds a source missing or changed. -/
def unchanged (sources : Array ProducerReport.SourceBinding) : IO Unit := do
  IO.ofExcept <| (← checkSources sources).mapError (·.detail)

/-- Require the producer's owned-source account to be the caller's frozen account
restricted to the actual loaded environment. -/
def validateAgainst (expected : Array ProducerReport.SourceBinding)
    (report : ProducerReport.Environment) :
    Except AdmissionFailure Unit := do
  let required := expected.filter (fun source => report.modules.contains source.moduleName)
  unless report.sourceBindings.size == required.size &&
      report.sourceBindings.all required.contains do
    throw ⟨"producer-source: report differs from requested source snapshots"⟩

/-- Require each supplied frontend transcript to retain its captured module/path/text.
The caller separately decides which transcripts are required. -/
def transcriptsMatch (sources : Array ProducerReport.SourceBinding)
    (transcripts : Array RegulaPolicy.Frontend.Transcript) : Except AdmissionFailure Unit := do
  for transcript in transcripts do
    unless sources.any (fun source => source.moduleName == transcript.module &&
        source.path == transcript.source && source.content == transcript.sourceContent) do
      throw ⟨"producer-source: frontend differs from requested source snapshot"⟩

/-- The configuration files of the project at `repo` whose presence and text a snapshot binds:
the selected policy manifest `manifest` first, then the root package's Lake configuration files,
toolchain file, Lake manifest and Lake's package-override file. A request records `manifest`
itself as its selection (`ResultProtocol.requestJson`), never a file name reconstructed from this
list (`configurationPaths_policy`). -/
def configurationPaths (repo manifest : FilePath) : Array FilePath :=
  #[manifest, repo / "lakefile.lean", repo / "lakefile.toml", repo / "lean-toolchain",
    repo / "lake-manifest.json", repo / ".lake" / "package-overrides.json"]

/-- The configuration files of the project at `repo` that a snapshot captures beside its manifest
(`configuration`): its Lake configuration in either format, its toolchain, its lock manifest and
Lake's package overrides. -/
def configurationFiles (repo : FilePath) : Array FilePath :=
  #[repo / "lakefile.lean", repo / "lakefile.toml", repo / "lean-toolchain",
    repo / "lake-manifest.json", repo / ".lake" / "package-overrides.json"]

/-- The selected policy manifest is the first configuration path. -/
theorem configurationPaths_policy (repo manifest : FilePath) :
    (configurationPaths repo manifest)[0]? = some manifest := rfl

/-- Configuration absence is also part of the snapshot: each of `configurationPaths`, in order,
with its text, `none` when Lean reports that nothing is there (`Filesystem.readFileIfPresent`).
Each other failure of a read, such as a permission error, is thrown, so it is never recorded as
absence. This is observation binding, not a new configuration resolution rule or an
authentication of dependencies. -/
def configuration (repo manifest : FilePath) : IO (Array (FilePath × Option String)) :=
  (configurationPaths repo manifest).mapM fun path => do
    return (path, ← Regula.Filesystem.readFileIfPresent path)

/-- Refuse a change in any captured configuration file's presence or exact text, and a read that
fails other than by finding nothing there (`Filesystem.readFileIfPresent`). -/
def checkConfiguration (snapshot : Array (FilePath × Option String)) : IO
    (Except AdmissionFailure Unit) := do
  for (path, content) in snapshot do
    let current ← (Regula.Filesystem.readFileIfPresent path).toBaseIO
    match current with
    | .error error =>
        return .error ⟨s!"producer-source: configuration snapshot unavailable: {path}: {error}"⟩
    | .ok current =>
      unless current == content do
        return .error ⟨s!"producer-source: configuration snapshot changed: {path}"⟩
  return .ok ()

/-- Throw an error when `checkConfiguration` finds a configuration file changed, added or
removed. -/
def configurationUnchanged (snapshot : Array (FilePath × Option String)) : IO Unit := do
  IO.ofExcept <| (← checkConfiguration snapshot).mapError (·.detail)

/-- Check the sources and configuration, run `action`, and check them again. A change is
returned as an admission failure: before the action it skips the action, and after it it takes
precedence over an action error. Otherwise the action's value is returned or its error
rethrown. -/
def withUnchanged {α : Type} (sources : Array ProducerReport.SourceBinding)
    (configuration : Array (FilePath × Option String)) (action : IO α) :
    IO (Except AdmissionFailure α) := do
  let check := do
    if let .error failure ← checkSources sources then return .error failure
    checkConfiguration configuration
  if let .error failure ← check then return .error failure
  let result ← action.toBaseIO
  if let .error failure ← check then return .error failure
  match result with
  | .ok value => return .ok value
  | .error error => throw error

end Regula.Checker.SourceBinding
