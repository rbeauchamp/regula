import Regula.Checker.ProducerReport
import Regula.Checker.Common

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
    if let some previous := bindings.find? (fun (s : ProducerReport.SourceBinding) => s.moduleName == moduleName) then
      unless previous.path == path.toString do
        throw <| IO.userError "producer-source: conflicting module source paths"
      continue
    if moduleName.isAnonymous then throw <| IO.userError "producer-source: anonymous source module"
    bindings := bindings.push { moduleName, path := path.toString, content := ← IO.FS.readFile path }
    observe bindings
  return bindings

/-- Compare exact text at each IO boundary; never recapture changed text as the claim. -/
def checkSources (sources : Array ProducerReport.SourceBinding) : IO (Except AdmissionFailure Unit) := do
  for source in sources do
    let current ← (IO.FS.readFile source.path).toBaseIO
    match current with
    | .error error => return .error ⟨s!"producer-source: source snapshot unavailable: {source.moduleName} ({source.path}): {error}"⟩
    | .ok current =>
      unless current == source.content do
        return .error ⟨s!"producer-source: source snapshot changed: {source.moduleName}"⟩
  return .ok ()

def unchanged (sources : Array ProducerReport.SourceBinding) : IO Unit := do
  IO.ofExcept <| (← checkSources sources).mapError (·.detail)

/-- Require the producer's owned-source account to be the caller's frozen account
restricted to the actual loaded environment. -/
def validateAgainst (expected : Array ProducerReport.SourceBinding) (report : ProducerReport.Environment) :
    Except AdmissionFailure Unit := do
  let required := expected.filter (fun source => report.modules.contains source.moduleName)
  unless report.sourceBindings.size == required.size && report.sourceBindings.all required.contains do
    throw ⟨"producer-source: report differs from requested source snapshots"⟩

/-- Require each supplied frontend transcript to retain its captured module/path/text.
The caller separately decides which transcripts are required. -/
def transcriptsMatch (sources : Array ProducerReport.SourceBinding)
    (transcripts : Array RegulaPolicy.Frontend.Transcript) : Except AdmissionFailure Unit := do
  for transcript in transcripts do
    unless sources.any (fun source => source.moduleName == transcript.module &&
        source.path == transcript.source && source.content == transcript.sourceContent) do
      throw ⟨"producer-source: frontend differs from requested source snapshot"⟩

/-- Configuration absence is also part of the snapshot. This is observation binding,
not a new configuration resolution rule or an authentication of dependencies. -/
def configuration (repo manifest : FilePath) : IO (Array (FilePath × Option String)) :=
  #[manifest, repo / "lakefile.lean", repo / "lakefile.toml", repo / "lean-toolchain",
    repo / "lake-manifest.json", repo / ".lake" / "package-overrides.json"].mapM fun path => do
      let content ← if ← path.pathExists then some <$> IO.FS.readFile path else pure none
      return (path, content)

/-- Refuse a change in any captured configuration file's presence or exact text. -/
def checkConfiguration (snapshot : Array (FilePath × Option String)) : IO (Except AdmissionFailure Unit) := do
  for (path, content) in snapshot do
    let read : IO (Option String) := do
      if ← path.pathExists then pure (some (← IO.FS.readFile path)) else pure none
    let current ← read.toBaseIO
    match current with
    | .error error => return .error ⟨s!"producer-source: configuration snapshot unavailable: {path}: {error}"⟩
    | .ok current =>
      unless current == content do
        return .error ⟨s!"producer-source: configuration snapshot changed: {path}"⟩
  return .ok ()

def configurationUnchanged (snapshot : Array (FilePath × Option String)) : IO Unit := do
  IO.ofExcept <| (← checkConfiguration snapshot).mapError (·.detail)

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
