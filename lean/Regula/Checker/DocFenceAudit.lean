import Regula.Checker.Documentation
import Regula.Checker.Lake
import Regula.Checker.AcceptanceLink

/-! Public Lean executable for documentation fence auditing: every Lean fence of the
Markdown below the documentation root and, with `--verso DIR:LIBRARY:RENDER`, every `lean`
block of that Verso library, whose build and rendering are then also required. -/

namespace Regula.Checker.DocFenceAudit

open Lean System
open Regula.Checker
open Regula.Checker.Documentation

structure Options where
  jobs : Nat := 4
  docsRoot : Option FilePath := none
  manifest : Option FilePath := none
  project : Option FilePath := none
  acceptanceLink : Option FilePath := none
  verso : Option (FilePath × Name × String) := none
  verbose : Bool := false
  help : Bool := false

private def usage : String :=
  "usage: lake exe docFenceAudit -- [--jobs N] [--verbose] [--docs-root PATH] " ++
  "[--project DIR] [--manifest PATH] [--acceptance-link PATH] [--verso DIR:LIBRARY:RENDER]"

/-- `DIR:LIBRARY:RENDER`: the Verso package directory (relative to the project), its
documentation library, and the executable that renders that library alone. -/
private def parseVerso (value : String) : IO (FilePath × Name × String) := do
  let (dir, library) ← IO.ofExcept <| parseVersoOption (":".intercalate ((value.splitOn ":").take 2))
  let [_, _, render] := value.splitOn ":"
    | throw <| IO.userError s!"--verso expects DIR:LIBRARY:RENDER, got {value}"
  if render.isEmpty then throw <| IO.userError s!"--verso expects DIR:LIBRARY:RENDER, got {value}"
  return (dir, library, render)

private def parseArgs : List String → Options → IO Options
  | [], options => return options
  | "--" :: rest, options => parseArgs rest options
  | "--jobs" :: value :: rest, options => do
      let jobs ← parseNatArg "--jobs" value
      parseArgs rest { options with jobs }
  | "--docs-root" :: value :: rest, options =>
      parseArgs rest { options with docsRoot := some (FilePath.mk value) }
  | "--manifest" :: value :: rest, options =>
      parseArgs rest { options with manifest := some (FilePath.mk value) }
  | "--project" :: value :: rest, options =>
      parseArgs rest { options with project := some (FilePath.mk value) }
  | "--acceptance-link" :: value :: rest, options =>
      parseArgs rest { options with acceptanceLink := some (FilePath.mk value) }
  | "--verso" :: value :: rest, options => do
      parseArgs rest { options with verso := some (← parseVerso value) }
  | "--verbose" :: rest, options => parseArgs rest { options with verbose := true }
  | "--help" :: rest, options | "-h" :: rest, options =>
      parseArgs rest { options with help := true }
  | flag :: _, _ => throw <| IO.userError s!"unknown or incomplete argument: {flag}"

private def resolve (repo path : FilePath) : FilePath :=
  if path.isAbsolute then path else repo / path.toString

/-- The first package pinned by both lock manifests at different Git revisions or sources. -/
private def sharedPinMismatch (root package : FilePath) : IO (Option String) := do
  let pins (dir : FilePath) : IO (Array (String × Json × Json)) := do
    let manifest ← readJson (dir / "lake-manifest.json")
    let packages ← IO.ofExcept (manifest.getObjValAs? (Array Json) "packages")
    packages.filterMapM fun p => do
      let name ← IO.ofExcept (p.getObjValAs? String "name")
      if (p.getObjValAs? String "type").toOption != some "git" then return none
      return some (name, (p.getObjVal? "url").toOption.getD .null, (p.getObjVal? "rev").toOption.getD .null)
  let rootPins ← pins root
  for (name, url, rev) in ← pins package do
    if let some (_, url', rev') := rootPins.find? (·.1 == name) then
      unless url == url' && rev == rev' do return some name
  return none

/-- Build the Verso library in the isolated copy, where every `lean` block is elaborated where it
is written by the library's own code block, and render it alone, which resolves every
cross-reference. The copy's library sources must be exactly the audited `documents`. -/
private def buildVerso (repo copy scratch : FilePath) (dir : FilePath) (library : Name) (render : String)
    (documents : Array RegulaPolicy.SourceSnapshot) : IO (Option String) := do
  let package := copy / dir.toString
  -- The Verso package shares the root's `.lake/packages`: a differing pin would make its build
  -- check out another revision of a shared dependency.
  if let some mismatch ← sharedPinMismatch copy package then
    return some s!"the Verso package pins {mismatch} differently from the root package"
  let copied ← captureVerso package library
  let original ← captureVerso (repo / dir.toString) library
  let relative (root : FilePath) (d : RegulaPolicy.SourceSnapshot) :=
    ((d.uri.dropPrefix (root.toString ++ "/")).toString, d.source)
  unless copied.map (relative package) == original.map (relative (repo / dir.toString)) &&
      original.all documents.contains do
    return some "the isolated copy's Verso sources are not the audited documents"
  let (_, failure) ← timedPhase "Verso documentation build" <|
    Lake.buildCheckedObservation package #[library.toString, render] "fresh"
  if let some lines := failure then return some ("\n".intercalate lines.toList)
  let output := scratch / "verso-render"
  let rendered ← timedPhase "Verso documentation rendering" <|
    runProcess package "lake" #["exe", render, "--output", output.toString] scrubbedLeanPathEnv
  unless rendered.succeeded do
    return some s!"Verso rendering failed ({rendered.exitCode}): {rendered.output}"
  return none

unsafe def run (args : List String) : IO UInt32 := do
  let options ← parseArgs args {}
  if options.help then IO.println usage; return 0
  if options.jobs == 0 then throw <| IO.userError "--jobs must be positive"
  let repo ← match options.project with
    | some dir => findRepoRoot dir
    | none => repoRoot
  let docsRoot := options.docsRoot.map (resolve repo) |>.getD (repo / "docs")
  let verso := options.verso.map fun (dir, library, _) => (repo / dir.toString, library)
  let sources : Sources := ⟨docsRoot, verso⟩
  let documents ← sources.capture
  withScratch repo "doc-fence-audit" fun scratch => do
    let copy := scratch / "project"
    copyProject repo copy scratch
    let manifestPath := options.manifest.map (resolve repo) |>.getD (Manifest.defaultPath copy)
    let configuration ← SourceBinding.configuration copy manifestPath
    let outcome ← SourceBinding.withUnchanged #[] configuration do
      let manifest ← Manifest.load manifestPath
      let inventory ← Lake.surfaceInventory copy
      let sources ← SourceBinding.capture inventory.moduleSources
      let dependencies ← Snapshot.dependencies inventory
      -- A linked run audits only the inputs ordinary acceptance already accepted.
      if let some link := options.acceptanceLink.map (resolve repo) then
        let digest ← AcceptanceLink.identity scratch copy docsRoot sources configuration dependencies documents
        AcceptanceLink.require link digest
        IO.println s!"acceptance link: documentation inputs equal the accepted ordinary inputs ({digest})"
      SourceBinding.withUnchanged sources configuration do
        SourceBinding.configurationUnchanged configuration
        let (buildProcess, buildResult) ← Lake.buildCheckedObservation copy (Manifest.positiveTargets manifest) "fresh"
        SourceBinding.unchanged sources
        SourceBinding.configurationUnchanged configuration
        if let some lines := buildResult then
          for line in lines do IO.println s!"    {line}"
          return 1
        IO.println "claimed surface built fresh; compiling fences"
        (← IO.getStdout).flush
        let result ← Documentation.auditBuiltProject copy docsRoot inventory sources configuration dependencies documents (Acceptance.buildObservation buildProcess) options.jobs options.verbose (verso := verso)
        if result != 0 then return result
        let some (dir, library, render) := options.verso | return result
        if let some failure ← buildVerso repo copy scratch dir library render documents then
          IO.println s!"FAIL: Verso documentation {library}: {failure}"
          return 1
        Documentation.Sources.check ⟨docsRoot, verso⟩ documents
        SourceBinding.unchanged sources
        IO.println s!"Verso documentation {library}: built fresh (every `lean` block elaborated where it is written) and rendered"
        return 0
    let outcome := outcome.bind id
    match outcome with
    | .ok result => return result
    | .error failure =>
        let finding ← IO.ofExcept <| RuleDiagnostics.contextFinding .admission docsRoot.toString
          failure.detail .documentationExample .incomplete
        RunFeedback.emit IO.println finding
        return 1

end Regula.Checker.DocFenceAudit

unsafe def main (args : List String) : IO UInt32 := do
  try
    Regula.Checker.initializeLeanSearchPath
    Regula.Checker.DocFenceAudit.run args
  catch error =>
    IO.eprintln s!"FAIL: {error}"
    return 1
