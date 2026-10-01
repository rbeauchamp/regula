import Regula.Checker.Documentation
import Regula.Checker.Lake
import Regula.Checker.AcceptanceLink
import RegulaCore.Site

/-! # Documentation fence audit executable

Public Lean executable for documentation fence auditing: every Lean fence of the
Markdown below the documentation root and, with `--verso DIR:LIBRARY:RENDER`, every `lean`
block of that Verso library, the standard, whose build and rendering are also required (with
`--verso`, every fence elaborates in the freshly built Verso package's workspace, which requires
the project and the other packages the standard's examples import), and whose rendered pages
must define every anchor the rule registry and the Markdown link, with the checklist's rows
exactly `Regula.checklistRows`. -/

namespace Regula.Checker.DocFenceAudit

open Lean System
open Regula.Checker
open Regula.Checker.Documentation

/-- The command-line options of one `docFenceAudit` invocation. -/
structure Options where
  /-- `--jobs N`: how many fence tasks run concurrently (4 by default; must be positive). -/
  jobs : Nat := 4
  /-- `--docs-root PATH`: the Markdown documentation root, by default `docs` in the project. -/
  docsRoot : Option FilePath := none
  /-- `--manifest PATH`: the surface manifest, by default `foundation_manifest.json`. -/
  manifest : Option FilePath := none
  /-- `--project DIR`: audit the nearest directory at or above `DIR` that has a Lake
  configuration and a `lean-toolchain`, instead of the current one. -/
  project : Option FilePath := none
  /-- `--acceptance-link PATH`: the acceptance link that ordinary acceptance recorded; the
  audit refuses unless its own inputs have the identity recorded there. -/
  acceptanceLink : Option FilePath := none
  /-- `--verso DIR:LIBRARY:RENDER`: the Verso library whose `lean` blocks are also audited,
  and which is then built fresh, rendered and checked for the anchors and rows it must define. -/
  verso : Option VersoPackage := none
  /-- `--verbose`: print the full detail of each failed fence instead of its first part. -/
  verbose : Bool := false
  /-- `--help` or `-h`: print the usage text and exit. -/
  help : Bool := false

private def usage : String :=
  "usage: lake exe docFenceAudit -- [--jobs N] [--verbose] [--docs-root PATH] " ++
  "[--project DIR] [--manifest PATH] [--acceptance-link PATH] [--verso DIR:LIBRARY:RENDER]"

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
      parseArgs rest { options with verso := some (← IO.ofExcept (parseVersoOption value)) }
  | "--verbose" :: rest, options => parseArgs rest { options with verbose := true }
  | "--help" :: rest, options | "-h" :: rest, options =>
      parseArgs rest { options with help := true }
  | flag :: _, _ => throw <| IO.userError s!"unknown or incomplete argument: {flag}"

private def resolve (repo path : FilePath) : FilePath :=
  if path.isAbsolute then path else repo / path.toString

/-- The first package that the Verso package at `package` and a package it requires by local path
both pin by Git at different revisions or sources, with that package's recorded directory. They
share one packages directory, so such a pin would make one build check out another revision of a
shared dependency. -/
private def sharedPinMismatch (package : FilePath) : IO (Option String) := do
  let entries (dir : FilePath) : IO (Array Json) := do
    IO.ofExcept ((← readJson (dir / "lake-manifest.json")).getObjValAs? (Array Json) "packages")
  let pins (dir : FilePath) : IO (Array (String × Json × Json)) := do
    (← entries dir).filterMapM fun p => do
      let name ← IO.ofExcept (p.getObjValAs? String "name")
      if (p.getObjValAs? String "type").toOption != some "git" then return none
      return some
          (name, (p.getObjVal? "url").toOption.getD .null, (p.getObjVal? "rev").toOption.getD .null)
  let versoPins ← pins package
  for entry in ← entries package do
    unless (entry.getObjValAs? String "type").toOption == some "path" do continue
    let dir ← IO.ofExcept (entry.getObjValAs? String "dir")
    let requiredPins ← pins (package / dir)
    for (name, url, rev) in versoPins do
      if let some (_, url', rev') := requiredPins.find? (·.1 == name) then
        unless url == url' && rev == rev' do return some s!"{name} (against {dir})"
  return none

/-- The rendered pages below `root`, by their paths below it. -/
private def renderedPages (root : FilePath) : IO (List Regula.Site.Page) := do
  let components := root.normalize.components
  (← root.walkDir).toList.filterMapM fun path => do
    if path.extension != some "html" then return none
    let relative := "/".intercalate (path.normalize.components.drop components.length)
    return some (Regula.Site.Page.ofHtml relative (← IO.FS.readFile path))

/-- Build the Verso library in the isolated copy, where every `lean` block is elaborated where it
is written by the library's own code block. The copy's library sources and Verso package inputs
must be exactly the audited and linked ones (`linked`), and the Verso package must pin every Git
dependency it shares with a package it requires by path at the same revision. -/
private def prepareVerso (repo copy : FilePath) (verso : VersoPackage)
    (linked : Array RegulaPolicy.SourceSnapshot) : IO (Option String) := do
  let package := copy / verso.dir.toString
  let versoDir := repo / verso.dir.toString
  if let some mismatch ← sharedPinMismatch package then
    return some s!"the Verso package pins {mismatch} differently from a package it requires by path"
  let library ← captureVerso { verso with dir := versoDir }
  let copied := (← captureVerso { verso with dir := package }) ++
      (← captureVersoPackage copy { verso with dir := package })
  let original := library ++ (← captureVersoPackage repo { verso with dir := versoDir })
  let relative (root : FilePath) (d : RegulaPolicy.SourceSnapshot) :=
    ((d.uri.dropPrefix (root.toString ++ "/")).toString, d.source)
  unless copied.map (relative package) == original.map (relative versoDir) &&
      original.all linked.contains do
    return some "the isolated copy's Verso sources and package inputs are not the audited ones"
  let (_, failure) ← timedPhase "Verso documentation build" <|
    Lake.buildCheckedObservation package #[verso.library.toString, verso.render] "fresh"
  if let some lines := failure then return some ("\n".intercalate lines.toList)
  return none

/-- The Lean search path of the Lake workspace rooted at `dir`: its root package's library
directory, then every package's, as Lake computes them. -/
private def workspaceSearchPath (dir : FilePath) : IO (Array FilePath) :=
  Workspace.withRootWorkspace dir fun ws => pure (#[ws.root.leanLibDir] ++ ws.leanPath.toArray)

/-- Render the Verso library that `prepareVerso` built in the isolated copy, alone, which resolves
every cross-reference. The rendered pages must define every section and checklist-row anchor the
rule registry links (`Regula.Site.standardAnchors`) and every anchor the linked Markdown below
`docsRoot` links (`Regula.Site.documentAnchors`); the rendered checklist's rows must be exactly
`Regula.checklistRows`, in order (`Regula.Site.rowsMismatch`); and each cited section's source
must be a module of the library. -/
private def renderVerso (repo copy scratch : FilePath) (verso : VersoPackage)
    (linked : Array RegulaPolicy.SourceSnapshot) : IO (Option String) := do
  let package := copy / verso.dir.toString
  let library ← captureVerso { verso with dir := repo / verso.dir.toString }
  let output := scratch / "verso-render"
  let rendered ← timedPhase "Verso documentation rendering" <|
    runProcess package "lake" #["exe", verso.render, "--output", output.toString]
        scrubbedLeanPathEnv
  unless rendered.succeeded do
    return some s!"Verso rendering failed ({rendered.exitCode}): {rendered.output}"
  let html := output / "html-multi"
  let pages ← renderedPages html
  let missing := Regula.Site.missingAnchors pages Regula.Site.standardAnchors
  unless missing.isEmpty do
    return some s!"the rendered standard does not define anchors the rule registry links: {missing}"
  let markdown := linked.filter fun d => (FilePath.mk d.uri).extension == some "md"
  let missing := Regula.Site.missingAnchors pages
      (Regula.Site.documentAnchors (markdown.map (·.source)).toList)
  unless missing.isEmpty do
    return some s!"the rendered standard does not define anchors the documentation links: {missing}"
  let rows := Regula.Site.renderedRows
      (← IO.FS.readFile (html / Regula.checklistChapter / "index.html"))
  if let some mismatch := Regula.Site.rowsMismatch rows then
    return some s!"the rendered checklist's rows are not Regula.checklistRows: {mismatch}"
  let unknown := Regula.Clause.all.filter fun c => !library.any
                                                    (·.uri == (repo / c.source).toString)
  unless unknown.isEmpty do
    return some
        s!"cited sections whose source is not a module \
          of {verso.library}: {unknown.map (·.heading)}"
  return none

/-- Run one documentation fence audit and return its exit code. In an isolated copy of the
project it builds the claimed surfaces fresh; with `--verso` it then builds the Verso library
fresh, whose workspace every fence then elaborates in; it compiles every Lean fence below the
documentation root and, with `--verso`, every `lean` block of the library, then renders the
library and checks its anchors and checklist rows. With `--acceptance-link`, it first requires the
inputs to equal the accepted ones. -/
unsafe def run (args : List String) : IO UInt32 := do
  let options ← parseArgs args {}
  if options.help then IO.println usage; return 0
  if options.jobs == 0 then throw <| IO.userError "--jobs must be positive"
  let repo ← match options.project with
    | some dir => findRepoRoot dir
    | none => repoRoot
  let docsRoot := options.docsRoot.map (resolve repo) |>.getD (repo / "docs")
  let verso := options.verso.map fun verso => { verso with dir := repo / verso.dir.toString }
  let sources : Sources := ⟨docsRoot, verso⟩
  let documents ← sources.capture
  -- The linked identity also brackets the Verso package's inputs.
  let linked ← sources.captureLinked repo
  withScratch repo "doc-fence-audit" fun scratch => do
    let copy := scratch / "project"
    copyProject repo copy scratch
    let manifestPath := options.manifest.map (resolve repo) |>.getD (Manifest.defaultPath copy)
    let configuration ← SourceBinding.configuration copy manifestPath
    let outcome ← SourceBinding.withUnchanged #[] configuration do
      let inventory ← Lake.surfaceInventory copy
      let manifest ← Manifest.loadFor manifestPath inventory
      let sources ← SourceBinding.capture inventory.moduleSources
      let dependencies ← Snapshot.dependencies inventory
      -- A linked run audits only the inputs ordinary acceptance already accepted.
      if let some link := options.acceptanceLink.map (resolve repo) then
        let digest ← AcceptanceLink.identity scratch copy docsRoot sources configuration
            dependencies linked
        AcceptanceLink.require link digest
        IO.println
            s!"acceptance link: documentation inputs equal the accepted ordinary inputs ({digest})"
      SourceBinding.withUnchanged sources configuration do
        SourceBinding.configurationUnchanged configuration
        let (buildProcess, buildResult) ← Lake.buildCheckedObservation copy
            (Manifest.positiveTargets manifest) "fresh"
        SourceBinding.unchanged sources
        SourceBinding.configurationUnchanged configuration
        if let some lines := buildResult then
          for line in lines do IO.println s!"    {line}"
          return 1
        IO.println "claimed surface built fresh"
        -- With a Verso package, every example elaborates in its workspace, which requires the
        -- project and resolves every module the documentation imports; it is built fresh first.
        let environment ← match options.verso with
          | none => pure none
          | some requested =>
            if let some failure ← prepareVerso repo copy requested linked then
              IO.println s!"FAIL: Verso documentation {requested.library}: {failure}"
              return 1
            let package := copy / requested.dir.toString
            pure (some (package, ← workspaceSearchPath package,
              ← versoLocalModules copy { requested with dir := package }))
        IO.println "compiling fences"
        (← IO.getStdout).flush
        let result ← Documentation.auditBuiltProject copy docsRoot inventory sources configuration
            dependencies documents (Acceptance.buildObservation buildProcess) options.jobs
                options.verbose (verso := verso) (environment := environment)
        if result != 0 then return result
        let some requested := options.verso | return result
        if let some failure ← renderVerso repo copy scratch requested linked then
          IO.println s!"FAIL: Verso documentation {requested.library}: {failure}"
          return 1
        Documentation.Sources.checkLinked ⟨docsRoot, verso⟩ repo linked
        SourceBinding.unchanged sources
        IO.println s!"Verso documentation {requested.library}: built fresh (every `lean` block \
          elaborated where it is written), rendered, defines every anchor the rule registry and \
          the documentation link, and its checklist rows are exactly Regula.checklistRows"
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

/-- The `docFenceAudit` executable: initialize the Lean search path, then `run`, reporting
any escaping error as `FAIL` with exit code 1. -/
unsafe def main (args : List String) : IO UInt32 := do
  try
    Regula.Checker.initializeLeanSearchPath
    Regula.Checker.DocFenceAudit.run args
  catch error =>
    IO.eprintln s!"FAIL: {error}"
    return 1
