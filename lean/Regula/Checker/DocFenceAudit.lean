import Regula.Removal
import Regula.TaskManagerCheck
import Regula.Checker.Documentation
import Regula.Checker.Lake
import Regula.Checker.AcceptanceLink
import Regula.Checker.LintBuild
import RegulaCore.Prose

/-! # Documentation fence audit executable

Public Lean executable for documentation fence auditing: every Lean fence of the
Markdown below the documentation root and, with `--verso DIR:LIBRARY:RENDER`, every `lean`
block of that Verso library, the standard, whose build and rendering are also required (with
`--verso`, every fence elaborates in the freshly built Verso package's workspace, which requires
the project and the other packages the standard's examples import), and whose rendered pages
must define every anchor the rule registry and the Markdown link, with the checklist's rows
exactly `Regula.checklistRows` and every rule ID in their prose a link to its rule page
(`Regula.Prose`). -/

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
  audit first refuses, before its build, unless its own inputs have the identity recorded there.
  When the link also records the build that step left in this project's `.lake/build`, the audit
  places the part of that build output that its claimed build compiles in its copy before its own
  build, only as `BuildReuse.reuse` decides (`AcceptanceLink.placeRetained`). -/
  acceptanceLink : Option FilePath := none
  /-- `--verso DIR:LIBRARY:RENDER`: the Verso library whose `lean` blocks are also audited,
  and which is then built in its copy in this run, rendered and checked for the anchors and rows
  it must define and for a rule ID in its prose that is not a link to its rule page. -/
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

/-- The rendered HTML files below `root`, each by its path below it with its text. -/
private def renderedHtml (root : FilePath) : IO (List (String × String)) := do
  let components := root.normalize.components
  (← Regula.Filesystem.Construction.walkDirectory root).toList.filterMapM fun path => do
    if path.extension != some "html" then return none
    let relative := "/".intercalate (path.normalize.components.drop components.length)
    return some (relative, ← IO.FS.readFile path)

/-- Build the Verso library in the isolated copy, where every `lean` block is elaborated where it
is written by the library's own code block. The copy's library sources and Verso package inputs
must be exactly the audited and linked ones (`linked`), and the Verso package must pin every Git
dependency it shares with a package it requires by path at the same revision
(`Documentation.sharedPinMismatch`).

The pin check reads the original Verso package at `repo`, not the copy, since it concerns the
audited project's configuration. The copy's generated overrides file (`Lake.copyProject`, from
`Lake.relocateDependencies`) makes each dependency of the accepted project a path entry, so on the
copy the check would compare no Git pin of the accepted project. The original holds each package's
own manifest and overrides file as a build in its directory reads them. The capture comparison
binds the inputs of the Verso package and of the other local packages, and acceptance's source
binding (`SourceBinding.configuration`) binds the accepted project's overrides file. -/
private def prepareVerso (repo copy : FilePath) (verso : VersoPackage)
    (linked : Array RegulaPolicy.SourceSnapshot) : IO (Option String) := do
  let package := copy / verso.dir.toString
  let versoDir := repo / verso.dir.toString
  if let some mismatch ← sharedPinMismatch versoDir then
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
  let failure ← timedPhase "Verso documentation build" <|
    Lake.buildDocumentation package
      #[.library (Manifest.targetSpelling verso.library), .executable verso.render] "fresh"
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
`Regula.checklistRows`, in order (`Regula.Site.rowsMismatch`); each cited section's source must be
a module of the library; and every rule ID in the prose of a rendered page must be a link to its
rule page, relative to the rendered root (`Regula.Prose.htmlErrors`). -/
private def renderVerso (repo copy scratch : FilePath) (verso : VersoPackage)
    (linked : Array RegulaPolicy.SourceSnapshot) : IO (Option String) := do
  let package := copy / verso.dir.toString
  let library ← captureVerso { verso with dir := repo / verso.dir.toString }
  let output := scratch / "verso-render"
  -- `prepareVerso` built the renderer without Lake's artifact cache; `lake exe` would build it
  -- again in a workspace that uses the cache.
  let rendered ← timedPhase "Verso documentation rendering" <|
    Lake.runBuiltExecutable package verso.render #["--output", output.toString]
  unless rendered.succeeded do
    return some s!"Verso rendering failed ({rendered.exitCode}): {rendered.output}"
  let html := output / "html-multi"
  let htmlFiles ← renderedHtml html
  let pages := htmlFiles.map fun (path, source) => Regula.Site.Page.ofHtml path source
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
  let bare := htmlFiles.flatMap fun (path, source) => Regula.Prose.htmlErrors "" path source
  unless bare.isEmpty do
    return some ("rule IDs in the rendered prose are not links to their rule pages:\n" ++
      "\n".intercalate bare)
  return none

/-- The module path (`AcceptanceLink.modulePath`) of each root-package module that the claimed
build of `copy` compiles: the modules of the claimed targets of `manifest`, as `inventory` names
them, and the modules they import transitively, as Lake's `transImports` facet reports them in the
workspace of `copy` (`Lake.moduleImports`, which builds nothing). `none` when Lake reports none. A
claimed target that `inventory` does not name adds no module, so its modules are compiled in the
copy. -/
private def claimedClosure (copy : FilePath) (inventory : Lake.SurfaceInventory)
    (manifest : Manifest) : IO (Option (List String)) := do
  let roots := (Lake.claimedTargets manifest).toList.flatMap fun
    | .library spelling =>
        ((inventory.libraries.find? (·.library == spelling)).map (·.modules.toList)).getD []
    | .executable spelling =>
        ((inventory.executables.find? (·.executable == spelling)).map ([·.root])).getD []
    | .moduleArtifacts name => [name]
  let some imports ← Workspace.withRootWorkspace copy fun ws =>
      Lake.moduleImports ws roots.toArray
    | return none
  let package := inventory.moduleSources.map (·.1)
  let closure := (roots ++ imports.toList.flatMap (·.2.toList)).filter package.contains
  return some (closure.map AcceptanceLink.modulePath).eraseDups

/-- Run one documentation fence audit and return its exit code. In an isolated copy of the
project, which holds no build output before any placement, it builds the claimed surfaces; with
`--verso` it then builds the Verso library there, whose workspace every fence then elaborates in;
it compiles every Lean fence below the documentation root and, with `--verso`, every `lean` block
of the library, then renders the library and checks its anchors, checklist rows and rule-ID links.
With `--acceptance-link`, it first requires the inputs to equal the accepted ones
(`AcceptanceLink.require`), so a missing link, or one that is not accepted, refuses at once, before any build. It then places the first acceptance
step's build output of the modules its claimed build compiles (`claimedClosure`) in the copy before
its build when `BuildReuse.reuse` accepts the link's record of it. Each compiled artifact of the
root package that the fences read was compiled from files equal to those of this copy: by that
step, in a copy that held no earlier build output (`BuildReuse.reuse_iff`), or in this run, against
artifacts of these two kinds. Its output tells whether that step's build was placed, not which build
compiled each artifact. -/
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
    let copied ← Lake.copyProject repo (scratch / "project") scratch
    let copy := copied.project
    let manifestPath := options.manifest.map (resolve repo) |>.getD (Manifest.defaultPath copy)
    let configuration ← SourceBinding.configuration copy manifestPath
    let outcome ← SourceBinding.withUnchanged #[] configuration do
      let inventory ← Lake.checkCopiedWorkspace copied.root (some copied.selection)
        (← Lake.surfaceInventory copy)
      let manifest ← Manifest.loadFor manifestPath inventory
      let sources ← SourceBinding.capture inventory.moduleSources
      let dependencies ← Snapshot.dependencies inventory
      -- A linked run audits only the inputs ordinary acceptance already accepted. It places
      -- that step's build output of the modules its claimed build compiles in its copy only
      -- when `BuildReuse.reuse` accepts the link's record of it; otherwise the copy keeps no
      -- build output (`AcceptanceLink.placeRetained`).
      let placed ← match options.acceptanceLink.map (resolve repo) with
        | none => pure (.error "no acceptance link was given")
        | some link => do
          let digest ← AcceptanceLink.identity scratch copy copied.root docsRoot sources
              configuration dependencies linked
          AcceptanceLink.require link digest
          IO.println
              s!"acceptance link: documentation inputs equal the accepted ordinary inputs ({digest})"
          let targets := (Lake.claimedTargets manifest).toList.map fun
            | .library spelling | .executable spelling => spelling
            | .moduleArtifacts name => s!"+{name}"
          let modules := inventory.moduleSources.toList.map (AcceptanceLink.modulePath ·.1)
          match ← timedPhase "claimed module closure" (claimedClosure copy inventory manifest) with
          | none => pure (.error "Lake did not report the imports of the claimed modules")
          | some closure =>
            timedPhase "retained build placement" <|
              AcceptanceLink.placeRetained repo copy scratch link digest targets modules closure
      -- After that placement, which requires the copy to hold no `.lake/build`.
      copied.placeObservers
      SourceBinding.withUnchanged sources configuration do
        SourceBinding.configurationUnchanged configuration
        let (buildProcess, buildResult) ← Lake.buildCheckedObservation copy
            (Lake.claimedTargets manifest) "fresh"
        SourceBinding.unchanged sources
        SourceBinding.configurationUnchanged configuration
        if let some lines := buildResult then
          for line in lines do IO.println s!"    {line}"
          return 1
        IO.println <| match placed with
          | .ok count => s!"claimed surface built from the first acceptance step's fresh build: \
              {count} files of it, those of the modules the claimed build compiles, placed in \
              this copy, each with the SHA-256 the acceptance link records, every file of this \
              copy outside .lake equal to that step's copy; Lake compiled here what its traces \
              required, warning-free"
          | .error reason => s!"claimed surface built fresh in this run, in a copy with no \
              earlier build output ({reason})"
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
        if let some requested := options.verso then
          if let some failure ← renderVerso repo copy scratch requested linked then
            IO.println s!"FAIL: Verso documentation {requested.library}: {failure}"
            return 1
          Documentation.Sources.checkLinked ⟨docsRoot, verso⟩ repo linked
          SourceBinding.unchanged sources
          IO.println s!"Verso documentation {requested.library}: built in this copy in this run \
            (every `lean` block elaborated where it is written), rendered, defines every anchor \
            the rule registry and the documentation link, its checklist rows are exactly \
            Regula.checklistRows, and every rule ID in the rendered prose `Regula.Prose` reads \
            links to its rule page"
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

/-- Initialize the Lean search path, then `run`, reporting any escaping error as `FAIL` with exit
code 1. -/
unsafe def docFenceAuditMain (args : List String) : IO UInt32 := do
  try
    Regula.Checker.initializeLeanSearchPath
    Regula.Checker.DocFenceAudit.run args
  catch error =>
    IO.eprintln s!"FAIL: {error}"
    return 1

/-- The refusal of the audit in a process without Lean's task manager
(`Regula.TaskManager.guard`): its arguments name no result destination, so it marks none, and it
returns 1. -/
def refuseDocFenceAudit (_reason : String) (_args : List String) : IO UInt32 :=
  pure 1

/-- The `docFenceAudit` executable: `docFenceAuditMain` on the command-line arguments. A process
without Lean's task manager is refused before the audit starts, with exit code 1
(`Regula.TaskManager.guard`). -/
unsafe def main : List String → IO UInt32 :=
  Regula.TaskManager.guard "docFenceAudit" refuseDocFenceAudit docFenceAuditMain

-- The removals and the writes that the compiled code of `main`, and of the initializers of the
-- modules it links, reaches are those of the filesystem observer and those that
-- `Regula.Removal.sharedPairs` lists, and those named here, each by the declaration of a source
-- that makes it: the build of this module fails otherwise, and when a name here admits no call
-- (`Regula.Removal.checkProgram`).
run_cmd Regula.Removal.checkProgram (named := [
  -- The build output of the first acceptance step, placed in the copy of the documentation step.
  (``Regula.Checker.AcceptanceLink.placeRetained, ``IO.FS.createDirAll),
  (``Regula.Checker.AcceptanceLink.placeRetained, ``IO.FS.writeBinFile)])

-- A program that needs Lean's task manager starts through its guard (`Regula.TaskManager.guard`),
-- and its refusal needs none: the build of this module fails otherwise
-- (`Regula.TaskManagerCheck.checkProgram`).
run_cmd Regula.TaskManagerCheck.checkProgram
