import Regula.Qualification.Support
import Regula.StructuralName
import RegulaQualification.Json
import Regula.Checker.Lake

/-! # Disposable adopter project setup

Shared disposable-adopter setup for producer and history controls. Lake's pinned
manifest is reused, not resolved against moving branches. All subprocesses scrub the
calling checkout's Lean paths. This adapter performs trusted IO, not policy inference. Before
the workspaces of a campaign run at once, `requireRootImportsBuilt` refuses when a module of the
root package that they import needs a build. -/
namespace Regula.Qualification
open Lean System RegulaQualification

/-- Remove inherited paths for commands running in isolated adopters. -/
def cleanEnv : Array (String × Option String) := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none)]

/-- A dotted Lean name as result documents write it (`RegistryCodec.printedNameJson`). -/
def nameJson (name : String) : Json := Regula.RegistryCodec.printedNameJson name.toName

/-- Fresh source-bound adopter sharing only pinned dependency artifacts. It is a Git repository
of its own, so `regula`, which it requires from `root`, is a trusted dependency in a different Git
work tree, as an adopter's is. -/
def prepareProject (root project : FilePath) (packageName claim rationale : String) : IO Unit := do
  let toolchain ← Regula.Filesystem.Construction.capture (root / "lean-toolchain") ["lean-toolchain"]
  Regula.Filesystem.construct project (Regula.Filesystem.Construction.layout toolchain)
  Regula.Filesystem.writeFile (project / "lakefile.lean")
    s!"import Lake\nopen Lake DSL\npackage {packageName} where\n  leanOptions := #[⟨`autoImplicit, \
      false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`linter.missingDocs, true⟩]\n  \
      plugins := #[`@regula/RegulaObserver:shared]\nrequire regula from \
      {toJson root.toString |>.compress}\n@[default_target] \
      {Regula.Checker.observedTargetLean .library "Example"}"
  Regula.Filesystem.writeJson (project / "foundation_manifest.json") (Json.mkObj [
    ("schema-version", toJson (2 : Nat)), ("surfaces", toJson #[Json.mkObj [
      ("library", .str "Example"), ("claim", .str claim), ("execution", .str "checked"),
      ("rationale", .str rationale)]]),
    ("excluded-libraries", toJson (#[] : Array Json)),
    ("excluded-executables", toJson (#[] : Array Json))])
  Regula.Checker.Lake.pinAdopter root project
  let initialized ← run project (.stated "git" "Git is the stated repository mechanism") #["init", "-q"]
  requireChecks [⟨"adopter repository", initialized.exitCode == 0⟩]

/-- Core-only adopter for source/evidence controls. No checker module is imported into the
observed surface, matching the original standalone qualification path; the project requires
`regula` from `root` only so that its library loads Regula's elaboration observer as a plugin
(`Regula.Checker.observerPluginToml`), as RG2006 requires, and lists it in `needs`
(`Regula.Checker.observerNeedToml`). -/
def prepareCoreProject (root project : FilePath) (packageName claim : String) : IO Unit := do
  let toolchain ← Regula.Filesystem.Construction.capture (root / "lean-toolchain") ["lean-toolchain"]
  Regula.Filesystem.construct project (Regula.Filesystem.Construction.layout toolchain)
  Regula.Filesystem.writeFile (project / "lakefile.toml") <| s!"name = \"{packageName}\"\n" ++
    Regula.Checker.observerPluginToml ++ Regula.Checker.regulaRequireToml root ++
    "[leanOptions]\nautoImplicit = false\nrelaxedAutoImplicit = false\n" ++
    "linter.missingDocs = true\n" ++
    Regula.Checker.observedTargetToml .library "Example"
  let manifest ← IO.ofExcept <| Json.parse (← Regula.Filesystem.readFile (root / "lake-manifest.json"))
  let packages := toJson #[Regula.Checker.regulaManifestEntry root]
  Regula.Filesystem.writeJson (project / "lake-manifest.json")
    ((manifest.setObjVal! "packages" packages).setObjVal! "name" (.str packageName))
  Regula.Filesystem.writeJson (project / "foundation_manifest.json") (Json.mkObj [
    ("schema-version", toJson (2 : Nat)), ("surfaces", toJson #[Json.mkObj [
      ("library", .str "Example"), ("claim", .str claim),
      ("rationale", .str "The same fixed mathematical claim in positive and restored phases.")]]),
    ("excluded-libraries", toJson (#[] : Array Json)),
    ("excluded-executables", toJson (#[] : Array Json))])
  IO.FS.createDirAll (project / "docs")

/-- Delete only this owned scratch project's build output before a restored control. -/
def clearBuild (project : FilePath) : IO Unit := do
  Regula.Filesystem.removePath .directory (project / ".lake/build")

/-- The modules of the root package of the workspace at `root` that the headers of `sources`
import, each with its source file: Lean's header parser reads each header (`Lean.parseImports'`),
and Lake's own lookup (`Workspace.findModule?`), which a build of the importing module uses,
resolves each import; the imports it resolves to another package's module or to none are not
returned. -/
def rootImports (root : FilePath) (sources : Array String) : IO (Array (Name × FilePath)) := do
  let mut imports : Array Name := #[]
  for source in sources do
    for i in (← Lean.parseImports' source "<workspace source>").imports do
      unless imports.contains i.module do imports := imports.push i.module
  Regula.Checker.Workspace.withRootWorkspace root (scrubSearchPath := true) fun ws =>
    return imports.filterMap fun name =>
      ((ws.findModule? name).filter (·.pkg.keyName == ws.root.keyName)).map (name, ·.leanFile)

/-- Refuse to let workspaces whose sources are `sources` run at once, when a module of the root
package that they import (`rootImports`) needs a build. For each such module, Lake's own up-to-date
check, `lake build --no-build +MODULE` in `root`, checks every job of the module's default facet
and of its import closure, builds nothing, and must exit 0. The refusal names each module that
fails it, with Lake's output, which names the jobs that need a build. -/
def requireRootImportsBuilt (root : FilePath) (sources : Array String) : IO Unit := do
  let mut stale : Array String := #[]
  for (name, _) in ← rootImports root sources do
    let result ← run root (.toolchain .lake) #["build", "--no-build", s!"+{name}"] cleanEnv
    unless result.exitCode == 0 do
      stale := stale.push s!"{name}:\n{result.stdout}{result.stderr}"
  unless stale.isEmpty do
    throw <| IO.userError s!"the workspaces import modules of the root package at {root} that \
      need a build, which their concurrent builds would write into its shared output; build \
      them first: {"\n".intercalate stale.toList}"

/-- The control of `requireRootImportsBuilt`, in a copy below `scratch` of the repository at
`root` (`Lake.copyProject`) given the module artifacts of its build, the files below the root
package's `leanLibDir` and `irDir` and the files in its `sharedLibDir`: the guard passes on that
copy for `sources`, and refuses, naming it, once the source of the first root module they import
(`rootImports`) has changed after its build. -/
def rootImportsGuardControl (root scratch : FilePath) (sources : Array String) : IO Unit := do
  let copy := scratch / "root-imports-guard"
  discard <| Regula.Checker.Lake.copyProject root copy copy
  Regula.Checker.Workspace.withRootWorkspace root (scrubSearchPath := true) fun ws => do
    let base := ws.root.dir.normalize.components
    -- Of the shared library directory, only its own files: the elaboration observer's library,
    -- which the `needs` entry of each target builds before its modules (`Lake.isObserverNeed`).
    for (place, below) in #[(ws.root.leanLibDir, true), (ws.root.irDir, true),
        (ws.root.sharedLibDir, false)] do
      let components := place.normalize.components
      unless base.isPrefixOf components && components.length > base.length do
        throw <| IO.userError s!"the build directory {place} is not inside {ws.root.dir}"
      unless ← Regula.Filesystem.isDirectory place do continue
      let destination := Regula.Filesystem.Construction.location copy
        (components.drop base.length)
      if below then
        let some parent := destination.parent | throw <| IO.userError "build copy has no parent"
        Regula.Filesystem.Construction.ensureDirectory 4096 parent
        discard <| Regula.Filesystem.copy place destination
      else
        -- The directory holds `leanLibDir`, already copied; its own files join it one by one.
        Regula.Filesystem.Construction.ensureDirectory 4096 destination
        for entry in ← Regula.Filesystem.Construction.listDirectory place do
          unless ← Regula.Filesystem.isDirectory entry.path do
            Regula.Filesystem.copyFile entry.path (destination / entry.fileName) 0o755
  requireRootImportsBuilt copy sources
  let some (name, file) := (← rootImports copy sources)[0]?
    | throw <| IO.userError "the guard control's sources import no module of the root package"
  IO.FS.writeFile file ((← IO.FS.readFile file) ++ "\n")
  let refusal : Option String ← try
      requireRootImportsBuilt copy sources
      pure none
    catch error => pure (some error.toString)
  requireChecks [⟨s!"the guard refuses the changed root module {name}, naming it",
    refusal.any (·.contains s!"{name}:")⟩]
  IO.println s!"root-import guard: unchanged copy PASS, changed {name} refused PASS"

/-- Require a new result path and run the actual public checker. -/
def observeProject (root project output : FilePath) (flags : Array String) : IO
    (IO.Process.Output × Json) := do
  requireChecks [⟨"result path must be fresh", !(← Regula.Filesystem.isPresent output)⟩]
  let result ← run project (.stated (root / ".lake/build/bin/axiomGate").toString "The caller selects this resolved non-toolchain executable")
    (#["--project", project.toString] ++ flags ++ #["--json-out", output.toString]) cleanEnv
  return (result, ← readResult output)

end Regula.Qualification
