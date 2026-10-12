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

/-- Fresh source-bound adopter sharing only pinned dependency artifacts. It links the packages
directory of `root` when there is one (`Regula.Filesystem.placeDirectoryLink`) and holds no other
symbolic link (`Regula.Filesystem.requireLinksPlaced`) before a caller runs Lake in it. It is a
Git repository of its own, so `regula`, which it requires from `root`, is a trusted dependency in
a different Git work tree, as an adopter's is. -/
def prepareProject (root project : FilePath) (packageName claim rationale : String) : IO Unit := do
  IO.FS.writeBinFile (project / "lean-toolchain") (← IO.FS.readBinFile (root / "lean-toolchain"))
  IO.FS.writeFile (project / "lakefile.lean")
    s!"import Lake\nopen Lake DSL\npackage {packageName} where\n  leanOptions := #[⟨`autoImplicit, \
      false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`linter.missingDocs, true⟩]\nrequire regula \
      from {toJson root.toString |>.compress}\n@[default_target] lean_lib Example\n"
  writeJson (project / "foundation_manifest.json") (Json.mkObj [
    ("schema-version", toJson (2 : Nat)), ("surfaces", toJson #[Json.mkObj [
      ("library", .str "Example"), ("claim", .str claim), ("execution", .str "checked"),
      ("rationale", .str rationale)]]),
    ("excluded-libraries", toJson (#[] : Array Json)),
    ("excluded-executables", toJson (#[] : Array Json))])
  let manifest ← readJson (root / "lake-manifest.json")
  let packages ← IO.ofExcept (manifest.getObjValAs? (Array Json) "packages")
  let packages := packages.map (·.setObjVal! "inherited" (.bool true)) |>.push (Json.mkObj [
    ("name", .str "regula"), ("scope", .str ""), ("type", .str "path"),
    ("dir", .str root.toString), ("configFile", .str "lakefile.lean"),
    ("manifestFile", .str "lake-manifest.json"), ("inherited", .bool false)])
  writeJson (project / "lake-manifest.json") (manifest.setObjVal! "packages" (toJson packages))
  let links ← Regula.Filesystem.placeDirectoryLink (root / ".lake/packages")
    (project / ".lake/packages")
  let initialized ← run project "git" #["init", "-q"]
  requireChecks [⟨"adopter repository", initialized.exitCode == 0⟩]
  Regula.Filesystem.requireLinksPlaced project links

/-- Core-only adopter for source/evidence controls. No checker dependency is imported
into the observed surface, matching the original standalone qualification path. It holds no
symbolic link (`Regula.Filesystem.requireLinksPlaced`) before a caller runs Lake in it. -/
def prepareCoreProject (root project : FilePath) (packageName claim : String) : IO Unit := do
  IO.FS.writeBinFile (project / "lean-toolchain") (← IO.FS.readBinFile (root / "lean-toolchain"))
  IO.FS.writeFile (project / "lakefile.toml") s!"name = \
    \"{packageName}\"\n[leanOptions]\nautoImplicit = false\nrelaxedAutoImplicit = \
    false\nlinter.missingDocs = true\n[[lean_lib]]\nname = \"Example\"\n"
  let manifest ← readJson (root / "lake-manifest.json")
  writeJson (project / "lake-manifest.json")
    ((manifest.setObjVal! "packages" (toJson (#[] : Array Json))).setObjVal! "name"
        (.str packageName))
  writeJson (project / "foundation_manifest.json") (Json.mkObj [
    ("schema-version", toJson (2 : Nat)), ("surfaces", toJson #[Json.mkObj [
      ("library", .str "Example"), ("claim", .str claim),
      ("rationale", .str "The same fixed mathematical claim in positive and restored phases.")]]),
    ("excluded-libraries", toJson (#[] : Array Json)),
    ("excluded-executables", toJson (#[] : Array Json))])
  IO.FS.createDirAll (project / "docs")
  Regula.Filesystem.requireLinksPlaced project []

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
    let result ← run root "lake" #["build", "--no-build", s!"+{name}"] cleanEnv
    unless result.exitCode == 0 do
      stale := stale.push s!"{name}:\n{result.stdout}{result.stderr}"
  unless stale.isEmpty do
    throw <| IO.userError s!"the workspaces import modules of the root package at {root} that \
      need a build, which their concurrent builds would write into its shared output; build \
      them first: {"\n".intercalate stale.toList}"

/-- The control of `requireRootImportsBuilt`, in a copy below `scratch` of the repository at
`root` (`Lake.copyProject`) given the module artifacts of its build, the files below the root
package's `leanLibDir` and `irDir`: the guard passes on that copy for `sources`, and refuses,
naming it, once the source of the first root module they import (`rootImports`) has changed after
its build. -/
def rootImportsGuardControl (root scratch : FilePath) (sources : Array String) : IO Unit := do
  let copy := scratch / "root-imports-guard"
  let copied ← Regula.Checker.Lake.copyProject root copy copy
  Regula.Checker.Workspace.withRootWorkspace root (scrubSearchPath := true) fun ws => do
    let base := ws.root.dir.normalize.components
    for place in #[ws.root.leanLibDir, ws.root.irDir] do
      let components := place.normalize.components
      unless base.isPrefixOf components && components.length > base.length do
        throw <| IO.userError s!"the build directory {place} is not inside {ws.root.dir}"
      unless ← place.isDir do continue
      for path in ← place.walkDir do
        if ← path.isDir then continue
        let destination :=
          (path.normalize.components.drop base.length).foldl (· / FilePath.mk ·) copy
        if let some parent := destination.parent then IO.FS.createDirAll parent
        IO.FS.writeBinFile destination (← IO.FS.readBinFile path)
  copied.requireLinksPlaced
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
  requireChecks [⟨"result path must be fresh", !(← output.pathExists)⟩]
  let result ← run project (root / ".lake/build/bin/axiomGate").toString
    (#["--project", project.toString] ++ flags ++ #["--json-out", output.toString]) cleanEnv
  return (result, ← readResult output)

end Regula.Qualification
