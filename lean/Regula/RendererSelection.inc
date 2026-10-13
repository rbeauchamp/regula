/-! # The renderer's build selection

Included by the cold website Lake configuration and the compiled workspace observer.
The shared refusal observes Lake's decoded selectors, never a scan of invocation text.
Configuration and the generated admission record remain trusted committed-build inputs.
-/

open Lean System

/-- The configuration and manifest admitted by the website's current build target. The record
is a build input, not artifact authentication. Its producer and compiler consumer use the same
selector refusal; stable configuration, selector files and record placement remain trusted. -/
structure BuildSelection where
  /-- The actual build's absolute workspace directory. -/
  directory : String
  /-- The package configuration file Lake loaded, relative to that directory. -/
  configFile : String
  /-- The committed manifest's package-relative location. -/
  manifestFile : String
  /-- The admitted configuration keys, each checked against its string reconstruction. -/
  lakeOptions : Array (String × String)
  /-- The decoded CLI package overrides used by the build. -/
  packageOverrides : Array _root_.Lake.PackageEntry
  /-- Whether the actual invocation requested reconfiguration. -/
  reconfigure : Bool
  /-- The committed manifest bytes admitted by the build target. -/
  manifestText : String
  deriving ToJson, FromJson

/-- One refusal for all Lake selector channels. An identical override is still an override.
Assumes: Lake v4.34.1 `Load/Resolve.lean:598-625` overlays workspace and LoadConfig overrides;
`Load/Manifest.lean:300-305` decodes the workspace file, and `Load/Materialize.lean:260-263`
uses the environment's package URL map. Selector inputs remain stable during the build. -/
def requireSelectors (config : _root_.Lake.LoadConfig) (workspace : _root_.Lake.Workspace)
    (manifest : _root_.Lake.Manifest) (exempted : Array Name) : IO Unit := do
  let overrides ← _root_.Lake.Manifest.tryLoadEntries workspace.packageOverridesFile
  for name in exempted do
    unless manifest.packages.any (·.name == name) do
      throw <| IO.userError s!"observer reach check incomplete: exempted dependency {name} is absent from the committed manifest"
    if overrides.any (·.name == name) || config.packageOverrides.any (·.name == name) ||
        (workspace.lakeEnv.pkgUrlMap.find? name).isSome then
      throw <| IO.userError s!"observer reach check incomplete: exempted dependency {name} has an overridden selection; the committed manifest is required"

/-- Admit the actual build selection before any renderer module is built. The actual resolved
workspace is supplied by Lake, rather than reconstructed with empty override inputs.
Assumes: Lake v4.34.1 `Build/Module.lean:550-557,591` awaits and traces library needs before
module processing. The committed Lake configuration installs this target as a renderer need.
Lean v4.34.1 `Lean/Data/Json/FromToJson/Basic.lean:183-187` represents names through strings;
the equality guard refuses configuration keys whose reconstruction differs from the original. -/
def admitBuild (config : _root_.Lake.LoadConfig) (workspace : _root_.Lake.Workspace) :
    IO BuildSelection := do
  let text ← IO.FS.readFile workspace.manifestFile
  let some manifest ← _root_.Lake.Manifest.load? workspace.manifestFile
    | throw <| IO.userError "observer reach check incomplete: missing committed renderer manifest"
  requireSelectors config workspace manifest #[`verso]
  unless (workspace.findPackageByName? `verso).isSome do
    throw <| IO.userError "observer reach check incomplete: exempted dependency verso was not resolved"
  let mut options := #[]
  for (name, value) in config.lakeOpts.toList do
    let spelling := name.toString
    unless spelling.toName == name do
      throw <| IO.userError "observer reach check incomplete: Lake configuration key cannot be serialized losslessly"
    options := options.push (spelling, value)
  return {
    directory := config.wsDir.toString, configFile := workspace.root.relConfigFile.toString,
    manifestFile := workspace.root.relManifestFile.toString,
    lakeOptions := options,
    packageOverrides := config.packageOverrides, reconfigure := config.reconfigure,
    manifestText := text }

/-- Reconstitute exactly the admitted selector fields in the compiler's checked Lake environment.
The build record is a trusted input; this function does not authenticate its producer. -/
def BuildSelection.configuration (selection : BuildSelection) (environment : _root_.Lake.Env) :
    _root_.Lake.LoadConfig := {
    lakeEnv := environment, wsDir := selection.directory,
    relConfigFile := selection.configFile, relManifestFile := selection.manifestFile,
    lakeOpts := selection.lakeOptions.foldl (fun options (name, value) =>
      options.insert name.toName value) {},
    packageOverrides := selection.packageOverrides, reconfigure := selection.reconfigure }

/-- The build artifact that carries the actual admitted selection into renderer elaboration. -/
def selectionFile (directory : FilePath) : FilePath :=
  directory / ".lake" / "build" / "regula-renderer-selection.json"
