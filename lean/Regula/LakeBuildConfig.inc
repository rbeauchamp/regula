/-- Recover the build's LoadConfig selectors with Lake's own option parser, using the exact
invocation that Lake carried into the actual workspace. Refuse non-CLI builds that did not
preserve it. This does not start Lake, discover an installation or parse options by hand.
Assumes: Lake v4.34.1 `CLI/Main.lean:154-157,1314-1322` parses options before and after the
command, `:116-130` makes its LoadConfig (`:124` supplies packageOverrides), `:334-338` decodes
--packages, and `Load/Workspace.lean:44` preserves its arguments. The invocation's cwd and
selector files remain unchanged. Lake's private parser is version-pinned; no command dispatcher
is run. The actual workspace supplies Lake's already detected environment. -/
def buildConfig (workspace : _root_.Lake.Workspace) : IO _root_.Lake.LoadConfig := do
  let some args := workspace.lakeArgs?
    | throw <| IO.userError "observer reach check incomplete: actual Lake build configuration is unavailable"
  let parse : _root_.Lake.CliM _root_.Lake.LakeOptions := do
    _root_.Lake.processLeadingOptions _root_.Lake.lakeOption
    let some _ ← _root_.Lake.takeArg?
      | throw <| _root_.Lake.CliError.missingCommand
    _root_.Lake.processLeadingOptions _root_.Lake.lakeOption
    getThe _root_.Lake.LakeOptions
  let parsed ← (parse.run' args.toList |>.run' { args := args.toList }).toBaseIO
  let options ← match parsed with
    | .ok (.ok options) => pure options
    | .ok (.error error) => throw <| IO.userError s!"observer reach check incomplete: {error}"
    | .error code => throw <| IO.userError s!"observer reach check incomplete: Lake option parser exited {code}"
  let some directory ← _root_.Lake.resolvePath? options.rootDir
    | throw <| IO.userError "observer reach check incomplete: Lake root directory is unavailable"
  unless directory == (← IO.FS.realPath workspace.dir) do
    throw <| IO.userError "observer reach check incomplete: invocation does not select the actual Lake workspace"
  return {
    lakeEnv := workspace.lakeEnv, wsDir := directory,
    lakeArgs? := some args, relConfigFile := options.configFile,
    lakeOpts := options.configOpts, packageOverrides := options.packageOverrides,
    reconfigure := options.reconfigure, updateDeps := options.updateDeps,
    updateToolchain := options.updateToolchain }
