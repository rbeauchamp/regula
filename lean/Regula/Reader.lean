/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Lake.Load.Workspace
public import Lake.Toml.Load
public import Lake.Load.Manifest
import Lake.Load.Materialize
public import Lean.Elab.Import
public import Lean.Parser.Module
public import Regula.Workspace
public import Regula.Language
import Regula.RuleId

/-!
# The reader of the language check

What fills `Regula.Language.Reading` from a project before anything of it is compiled, and what runs the
build after it. This module is in the library `Regula`, which is no default target, because it calls
Lake (`Regula.Workspace`).

The full gate is `lake exe lint PROFILE full DIR`, started from a checkout of Regula itself. So the Lake
that starts it loads Regula's configuration and none of the project's, and the checker's program was built
without the project. `startedOutside` refuses any other start, such as `lake lint -- full DIR` in the
project.

It reads the project at `DIR` in this order, and stops at the first refusal, so that nothing of the project
runs and no Lake load of the project happens before what it would run has been read:

- `.lake`: anything there is a planted build, package or checker, and it stops the reading.
- `lean-toolchain`, `lakefile.lean` and `lakefile.toml`, each by name. Lake prefers `lakefile.lean` and
  runs it (`Lake/Load/Package.lean:109-117` at v4.35.0). `lakefile.toml` goes through Lake's own TOML
  parser, as a list of key paths.
- `lake-manifest.json`, through Lake's reader. Each package is fetched by Lake's own
  `PackageEntry.materialize`, which clones it and runs nothing of it (`Lake/Load/Materialize.lean:267-293`),
  and then its configuration is read by name. A package whose configuration is code stops the reading
  here, with only the proof verdict left, because a Lake load would run it.
- The workspace, through Lake's load (`Regula.Load.loadWorkspace`), and the modules of the default targets.
- Each module those reach, by its header, through Lean's `parseHeader`. A module is the file Lake names
  for it, or else a module of the toolchain's own library. No file is found otherwise.
- Each file's commands, through Lean's `parseCommand`, with the context that the specification's H1
  states: an environment of the toolchain modules the file sees, no options, no namespace and no open
  declaration.

No `.olean` file of the project or of a dependency is loaded. Only the toolchain's own parsers run.
-/

public section

namespace Regula.Reader

open Lean (Name Syntax Environment Import MessageLog)
open Lean.Parser (InputContext ModuleParserState mkInputContext parseHeader parseCommand
  isTerminalCommand)
open System (FilePath)
open Regula.Language

/-- The key paths of a TOML table: each key whose value is not a table, and each key of each table and
array of tables under it. `fuel` bounds the depth; a table deeper than that gives the key `«too deep»`,
which no table holds. -/
def keysOf (fuel : Nat) (pre : Name) (t : Lake.Toml.Table) : List Name :=
  match fuel with
  | 0 => [pre ++ `«too deep»]
  | fuel + 1 =>
    t.items.toList.flatMap fun (k, v) =>
      let key := pre ++ k
      match v with
      | .table _ sub => keysOf fuel key sub
      | .array _ xs =>
        let tables := xs.toList.filterMap fun
          | .table _ sub => some sub
          | _ => none
        if tables.isEmpty then [key] else tables.flatMap (keysOf fuel key)
      | _ => [key]

/-- The refusal of everything that follows: what was read of the configuration, and why reading stopped.
-/
def stopped (toolchainFile : Option String) (leanConfig : Bool) (keys : List Name)
    (why : Option String) : Reading :=
  { outside := true, toolchainFile, leanConfig, configKeys := keys, packages := [], roots := [],
    reached := [], files := [], unread := why.toList.map (`config, ·), outputs := [] }

/-- The modules a file's parser sees, read from its header: the imports `importModulesCore` loads data
for (`Lean/Environment.lean:2108-2190` at v4.35.0). In a `module` file that is each direct import, and
through it each `public` import. The project's own modules are followed by their headers, since they have
no `.olean`, and the search stops at a module of the toolchain, whose own closure Lean follows. -/
def visibleToolchain (headers : Name → Option (Array Import)) (isToolchain : Name → Bool)
    (imports : Array Import) (fuel : Nat) : List Name :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    imports.toList.flatMap fun i =>
      if isToolchain i.module then [i.module]
      else
        match headers i.module with
        | some next =>
          visibleToolchain headers isToolchain (next.filter (·.isExported)) fuel
        | none => []

/-- The namespaces that hold a scoped parser entry in `env`. -/
def scopedParsersOf (env : Environment) : List Name :=
  (Lean.Parser.parserExtension.ext.getState env).scopedEntries.map.toList.map (·.1)

/-- Each command of a file, parsed with the constant context, up to the parser's end of input. `fuel`
bounds the commands: `parseCommand` consumes at least one character of a file on each call or ends it. -/
def parseAll (env : Environment) (ictx : InputContext) (mps : ModuleParserState)
    (msgs : MessageLog) (fuel : Nat) : List Syntax × MessageLog :=
  match fuel with
  | 0 => ([], msgs)
  | fuel + 1 =>
    let (stx, mps', msgs') := parseCommand ictx { env, options := {} } mps msgs
    if isTerminalCommand stx then ([stx], msgs')
    else
      let (rest, msgs'') := parseAll env ictx mps' msgs' fuel
      (stx :: rest, msgs'')

/-- A file's text and header. -/
structure Source where
  /-- Where Lake says the module's source is. -/
  path : FilePath
  /-- Whether the root package holds it. -/
  inRoot : Bool
  /-- The parser's input. -/
  input : InputContext
  /-- The tree of the header. -/
  header : Syntax
  /-- Where the header ended. -/
  state : ModuleParserState
  /-- The messages of the header. -/
  messages : MessageLog
  /-- The imports the header states. -/
  imports : Array Import

/-- Read one module's file through Lean's own header parser, as the frontend does
(`Lean/Elab/Frontend.lean:287`, `Lean/Shell.lean:519`). -/
def readSource (path : FilePath) (inRoot : Bool) : IO Source := do
  let text ← IO.FS.readFile path
  let input := mkInputContext text path.toString
  let (header, state, messages) ← parseHeader input
  return { path, inRoot, input, header := header.raw, state, messages,
           imports := Lean.Elab.HeaderSyntax.imports header }

/-- The file Lake would compile for the module `m`, with whether the root package holds it. -/
def lakeFile (ws : Lake.Workspace) (m : Name) : Option (FilePath × Bool × Lake.Package) :=
  ws.packages.findSome? fun pkg =>
    (pkg.findTargetModule? m).map fun mod => (mod.leanFile, pkg.baseName == ws.root.baseName, pkg)

/-- What the walk over the imports has found so far. -/
structure Walk where
  /-- The modules reached, the toolchain's excluded, last first. -/
  reached : List Name := []
  /-- The source of each module read. -/
  sources : List (Name × Source) := []
  /-- The toolchain's modules named by an import. -/
  toolchain : List Name := []
  /-- What could not be read. -/
  unread : List (Name × String) := []
  /-- The packages that hold a file read. -/
  holders : List Lake.Package := []

/-- Follow imports from `todo`, outside the toolchain. `fuel` bounds the modules visited, and running out
is a failure to read. -/
def walk (ws : Lake.Workspace) (fuel : Nat) (todo : List Name) (w : Walk) : IO Walk := do
  match fuel, todo with
  | _, [] => return w
  | 0, m :: _ => return { w with unread := (m, "the imports reach too many modules") :: w.unread }
  | fuel + 1, m :: rest =>
    if w.reached.contains m || w.toolchain.contains m then return ← walk ws fuel rest w
    if m.getRoot == `Mathlib then
      return ← walk ws fuel rest { w with reached := m :: w.reached }
    match lakeFile ws m with
    | some (path, inRoot, pkg) =>
      match ← (readSource path inRoot).toBaseIO with
      | .ok s =>
        walk ws fuel (s.imports.toList.map (·.module) ++ rest)
          { w with reached := m :: w.reached, sources := (m, s) :: w.sources,
                   holders := pkg :: w.holders }
      | .error e =>
        walk ws fuel rest
          { w with reached := m :: w.reached, unread := (m, toString e) :: w.unread }
    | none =>
      match ← (Lean.findOLean m).toBaseIO with
      | .ok _ => walk ws fuel rest { w with toolchain := m :: w.toolchain }
      | .error e =>
        walk ws fuel rest
          { w with reached := m :: w.reached,
                   unread := (m, s!"neither Lake nor the toolchain holds it: {e}") :: w.unread }

/-- Every file under `dir`, recursively; nothing when it does not exist. -/
def filesUnder (dir : FilePath) : IO (List String) := do
  unless ← dir.pathExists do return []
  return (← dir.walkDir).toList.map (·.toString)

/-- The parser's environment for a set of toolchain modules, at the level the frontend uses for a
`module` file (`Lean/Elab/Import.lean:141-149`). `enable` is Lean's `enableInitializersExecution`, which
must run before each import (`Lean/ImportingFlag.lean`) and which this module's caller holds because it is
`unsafe`. Each set is imported once. -/
def environmentFor (enable : IO Unit) (cache : IO.Ref (List (List Name × Environment)))
    (mods : List Name) : IO Environment := do
  let key := mods.eraseDups
  if let some env := (← cache.get).lookup key then return env
  enable
  let env ← Lean.importModules (key.toArray.map ({ module := · })) {} (loadExts := true)
    (level := .exported)
  cache.modify ((key, env) :: ·)
  return env

/-- Read the file of a source in the parser's constant context. -/
def readFile (enable : IO Unit) (cache : IO.Ref (List (List Name × Environment)))
    (sources : List (Name × Source)) (toolchain : List Name) (m : Name) (s : Source) :
    IO FileRead := do
  let headers := fun n => (sources.lookup n).map (·.imports)
  let mods := visibleToolchain headers toolchain.contains s.imports (sources.length + 1)
  let env ← environmentFor enable cache mods
  let (commands, messages) :=
    parseAll env s.input s.state s.messages (s.input.inputString.utf8ByteSize + 1)
  return { module := m, inRoot := s.inRoot, header := s.header, commands,
           parsed := !messages.hasErrors, scopedParsers := scopedParsersOf env }

/-- Whether this checker was started from outside the project at `project`: its program lies outside
it, and the Lake that started it dispatched from the checker's own package, whose library lies beside
its program (`<package>/.lake/build/bin/lint`, and `<package>/.lake/build/lib/lean`). `dispatchedFrom_iff`
states what that test identifies. A project's own code that ran before this checker could make any
program say anything, so this guards the start and is no defence against that: a verdict is worth what
the start from outside gives it. -/
def startedOutside (project : FilePath) : IO Bool := do
  let app ← IO.FS.realPath (← IO.appPath)
  let lakeEnv ← Regula.Load.lakeEnvironment
  let ownLib := app.parent.bind (·.parent) |>.map (· / "lib" / "lean")
  let received ← Regula.Load.receivedLeanPath
  let dispatched := ownLib.any fun lib =>
    Regula.Load.dispatchedFrom lib.toString lakeEnv.lake.libDir.toString received
  return !Regula.Load.below project app && dispatched

/-- What `lean-toolchain` says, or none. -/
def toolchainOf (project : FilePath) : IO (Option String) := do
  match ← (IO.FS.readFile (project / "lean-toolchain")).toBaseIO with
  | .ok text => return some text.trimAscii.toString
  | .error _ => return none

/-- Each package of the manifest, fetched by Lake and read by name, with what could not be. Its
packages directory is the default one or nothing is read of it: a manifest that names another makes Lake
take packages from there (`Lake/Load/Resolve.lean:598`). -/
def packagesOf (project : FilePath) (lakeEnv : Lake.Env) :
    IO (List PackageRead × List (Name × String)) := do
  let some manifest ← Lake.Manifest.load? (project / "lake-manifest.json")
    | return ([], [])
  if manifest.packagesDir?.any (·.normalize != Lake.defaultPackagesDir.normalize) then
    return ([], [(`manifest, "it names another packages directory")])
  let reads ← manifest.packages.toList.mapM fun entry => do
    let name := entry.name
    match entry.src with
    | .path .. =>
      return ({ name, fromGit := false, tomlConfig := false : PackageRead }, none)
    | .git .. =>
      let (dep?, log) ← (entry.materialize lakeEnv project Lake.defaultPackagesDir).captureLog
      match dep? with
      | none =>
        let why := "; ".intercalate (log.entries.map (·.message)).toList
        return ({ name, fromGit := true, tomlConfig := false : PackageRead },
          some (name, s!"Lake could not fetch it: {why}"))
      | some dep =>
        let toml := entry.configFile.extension == some "toml" &&
          !(← (dep.pkgDir / "lakefile.lean").pathExists)
        return ({ name, fromGit := true, tomlConfig := toml : PackageRead }, none)
  return (reads.map (·.1), reads.filterMap (·.2))

/-- Read the project at `project`. -/
def readProject (enable : IO Unit) (project : FilePath) :
    IO (Reading × List (Name × Source)) := do
  let project ← IO.FS.realPath project
  let toolchainFile ← toolchainOf project
  unless ← startedOutside project do
    return ({ stopped toolchainFile false [] none with outside := false }, [])
  let planted ← filesUnder (project / ".lake")
  unless planted.isEmpty do
    return ({ stopped toolchainFile false [] none with outputs := planted }, [])
  if ← (project / "lakefile.lean").pathExists then
    return (stopped toolchainFile true [] none, [])
  let tomlFile := project / "lakefile.toml"
  let text ← match ← (IO.FS.readFile tomlFile).toBaseIO with
    | .ok text => pure text
    | .error e => return (stopped toolchainFile false [] (some s!"lakefile.toml: {e}"), [])
  let keys ← match ← (Lake.Toml.loadToml (mkInputContext text "lakefile.toml")).toBaseIO with
    | .ok table => pure (keysOf 8 .anonymous table)
    | .error _ =>
      return (stopped toolchainFile false [] (some "Lake's TOML parser refused lakefile.toml"), [])
  let start := stopped toolchainFile false keys none
  unless start.configClosed do
    return (start, [])
  let lakeEnv ← Regula.Load.lakeEnvironment
  let (packages, failures) ← packagesOf project lakeEnv
  let started := { start with packages, unread := failures }
  unless started.configClosed && started.readInFull && !started.dependencyConfigIsCode do
    return (started, [])
  let ws ← Regula.Load.loadWorkspace project
  let roots := (← Regula.Load.defaultModules ws).toList
  -- A module is the file Lake names, or else the toolchain's: no output of the project is on this path.
  Lean.searchPathRef.set ws.lakeEnv.leanPath
  let w ← walk ws 1000000 roots {}
  let base := { started with roots, reached := w.reached.reverse, unread := w.unread.reverse }
  if base.mathlibReached then
    return (base, [])
  -- A dependency's own build output would stand in for what is read of its files.
  let outputs ← w.holders.flatMapM fun pkg => filesUnder pkg.buildDir
  let cache ← IO.mkRef []
  let sources := w.sources.reverse
  let files ← sources.mapM fun (m, s) => readFile enable cache sources w.toolchain m s
  return ({ base with files, outputs }, sources)

/-- The line of a position in a source. -/
def lineOf (s : Source) (stx : Syntax) : Nat :=
  match stx.getPos? with
  | some p => (s.input.fileMap.toPosition p).line
  | none => 0

/-- What a position is, for a report. -/
def describe : Syntax → String
  | .missing => "a place Lean's parser could not fill"
  | .atom _ v => s!"the token `{v}`"
  | .ident _ _ n _ => s!"the name `{n}`"
  | .node _ k _ => s!"the construct {k}"

/-- The report of what the decision read: one line for each thing that made the reading other than
admitted. At most `limit` lines of the positions. -/
def findingLines (r : Reading) (sources : List (Name × Source)) (limit : Nat) : List String :=
  let rule := Regula.RuleId.language.spelling
  let start :=
    if r.outside then [] else ["RG2001 this checker was built or started by the project's Lake, so it \
      gives no full verdict: from a checkout of Regula, run `lake exe lint PROFILE full DIR`"]
  let toolchain :=
    if r.outside && r.toolchainFile != some leanToolchain then
      [s!"{rule} lean-toolchain: it must say {leanToolchain}"]
    else []
  let config := start ++ toolchain ++
    (if r.leanConfig then [s!"{rule} lakefile.lean: Lake runs it, so it is refused"] else []) ++
    (r.configKeys.filter (!configKeyAdmitted ·)).map
      (fun k => s!"{rule} lakefile.toml: the key {k} is outside the closed set") ++
    (r.packages.filter (!·.fromGit)).map
      (fun p => s!"{rule} {p.name}: a package from a local path is outside the closed set")
  let unread := r.unread.map fun (m, why) => s!"RG2001 {m}: {why}"
  let outputs := r.outputs.take 5 |>.map fun p =>
    s!"RG2001 {p}: this exists, so a build could reuse it without compiling what was read (`lake clean`)"
  let code := (r.packages.filter (!·.tomlConfig)).map
    fun p => s!"regula: the Lake configuration of {p.name} is code, so a build gets only the proof verdict"
  let files : List String := r.files.flatMap fun f =>
    let s? := sources.lookup f.module
    let head :=
      (if f.parsed then [] else [s!"{rule} {f.module}: Lean's parser refused the file"]) ++
      (if moduleFile f.header then [] else [s!"{rule} {f.module}: the file is not a `module` file"])
    head ++ f.offenders.map fun stx =>
      let line := (s?.map (lineOf · stx)).getD 0
      s!"{rule} {f.module}:{line}: {describe stx}"
  config ++ unread ++ outputs ++ code ++ files.take limit

/-- Read the project and give the decision's input with the lines that report it. -/
def read (enable : IO Unit) (project : String) : IO (Reading × List String) := do
  let (r, sources) ← readProject enable project
  return (r, findingLines r sources 50)

/-- `lake build --wfail` and `lake check` in the project, with the Lake installed beside this Lean, so
that the project's `lean-toolchain` chooses nothing. No inherited search path, and no artifact cache, so
that nothing is restored without being compiled. -/
def buildAndReplay (project : String) : IO Bool := do
  let lakeEnv ← Regula.Load.lakeEnvironment
  let run (args : Array String) : IO Bool := do
    IO.println s!"regula: lake {" ".intercalate args.toList}"
    (← IO.getStdout).flush
    let child ← IO.Process.spawn
      { cmd := lakeEnv.lake.lake.toString, args, cwd := some project, stdin := .null,
        env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none), ("LAKE_ARTIFACT_CACHE", some "false")] }
    return (← child.wait) == 0
  if !(← run #["build", "--wfail"]) then return false
  run (if System.Platform.isOSX then #["check", "--inadvisably-no-sandbox"] else #["check"])

end Regula.Reader
