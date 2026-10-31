/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Lake.Toml.Data.Value
public import Lean.Elab.Import
public import Lean.Parser.Module
public import Regula.Language
public import Regula.Load
import Regula.RuleId

/-!
# The reader of the language check

What fills `Regula.Language.Reading` from a project before anything of it is compiled, and what runs the
build after it. It is in the default target `RegulaChecker`, so a full verdict on Regula reads it. It takes
what calls Lake as arguments (`LakeCalls`, which `Regula.Workspace` fills).

The full gate is `lake exe lint PROFILE full DIR`, started from a checkout of Regula itself. So the Lake
that starts it loads Regula's configuration and none of the project's, and the checker's program was built
without the project. `startedOutside` refuses any other start, such as `lake lint -- full DIR` in the
project.

**Every Lake call and child process of the gate works in a tree the checker made for this run** (`tree`), and
none works in the project's directory. The tree holds only what the checker read itself, and it writes the
same text it parsed, so what is compiled is what was read. A name, a link or a file of the project can then
select no path outside the tree, whatever Lake derives at this or a later version. The project's own directory
is read and never written, and its `.lake`, its manifest and every other file of it are not read at all.

It reads, in this order, and stops at the first refusal:

- The start from outside.
- `lean-toolchain`, `lakefile.lean` by name, and `lakefile.toml`, which it writes to the tree. `lakefile.toml`
  goes through Lake's own TOML parser, as a list of key paths. A key with the root `require` stops the reading
  here, with only the proof verdict left: the checker runs no Lake call on such a project.
- The root package, through Lake's load of the tree's configuration alone (`Lake.loadWorkspaceRoot`), which
  resolves no dependency and lists no directory: its source directories, its libraries' and executables' names,
  and whether each `globs` entry of each library is a single module. Each source directory must lie below the
  tree (`treeRelative`), and each `globs` entry must be a single module, because the tree holds no source yet.
- The modules of the default targets, with the files Lake names for them in the tree.
- Each module those reach, by its header, through Lean's `parseHeader`. A name outside `closedModuleName` is
  unread before any path is built from it. A root is the file of its own `Module`, and a root whose name Lake's
  import resolution gives another file for is unread. An import is the file `Lake.Workspace.findModule?` gives,
  as Lake's build resolves it (`Lake/Build/Module.lean:37`), or else a module of the toolchain's own library,
  whose `.olean` must lie below that library, and an import of a default executable's root that no library holds
  is unread. The same relative path of the project is read if it is, by its real path, exactly itself, so a link
  at any depth leaves a file unread, and no name found outside the project is printed.
- Each file's commands, through Lean's `parseCommand`, with the context that the specification's H1 states: an
  environment of the toolchain modules the file sees, no options, no namespace and no open declaration.

`MathlibReached` is a test of the name's root, on the modules `reached` holds, so a module whose root is
`Mathlib` is recorded and not read. No `.olean` file of the project or of a dependency is loaded. Only the
toolchain's own parsers run.
-/

public section

namespace Regula.Reader

open Lean (Name Syntax Environment Import MessageLog)
open Lean.Parser (InputContext ModuleParserState mkInputContext parseHeader parseCommand
  isTerminalCommand)
open System (FilePath)
open Regula.Language

/-- What the reader needs from Lake's load of the root package's configuration. -/
structure Root where
  /-- The source directories that the configuration names, in the tree: the package's, each library's and
  each executable's. -/
  sourceDirs : List FilePath
  /-- Each library, with whether every entry of its `globs` is a single module. -/
  libraries : List (Name × Bool)
  /-- The modules of the default targets, each with the file Lake names for it in the tree. Lake lists a
  directory for this unless every `globs` entry is a single module, so `readProject` calls it only after that
  test. -/
  modules : IO (List (Name × FilePath))
  /-- The names of the package's libraries and executables, which Lake joins onto its output directories. -/
  targets : List Name
  /-- The file of a module, by Lake's own resolution of an import. -/
  resolve : Name → Option FilePath
  /-- The toolchain's library directories. -/
  toolchain : List FilePath

/-- The file of a module, given the `modules` of the default targets: a root's own, and otherwise the one
Lake's import resolution gives. `configUnread` and `importedExecutableRoots` leave unread each case where a
root's own file is not the file of that name that Lake compiles or that an import names. -/
def Root.fileOf (root : Root) (modules : List (Name × FilePath)) (m : Name) : Option FilePath :=
  match modules.lookup m with
  | some file => some file
  | none => root.resolve m

/-- What the reader asks of Lake, which `Regula.Workspace` fills, because a constant that calls Lake's load
depends on axioms that no profile admits. -/
structure LakeCalls where
  /-- The `lake` program of the toolchain. -/
  program : IO FilePath
  /-- The library directory of that Lake. -/
  libDir : IO FilePath
  /-- Lake's TOML parser. -/
  parseToml : InputContext → IO Lake.Toml.Table
  /-- Lake's load of the root package's configuration in the tree, with no manifest and no dependency. It
  lists no directory. -/
  loadRoot : FilePath → IO Root

/-- The key paths of a TOML table: each key whose value is neither a table nor an array that holds one,
and each key of each table and array of tables under it. A table with no key gives its own key, so an
empty table, in any form, is not lost. `fuel` bounds the depth; a table deeper than that gives the key
`«too deep»`, which no table holds. -/
def keysOf (fuel : Nat) (pre : Name) (t : Lake.Toml.Table) : List Name :=
  match fuel with
  | 0 => [pre ++ `«too deep»]
  | fuel + 1 =>
    t.items.toList.flatMap fun (k, v) =>
      let key := pre ++ k
      let under (sub : Lake.Toml.Table) : List Name :=
        if sub.items.isEmpty then [key] else keysOf fuel key sub
      match v with
      | .table _ sub => under sub
      | .array _ xs =>
        let tables := xs.toList.filterMap fun
          | .table _ sub => some sub
          | _ => none
        if tables.isEmpty then [key] else tables.flatMap under
      | _ => [key]

/-- The refusal of everything that follows: what was read of the configuration, and why reading stopped.
-/
def stopped (toolchainFile : Option String) (leanConfig : Bool) (keys : List Name)
    (why : Option String) : Reading :=
  { outside := true, toolchainFile, leanConfig, configKeys := keys, openPaths := [], roots := [],
    reached := [], files := [], unread := why.toList.map (`config, ·) }

/-- The modules a file's parser sees, read from its header: the imports `importModulesCore` loads data
for (`Lean/Environment.lean:2108-2190` at v4.35.0). In a `module` file that is each direct import, and
through it each `public` import. `todo` starts as the file's direct imports. The project's own modules are
followed by their headers, since they have no `.olean`, each once (`seen`), so a project whose imports
form many paths to one module takes no longer for it. The search stops at a module of the toolchain, whose
own closure Lean follows. `fuel` bounds the names taken from `todo`: the direct imports and the imports of
each header together suffice, so it does not run out. -/
def visibleToolchain (headers : Name → Option (Array Import)) (isToolchain : Name → Bool)
    (todo seen : List Name) (fuel : Nat) : List Name :=
  match fuel, todo with
  | 0, _ => []
  | _, [] => []
  | fuel + 1, m :: rest =>
    if isToolchain m then
      m :: visibleToolchain headers isToolchain rest seen fuel
    else if seen.contains m then
      visibleToolchain headers isToolchain rest seen fuel
    else
      let next := ((headers m).getD #[]).toList.filter (·.isExported) |>.map (·.module)
      visibleToolchain headers isToolchain (next ++ rest) (m :: seen) fuel

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

/-- An error unless `path` is, by its real path, exactly itself at or below the directory `project`, which is
itself a real path (`Regula.Load.exactBelow`). So it crosses no link at any depth, and an absolute path
outside the project fails. The error names `path` and never where it leads. -/
def requireExactPath (project path : FilePath) : IO Unit := do
  unless Regula.Load.exactBelow project path (← IO.FS.realPath path) do
    throw (IO.userError s!"{path} is not, by its real path, this same path below the project")

/-- The text of a file that `requireExactPath` admits, or an error. -/
def readExact (project path : FilePath) : IO String := do
  requireExactPath project path
  IO.FS.readFile path

/-- `parts` joined below a directory. -/
def joinParts (dir : FilePath) (parts : List String) : FilePath :=
  parts.foldl (fun d p => d.join (FilePath.mk p)) dir

/-- Write `text` to a file of the tree, making its directories. -/
def writeInTree (path : FilePath) (text : String) : IO Unit := do
  if let some dir := path.parent then
    IO.FS.createDirAll dir
  IO.FS.writeFile path text

/-- Read the file of the project that lies at the same relative path as `path` in the tree, and write the
same text to `path`. Refuses a `path` that `treeRelative` refuses, before any path of the project is built
from it. -/
def copyToTree (project tree path : FilePath) : IO String := do
  let some rel := treeRelative (Regula.Load.exactParts tree) (Regula.Load.exactParts path)
    | throw (IO.userError s!"{path} does not lie below the checker's tree")
  let text ← readExact project (joinParts project rel)
  writeInTree path text
  return text

/-- Read one module's file through Lean's own header parser, as the frontend does
(`Lean/Elab/Frontend.lean:287`, `Lean/Shell.lean:519`), and copy that text to the tree. -/
def readSource (project tree path : FilePath) : IO Source := do
  let text ← copyToTree project tree path
  let input := mkInputContext text path.toString
  let (header, state, messages) ← parseHeader input
  return { input, header := header.raw, state, messages,
           imports := Lean.Elab.HeaderSyntax.imports header }

/-- Whether the toolchain's library holds the module `m`: Lean finds its `.olean` on the search path, and
its real path lies below one of `dirs`, the real paths of that library's directories. An error is that it
holds no such module. -/
def toolchainOLean (dirs : List FilePath) (m : Name) : IO Unit := do
  let real ← IO.FS.realPath (← Lean.findOLean m)
  unless dirs.any (Regula.Load.below · real) do
    throw (IO.userError s!"its .olean is not below the toolchain's library")

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

/-- Record that the module `m` could not be read. -/
def Walk.leaveUnread (w : Walk) (m : Name) (why : String) : Walk :=
  { w with reached := m :: w.reached, unread := (m, why) :: w.unread }

/-- Follow imports from `todo`, outside the toolchain. `fuel` bounds the modules visited, and running out
is a failure to read. -/
def walk (project tree : FilePath) (root : Root) (modules : List (Name × FilePath)) (dirs : List FilePath)
    (fuel : Nat) (todo : List Name) (w : Walk) : IO Walk := do
  match fuel, todo with
  | _, [] => return w
  | 0, m :: _ => return w.leaveUnread m "the imports reach too many modules"
  | fuel + 1, m :: rest =>
    if w.reached.contains m || w.toolchain.contains m then
      return ← walk project tree root modules dirs fuel rest w
    if !closedModuleName m then
      return ← walk project tree root modules dirs fuel rest
        (w.leaveUnread m "its name is outside the closed domain")
    if m.getRoot == `Mathlib then
      return ← walk project tree root modules dirs fuel rest { w with reached := m :: w.reached }
    match root.fileOf modules m with
    | some path =>
      match ← (readSource project tree path).toBaseIO with
      | .ok s =>
        walk project tree root modules dirs fuel (s.imports.toList.map (·.module) ++ rest)
          { w with reached := m :: w.reached, sources := (m, s) :: w.sources }
      | .error e => walk project tree root modules dirs fuel rest (w.leaveUnread m (toString e))
    | none =>
      match ← (toolchainOLean dirs m).toBaseIO with
      | .ok _ => walk project tree root modules dirs fuel rest { w with toolchain := m :: w.toolchain }
      | .error e =>
        walk project tree root modules dirs fuel rest
          (w.leaveUnread m s!"neither Lake nor the toolchain holds it: {e}")

/-- Whether anything has this name in the file system, a link with no target included. -/
def existsByName (path : FilePath) : IO Bool := do
  match ← path.symlinkMetadata.toBaseIO with
  | .ok _ => return true
  | .error (.noFileOrDirectory ..) => return false
  | .error e => throw e

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
  let direct := s.imports.toList.map (·.module)
  let fuel := direct.length + (sources.map (·.2.imports.size)).sum + 1
  let mods := visibleToolchain headers toolchain.contains direct [] fuel
  let env ← environmentFor enable cache mods
  let (commands, messages) :=
    parseAll env s.input s.state s.messages (s.input.inputString.utf8ByteSize + 1)
  return { module := m, header := s.header, commands,
           parsed := !messages.hasErrors, scopedParsers := scopedParsersOf env }

/-- Whether this checker was started from outside the project at `project`: its program lies outside
it, and the Lake that started it, whose library directory is `lakeLib`, dispatched from the checker's own
package, whose library lies beside its program (`<package>/.lake/build/bin/lint`, and
`<package>/.lake/build/lib/lean`). `dispatchedFrom_iff` states what that test identifies. A project's own
code that ran before this checker could make any program say anything, so this guards the start and is no
defence against that: a verdict is worth what the start from outside gives it. -/
def startedOutside (lakeLib project : FilePath) : IO Bool := do
  let app ← IO.FS.realPath (← IO.appPath)
  let ownLib := app.parent.bind (·.parent) |>.map (· / "lib" / "lean")
  let received ← Regula.Load.receivedLeanPath
  let dispatched := ownLib.any fun lib =>
    Regula.Load.dispatchedFrom lib.toString lakeLib.toString received
  return !Regula.Load.below project app && dispatched

/-- What `lean-toolchain` says, or none, when `readExact` does not read it. -/
def toolchainOf (project : FilePath) : IO (Option String) := do
  match ← (readExact project (project / "lean-toolchain")).toBaseIO with
  | .ok text => return some text.trimAscii.toString
  | .error _ => return none

/-- What the configuration names outside the closed domain of paths, each with its report: a source directory
that does not lie below the tree (`treeRelative`), and a library with a `globs` entry that is not a single
module. Each report names what the configuration states, never what it leads to. -/
def openPathsOf (tree : FilePath) (root : Root) : List String :=
  let inTree (dir : FilePath) :=
    (treeRelative (Regula.Load.exactParts tree) (Regula.Load.exactParts dir)).isSome
  let dirs := (root.sourceDirs.filter (!inTree ·)).eraseDups.map
    fun dir => s!"the source directory {dir} does not lie below the project"
  let globs := (root.libraries.filter (!·.2)).map fun (lib, _) =>
    s!"the library {lib}: a `globs` entry other than a single module needs a directory listing"
  dirs ++ globs

/-- What in the configuration Lake's load gave is unread before any file, given the `modules` of the default
targets: a library's or an executable's name outside the closed domain, which Lake joins onto an output
directory (`LeanExe.file`, `Lake/Config/LeanExe.lean:72`), and a root whose name Lake's import resolution
gives another file for, so that the file an importer compiles is not the file read. -/
def configUnread (root : Root) (modules : List (Name × FilePath)) : List (Name × String) :=
  let names := (root.targets.filter (!closedModuleName ·)).map
    fun n => (n, "this target's name is outside the closed domain")
  let others := modules.filter fun (m, file) =>
    match root.resolve m with
    | some other => other != file
    | none => false
  names ++ others.map fun (m, file) => (m, s!"a library holds this name with a file other than {file}")

/-- The imports in `sources` of a default executable's root, among the `modules` of the default targets, that
no library holds. The file read for that root is not what such an import names: Lake's import resolution
covers libraries alone (`Package.findModule?`, `Lake/Config/Module.lean:58-59`), so it finds a module of that
name elsewhere or none. -/
def importedExecutableRoots (root : Root) (modules : List (Name × FilePath))
    (sources : List (Name × Source)) : List (Name × String) :=
  let imports := (sources.flatMap fun (_, s) => s.imports.toList.map (·.module)).eraseDups
  let executable := imports.filter fun m =>
    (modules.lookup m).isSome && (root.resolve m).isNone
  executable.map fun m => (m, "an import names this executable's root, and no library holds it")

/-- Read the project at `project`, and fill the checker's own `tree` from what is read. -/
def readProject (enable : IO Unit) (calls : LakeCalls) (project tree : FilePath) :
    IO (Reading × List (Name × Source)) := do
  let project ← IO.FS.realPath project
  let tree ← IO.FS.realPath tree
  let outside ← startedOutside (← calls.libDir) project
  let toolchainFile ← toolchainOf project
  unless outside do
    return ({ stopped toolchainFile false [] none with outside := false }, [])
  if ← existsByName (project / "lakefile.lean") then
    return (stopped toolchainFile true [] none, [])
  let text ← match ← (readExact project (project / "lakefile.toml")).toBaseIO with
    | .ok text => pure text
    | .error e => return (stopped toolchainFile false [] (some s!"lakefile.toml: {e}"), [])
  let keys ← match ← (calls.parseToml (mkInputContext text "lakefile.toml")).toBaseIO with
    | .ok table => pure (keysOf 8 .anonymous table)
    | .error _ =>
      return (stopped toolchainFile false [] (some "Lake's TOML parser refused lakefile.toml"), [])
  let start := stopped toolchainFile false keys none
  if !start.configClosed || start.requiresDependency then
    return (start, [])
  writeInTree (tree / "lakefile.toml") text
  writeInTree (tree / "lean-toolchain") leanToolchain
  let root ← calls.loadRoot tree
  let openPaths := openPathsOf tree root
  unless openPaths.isEmpty do
    return ({ start with openPaths }, [])
  let modules ← root.modules
  let roots := modules.map (·.1)
  let failures := configUnread root modules
  unless failures.isEmpty do
    return ({ start with roots, unread := failures }, [])
  -- A module is the file Lake names, or else the toolchain's: no output of the project is on this path.
  Lean.searchPathRef.set root.toolchain
  let dirs ← root.toolchain.mapM IO.FS.realPath
  let w ← walk project tree root modules dirs 1000000 roots {}
  let sources := w.sources.reverse
  let base := { start with
    roots, reached := w.reached.reverse,
    unread := w.unread.reverse ++ importedExecutableRoots root modules sources }
  if !base.readInFull || base.mathlibReached then
    return (base, [])
  let cache ← IO.mkRef []
  let files ← sources.mapM fun (m, s) => readFile enable cache sources w.toolchain m s
  return ({ base with files }, sources)

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
  let paths := r.openPaths.map fun p => s!"{rule} {p}"
  let config := start ++ toolchain ++ paths ++
    (if r.leanConfig then [s!"{rule} lakefile.lean: Lake runs it, so it is refused"] else []) ++
    (r.configKeys.filter fun k => k.getRoot != `require && !configKeyAdmitted k).map
      (fun k => s!"{rule} lakefile.toml: the key {k} is outside the closed set")
  let unread := r.unread.map fun (m, why) => s!"RG2001 {m}: {why}"
  let dependency :=
    if r.requiresDependency then
      ["regula: lakefile.toml has a `require`, and a full verdict needs a project with no dependency"]
    else []
  let mathlib :=
    if r.mathlibReached then ["regula: Mathlib is in the imports, and its code runs when it is imported"]
    else []
  let files : List String := r.files.flatMap fun f =>
    let s? := sources.lookup f.module
    let head :=
      (if f.parsed then [] else [s!"{rule} {f.module}: Lean's parser refused the file"]) ++
      (if moduleFile f.header then [] else [s!"{rule} {f.module}: the file is not a `module` file"])
    head ++ f.offenders.map fun stx =>
      let line := (s?.map (lineOf · stx)).getD 0
      s!"{rule} {f.module}:{line}: {describe stx}"
  config ++ unread ++ dependency ++ mathlib ++ files.take limit

/-- Read the project and give the decision's input with the lines that report it. -/
def read (enable : IO Unit) (calls : LakeCalls) (project tree : String) :
    IO (Reading × List String) := do
  let (r, sources) ← readProject enable calls project tree
  return (r, findingLines r sources 50)

/-- `lake build --wfail` and `lake check` in the checker's `tree`, with the Lake installed beside this Lean,
so that no `lean-toolchain` chooses anything. No inherited search path, and no artifact cache, so that nothing
is restored without being compiled. -/
def buildAndReplay (calls : LakeCalls) (tree : String) : IO Bool := do
  let lake ← calls.program
  let run (args : Array String) : IO Bool := do
    IO.println s!"regula: lake {" ".intercalate args.toList}"
    (← IO.getStdout).flush
    let child ← IO.Process.spawn
      { cmd := lake.toString, args, cwd := some tree, stdin := .null,
        env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none), ("LAKE_ARTIFACT_CACHE", some "false")] }
    return (← child.wait) == 0
  if !(← run #["build", "--wfail"]) then return false
  run (if System.Platform.isOSX then #["check", "--inadvisably-no-sandbox"] else #["check"])

end Regula.Reader
