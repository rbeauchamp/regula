/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Regula.Effect
public import Regula.Language
public import Regula.Load
import Regula.RuleId

/-!
# The reader of the language check

What fills `Regula.Language.Reading` from a project before anything of it is compiled, as a program over the
closed operations of `Regula.Effect`. It performs nothing: `specification/RegulaSpecification/Proofs/Reader.lean`
states what the program does for every response, and `Regula.LintMain` runs it.

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

- The start from outside, and that the project and the tree lie apart.
- `lean-toolchain`, `lakefile.lean` by name, and `lakefile.toml`, which it writes to the tree. `lakefile.toml`
  goes through Lake's own TOML parser, as a list of key paths. A key with the root `require` stops the reading
  here, with only the proof verdict left: the checker runs no Lake call on such a project.
- The root package, through Lake's load of the tree's configuration alone (`Lake.loadWorkspaceRoot`), which
  resolves no dependency and lists no directory: its source directories, its libraries' and executables' names,
  and each library's `globs`. Each source directory must lie below the tree (`treeRelative`), and each `globs`
  entry must be a single module, because the tree holds no source yet.
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

open Lean (Name Syntax Import MessageLog)
open Lean.Parser (InputContext ModuleParserState mkInputContext isTerminalCommand)
open System (FilePath)
open Regula.Language
open Regula.Effect

variable {L E : Type}

/-- A program that can stop with a reason. -/
abbrev Attempt (L E α : Type) : Type := ExceptT String (Prog L E) α

/-- An operation that can fail, with its failure as the reason. -/
def attempt {α : Type} (step : Prog L E (Except IO.Error α)) : Attempt L E α :=
  ExceptT.mk do
    match ← step with
    | .ok a => pure (.ok a)
    | .error e => pure (.error (toString e))

/-- Print a line that is no verdict. Two spaces start it, so that no such line can be read as a verdict's, and
a failed print changes nothing the run decides. -/
def say (text : String) : Prog L E Unit := do
  let _ ← Prog.call (.println ("  " ++ text))
  pure ()

/-- Print each line. -/
def sayAll : List String → Prog L E Unit
  | [] => pure ()
  | l :: rest => do
    say l
    sayAll rest

/-- The real path of a path. -/
def realPath (path : FilePath) : Attempt L E FilePath :=
  attempt (Prog.call (.realPath path))

/-- An environment variable that a run needs. -/
def requireEnv (name : String) (why : String) : Attempt L E String :=
  ExceptT.mk do
    match ← (Prog.call (.getEnv name) : Prog L E (Option String)) with
    | some value => pure (.ok value)
    | none => pure (.error why)

/-- The file of a module, given the `modules` of the default targets: a root's own, and otherwise the one
Lake's import resolution gives. `configUnread` and `importedExecutableRoots` leave unread each case where a
root's own file is not the file of that name that Lake compiles or that an import names. -/
def fileOf (root : Root L) (modules : List (Name × FilePath)) (m : Name) : Option FilePath :=
  match modules.lookup m with
  | some file => some file
  | none => root.resolve m

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
for (`Lean/Environment.lean:2108-2190` at v4.35.0). This states Lean's rule, because the project's modules
have no `.olean` that Lean could follow them through; `Sees` is its statement, and H1 holds what is assumed.
In a `module` file that is each direct import, and through it each `public` import. `todo` starts as the file's
direct imports. The project's own modules are followed by their headers, each once (`seen`), so a project whose
imports form many paths to one module takes no longer for it. The search stops at a module of the toolchain,
whose own closure Lean follows. `fuel` bounds the names taken from `todo`, and
`visibleToolchain_sufficient` proves that the bound the reader gives it suffices. -/
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

/-- Each command of a file, parsed with the constant context, up to the parser's end of input. `fuel`
bounds the commands: `parseCommand` consumes at least one character of a file on each call or ends it. -/
def parseAll (input : InputContext) (env : E) (state : ModuleParserState) (messages : MessageLog) :
    Nat → Prog L E (List Syntax × MessageLog)
  | 0 => pure ([], messages)
  | fuel + 1 => do
    let (stx, state', messages') ←
      (Prog.call (.parseCommand input env state messages) :
        Prog L E (Syntax × ModuleParserState × MessageLog))
    if isTerminalCommand stx then
      pure ([stx], messages')
    else
      let (rest, final) ← parseAll input env state' messages' fuel
      pure (stx :: rest, final)

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

/-- The text of a file, if `path` is, by its real path, exactly itself at or below the directory `project`,
which is itself a real path (`Regula.Load.exactBelow`). So it crosses no link at any depth, and an absolute
path outside the project fails. The error names `path` and never where it leads. -/
def readExact (project path : FilePath) : Attempt L E String := do
  let real ← realPath path
  if Regula.Load.exactBelow project path real then
    attempt (Prog.call (.readFile path))
  else
    throw s!"{path} is not, by its real path, this same path below the project"

/-- `parts` joined below a directory. -/
def joinParts (dir : FilePath) (parts : List String) : FilePath :=
  parts.foldl (fun d p => d.join (FilePath.mk p)) dir

/-- Whether a path lies at or below the checker's tree, by `treeRelative`. Every write asks this first, so
no write of a run leaves the tree, whatever a path holds. -/
def inTree (tree path : FilePath) : Bool :=
  (treeRelative (Regula.Load.exactParts tree) (Regula.Load.exactParts path)).isSome

/-- Write `text` to a file of the tree, making its directories. -/
def writeInTree (tree path : FilePath) (text : String) : Attempt L E Unit := do
  unless inTree tree path do
    throw s!"{path} does not lie below the checker's tree"
  if let some dir := path.parent then
    unless inTree tree dir do
      throw s!"{dir} does not lie below the checker's tree"
    attempt (Prog.call (.createDirAll dir))
  attempt (Prog.call (.writeFile path text))

/-- Read the file of the project that lies at the same relative path as `path` in the tree, and write the
same text to `path`. Refuses a `path` that `treeRelative` refuses, before any path of the project is built
from it. -/
def copyToTree (project tree path : FilePath) : Attempt L E String := do
  match treeRelative (Regula.Load.exactParts tree) (Regula.Load.exactParts path) with
  | none => throw s!"{path} does not lie below the checker's tree"
  | some rel =>
    let text ← readExact project (joinParts project rel)
    writeInTree tree path text
    pure text

/-- Read one module's file through Lean's own header parser, as the frontend does
(`Lean/Elab/Frontend.lean:287`, `Lean/Shell.lean:519`), and copy that text to the tree. -/
def readSource (project tree path : FilePath) : Attempt L E Source := do
  let text ← copyToTree project tree path
  let input := mkInputContext text path.toString
  let (header, state, messages, imports) ← attempt (Prog.call (.parseHeader input))
  pure { input, header, state, messages, imports }

/-- Whether the toolchain's library holds the module `m`: Lean finds its `.olean` on the search path, and
its real path lies below one of `dirs`, the real paths of that library's directories. An error is that it
holds no such module. -/
def toolchainOLean (dirs : List FilePath) (m : Name) : Attempt L E Unit := do
  let olean ← attempt (Prog.call (.findOLean m))
  let real ← realPath olean
  unless dirs.any (Regula.Load.below · real) do
    throw "its .olean is not below the toolchain's library"

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
def walk (project tree : FilePath) (root : Root L) (modules : List (Name × FilePath))
    (dirs : List FilePath) : Nat → List Name → Walk → Prog L E Walk
  | _, [], w => pure w
  | 0, m :: _, w => pure (w.leaveUnread m "the imports reach too many modules")
  | fuel + 1, m :: rest, w =>
    if w.reached.contains m || w.toolchain.contains m then
      walk project tree root modules dirs fuel rest w
    else if !closedModuleName m then
      walk project tree root modules dirs fuel rest
        (w.leaveUnread m "its name is outside the closed domain")
    else if m.getRoot == `Mathlib then
      walk project tree root modules dirs fuel rest { w with reached := m :: w.reached }
    else
      match fileOf root modules m with
      | some path => do
        match ← (readSource project tree path).run with
        | .ok s =>
          walk project tree root modules dirs fuel (s.imports.toList.map (·.module) ++ rest)
            { w with reached := m :: w.reached, sources := (m, s) :: w.sources }
        | .error e => walk project tree root modules dirs fuel rest (w.leaveUnread m e)
      | none => do
        match ← (toolchainOLean dirs m).run with
        | .ok _ =>
          walk project tree root modules dirs fuel rest { w with toolchain := m :: w.toolchain }
        | .error e =>
          walk project tree root modules dirs fuel rest
            (w.leaveUnread m s!"neither Lake nor the toolchain holds it: {e}")

/-- Whether anything has this name in the file system, a link with no target included. -/
def existsByName (path : FilePath) : Attempt L E Bool :=
  ExceptT.mk do
    match ← (Prog.call (.symlinkMetadata path) : Prog L E (Except IO.Error IO.FS.Metadata)) with
    | .ok _ => pure (.ok true)
    | .error (.noFileOrDirectory ..) => pure (.ok false)
    | .error e => pure (.error (toString e))

/-- What the imports of Lean's parser gave so far, by the set of modules: each set is imported once. -/
abbrev ParserCache (E : Type) : Type := List (List Name × (E × List Name))

/-- The parser's environment for a set of toolchain modules, with the namespaces that hold a scoped parser
entry in it. -/
def environmentFor (cache : ParserCache E) (mods : List Name) :
    Attempt L E ((E × List Name) × ParserCache E) := do
  let key := mods.eraseDups
  match cache.lookup key with
  | some pair => pure (pair, cache)
  | none =>
    let pair ← attempt (Prog.call (.importForParser key))
    pure (pair, (key, pair) :: cache)

/-- Read the file of a source in the parser's constant context. -/
def parseFile (cache : ParserCache E) (sources : List (Name × Source)) (toolchain : List Name) (m : Name)
    (s : Source) : Attempt L E (FileRead × ParserCache E) := do
  let headers := fun n => (sources.lookup n).map (·.imports)
  let direct := s.imports.toList.map (·.module)
  let fuel := direct.length + (sources.map (·.2.imports.size)).sum + 1
  let mods := visibleToolchain headers toolchain.contains direct [] fuel
  let ((env, scopedParsers), cache') ← environmentFor cache mods
  let (commands, final) ← ExceptT.lift
    (parseAll s.input env s.state s.messages (s.input.inputString.utf8ByteSize + 1))
  pure ({ module := m, header := s.header, commands, parsed := !final.hasErrors, scopedParsers }, cache')

/-- Read each file of `todo`, keeping what the imports of Lean's parser gave. -/
def parseFiles (sources : List (Name × Source)) (toolchain : List Name) (cache : ParserCache E) :
    List (Name × Source) → Attempt L E (List FileRead)
  | [] => pure []
  | (m, s) :: rest => do
    let (file, cache') ← parseFile cache sources toolchain m s
    let files ← parseFiles sources toolchain cache' rest
    pure (file :: files)

/-- Whether this checker was started from outside the project at `project`: its program lies outside
it, and the Lake that started it, whose library directory is `lakeLib`, dispatched from the checker's own
package, whose library lies beside its program (`<package>/.lake/build/bin/lint`, and
`<package>/.lake/build/lib/lean`). `dispatchedFrom_iff` states what that test identifies. A project's own
code that ran before this checker could make any program say anything, so this guards the start and is no
defence against that: a verdict is worth what the start from outside gives it. -/
def startedOutside (lakeLib project : FilePath) : Attempt L E Bool := do
  let app ← attempt (Prog.call .appPath)
  let real ← realPath app
  let received ← requireEnv "LEAN_PATH"
    "LEAN_PATH is not set, so the workspace that Lake dispatched is not known: run the checker with \
      `lake lint` or `lake exe lint`, which set it"
  let leanPath := (System.SearchPath.parse received).map toString
  let ownLib := real.parent.bind (·.parent) |>.map (· / "lib" / "lean")
  let dispatched := ownLib.any fun lib =>
    Regula.Load.dispatchedFrom lib.toString lakeLib.toString leanPath
  pure (!Regula.Load.below project real && dispatched)

/-- What `lean-toolchain` says, or none, when `readExact` does not read it. -/
def toolchainOf (project : FilePath) : Prog L E (Option String) := do
  match ← (readExact project (project / "lean-toolchain")).run with
  | .ok text => pure (some text.trimAscii.toString)
  | .error _ => pure none

/-- What the configuration names outside the closed domain of paths, each with its report: a source directory
that does not lie below the tree (`treeRelative`), and a library with a `globs` entry that is not a single
module. Each report names what the configuration states, never what it leads to. -/
def openPathsOf (tree : FilePath) (root : Root L) : List String :=
  let single : Lake.Glob → Bool
    | .one _ => true
    | _ => false
  let dirs := (root.sourceDirs.filter (!inTree tree ·)).eraseDups.map
    fun dir => s!"the source directory {dir} does not lie below the project"
  let globs := (root.libraries.filter (!·.2.all single)).map fun (lib, _) =>
    s!"the library {lib}: a `globs` entry other than a single module needs a directory listing"
  dirs ++ globs

/-- What in the configuration Lake's load gave is unread before any file, given the `modules` of the default
targets: a library's or an executable's name outside the closed domain, which Lake joins onto an output
directory (`LeanExe.file`, `Lake/Config/LeanExe.lean:72`), and a root whose name Lake's import resolution
gives another file for, so that the file an importer compiles is not the file read. -/
def configUnread (root : Root L) (modules : List (Name × FilePath)) : List (Name × String) :=
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
def importedExecutableRoots (root : Root L) (modules : List (Name × FilePath))
    (sources : List (Name × Source)) : List (Name × String) :=
  let imports := (sources.flatMap fun (_, s) => s.imports.toList.map (·.module)).eraseDups
  let executable := imports.filter fun m =>
    (modules.lookup m).isSome && (root.resolve m).isNone
  executable.map fun m => (m, "an import names this executable's root, and no library holds it")

/-- The modules of the targets `targets` of the root package, with the file Lake compiles for each: each module
of a default library, and the root of each default executable. A default target that is neither builds no
Lean module (`Package.recCollectDefaultModules`, `Lake/Build/Package.lean:45-61` at v4.35.0). Lake lists a
directory for a `globs` entry other than a single module (`Glob.forEachModuleIn`,
`Lake/Config/Glob.lean:53-59`): the reader asks this only after it has tested each entry through
`openPathsOf`, and the plain `lake lint` keeps Lake's own listing. -/
def defaultModules (root : Root L) : List Name → Attempt L E (List (Name × FilePath))
  | [] => pure []
  | target :: targets => do
    let here ← match root.findLib target with
      | some lib => do
        let listed ← attempt (Prog.call (.libModules lib))
        pure (Array.toList listed)
      | none =>
        match root.findExe target with
        | some m => pure [m]
        | none => pure []
    let rest ← defaultModules root targets
    pure (here ++ rest)

/-- The root package that Lake's load gave, or why it gave none. -/
def loaded (what : String) : Except String (Option (Root L) × List String) → Except String (Root L)
  | .error why => .error why
  | .ok (some root, _) => .ok root
  | .ok (none, log) => .error s!"Lake could not load {what}: {"; ".intercalate log}"

/-- The modules that the imports of `modules` reach, each file read, and each file's commands. The search path
holds the toolchain's directories alone, because a module is the file Lake names or else the toolchain's: no
output of the project is on it. -/
def readFiles (project tree : FilePath) (root : Root L) (modules : List (Name × FilePath)) (start : Reading) :
    Attempt L E (Reading × List (Name × Source)) := do
  ExceptT.lift (Prog.call (.setSearchPath root.toolchain))
  let dirs ← root.toolchain.mapM realPath
  let w ← ExceptT.lift (walk project tree root modules dirs 1000000 (modules.map (·.1)) {})
  let sources := w.sources.reverse
  let base := { start with
    roots := modules.map (·.1), reached := w.reached.reverse,
    unread := w.unread.reverse ++ importedExecutableRoots root modules sources }
  if !base.readInFull || base.mathlibReached then
    pure (base, [])
  else
    let files ← parseFiles sources w.toolchain [] sources
    pure ({ base with files }, sources)

/-- The root package through Lake's load of the tree's configuration, the paths it names, and what follows. -/
def readRoot (sysroot : String) (project tree : FilePath) (start : Reading) :
    Attempt L E (Reading × List (Name × Source)) := do
  let root ← ExceptT.mk (Prog.bind (Prog.call (.loadRoot sysroot tree)) fun r =>
    pure (loaded "the configuration" r))
  let openPaths := openPathsOf tree root
  if !openPaths.isEmpty then
    pure ({ start with openPaths }, [])
  else
    let modules ← defaultModules root root.defaultTargets
    let failures := configUnread root modules
    if !failures.isEmpty then
      pure ({ start with roots := modules.map (·.1), unread := failures }, [])
    else
      readFiles project tree root modules start

/-- What a configuration's text says, its copy in the tree, and what follows. -/
def readKeys (sysroot : String) (project tree : FilePath) (toolchainFile : Option String) (text : String) :
    Attempt L E (Reading × List (Name × Source)) := do
  match ← ExceptT.lift (Prog.call (.parseToml (mkInputContext text "lakefile.toml")) :
      Prog L E (Except MessageLog Lake.Toml.Table)) with
  | .error _ =>
    pure (stopped toolchainFile false [] (some "Lake's TOML parser refused lakefile.toml"), [])
  | .ok table =>
    let start := stopped toolchainFile false (keysOf 8 .anonymous table) none
    if !start.configClosed || start.requiresDependency then
      pure (start, [])
    else
      writeInTree tree (tree / "lakefile.toml") text
      writeInTree tree (tree / "lean-toolchain") leanToolchain
      readRoot sysroot project tree start

/-- `lakefile.lean` by its name, `lakefile.toml`, and what follows. -/
def readConfig (sysroot : String) (project tree : FilePath) (toolchainFile : Option String) :
    Attempt L E (Reading × List (Name × Source)) := do
  if ← existsByName (project / "lakefile.lean") then
    pure (stopped toolchainFile true [] none, [])
  else
    match ← ExceptT.lift (readExact project (project / "lakefile.toml")).run with
    | .error e => pure (stopped toolchainFile false [] (some s!"lakefile.toml: {e}"), [])
    | .ok text => readKeys sysroot project tree toolchainFile text

/-- Read the project at `dir`, and fill the checker's own tree at `treeDir` from what is read. -/
def readProject (sysroot : String) (dir treeDir : FilePath) :
    Attempt L E (Reading × List (Name × Source)) := do
  let project ← realPath dir
  let tree ← realPath treeDir
  let (_, lakeLib) ← (ExceptT.lift (Prog.call (.lakeInstall sysroot)) :
    Attempt L E (FilePath × FilePath))
  let outside ← startedOutside lakeLib project
  let toolchainFile ← ExceptT.lift (toolchainOf project)
  if !outside then
    pure ({ stopped toolchainFile false [] none with outside := false }, [])
  else if inTree project tree || inTree tree project then
    pure (stopped toolchainFile false [] (some "the checker's tree and the project do not lie apart"), [])
  else
    readConfig sysroot project tree toolchainFile

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
def read (sysroot : String) (dir treeDir : FilePath) : Attempt L E (Reading × List String) := do
  let (r, sources) ← readProject sysroot dir treeDir
  pure (r, findingLines r sources 50)

end Regula.Reader
