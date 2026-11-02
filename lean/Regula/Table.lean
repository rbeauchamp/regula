/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Lean.Elab.Import
public import Regula.Effect
public import Lean.Util.Path
import Lean.Parser.Extension

/-!
# The one table of effects

`table` answers each operation of `Regula.Effect.Op` by a straight line of calls of Lean or of the operating system's
function as Lean gives it, or by a row of `LakeCalls`, which `Regula.Workspace` fills. A lookup or an import takes its search path as an argument, and its row sets `Lean.searchPathRef` to it first, because `Lean.findOLean` and `Lean.importModules` read that reference and take no path (`Lean/Util/Path.lean:117-118`, `Lean/Environment.lean:2079-2080` at v4.35.0). Nothing here tests a result: a row
passes on what the calls give. `table_rows` in `specification/RegulaSpecification/Proofs/Program.lean` states each row.
-/

public section

namespace Regula.Effect

open Lean (Name Syntax Environment Import MessageLog)
open Lean.Parser (InputContext ModuleParserState)
open System (FilePath)

/-- The rows that call Lake, which `Regula.Workspace` fills, because a constant that calls Lake's load depends on
axioms that no profile admits. -/
structure LakeCalls (L : Type) where
  /-- Lake's TOML parser. -/
  parseToml : InputContext → BaseIO (Except MessageLog Lake.Toml.Table)
  /-- The Lake beside the Lean of a system root: its program and library directory. -/
  lakeInstall : String → BaseIO (FilePath × FilePath)
  /-- Lake's load of a workspace with its dependencies. -/
  loadWorkspace : String → FilePath → BaseIO (Except String (Option (Root L) × List String))
  /-- Lake's load of a root package's `lakefile.toml` alone. -/
  loadRoot : String → FilePath → BaseIO (Except String (Option (Root L) × List String))
  /-- The modules of a library, with the file Lake compiles for each. -/
  libModules : L → BaseIO (Except IO.Error (Array (Name × FilePath)))

/-- The namespaces that hold a scoped parser entry in `env`. -/
def scopedParsersOf (env : Environment) : List Name :=
  (Lean.Parser.parserExtension.ext.getState env).scopedEntries.map.toList.map (·.1)

/-- A Lake command in a directory, with the standard streams of this process and a closed environment: `env -i` starts it with these two variables and no other, so no
variable that a Lake before this checker composed, or that this process inherited, reaches its lookups of a program or a library. `IO.Process.SpawnArgs.inheritEnv := false` would say this
directly, and it ends with a segmentation fault on macOS at v4.35.0. Lake takes `lean` and its own tools from the toolchain's directory, so the search path is only for what it asks of the system, such
as `which` and `git`. Lake's artifact cache is off: nothing is restored without being compiled. -/
def spawnLake (program cwd : FilePath) (args : List String) : IO UInt32 := do
  let child ← IO.Process.spawn
    { cmd := "/usr/bin/env", args := #["-i", "PATH=/usr/bin:/bin", "LAKE_ARTIFACT_CACHE=false", program.toString] ++ args.toArray,
      cwd := some cwd, stdin := .null }
  child.wait

/-- `enable` is Lean's `enableInitializersExecution`, which is `unsafe` and which must run before each import of
Lean's parsers (`Lean/ImportingFlag.lean`), at the level the frontend uses for a `module` file
(`Lean/Elab/Import.lean:141-149`). -/
def importParsers (enable : BaseIO Unit) (modules : List Name) : IO (Environment × List Name) := do
  enable
  let env ← Lean.importModules (modules.toArray.map ({ module := · })) {} (loadExts := true)
    (level := .exported)
  return (env, scopedParsersOf env)

/-- Each operation, by its row. -/
def table {L : Type} (enable : BaseIO Unit) (lake : LakeCalls L) : (o : Op L Environment) → BaseIO (Resp o)
  | .leanVersion => pure (Lean.versionString, Lean.githash)
  | .getEnv name => IO.getEnv name
  | .realPath path => (IO.FS.realPath path).toBaseIO
  | .readFile path => (IO.FS.readFile path).toBaseIO
  | .symlinkMetadata path => path.symlinkMetadata.toBaseIO
  | .writeFile path text => (IO.FS.writeFile path text).toBaseIO
  | .createDirAll path => (IO.FS.createDirAll path).toBaseIO
  | .createTempDir => IO.FS.createTempDir.toBaseIO
  | .removeDirAll path => (IO.FS.removeDirAll path).toBaseIO
  | .println text => (IO.println text).toBaseIO
  | .flush => (do (← IO.getStdout).flush : IO Unit).toBaseIO
  | .parseHeader input =>
    (do
      let (header, state, messages) ← Lean.Parser.parseHeader input
      return (header.raw, state, messages, Lean.Elab.HeaderSyntax.imports header) :
        IO (Syntax × ModuleParserState × MessageLog × Array Import)).toBaseIO
  | .parseCommand input env state messages =>
    pure (Lean.Parser.parseCommand input { env, options := {} } state messages)
  | .findOLean path module => (do Lean.searchPathRef.set path; Lean.findOLean module : IO FilePath).toBaseIO
  | .importForRules path modules =>
    (do
      Lean.searchPathRef.set path
      Lean.importModules (modules.map ({ module := · })) {} (loadExts := false) (level := .private) : IO Environment).toBaseIO
  | .importForParser path modules =>
    (do Lean.searchPathRef.set path; importParsers enable modules : IO (Environment × List Name)).toBaseIO
  | .parseToml input => lake.parseToml input
  | .lakeInstall sysroot => lake.lakeInstall sysroot
  | .loadWorkspace sysroot dir => lake.loadWorkspace sysroot dir
  | .loadRoot sysroot dir => lake.loadRoot sysroot dir
  | .libModules lib => lake.libModules lib
  | .runLake program cwd args => (spawnLake program cwd args).toBaseIO

end Regula.Effect
