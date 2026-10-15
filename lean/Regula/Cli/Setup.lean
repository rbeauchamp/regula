import Regula.Checker.AxiomGate
import Regula.CompilerProbe
import RegulaCore.Guidance
import Lake.Toml.Grammar
import Lake.Toml.Load
import Lean.Elab.Frontend

/-! # `regula init` and `regula doctor`

`init` writes the setup a project is missing, and `doctor` reports every missing or wrong piece
with its fix. Both execute the proved decision of `RegulaCore.Setup` over what they observe:
`init` writes exactly the edits of `Regula.Setup.plan` (so `plan_idempotent` says what a second
run writes: nothing), and `doctor` prints `Regula.Setup.issues` together with the linter's own
RG2002 manifest validation and RG2006 option decision, in the linter's finding text, one RG2006
finding for the targets that share a claim and failures.

## Main declarations

- `observe`, `resolveImport`, `importClosure`, `soleDeclared`: the `Regula.Setup.Observation` of
  a project, from Lake's loaded package, the files, the import headers of the root package's
  modules that Lake's own lookup reaches from the claimed modules, and the place of its only
  library's glob, found by the walk that writes it (`tomlPlaces`, `soleLibraryCommand`).
- `pinned`: the compiler the project's own `lean-toolchain` selects, resolved to a toolchain
  `elan toolchain list` names and identified by its reported version and commit.
- `guidanceDirs`, `guidanceFile`: the repository's `AGENTS.md` that holds or receives the
  agent-guidance section, searched from the Lake root up to the Git repository root, and that
  root, where the skill files are.
- `lakefileText`: the lakefile with the planned `lintDriver`, `leanOptions` and `globs` edits
  written into it, located with Lake's own TOML grammar or Lean's parser over the `package`,
  `lean_lib` and `lean_exe` declarations.
- `starterManifest`: every root `lean_lib` claimed `standard-logical`, as a `Manifest` value that
  `Manifest.parse` admits before it is written.
- `init`: apply the plan, observe again and restore every written file unless the new plan is
  empty, the new observation leaves out no module of a library the plan gave a glob
  (`Regula.Setup.uncovered_run`), and each claimed target of both observations, matched by kind
  and name, sets the same required options only with a `-D` (`Regula.Setup.arguedBy_run`); then
  run `doctor`.
- `doctor`: print the findings and the edits `init` would write, exiting 0 only when there is
  none, and a note, which does not count, for each module outside every library that no claimed
  module imports.

## Boundaries

Lake's loader, the parsers (including Lean's import-header parser), the filesystem and the Lean
frontend that locates the `package`, `lean_lib` and `lean_exe` declarations are trusted. That a
text edit realizes `Regula.Setup.apply` is not proved: `init` observes the project again after
writing and refuses, restoring the files it wrote, unless the plan of the new observation is
empty and its `uncovered` has no entry for a library the plan gave a glob. `init` never changes
a value the project already gives: it inserts text only, into the package's configuration and
each claimed target's as the plan decides, and a `globs` setting into
the library of `Regula.Setup.Observation.globCase`, located the same way. That case is read from
Lake: the package's only library, with one root and its globs Lake's default, whose glob has a
place in the configuration file, found by the walk that writes it (`soleDeclared`), and whose
glob, Lake's own over its source directory, adds only source files the import closure of the
claimed modules, the claimed roots included, already read under the same name, compared by
canonical path (`IO.FS.realPath`). That closure resolves each import with Lake's own lookup
(`resolveImport`) and reads the headers of the files Lake gives those modules alone; the files the
walk below each library root finds decide only what `doctor` reports a library leaves out. A
`.git` entry marks the repository root for the agent guidance; Git itself is not run. RG2006 in
`doctor` applies Mathlib's options when the workspace contains Mathlib, where the linter applies
them to a target whose modules import Mathlib; by
`RegulaPolicy.Community.conforming_of_mathlib`, a target `doctor` accepts also passes the
linter's decision. Elan's listing and that
compiler's report of its own version and commit are trusted; nothing is installed, and a pin
that does not resolve is a setup issue. -/

namespace Regula.Cli.Setup

open Lean System
open Regula.Setup
open Regula.Checker
open RegulaPolicy.Community (OptionValue)

/-- The agent-guidance file of a project, as `guidanceFile` finds it. -/
structure GuidanceFile where
  /-- The file. -/
  path : FilePath
  /-- The file relative to the project root, such as `../AGENTS.md`. -/
  name : String
  /-- The project root relative to the file's directory, such as `lean`; empty when they are the
  same directory. -/
  project : String
  /-- The file exists. -/
  present : Bool
  /-- The file has the `agentsHeading` line. -/
  hasSection : Bool
  /-- A Git repository contains the project root (`guidanceDirs`). -/
  repository : Bool
  /-- The repository root relative to the project root, as a prefix such as `../`; empty when
  they are the same directory. -/
  up : String

/-- What the commands read of a project in one observation. -/
structure Project where
  /-- The project root. -/
  root : FilePath
  /-- The root package's configuration format. -/
  lakefile : Lakefile
  /-- The root package's configuration file. -/
  configFile : FilePath
  /-- The agent-guidance file `Observation.agentsFile` names. -/
  guidance : GuidanceFile
  /-- The facts the setup decision reads. -/
  observation : Observation

/-- Whether `text` has `agentsHeading` as one of its lines. -/
def hasAgentsHeading (text : String) : Bool :=
  (text.splitOn "\n").any fun line => line == agentsHeading || line == agentsHeading ++ "\r"

/-- The directories from `root` up to the root of the Git repository that contains it, nearest
first, with whether there is one: the walk ends at the first directory holding `.git` (the
directory, or the file of a worktree or submodule), and is `root` alone when no ancestor holds
one. The upward walk terminates on the byte length of the path, as `findRepoRoot`'s does. -/
def guidanceDirs (root : FilePath) : IO (List FilePath × Bool) := do
  let rec loop (path : FilePath) (walked : List FilePath) : IO (Option (List FilePath)) := do
    let walked := path :: walked
    if ← Regula.Filesystem.isPresent (path / ".git") then return some walked.reverse
    match path.parent with
    | some parent =>
      if parent.toString.utf8ByteSize < path.toString.utf8ByteSize then loop parent walked
      else return none
    | none => return none
  termination_by path.toString.utf8ByteSize
  match ← loop root [] with
  | some dirs => return (dirs, true)
  | none => return ([root], false)

/-- The agent-guidance file of the project at `root`, the repository's rather than a nested Lake
project's own: among the `AGENTS.md` files of `guidanceDirs root`, the nearest with the
`agentsHeading` line, else the nearest that exists, else the repository root's. -/
def guidanceFile (root : FilePath) : IO GuidanceFile := do
  let (dirs, repository) ← guidanceDirs root
  let up := String.join (List.replicate (dirs.length - 1) "../")
  -- The file in the directory `i` levels above `root`.
  let file (i : Nat) (present hasSection : Bool) : GuidanceFile :=
    { path := (dirs.getD i root) / "AGENTS.md"
      name := String.join (List.replicate i "../") ++ "AGENTS.md"
      project := "/".intercalate (root.components.drop (root.components.length - i))
      present, hasSection, repository, up }
  let mut found : List GuidanceFile := []
  for (dir, i) in dirs.zipIdx do
    let path := dir / "AGENTS.md"
    if ← Regula.Filesystem.isPresent path then
      found := found ++ [file i true (hasAgentsHeading (← IO.FS.readFile path))]
  return (found.find? (·.hasSection) <|> found.head?).getD (file (dirs.length - 1) false false)

/-- The compiler the `lean-toolchain` of the project at `root` selects: the file's
selector resolves to a toolchain `elan toolchain list` names (`installedName?`), whose compiler
reports its version and commit (`Regula.Toolchain.probe`). An override or the compiler running
`regula` does not enter. A selector naming no toolchain Elan lists as installed, or a failed
probe, is `Pin.unresolved`. The file exists: `findRepoRoot` finds the project root by it. -/
def pinned (root : FilePath) : IO Pin := do
  let selector := (← IO.FS.readFile (root / "lean-toolchain")).trimAscii.toString
  match ← (Regula.Toolchain.probe root selector).toBaseIO with
  | .ok identity => return .compiler selector identity.version identity.commit
  | .error error => return .unresolved selector error.toString

/-- The module of the root package of `ws` that an import of `name` resolves to: Lake's own lookup,
`Workspace.findModule?`, which a build of the importing module uses (`Module.recFetchInput`);
`none` when it finds no module or another package's. -/
def resolveImport (ws : Lake.Workspace) (name : Name) : Option Lake.Module :=
  (ws.findModule? name).filter (·.pkg.keyName == ws.root.keyName)

/-- The modules of the root package of `ws` reachable by import from `starts`, the starts
included, each with the canonical path (`IO.FS.realPath`) of the source file read for it. Each
import resolves through `resolveImport`, so the closure holds only modules Lake gives it, each
with the `Module.leanFile` Lake gives that module, and reads only their headers, with Lean's
header parser, without building. An import of another package or of the toolchain ends its path.
A module of the closure whose source file does not exist is refused, naming the module and the
module that imports it, or naming it as a claimed module: Lake's build of that module fails
reading the file (`Module.recFetchInput`).
-/
def importClosure (ws : Lake.Workspace) (starts : List Lake.Module) :
    IO (List (Name × FilePath)) := do
  let mut visited : Std.HashSet (Name × String) := {}
  let mut reached : Array (Name × FilePath) := #[]
  let mut canonical : Std.HashSet (Name × String) := {}
  -- Each pending module with the module whose import reached it; a start has none.
  let mut pending : List (Lake.Module × Option Name) := starts.map (·, none)
  repeat
    let (m, importer) :: rest := pending | break
    pending := rest
    let file := m.leanFile
    if visited.contains (m.name, file.toString) then continue
    visited := visited.insert (m.name, file.toString)
    unless ← Regula.Filesystem.isPresent file do
      throw <| IO.userError <| match importer with
        | some i => s!"module {i} imports {m.name}, which Lake resolves to {file}, and that file \
            does not exist, so Lake cannot build {i}"
        | none => s!"the source {file} of claimed module {m.name} does not exist, so Lake cannot \
            build it"
    let path ← IO.FS.realPath file
    if canonical.contains (m.name, path.toString) then continue
    canonical := canonical.insert (m.name, path.toString)
    reached := reached.push (m.name, path)
    let header ← Lean.parseImports' (← IO.FS.readFile file) file.toString
    -- An entry of module names: the import lines of a project source.
    Regula.Checker.requireSafeModuleNames s!"the imports of {file}" (header.imports.map (·.module))
    for i in header.imports do
      if let some next := resolveImport ws i.module then pending := (next, some m.name) :: pending
  return reached.toList

/-- The project's manifest with its Lake inventory, refused unless it loads and classifies every
root target: the audit's own RG2002 functions. -/
def validManifest (root : FilePath) : IO (Manifest × Lake.SurfaceInventory) := do
  let inventory ← Lake.surfaceInventory root
  let manifest ← Manifest.loadFor (Manifest.defaultPath root) inventory
  discard <| IO.ofExcept <| Acceptance.surfaceAssignments manifest inventory
  AxiomGate.checkClassification manifest inventory
  return (manifest, inventory)

/-! ## Text edits -/

/-- `s` with each `(position, text)` inserted at its byte position, insertions at one position
in the given order. Positions come from the parsers' syntax positions and from line ends, so they
fall on character boundaries; any other position is refused. -/
def splice (s : String) (insertions : List (Nat × String)) : Except String String := do
  let bytes := s.toUTF8
  let sorted := insertions.mergeSort fun a b => a.1 ≤ b.1
  let mut out := ByteArray.empty
  let mut last := 0
  for (pos, text) in sorted do
    if pos < last || pos > bytes.size then throw s!"insertion position {pos} is out of range"
    out := out ++ bytes.extract last pos ++ text.toUTF8
    last := pos
  out := out ++ bytes.extract last bytes.size
  match String.fromUTF8? out with
  | some result => return result
  | none => throw "an insertion split a character"

/-- The byte position of the end of the line containing byte `pos`. -/
def lineEnd (s : String) (pos : Nat) : Nat := Id.run do
  let bytes := s.toUTF8
  for i in [pos:bytes.size] do
    if bytes[i]! == 10 then return i
  return bytes.size

/-- The number of bytes between the start of the line containing byte `pos` and `pos`. -/
def column (s : String) (pos : Nat) : Nat := Id.run do
  let bytes := s.toUTF8
  let mut start := pos
  for _ in [0:pos] do
    if start == 0 || bytes[start - 1]! == 10 then break
    start := start - 1
  return pos - start

private def startOf (stx : Syntax) : Except String Nat :=
  match stx.getPos? with
  | some p => .ok p.byteIdx
  | none => .error "syntax without a position"

private def endOf (stx : Syntax) : Except String Nat :=
  match stx.getTailPos? with
  | some p => .ok p.byteIdx
  | none => .error "syntax without a position"

private def sourceText (s : String) (stx : Syntax) : Except String String := do
  let bytes := s.toUTF8
  match String.fromUTF8? (bytes.extract (← startOf stx) (← endOf stx)) with
  | some text => return text
  | none => throw "syntax range splits a character"

/-- A `[[lean_lib]]` or `[[lean_exe]]` table of a `lakefile.toml` and where it receives options:
after its last key, or into its inline `leanOptions` table. -/
private structure TomlTarget where
  exe : Bool
  name : Option String := none
  lastEnd : Nat
  inline : Option (Nat × Bool) := none
  unsupported : Bool := false
  globs : Bool := false

/-- Where a `lakefile.toml` receives the edits: after the last top-level key, into an existing
`[leanOptions]` table or inline `leanOptions` table, and into each target table. -/
private structure TomlPlaces where
  topEnd : Option Nat := none
  table : Option Nat := none
  inline : Option (Nat × Bool) := none
  unsupported : Bool := false
  targets : Array TomlTarget := #[]

/-- Where a `leanOptions` key-value pair `e` receives entries: after the last pair of its inline
table, or inside the braces of an empty one; `none` for any other value. -/
private def inlinePlace (e : Syntax) : Except String (Option (Nat × Bool)) := do
  let value := e[2]
  unless value.isOfKind `Lake.Toml.inlineTable do return none
  let pairs := value[1].getArgs.filter fun x => x.isOfKind `Lake.Toml.keyval
  if let some lastPair := pairs.back? then return some (← endOf lastPair, true)
  return some (← startOf value[2], false)

/-- The simple keys of TOML syntax `stx`, in order. -/
private partial def simpleKeys (stx : Syntax) : Array Syntax :=
  if stx.isOfKind `Lake.Toml.simpleKey then #[stx]
  else stx.getArgs.foldl (fun acc a => acc ++ simpleKeys a) #[]

/-- The table a key of a `lakefile.toml` belongs to: the top level, the `[leanOptions]` table, a
`[[lean_lib]]` or `[[lean_exe]]` table, or another. -/
private inductive TomlSection where
  | top | options | target | other

/-- Where `lakefile.toml` text `input` receives the edits, from one walk of the file as Lake's
TOML grammar parses it. Each key is read as Lake's TOML loader reads it (`Lake.Toml.elabSimpleKey`
for each bare or quoted simple key), and each target's `name` value as the loader decodes it. -/
private def tomlPlaces (input : String) : IO TomlPlaces := do
  let ictx := Parser.mkInputContext input "lakefile.toml"
  let env ← mkEmptyEnvironment
  let s := Lake.Toml.toml.fn.run ictx { env, options := {} } {}
    (Parser.mkParserState ictx.inputString)
  if let some error := s.errorMsg then
    throw <| IO.userError s!"lakefile.toml does not parse: {error}"
  -- Each target table's `name` as Lake's TOML loader decodes it, by the position of its value.
  let decodedTable ← match ← (Lake.Toml.loadToml ictx).toBaseIO with
    | .ok table => pure table
    | .error _ => throw <| IO.userError "lakefile.toml does not load as TOML"
  let names : List (Nat × String) := [`lean_lib, `lean_exe].flatMap fun kind =>
    match decodedTable.find? kind with
    | some (.array _ tables) => tables.toList.filterMap fun
      | .table' _ t => match t.find? `name with
        | some (.string ref s) => ref.getPos?.map (·.byteIdx, s)
        | _ => none
      | _ => none
    | _ => []
  let stx := s.stxStack.back
  let expressions := stx[1].getArgs.filter fun e => !e.isOfKind nullKind
  -- Each expression's key, decoded: a table's header, or a key-value pair's key.
  let decode (x : Syntax) : IO String := do
    let ctx : Core.Context := { fileName := ictx.fileName, fileMap := ictx.fileMap }
    match ← ((Lake.Toml.elabSimpleKey ⟨x⟩).run' ctx { env }).toBaseIO with
    | .ok key => pure key
    | .error _ => throw <| IO.userError "lakefile.toml has a key Lake's TOML loader does not read"
  let keys ← expressions.mapM fun e =>
    (simpleKeys (if e.isOfKind `Lake.Toml.keyval then e[0] else e)).toList.mapM decode
  let places ← IO.ofExcept <| (expressions.zip keys).foldlM (init := ({}, TomlSection.top))
    (fun ((p : TomlPlaces), (current : TomlSection)) (e, key) => do
      let lastTarget (f : TomlTarget → TomlTarget) : TomlPlaces :=
        { p with targets := p.targets.modify (p.targets.size - 1) f }
      -- A dotted key below `leanOptions`, which `init` does not write into.
      let dotted := key.head? == some "leanOptions" && key.length > 1
      if e.isOfKind `Lake.Toml.stdTable then
        let headerEnd := lineEnd input (← endOf e)
        if key == ["leanOptions"] then return ({ p with table := some headerEnd }, .options)
        let p := if dotted then { p with unsupported := true }
          else if key.take 2 == ["lean_lib", "leanOptions"] ||
              key.take 2 == ["lean_exe", "leanOptions"] then
            lastTarget ({ · with unsupported := true })
          else p
        return (p, .other)
      if e.isOfKind `Lake.Toml.arrayTable then
        if key == ["lean_lib"] || key == ["lean_exe"] then
          let target : TomlTarget :=
            { exe := key == ["lean_exe"], lastEnd := lineEnd input (← endOf e) }
          return ({ p with targets := p.targets.push target }, .target)
        return (p, .other)
      match current with
      | .top =>
        let p := { p with topEnd := some (lineEnd input (← endOf e)) }
        if key == ["leanOptions"] then
          match ← inlinePlace e with
          | some place => return ({ p with inline := some place }, current)
          | none => return ({ p with unsupported := true }, current)
        if dotted then return ({ p with unsupported := true }, current)
        return (p, current)
      | .options => return ({ p with table := some (lineEnd input (← endOf e)) }, current)
      | .target =>
        let lastEnd := lineEnd input (← endOf e)
        let decoded := names.lookup (← startOf e[2])
        let inline ← if key == ["leanOptions"] then inlinePlace e else pure none
        return (lastTarget fun t => { t with
          lastEnd
          name := if key == ["name"] then decoded else t.name
          inline := if key == ["leanOptions"] then inline else t.inline
          unsupported := t.unsupported || dotted || (key == ["leanOptions"] && inline.isNone)
          globs := t.globs || key.head? == some "globs" }, current)
      | .other => return (p, current))
  return places.1

/-- The place of the `globs` of library `library` in the walk `places` of a `lakefile.toml`: after
the last key of its `[[lean_lib]]` table, when that table is the file's only `[[lean_lib]]` table,
its `name` decodes to `library`, and it has no `globs` key; `none` otherwise, such as for a library
written as an inline table (`lean_lib = [{ name = "Demo" }]`), which has no table to edit. -/
private def TomlPlaces.globPlace (places : TomlPlaces) (library : String) : Option Nat :=
  match places.targets.filter (!·.exe) with
  | #[t] =>
    if !t.globs && t.name.any (fun s => (Lake.stringToLegalOrSimpleName s).toString == library)
    then some t.lastEnd else none
  | _ => none

/-- `lakefile.toml` with the planned edits: `lintDriver` as a new last top-level key, the missing
package options appended to the `[leanOptions]` table, to an inline `leanOptions` table, or in a
new `[leanOptions]` table after the top-level keys, and each target's missing options appended to
its inline `leanOptions` table or as a new inline table after its last key, and the `globs` of
each library of `globs` (its name and roots) at `TomlPlaces.globPlace`, the place whose presence
`soleDeclared` requires. A `leanOptions` written with dotted keys or as sub-tables is refused,
with the entries to add by hand. -/
def tomlText (input : String) (driver : Bool) (entries : List (Name × OptionValue))
    (targets : List Regula.Setup.Target) (globs : List (String × List String)) :
    IO String := do
  let places ← tomlPlaces input
  let lines := entries.map (Lakefile.toml.entry ·)
  -- After the last top-level key's line; with none, at the start of the file.
  let (top, before, after) := match places.topEnd with
    | some pos => (pos, "\n", "")
    | none => (0, "", "\n")
  let driverText :=
    if driver then [(top, before ++ "lintDriver = \"" ++ lintDriver ++ "\"" ++ after)] else []
  let optionText ← if entries.isEmpty then pure [] else
    if places.unsupported then
      throw <| IO.userError s!"lakefile.toml writes leanOptions as dotted keys or sub-tables; add \
        {", ".intercalate lines} to it by hand"
    else match places.table, places.inline with
      | some pos, _ => pure [(pos, String.join (lines.map ("\n" ++ ·)))]
      | none, some (pos, true) => pure [(pos, String.join (lines.map (", " ++ ·)))]
      | none, some (pos, false) => pure [(pos, " " ++ ", ".intercalate lines ++ " ")]
      | none, none =>
        let table := "[leanOptions]" ++ String.join (lines.map ("\n" ++ ·))
        pure [(top, if places.topEnd.isSome then "\n\n" ++ table else table ++ "\n\n")]
  let targetText ← targets.mapM fun t => do
    let table := s!"[[{if t.exe then "lean_exe" else "lean_lib"}]] table named \"{tomlName t.name}\""
    let lines := t.options.map (Lakefile.toml.entry ·)
    let some place := places.targets.find? fun p =>
        p.exe == t.exe && p.name.any fun s => (Lake.stringToLegalOrSimpleName s).toString == t.name
      | throw <| IO.userError s!"lakefile.toml has no {table}; add \
          {", ".intercalate lines} to its leanOptions by hand"
    if place.unsupported then
      throw <| IO.userError s!"the {table} writes leanOptions as \
        dotted keys or a sub-table; add {", ".intercalate lines} to it by hand"
    match place.inline with
    | some (pos, true) => pure (pos, String.join (lines.map (", " ++ ·)))
    | some (pos, false) => pure (pos, " " ++ ", ".intercalate lines ++ " ")
    | none => pure (place.lastEnd, "\nleanOptions = { " ++ ", ".intercalate lines ++ " }")
  let globText ← globs.mapM fun (library, roots) => do
    let table := s!"[[lean_lib]] table named \"{tomlName library}\""
    let setting := Lakefile.toml.globsSetting roots
    -- `soleDeclared` found this place in the same file before the plan included the edit.
    let some place := places.globPlace library
      | throw <| IO.userError s!"lakefile.toml has no {table} to add `{setting}` to"
    pure (place, "\n" ++ setting)
  IO.ofExcept <| splice input (driverText ++ optionText ++ targetText ++ globText)

/-- The commands of a `lakefile.lean` as Lean's parser reads them while Lake elaborates the file
(with the file's own imports and `open` commands in effect), and its first errors. -/
def lakefileCommands (path : FilePath) (input : String) : IO (Array Syntax × List String) := do
  initializeLeanSearchPath
  -- The file's `import Lake` runs Lake's initializers, as when Lake loads it.
  unsafe Lean.enableInitializersExecution
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let options ← Regula.Process.leanOptions
  let (env, messages) ← Elab.processHeader header options messages inputCtx (mainModule := `lakefile)
  let env := Lake.dirExt.setState env (some ((path.parent.getD ".")))
  let env := Lake.optsExt.setState env (some {})
  let s ← Elab.IO.processCommands inputCtx parserState (Elab.Command.mkState env messages options)
  let errors ← (s.commandState.messages.toList.filter (·.severity == .error)).mapM (·.toString)
  return (s.commands, errors.take 3)

/-- The name a `lean_lib` or `lean_exe` command declares, as Lake spells the target's name. -/
def commandName (command : Syntax) : Option String :=
  let name := command[3][0][0]
  if name.isIdent then some name.getId.toString
  else name.isStrLit?.map fun s => (Name.mkSimple s).toString

/-- The configuration fields of a `package` declaration, in source order. -/
partial def declFields (stx : Syntax) : Array Syntax :=
  if stx.getKind == `Lake.DSL.declField then #[stx]
  else stx.getArgs.foldl (fun acc a => acc ++ declFields a) #[]

/-- Whether `stx` contains a node of `kind`. -/
partial def containsKind (stx : Syntax) (kind : SyntaxNodeKind) : Bool :=
  stx.getKind == kind || stx.getArgs.any (containsKind · kind)

/-- The insertions that write the planned edits into the configuration of declaration `command`
(`what` names it): `lintDriver` and the `globs` setting `globs` as new last fields, and the
missing options appended to the `leanOptions` array literal, appended to any other `leanOptions`
term with `++`, or as a new last field. A `globs` field already in the declaration, which
`soleDeclared` rules out for the library that receives one, is refused. An empty `where` block
receives the `globs` setting alone; any other field into an empty `where` block or structure
instance is refused. -/
def configInsertions (input : String) (command : Syntax) (what : String) (driver : Bool)
    (entries : List (Name × OptionValue)) (globs : Option String := none) :
    Except String (List (Nat × String)) := do
  let fields := declFields command
  let structForm := containsKind command `Lake.DSL.declValStruct
  let whereForm := containsKind command `Lake.DSL.declValWhere
  let rendered := entries.map (Lakefile.lean.entry ·)
  let optionsField := fields.find? fun f => f[0].getId == `leanOptions
  if let some setting := globs then
    if fields.any (·[0].getId == `globs) then
      throw s!"{what} writes `globs`; add `{setting}` to it by hand"
  -- The new fields; a new `leanOptions` array puts one entry per line below the field when the
  -- fields are written one per line at indentation `indent`.
  let newFields (indent : Option String) : List String :=
    (if driver then ["lintDriver := \"" ++ lintDriver ++ "\""] else []) ++
    (if optionsField.isNone && !entries.isEmpty then
      match indent with
      | some i =>
        ["leanOptions := #[" ++ ",".intercalate (rendered.map (("\n" ++ i ++ "  ") ++ ·)) ++ "]"]
      | none => ["leanOptions := #[" ++ ", ".intercalate rendered ++ "]"]
    else []) ++
    globs.toList
  let fieldInsertions ← do
    if (newFields none).isEmpty then pure []
    else match fields.back? with
    | some last =>
      if structForm then
        pure [(← endOf last, String.join ((newFields none).map ("; " ++ ·)))]
      else
        let indent := "".pushn ' ' (column input (← startOf fields[0]!))
        pure [(lineEnd input (← endOf last),
          String.join ((newFields (some indent)).map (("\n" ++ indent) ++ ·)))]
    | none =>
      if structForm || (whereForm && (driver || !entries.isEmpty)) then
        throw s!"{what} has an empty configuration; add the fields by hand"
      if whereForm then
        -- An empty `where` block, as in Lake's `lake new` template: the glob goes on its own
        -- line after `where`.
        let some keyword := command.find? (·.isToken "where")
          | throw s!"{what} has a `where` block without its keyword; add the fields by hand"
        pure [(← endOf keyword, String.join ((newFields (some "  ")).map ("\n  " ++ ·)))]
      else
        -- A declaration with no configuration: open a `where` block after its name.
        pure [(← endOf command,
          " where" ++ String.join ((newFields (some "  ")).map ("\n  " ++ ·)))]
  let optionInsertions ← do
    match optionsField with
    | none => pure []
    | some field =>
      if entries.isEmpty then pure []
      else
        let value := field[2]
        match value[0] with
        | .atom _ "#[" =>
          let elements := value[1].getArgs.toList.zipIdx.filterMap fun (x, i) =>
            if i % 2 == 0 then some x else none
          match elements.getLast?, elements.head? with
          | some last, some first =>
            let firstStart ← startOf first
            let multiline := lineEnd input firstStart != lineEnd input (← startOf value)
            let sep := if multiline then ",\n" ++ "".pushn ' ' (column input firstStart) else ", "
            pure [(← endOf last, String.join (rendered.map (sep ++ ·)))]
          | _, _ => pure [(← endOf value[0], ", ".intercalate rendered)]
        | _ => pure [(← startOf value, "("),
            (← endOf value, ") ++ #[" ++ ", ".intercalate rendered ++ "]")]
  -- At one position, an edit inside the `leanOptions` value precedes a new field after it.
  return optionInsertions ++ fieldInsertions

/-- The `lean_lib` command of library `name` among the commands of a `lakefile.lean`, when it is
the file's only `lean_lib` command, at the top level, named `name`, in a `where` block or with no
configuration, and without a `globs` field, and no other command contains a `lean_lib`, such as
`meta if`; `none` otherwise. -/
def soleLibraryCommand (commands : Array Syntax) (name : String) : Option Syntax :=
  let nested := commands.any fun c =>
    c.getKind != `Lake.DSL.leanLibCommand && containsKind c `Lake.DSL.leanLibCommand
  match commands.filter (·.getKind == `Lake.DSL.leanLibCommand) with
  | #[command] =>
    if !nested && commandName command == some name &&
        !containsKind command `Lake.DSL.declValSimple &&
        !containsKind command `Lake.DSL.declValStruct &&
        !(declFields command).any (·[0].getId.eraseMacroScopes == `globs) then
      some command
    else none
  | _ => none

/-- `lakefile.lean` with the planned edits in its `package` declaration and in the `lean_lib` and
`lean_exe` declarations of the targets with entries and of the libraries of `globs` (each name
with its roots, its declaration `soleLibraryCommand`), one `configInsertions` for each
declaration. -/
def leanText (path : FilePath) (input : String) (driver : Bool)
    (entries : List (Name × OptionValue)) (targets : List Regula.Setup.Target)
    (globs : List (String × List String)) : IO String := do
  let (commands, errors) ← lakefileCommands path input
  let some package := commands.find? (·.getKind == `Lake.DSL.packageCommand)
    | throw <| IO.userError s!"{path}: Lean found no `package` declaration\
        {String.join (errors.map ("\n" ++ ·))}"
  let mut insertions ← IO.ofExcept <|
    configInsertions input package "the `package` declaration" driver entries
  -- Each declaration once: the targets with entries, then the other libraries with a glob.
  let declared := targets.map (fun t => (t.exe, t.name)) ++
    (globs.filter fun (l, _) => !targets.any fun t => !t.exe && t.name == l).map (false, ·.1)
  for (exe, name) in declared do
    let options := ((targets.find? fun t => t.exe == exe && t.name == name).map (·.options)).getD []
    let setting := if exe then none else (globs.lookup name).map Lakefile.lean.globsSetting
    let declaration := s!"`{if exe then "lean_exe" else "lean_lib"} {name}`"
    let kind := if exe then `Lake.DSL.leanExeCommand else `Lake.DSL.leanLibCommand
    -- A library with a glob: the command `soleDeclared` found in the same file.
    let found := if setting.isSome then soleLibraryCommand commands name
      else commands.find? fun c => c.getKind == kind && commandName c == some name
    let some command := found
      | throw <| IO.userError s!"{path}: Lean found no {declaration} declaration; add \
          {", ".intercalate (options.map (Lakefile.lean.entry ·) ++ setting.toList)} to it by \
          hand"
    insertions := insertions ++ (← IO.ofExcept <|
      configInsertions input command s!"the {declaration} declaration" false options setting)
  IO.ofExcept <| splice input insertions

/-- The lakefile text after the plan's `lintDriver`, `leanOptions` and `globs` edits. -/
def lakefileText (project : Project) (input : String) (edits : List Edit) : IO String := do
  let driver := edits.contains .driver
  let entries := edits.flatMap Edit.entries
  let targets := (edits.filterMap Edit.added?).flatten.filter (!·.options.isEmpty)
  let globs := edits.filterMap fun | .globs library roots => some (library, roots) | _ => none
  match project.lakefile with
  | .toml => tomlText input driver entries targets globs
  | .lean => leanText project.configFile input driver entries targets globs

/-! ## Observation -/

/-- Whether the configuration file `path` (of format `kind`) gives the root package's only
library, `name`, with root `root`, the place where `init` writes its glob, found by the walk that
writes it: in `lakefile.toml`, `TomlPlaces.globPlace` of `tomlPlaces`, the file's only
`[[lean_lib]]` table, its `name` decoding to `name`, without a `globs` key; in `lakefile.lean`,
`soleLibraryCommand`, which `leanText` edits, and `configInsertions` of its glob into it. A
library written as an inline table, or a walk that fails, has no place, and the glob case does
not hold. -/
def soleDeclared (kind : Lakefile) (path : FilePath) (name root : String) : IO Bool := do
  let input ← IO.FS.readFile path
  match kind with
  | .toml =>
    try return ((← tomlPlaces input).globPlace name).isSome catch _ => return false
  | .lean =>
    try
      let (commands, errors) ← lakefileCommands path input
      unless errors.isEmpty do return false
      let setting := Lakefile.lean.globsSetting [root]
      return (soleLibraryCommand commands name).any fun command =>
        (configInsertions input command "" false [] (some setting)).toBool
    catch _ => return false

/-- Observe the project at `root`: Lake's loaded root package (its `lintDriver`, package-level
`leanOptions`, whether it has a `lean_lib`, and the root targets the manifest does not exclude with
their own `leanOptions` and resolved extra `lean` arguments), whether the workspace contains
Mathlib, the compiler its `lean-toolchain` selects (`pinned`), the manifest and agent-guidance
files, the modules a walk of each library root's directory finds that no library includes, each
split by whether the import closure of the claimed modules (`importClosure`) read that module from
the file the walk found, and the facts of `Regula.Setup.Observation.globCase`: the package's only
`lean_lib` when it has one root, Lake reports its globs as that root alone and `soleDeclared`
holds, each module Lake's glob of the root's submodules finds in its source directory with its
`Module.leanFile`, and the file the import closure of the claimed modules, the claimed roots
included, read under each of those names, every file by its canonical path.

Assumes: Lake v4.34.1 selects the language from `relConfigFile`, not the resolved `configFile`
(`Lake/Load/Package.lean:100`), under `LakeConfig.language`'s assumptions. -/
def observe (root : FilePath) : IO Project := do
  -- Without a manifest every root target is claimed, as in the starter `init` writes; a target the
  -- manifest that loads excludes is not. A manifest that does not parse or classify every root
  -- target claims none for the option edits until it does (`doctor` reports it as RG2002). A
  -- manifest that is there but cannot be read is a failure, never read as one that does not parse.
  let manifestPath := Manifest.defaultPath root
  let manifestExists ← Regula.Filesystem.isPresent manifestPath
  let manifest ← if manifestExists then
      pure (Manifest.parse manifestPath.toString (← IO.FS.readFile manifestPath)).toOption
    else pure none
  let invalid ← if manifestExists then
      try validManifest root *> pure false catch _ => pure true
    else pure false
  let excludedLibraries := (manifest.map (·.excludedLibraries.map (·.library))).getD #[]
  let excludedExecutables := (manifest.map (·.excludedExecutables.map (·.executable))).getD #[]
  let (lakefile, configFile, driver, options, targets, allClaimed, libraries, mathlib,
      uncovered, unimported, candidate, added, read) ←
      Workspace.withRootWorkspace root fun ws => do
      -- An entry of module names: the configuration of each package of the workspace, before
      -- any module is resolved or any path is built from a name (`Lake.checkModuleNames`).
      Regula.Checker.Lake.checkWorkspaceModuleNames ws
      let pkg := ws.root
      -- The names of every module a root library includes and of every executable root, and the
      -- claimed modules among them, each as Lake gives it.
      let mut included : NameSet := {}
      let mut claimed : List _root_.Lake.Module := []
      for lib in pkg.leanLibs do
        for m in ← lib.getModuleArray do
          included := included.insert m.name
          unless excludedLibraries.contains (Manifest.targetSpelling lib.name) do
            claimed := m :: claimed
      for exe in pkg.leanExes do
        included := included.insert exe.root.name
        unless excludedExecutables.contains (Manifest.targetSpelling exe.name) do
          claimed := exe.root :: claimed
      -- The modules below each library root that no root library includes, with the file the walk
      -- found for each: what the coverage report states, never a source of the import closure.
      let mut missedBy : Array (String × List String × Array (Name × FilePath)) := #[]
      for lib in pkg.leanLibs do
        let mut missed : Array (Name × FilePath) := #[]
        for r in lib.roots do
          let dir := Lean.modToFilePath lib.srcDir r ""
          unless ← Regula.Filesystem.isDirectory dir do continue
          for path in ← Regula.Filesystem.Construction.walkDirectory dir do
            if path.extension != some "lean" || (← Regula.Filesystem.isDirectory path) then
              continue
            let parts := (path.withExtension "").components.drop dir.components.length
            let name := parts.foldl Name.str r
            unless included.contains name do missed := missed.push (name, path)
        unless missed.isEmpty do
          missedBy := missedBy.push (lib.name.toString, lib.roots.toList.map toString, missed)
      -- The package's only library when it has one root and Lake reports its globs as that root
      -- alone, and the modules its glob would add: Lake's own glob of the root's submodules, each
      -- with the file Lake gives a module of the library, `Module.leanFile`.
      let mut candidate : Option (String × String) := none
      let mut added : Array (Name × FilePath) := #[]
      if let #[lib] := pkg.leanLibs then
        if let #[r] := lib.roots then
          if lib.config.globs == #[.one r] then
            candidate := some (lib.name.toString, r.toString)
            if ← Regula.Filesystem.isDirectory (Lean.modToFilePath lib.srcDir r "") then
              let found ← IO.mkRef (#[] : Array Name)
              (Lake.Glob.submodules r).forEachModuleIn lib.srcDir fun m => found.modify (·.push m)
              added := (← found.get).map fun m => (m, Lean.modToFilePath lib.srcDir m "lean")
      -- Each module of the closure Lake resolves, with the canonical path of the file read for it.
      let imported ← importClosure ws claimed
      let importedSet : Std.HashSet (Name × String) :=
        .ofList (imported.map fun (m, path) => (m, path.toString))
      let sorted (names : Array Name) := ((names.map toString).qsort (· < ·)).toList
      let mut uncovered := []
      let mut unimported := []
      -- A module the walk found is imported when the closure read its name from the same file.
      for (library, roots, missed) in missedBy do
        let mut hit := #[]
        let mut rest := #[]
        for (name, path) in missed do
          let file := (← IO.FS.realPath path).toString
          if importedSet.contains (name, file) then hit := hit.push name
          else rest := rest.push name
        unless hit.isEmpty do uncovered := uncovered ++ [(library, roots, sorted hit)]
        unless rest.isEmpty do unimported := unimported ++ [(library, roots, sorted rest)]
      let own (options : Array Lean.LeanOption) :=
        (Lake.buildOptions (.ofArray options) #[] #[] .anonymous #[] #[]).options
      let libs := pkg.leanLibs.filter fun lib =>
        !excludedLibraries.contains (Manifest.targetSpelling lib.name)
      let exes := pkg.leanExes.filter fun exe =>
        !excludedExecutables.contains (Manifest.targetSpelling exe.name)
      -- A target's extra `lean` arguments are the audit inventory's, read by the same functions.
      -- With a valid manifest, `targets` lists every root target exactly when `allClaimed` holds.
      let target (exe : Bool) (name : Name) (options : Array Lean.LeanOption)
          (build : RegulaPolicy.Community.BuildOptions) : Regula.Setup.Target :=
        ⟨exe, name.toString, own options, build.arguments⟩
      let targets := if invalid then [] else
        (libs.map (fun lib => target false lib.name lib.config.leanOptions
            (Lake.libraryOptions lib)) ++
          exes.map (fun exe => target true exe.name exe.config.leanOptions
            (Lake.executableOptions exe))).toList
      let kind := match ← IO.ofExcept (LakeConfig.language pkg.relConfigFile) with
        | .toml => Lakefile.toml
        | .lean => Lakefile.lean
      let addedNames := added.foldl (fun s (m, _) => s.insert m) ({} : NameSet)
      return (kind, pkg.configFile, pkg.lintDriver,
        (Lake.buildOptions pkg.leanOptions #[] #[] .anonymous #[] #[]).options, targets,
        !invalid && libs.size == pkg.leanLibs.size && exes.size == pkg.leanExes.size,
        !pkg.leanLibs.isEmpty,
        ws.packages.any (·.baseName == `mathlib), uncovered, unimported, candidate,
        added.toList, imported.filter (fun (m, _) => addedNames.contains m))
  -- The configuration file is read only when the glob could apply: a library with modules for its
  -- glob to add.
  let sole ← match candidate with
    | some (name, r) =>
      if !added.isEmpty && (← soleDeclared lakefile configFile name r) then pure (some (name, r))
      else pure none
    | none => pure none
  -- Each file by its canonical path, `IO.FS.realPath`, so two spellings of one file agree; a file
  -- that is not there leaves the glob case, and one that cannot be resolved is a failure
  -- (`Regula.Filesystem.realPathIfPresent`).
  let canonical (pairs : List (Name × FilePath)) : IO (Option (List (String × String))) := do
    let mut out := []
    for (m, file) in pairs do
      let some path ← Regula.Filesystem.realPathIfPresent file | return none
      out := out ++ [(m.toString, path.toString)]
    return some out
  let (sole, added, read) ← match sole with
    | some s => do
      match ← canonical added, ← canonical read with
      | some a, some r => pure (some s, a, r)
      | _, _ => pure (none, [], [])
    | none => pure (none, [], [])
  let guidance ← guidanceFile root
  let skills ← skillPaths.filterMapM fun (p : String) => do
    let name := guidance.up ++ p
    if ← Regula.Filesystem.isPresent (root / name) then
      return some (name, (← IO.FS.readFile (root / name)) == Regula.Guidance.skill)
    return none
  return {
    root, lakefile, configFile, guidance
    observation := {
      driver, options, targets, allClaimed, libraries, mathlib
      manifest := ← Regula.Filesystem.isPresent (Manifest.defaultPath root)
      agentsFile := guidance.name, agentsSection := guidance.hasSection
      skillFile := guidance.up ++ skillPath, skills
      pin := ← pinned root
      uncovered, unimported
      sole, added, read } }

/-! ## The starter manifest -/

/-- The rationale of every starter claim. -/
def starterRationale : String :=
  "Starter claim written by `lake exe regula init`: every declaration may use propext, " ++
  "Quot.sound and Classical.choice, and compiled boundaries are reported. Replace this with " ++
  "the reason for the claim, and strengthen it where the library allows."

/-- Every root `lean_lib` claimed `standard-logical` with `report` execution; every root
`lean_exe` is claimed with the first library that contains its root module, as RG2002 requires
(`RegulaPolicy.RootsClassifiedAlike`), and with the first library when none does. -/
def starterManifest (inventory : Lake.SurfaceInventory) : Manifest :=
  let home (exe : Lake.ExecutableInventory) : Nat :=
    (inventory.libraries.findIdx? (·.modules.contains exe.root)).getD 0
  { surfaces := inventory.libraries.mapIdx fun i library =>
      { library := library.library
        executables := (inventory.executables.filter (home · == i)).map (·.executable)
        claim := .standardLogical, execution := .report, rationale := starterRationale }
    excludedLibraries := #[], excludedExecutables := #[] }

/-- A manifest as `init` writes it: a fixed key order, one surface per object, two-space indent. -/
def manifestText (m : Manifest) : String :=
  let str (s : String) : String := (Json.str s).compress
  let strings (xs : Array String) : String := "[" ++ ", ".intercalate (xs.toList.map str) ++ "]"
  let surface (s : Manifest.Surface) : String :=
    "    {\n" ++
    "      \"library\": " ++ str s.library ++ ",\n" ++
    "      \"executables\": " ++ strings s.executables ++ ",\n" ++
    "      \"claim\": " ++ str s.claim.toString ++ ",\n" ++
    "      \"execution\": " ++ str s.execution.spelling ++ ",\n" ++
    "      \"rationale\": " ++ str s.rationale ++ "\n" ++
    "    }"
  "{\n" ++
  "  \"schema-version\": 2,\n" ++
  "  \"surfaces\": [\n" ++ ",\n".intercalate (m.surfaces.toList.map surface) ++ "\n  ],\n" ++
  let excluded (key : String) (xs : List (String × String)) : String :=
    "[" ++ ", ".intercalate (xs.map fun (name, why) =>
      "{ \"" ++ key ++ "\": " ++ str name ++ ", \"rationale\": " ++ str why ++ " }") ++ "]"
  "  \"excluded-libraries\": " ++
    excluded "library" (m.excludedLibraries.toList.map fun l => (l.library, l.rationale)) ++
    ",\n" ++
  "  \"excluded-executables\": " ++
    excluded "executable"
      (m.excludedExecutables.toList.map fun e => (e.executable, e.rationale)) ++ "\n" ++
  "}\n"

/-! ## The commands -/

/-- The linter's configuration findings for a project with a manifest: RG2002 when the manifest
does not parse or does not classify every root target, and otherwise RG2006 for each claimed
target, decided by `RegulaPolicy.Community.failures` exactly as the audit decides it. Targets
with the same claim and the same failures share one finding naming them all, in manifest order,
where the linter prints one per target: a `-D` in the package's arguments fails every target
alike. -/
def configurationFindings (project : Project) : IO (Array Regula.Finding) := do
  let root := project.root
  let mode : EvidenceMode := .incrementalProject
  try
    let (manifest, inventory) ← validManifest root
    -- Each distinct claim and finding detail, with the targets that have it.
    let mut groups : Array (String × String × Array String) := #[]
    for surface in manifest.surfaces do
      let some library := inventory.libraries.find? (·.library == surface.library)
        | continue
      let mut targets := #[(surface.library, library.options)]
      for exe in surface.executables do
        if let some info := inventory.executables.find? (·.executable == exe) then
          targets := targets.push (exe, info.options)
      for (target, options) in targets do
        let failed := RegulaPolicy.Community.failures options project.observation.mathlib
        unless failed.isEmpty do
          let claim := surface.claim.toString
          let detail := RegulaPolicy.Community.detail failed
          match groups.findIdx? fun g => g.1 == claim && g.2.1 == detail with
          | some i => groups := groups.modify i fun g => (g.1, g.2.1, g.2.2.push target)
          | none => groups := groups.push (claim, detail, #[target])
    groups.mapM fun (claim, detail, targets) => do
      let d ← IO.ofExcept <| Regula.makeDiagnostic .communityConfiguration
        ⟨", ".intercalate targets.toList, detail⟩ (.project root.toString) mode (some claim)
        .violation
      return ⟨.communityConfiguration, d⟩
  catch error =>
    let configuration := error.toString.startsWith "manifest-"
    let finding ← IO.ofExcept <| Regula.Findings.contextFinding
      (if configuration then .configuration else .environment) root.toString error.toString mode
      (if configuration then .violation else .incomplete)
    return #[finding]

/-- Print every setup finding of the project at `root`, then the edits `init` would write, and a
note for each module left out of every library that no claimed module imports. Returns 0 when
there is nothing to fix and 1 otherwise; notes do not count. -/
def doctor (root : FilePath) : IO UInt32 := do
  RunFeedback.reset
  let project ← observe root
  let o := project.observation
  IO.println s!"regula doctor: {root} ({project.lakefile.name})"
  let setup := issues o
  for issue in setup do
    IO.println (issue.message project.lakefile ++ "\n" ++ issue.fix project.lakefile)
  let findings ← if o.manifest then configurationFindings project else pure #[]
  RunFeedback.emitAll IO.println findings
  for entry in o.unimported do IO.println (unimportedNote project.lakefile entry)
  let count := setup.length + findings.size
  if count == 0 then
    IO.println "regula doctor: the setup is complete; run `lake lint`"
    return 0
  IO.println s!"regula doctor: {count} problem{if count == 1 then "" else "s"}"
  let edits := plan .agentsMd o
  unless edits.isEmpty do
    IO.println "`lake exe regula init` would write:"
    for edit in edits do IO.println s!"  - {edit.summary project.lakefile}"
  return 1

/-- A file `init` writes, with its previous content (`none` when it did not exist). -/
private structure Written where
  path : FilePath
  previous : Option String

private def write (written : IO.Ref (Array Written)) (path : FilePath) (text : String) :
    IO Unit := do
  let previous ← Regula.Filesystem.readFileIfPresent path
  written.modify (·.push { path, previous })
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path text

/-- Restore each file of `written`, the last written first: write its previous content back, or
remove it when it did not exist, below the real path of its directory
(`Regula.Filesystem.ownRoot`). A file that cannot be restored does not stop the others; the result
names each such file with its error. -/
private def restore (written : Array Written) : IO (Array String) := do
  let mut failures := #[]
  for w in written.reverse do
    try
      match w.previous with
      | some text => IO.FS.writeFile w.path text
      | none =>
        if ← Regula.Filesystem.isPresent w.path then
          let (some directory, some name) := (w.path.parent, w.path.fileName)
            | throw <| IO.userError "it has no directory and name"
          Regula.Filesystem.removeOwn .file ((← Regula.Filesystem.ownRoot directory) / name)
    catch error => failures := failures.push s!"{w.path} ({error})"
  return failures

/-- Write the plan's edits into the project's files. -/
private def realize (written : IO.Ref (Array Written)) (project : Project) (edits : List Edit) :
    IO Unit := do
  let root := project.root
  if edits.any (fun e => e == .driver || !e.entries.isEmpty || e.added?.isSome ||
      e.library?.isSome) then
    let input ← IO.FS.readFile project.configFile
    write written project.configFile (← lakefileText project input edits)
  for edit in edits do
    match edit with
    | .manifest =>
      let inventory ← Lake.surfaceInventory root
      let manifest := starterManifest inventory
      let text := manifestText manifest
      -- The parser the audit runs must read the text back as exactly this manifest before it is
      -- written.
      let parsed ← IO.ofExcept <| Manifest.parse "foundation_manifest.json" text
      unless Regula.JsonAgreement.conforms (Manifest.toJson parsed) (Manifest.toJson manifest) do
        throw <| IO.userError "the starter manifest text does not read back as the starter"
      write written (Manifest.defaultPath root) text
    | .agentsSection _ =>
      let path := project.guidance.path
      let previous := (← Regula.Filesystem.readFileIfPresent path).getD ""
      let separator := if previous.isEmpty then "" else
        if previous.endsWith "\n\n" then "" else if previous.endsWith "\n" then "\n" else "\n\n"
      write written path (previous ++ separator ++ agentsSectionFor project.guidance.project)
    | .skill p => write written (root / p) Regula.Guidance.skill
    | _ => pure ()

/-- Write the missing setup of the project at `root` with guidance preference `g`, confirm that
the plan of the project as written is empty and that no library the plan gave a glob leaves out a
module, and run `doctor`. Any failure restores the files written (`restore`), and its error names
each file that could not be restored. -/
def init (g : Guidance) (root : FilePath) : IO UInt32 := do
  let project ← observe root
  let edits := plan g project.observation
  if edits.isEmpty then
    IO.println "regula init: nothing to write"
  else
    let written ← IO.mkRef #[]
    try
      realize written project edits
      let after ← observe root
      let left := plan g after.observation
      unless left.isEmpty do
        throw <| IO.userError s!"the files as written still need: \
          {", ".intercalate (left.map (·.summary project.lakefile))}"
      let globbed := edits.filterMap Edit.library?
      for (library, _, modules) in after.observation.uncovered do
        if globbed.contains library then
          throw <| IO.userError s!"the glob written for lean_lib `{library}` still leaves out \
            {", ".intercalate modules}"
      -- `arguedBy_run`: the plan adds no option to a claimed target that sets it only with a `-D`.
      for t in after.observation.targets do
        let some t₀ := project.observation.targets.find? fun t₀ =>
            t₀.exe == t.exe && t₀.name == t.name
          | continue
        unless after.observation.arguedBy t == project.observation.arguedBy t₀ do
          throw <| IO.userError s!"the files as written change which required options claimed \
            {if t.exe then "lean_exe" else "lean_lib"} `{t.name}` sets only with a `-D`"
    catch error =>
      let failures ← restore (← written.get)
      if failures.isEmpty then
        throw <| IO.userError s!"{error}; every file init wrote is restored"
      throw <| IO.userError s!"{error}; init could not restore \
        {", ".intercalate failures.toList}; every other file init wrote is restored"
    for edit in edits do
      match edit with
      | .skill p =>
        if project.observation.skills.any (·.1 == p) then
          IO.println s!"regula init: replaced {p} with the installed Regula's skill (init owns \
            this file; local edits are not kept)"
        else IO.println s!"regula init: wrote {edit.summary project.lakefile}"
      | .agentsSection a =>
        let created :=
          if project.guidance.present then ""
          else if project.guidance.repository then
            s!", creating {a} at the repository root: no AGENTS.md exists from the Lake project \
              up to it"
          else s!", creating {a}: no AGENTS.md exists and no Git repository contains the project"
        IO.println s!"regula init: wrote {edit.summary project.lakefile}{created}"
      | _ => IO.println s!"regula init: wrote {edit.summary project.lakefile}"
  doctor root

end Regula.Cli.Setup
