import Regula.Checker.AxiomGate
import RegulaCore.Guidance
import Lake.Toml.Grammar
import Lean.Elab.Frontend

/-! # `regula init` and `regula doctor`

`init` writes the setup a project is missing, and `doctor` reports every missing or wrong piece
with its fix. Both execute the proved decision of `RegulaCore.Setup` over what they observe:
`init` writes exactly the edits of `Regula.Setup.plan` (so `plan_idempotent` says what a second
run writes: nothing), and `doctor` prints `Regula.Setup.issues` together with the linter's own
RG2002 manifest validation and RG2006 option decision, in the linter's finding text.

## Main declarations

- `observe`: the `Regula.Setup.Observation` of a project, from Lake's loaded package and the files.
- `lakefileText`: the lakefile with the planned `lintDriver` and `leanOptions` edits written into
  it, located with Lake's own TOML grammar or Lean's parser over the `package` declaration.
- `starterManifest`: every root `lean_lib` claimed `standard-logical`, as a `Manifest` value that
  `Manifest.parse` admits before it is written.
- `init`: apply the plan, observe again and restore every written file unless the new plan is
  empty; then run `doctor`.
- `doctor`: print the findings and the edits `init` would write; exit 0 only when there is none.

## Boundaries

Lake's loader, the parsers, the filesystem and the Lean frontend that locates the `package`
declaration are trusted. That a text edit realizes `Regula.Setup.apply` is not proved: `init`
observes the project again after writing and refuses, restoring the files it wrote, unless the
plan of the new observation is empty. `init` never changes a value the project already gives: it
inserts text only. RG2006 in `doctor` applies Mathlib's options when the workspace contains
Mathlib, where the linter applies them to a target whose modules import Mathlib; by
`RegulaPolicy.Community.conforming_of_mathlib`, a target `doctor` accepts also passes the
linter's decision. -/

namespace Regula.Cli.Setup

open Lean System
open Regula.Setup
open Regula.Checker
open RegulaPolicy.Community (OptionValue)

/-- What the commands read of a project in one observation. -/
structure Project where
  /-- The project root. -/
  root : FilePath
  /-- The root package's configuration format. -/
  lakefile : Lakefile
  /-- The root package's configuration file. -/
  configFile : FilePath
  /-- The facts the setup decision reads. -/
  observation : Observation

/-- Whether `text` has `agentsHeading` as one of its lines. -/
def hasAgentsHeading (text : String) : Bool :=
  (text.splitOn "\n").any fun line => line == agentsHeading || line == agentsHeading ++ "\r"

private def readTrimmed (path : FilePath) : IO String := do
  if ← path.pathExists then return (← IO.FS.readFile path).trimAscii.toString
  return ""

/-- Observe the project at `root`: Lake's loaded root package (its `lintDriver` and package-level
`leanOptions`), whether the workspace contains Mathlib, the required Regula's `lean-toolchain`,
and the manifest and agent-guidance files. -/
def observe (root : FilePath) : IO Project := do
  let (lakefile, configFile, driver, options, targets, mathlib, regulaDir, uncovered) ←
    Workspace.withRootWorkspace root fun ws => do
      let pkg := ws.root
      -- The modules below each library root that no root library includes.
      let mut included : NameSet := {}
      for lib in pkg.leanLibs do
        for m in ← lib.getModuleArray do included := included.insert m.name
      for exe in pkg.leanExes do included := included.insert exe.root.name
      let mut uncovered := []
      for lib in pkg.leanLibs do
        let mut missed : Array Name := #[]
        for r in lib.roots do
          let dir := Lean.modToFilePath lib.srcDir r ""
          unless ← dir.isDir do continue
          for path in ← dir.walkDir do
            if path.extension != some "lean" || (← path.isDir) then continue
            let parts := (path.withExtension "").components.drop dir.components.length
            let name := parts.foldl Name.str r
            unless included.contains name do missed := missed.push name
        unless missed.isEmpty do
          let sorted := (missed.qsort Name.quickLt).toList.map toString
          uncovered := uncovered ++ [(lib.name.toString, lib.roots.toList.map toString, sorted)]
      let own (options : Array Lean.LeanOption) :=
        (Lake.buildOptions (.ofArray options) #[] #[]).options
      let kind := if pkg.configFile.extension == some "toml" then Lakefile.toml else .lean
      let regulaDir := match ws.packages.find? (·.baseName == `regula) with
        | some regula => regula.dir
        | none => pkg.dir
      return (kind, pkg.configFile, pkg.lintDriver,
        (Lake.buildOptions pkg.leanOptions #[] #[]).options,
        (pkg.leanLibs.map (own ·.config.leanOptions) ++
          pkg.leanExes.map (own ·.config.leanOptions)).toList,
        ws.packages.any (·.baseName == `mathlib), regulaDir, uncovered)
  let agents := root / "AGENTS.md"
  let agentsSection ← if ← agents.pathExists then pure (hasAgentsHeading (← IO.FS.readFile agents))
    else pure false
  let skills ← skillPaths.filterMapM fun (p : String) => do
    let path := root / p
    if ← path.pathExists then
      return some (p, (← IO.FS.readFile path) == Regula.Guidance.skill)
    return none
  return {
    root, lakefile, configFile
    observation := {
      driver, options, targets, mathlib
      manifest := ← (Manifest.defaultPath root).pathExists
      agentsSection, skills
      toolchain := ← readTrimmed (root / "lean-toolchain")
      supported := ← readTrimmed (regulaDir / "lean-toolchain")
      uncovered } }

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

/-- Where a `lakefile.toml` receives the edits: after the last top-level key, into an existing
`[leanOptions]` table or inline `leanOptions` table. -/
private structure TomlPlaces where
  topEnd : Option Nat := none
  table : Option Nat := none
  inline : Option (Nat × Bool) := none
  unsupported : Bool := false

/-- `lakefile.toml` with the planned edits: `lintDriver` as a new last top-level key, and the
missing options appended to the `[leanOptions]` table, to an inline `leanOptions` table, or in a
new `[leanOptions]` table after the top-level keys. A `leanOptions` written with dotted top-level
keys or as sub-tables is refused, with the entries to add by hand. -/
def tomlText (input : String) (driver : Bool) (entries : List (Name × OptionValue)) :
    IO String := do
  let ictx := Parser.mkInputContext input "lakefile.toml"
  let env ← mkEmptyEnvironment
  let s := Lake.Toml.toml.fn.run ictx { env, options := {} } {}
    (Parser.mkParserState ictx.inputString)
  if let some error := s.errorMsg then
    throw <| IO.userError s!"lakefile.toml does not parse: {error}"
  let stx := s.stxStack.back
  let expressions := stx[1].getArgs.filter fun e => !e.isOfKind nullKind
  let places ← IO.ofExcept <| expressions.foldlM (init := ({}, none))
    (fun ((p : TomlPlaces), (table : Option String)) e => do
      let key ← sourceText input e[0]
      let keyOf (t : Syntax) : Except String String := do
        return (← sourceText input t).replace " " ""
      if e.isOfKind `Lake.Toml.stdTable then
        let name ← keyOf e[1]
        let headerEnd := lineEnd input (← endOf e)
        let p := if name == "leanOptions" then { p with table := some headerEnd }
          else if name.startsWith "leanOptions." then { p with unsupported := true } else p
        return (p, some name)
      if e.isOfKind `Lake.Toml.arrayTable then
        return (p, some "")
      let name := key.replace " " ""
      match table with
      | none =>
        let p := { p with topEnd := some (lineEnd input (← endOf e)) }
        if name == "leanOptions" then
          let value := e[2]
          if value.isOfKind `Lake.Toml.inlineTable then
            let pairs := value[1].getArgs.filter fun x => x.isOfKind `Lake.Toml.keyval
            if let some lastPair := pairs.back? then
              return ({ p with inline := some (← endOf lastPair, true) }, table)
            return ({ p with inline := some (← startOf value[2], false) }, table)
          return ({ p with unsupported := true }, table)
        if name.startsWith "leanOptions." then return ({ p with unsupported := true }, table)
        return (p, table)
      | some "leanOptions" => return ({ p with table := some (lineEnd input (← endOf e)) }, table)
      | some _ => return (p, table))
  let places := places.1
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
  IO.ofExcept <| splice input (driverText ++ optionText)

/-- The `package` command of a `lakefile.lean`, located by Lean's parser as Lake elaborates the
file (with the file's own imports and `open` commands in effect). -/
def packageCommand (path : FilePath) (input : String) : IO Syntax := do
  initializeLeanSearchPath
  -- The file's `import Lake` runs Lake's initializers, as when Lake loads it.
  unsafe Lean.enableInitializersExecution
  let inputCtx := Parser.mkInputContext input path.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← Elab.processHeader header {} messages inputCtx (mainModule := `lakefile)
  let env := Lake.dirExt.setState env (some ((path.parent.getD ".")))
  let env := Lake.optsExt.setState env (some {})
  let s ← Elab.IO.processCommands inputCtx parserState (Elab.Command.mkState env messages {})
  match s.commands.find? (·.getKind == `Lake.DSL.packageCommand) with
  | some command => return command
  | none =>
    let errors ← (s.commandState.messages.toList.filter (·.severity == .error)).mapM (·.toString)
    throw <| IO.userError s!"{path}: Lean found no `package` declaration\
      {String.join (errors.take 3 |>.map ("\n" ++ ·))}"

/-- The configuration fields of a `package` declaration, in source order. -/
partial def declFields (stx : Syntax) : Array Syntax :=
  if stx.getKind == `Lake.DSL.declField then #[stx]
  else stx.getArgs.foldl (fun acc a => acc ++ declFields a) #[]

/-- Whether `stx` contains a node of `kind`. -/
partial def containsKind (stx : Syntax) (kind : SyntaxNodeKind) : Bool :=
  stx.getKind == kind || stx.getArgs.any (containsKind · kind)

/-- `lakefile.lean` with the planned edits in its `package` declaration: `lintDriver` as a new
last field, and the missing options appended to the `leanOptions` array literal, appended to any
other `leanOptions` term with `++`, or as a new last field. -/
def leanText (path : FilePath) (input : String) (driver : Bool)
    (entries : List (Name × OptionValue)) : IO String := do
  let command ← packageCommand path input
  let fields := declFields command
  let structForm := containsKind command `Lake.DSL.declValStruct
  let whereForm := containsKind command `Lake.DSL.declValWhere
  let rendered := entries.map (Lakefile.lean.entry ·)
  let optionsField := fields.find? fun f => f[0].getId == `leanOptions
  -- The new fields; a new `leanOptions` array puts one entry per line below the field when the
  -- fields are written one per line at indentation `indent`.
  let newFields (indent : Option String) : List String :=
    (if driver then ["lintDriver := \"" ++ lintDriver ++ "\""] else []) ++
    (if optionsField.isNone && !entries.isEmpty then
      match indent with
      | some i =>
        ["leanOptions := #[" ++ ",".intercalate (rendered.map (("\n" ++ i ++ "  ") ++ ·)) ++ "]"]
      | none => ["leanOptions := #[" ++ ", ".intercalate rendered ++ "]"]
    else [])
  let fieldInsertions ← IO.ofExcept <| do
    if (newFields none).isEmpty then return []
    match fields.back? with
    | some last =>
      if structForm then
        return [(← endOf last, String.join ((newFields none).map ("; " ++ ·)))]
      let indent := "".pushn ' ' (column input (← startOf fields[0]!))
      return [(lineEnd input (← endOf last),
        String.join ((newFields (some indent)).map (("\n" ++ indent) ++ ·)))]
    | none =>
      if whereForm || structForm then
        throw "the `package` declaration has an empty configuration; add the fields by hand"
      -- `package name` with no configuration: open a `where` block after the name.
      return [(← endOf command,
        " where" ++ String.join ((newFields (some "  ")).map ("\n  " ++ ·)))]
  let optionInsertions ← IO.ofExcept <| do
    match optionsField with
    | none => return []
    | some field =>
      if entries.isEmpty then return []
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
          return [(← endOf last, String.join (rendered.map (sep ++ ·)))]
        | _, _ => return [(← endOf value[0], ", ".intercalate rendered)]
      | _ => return [(← startOf value, "("),
          (← endOf value, ") ++ #[" ++ ", ".intercalate rendered ++ "]")]
  -- At one position, an edit inside the `leanOptions` value precedes a new field after it.
  IO.ofExcept <| splice input (optionInsertions ++ fieldInsertions)

/-- The lakefile text after the plan's `lintDriver` and `leanOptions` edits. -/
def lakefileText (project : Project) (input : String) (edits : List Edit) : IO String := do
  let driver := edits.contains .driver
  let entries := edits.flatMap Edit.entries
  match project.lakefile with
  | .toml => tomlText input driver entries
  | .lean => leanText project.configFile input driver entries

/-! ## The starter manifest -/

/-- The rationale of every starter claim. -/
def starterRationale : String :=
  "Starter claim written by `lake exe regula init`: every declaration may use propext, " ++
  "Quot.sound and Classical.choice, and compiled boundaries are reported. Replace this with " ++
  "the reason for the claim, and strengthen it where the library allows."

/-- Every root `lean_lib` claimed `standard-logical` with `report` execution; every root
`lean_exe` is claimed with the first library. -/
def starterManifest (inventory : Lake.SurfaceInventory) : Manifest :=
  let exes := inventory.executables.map (·.executable)
  { surfaces := inventory.libraries.mapIdx fun i library =>
      { library := library.library, executables := if i == 0 then exes else #[]
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
target, decided by `RegulaPolicy.Community.failures` exactly as the audit decides it. -/
def configurationFindings (project : Project) : IO (Array Regula.Finding) := do
  let root := project.root
  let mode : EvidenceMode := .incrementalProject
  try
    let manifest ← Manifest.load (Manifest.defaultPath root)
    let inventory ← Lake.surfaceInventory root
    discard <| IO.ofExcept <| Acceptance.surfaceAssignments manifest inventory
    AxiomGate.checkClassification manifest inventory
    let mut findings := #[]
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
          let d ← IO.ofExcept <| Regula.makeDiagnostic .communityConfiguration
            ⟨target, RegulaPolicy.Community.detail failed⟩ (.project root.toString) mode
            (some surface.claim.toString) .violation
          findings := findings.push ⟨.communityConfiguration, d⟩
    return findings
  catch error =>
    let configuration := error.toString.startsWith "manifest-"
    let finding ← IO.ofExcept <| Regula.Findings.contextFinding
      (if configuration then .configuration else .environment) root.toString error.toString mode
      (if configuration then .violation else .incomplete)
    return #[finding]

/-- Print every setup finding of the project at `root`, then the edits `init` would write.
Returns 0 when there is nothing to fix and 1 otherwise. -/
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
  let previous ← if ← path.pathExists then some <$> IO.FS.readFile path else pure none
  written.modify (·.push { path, previous })
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path text

private def restore (written : Array Written) : IO Unit := do
  for w in written.reverse do
    match w.previous with
    | some text => IO.FS.writeFile w.path text
    | none => if ← w.path.pathExists then IO.FS.removeFile w.path

/-- Write the plan's edits into the project's files. -/
private def realize (written : IO.Ref (Array Written)) (project : Project) (edits : List Edit) :
    IO Unit := do
  let root := project.root
  if edits.any (fun e => e == .driver || !e.entries.isEmpty) then
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
      unless (Manifest.toJson parsed).compress == (Manifest.toJson manifest).compress do
        throw <| IO.userError "the starter manifest text does not read back as the starter"
      write written (Manifest.defaultPath root) text
    | .agentsSection =>
      let path := root / "AGENTS.md"
      let previous ← if ← path.pathExists then IO.FS.readFile path else pure ""
      let separator := if previous.isEmpty then "" else
        if previous.endsWith "\n\n" then "" else if previous.endsWith "\n" then "\n" else "\n\n"
      write written path (previous ++ separator ++ agentsSection)
    | .skill p => write written (root / p) Regula.Guidance.skill
    | _ => pure ()

/-- Write the missing setup of the project at `root` with guidance preference `g`, confirm that
the plan of the project as written is empty, and run `doctor`. Any failure restores the files
written. -/
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
    catch error =>
      restore (← written.get)
      throw <| IO.userError s!"{error}; every file init wrote is restored"
    for edit in edits do IO.println s!"regula init: wrote {edit.summary project.lakefile}"
  doctor root

end Regula.Cli.Setup
