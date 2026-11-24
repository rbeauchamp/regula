module

public import Regula.Effect
public import Regula.Language
public import Regula.Load

public section

namespace Regula.Reader

open Lean (Name Syntax Import MessageLog)
open Lean.Parser (InputContext ModuleParserState mkInputContext isTerminalCommand)
open System (FilePath)
open Regula.Language
open Regula.Effect

variable {L E : Type}

abbrev Attempt (L E α : Type) : Type := ExceptT String (Prog L E) α

def attempt {α : Type} (step : Prog L E (Except IO.Error α)) : Attempt L E α :=
  ExceptT.mk do
    match ← step with
    | .ok a => pure (.ok a)
    | .error e => pure (.error (toString e))

def say (text : String) : Prog L E Unit := do
  let _ ← Prog.call (.println ("  " ++ Regula.Closed.detailText text))
  pure ()

def sayAll : List String → Prog L E Unit
  | [] => pure ()
  | l :: rest => do
    say l
    sayAll rest

def realPath (path : FilePath) : Attempt L E FilePath :=
  attempt (Prog.call (.realPath path))

def requireEnv (name : String) (why : String) : Attempt L E String :=
  ExceptT.mk do
    match ← (Prog.call (.getEnv name) : Prog L E (Option String)) with
    | some value => pure (.ok value)
    | none => pure (.error why)

def fileOf (root : Root L) (modules : List (Name × FilePath)) (m : Name) : Option FilePath :=
  match modules.lookup m with
  | some file => some file
  | none => root.resolve m

def tablesIn (xs : Array Lake.Toml.Value) : List Lake.Toml.Table :=
  xs.toList.filterMap fun
    | .table _ sub => some sub
    | _ => none

def keysOf (fuel : Nat) (pre : Name) (t : Lake.Toml.Table) : List Name :=
  match fuel with
  | 0 => [.str pre "too deep"]
  | fuel + 1 =>
    t.items.toList.flatMap fun (k, v) =>
      let key := pre ++ k
      let under (sub : Lake.Toml.Table) : List Name :=
        if sub.items.isEmpty then [key] else keysOf fuel key sub
      match v with
      | .table _ sub => under sub
      | .array _ xs =>
        if (tablesIn xs).isEmpty then [key] else (tablesIn xs).flatMap under
      | _ => [key]

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

structure Source where
  path : FilePath
  text : String
  input : InputContext
  header : Syntax
  state : ModuleParserState
  messages : MessageLog
  imports : Array Import

def readExact (project path : FilePath) : Attempt L E String := do
  let real ← realPath path
  if Regula.Load.exactBelow project path real then
    attempt (Prog.call (.readFile path))
  else
    throw s!"{path} is not, by its real path, this same path below the project"

def joinParts (dir : FilePath) (parts : List String) : FilePath :=
  parts.foldl (fun d p => d.join (FilePath.mk p)) dir

def inTree (tree path : FilePath) : Bool :=
  (treeRelative (Regula.Load.parts tree) (Regula.Load.parts path)).isSome

def apart (a b : FilePath) : Bool :=
  !(Regula.Load.parts a).isPrefixOf (Regula.Load.parts b) &&
    !(Regula.Load.parts b).isPrefixOf (Regula.Load.parts a)

def makeParent (tree path : FilePath) : Attempt L E Unit :=
  match path.parent with
  | none => pure ()
  | some dir =>
    if inTree tree dir then
      attempt (Prog.call (.createDirAll dir))
    else
      throw s!"{dir} does not lie below the checker's tree"

def writeInTree (tree path : FilePath) (text : String) : Attempt L E Unit :=
  if inTree tree path then do
    makeParent tree path
    attempt (Prog.call (.writeFile path text))
  else
    throw s!"{path} does not lie below the checker's tree"

def parentInTree (tree path : FilePath) : Bool :=
  match path.parent with
  | none => true
  | some dir => inTree tree dir

def readForTree (project tree path : FilePath) : Attempt L E String :=
  match treeRelative (Regula.Load.parts tree) (Regula.Load.parts path) with
  | none => throw s!"{path} does not lie below the checker's tree"
  | some rel =>
    if parentInTree tree path then
      readExact project (joinParts project rel)
    else
      throw s!"the directory above {path} does not lie below the checker's tree"

def readSource (project tree path : FilePath) : Attempt L E Source := do
  let text ← readForTree project tree path
  let input := mkInputContext text (Regula.Load.inputName path)
  let (header, state, messages, imports) ← attempt (Prog.call (.parseHeader input))
  pure { path, text, input, header, state, messages, imports }

def plannedOf (config : List (FilePath × String)) (sources : List (Name × Source)) : List (Name × FilePath × String) :=
  config.map (fun (path, text) => (`config, path, text)) ++ sources.map fun (m, s) => (m, s.path, s.text)

def twoTexts (planned : List (Name × FilePath × String)) : List (Name × String) :=
  let clash := planned.filter fun (_, path, text) =>
    planned.any fun (_, other, text') =>
      Regula.Load.parts path == Regula.Load.parts other && text != text'
  clash.map fun (m, path, _) => (m, s!"its file {path} would hold two texts")

def writeSources (tree : FilePath) : List (Name × Source) → Attempt L E Unit
  | [] => pure ()
  | (_, s) :: rest => do
    writeInTree tree s.path s.text
    writeSources tree rest

def readBack : List (FilePath × String) → Attempt L E Unit
  | [] => pure ()
  | (path, text) :: rest => do
    let held ← attempt (Prog.call (.readFile path))
    if held == text then
      readBack rest
    else
      throw s!"{path} does not hold the text written to it"

def toolchainOLean (path : List FilePath) (m : Name) : Attempt L E Unit := do
  let _ ← attempt (Prog.call (.findOLean path m))
  pure ()

structure Walk where
  reached : List Name := []
  sources : List (Name × Source) := []
  toolchain : List Name := []
  unread : List (Name × String) := []

def Walk.leaveUnread (w : Walk) (m : Name) (why : String) : Walk :=
  { w with reached := m :: w.reached, unread := (m, why) :: w.unread }

def walk (project tree : FilePath) (root : Root L) (modules : List (Name × FilePath)) :
    Nat → List Name → Walk → Prog L E Walk
  | _, [], w => pure w
  | 0, m :: _, w => pure (w.leaveUnread m "the imports reach too many modules")
  | fuel + 1, m :: rest, w =>
    if w.reached.contains m || w.toolchain.contains m then
      walk project tree root modules fuel rest w
    else if !closedModuleName m then
      walk project tree root modules fuel rest
        (w.leaveUnread m "its name is outside the closed domain")
    else if m.getRoot == `Mathlib then
      walk project tree root modules fuel rest { w with reached := m :: w.reached }
    else
      match fileOf root modules m with
      | some path => do
        match ← (readSource project tree path).run with
        | .ok s =>
          walk project tree root modules fuel (s.imports.toList.map (·.module) ++ rest)
            { w with reached := m :: w.reached, sources := (m, s) :: w.sources }
        | .error e => walk project tree root modules fuel rest (w.leaveUnread m e)
      | none => do
        match ← (toolchainOLean root.toolchain m).run with
        | .ok _ =>
          walk project tree root modules fuel rest { w with toolchain := m :: w.toolchain }
        | .error e =>
          walk project tree root modules fuel rest
            (w.leaveUnread m s!"neither Lake nor the toolchain holds it: {e}")

def existsByName (path : FilePath) : Attempt L E Bool :=
  ExceptT.mk do
    match ← (Prog.call (.symlinkMetadata path) : Prog L E (Except IO.Error IO.FS.Metadata)) with
    | .ok _ => pure (.ok true)
    | .error (.noFileOrDirectory ..) => pure (.ok false)
    | .error e => pure (.error (toString e))

def noOtherConfig (tree : FilePath) : Attempt L E Unit := do
  if ← existsByName (tree / "lakefile.lean") then
    throw "something answers to `lakefile.lean` in the checker's tree, and Lake would take it as its \
      configuration in place of the `lakefile.toml` read: rename the file that the file system takes for it"
  else
    pure ()

abbrev ParserCache (E : Type) : Type := List (List Name × (E × List Name))

def environmentFor (path : List FilePath) (cache : ParserCache E) (mods : List Name) :
    Attempt L E ((E × List Name) × ParserCache E) := do
  let key := mods.eraseDups
  match cache.lookup key with
  | some pair => pure (pair, cache)
  | none =>
    let pair ← attempt (Prog.call (.importForParser path key))
    pure (pair, (key, pair) :: cache)

def parseFile (path : List FilePath) (cache : ParserCache E) (sources : List (Name × Source)) (toolchain : List Name) (m : Name)
    (s : Source) : Attempt L E (FileRead × ParserCache E) := do
  let headers := fun n => (sources.lookup n).map (·.imports)
  let direct := s.imports.toList.map (·.module)
  let fuel := direct.length + (sources.map (·.2.imports.size)).sum + 1
  let mods := visibleToolchain headers toolchain.contains direct [] fuel
  let ((env, scopedParsers), cache') ← environmentFor path cache mods
  let (commands, final) ← ExceptT.lift
    (parseAll s.input env s.state s.messages (s.input.inputString.utf8ByteSize + 1))
  pure ({ module := m, header := s.header, commands, parsed := !final.hasErrors, scopedParsers }, cache')

def parseFiles (path : List FilePath) (sources : List (Name × Source)) (toolchain : List Name) (cache : ParserCache E) :
    List (Name × Source) → Attempt L E (List FileRead)
  | [] => pure []
  | (m, s) :: rest => do
    let (file, cache') ← parseFile path cache sources toolchain m s
    let files ← parseFiles path sources toolchain cache' rest
    pure (file :: files)

def toolchainOf (project : FilePath) : Prog L E (Option String) := do
  match ← (readExact project (project / "lean-toolchain")).run with
  | .ok text => pure (some text.trimAscii.toString)
  | .error _ => pure none

def closedSourceDir (tree dir : FilePath) : Bool :=
  match treeRelative (Regula.Load.parts tree) (Regula.Load.parts dir) with
  | some rel => rel.all closedComponent
  | none => false

def openPathsOf (tree : FilePath) (root : Root L) : List String :=
  let single : Lake.Glob → Bool
    | .one _ => true
    | _ => false
  let dirs := (root.sourceDirs.filter (!closedSourceDir tree ·)).eraseDups.map
    fun dir => s!"the source directory {dir} is not a path below the project whose names hold only ASCII letters, digits, `_` and `'`"
  let globs := (root.libraries.filter (!·.2.all single)).map fun (lib, _) =>
    s!"the library {lib}: a `globs` entry other than a single module needs a directory listing"
  let targets := (root.defaultTargets.filter fun target => (root.findLib target).isNone).map
    fun target => s!"the default target {target} is not a library"
  dirs ++ globs ++ targets

def configUnread (tree : FilePath) (root : Root L) (modules : List (Name × FilePath)) : List (Name × String) :=
  let names := (root.targets.filter (!closedModuleName ·)).map
    fun n => (n, "this target's name is outside the closed domain")
  let others := modules.filter fun (m, file) =>
    match root.resolve m with
    | some other => Regula.Load.parts other != Regula.Load.parts file
    | none => true
  let named := modules.flatMap fun (m, file) => (m, file) :: (root.resolve m).toList.map (m, ·)
  let outside := named.filter fun (_, path) => !inTree tree path || !parentInTree tree path
  names ++ others.map (fun (m, file) => (m, s!"Lake's resolution of an import does not give this name the file {file}")) ++
    outside.map fun (m, path) => (m, s!"its file {path} does not lie below the checker's tree")

def modulesOfTarget (root : Root L) (target : Name) : Attempt L E (List (Name × FilePath)) :=
  match root.findLib target with
  | some lib => do
    let listed ← attempt (Prog.call (.libModules lib))
    pure (Array.toList listed)
  | none =>
    match root.findExe target with
    | some m => pure [m]
    | none => pure []

def defaultModules (root : Root L) : List Name → Attempt L E (List (Name × FilePath))
  | [] => pure []
  | target :: targets => do
    let here ← modulesOfTarget root target
    let rest ← defaultModules root targets
    pure (here ++ rest)

def loaded (what : String) : Except String (Option (Root L) × List String) → Except String (Root L)
  | .error why => .error why
  | .ok (some root, _) => .ok root
  | .ok (none, log) => .error s!"Lake could not load {what}: {"; ".intercalate log}"

def readFiles (config : List (FilePath × String)) (project tree : FilePath) (root : Root L)
    (modules : List (Name × FilePath)) (cfg : ClosedConfig) :
    Attempt L E (Stage × List (Name × Source)) := do
  let w ← ExceptT.lift (walk project tree root modules 1000000 (modules.map (·.1)) {})
  let roots := modules.map (·.1)
  let reached := w.reached.reverse
  let unread := w.unread.reverse ++ twoTexts (plannedOf config w.sources.reverse)
  match hu : unread.isEmpty with
  | false => pure (.unread cfg roots reached unread hu, [])
  | true =>
    match hm : reached.any (·.getRoot == `Mathlib) with
    | true => pure (.mathlib cfg roots reached hm, [])
    | false =>
      let files ← parseFiles root.toolchain w.sources.reverse w.toolchain [] w.sources.reverse
      let stage := Stage.ofFiles cfg roots reached files hm
      match stage with
      | .admitted .. =>
        writeSources tree w.sources.reverse
        readBack (config ++ w.sources.reverse.map fun x => (x.2.path, x.2.text))
        noOtherConfig tree
        pure (stage, w.sources.reverse)
      | _ => pure (stage, w.sources.reverse)

def readRoot (config : List (FilePath × String)) (sysroot : String) (project tree : FilePath)
    (cfg : ClosedConfig) : Attempt L E (Stage × List (Name × Source)) := do
  let root ← ExceptT.mk (Prog.bind (Prog.call (.loadRoot sysroot tree)) fun r =>
    pure (loaded "the configuration" r))
  let openPaths := openPathsOf tree root
  match ho : openPaths.isEmpty with
  | false => pure (Stage.mkOpenPaths cfg openPaths ho, [])
  | true =>
    let modules ← defaultModules root root.defaultTargets
    let failures := configUnread tree root modules
    match hf : failures.isEmpty with
    | false => pure (.unread cfg (modules.map (·.1)) [] failures hf, [])
    | true => readFiles config project tree root modules cfg

def readKeys (sysroot : String) (project tree : FilePath) (toolchainFile : Option String) (text : String) :
    Attempt L E (Stage × List (Name × Source)) := do
  match ← ExceptT.lift (Prog.call (.parseToml (mkInputContext text "lakefile.toml")) :
      Prog L E (Except MessageLog Lake.Toml.Table)) with
  | .error _ =>
    pure (Stage.earlyUnread toolchainFile "Lake's TOML parser refused lakefile.toml", [])
  | .ok table =>
    match Stage.ofConfig toolchainFile (keysOf 8 .anonymous table) with
    | .error stage => pure (stage, [])
    | .ok cfg =>
      writeInTree tree (tree / "lakefile.toml") text
      writeInTree tree (tree / "lean-toolchain") leanToolchain
      readRoot [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] sysroot project tree cfg

def readConfig (sysroot : String) (project tree : FilePath) (toolchainFile : Option String) :
    Attempt L E (Stage × List (Name × Source)) := do
  if ← existsByName (project / "lakefile.lean") then
    pure (Stage.mkLeanConfig toolchainFile, [])
  else
    match ← ExceptT.lift (readExact project (project / "lakefile.toml")).run with
    | .error e => pure (Stage.earlyUnread toolchainFile s!"lakefile.toml: {e}", [])
    | .ok text => readKeys sysroot project tree toolchainFile text

def readProjectStage (sysroot : String) (dir treeDir : FilePath) :
    Attempt L E (Stage × List (Name × Source)) := do
  let project ← realPath dir
  let tree ← realPath treeDir
  let toolchainFile ← ExceptT.lift (toolchainOf project)
  if !apart project tree then
    pure (Stage.earlyUnread toolchainFile "the checker's tree and the project do not lie apart", [])
  else
    readConfig sysroot project tree toolchainFile

def readProject (sysroot : String) (dir treeDir : FilePath) :
    Attempt L E (Reading × List (Name × Source)) := do
  let (stage, sources) ← readProjectStage sysroot dir treeDir
  pure (stage.toReading, sources)

def lineOf (s : Source) (stx : Syntax) : Nat :=
  match stx.getPos? with
  | some p => (s.input.fileMap.toPosition p).line
  | none => 0

def describe : Syntax → String
  | .missing => "a place Lean's parser could not fill"
  | .atom _ v => s!"the token `{v}`"
  | .ident _ _ n _ => s!"the name `{n}`"
  | .node _ k _ => s!"the construct {k}"

def findingLines (r : Reading) (sources : List (Name × Source)) (limit : Nat) : List String :=
  let rule := "RG1010"
  let toolchain :=
    if r.toolchainFile != some leanToolchain then
      [s!"{rule} lean-toolchain: it must say {leanToolchain}"]
    else []
  let paths := r.openPaths.map fun p => s!"{rule} {p}"
  let config := toolchain ++ paths ++
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

def read (sysroot : String) (dir treeDir : FilePath) : Attempt L E (Reading × List String) := do
  let (r, sources) ← readProject sysroot dir treeDir
  pure (r, findingLines r sources 50)

end Regula.Reader
