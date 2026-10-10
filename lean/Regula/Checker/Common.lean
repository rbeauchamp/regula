import Regula.Checker.Producer
import Regula.Checker.PolicyCodec
import Regula.Scratch
import RegulaPolicy.ResultState
import Lean
import Lake.Load.Manifest
import Std.Sync.Mutex

/-! # Shared checker support

Shared process, path, JSON, and bounded-concurrency support. -/

namespace Regula.Checker

open Lean System

/-- The observed outcome of one finished child process. -/
structure ProcessResult where
  /-- The exit code the process returned. -/
  exitCode : UInt32
  /-- Everything the process wrote to standard output. -/
  stdout : String
  /-- Everything the process wrote to standard error. -/
  stderr : String
  deriving Repr

instance : ToJson ProcessResult where
  toJson value := Json.mkObj [
    ("exitCode", toJson value.exitCode.toNat),
    ("stdout", toJson value.stdout), ("stderr", toJson value.stderr)]

instance : FromJson ProcessResult := ⟨fun value => do
  PolicyCodec.exactFields value ["exitCode", "stdout", "stderr"]
  let code : Nat ← value.getObjValAs? Nat "exitCode"
  if code >= 2^32 then throw "invalid process exit code"
  return {
    exitCode := UInt32.ofNat code,
    stdout := ← value.getObjValAs? String "stdout", stderr :=
        ← value.getObjValAs? String "stderr" }⟩

namespace ProcessResult

/-- Standard output followed by standard error, as one text. -/
def output (result : ProcessResult) : String :=
  result.stdout ++ result.stderr

/-- Whether the process exited with code 0. -/
def succeeded (result : ProcessResult) : Bool :=
  result.exitCode == 0

end ProcessResult

/-- Environment entries that remove the caller's inherited Lean search paths.
`lake exe` exports the invoking checkout's `LEAN_PATH`, and `lake env` appends
an inherited `LEAN_PATH` after the workspace's own entries, so a child `lake`
started without this scrub can resolve modules from the main checkout's
pre-existing build output instead of the isolated copy. -/
def scrubbedLeanPathEnv : Array (String × Option String) :=
  #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none)]

/-- Run `cmd` with `args` in directory `repo`, with the environment changes `env`, wait for it
to finish and return its exit code and captured output. -/
def runProcess (repo : FilePath) (cmd : String) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO ProcessResult := do
  let result ← IO.Process.output { cmd, args, cwd := some repo, env }
  return { exitCode := result.exitCode, stdout := result.stdout, stderr := result.stderr }

/-- The environment variable that turns timing output on in a checker process: `1` on, otherwise
off. A coordinator passes it to the workers whose output it shows (`runTypedWorker`). -/
def timingVariable : String := "REGULA_TIMING"

/-- Whether this process prints timing spans (`timedPhase`, `timingSpan`): off by default, on
with `axiomGate --verbose` (so also `lake lint -- --verbose`) or when `timingVariable` is `1`.
The spans measure the checker's own cost; they are never findings or results. -/
initialize timing : IO.Ref Bool ← do IO.mkRef ((← IO.getEnv timingVariable) == some "1")

/-- Print one timing line when timing output is on. -/
def timingSpan (line : String) : IO Unit := do
  if ← timing.get then
    IO.println line
    (← IO.getStdout).flush

/-- Lake's own progress line for one build job: the job's status icon (`LogLevel.icon`, or `✔`)
and its `[i/n]` position, as `Lake.Build.Run.reportJob` prints it without ANSI codes, such as
`✔ [3/10] Built Widget (1.2s)`. -/
def isLakeProgressLine (line : String) : Bool :=
  ["✔ [", "ℹ [", "⚠ [", "✖ ["].any fun (icon : String) => line.startsWith icon

/-- A stream that writes everything to `target` and also prints to standard output, as each line
is completed, every line `display` selects. -/
def showingStream (target : IO.FS.Stream) (display : String → Bool) : IO IO.FS.Stream := do
  let pending ← IO.mkRef ""
  let stdout ← IO.getStdout
  return { target with
    putStr := fun text => do
      target.putStr text
      let parts := ((← pending.get) ++ text).splitOn "\n"
      pending.set parts.getLast!
      for line in parts.dropLast do
        if display line then
          stdout.putStrLn line
          stdout.flush }

/-- `runProcess`, also printing to standard output each line of the child's standard output that
`display` selects (with its newline), as the child writes it. The captured output is the
child's complete output. -/
def runProcessShowing (repo : FilePath) (cmd : String) (args : Array String)
    (env : Array (String × Option String)) (display : String → Bool) : IO ProcessResult := do
  let child ← IO.Process.spawn {
    cmd, args, cwd := some repo, env, stdin := .null, stdout := .piped, stderr := .piped }
  -- Drain standard error while standard output is read, so neither pipe can block the child.
  let errors ← IO.asTask child.stderr.readToEnd .dedicated
  let stdout ← IO.mkRef ""
  let read : IO Unit := do
    repeat
      let line ← child.stdout.getLine
      if line.isEmpty then break
      stdout.modify (· ++ line)
      if display line then
        IO.print line
        (← IO.getStdout).flush
  let readResult ← read.toBaseIO
  let waited ← child.wait.toBaseIO
  let errors ← IO.wait errors
  IO.ofExcept readResult
  return {
    exitCode := ← IO.ofExcept waited, stdout := ← stdout.get, stderr := ← IO.ofExcept errors }

/-- Report elapsed wall time around an action, including exceptional completion, when timing
output is on (`timing`). -/
def timedPhase {α : Type} (label : String) (action : IO α) : IO α := do
  timingSpan s!"verification phase {label}: start"
  let start ← IO.monoNanosNow
  try action
  finally
    let elapsed ← IO.monoNanosNow
    timingSpan s!"verification phase {label}: {(elapsed - start) / 1000000}ms (finished)"

/-- The lines of `output`, split at each newline. -/
def outputLines (output : String) : Array String :=
  output.splitOn "\n" |>.toArray

/-- The pinned toolchain renders a diagnostic head as `file:l:c: warning: msg`
or, for a named diagnostic, `file:l:c: warning(name): msg`
(`Lean.mkErrorStringWithPos`); both forms are warnings. -/
def isWarningLine (line : String) : Bool :=
  let lower := line.toLower
  lower.contains "warning:" || lower.contains ": warning("

/-- Whether `line` reads, ignoring case, as an error diagnostic head: it contains `: error` or
starts with `error:`. -/
def isErrorLine (line : String) : Bool :=
  let lower := line.toLower
  lower.contains ": error" || lower.startsWith "error:"

/-- The lines of `output` that `isWarningLine` accepts. -/
def warningLines (output : String) : Array String :=
  outputLines output |>.filter isWarningLine

/-- The lines of `output` that `isErrorLine` accepts. -/
def errorLines (output : String) : Array String :=
  outputLines output |>.filter isErrorLine

/-- Lake's own progress markers, build summaries (`Lake/Build/Run.lean` in the
pinned toolchain prints `Build completed successfully` and `Some required
targets logged failures:`), and replayed `info:`/`trace:` log lines, each of
which ends a Lean diagnostic body in a `lake build` transcript. -/
private def isLakeStatusLine (line : String) : Bool :=
  #["\u2714", "\u26A0", "\u2716", "\u2139", "Build completed", "Some required targets",
    "info:", "trace:"].any
    fun marker => line.startsWith marker

/-- Every diagnostic whose head line satisfies `isHead`, together with its
body: a Lean diagnostic head (`warning:`, `error:`) is followed by
continuation lines (the unused argument, expected type, hints) up to the next
diagnostic head, Lake status line, or replayed `info:`/`trace:` line.
Trailing blank body lines are dropped. -/
def diagnosticBlocks (output : String) (isHead : String → Bool) : Array String := Id.run do
  let mut blocks : Array String := #[]
  let mut inBlock := false
  for line in outputLines output do
    if isHead line then
      inBlock := true
      blocks := blocks.push line
    else if isWarningLine line || isErrorLine line || isLakeStatusLine line then
      inBlock := false
    else if inBlock then
      blocks := blocks.push line
  while !blocks.isEmpty && blocks.back!.all (·.isWhitespace) do
    blocks := blocks.pop
  return blocks

/-- The nearest ancestor of `start` (itself included) holding one Lake configuration file and
a `lean-toolchain`. The upward walk terminates on the byte length of the path. The length
check cannot fail: `FilePath.parent` returns a proper prefix, cut at the last separator or
after the root directory. Its `revFind?`-based definition has no lemmas in core to prove
that, so the check states it. -/
def findRepoRoot (start : FilePath) : IO FilePath := do
  let root ← IO.FS.realPath start
  let rec loop (path : FilePath) : IO FilePath := do
    let hasLean ← (path / "lakefile.lean").pathExists
    let hasToml ← (path / "lakefile.toml").pathExists
    if hasLean && hasToml then
      throw <|
          IO.userError s!"ambiguous Lean project root {path}: both lakefile.lean and lakefile.toml"
    if (hasLean || hasToml) && (← (path / "lean-toolchain").pathExists) then
      return path
    match path.parent with
    | some parent =>
      if parent.toString.utf8ByteSize < path.toString.utf8ByteSize then loop parent
      else throw <| IO.userError s!"parent of {path} is not a proper prefix"
    | none => throw <| IO.userError s!"cannot find Lean project root above {root}"
  termination_by path.toString.utf8ByteSize
  loop root

/-- The project root that `findRepoRoot` finds from the current working directory. -/
def repoRoot : IO FilePath := do
  findRepoRoot (← IO.currentDir)

/-- Initialize dynamic module lookup from Lake's `LEAN_PATH`. Compiled checker
executables do not receive the `lean` driver's search-path initialization. -/
def initializeLeanSearchPath : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)

/-- The compiled library directory of the running checker executable's own
package, when it follows Lake's standard layout. The trusted probe module
resolves from here even when no Lake-provided `LEAN_PATH` is in scope. -/
def checkerPackageLibDir : IO (Option FilePath) := do
  let some bin := (← IO.appPath).parent | return none
  let libDir := bin / ".." / "lib" / "lean"
  if ← (libDir / "Regula" / "Probe.olean").pathExists then
    return some libDir
  return none

/-- A fresh scratch directory under `Regula.Scratch.directory repo`
(`repo/.lake/regula-scratch`), removed on return; orphans of dead runs are reclaimed
(`Regula.Scratch`). -/
def withScratch {α : Type} (repo : FilePath) (stem : String)
    (action : FilePath → IO α) : IO α :=
  return (← Regula.Scratch.withScratch repo stem action).1

/-- The real path of the top level of the Git work tree that holds the directory `dir`, as
`git rev-parse --show-toplevel` run in `dir` prints it, or `none` when that command fails, for
example where Git finds no work tree, or when `dir` or the printed path cannot be resolved. Git
runs without `GIT_DIR` and `GIT_WORK_TREE`, so the work tree is the one Git finds from `dir`
itself. Git and the filesystem are trusted. -/
def gitWorkTree (dir : FilePath) : IO (Option FilePath) := do
  let result ← try
      runProcess dir "git" #["rev-parse", "--show-toplevel"]
        #[("GIT_DIR", none), ("GIT_WORK_TREE", none)]
    catch _ => return none
  let top := result.stdout.trimAscii.toString
  if !result.succeeded || top.isEmpty then return none
  try some <$> IO.FS.realPath (FilePath.mk top) catch _ => return none

/-- Whether a dependency whose directory is in the Git work tree `dependency` is in the work tree
`root` of the root package: both are known and they are the same directory. -/
def sameWorkTree (root dependency : Option FilePath) : Bool :=
  match root, dependency with
  | some root, some dependency => decide (root = dependency)
  | _, _ => false

/-- `sameWorkTree` holds exactly when one known work tree holds the two directories, so a
dependency is never in an unknown work tree of the root package, and a root package outside every
work tree has no dependency in its work tree. -/
theorem sameWorkTree_iff (root dependency : Option FilePath) :
    sameWorkTree root dependency = true ↔ ∃ tree, root = some tree ∧ dependency = some tree := by
  cases root <;> cases dependency <;> simp [sameWorkTree, eq_comm]

/-- Whether the directory `dir` of a dependency is in the Git work tree `root` of the root
package (`gitWorkTree`, `sameWorkTree`). The audit owns such a dependency: it is a path
dependency in the project's own repository. -/
def ownedDirectory (root : Option FilePath) (dir : FilePath) : IO Bool :=
  return sameWorkTree root (← gitWorkTree dir)

/-- One component of `joinWithin`'s lexical join below `base`: `.` and empty components are
dropped, `..` removes the last component unless that would leave `base`, and any other
component is appended. -/
def joinStep (base acc : List String) (component : String) : Option (List String) :=
  if component == "." || component.isEmpty then some acc
  else if component == ".." then
    if acc.length > base.length then some acc.dropLast else none
  else some (acc ++ [component])

/-- The path components of `base / relative`, with each `.` dropped and each `..` removing the
component before it, or `none` when a `..` would leave `base`. A purely lexical join: no
component is resolved through a symbolic link. -/
def joinWithin (base relative : List String) : Option (List String) :=
  relative.foldlM (joinStep base) base

/-- One step keeps `base` as a prefix. -/
theorem joinStep_extends {base acc next : List String} {component : String}
    (hacc : base <+: acc) (h : joinStep base acc component = some next) : base <+: next := by
  unfold joinStep at h
  split at h
  · cases h; exact hacc
  · split at h
    · split at h
      · rename_i hlong
        cases h
        obtain ⟨suffix, rfl⟩ := hacc
        have hne : suffix ≠ [] := by
          rintro rfl
          simp at hlong
        exact ⟨suffix.dropLast, by rw [List.dropLast_append_of_ne_nil hne]⟩
      · cases h
    · cases h
      obtain ⟨suffix, rfl⟩ := hacc
      exact ⟨suffix ++ [component], by simp⟩

/-- Folding the steps from any extension of `base` keeps `base` as a prefix. -/
theorem foldlM_joinStep_extends (base : List String) :
    ∀ (relative acc result : List String), base <+: acc →
      relative.foldlM (joinStep base) acc = some result → base <+: result
  | [], acc, result, hacc, h => by
    cases h
    exact hacc
  | component :: rest, acc, result, hacc, h => by
    rw [List.foldlM_cons] at h
    cases hs : joinStep base acc component with
    | none => simp [hs] at h
    | some next =>
      rw [hs] at h
      exact foldlM_joinStep_extends base rest next result (joinStep_extends hacc hs) h

/-- `joinWithin` never leaves `base`: every result extends it. -/
theorem joinWithin_extends (base relative result : List String)
    (h : joinWithin base relative = some result) : base <+: result :=
  foldlM_joinStep_extends base relative base result (List.prefix_refl base) h

/-- The module name prefixes reserved to the checker: those of its force-loaded reporter's import
closure outside the toolchain, which the reporter's overlay serves (`Environment.probePrefixes`).
A package other than the checker's own may provide a module under them only with the checker's
own source text (`Lake.surfaceInventory`). -/
def reservedPrefixes : Array String := #["Regula", "RegulaPolicy"]

/-- Whether module `name` lies under a prefix reserved to the checker (`reservedPrefixes`). -/
def reservedModule (name : Name) : Bool :=
  reservedPrefixes.contains name.getRoot.toString

/-- Whether `segment`, a part of a path between separators, names one entry directly below a
directory: it is not empty, not `.` or `..`, and holds no path separator
(`FilePath.pathSeparators`). -/
def safeSegment (segment : String) : Bool :=
  !segment.isEmpty && segment != "." && segment != ".." &&
    !segment.any (FilePath.pathSeparators.contains ·)

/-- The segments of `part` between path separators (`FilePath.pathSeparators`). -/
def pathSegments (part : String) : List String :=
  part.splitToList (FilePath.pathSeparators.contains ·)

/-- Whether `part`, one component of a module name, names entries below a directory: it is not an
absolute path (`FilePath.isAbsolute`, so on Windows also a drive such as `C:`), and each of its
segments between path separators is a `safeSegment`, so it is not empty and has no `.` or `..`
segment. A relative component with separators, such as `foo/bar` of a library named `foo/bar`,
names `foo/bar` below the directory. `FilePath.join` discards its base for an absolute right
operand, so `Lean.modToFilePath` puts a module with an absolute component outside its directory,
and a `..` segment leaves it. -/
def safeModuleComponent (part : String) : Bool :=
  !(FilePath.mk part).isAbsolute && (pathSegments part).all safeSegment

/-- The string components of module name `name`, root first, when there is at least one and each
is a `safeModuleComponent`; `none` for the anonymous name, a numeric component or an unsafe one. -/
def safeModuleComponents? : Name → Option (List String)
  | .anonymous => none
  | .num .. => none
  | .str p s =>
    if safeModuleComponent s then
      match p with
      | .anonymous => some [s]
      | p => (safeModuleComponents? p).map (· ++ [s])
    else none

/-- The path segments of the file of module `name` with extension `ext`, below the directory it
belongs to: the segments of each component of `name` (`safeModuleComponents?`, `pathSegments`), the
last one with `.` and `ext` appended; `none` unless `name` is admitted and every resulting segment
is a `safeSegment`. -/
def moduleSegments? (name : Name) (ext : String) : Option (List String) :=
  match safeModuleComponents? name with
  | none => none
  | some parts =>
    let segments := parts.flatMap pathSegments
    let withExtension := segments.dropLast ++ segments.getLast?.toList.map (· ++ "." ++ ext)
    if !withExtension.isEmpty && withExtension.all safeSegment then some withExtension else none

/-- The path of `segments` below the directory `dir`: the text of `dir`, then the path separator
and each segment. -/
def pathBelow (dir : FilePath) (segments : List String) : FilePath :=
  ⟨dir.toString ++ String.join (segments.map (FilePath.pathSeparator.toString ++ ·))⟩

/-- The file of module `name` with extension `ext` below the directory `dir`, the path of its
segments (`moduleSegments?`, `pathBelow`); `none` for a name that `safeModuleComponents?` does not
admit. Every module-to-path construction of the ownership audit goes through this one function
(`Lake.checkerSource`, `Lake.packageModules`, `Environment.attributeLoaded`), and
`Lake.surfaceInventory` refuses every package that configures or provides a module whose name it
does not admit, before any path is built from it. `modulePath?_below` states that the path lies
below `dir`. -/
def modulePath? (dir : FilePath) (name : Name) (ext : String) : Option FilePath :=
  (moduleSegments? name ext).map (pathBelow dir)

/-- For every admitted module name, the path `modulePath?` builds lies below the base directory: its
text is the text of `dir`, then the path separator and each of a nonempty list of segments, none of
which is empty, `.` or `..` or holds a path separator. So the components of `dir` are a prefix of
its components, each further component names one entry directly below the previous one, and none
climbs out of `dir`. -/
theorem modulePath?_below {dir : FilePath} {name : Name} {ext : String} {path : FilePath}
    (h : modulePath? dir name ext = some path) :
    ∃ segments : List String, segments ≠ [] ∧ (∀ s ∈ segments, safeSegment s = true) ∧
      path = pathBelow dir segments ∧
      path.toString = dir.toString ++
        String.join (segments.map (FilePath.pathSeparator.toString ++ ·)) := by
  unfold modulePath? at h
  obtain ⟨segments, hsegments, rfl⟩ := Option.map_eq_some_iff.mp h
  unfold moduleSegments? at hsegments
  split at hsegments
  · cases hsegments
  · dsimp only at hsegments
    split at hsegments
    · rename_i hsafe
      cases hsegments
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        List.all_eq_true] at hsafe
      exact ⟨_, hsafe.1, hsafe.2, rfl, rfl⟩
    · cases hsegments

/-- The text of the base directory is a prefix of the text of each path `modulePath?` builds. -/
theorem modulePath?_prefix {dir : FilePath} {name : Name} {ext : String} {path : FilePath}
    (h : modulePath? dir name ext = some path) :
    ∃ rest, path.toString = dir.toString ++ rest := by
  obtain ⟨segments, -, -, -, htext⟩ := modulePath?_below h
  exact ⟨_, htext⟩

/-- One owned package, the root package or an owned dependency, as the audit passes it to each
environment: its compiled-module output directory, Lake's default `.lake/build/lib/lean` of the
package (`Lake.checkDefaultLayout`), and the modules its own libraries and executables provide. -/
structure OwnedPackage where
  /-- The package's name. -/
  package : String := ""
  /-- The package's compiled-module output directory. -/
  output : FilePath
  /-- The modules of the package. -/
  modules : Array Name
  deriving Inhabited, Repr

/-- The modules of an owned package as they cross the worker boundary: each in the exact encoding
of `RegistryCodec.printedNameJson`. A package's configuration can give a module a name, such as
`bar»`, whose printed text Lean's parser does not read back. -/
def OwnedPackage.modulesJson (modules : Array Name) : Array Json :=
  modules.map RegistryCodec.printedNameJson

/-- Every module list survives its written form (`RegistryCodec.printedNameJson_roundtrip`). -/
theorem OwnedPackage.modulesJson_roundtrip (modules : Array Name) :
    (OwnedPackage.modulesJson modules).mapM RegistryCodec.parsePrintedNameJson = .ok modules := by
  rcases modules with ⟨modules⟩
  simp only [OwnedPackage.modulesJson, List.map_toArray, List.mapM_toArray]
  induction modules with
  | nil => rfl
  | cons name rest ih =>
    simp only [List.map_cons, List.mapM_cons, RegistryCodec.printedNameJson_roundtrip]
    revert ih
    cases List.mapM RegistryCodec.parsePrintedNameJson (List.map RegistryCodec.printedNameJson rest)
      <;> simp_all [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

instance : ToJson OwnedPackage := ⟨fun p => Json.mkObj [("package", toJson p.package),
  ("output", toJson p.output), ("modules", toJson (OwnedPackage.modulesJson p.modules))]⟩

instance : FromJson OwnedPackage := ⟨fun j => do
  let modules ← j.getObjValAs? (Array Json) "modules"
  return {
    package := ← j.getObjValAs? String "package"
    output := ← j.getObjValAs? FilePath "output"
    modules := ← modules.mapM RegistryCodec.parsePrintedNameJson }⟩

/-- What an audit owns beyond the modules it requests, as it passes that to each environment it
loads (`Lake.SurfaceInventory.ownership`). -/
structure Ownership where
  /-- The compiled-module output directories of the owned packages: the root package's, then each
  owned dependency's. -/
  outputs : Array FilePath := #[]
  /-- The root package, by the same record as an owned dependency. A loaded module that is its
  artifact belongs to it (`Environment.attributeLoaded`). -/
  root : Option OwnedPackage := none
  /-- The owned dependency packages. A module an environment loads is one of theirs when the
  `.olean` it loaded is exactly the artifact of that module in the package's output directory
  (`Environment.attributeLoaded`); an environment owns such a module only when it lies outside the
  checker's reserved prefixes (`Environment.projectModules`) and the import closure of a module it
  requests contains it, or it imports an owned module (`Environment.ownedModuleSet`). -/
  dependencies : Array OwnedPackage := #[]
  /-- In a copy that the audit made, the copy's real directory (`Lake.SurfaceInventory.copy`):
  every owned module an environment loads must resolve below it
  (`Environment.ModuleGraph.outsideCopy`). -/
  copy : Option FilePath := none
  deriving ToJson, FromJson, Inhabited, Repr

/-- The parts of a compiled module that Lean's import reads, by extension: the module data of each
level, and the compiled code and its signature. -/
def moduleParts : Array String :=
  #["olean", "olean.server", "olean.private", "ir", "ir.sig"]

/-- Whether a file named `name` is a part of a compiled module (`moduleParts`). -/
def isModulePart (name : String) : Bool :=
  moduleParts.any fun part => name.endsWith ("." ++ part)

/-- The longest common prefix of two component lists. -/
def commonPrefix : List String → List String → List String
  | a :: as, b :: bs => if a = b then a :: commonPrefix as bs else []
  | _, _ => []

/-- Refuse historical development observations rather than treating them as audit evidence. -/
def requireAuditDocument (value : Json) : IO Json := do
  if (value.getObjValAs? String "purpose").toOption == some "compiler-qualification" then
    throw <| IO.userError "compiler qualification output is not supported audit evidence"
  return value

/-- Strict JSON parsing; historical development observations are not audit evidence. -/
def readJson (path : FilePath) : IO Json := do
  let text ← IO.FS.readFile path
  requireAuditDocument (← IO.ofExcept <| Regula.Checker.PolicyCodec.parse text)

/-- Write `value` as compact JSON and a final newline to `path`, creating its parent
directories, and report how long encoding and writing took when timing output is on. -/
def writeJson (path : FilePath) (value : Json) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  let encodeStart ← IO.monoMsNow
  let encoded := Json.compress value ++ "\n"
  timingSpan s!"diagnostic span: writeJson encode {path}: {(← IO.monoMsNow) - encodeStart}ms"
  let writeStart ← IO.monoMsNow
  IO.FS.writeFile path encoded
  timingSpan s!"diagnostic span: writeJson write {path}: {(← IO.monoMsNow) - writeStart}ms"

/-- The JSON on a succeeded process's standard output, parsed strictly; a failed process or
malformed output throws an error that names `what`. -/
def parseJsonOutput (what : String) (result : ProcessResult) : IO Json := do
  if !result.succeeded then
    throw <| IO.userError s!"lake-query-failed: {what}: {result.output.trimAscii.toString}"
  match Regula.Checker.PolicyCodec.parse result.stdout with
  | .ok value => return value
  | .error error =>
      throw <| IO.userError s!"lake-query-malformed: {what}: {error}"

/-- A JSON array of unique nonempty strings. -/
def stringArray (what : String) (value : Json) : Except String (Array String) := do
  let .arr values := value | throw s!"{what}: expected a JSON string array"
  values.foldlM (init := #[]) fun result item => do
    let .str text := item | throw s!"{what}: expected a JSON string array"
    if text.isEmpty || result.contains text then
      throw s!"{what}: expected unique nonempty strings"
    return result.push text

/-- `stringArray` in `IO`: the array of unique nonempty strings `value` holds, or an error
naming `what`. -/
def jsonStringArray (what : String) (value : Json) : IO (Array String) :=
  IO.ofExcept (stringArray what value)

/-- Run `lake query TARGET --json` in `repo` and return its parsed JSON output. -/
def lakeQuery (repo : FilePath) (target : String) : IO Json := do
  parseJsonOutput target <| ← runProcess repo "lake" #["query", target, "--json"]

/-- The last `count` elements of `lines`, or all of them when there are fewer. -/
def takeLast (count : Nat) (lines : Array String) : Array String :=
  lines.extract (lines.size - min count lines.size) lines.size

/-- Keep bounded workers busy without batch barriers. The mutex admits each
index once; each worker owns its results. Join every worker before propagating
errors so callers can safely restore the shared search path. -/
def mapWorkQueue {α β : Type} (jobs : Nat) (items : Array α)
    (action : α → IO β) : IO (Array β) := do
  if jobs == 0 then throw <| IO.userError "job count must be positive"
  let next ← Std.Mutex.new 0
  let mut workers : Array (_root_.Task (Except IO.Error (Array (Nat × β)))) := #[]
  for _ in [:min jobs items.size] do
    workers := workers.push (← IO.asTask (prio := .dedicated) do
      let mut results := #[]
      for _ in [:items.size] do
        let index ← next.atomically do
          let index ← get
          if index < items.size then
            set (index + 1)
            return some index
          return none
        let some index := index | break
        let some item := items[index]?
          | throw <| IO.userError "internal error: invalid work queue index"
        results := results.push (index, ← action item)
      return results)
  let outcomes := workers.map (·.get)
  let mut responses := #[]
  for outcome in outcomes do
    responses := responses ++ (← IO.ofExcept outcome)
  IO.ofExcept <| (RegulaPolicy.checked_indexedResults.run items.size (fun _ _ => true)
    responses.toList).mapError fun failure =>
      s!"internal error: work queue result admission: {repr failure}"

/-- Bounded concurrent map implemented in deterministic batches. -/
def mapConcurrent {α β : Type} (jobs : Nat) (items : Array α) (action : α → IO β) :
    IO (Array β) := do
  if jobs == 0 then throw <| IO.userError "job count must be positive"
  let mut results : Array β := #[]
  let mut offset := 0
  while offset < items.size do
    let stop := min items.size (offset + jobs)
    let batch := items.extract offset stop
    let mut tasks : Array (Task (Except IO.Error β)) := #[]
    for item in batch do
      tasks := tasks.push (← IO.asTask (action item) Task.Priority.dedicated)
    -- Join the entire batch before propagating any error. Callers may restore
    -- scoped resources on failure; no worker may still be using them then.
    let outcomes := tasks.map (·.get)
    for outcome in outcomes do
      results := results.push (← IO.ofExcept outcome)
    offset := stop
  return results

/-- Whether `child` lies at or below `parent`, comparing the path components of both after
resolving them with `IO.FS.realPath`. -/
def pathWithin (child parent : FilePath) : IO Bool := do
  let child ← IO.FS.realPath child
  let parent ← IO.FS.realPath parent
  return parent.components.isPrefixOf child.components

/-- The natural number `value` spells; otherwise an error saying that `flag` requires one. -/
def parseNatArg (flag value : String) : IO Nat :=
  match value.toNat? with
  | some n => return n
  | none => throw <| IO.userError s!"{flag} requires a natural number"

/-- Exact source request shared by the remaining command-line worker adapters. -/
def sourceWorkerRequest (stage : String) (moduleName : Name) (path : FilePath)
    (content : String) : Json :=
  Json.mkObj [("stage", .str stage), ("module", Regula.RegistryCodec.nameJson moduleName),
    ("source", .str path.toString), ("content", .str content)]

/-- Versioned raw worker transport. Request equality is exact JSON-tree equality;
this records completion data and never constructs policy acceptance. -/
def workerPacket (request payload : Json) : Json := Json.mkObj [
  ("schema", toJson (1 : Nat)),
  ("producer", Json.mkObj
      (Regula.RegistryCodec.identityFields Regula.Checker.Producer.identity ++
          [("compilerCommit", .str Lean.githash)])),
  ("request", request), ("payload", payload)]

/-- The payload of a worker packet whose schema is 1 and whose producer, toolchain commit and
request equal this checker's and `request`; otherwise an error naming the mismatch. -/
def readWorkerPacket (request packet : Json) : Except String Json := do
  Regula.Checker.PolicyCodec.exactFields packet ["schema", "producer", "request", "payload"]
  unless (← packet.getObjValAs? Nat "schema") == 1 do throw "unsupported worker schema"
  unless (← packet.getObjVal? "producer") ==
      Json.mkObj
          (Regula.RegistryCodec.identityFields Regula.Checker.Producer.identity ++
              [("compilerCommit", .str Lean.githash)]) do
    throw "worker producer or toolchain mismatch"
  unless (← packet.getObjVal? "request") == request do throw "worker request binding mismatch"
  packet.getObjVal? "payload"

/-- Indexed raw results retain multiplicity before admission into the fixed key set. -/
def indexedWorkerPayload {α : Type} [ToJson α] (values : Array α) : Json :=
  toJson (values.mapIdx fun i value => (i, toJson value))

/-- Decode indexed worker results and admit them through `checked_indexedResults`: success
returns exactly one bound payload for each requested slot, in slot order. -/
def admitIndexedWorkerResults {α : Type} [FromJson α] (count : Nat) (binding : Nat → α → Bool)
    (payload : Json) : Except String (Array α) := do
  let responses : Array (Nat × α) ← fromJson? payload
  (RegulaPolicy.checked_indexedResults.run count binding responses.toList).mapError fun
    | .admission failure => s!"invalid worker result admission: {repr failure}"
    | .missing slot => s!"worker result missing required key {slot}"

/-- The `axiomGate` binary beside the running checker's package library: every checker
worker spawn runs it. -/
def workerBinary : IO FilePath := do
  let some selfLib ← checkerPackageLibDir
    | throw <| IO.userError "checker library directory unavailable"
  return selfLib.parent.getD selfLib / ".." / "bin" / "axiomGate"

/-- A failed worker's error text: its standard error, trimmed and without the `FAIL: ` prefix
the `axiomGate` entry prints before an escaped error, or a note that it wrote none. -/
def workerErrorText (stderr : String) : String :=
  let text := stderr.trimAscii.toString
  let text := ((text.dropPrefix? "FAIL: ").map (·.toString)).getD text
  if text.isEmpty then "the worker wrote no error" else text

/-- Await an isolated checker worker and decode its typed result. The child
stays in the caller’s process group and its scratch files outlive its exit. Its standard error
is captured: a nonzero exit raises an error that carries it (`workerErrorText`), and a
successful worker's is copied to this process's standard error. -/
def runTypedWorker {α β : Type} [ToJson α] [FromJson β]
    (flag : String) (request : α) : IO β := do
  let binary ← workerBinary
  withScratch (← IO.currentDir) "typed-worker" fun scratch => do
    let input := scratch / "request.json"
    let output := scratch / "report.json"
    writeJson input (toJson request)
    let child ← IO.Process.spawn {
      cmd := binary.toString
      args := #[flag, input.toString, output.toString]
      env := #[("LEAN_PATH", some (SearchPath.toString (← Lean.searchPathRef.get))),
        (timingVariable, if ← timing.get then some "1" else none)]
      stdin := .null
      stdout := .inherit
      stderr := .piped
      setsid := false
    }
    -- Drain standard error while the worker runs, so a full pipe cannot block it.
    let errors ← IO.asTask child.stderr.readToEnd .dedicated
    let waited : Except IO.Error UInt32 ← try pure (.ok (← child.wait))
      catch error => pure (.error error)
    let errors ← IO.ofExcept (← IO.wait errors)
    let code ← IO.ofExcept waited
    if code != 0 then
      throw <| IO.userError s!"{flag} exited with code {code}: {workerErrorText errors}"
    unless errors.isEmpty do IO.eprint errors
    let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile output)
    let payload ← IO.ofExcept <| readWorkerPacket (toJson request) json
    IO.ofExcept (fromJson? payload)

end Regula.Checker
