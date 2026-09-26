import Regula.Checker.Producer
import Regula.Checker.PolicyCodec
import Regula.Scratch
import RegulaPolicy.ResultState
import Lean
import Lake.Load.Manifest
import Std.Sync.Mutex

/-! Shared process, path, JSON, and bounded-concurrency support. -/

namespace Regula.Checker

open Lean System

structure ProcessResult where
  exitCode : UInt32
  stdout : String
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
    stdout := ← value.getObjValAs? String "stdout", stderr := ← value.getObjValAs? String "stderr" }⟩

namespace ProcessResult

def output (result : ProcessResult) : String :=
  result.stdout ++ result.stderr

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

def runProcess (repo : FilePath) (cmd : String) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO ProcessResult := do
  let result ← IO.Process.output { cmd, args, cwd := some repo, env }
  return { exitCode := result.exitCode, stdout := result.stdout, stderr := result.stderr }

/-- Report elapsed wall time around an action, including exceptional completion. -/
def timedPhase (label : String) (action : IO α) : IO α := do
  IO.println s!"verification phase {label}: start"
  (← IO.getStdout).flush
  let start ← IO.monoNanosNow
  try action
  finally
    let elapsed ← IO.monoNanosNow
    IO.println s!"verification phase {label}: {(elapsed - start) / 1000000}ms (finished)"
    (← IO.getStdout).flush

def outputLines (output : String) : Array String :=
  output.splitOn "\n" |>.toArray

/-- The pinned toolchain renders a diagnostic head as `file:l:c: warning: msg`
or, for a named diagnostic, `file:l:c: warning(name): msg`
(`Lean.mkErrorStringWithPos`); both forms are warnings. -/
def isWarningLine (line : String) : Bool :=
  let lower := line.toLower
  lower.contains "warning:" || lower.contains ": warning("

def isErrorLine (line : String) : Bool :=
  let lower := line.toLower
  lower.contains ": error" || lower.startsWith "error:"

def warningLines (output : String) : Array String :=
  outputLines output |>.filter isWarningLine

def errorLines (output : String) : Array String :=
  outputLines output |>.filter isErrorLine

/-- Lake's own progress markers, build summaries (`Lake/Build/Run.lean` in the
pinned toolchain prints `Build completed successfully` and `Some required
targets logged failures:`), and replayed `info:`/`trace:` log lines, each of
which ends a Lean diagnostic body in a `lake build` transcript. -/
private def isLakeStatusLine (line : String) : Bool :=
  #["✔", "⚠", "✖", "ℹ", "Build completed", "Some required targets", "info:", "trace:"].any
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
      throw <| IO.userError s!"ambiguous Lean project root {path}: both lakefile.lean and lakefile.toml"
    if (hasLean || hasToml) && (← (path / "lean-toolchain").pathExists) then
      return path
    match path.parent with
    | some parent =>
      if parent.toString.utf8ByteSize < path.toString.utf8ByteSize then loop parent
      else throw <| IO.userError s!"parent of {path} is not a proper prefix"
    | none => throw <| IO.userError s!"cannot find Lean project root above {root}"
  termination_by path.toString.utf8ByteSize
  loop root

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

/-- A fresh scratch directory under `repo/tmp`, removed on return; orphans of dead runs are
reclaimed (`Regula.Scratch`). -/
def withScratch (repo : FilePath) (stem : String)
    (action : FilePath → IO α) : IO α :=
  return (← Regula.Scratch.withScratch repo stem action).1

/-- Lake resolves a manifest `path` dependency relative to the workspace
root, so a relative `dir` copied verbatim would name a different directory
under the scratch area. Record every relative `path` entry of the copied Lake
manifest as an absolute workspace override for the copy (Lake reads
`.lake/package-overrides.json` on every workspace load); git entries and
absolute paths are left as pinned. A referenced directory that does not
exist fails closed here with the Lake load-failure prefix. -/
def relocatePathDependencies (repo target : FilePath) : IO Unit := do
  let some manifest ← _root_.Lake.Manifest.load? (target / "lake-manifest.json") | return
  let mut overrides : Array _root_.Lake.PackageEntry := #[]
  for entry in manifest.packages do
    if let .path dir := entry.src then
      if !dir.isAbsolute then
        let source := repo / dir
        if !(← source.isDir) then
          throw <| IO.userError <|
            s!"lake-workspace-load-failed: path dependency '{entry.name}' at {source} is not a directory"
        overrides := overrides.push { entry with src := .path (← IO.FS.realPath source) }
  if overrides.isEmpty then return
  IO.FS.createDirAll (target / ".lake")
  _root_.Lake.Manifest.saveEntries (target / ".lake" / "package-overrides.json") overrides

/-- Copy a checked project into `target`, skipping VCS data, Lake build
state, machine artifact caches, the checker's scratch area, and the `exclude`
path that receives the copy. Dependency checkouts are shared through a
`.lake/packages` link, so a fresh build in the copy does not refetch or
rebuild dependencies while the copy's own build output starts empty, and
relative `path` dependencies are re-anchored to the original project
(`relocatePathDependencies`). -/
def copyProject (repo target exclude : FilePath) : IO Unit := do
  IO.FS.createDirAll target
  let sourceComponents := repo.normalize.components
  let excludeComponents := exclude.normalize.components
  -- Exclusion is closed under descendants. Prune before traversal: filtering
  -- afterwards still visits dependency checkouts and every prior scratch copy.
  -- VCS data, Lake build state, and artifact caches are pruned at every depth
  -- (a nested Lake workspace such as a committed example adopter carries its
  -- own `.lake` with full dependency checkouts); the checker's `tmp/` scratch
  -- area is pruned only at the project root, where it lives.
  let prunedAnywhere := fun (component : String) =>
    component == ".git" || component == ".lake" || component == ".cache"
  let includePath := fun (path : FilePath) =>
    let components := path.normalize.components
    !excludeComponents.isPrefixOf components &&
      (match components.drop sourceComponents.length with
        | "tmp" :: _ => false
        | relative => !relative.any prunedAnywhere)
  for path in ← repo.walkDir (fun path => pure (includePath path)) do
    let components := path.normalize.components
    if components == sourceComponents || !includePath path then
      continue
    let relative := components.drop sourceComponents.length
    let destination := relative.foldl (· / FilePath.mk ·) target
    if ← path.isDir then
      IO.FS.createDirAll destination
    else
      if let some parent := destination.parent then IO.FS.createDirAll parent
      IO.FS.writeBinFile destination (← IO.FS.readBinFile path)
  let packages := repo / ".lake" / "packages"
  if ← packages.isDir then
    IO.FS.createDirAll (target / ".lake")
    let link ← runProcess target "ln" #["-s", packages.toString,
      (target / ".lake" / "packages").toString]
    if !link.succeeded then
      throw <| IO.userError s!"could not link pinned Lake packages: {link.output}"
  relocatePathDependencies repo target

def readJson (path : FilePath) : IO Json := do
  let text ← IO.FS.readFile path
  IO.ofExcept <| Regula.Checker.PolicyCodec.parse text

def writeJson (path : FilePath) (value : Json) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  let encodeStart ← IO.monoMsNow
  let encoded := Json.compress value ++ "\n"
  IO.println s!"diagnostic span: writeJson encode {path}: {(← IO.monoMsNow) - encodeStart}ms"
  let writeStart ← IO.monoMsNow
  IO.FS.writeFile path encoded
  IO.println s!"diagnostic span: writeJson write {path}: {(← IO.monoMsNow) - writeStart}ms"

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

def jsonStringArray (what : String) (value : Json) : IO (Array String) :=
  IO.ofExcept (stringArray what value)

def lakeQuery (repo : FilePath) (target : String) : IO Json := do
  parseJsonOutput target <| ← runProcess repo "lake" #["query", target, "--json"]

def takeLast (count : Nat) (lines : Array String) : Array String :=
  lines.extract (lines.size - min count lines.size) lines.size

/-- Keep bounded workers busy without batch barriers. The mutex admits each
index once; each worker owns its results. Join every worker before propagating
errors so callers can safely restore the shared search path. -/
def mapWorkQueue (jobs : Nat) (items : Array α)
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
  IO.ofExcept <| (RegulaPolicy.checkedIndexedResults.run items.size (fun _ _ => true)
    responses.toList).mapError fun failure =>
      s!"internal error: work queue result admission: {repr failure}"

/-- Bounded concurrent map implemented in deterministic batches. -/
def mapConcurrent (jobs : Nat) (items : Array α) (action : α → IO β) : IO (Array β) := do
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

def pathWithin (child parent : FilePath) : IO Bool := do
  let child ← IO.FS.realPath child
  let parent ← IO.FS.realPath parent
  return parent.components.isPrefixOf child.components

def parseNatArg (flag value : String) : IO Nat :=
  match value.toNat? with
  | some n => return n
  | none => throw <| IO.userError s!"{flag} requires a natural number"

/-- Exact source request shared by the remaining command-line worker adapters. -/
def sourceWorkerRequest (stage : String) (moduleName : Name) (path : FilePath) (content : String) : Json :=
  Json.mkObj [("stage", .str stage), ("module", Regula.RegistryCodec.nameJson moduleName),
    ("source", .str path.toString), ("content", .str content)]

/-- Versioned raw worker transport. Request equality is exact JSON-tree equality;
this records completion data and never constructs policy acceptance. -/
def workerPacket (request payload : Json) : Json := Json.mkObj [
  ("schema", toJson (1 : Nat)),
  ("producer", Json.mkObj (Regula.RegistryCodec.identityFields Regula.Checker.Producer.identity ++ [("compilerCommit", .str Lean.githash)])),
  ("request", request), ("payload", payload)]

def readWorkerPacket (request packet : Json) : Except String Json := do
  Regula.Checker.PolicyCodec.exactFields packet ["schema", "producer", "request", "payload"]
  unless (← packet.getObjValAs? Nat "schema") == 1 do throw "unsupported worker schema"
  unless (← packet.getObjVal? "producer") ==
      Json.mkObj (Regula.RegistryCodec.identityFields Regula.Checker.Producer.identity ++ [("compilerCommit", .str Lean.githash)]) do
    throw "worker producer or toolchain mismatch"
  unless (← packet.getObjVal? "request") == request do throw "worker request binding mismatch"
  packet.getObjVal? "payload"

/-- Indexed raw results retain multiplicity before admission into the fixed key set. -/
def indexedWorkerPayload [ToJson α] (values : Array α) : Json :=
  toJson (values.mapIdx fun i value => (i, toJson value))

/-- Decode indexed worker results and admit them through `checkedIndexedResults`: success
returns exactly one bound payload for each requested slot, in slot order. -/
def admitIndexedWorkerResults {α : Type} [FromJson α] (count : Nat) (binding : Nat → α → Bool)
    (payload : Json) : Except String (Array α) := do
  let responses : Array (Nat × α) ← fromJson? payload
  (RegulaPolicy.checkedIndexedResults.run count binding responses.toList).mapError fun
    | .admission failure => s!"invalid worker result admission: {repr failure}"
    | .missing slot => s!"worker result missing required key {slot}"

/-- The `axiomGate` binary beside the running checker's package library: every checker
worker spawn runs it. -/
def workerBinary : IO FilePath := do
  let some selfLib ← checkerPackageLibDir
    | throw <| IO.userError "checker library directory unavailable"
  return selfLib.parent.getD selfLib / ".." / "bin" / "axiomGate"

/-- Await an isolated checker worker and decode its typed result. The child
stays in the caller’s process group and its scratch files outlive its exit. -/
def runTypedWorker [ToJson α] [FromJson β]
    (flag : String) (request : α) : IO β := do
  let binary ← workerBinary
  withScratch (← IO.currentDir) "typed-worker" fun scratch => do
    let input := scratch / "request.json"
    let output := scratch / "report.json"
    writeJson input (toJson request)
    let child ← IO.Process.spawn {
      cmd := binary.toString
      args := #[flag, input.toString, output.toString]
      env := #[("LEAN_PATH", some (SearchPath.toString (← Lean.searchPathRef.get)))]
      stdin := .null
      stdout := .inherit
      stderr := .inherit
      setsid := false
    }
    let code ← child.wait
    if code != 0 then throw <| IO.userError s!"{flag} failed with exit code {code}"
    let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile output)
    let payload ← IO.ofExcept <| readWorkerPacket (toJson request) json
    IO.ofExcept (fromJson? payload)

end Regula.Checker
