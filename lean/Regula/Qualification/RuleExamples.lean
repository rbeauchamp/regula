import Regula.Qualification.Project
import Regula.Checker.Lake
import Regula.Checker.Snapshot
import Regula.Qualification.Slot
import RegulaQualification.Evidence
import RegulaQualification.Template
import RegulaQualification.Producer
import RegulaQualification.CorpusWindow
import Regula.Checker.RuleExampleCorpusProjection
import Regula.Checker.ResultProtocol

/-! # Rule-example corpus orchestration

Source-owned corpus orchestration. Actual detector receipts are admitted by the
existing RuleExampleQualification executable and its proof-linked policy functions.
This adapter does not infer policy from source text. Filesystem/process authenticity
remains trusted. At most five producer jobs run at once, each in its own fresh
workspace over one shared private ROOT copy and the shared dependency roots; the
run refuses unless a content-level identity of every shared tree at the end equals
the identity before any producer started (end-state equality, not an absence of
writes). Launches and consumption order come from the proved pure
`RegulaQualification.CorpusWindow` state; the final `COMPLETED` export requires
the scratch cleanup witness, and the run verdict is the process exit status. The consumer
path — control admission and terminal qualification — consumes captured data and the
real ROOT checkout and never dereferences the slot path. The consumer thread reuses
pure snapshot construction only at proved exact equality of fresh captures; producer
tasks stay uncached. -/
namespace Regula.Qualification.RuleExamples
open Lean System RegulaQualification.Evidence

private def get (j : Json) (key : String) : IO Json := IO.ofExcept (field j key)
private def string (j : Json) (key : String) : IO String := IO.ofExcept (text j key)
private def entries (j : Json) (key : String) : IO (Array Json) := IO.ofExcept (array j key)
private def optionalText (j : Json) (key fallback : String) : IO String :=
  match field j key with
  | .error _ => pure fallback
  | .ok value => IO.ofExcept value.getStr?

/-- Producer-window environment: the scrub plus no-optional-write Git and a
disabled Lake artifact cache (fail-closed), so producer children take no shared
optional locks and restore no shared cache artifacts. -/
def corpusEnv : Array (String × Option String) :=
  cleanEnv ++ #[("GIT_OPTIONAL_LOCKS", some "0"), ("LAKE_CACHE_DIR", some "")]

/-- Pure snapshot entry construction; the exact `Json.mkObj` request shape. -/
def snapshotEntry (uri source : String) : Json :=
  Json.mkObj [("uri", .str uri), ("source", .str source)]

/-- Pure request-snapshot construction from exact captured path/source pairs. -/
def snapshotOf (captured : Array (String × String)) : Json :=
  toJson (captured.map fun (uri, source) => snapshotEntry uri source)

/-- Fresh exact capture of every requested path. No read is ever skipped. -/
def capture (paths : Array FilePath) : IO (Array (String × String)) :=
  paths.mapM fun path => do pure (path.toString, ← IO.FS.readFile path)

/-- Constructed-value cache over exact captured sources. The `sound` field keeps
the invariant `value = snapshotOf captured` by type. -/
structure SnapshotCache where
  /-- The path/source pairs the cached value was constructed from, in request order. -/
  captured : Array (String × String)
  /-- The cached request snapshot. -/
  value : Json
  /-- The cached snapshot is the construction for exactly the captured sources. -/
  sound : value = snapshotOf captured

/-- The empty cache: the construction for no captured sources. -/
def SnapshotCache.empty : SnapshotCache := ⟨#[], snapshotOf #[], rfl⟩

/-- Pure reuse decision. At proved exact equality of the fresh captures it
returns the cached construction; otherwise it constructs from the fresh
captures. In both cases the first component is exactly `snapshotOf fresh`. -/
def decideSnapshot (cache : SnapshotCache) (fresh : Array (String × String)) :
    Json × SnapshotCache :=
  dite (fresh = cache.captured) (fun _ => (cache.value, cache))
    (fun _ => (snapshotOf fresh, ⟨fresh, snapshotOf fresh, rfl⟩))

/-- Execution-linked equivalence: the value returned by the executed
`decideSnapshot` is exactly the uncached construction `snapshotOf fresh` over the
same fresh captures, so reuse at equal bytes changes no result. -/
theorem decideSnapshot_value (cache : SnapshotCache) (fresh : Array (String × String)) :
    (decideSnapshot cache fresh).1 = snapshotOf fresh :=
  if hc : fresh = cache.captured then by
    unfold decideSnapshot
    rw [dite_eq_left hc, hc]
    exact cache.sound
  else by
    unfold decideSnapshot
    rw [dite_eq_right hc]

/-- Exact request-snapshot value from fresh reads of every path. -/
def snapshot (paths : Array FilePath) : IO Json :=
  return snapshotOf (← capture paths)

/-- Fresh reads every path (mandatory), then constructs through the proved
`decideSnapshot`. Only the pure construction of an equal value is reused, and
only at proved exact equality of the fresh captures. Consumer-thread only:
concurrent producers use uncached `snapshot`. -/
def snapshotCached (cache : IO.Ref SnapshotCache) (paths : Array FilePath) : IO Json := do
  let fresh ← capture paths
  let (value, next) := decideSnapshot (← cache.get) fresh
  cache.set next
  return value

private def configuration (paths : Array FilePath) : IO Json := do
  return toJson (← paths.mapM fun path => do
    let value ← if (← path.pathExists) && !(← path.isDir) then pure
                                                                (some (← IO.FS.readFile path)) else
                                                                    pure none
    pure (path.toString, value))

private def save (path : FilePath) (value : Json) : IO Unit := do
  let temporary := FilePath.mk (path.toString ++ ".pending")
  IO.FS.writeFile temporary (value.compress ++ "\n")
  IO.FS.rename temporary path

/-- Invalidate the previous verdict before any campaign setup or timer acquisition. -/
def beginAttempt (evidence : FilePath) (attempt : String) : IO Unit := do
  if let some parent := evidence.parent then IO.FS.createDirAll parent
  save evidence (Json.mkObj [("outcome", .str "INCOMPLETE"), ("attempt", .str attempt),
    ("rawDirectory", .str (evidence.toString ++ ".raw/" ++ attempt))])

private def digest (root path : FilePath) : IO Json := do
  let result ← run root "shasum" #["-a", "256", path.toString]
  let value := (result.stdout.splitOn " ").head!
  requireChecks [⟨"raw observation digest", result.exitCode == 0 && value.length == 64 &&
    value.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))⟩]
  return Json.mkObj [("sha256", .str value), ("bytes", toJson (← path.metadata).byteSize)]

/-- Line bound of one drained process stream (`drain`). -/
private def drainLineBound : Nat := 2 ^ 32

/-- Drain textual process streams one line at a time, retaining line terminators and
the final EOF-terminated line. A kill preserves completed lines already read; a pending
unterminated line can remain buffered. Only terminal observations claim complete streams.
EOF depends on the external producer, so the drain is total through `lines`, structural
fuel started at `drainLineBound`: a stream of fewer lines drains unchanged, and a longer
one fails closed, leaving the observation non-terminal. -/
private def drain (source target : IO.FS.Handle) : (lines : Nat) → IO Unit
  | 0 => throw <| IO.userError s!"process stream exceeds {drainLineBound} lines"
  | lines + 1 => do
    let line ← source.getLine
    unless line.isEmpty do
      target.putStr line
      target.flush
      drain source target lines

/-- Observe one detector run. The returned observation is taken only after the
direct child is waited and both stream drains reach EOF: direct-child reaping
and stream-holder closure at producer return. Universal detached-grandchild
termination is not claimed; the joined-worker discipline is the stated basis
(`Common.runProcess`, `runTypedWorker`, `observe` and `run` all wait their
children). -/
private def observe (project binary stdout stderr : FilePath) (command : Array String)
    (env : Array (String × Option String) := corpusEnv) : IO IO.Process.Output := do
  let out ← IO.FS.Handle.mk stdout .write
  let err ← IO.FS.Handle.mk stderr .write
  let child ← IO.Process.spawn {
    cmd := binary.toString, args := command, cwd := some project,
    env, stdin := .null, stdout := .piped, stderr := .piped }
  let outTask ← IO.asTask (drain child.stdout out drainLineBound) Task.Priority.dedicated
  let errTask ← IO.asTask (drain child.stderr err drainLineBound) Task.Priority.dedicated
  -- Hold every managed outcome until both launched drains have joined. A failed
  -- wait is not successful reaping; it still owes the stream joins before
  -- unwinding. Preserve the original error order and exact error values.
  let waited : Except IO.Error UInt32 ← try
    pure (.ok (← child.wait))
  catch error => pure (.error error)
  let drainedOut ← IO.wait outTask
  let drainedErr ← IO.wait errTask
  let code ← IO.ofExcept waited
  IO.ofExcept drainedOut
  IO.ofExcept drainedErr
  return ⟨code, ← IO.FS.readFile stdout, ← IO.FS.readFile stderr⟩

private def addPackage (project : FilePath) (name : String) (dir : FilePath) (config : String) :
    IO Unit := do
  let path := project / "lake-manifest.json"
  let lock ← readJson path
  let packages ← entries lock "packages"
  writeJson path (lock.setObjVal! "packages" (toJson (packages.push (Json.mkObj [
    ("type", .str "path"), ("name", .str name), ("dir", .str dir.toString),
    ("manifestFile", .str "lake-manifest.json"), ("inherited", .bool false),
    ("configFile", .str config)]))))

/-- Consumer context: carries no slot paths. Control admission and terminal
qualification consume captured data and the real ROOT checkout only. -/
private structure Context where
  root : FilePath
  scratch : FilePath
  specs : Json
  checkerPaths : Array FilePath
  checkerBefore : Json
  attempt : String
  rawDirectory : FilePath
  cache : IO.Ref SnapshotCache

/-- Produce one record in its own fresh workspace over the shared ROOT copy. Direct
children are waited and stream holders closed before return (`observe`/`run`;
joined-worker discipline, no universal grandchild claim). -/
private def produce (ctx : Context) (slot : Slot.ProducerSlot) (rule phase : String)
    (sourceText : Option String := none) (producerClaim : Option String := none) : IO Json := do
  let root := ctx.root
  let spec ← get ctx.specs rule
  let case := if phase == "Violation" then "Violation" else "Fixed"
  let project := ctx.scratch / s!"{rule}-{phase}"
  IO.FS.createDir project
  Slot.prepareSlotProject slot project "rule_examples" "kernel-only"
      "The fixture's exact mathematical claim and scope."
  IO.FS.writeFile
      (project / "Example.lean")
          "/-! The true proposition. -/\ntheorem baseline : True := True.intro\n"
  let folder := root / "examples/rules" / rule
  let sourceName := (← optionalText spec "source" "{case}.lean").replace "{case}" case
  let sourceFile := folder / sourceName
  let displayed ← match sourceText with
    | some text => pure text
    | none => IO.FS.readFile sourceFile
  let mut paths := #[project / "Example.lean"]
  let mut sourcePath := project / "Example.lean"
  let raw := ctx.rawDirectory / rule / phase
  IO.FS.createDirAll raw
  let output := raw / "result.json"
  requireChecks [⟨"fresh corpus output", !(← output.pathExists)⟩]
  let kind ← if case == "Fixed" then pure "positive" else string spec "kind"
  let mode ← string spec "invocation"
  if mode == "file" && rule != "RG2001" then
    sourcePath := project / "Fixture.lean"
    paths := paths.push sourcePath
  let mut binary := root / ".lake/build/bin/axiomGate"
  let mut command := #["--project", project.toString]
  if mode == "documentation" then
    IO.FS.createDir (project / "docs")
    sourcePath := project / "docs/Example.md"
    IO.FS.writeFile sourcePath displayed
    paths := paths.push sourcePath
    binary := root / ".lake/build/bin/ruleExamples"
    command := #["--documentation", project.toString, (project / "docs").toString, output.toString]
  else
    IO.FS.writeFile sourcePath displayed
    if rule == "RG2001" then
      let request ← readJson (folder / s!"{case}.json")
      if (request.getObjValAs? Bool "unavailableWorkspace").toOption == some true then
        let config := project / "lakefile.lean"
        IO.FS.writeFile config
            ((← IO.FS.readFile config) ++ "\nrequire unavailable from \"./missing\"\n")
        addPackage project "unavailable" "./missing" "lakefile.lean"
      command := command ++
          #["--file", (project / (← string request "source")).toString, "--claim", "kernel-only",
              "--execution", "checked"]
    else if rule == "RG2002" then
      IO.FS.writeBinFile (project / "foundation_manifest.json")
          (← IO.FS.readBinFile (folder / s!"{case}.json"))
    else if rule == "RG2006" then
      -- The case file is the package's `lakefile.lean`; the run adds its `require` of the
      -- slot's ROOT copy, as `Slot.prepareSlotProject` writes it.
      let config := project / "lakefile.lean"
      let require := ((← IO.FS.readFile config).splitOn "\n").filter
        (·.startsWith "require regula ")
      IO.FS.writeFile config ((← IO.FS.readFile (folder / s!"{case}.lean")) ++ "\n" ++
        "\n".intercalate require ++ "\n")
    else if rule == "RG1003" then
      let vendor := project / "vendor"
      IO.FS.createDir vendor
      IO.FS.writeBinFile (vendor / "Dependency.lean")
          (← IO.FS.readBinFile (folder / s!"{case}.lean"))
      IO.FS.writeBinFile (vendor / "lean-toolchain") (← IO.FS.readBinFile (root / "lean-toolchain"))
      IO.FS.writeFile
          (vendor / "lakefile.toml")
              "name = \"example_dependency\"\n[[lean_lib]]\nname = \"Dependency\"\n"
      let config := project / "lakefile.lean"
      IO.FS.writeFile config
          ((← IO.FS.readFile config) ++
              s!"\nrequire example_dependency from {toJson vendor.toString |>.compress}\n")
      addPackage project "example_dependency" vendor "lakefile.toml"
      paths := paths ++
          #[vendor / "Dependency.lean", vendor / "lakefile.toml", vendor / "lean-toolchain"]
    else if mode == "file" then
      let claim ← match producerClaim with
        | some claim => pure claim
        | none => optionalText spec "claim" "kernel-only"
      command := command ++
          #["--file", sourcePath.toString, "--claim", claim, "--execution", "checked"]
    if rule == "RG1002" && case == "Violation" then
      binary := root / ".lake/build/bin/ruleExamples"
      command := #["--policy-negative", project.toString, sourcePath.toString, output.toString]
    else command := command ++ #["--json-out", output.toString]
  -- Internal qualification-only entry (`ruleExamples --injected-git-facts`): the
  -- same detector body, given the runner's once-captured shared-dependency Git
  -- facts. The user-facing `axiomGate` is never given injected facts.
  let facts := (ctx.rawDirectory / "injected-git-facts.json").toString
  if binary == root / ".lake/build/bin/axiomGate" then
    binary := root / ".lake/build/bin/ruleExamples"
    command := #["--injected-git-facts", facts, "axiomGate"] ++ command
  else
    command := #["--injected-git-facts", facts] ++ command
  let configPaths :=
      #["foundation_manifest.json", "lakefile.lean", "lakefile.toml", "lean-toolchain",
          "lake-manifest.json", ".lake/package-overrides.json"].map
              (fun (name : String) => project / name)
  let configurationBefore ← configuration configPaths
  let frozen := Json.mkObj
      [("uri", .str project.toString), ("source", .str configurationBefore.compress)]
  let mut before := Json.mkObj [("sources", ← snapshot paths), ("configuration", frozen)]
  let requestKind := if rule == "RG1002" && case == "Violation" then "policyNegative"
    else if mode == "documentation" then "documentation" else if mode == "file" then
                                                               "file" else "project"
  let requestedClaim ← optionalText spec "claim" "kernel-only"
  let request := Json.mkObj [
    ("kind", .str requestKind), ("project", .str project.toString),
    ("subject", .str (if #["file", "policyNegative"].contains requestKind then sourcePath.toString
      else if requestKind == "documentation" then (project / "docs").toString else
                                                   project.toString)),
    ("claim", if requestKind == "file" then .str requestedClaim else .null),
    ("execution", if requestKind == "file" then .str "checked" else .null),
    ("configuration", configurationBefore)]
  let registration := Json.mkObj [
    ("attempt", .str ctx.attempt), ("rule", .str rule), ("phase", .str phase),
    ("resultPath", .str output.toString), ("stdoutPath", .str (raw / "stdout").toString),
    ("stderrPath", .str (raw / "stderr").toString),
    ("command", toJson (#[binary.toString] ++ command)), ("cwd", .str project.toString),
    ("environment", toJson corpusEnv), ("request", request), ("before", before)]
  save (raw / "registered.json") registration
  let started ← IO.monoMsNow
  let execution ← observe project binary (raw / "stdout") (raw / "stderr") command
  let elapsed := (← IO.monoMsNow) - started
  IO.println s!"driver span: process wait: {elapsed}ms"
  let loggedMs := (execution.stdout.splitOn "\n").foldl (fun acc line =>
    if line.endsWith "ms (finished)" then
      acc + ((((line.splitOn ": ").getLast!).splitOn "ms").head!).toNat?.getD 0
    else acc) 0
  IO.println s!"driver span: detector logged-phase total: {loggedMs}ms (child elapsed {elapsed}ms)"
  let terminal := Json.mkObj
      [("registration", registration), ("exitCode", toJson execution.exitCode.toNat),
    ("stdout", .str execution.stdout), ("stderr", .str execution.stderr),
    ("detectorMillis", toJson elapsed)]
  save (raw / "terminal.json") terminal
  let mut after := Json.mkObj [("sources", ← snapshot paths), ("configuration", Json.mkObj [
    ("uri", .str project.toString), ("source", .str (← configuration configPaths).compress)])]
  let terminal := terminal.setObjVal! "after" after
  save (raw / "terminal.json") terminal
  requireChecks
      [⟨s!"{rule}/{phase}: missing terminal result\n{execution.stdout}{execution.stderr}",
          ← output.pathExists⟩,
    ⟨s!"{rule}/{phase}: process failed/timed out",
        !#[124, 125, 126, 127, 137].contains execution.exitCode⟩]
  let evidenceStart ← IO.monoMsNow
  let rawObservation := terminal.setObjVal! "resultIdentity" (← digest root output)
  save (raw / "terminal.json") rawObservation
  let observed ← readJson output
  if let .error problem := Regula.Checker.ResultProtocol.admitGuidance observed then
    throw <| IO.userError s!"{rule}/{phase}: result guidance: {problem}"
  IO.println s!"driver span: raw digest/read/parse/projection: {(← IO.monoMsNow) - evidenceStart}ms"
  let mut replacements := [("$PROJECT", project.toString), ("$SOURCE", sourcePath.toString),
    ("$MISSING", (project / "Missing.lean").toString),
    ("$SOURCE_TEXT", ← IO.FS.readFile sourcePath),
    ("$DOCS", (project / "docs").toString)]
  if mode == "project" then
    let captured ← match field observed "sourceAccount" with
      | .ok value => IO.ofExcept value.getArr?
      | .error _ => pure #[]
    let account ← if captured.isEmpty then entries (← get observed "scope") "sources" else
      captured.mapM fun s => return Json.mkObj
                              [("module", ← get s "moduleName"), ("path", ← get s "path"),
                                  ("source", ← get s "content")]
    let candidates ← account.filterM fun s => return (← get s "module") == nameJson "Example"
    let #[item] := candidates | throw <| IO.userError "project example source account mismatch"
    let originalSources ← entries before "sources"
    let some original := originalSources[0]? | throw <| IO.userError "missing frozen source"
    let actualSource ← string item "source"
    let actualPath ← string item "path"
    requireChecks [⟨"project source binding", actualSource == (← string original "source")⟩,
      ⟨"fresh project source belongs to owned copy", actualPath.startsWith
          ((project / "tmp").toString ++ "/")⟩]
    replacements := ("$SOURCE", actualPath) :: replacements.filter (·.1 != "$SOURCE")
    let sourceAlias := Json.mkObj [("uri", .str actualPath), ("source", .str actualSource)]
    before := before.setObjVal! "sources" (toJson (originalSources.push sourceAlias))
    after := after.setObjVal! "sources" (toJson ((← entries after "sources").push sourceAlias))
  if mode == "documentation" && case == "Violation" then
    if let .ok raw := field spec "snippet" then
      let values ← IO.ofExcept raw.getArr?
      let #[start, stop, origin] := values | throw <| IO.userError "invalid snippet range"
      let start ← IO.ofExcept start.getNat?
      let stop ← IO.ofExcept stop.getNat?
      let bytes ← IO.FS.readBinFile sourcePath
      requireChecks [⟨"snippet byte bounds", start ≤ stop && stop ≤ bytes.size⟩]
      let some snippet := String.fromUTF8? (bytes.extract start stop) | throw <|
                                                                         IO.userError
                                                                             "invalid UTF-8 snippet"
      let uri := (project / "docs").toString ++ "/" ++ (← IO.ofExcept origin.getStr?) ++
          "#lean-snippet"
      replacements := [("$SNIPPET_URI", uri), ("$SNIPPET_TEXT", snippet)] ++ replacements
      let sourceAlias := Json.mkObj [("uri", .str uri), ("source", .str snippet)]
      before := before.setObjVal! "sources" (toJson ((← entries before "sources").push sourceAlias))
      after := after.setObjVal! "sources" (toJson ((← entries after "sources").push sourceAlias))
  let expected ← if case == "Fixed" then pure (toJson (#[] : Array Json)) else do
    let template ← get spec "diagnostics"
    pure (← IO.ofExcept (RegulaQualification.Template.instantiate
      (RegulaQualification.Template.replace replacements) 64 template)).val
  let record := Regula.Checker.RuleExampleProjection.record [
    ("rule", .str rule), ("phase", .str phase), ("kind", .str kind), ("mode", ← get spec "mode"),
    ("sourcePath", .str s!"examples/rules/{rule}/{sourceName}"), ("source", .str displayed),
    ("command", toJson (#[binary.toString] ++ command)),
    ("exitCode", toJson execution.exitCode.toNat),
    ("before", before), ("after", after), ("request", request), ("expected", expected),
    ("rawObservation", rawObservation),
    ("unresolvedPatterns", if case == "Fixed" then toJson (#[] : Array Json) else
                                                    (field spec "unresolvedPatterns").toOption.getD
                                                    (toJson (#[] : Array Json))),
    ("stdout", .str execution.stdout), ("stderr", .str execution.stderr),
    ("detectorMillis", toJson elapsed)]
    (Regula.Checker.RuleExampleProjection.resultView observed)
  let recordStart ← IO.monoMsNow
  save (raw / "record.json") record
  IO.println s!"driver span: save record transport: {(← IO.monoMsNow) - recordStart}ms"
  return record

/-- Admit one real special production individually. Each is kept for an external
boundary: the producer's own account of the request it ran under (wrong claim) or of
its documentation classification (trusted and negative fences). What admission then
concludes from any record is proved universally (`RuleExampleQualification.qualify_sound`). -/
private def admitRecord (ctx : Context) (record : Json) (refusal : Option String := none) :
    IO Unit := do
  let current := ctx.rawDirectory / "current.json"
  let currentStart ← IO.monoMsNow
  save current
      (Json.mkObj
          [("checkerBefore", ctx.checkerBefore),
              ("checkerAfter", ← snapshotCached ctx.cache ctx.checkerPaths),
              ("records", toJson #[record])])
  IO.println s!"driver span: save current transport: {(← IO.monoMsNow) - currentStart}ms"
  let admissionStart ← IO.monoMsNow
  let checked ← run ctx.root (ctx.root / ".lake/build/bin/ruleExampleQualification").toString
      #["--record", current.toString] cleanEnv
  IO.println s!"driver span: admission subprocess: {(← IO.monoMsNow) - admissionStart}ms"
  requireChecks [⟨s!"corpus record admission: {checked.stdout}{checked.stderr}", match refusal with
    | none => checked.exitCode == 0
    | some reason => checked.exitCode != 0 && (checked.stdout ++ checked.stderr).contains reason⟩]

/-- The checker, corpus and configuration sources whose exact bytes a campaign records before
and after production (`checkerBefore`, `checkerAfter`): the Lake-discovered root-package module
sources, the toolchain, Lake configuration and manifest, and every corpus file. The site builder
recomputes this set to require that exported evidence belongs to the current sources. -/
def sourcePaths (root : FilePath) (modulePaths : Array FilePath) : IO (Array FilePath) := do
  let corpusPaths ← (← (root / "examples/rules").walkDir).filterM fun path => return !(← path.isDir)
  return (modulePaths ++
      #[root / "lean-toolchain", root / "lakefile.lean", root / "lake-manifest.json"] ++
          corpusPaths).toList.eraseDups.toArray

/-- The rule pair validated together by the fresh-project producer oracle, which requires
one shared elaborated theorem type; the pair must therefore share a shard. -/
def sharedTheoremTypeRules : String × String := ("RG5001", "RG5002")

/-- The rule whose corpus position decides `key`'s shard: the first rule of
`sharedTheoremTypeRules` for the second when the first is in the corpus, otherwise `key`. -/
def shardAnchor (keys : Array String) (key : String) : String :=
  if key == sharedTheoremTypeRules.2 && keys.contains sharedTheoremTypeRules.1 then
    sharedTheoremTypeRules.1 else key

/-- The 1-based shard of `key` among `count` shards: its anchor's corpus position
modulo `count`. -/
def shardOf (keys : Array String) (count : Nat) (key : String) : Option Nat :=
  (keys.idxOf? (shardAnchor keys key)).map fun position => position % count + 1

/-- Corpus rules selected for this run: the complete corpus, an explicit scoped list, or
shard `index` of `count` (every rule whose `shardOf` is `index`). -/
def selectRules (keys : Array String) (selection : Option (Array String))
    (shard : Option (Nat × Nat)) : Array String :=
  match shard with
  | some (index, count) => keys.filter fun key => shardOf keys count key == some index
  | none => selection.getD keys

/-- A rule is selected by shard `index` exactly when it is a corpus rule whose single
`shardOf` value is `index`, so no rule is in two shards. -/
theorem mem_selectRules_shard (keys : Array String) (index count : Nat) (key : String) :
    key ∈ selectRules keys none (some (index, count)) ↔
      key ∈ keys ∧ shardOf keys count key = some index := by
  simp [selectRules]

/-- A corpus rule's shard anchor is itself a corpus rule. -/
theorem shardAnchor_mem (keys : Array String) (key : String) (h : key ∈ keys) :
    shardAnchor keys key ∈ keys := by
  unfold shardAnchor
  split
  · simp_all
  · exact h

/-- Every corpus rule is selected by some shard `index` with `1 ≤ index ≤ count`; with
`mem_selectRules_shard`, the `count` shards partition the corpus. -/
theorem mem_selectRules_some_shard (keys : Array String) (count : Nat) (key : String)
    (h : key ∈ keys) (hc : 0 < count) :
    ∃ index, 1 ≤ index ∧ index ≤ count ∧ key ∈ selectRules keys none (some (index, count)) := by
  obtain ⟨position, hp⟩ := Option.isSome_iff_exists.mp
    (Array.isSome_idxOf?.mpr (shardAnchor_mem keys key h))
  refine ⟨position % count + 1, by omega, Nat.mod_lt _ hc, ?_⟩
  rw [mem_selectRules_shard]
  exact ⟨h, by simp [shardOf, hp]⟩

/-- RG5001 and RG5002 always land in the same shard while RG5001 is in the corpus. -/
theorem rg5001_rg5002_same_shard (keys : Array String) (count : Nat)
    (h : sharedTheoremTypeRules.1 ∈ keys) :
    shardOf keys count sharedTheoremTypeRules.2 = shardOf keys count sharedTheoremTypeRules.1 := by
  simp only [sharedTheoremTypeRules] at h ⊢
  simp [shardOf, shardAnchor, sharedTheoremTypeRules, h]

/-- At most this many producer Tasks are launched and not yet consumed
(`CorpusWindow.launched_le`). -/
def producerWidth : Nat := 5

/-- The completed-corpus export, the only writer of outcome `COMPLETED`. It takes the
cleanup witness of the campaign's own scratch, which exists only after every producer
join, the terminal admission, the shared-identity check, slot deletion and scratch
removal have returned. It records what finished, not a run verdict: the run's verdict
is its exit status, and a deadline kill after this save still fails the run. -/
private def saveCompleted (evidence : FilePath) (fields : List (String × Json))
    (records : Array Json) (_cleaned : Cleaned) : IO Unit :=
  save evidence (Regula.Checker.RuleExampleProjection.corpus
    (("outcome", .str "COMPLETED") :: fields) records)

/-- Full corpus, explicit scoped selection, or one corpus shard; all records and admission
controls are exported. No partial export is labelled a successfully qualified complete
corpus. Every canonical record is admitted exactly once, by the terminal corpus admission;
the three special refusal productions are admitted individually. Former derived admission
mutations (relabelled demonstrations, stale displayed sources, dropped source accounts)
and in-process per-record mutations are replaced by `qualify_sound`, which covers every
record rather than sampled edits. Each production runs in its own fresh
workspace, so no restored rerun repeats an earlier production (standard §7.8). -/
def check (evidence : FilePath) (selection : Option (Array String))
    (suppliedAttempt : Option String := none) (shard : Option (Nat × Nat) := none) : IO Unit := do
  let attempt ← match suppliedAttempt with
    | some attempt => pure attempt
    | none => freshAttempt
  beginAttempt evidence attempt
  let root ← rootDirectory
  let evidence ← IO.FS.realPath evidence
  let rawDirectory := FilePath.mk (evidence.toString ++ ".raw/" ++ attempt)
  requireChecks [⟨"fresh raw observation attempt", !(← rawDirectory.pathExists)⟩]
  IO.FS.createDirAll rawDirectory
  let specs ← readJson (root / "examples/rules/corpus.json")
  let keys := (← IO.ofExcept specs.getObj?).toList.map Prod.fst |>.toArray
  let selected := selectRules keys selection shard
  requireChecks
      [⟨"nonempty known unique selected rules", !selected.isEmpty && selected.all keys.contains &&
          decide selected.toList.Nodup⟩]
  let inventory ← Regula.Checker.Lake.surfaceInventory root
  let modulePaths := inventory.moduleSources.map Prod.snd
  let checkerPaths ← sourcePaths root modulePaths
  let cache ← IO.mkRef SnapshotCache.empty
  let checkerBefore ← snapshotCached cache checkerPaths
  let complete := selection.isNone && shard.isNone
  let shardField := toJson (shard.map fun (index, count) => s!"{index}/{count}")
  save evidence (Json.mkObj [("outcome", .str "INCOMPLETE"),
    ("schemaVersion", toJson (1 : Nat)), ("completeCorpus", .bool complete), ("shard", shardField),
    ("attempt", .str attempt), ("rawDirectory", .str rawDirectory.toString),
    ("selected", toJson selected), ("checkerBefore", checkerBefore)])
  let ((finalFields, records), cleaned) ← withScratchCleaned root "rule-examples" fun scratch => do
    let ctx : Context :=
        ⟨root, scratch, specs, checkerPaths, checkerBefore, attempt, rawDirectory, cache⟩
    -- One private ROOT copy shared by every producer. Its only writers are this
    -- preparation; the shared identity below refuses unless its recorded content at
    -- the end equals the content before any producer started.
    let slot : Slot.ProducerSlot := ⟨scratch / "slot"⟩
    IO.FS.createDirAll slot.root
    let configNames ← (#["lean-toolchain", "lakefile.lean", "lake-manifest.json",
      "foundation_manifest.json"] : Array String).filterM
        (fun (name : String) => (root / name).pathExists)
    let rootConfigs ← configNames.mapM (fun (name : String) => do
      pure (root / name, ← IO.FS.readBinFile (root / name)))
    let rootSources ← modulePaths.mapM fun path => do
      pure (path, ← IO.FS.readBinFile path)
    let depObservations ← Regula.Checker.Snapshot.dependencies inventory
    let _ ← Slot.prepareSlot root slot rootSources rootConfigs depObservations
    let dependencyRoots := depObservations.map (·.root)
    -- Capture once before any producer starts: the runner's own complete
    -- dependency capture. Producers receive only its Git facts, keyed by the
    -- exact capture request, and still read every byte themselves.
    let onceCaptures ← Regula.Checker.Snapshot.dependenciesCaptures inventory
    requireChecks [⟨"capture-once roots match the captured dependencies",
      onceCaptures.map (·.root) == dependencyRoots⟩]
    save (rawDirectory / "injected-git-facts.json")
      (toJson (onceCaptures.map Regula.Checker.Snapshot.DependencyCaptures.gitFacts))
    -- No-writer backstop over every shared tree: content-level identity of the
    -- captured dependency roots and the shared ROOT copy, taken before any producer
    -- starts and required equal after every producer has been joined.
    let sharedRoots := dependencyRoots.push (← IO.FS.realPath (slot.root / "root"))
    let sharedBefore ← Slot.sharedIdentity sharedRoots
    let mut records : Array Json := #[]
    let mut controls : Array Json := #[]
    -- Pooled productions (`CorpusWindow.productions`): the record jobs, then the
    -- selected special refusal controls, consumed in this fixed order. With the
    -- duplicate-free selection checked above, `productions_nodup` gives each its own
    -- `(rule, phase)` workspace.
    let productions := (RegulaQualification.CorpusWindow.productions selected.toList).toArray
    let recordCount := (RegulaQualification.CorpusWindow.records selected.toList).length
    let total := productions.size
    -- Special source reads happen inside their own selected producer jobs
    -- (scoped selections never read unselected specials' sources); a captured
    -- IO error fails that job's task and is delivered at its original job order.
    let produceJob (index : Nat) : IO Json := do
      let some (rule, phase) := productions[index]?
        | throw <| IO.userError s!"internal error: corpus production {index} outside the pool"
      match rule, phase with
        | "RG1005", "WrongClaim" =>
          produce ctx slot rule phase
            (some (← IO.FS.readFile (root / "examples/rules/RG1005/Violation.lean")))
            (some "standard-logical")
        | "RG4004", "TrustedControl" =>
          produce ctx slot rule phase (some ("<!-- lean-trusted-compiler -->\n```lean\n" ++
            (← IO.FS.readFile (root / "examples/rules/RG1004/Violation.lean")) ++ "```\n"))
        | "RG4004", "NegativeControl" =>
          produce ctx slot rule phase
            (some "<!-- lean-fail: Unknown identifier -->\n```lean\n#check missingExample\n```\n")
        | _, _ => produce ctx slot rule phase
    -- At most `producerWidth` concurrent producers, each in its own fresh workspace.
    -- Every launch and the consumption order come from the pure `CorpusWindow` state:
    -- `launch_order` shows the launches name jobs `0, 1, …, total - 1` once each in
    -- that order, so `pending[i]` is job `i`'s Task, and `launched_le` bounds the
    -- unconsumed Tasks by the width. Drain every launched task before scratch
    -- cleanup, including on a refusal.
    let pending ← IO.mkRef (#[] : Array (Task (Except IO.Error Json)))
    let launch (job : Nat) : IO Unit := do
      let task ← IO.asTask (produceJob job)
      pending.modify (·.push task)
    let initial := RegulaQualification.CorpusWindow.init producerWidth total
    for job in List.range initial.launched do
      launch job
    try
      let mut window := initial
      for _ in [:total] do
        let index := window.consumed
        let some task := (← pending.get)[index]?
          | throw <| IO.userError s!"internal error: corpus task {index} was not launched"
        let record ← match (← IO.wait task) with
          | .ok value => pure value
          | .error error => throw error
        if index < recordCount then
          records := records.push record
        else
          controls := controls.push record
        if let some job := RegulaQualification.CorpusWindow.refill window then
          launch job
        window := RegulaQualification.CorpusWindow.consume window
        if index < recordCount then
          IO.println
              s!"{← string record "rule"}/{← string record "phase"}: \
                produced {← string record "kind"}"
          (← IO.getStdout).flush
        else
          -- Special refusal controls: completed producer outcome, then the intended
          -- admission refusal.
          match productions[index]? with
          | some ("RG1005", "WrongClaim") =>
            requireChecks
                [⟨"Standard-Logical producer control completes", (← get record "exitCode") == toJson
                    (0 : Nat) && (← string (← get record "result") "status") == "completed"⟩]
            admitRecord ctx record (some "producer request differs from frozen example request")
          | _ =>
            requireChecks
                [⟨"nonpositive documentation classifies", (← get record "exitCode") == toJson
                    (0 : Nat) && (← string (← get record "result") "status") == "classified"⟩]
            admitRecord ctx record
                (some "documentation correction requires completed positive fences")
    finally
      for task in ← pending.get do
        let _ ← IO.wait task
        pure ()
    -- The fresh-project producer controls: the corpus `sharedTheoremTypeRules` records are the
    -- only fresh-project runs of those fixtures, so the producer oracle validates these
    -- same observations (one shared elaborated theorem type, as in the producer campaign).
    let mut theoremType : Option Json := none
    for record in records do
      let rule ← string record "rule"
      unless rule == sharedTheoremTypeRules.1 || rule == sharedTheoremTypeRules.2 do continue
      let report ← get record "result"
      let account ← IO.ofExcept (RegulaQualification.Producer.account report)
      let declarations ← entries account "declarations"
      let some declaration := declarations[0]? | throw <| IO.userError "missing theorem declaration"
      let expectedType := theoremType.getD (← get declaration "type")
      theoremType := some expectedType
      let phase ← string record "phase"
      IO.ofExcept (RegulaQualification.Producer.checked_validation.run report
        (← IO.ofExcept (← get record "exitCode").getNat?) rule "freshProject"
        (← string record "source")
        (phase == "Fixed") expectedType)
      IO.println s!"fresh project producer {rule}/{phase}: PASS"
    let finalFields := [("schemaVersion", toJson (1 : Nat)), ("completeCorpus", .bool complete),
      ("shard", shardField), ("attempt", .str attempt),
      ("rawDirectory", .str rawDirectory.toString),
      ("selected", toJson selected), ("checkerBefore", checkerBefore),
      ("checkerAfter", ← snapshotCached cache checkerPaths), ("admissionControls", toJson controls)]
    save evidence
        (Regula.Checker.RuleExampleProjection.corpus
            (("outcome", .str "INCOMPLETE") :: finalFields) records)
    -- The single admission of every canonical record: the terminal corpus qualifier.
    let checked ← run root (root / ".lake/build/bin/ruleExampleQualification").toString
      #[evidence.toString] cleanEnv
    requireChecks [⟨s!"corpus admission: {checked.stdout}{checked.stderr}", checked.exitCode == 0⟩]
    requireChecks
        [⟨"terminal checker sources changed", (← snapshotCached cache checkerPaths) ==
            checkerBefore⟩]
    -- The campaign's one dependency recheck: the product's own terminal decision on
    -- the once-captured value (fresh Lake inventory, fresh reads and fresh Git).
    Regula.Checker.Snapshot.inputsUnchanged inventory
      (onceCaptures.map Regula.Checker.Snapshot.observe)
    let sharedAfter ← Slot.sharedIdentity sharedRoots
    requireChecks
        [⟨s!"shared trees changed during the producer \
          window: {sharedBefore.difference sharedAfter}",
      sharedAfter == sharedBefore⟩]
    -- Every producer (including child/stream joins), admission subprocess and the
    -- terminal qualifier has finished. Authenticate the owned slot before deletion;
    -- retained evidence lives outside scratch. Complete deletion precedes the
    -- COMPLETED save, which needs the scratch cleanup witness.
    let expected := (← IO.FS.realPath scratch) / "slot"
    requireChecks [⟨"contained owned cleanup slot", (← IO.FS.realPath slot.root) == expected &&
      (← slot.root.symlinkMetadata).type == .dir⟩]
    IO.FS.removeDirAll slot.root
    return (finalFields, records)
  saveCompleted evidence finalFields records cleaned
  IO.println s!"rule example campaign: COMPLETED ({selected.size} selected rules; diagnostic \
    evidence only; the run verdict is the exit status)"
end Regula.Qualification.RuleExamples
