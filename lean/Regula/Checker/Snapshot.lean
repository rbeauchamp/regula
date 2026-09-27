import Regula.Checker.Lake
import Regula.Checker.Producer
import RegulaPolicy.Claim

/-! Exact request snapshots of Lake-resolved sources and configuration, with nominal
Git revisions and input-scoped dirty status where available. These are IO observations,
not kernel authentication of a filesystem or compiled artifact. The request state is
derived purely from the exact captures (`stateOfCore`) and carried with its derivation
invariant. The terminal decision always executes the retired observation/state `BEq`
chain on the completed values; only the state construction is cached and reused at
proved equal captures. -/
namespace Regula.Checker.Snapshot
open Lean System RegulaPolicy

/-- Pure request-state derivation from exact captures. The `mkObj` shape and key
order are exactly the state previously built inside `dependency`; request bytes
are unchanged. -/
def stateOfCore (root : String) (revision : Option String)
    (sourceCaptures : Array (Name × String × String × String))
    (configurationCaptures : Array (String × Option (String × ByteArray))) : Json :=
  Json.mkObj [("root", toJson root), ("revision", toJson revision),
    ("sources", toJson (sourceCaptures.map fun (module, path, canonical, source) =>
      Json.mkObj [("module", toJson module), ("path", toJson path),
        ("canonical", toJson canonical), ("source", toJson source)])),
    ("configuration", toJson (configurationCaptures.map fun (path, entry) =>
      match entry with
      | none => Json.mkObj [("path", toJson path), ("bytes", Json.null)]
      | some (canonical, bytes) => Json.mkObj [("path", toJson path),
        ("canonical", toJson canonical), ("bytes", toJson (bytes.toList.map UInt8.toNat))]))]

/-- Equal captures give equal request state (kernel-only congruence); this holds
for any comparator, including the opaque core `Json` `BEq`. -/
theorem stateOfCore_congruence {root root' : String} {revision revision' : Option String}
    {sourceCaptures sourceCaptures' : Array (Name × String × String × String)}
    {configurationCaptures configurationCaptures' :
      Array (String × Option (String × ByteArray))}
    (hr : root = root') (hv : revision = revision')
    (hs : sourceCaptures = sourceCaptures')
    (hc : configurationCaptures = configurationCaptures') :
    stateOfCore root revision sourceCaptures configurationCaptures
      = stateOfCore root' revision' sourceCaptures' configurationCaptures' := by
  rw [hr, hv, hs, hc]

/-- Any request-state difference implies a difference in the exact captures, so
every input change visible to the request state still changes the executed
comparison. -/
theorem captures_ne_of_stateOfCore_ne {root root' : String} {revision revision' : Option String}
    {sourceCaptures sourceCaptures' : Array (Name × String × String × String)}
    {configurationCaptures configurationCaptures' :
      Array (String × Option (String × ByteArray))}
    (h : stateOfCore root revision sourceCaptures configurationCaptures
      ≠ stateOfCore root' revision' sourceCaptures' configurationCaptures') :
    ¬(root = root' ∧ revision = revision' ∧ sourceCaptures = sourceCaptures'
      ∧ configurationCaptures = configurationCaptures') := by
  intro he
  rw [he.1, he.2.1, he.2.2.1, he.2.2.2] at h
  exact h rfl

/-- Exact dependency captures at one freeze point: the raw bytes/texts observed
by fresh reads, before any request-state construction. -/
structure DependencyCaptures where
  project : FilePath
  package : String
  root : FilePath
  revision : Option String
  dirty : Bool
  sourcePaths : Array (Name × FilePath)
  sourceCaptures : Array (Name × String × String × String)
  configurationCaptures : Array (String × Option (String × ByteArray))

/-- An actual dependency observation: exact captures plus the request state
derived from them, including dirty/path state, not only a lockfile pin. The
`state_sound` field carries the derivation invariant by type, so any carried
state value is known to be the pure derivation of the carried captures. -/
structure DependencyObservation where
  project : FilePath
  package : String
  root : FilePath
  revision : Option String
  dirty : Bool
  sourcePaths : Array (Name × FilePath)
  sourceCaptures : Array (Name × String × String × String)
  configurationCaptures : Array (String × Option (String × ByteArray))
  state : Json
  state_sound : state = stateOfCore root.toString revision sourceCaptures configurationCaptures

/-- The carried request state is exactly the pure derivation of the carried
captures (kernel-only). -/
theorem observation_state_sound (o : DependencyObservation) :
    o.state = stateOfCore o.root.toString o.revision o.sourceCaptures o.configurationCaptures :=
  o.state_sound

/-- Retained observation shape: captures plus the request state freshly derived
from them. -/
def observe (fresh : DependencyCaptures) : DependencyObservation where
  project := fresh.project
  package := fresh.package
  root := fresh.root
  revision := fresh.revision
  dirty := fresh.dirty
  sourcePaths := fresh.sourcePaths
  sourceCaptures := fresh.sourceCaptures
  configurationCaptures := fresh.configurationCaptures
  state := stateOfCore fresh.root.toString fresh.revision fresh.sourceCaptures
    fresh.configurationCaptures
  state_sound := rfl

/-- Complete a fresh capture into the retained observation shape. At proved
exact equality of the request-state inputs it reuses the retained request-state
value instead of rebuilding it; otherwise it rebuilds from the fresh captures.
Every completed value is a `DependencyObservation`, so the derivation invariant
holds by type in both branches. -/
def completeObservation (before : DependencyObservation) (fresh : DependencyCaptures) :
    DependencyObservation :=
  if h : before.root = fresh.root ∧ before.revision = fresh.revision ∧
      before.sourceCaptures = fresh.sourceCaptures ∧
      before.configurationCaptures = fresh.configurationCaptures then
    { project := fresh.project, package := fresh.package, root := fresh.root,
      revision := fresh.revision, dirty := fresh.dirty, sourcePaths := fresh.sourcePaths,
      sourceCaptures := fresh.sourceCaptures,
      configurationCaptures := fresh.configurationCaptures,
      state := before.state,
      state_sound := by rw [← h.1, ← h.2.1, ← h.2.2.1, ← h.2.2.2]; exact before.state_sound }
  else
    { project := fresh.project, package := fresh.package, root := fresh.root,
      revision := fresh.revision, dirty := fresh.dirty, sourcePaths := fresh.sourcePaths,
      sourceCaptures := fresh.sourceCaptures,
      configurationCaptures := fresh.configurationCaptures,
      state := stateOfCore fresh.root.toString fresh.revision fresh.sourceCaptures
        fresh.configurationCaptures,
      state_sound := rfl }

/-- Cache-reuse equality: at proved equality of the request-state inputs the
completed observation carries the retained cached value (kernel-only). -/
theorem completeObservation_reuse {before : DependencyObservation} {fresh : DependencyCaptures}
    (h : before.root = fresh.root ∧ before.revision = fresh.revision ∧
      before.sourceCaptures = fresh.sourceCaptures ∧
      before.configurationCaptures = fresh.configurationCaptures) :
    (completeObservation before fresh).state = before.state := by
  unfold completeObservation
  rw [dite_eq_left h]

/-- The cached retained value equals any fresh construction at the same captures
(kernel-only congruence). With `completeObservation_reuse`, the executed
comparator therefore receives exactly the retired values even on cache reuse,
while the comparator itself stays opaque and always executes. -/
theorem stateOfCore_reuse_eq {before : DependencyObservation} {fresh : DependencyCaptures}
    (h : before.root = fresh.root ∧ before.revision = fresh.revision ∧
      before.sourceCaptures = fresh.sourceCaptures ∧
      before.configurationCaptures = fresh.configurationCaptures) :
    before.state = stateOfCore fresh.root.toString fresh.revision fresh.sourceCaptures
      fresh.configurationCaptures := by
  rw [before.state_sound, h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- The retained complete observation/state `BEq` decision: exactly the retired
structural `BEq` chain, same field set and order, over the carried request-state
values. This predicate always executes; nothing is substituted for its result. -/
def legacyBeq (a b : DependencyObservation) : Bool :=
  (a.project == b.project) && (a.package == b.package) && (a.root == b.root) &&
    (a.revision == b.revision) && (a.dirty == b.dirty) && (a.state == b.state) &&
    (a.sourcePaths == b.sourcePaths)

/-- The retained terminal decision over observation arrays: the retired
`Array.isEqv`/`BEq` shape over `legacyBeq`, executed on the completed fresh
values. Size correspondence is checked first, as in the retired array `BEq`. -/
def terminalBeq (fresh : Array DependencyCaptures) (before : Array DependencyObservation) : Bool :=
  fresh.size = before.size &&
    Array.isEqv (Array.zipWith completeObservation before fresh) before legacyBeq

/-- Fresh exact configuration capture: original path, canonical path and raw
bytes, with presence preserved. -/
private def captureConfiguration (path : FilePath) :
    IO (String × Option (String × ByteArray)) := do
  if !(← path.pathExists) then return (path.toString, none)
  let canonical ← IO.FS.realPath path
  let bytes ← IO.FS.readBinFile canonical
  return (path.toString, some (canonical.toString, bytes))

/-- One record of `git status --porcelain=v1 -z`: the reported path and, for a
rename or copy on either side, its original path. A field that is not UTF-8 is kept
as `none`: its bytes cannot equal a declared input, and no `…/` prefix of a UTF-8
input can contain it, so dropping it cannot hide a declared input. -/
structure StatusEntry where
  path : Option String
  original : Option String := none
  deriving BEq, Repr, Inhabited

/-- Every UTF-8 path an entry reports. -/
def StatusEntry.paths (entry : StatusEntry) : List String :=
  entry.path.toList ++ entry.original.toList

/-- A reported root-relative path covers a declared input when it is the input
itself or an ancestor directory. Git reports a collapsed ignored or untracked
directory (including an untracked nested repository) as `dir/`, and a gitlink as
`dir`, so both spellings are treated as directories. -/
def statusCovers (reported input : String) : Bool :=
  input == reported ||
    (if reported.endsWith "/" then reported else reported ++ "/").isPrefixOf input

/-- A declared input is dirty when some reported path covers it. -/
def inputDirty (entries : List StatusEntry) (input : String) : Bool :=
  entries.any fun entry => entry.paths.any fun reported => statusCovers reported input

/-- Dependency dirty status: membership of the declared inputs in one unrestricted
status of the dependency root. -/
def dirtyOf (entries : List StatusEntry) (inputs : List String) : Bool :=
  inputs.any (inputDirty entries)

/-- Model of the retired pathspec-limited status: exactly the entries of the
unrestricted status that cover some declared input. -/
def restrictedStatus (entries : List StatusEntry) (inputs : List String) : List StatusEntry :=
  entries.filter fun entry => inputs.any fun input => entry.paths.any fun reported =>
    statusCovers reported input

/-- Membership characterization of the executed dirty decision. -/
theorem dirtyOf_iff {entries : List StatusEntry} {inputs : List String} :
    dirtyOf entries inputs = true ↔
      ∃ input ∈ inputs, ∃ entry ∈ entries, ∃ reported ∈ entry.paths,
        statusCovers reported input = true := by
  simp [dirtyOf, inputDirty]

/-- The executed decision is non-emptiness of the modeled restricted status: the
retired pathspec decision whenever Git's restricted output is that model. -/
theorem dirtyOf_eq_restricted {entries : List StatusEntry} {inputs : List String} :
    dirtyOf entries inputs = !(restrictedStatus entries inputs).isEmpty := by
  cases h : dirtyOf entries inputs
  · simp_all only [dirtyOf, List.any_eq_false, inputDirty, List.any_eq_true, not_exists, not_and,
      Bool.not_eq_true, restrictedStatus, Bool.false_eq, Bool.not_eq_eq_eq_not, Bool.not_false,
      List.isEmpty_iff, List.filter_eq_nil_iff]
    exact fun entry he input hi reported hr => h input hi entry he reported hr
  · simp_all only [dirtyOf, List.any_eq_true, inputDirty, restrictedStatus, Bool.true_eq,
      Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff, ne_eq,
      List.filter_eq_nil_iff, not_exists, not_and, Bool.not_eq_true, Classical.not_forall,
      Bool.not_eq_false]
    obtain ⟨input, hi, entry, he, reported, hr, hc⟩ := h
    exact ⟨entry, he, input, hi, reported, hr, hc⟩

/-- A clean status leaves every declared input clean. -/
theorem dirtyOf_nil {inputs : List String} : dirtyOf [] inputs = false := by
  simp [dirtyOf, inputDirty]

/-- Additional reported entries can only make the decision dirtier. -/
theorem dirtyOf_mono {entries entries' : List StatusEntry} {inputs : List String}
    (hsub : ∀ entry ∈ entries, entry ∈ entries') (h : dirtyOf entries inputs = true) :
    dirtyOf entries' inputs = true := by
  rw [dirtyOf_iff] at h ⊢
  obtain ⟨input, hi, entry, he, reported, hr, hc⟩ := h
  exact ⟨input, hi, entry, hsub entry he, reported, hr, hc⟩

/-- Every path covers itself. -/
theorem statusCovers_self (path : String) : statusCovers path path = true := by
  simp [statusCovers]

/-- A path covers every input beneath it as a directory. -/
theorem statusCovers_of_prefix {reported input : String}
    (h : (if reported.endsWith "/" then reported else reported ++ "/").isPrefixOf input = true) :
    statusCovers reported input = true := by
  simp [statusCovers, h]

/-- A declared input reported by any path of any entry (including a rename's
original) is dirty. -/
theorem dirtyOf_of_reported {entries : List StatusEntry} {inputs : List String}
    {entry : StatusEntry} {input : String} (he : entry ∈ entries) (hr : input ∈ entry.paths)
    (hi : input ∈ inputs) : dirtyOf entries inputs = true :=
  dirtyOf_iff.mpr ⟨input, hi, entry, he, input, hr, statusCovers_self input⟩

/-- A declared input beneath a reported directory is dirty. -/
theorem dirtyOf_of_directory {entries : List StatusEntry} {inputs : List String}
    {entry : StatusEntry} {reported input : String} (he : entry ∈ entries)
    (hr : reported ∈ entry.paths) (hi : input ∈ inputs)
    (hp : (if reported.endsWith "/" then reported else reported ++ "/").isPrefixOf input = true) :
    dirtyOf entries inputs = true :=
  dirtyOf_iff.mpr ⟨input, hi, entry, he, reported, hr, statusCovers_of_prefix hp⟩

/-- Whether a porcelain status code letter carries an original-path field. -/
def statusCarriesOriginal (code : UInt8) : Bool :=
  code == 'R'.toNat.toUInt8 || code == 'C'.toNat.toUInt8

/-- Parse NUL-terminated porcelain v1 fields: `XY path` (two status letters, a space and the
path), followed by the original path when either status letter is a rename or copy. Malformed
output is `none`. -/
def parseStatusFields : List ByteArray → Option (List StatusEntry)
  | [] => some []
  | field :: rest =>
    if field.size < 4 || field.get! 2 != ' '.toNat.toUInt8 then none
    else
      let path := String.fromUTF8? (field.extract 3 field.size)
      if statusCarriesOriginal (field.get! 0) || statusCarriesOriginal (field.get! 1) then
        match rest with
        | original :: rest' =>
          (parseStatusFields rest').map ({ path, original := String.fromUTF8? original } :: ·)
        | [] => none
      else (parseStatusFields rest).map ({ path } :: ·)

/-- Split `-z` output into its NUL-terminated fields; `none` when bytes follow the
final NUL. -/
def splitStatusFields (bytes : ByteArray) : Option (List ByteArray) := Id.run do
  let mut fields : Array ByteArray := #[]
  let mut start := 0
  for index in [0:bytes.size] do
    if bytes.get! index == 0 then
      fields := fields.push (bytes.extract start index)
      start := index + 1
  return if start == bytes.size then some fields.toList else none

/-- Lexical normalization as Git applies it to a pathspec: empty and `.`
components are dropped and `..` removes the previous component. -/
private def lexicalComponents (path : FilePath) : List String :=
  path.components.foldl (fun acc component =>
    if component.isEmpty || component == "." then acc
    else if component == ".." then acc.dropLast else acc ++ [component]) []

/-- The root-relative spelling Git gives a declared input when it is passed as a
literal pathspec from the canonical root: relative inputs are resolved against the
root; otherwise the shortest leading directory prefix that is the root, lexically
first and then by `realPath`, is removed and the remainder is kept literally.
`none` when no prefix is the root (Git refuses such a pathspec). -/
private def statusRelative (root path : FilePath) : IO (Option String) := do
  let rootComponents := lexicalComponents root
  let components := lexicalComponents (if path.isAbsolute then path else root / path)
  let relative (count : Nat) : Option String :=
    let rest := components.drop count
    if rest.isEmpty then none else some ("/".intercalate rest)
  if rootComponents.isPrefixOf components then return relative rootComponents.length
  for count in [1:components.length] do
    let candidate := FilePath.mk ("/" ++ "/".intercalate (components.take count))
    if ← candidate.pathExists then
      if (← IO.FS.realPath candidate) == root then return relative count
  return none

/-- One unrestricted `git status` of the canonical root, as raw bytes: file names
in unrelated entries need not be UTF-8. -/
private def statusBytes (root : FilePath) : IO (UInt32 × ByteArray) := do
  let child ← IO.Process.spawn {
    cmd := "git", cwd := some root, stdin := .null, stdout := .piped, stderr := .piped
    args := #["status", "--porcelain=v1", "-z", "--untracked-files=all", "--ignored=matching"] }
  let stderr ← IO.asTask child.stderr.readBinToEnd .dedicated
  let stdout ← child.stdout.readBinToEnd
  let _ ← IO.ofExcept stderr.get
  return (← child.wait, stdout)

/-- Input-scoped dirty status: one unrestricted porcelain status of the dependency
root, decided purely by `dirtyOf` over the declared inputs' root-relative paths.
Status failure, malformed output or an input outside the root refuses, as a
failing pathspec status did. -/
private def inputsDirty (root : FilePath) (paths : Array FilePath) : IO Bool := do
  let inputs ← paths.toList.mapM fun path => do
    let some relative ← statusRelative root path
      | throw <| IO.userError "dependency input status unavailable"
    pure relative
  let (exitCode, output) ← statusBytes root
  unless exitCode == 0 do throw <| IO.userError "dependency input status unavailable"
  let some entries := splitStatusFields output >>= parseStatusFields
    | throw <| IO.userError "dependency input status unavailable"
  return dirtyOf entries inputs

/-- The Git-derived part of one dependency capture, together with the exact
capture request it answers: package, canonical root, and the ordered source and
configuration path strings. -/
structure GitFacts where
  package : String
  root : String
  sourcePaths : Array String
  configurationPaths : Array String
  revision : Option String
  dirty : Bool
  deriving ToJson, FromJson, BEq, Inhabited

/-- Qualification-only table of Git facts captured once by the corpus runner
under identity-checked shared dependency roots. It is empty in
every process except one started through the internal qualification entry point
(`ruleExamples --injected-git-facts`); no user-facing checker mode sets it. -/
initialize injectedGitFacts : IO.Ref (Array GitFacts) ← IO.mkRef #[]

/-- The Git facts for one exact capture request: the nominal revision (only for
a dependency that is its own repository) and input-scoped dirty status. One
`rev-parse` prints the revision line and then the top level. It fails when there is
no repository or `HEAD` does not resolve; the two separate calls it replaces then
also yielded no revision, so the facts are unchanged. -/
def observeGitFacts (package : String) (root : FilePath)
    (sourcePaths : Array (Name × FilePath)) (configurationPaths : Array FilePath) :
    IO (Option String × Bool) := do
  let parsed ← runProcess root "git" #["rev-parse", "HEAD", "--show-toplevel"]
  let (head, top) := match parsed.stdout.splitOn "\n" with
    | head :: rest => (head, "\n".intercalate rest)
    | [] => ("", "")
  let ownRepository ← if parsed.succeeded then
    pure ((← IO.FS.realPath (FilePath.mk top.trimAscii.toString)) == root)
    else pure false
  let revision ← if parsed.succeeded && ownRepository then do
      let revision := head.trimAscii.toString
      if revision.isEmpty then throw <| IO.userError s!"empty dependency revision: {package}"
      pure (some revision)
    else pure none
  let dirty ← if revision.isSome then inputsDirty root (sourcePaths.map (·.2) ++ configurationPaths)
    else pure true
  return (revision, dirty)

/-- The exact request key an injected entry must match. -/
def GitFacts.answers (facts : GitFacts) (package : String) (root : FilePath)
    (sourcePaths : Array (Name × FilePath)) (configurationPaths : Array FilePath) : Bool :=
  facts.package == package && facts.root == root.toString &&
    facts.sourcePaths == sourcePaths.map (·.2.toString) &&
    facts.configurationPaths == configurationPaths.map (·.toString)

/-- Pure assembly of one capture from its fresh reads and its Git facts. -/
def assemble (project : FilePath) (package : String) (root : FilePath)
    (sourcePaths : Array (Name × FilePath))
    (sourceCaptures : Array (Name × String × String × String))
    (configurationCaptures : Array (String × Option (String × ByteArray)))
    (facts : Option String × Bool) : DependencyCaptures :=
  { project := project, package := package, root := root, sourcePaths := sourcePaths,
    revision := facts.1, dirty := facts.2,
    sourceCaptures := sourceCaptures, configurationCaptures := configurationCaptures }

/-- Capture-once equality: with the same request and the same fresh reads, an
injected Git-facts pair equal to the pair the process would observe itself
yields the identical capture, hence (`stateOfCore_congruence`) identical request
state and request/report bytes. The premise — equal Git facts — is the
no-writer invariant of the qualification window (equal content identity and
the runner's terminal recheck), not a theorem about Git. -/
theorem assemble_facts_eq {project : FilePath} {package : String} {root : FilePath}
    {sourcePaths : Array (Name × FilePath)}
    {sourceCaptures : Array (Name × String × String × String)}
    {configurationCaptures : Array (String × Option (String × ByteArray))}
    {injected observed : Option String × Bool} (h : injected = observed) :
    assemble project package root sourcePaths sourceCaptures configurationCaptures injected
      = assemble project package root sourcePaths sourceCaptures configurationCaptures observed := by
  rw [h]

/-- Fresh capture of one dependency. Source and configuration bytes are always
read here. The Git facts are observed here too, unless the internal
qualification table holds an entry answering exactly this request, in which case
that once-captured pair is used (`assemble_facts_eq`). -/
def captureDependency (project : FilePath) (package : String) (root : FilePath)
    (sourcePaths : Array (Name × FilePath)) (configurationPaths : Array FilePath) :
    IO DependencyCaptures := do
  let root ← IO.FS.realPath root
  let sourceCaptures ← sourcePaths.mapM fun (name, path) => do
    let canonical ← IO.FS.realPath path
    let bytes ← IO.FS.readBinFile canonical
    let some text := String.fromUTF8? bytes
      | throw <| IO.userError s!"dependency source is not UTF-8: {path}"
    pure (name, path.toString, canonical.toString, text)
  let configurationCaptures ← configurationPaths.mapM captureConfiguration
  let table ← injectedGitFacts.get
  let facts ← match table.find? (·.answers package root sourcePaths configurationPaths) with
    | some injected =>
      IO.println s!"injected git facts: {package} reused"
      pure (injected.revision, injected.dirty)
    | none =>
      unless table.isEmpty do IO.println s!"injected git facts: {package} observed"
      observeGitFacts package root sourcePaths configurationPaths
  return assemble project package root sourcePaths sourceCaptures configurationCaptures facts

/-- The Git facts a completed capture answers, for export by the corpus runner. -/
def DependencyCaptures.gitFacts (c : DependencyCaptures) : GitFacts where
  package := c.package
  root := c.root.toString
  sourcePaths := c.sourcePaths.map (·.2.toString)
  configurationPaths := c.configurationCaptures.map (·.1)
  revision := c.revision
  dirty := c.dirty

/-- Fresh captures of every dependency input, resolved through the frozen Lake
discovery. Every read and Git observation is taken here on every call. -/
def dependenciesCaptures (inventory : Lake.SurfaceInventory) :
    IO (Array DependencyCaptures) :=
  timedPhase "dependency snapshot capture" <| inventory.dependencies.mapM fun entry =>
    captureDependency inventory.root entry.package entry.root
      (entry.sources.map fun source => (source.module, source.source))
      entry.configurationPaths

/-- Resolve dependency names/locations through the frozen Lake discovery,
completing each fresh capture with its request state derived from that capture. -/
def dependencies (inventory : Lake.SurfaceInventory) : IO (Array DependencyObservation) :=
  return (← dependenciesCaptures inventory).map observe

/-- True when the qualification-only injected table answers this captured dependency. -/
def injectedFor (table : Array GitFacts) (o : DependencyObservation) : Bool :=
  table.any (·.answers o.package o.root o.sourcePaths
    (o.configurationCaptures.map fun (path, _) => FilePath.mk path))

/-- Reconcile the frozen Lake root and dependency inputs at the terminal boundary.
Every fresh read and Git observation is retaken; the executed decision is the
retired comparison on the completed values, with only the request-state
construction reused at proved equal captures. Under the internal qualification entry
only, a dependency answered by the injected table is instead rechecked once by the
campaign runner that captured it (its terminal `inputsUnchanged` and content identity);
the dependency inventory itself and every other dependency are still rechecked here. -/
def inputsUnchanged (inventory : Lake.SurfaceInventory)
    (before : Array DependencyObservation) : IO Unit := do
  let current ← timedPhase "terminal Lake inventory" <| Lake.surfaceInventory inventory.root
  unless current.root == inventory.root && current.leanLibDir == inventory.leanLibDir &&
      current.leanPath == inventory.leanPath && current.leanSrcPath == inventory.leanSrcPath &&
      current.libraries == inventory.libraries && current.executables == inventory.executables do
    throw <| IO.userError "root inventory changed: Lake modules, targets or source identities"
  let table ← injectedGitFacts.get
  let unchanged ← if table.isEmpty then do
      pure (terminalBeq (← dependenciesCaptures current) before)
    else do
      let owned := (current.dependencies.zip before).filter fun (_, o) => !injectedFor table o
      let fresh ← timedPhase "dependency snapshot capture" <| owned.mapM fun (entry, _) =>
        captureDependency current.root entry.package entry.root
          (entry.sources.map fun source => (source.module, source.source)) entry.configurationPaths
      pure (current.dependencies == inventory.dependencies && current.dependencies.size == before.size &&
        terminalBeq fresh (owned.map (·.2)))
  unless unchanged do
    throw <| IO.userError "dependency snapshot changed: Lake inventory or source/configuration state"

/-- Exact request bytes include configuration presence/absence and actual dependency state.
Additional imported sources (for example history) are included by the coordinator only
after matching their own before/after producer binding against current source bytes. -/
def make (root : FilePath) (configuration : Array (FilePath × Option String))
    (sources : Array SourceSnapshot) (deps : Array DependencyObservation) : Except String AdmittedSnapshot :=
  admitSnapshot {
    sources
    configuration := ⟨root.toString, (Json.mkObj [
      ("configuration", toJson (configuration.map fun (path, text) => (path.toString, text))),
      ("dependencies", toJson (deps.map fun dep => Json.mkObj [
        ("package", toJson dep.package), ("state", dep.state)]))]).compress⟩
    toolchain := ⟨Lean.versionString, Lean.githash, Producer.identity.sourceRevision⟩
    dependencies := deps.map fun dep => {
      package := dep.package, nominalRevision := dep.revision, dirty := dep.dirty, files := #[] } }

end Regula.Checker.Snapshot
