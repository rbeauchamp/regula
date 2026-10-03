import Lean.Data.Json

/-! # Shared Mathlib provisioning

Dependency provisioning: one shared, read-only Mathlib per pinned revision, exact
compiler and artifact mode, reused by local copies. CI runs the build plan defined here.

Mathlib's `lake exe cache get` downloads its archives once into the shared archive cache
(`~/.cache/mathlib`) but unpacks them into every copy's `.lake/packages`. This program
unpacks them once into `~/.cache/mathlib-packages/<rev>-lean-<githash>/`, keyed by the
exact Mathlib revision pinned in the lock manifest of the Mathlib-dependent package
(`audit/lake-manifest.json`; the root `regula` package requires nothing) and the running
toolchain's commit, builds the modules the upstream cache lacks and every module's exported
native object (so neither an import nor an executable link has to write there), makes that
directory read-only, and points each copy at it:

* `.lake/packages/mathlib` becomes a symbolic link to the shared, read-only checkout. The
  Mathlib-dependent package in `audit/` and the Verso website package name the root
  `.lake/packages` as their packages directory, and isolated copies link it.
* The other packages of Mathlib's closure (Batteries, Aesop, ...) become writable
  copy-on-write clones of the shared checkouts, because executables that import them
  compile native objects into their build directories.

The shared directory is created from a staging directory and made visible by one rename after
it is complete and sealed, so a half-created directory is never used. Its receipt records the
revisions it holds; a copy uses it only when that receipt admits the copy's pins. A registry
beside it records the copies provisioned to link it, and each run removes the shared
directories of other pins, toolchains, artifact modes and source artifact policies that no
registered copy still links; a source directory is identified only in the
`-source-v<policy>-<hash>` form, under the policy its receipt records. One exclusive
lock under `~/.cache/mathlib-packages` orders all of this. The pure planning decisions below
carry proofs; Git, Lake, `cp`, `chmod`, `ln`, rename and file locking are trusted process and
filesystem effects. `dependency-build-mode` selects `upstream-cache` or `source`. The latter
disables Lake's automatic cache and Mathlib's update hook and builds the discovered imports'
transitive exported native closure. Source mode has a separate shared directory and is admitted
only by a source-mode receipt. GitHub Actions invokes the Mathlib and Verso plans defined
here: its upstream-cache Mathlib command only fetches the published artifacts into the job's
writable packages directory, and its source Mathlib command uses the shared directory.

Run `./scripts/provision.sh` once in a fresh copy, before the first `lake build`;
`scripts/verify.sh` runs it before its deadline. -/
namespace RegulaProvision
open System Lean

/-! ## Pure decisions -/

/-- Where dependency artifacts come from. `source` builds with the running compiler. -/
inductive BuildMode where
  /-- Use the dependencies' published artifacts and build only what they lack. -/
  | upstreamCache
  /-- Disable Lake and Mathlib artifact downloads and build from pinned source. -/
  | source
  deriving DecidableEq, Repr, ToJson, FromJson

/-- The spellings admitted in `dependency-build-mode`. -/
def BuildMode.spelling : BuildMode → String
  | .upstreamCache => "upstream-cache"
  | .source => "source"

/-- Decode an explicit mode; an unknown spelling never falls back to downloading artifacts. -/
def buildMode? (text : String) : Option BuildMode :=
  if text == "upstream-cache" then some .upstreamCache
  else if text == "source" then some .source
  else none

/-- Every admitted mode has the exact requested spelling. -/
theorem buildMode?_sound (text : String) (mode : BuildMode)
    (h : buildMode? text = some mode) : mode.spelling = text := by
  unfold buildMode? at h
  split at h
  · cases Option.some.inj h
    simp_all [BuildMode.spelling]
  · split at h
    · cases Option.some.inj h
      simp_all [BuildMode.spelling]
    · simp at h

/-- Environment passed to every dependency command and its descendants. Source mode uses
an owned fresh artifact cache, retained with the workspace if package settings enable it. -/
def buildEnvironment (sourceCache : String) : BuildMode → Array (String × Option String)
  | .upstreamCache => #[]
  | .source => #[("LAKE_NO_CACHE", some "true"), ("MATHLIB_NO_CACHE_ON_UPDATE", some "1"),
      ("LAKE_ARTIFACT_CACHE", some "false"), ("LAKE_CACHE_DIR", some sourceCache),
      ("LAKE_RESTORE_ARTIFACTS", some "true")]

/-- Lake options for a dependency build; source mode also preserves the selected toolchain. -/
def lakeOptions : BuildMode → Array String
  | .upstreamCache => #[]
  | .source => #["--no-cache", "--keep-toolchain"]

/-- Version of the isolated-cache and import-scope policy, recorded before any source build. -/
def sourceArtifactPolicy : Nat := 2

/-- The Mathlib build plan of local provisioning and CI. `readOnly` says the workspace is
sealed afterwards as the shared directory, so the upstream route also builds every module's
exported native object there. CI's upstream route keeps a writable workspace and only fetches
the published artifacts; its later builds write the objects they link. -/
def mathlibCommands (readOnly : Bool) : BuildMode → List (Array String)
  | .upstreamCache => #["exe", "cache", "get"] ::
      if readOnly then [#["build", "Mathlib", "Mathlib:static.export"]] else []
  | .source => [#["build", "regulaMathlibSource"]]

/-- The upstream route always fetches the published artifacts first, and builds the exported
native objects exactly when its workspace is sealed read-only afterwards. -/
theorem upstream_plan (readOnly : Bool) :
    mathlibCommands readOnly .upstreamCache =
      if readOnly then [#["exe", "cache", "get"], #["build", "Mathlib", "Mathlib:static.export"]]
      else [#["exe", "cache", "get"]] := by
  cases readOnly <;> rfl

/-- Source provisioning schedules only the source build with package-cache downloads and
artifact-cache reuse disabled, a supplied isolated artifact location, and restoration requested.
The invoked Lake, package hooks, cache freshness and process environment remain trusted. -/
theorem source_plan (readOnly : Bool) (sourceCache : String) :
    mathlibCommands readOnly .source = [#["build", "regulaMathlibSource"]] ∧
    lakeOptions .source = #["--no-cache", "--keep-toolchain"] ∧
    buildEnvironment sourceCache .source =
      #[("LAKE_NO_CACHE", some "true"), ("MATHLIB_NO_CACHE_ON_UPDATE", some "1"),
        ("LAKE_ARTIFACT_CACHE", some "false"), ("LAKE_CACHE_DIR", some sourceCache),
        ("LAKE_RESTORE_ARTIFACTS", some "true")] := by
  exact ⟨rfl, rfl, rfl⟩

/-- A full-length lowercase hexadecimal Git object name, the form of Lake's pinned
revisions and of `Lean.githash`. -/
def isObjectName (text : String) : Bool :=
  text.length == 40 && text.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- One non-hidden path component without separators. -/
def isComponent (text : String) : Bool :=
  !text.isEmpty && !text.startsWith "." &&
    text.all fun c => c.isAlphanum || c == '-' || c == '_' || c == '.'

/-- A name admitted as a single path component; the type excludes separators and `..`. -/
abbrev Component := {text : String // isComponent text = true}

/-- Admit `text` as a path component, or refuse. -/
def component? (text : String) : Option Component :=
  if h : isComponent text then some ⟨text, h⟩ else none

/-- The shared directory's name for one Mathlib revision, compiler commit and artifact mode;
a source name also carries its artifact policy and the hash of its import module.
The upstream-cache spelling preserves existing shared directories. -/
def sharedKey (mode : BuildMode) (mathlibRev githash : String) (policy : Nat)
    (source : String) : String :=
  s!"{mathlibRev}-lean-{githash}" ++
    if mode == .source then s!"-source-v{policy}-{hash source}" else ""

/-- One package revision recorded by the shared directory or pinned by a copy. -/
structure Pin where
  /-- The package's name, which is also its checkout directory's name. -/
  name : String
  /-- The Git commit of the package. -/
  rev : String
  deriving DecidableEq, Repr, ToJson, FromJson

/-- The shared directory's receipt, written before it becomes visible. -/
structure Receipt where
  /-- The receipt format version; this program writes and accepts `receiptSchema`. -/
  schemaVersion : Nat
  /-- The Mathlib commit the shared directory holds. -/
  mathlibRev : String
  /-- The Git commit of the Lean toolchain that built the shared directory. -/
  leanGithash : String
  /-- The version string of that Lean toolchain. -/
  leanVersion : String
  /-- The artifact acquisition mode. Receipts predating this field used upstream caches. -/
  mode : BuildMode := .upstreamCache
  /-- Source artifacts require the current isolated-cache policy; legacy receipts had none. -/
  artifactPolicy : Nat := 0
  /-- Exact generated import module. Its hash only indexes the directory; admission compares bytes. -/
  source : String := ""
  /-- Each package checkout in the shared directory, at the commit it was materialized at. -/
  packages : Array Pin
  deriving Repr, ToJson, FromJson

/-- Receipt schema this program writes and accepts. -/
def receiptSchema : Nat := 1

/-- The directory name a receipt identifies, under the artifact policy it records. -/
def Receipt.key (receipt : Receipt) : String :=
  sharedKey receipt.mode receipt.mathlibRev receipt.leanGithash receipt.artifactPolicy
    receipt.source

/-- The complete source inputs of one staged dependency workspace. -/
structure StageInputs where
  /-- Artifact policy recorded before the stage's first build. -/
  artifactPolicy : Nat
  /-- Lake configuration selecting the pinned Mathlib source. -/
  configuration : String
  /-- Exact package manifest serialized by this program. -/
  manifest : String
  /-- The repository's complete toolchain selector file. -/
  toolchain : String
  /-- Generated Mathlib import module, empty for the full upstream-cache build. -/
  source : String
  deriving DecidableEq, Repr

/-- Only a source-mode stage with exactly the requested inputs may be resumed. The caller
also restricts discovery to real directories under the current compiler/mode key. -/
def resumes (mode : BuildMode) (expected observed : StageInputs) : Bool :=
  mode == .source && expected == observed

/-- Resumption binds every staged source input and is unavailable to the upstream-cache route. -/
theorem resumes_iff (mode : BuildMode) (expected observed : StageInputs) :
    resumes mode expected observed = true ↔ mode = .source ∧ expected = observed := by
  simp [resumes]

/-- The shared directory serves a copy only when its revision, compiler and artifact mode
match and it records no package the copy pins at a different revision. -/
def admits (receipt : Receipt) (mode : BuildMode) (mathlibRev githash : String)
    (pins : Array Pin) (source : String := "") : Bool :=
  receipt.schemaVersion == receiptSchema && receipt.mathlibRev == mathlibRev &&
  receipt.leanGithash == githash && receipt.mode == mode &&
    (mode != .source || receipt.artifactPolicy == sourceArtifactPolicy) &&
    receipt.source == source &&
    pins.all fun pin => receipt.packages.all fun held => held.name != pin.name ||
                                                          held.rev == pin.rev

/-- Admission binds revision, compiler, artifact mode and exact generated import source;
no admitted pin names a package that the receipt records at another revision. -/
theorem admits_sound (receipt : Receipt) (mode : BuildMode) (mathlibRev githash : String)
    (pins : Array Pin) (source : String)
    (h : admits receipt mode mathlibRev githash pins source = true) :
    receipt.mathlibRev = mathlibRev ∧ receipt.leanGithash = githash ∧
      receipt.mode = mode ∧
      (mode = .source → receipt.artifactPolicy = sourceArtifactPolicy) ∧
      receipt.source = source ∧
      ∀ pin ∈ pins, ∀ held ∈ receipt.packages, held.name = pin.name → held.rev = pin.rev := by
  simp only [admits, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨_, hRev⟩, hGithash⟩, hMode⟩, hPolicy⟩, hSource⟩, hPins⟩ := h
  refine ⟨hRev, hGithash, hMode, ?_, hSource, fun pin hPin held hHeld hName => ?_⟩
  · intro hSource
    exact hPolicy.resolve_left (fun different => different hSource)
  · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hPin
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hHeld
    exact ((hPins i hi) j hj).resolve_left (fun h => h hName)

/-- An admitted receipt identifies the directory requested under the current artifact policy.
A source receipt recorded under another policy is refused by `admits`; it identifies only its
own directory, for retention. -/
theorem admits_key (receipt : Receipt) (mode : BuildMode) (mathlibRev githash : String)
    (pins : Array Pin) (source : String)
    (h : admits receipt mode mathlibRev githash pins source = true) :
    receipt.key = sharedKey mode mathlibRev githash sourceArtifactPolicy source := by
  obtain ⟨hRev, hGithash, hMode, hPolicy, hSource, _⟩ :=
    admits_sound receipt mode mathlibRev githash pins source h
  unfold Receipt.key
  rw [hMode, hRev, hGithash, hSource]
  cases mode with
  | upstreamCache => simp [sharedKey]
  | source => rw [hPolicy rfl]

/-- An upstream-cache receipt can never admit a source-build request. -/
theorem source_refuses_cache (receipt : Receipt) (mathlibRev githash : String)
    (pins : Array Pin) (source : String) (h : receipt.mode = .upstreamCache) :
    admits receipt .source mathlibRev githash pins source = false := by
  simp [admits, h]

/-- What a copy has at one package path. -/
inductive Observed where
  /-- Nothing. -/
  | absent
  /-- A symbolic link; `target` is its resolved location (empty when it dangles). -/
  | link (target : String)
  /-- A real directory: its Git `HEAD` (`none` when it is not a Git checkout) and whether
  it is clean: `git status --porcelain`, `git stash list` and the commits of `HEAD` and local
  branches that no remote-tracking branch holds all report nothing. -/
  | directory (head : Option String) (clean : Bool)
  /-- Any other kind of file. -/
  | other
  deriving DecidableEq, Repr

/-- The action for one package path. -/
inductive Step where
  /-- Already what provisioning installs. -/
  | keep
  /-- Install at the absent path. -/
  | install
  /-- Remove the existing link or clean checkout, then install. -/
  | replace
  /-- Leave the path as it is, for the stated reason. -/
  | leave (reason : String)
  /-- Stop: acting would discard local changes or unknown content. -/
  | refuse (reason : String)
  deriving DecidableEq, Repr

/-- Mathlib's step: only a link to the shared checkout is kept. A real directory is
replaced when it is a clean Git checkout (its work is held by its remotes) and otherwise refused,
so provisioning completes only with Mathlib linked and discards no local change. -/
def mathlibStep (target : String) : Observed → Step
  | .absent => .install
  | .link resolved => if resolved == target then .keep else .replace
  | .directory (some _) true => .replace
  | .directory _ _ => .refuse "it is not a clean Git checkout; move your changes elsewhere, \
      remove it, and provision again"
  | .other => .refuse "it is not a directory or a link; remove it and provision again"

/-- A clone's step: a clean checkout at the pinned revision is kept; links and clean
checkouts at other revisions are replaced; local changes are left for Lake. -/
def cloneStep (rev : String) : Observed → Step
  | .absent => .install
  | .link _ => .replace
  | .directory (some head) true => if head == rev then .keep else .replace
  | .directory (some _) false => .leave "it has local changes"
  | .directory none _ => .leave "it is not a Git checkout"
  | .other => .refuse "it is not a directory or a link; remove it and provision again"

/-- Mathlib is kept exactly when the copy already links the shared checkout. -/
theorem mathlibStep_keep_iff (target : String) (observed : Observed) :
    mathlibStep target observed = .keep ↔ observed = .link target := by
  cases observed with
  | absent => simp [mathlibStep]
  | link resolved => by_cases h : resolved = target <;> simp [mathlibStep, h]
  | directory head clean => cases head <;> cases clean <;> simp [mathlibStep]
  | other => simp [mathlibStep]

/-- Every step on a real Mathlib directory replaces it or refuses. -/
theorem mathlibStep_directory (target : String) (head : Option String) (clean : Bool) :
    mathlibStep target (.directory head clean) = .replace ∨
      ∃ reason, mathlibStep target (.directory head clean) = .refuse reason := by
  cases head <;> cases clean <;> simp [mathlibStep]

/-- Removal is confined to links and clean Git checkouts. -/
theorem mathlibStep_replace (target : String) (observed : Observed)
    (h : mathlibStep target observed = .replace) :
    (∃ resolved, observed = .link resolved) ∨ ∃ head, observed = .directory (some head) true := by
  cases observed with
  | absent => simp [mathlibStep] at h
  | link resolved => exact .inl ⟨resolved, rfl⟩
  | directory head clean =>
    cases head <;> cases clean <;> simp_all [mathlibStep]
  | other => simp [mathlibStep] at h

/-- Removal is confined to links and clean Git checkouts. -/
theorem cloneStep_replace (rev : String) (observed : Observed)
    (h : cloneStep rev observed = .replace) :
    (∃ resolved, observed = .link resolved) ∨ ∃ head, observed = .directory (some head) true := by
  cases observed with
  | absent => simp [cloneStep] at h
  | link resolved => exact .inl ⟨resolved, rfl⟩
  | directory head clean =>
    cases head <;> cases clean <;> simp_all [cloneStep]
  | other => simp [cloneStep] at h

/-! ### Retention

Each shared directory has a registry beside it of the copies provisioned to link it. Under the
one provisioning lock, a copy registers before it links, and a run removes a shared directory
only when it is not the run's own and no registered copy still links it. A removal first
renames the directory out of use, so a later run finishes one that was interrupted. Only a
directory whose receipt identifies it is ever removed. -/

/-- The name of the shared directory `key` while it is being removed, before a unique suffix. -/
def removingPrefix (key : String) : String := s!"{key}.removing-"

/-- A directory under the shared parent, as its receipt identifies it. -/
inductive Found where
  /-- A shared directory: its name is its receipt's key. -/
  | shared
  /-- A shared directory being removed: its name extends its receipt's removing prefix. -/
  | removing
  /-- Anything else; it is never touched. -/
  | foreign
  deriving DecidableEq, Repr

/-- Identify a directory by its name and its receipt. -/
def found (name : String) : Option Receipt → Found
  | none => .foreign
  | some receipt =>
    if name == receipt.key then .shared
    else if name.startsWith (removingPrefix receipt.key) then .removing
    else .foreign

/-- Only a receipt that names the directory, under the artifact policy that receipt records,
identifies it as shared or being removed. -/
theorem found_identified (name : String) (receipt : Option Receipt)
    (h : found name receipt ≠ .foreign) :
    ∃ r, receipt = some r ∧ (name = r.key ∨
      name.startsWith (removingPrefix r.key) = true) := by
  cases receipt with
  | none => simp [found] at h
  | some r =>
    refine ⟨r, rfl, ?_⟩
    by_cases hName : name = r.key
    · exact .inl hName
    · by_cases hPrefix : name.startsWith (removingPrefix r.key)
      · exact .inr hPrefix
      · simp [found, hName, hPrefix] at h

/-- Record `copy` in a registry once. -/
def register (copy : String) (registry : Array String) : Array String :=
  if registry.contains copy then registry else registry.push copy

/-- Registering records the copy and drops no registration. -/
theorem register_mem (copy : String) (registry : Array String) :
    copy ∈ register copy registry ∧ ∀ other ∈ registry, other ∈ register copy registry := by
  unfold register
  split <;> simp_all

/-- The registered copies, each paired with whether it still links the directory, that still
link it. -/
def stillLinked (copies : Array (String × Bool)) : Array String :=
  copies.filterMap fun copy => if copy.2 then some copy.1 else none

/-- A registration is kept exactly when its copy still links the directory. -/
theorem mem_stillLinked (copies : Array (String × Bool)) (copy : String) :
    copy ∈ stillLinked copies ↔ (copy, true) ∈ copies := by
  simp [stillLinked, Array.mem_filterMap]

/-- A shared directory is removed when it is not the current one and none of its registered
copies, each paired with whether it still links the directory, still links it. -/
def prunes (current name : String) (copies : Array (String × Bool)) : Bool :=
  name != current && copies.all fun copy => !copy.2

/-- Removal spares the current directory and every directory a registered copy links. -/
theorem prunes_sound (current name : String) (copies : Array (String × Bool))
    (h : prunes current name copies = true) :
    name ≠ current ∧ ∀ copy ∈ copies, copy.2 = false := by
  simp only [prunes, Bool.and_eq_true, bne_iff_ne, ne_eq, Array.all_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true] at h
  refine ⟨h.1, fun copy hCopy => ?_⟩
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hCopy
  exact h.2 i hi

/-! ## Process and filesystem effects -/

/-- Captured result of one argv invocation; there is no shell. -/
structure Ran where
  /-- The process's exit code. -/
  exitCode : UInt32
  /-- The process's standard output. -/
  stdout : String
  /-- The process's standard error. -/
  stderr : String

private def run (cwd : FilePath) (cmd : String) (args : Array String) : IO Ran := do
  let out ← IO.Process.output { cmd, args, cwd := some cwd, stdin := .null }
  return ⟨out.exitCode, out.stdout, out.stderr⟩

private def require (cwd : FilePath) (cmd : String) (args : Array String) : IO String := do
  let ran ← run cwd cmd args
  unless ran.exitCode == 0 do
    throw <| IO.userError s!"provisioning: `{cmd} {" ".intercalate args.toList}` in {cwd} \
      failed ({ran.exitCode}): {ran.stderr.trimAscii}"
  return ran.stdout

/-- Run with inherited output, for long steps whose progress the user should see. -/
private def stream (cwd : FilePath) (cmd : String) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO Unit := do
  let child ← IO.Process.spawn {
    cmd, args, env, cwd := some cwd, stdin := .null, stdout := .inherit, stderr := .inherit }
  let exit ← child.wait
  unless exit == 0 do
    throw <|
        IO.userError
            s!"provisioning: `{cmd} {" ".intercalate args.toList}` in {cwd} failed ({exit})"

private def say (line : String) : IO Unit := IO.println s!"provisioning: {line}"

private def nonce : IO String := do
  let bytes ← IO.getRandomBytes 8
  return s!"{← IO.Process.getPID}-{bytes.foldl (fun value byte => value * 256 + byte.toNat) 0}"

/-- Source commands get a newly created cache directory, so an explicit package cache opt-in
cannot read an inherited remote mapping. Retain it: such a package may store outputs there
despite the environment's requested defaults. Creation and package hooks remain trusted. -/
private def freshBuildEnvironment (root : FilePath) (mode : BuildMode) :
    IO (Array (String × Option String)) := do
  match mode with
  | .upstreamCache => return buildEnvironment "" mode
  | .source =>
    let parent := root / ".lake" / "regula-source-caches"
    IO.FS.createDirAll parent
    let cache := parent / (← nonce)
    IO.FS.createDir cache
    return buildEnvironment (← IO.FS.realPath cache).toString mode

/-- Read the repository's explicit artifact mode. A missing or malformed
`dependency-build-mode` is refused. -/
def readBuildMode (repo : FilePath) : IO BuildMode := do
  let text := (← IO.FS.readFile (repo / "dependency-build-mode")).trimAscii.toString
  let some mode := buildMode? text
    | throw <| IO.userError s!"provisioning: unknown dependency-build-mode '{text}'"
  return mode

/-- Execute the Mathlib plan. `workspaceArgs` selects the Lake workspace, while the process
directory stays at its package-cache root as required by Mathlib's cache tool. -/
private def buildMathlib (cwd : FilePath) (mode : BuildMode) (readOnly : Bool)
    (workspaceArgs : Array String := #[]) : IO Unit := do
  let env ← freshBuildEnvironment cwd mode
  for command in mathlibCommands readOnly mode do
    stream cwd "lake" (lakeOptions mode ++ workspaceArgs ++ command) env

private def admitComponent (what text : String) : IO Component := do
  let some name := component? text
    | throw <| IO.userError s!"provisioning: {what} '{text}' is not a single path component"
  return name

/-- Kind of the path itself, without following a final symbolic link. -/
private def kind? (path : FilePath) : IO (Option IO.FS.FileType) := do
  try return some (← path.symlinkMetadata).type catch _ => return none

/-- Build the planner in a separate workspace with the repository's exact configuration and
linked sources, so the root package's Lake configuration and build caches stay untouched; the
planner's own Lake loads of the Audit and standard packages may write their configuration
caches. The workspace's key includes the repository's canonical path, which its absolute source
links name, so a moved repository gets a new workspace and the old one is left in place.
A workspace is written whole in a sibling staging directory and published as `v2-<key>` by one
rename, so this program leaves no partly written workspace at that path; the rename is a trusted
filesystem effect, and this is no claim of durability across power loss. An interrupted attempt,
and one that another process outran, stays in its staging directory, unused and never removed.
A `<key>` directory of the earlier in-place construction, which may be partial, is likewise
neither used nor removed.
Generated configuration is never overwritten: an existing workspace must retain the same bytes
and source links. -/
private def sourceModule (repo : FilePath) (mode : BuildMode) : IO String := do
  if mode == .upstreamCache then return ""
  let inputs ← #["lakefile.lean", "lake-manifest.json", "lean-toolchain"].mapM fun (name : String) => do
    return (name, ← IO.FS.readFile (repo / name))
  let parent := repo / ".lake/regula-dependency-planner"
  IO.FS.createDirAll parent
  let key := hash (inputs.toList, Lean.githash, (← IO.FS.realPath repo).toString)
  let workspace := parent / s!"v2-{key}"
  match ← kind? workspace with
  | none =>
    let staged := parent / s!"v2-{key}.staging-{← nonce}"
    IO.FS.createDir staged
    for (name, source) in inputs do IO.FS.writeFile (staged / name) source
    for name in #["lean", "examples"] do
      let _ ← require repo "ln" #["-s", (repo / name).toString, (staged / name).toString]
    try IO.FS.rename staged workspace
    catch error => unless (← kind? workspace) == some .dir do throw error
  | some .dir => pure ()
  | some _ => throw <| IO.userError s!"provisioning: planner workspace is not a directory: {workspace}"
  for (name, source) in inputs do
    unless (← kind? (workspace / name)) == some .file &&
        (← IO.FS.readFile (workspace / name)) == source do
      throw <| IO.userError s!"provisioning: planner configuration differs: {workspace / name}"
  for name in #["lean", "examples"] do
    unless (← kind? (workspace / name)) == some .symlink &&
        (← IO.FS.realPath (workspace / name)) == (← IO.FS.realPath (repo / name)) do
      throw <| IO.userError s!"provisioning: planner source link differs: {workspace / name}"
  stream workspace "lake" #["--no-cache", "--keep-toolchain", "build", "dependencyScope"]
    (← freshBuildEnvironment workspace mode)
  let result ← require repo (workspace / ".lake/build/bin/dependencyScope").toString #[]
  IO.ofExcept <| Json.parse result >>= fromJson?

private def observe (path : FilePath) : IO Observed := do
  match ← kind? path with
  | none => return .absent
  | some .symlink =>
    try return .link (← IO.FS.realPath path).toString catch _ => return .link ""
  | some .dir =>
    -- Without its own `.git`, Git would answer for the enclosing repository instead.
    unless ← (path / ".git").pathExists do return .directory none false
    let head ← run path "git" #["rev-parse", "HEAD"]
    let reports ← [#["status", "--porcelain"], #["stash", "list"],
      #["rev-list", "-n", "1", "HEAD", "--branches", "--not", "--remotes"]].mapM (run path "git")
    let head := if head.exitCode == 0 then some head.stdout.trimAscii.toString else none
    return .directory head
        (reports.all fun ran => ran.exitCode == 0 && ran.stdout.trimAscii.isEmpty)
  | some _ => return .other

/-- Remove what `observe` classified, never following a link into its target. -/
private def removeObserved (path : FilePath) : Observed → IO Unit
  | .link _ => IO.FS.removeFile path
  | .directory .. => IO.FS.removeDirAll path
  | _ => pure ()

/-- Replace `path` by a symbolic link to `target`: the link is made beside it and renamed
over it, so readers see the old entry or the new link. -/
private def installLink (path : FilePath) (target : String) : IO Unit := do
  let some parent := path.parent | throw <| IO.userError s!"provisioning: {path} has no parent"
  IO.FS.createDirAll parent
  let staged := parent / s!".{path.fileName.getD "link"}.{← nonce}"
  let _ ← require parent "ln" #["-s", target, staged.toString]
  try IO.FS.rename staged path
  catch error =>
    if (← kind? staged) matches some _ then IO.FS.removeFile staged
    throw error

/-- Install a writable copy-on-write clone of `source` at the absent `path`. `cp -c` asks for
APFS clones; elsewhere the plain recursive copy is the fallback. -/
private def installClone (path source : FilePath) : IO Unit := do
  let some parent := path.parent | throw <| IO.userError s!"provisioning: {path} has no parent"
  let staged := parent / s!".{path.fileName.getD "clone"}.{← nonce}"
  let cloned ← run parent "cp" #["-R", "-c", "-p", source.toString, staged.toString]
  unless cloned.exitCode == 0 do
    if (← kind? staged) matches some .dir then IO.FS.removeDirAll staged
    let _ ← require parent "cp" #["-R", "-p", source.toString, staged.toString]
  let _ ← require parent "chmod" #["-R", "u+w", staged.toString]
  -- The clone's files are new inodes; refresh the index so Lake's `git diff` stays cheap.
  let _ ← run staged "git" #["update-index", "-q", "--refresh"]
  try IO.FS.rename staged path
  catch error =>
    IO.FS.removeDirAll staged
    throw error

/-! ## The shared directory -/

/-- The directory, relative to the repository root, of the package whose Lake manifest pins
Mathlib: the Mathlib-dependent package, which requires the root `regula` package by relative
path and names the root `.lake/packages` as its packages directory. -/
def mathlibPackage : FilePath := "audit"

/-- What the Mathlib package pins: the Git entries of its Lake manifest, each with the entry
object exactly as the manifest records it. -/
structure Pins where
  /-- The manifest's `packagesDir`, relative to the Mathlib package; `.lake/packages` when it
  gives none. -/
  packagesDir : FilePath
  /-- The Git URL of the pinned Mathlib. -/
  mathlibUrl : String
  /-- The pinned Mathlib commit. -/
  mathlibRev : String
  /-- Every Git entry of the manifest, with its decoded name and commit. -/
  git : Array (Json × Pin)

/-- Decode one manifest entry that Lake materializes from Git (`type` `git`); Lake names its
checkout `<packagesDir>/<name>`. Other entry types are not shared. -/
private def gitPin (entry : Json) : Except String (Option (Json × Pin × String)) := do
  unless (← entry.getObjValAs? String "type") == "git" do return none
  let name ← entry.getObjValAs? String "name"
  let rev ← entry.getObjValAs? String "rev"
  let url ← entry.getObjValAs? String "url"
  if (entry.getObjValD "subDir") != .null then
    throw s!"{name}: a Git package in a subdirectory is not supported"
  return some (entry, ⟨name, rev⟩, url)

/-- Read the Mathlib package's pins with Lake's lock-file format (version `1.x`, as the pinned
Lake writes); another major version fails closed rather than being guessed. Its `path` entries,
such as the root `regula` package, are not shared. -/
private def readPins (repo : FilePath) : IO (Option (Json × Pins)) := do
  let manifest ← IO.ofExcept
      (Json.parse (← IO.FS.readFile (repo / mathlibPackage / "lake-manifest.json")))
  let version ← IO.ofExcept (manifest.getObjValAs? String "version")
  unless version.startsWith "1." do
    throw <| IO.userError s!"provisioning: lake-manifest.json version {version} is not supported"
  let entries ← IO.ofExcept (manifest.getObjValAs? (Array Json) "packages")
  let decoded ← IO.ofExcept (entries.filterMapM gitPin)
  let some (_, mathlibPin, url) := decoded.find? (·.2.1.name == "mathlib") | return none
  unless isObjectName mathlibPin.rev do
    throw <|
        IO.userError
            s!"provisioning: the pinned Mathlib revision '{mathlibPin.rev}' is not a commit"
  unless url.all (fun c => c != '"' && c != '\\' && c != '\n') do
    throw <| IO.userError s!"provisioning: the pinned Mathlib URL '{url}' is not a plain URL"
  for (_, pin, _) in decoded do
    let _ ← admitComponent "package directory" pin.name
  let packagesDir := (manifest.getObjValAs? String "packagesDir").toOption.getD ".lake/packages"
  return some (manifest, {
    packagesDir, mathlibUrl := url, mathlibRev := mathlibPin.rev,
    git := decoded.map fun (entry, pin, _) => (entry, pin) })

private def cacheBase : IO FilePath := do
  if let some base ← IO.getEnv "XDG_CACHE_HOME" then
    if !base.isEmpty then return base
  let some home ← IO.getEnv "HOME"
    | throw <| IO.userError "provisioning: HOME is not set"
  return FilePath.mk home / ".cache"

/-- Receipt file name at the top of the shared directory. -/
def receiptName : String := "regula-provisioned.json"

private def readReceipt (dir : FilePath) : IO (Option Receipt) := do
  try
    let text ← IO.FS.readFile (dir / receiptName)
    let .ok json := Json.parse text | return none
    let .ok fields := json.getObj? | return none
    -- Before artifact modes existed every receipt described the upstream-cache route.
    let json := if fields.contains "mode" then json else
      json.setObjVal! "mode" (toJson BuildMode.upstreamCache)
    let json := if fields.contains "artifactPolicy" then json else
      json.setObjVal! "artifactPolicy" (toJson (0 : Nat))
    let json := if fields.contains "source" then json else
      json.setObjVal! "source" (toJson ("" : String))
    let .ok receipt := fromJson? json | return none
    return some receipt
  catch _ => return none

/-- The shared workspace's package directory inside the shared directory. -/
def sharedPackages (dir : FilePath) : FilePath := dir / ".lake" / "packages"

/-- Remove the directory `path`, which may be read-only, never following a link inside it. -/
private def removeReadOnly (path : FilePath) : IO Unit := do
  let _ ← require (path.parent.getD ".") "chmod" #["-R", "u+w", path.toString]
  IO.FS.removeDirAll path

/-- Remove a shared directory being removed, its receipt last, so that a run killed partway
leaves it still identified and the next run finishes the removal. -/
private def removeShared (path : FilePath) : IO Unit := do
  let _ ← require (path.parent.getD ".") "chmod" #["-R", "u+w", path.toString]
  for entry in ← path.readDir do
    unless entry.fileName == receiptName do
      if (← kind? entry.path) == some .dir then IO.FS.removeDirAll entry.path
      else IO.FS.removeFile entry.path
  if (← kind? (path / receiptName)).isSome then IO.FS.removeFile (path / receiptName)
  IO.FS.removeDir path

/-- Make the staged directory read-only. Each checkout's index is refreshed after its files
changed mode, before its `.git` becomes read-only, so Lake's `git diff` stays cheap. -/
private def makeReadOnly (staging : FilePath) (packages : Array FilePath) : IO Unit := do
  let _ ← require staging "chmod" #["-R", "a-w", staging.toString]
  for package in packages do
    let git := package / ".git"
    let _ ← require package "chmod" #["u+w", git.toString]
    let _ ← require package "git" #["update-index", "-q", "--refresh"]
    let _ ← require package "chmod" #["a-w", (git / "index").toString, git.toString]

/-- The complete dependency workspace input written before a build begins. -/
private def stageInputs (repo : FilePath) (manifest : Json) (pins : Pins)
    (mode : BuildMode) (source : String) : IO StageInputs := do
  return {
    artifactPolicy := if mode == .source then sourceArtifactPolicy else 0
    configuration :=
      "name = \"regula_mathlib_packages\"\n\n[[require]]\nname = \"mathlib\"\n" ++
        s!"git = \"{pins.mathlibUrl}\"\nrev = \"{pins.mathlibRev}\"\n" ++
        (if mode == .source then
          "\n[[lean_exe]]\nname = \"regulaMathlibSource\"\nroot = \"RegulaMathlibSource\"\n\
            supportInterpreter = true\n" else "")
    manifest := (manifest
      |>.setObjVal! "name" (.str "regula_mathlib_packages")
      |>.setObjVal! "packagesDir" (.str ".lake/packages")
      |>.setObjVal! "packages" (.arr (pins.git.map (·.1)))).pretty ++ "\n"
    toolchain := ← IO.FS.readFile (repo / "lean-toolchain")
    source }

/-- Recover exact inputs from an interrupted stage. Unknown or incomplete stages are left
untouched. Filesystem content and Lake's dependency traces remain trusted observations. -/
private def readStageInputs (path : FilePath) : IO (Option StageInputs) := do
  try
    return some {
      artifactPolicy := ← IO.ofExcept <| fromJson? (← IO.ofExcept <|
        Json.parse (← IO.FS.readFile (path / "regula-artifact-policy.json")))
      configuration := ← IO.FS.readFile (path / "lakefile.toml")
      manifest := ← IO.FS.readFile (path / "lake-manifest.json")
      toolchain := ← IO.FS.readFile (path / "lean-toolchain")
      source := ← IO.FS.readFile (path / "RegulaMathlibSource.lean") }
  catch _ => return none

/-- Refuse a retained package tree that Lake could replace or clean. The pinned HEAD itself
is admitted even when a shallow fetch recorded only FETCH_HEAD; other local branch work,
stashes and working-tree edits remain protected. No package mutation precedes this check. -/
private def requireRetainedPackages (staging : FilePath) (pins : Pins) : IO Unit := do
  for path in #[staging / ".lake", sharedPackages staging] do
    if let some kind ← kind? path then
      unless kind == .dir do
        throw <| IO.userError s!"provisioning: refusing retained non-directory {path}"
  let packages := sharedPackages staging
  unless ← packages.pathExists do return
  for entry in ← packages.readDir do
    let some (json, pin) := pins.git.find? (·.2.name == entry.fileName)
      | throw <| IO.userError s!"provisioning: retained stage has unpinned package {entry.path}"
    unless (← kind? entry.path) == some .dir &&
        (← kind? (entry.path / ".git")) == some .dir do
      throw <| IO.userError s!"provisioning: retained package {entry.path} is not an owned checkout"
    let head ← require entry.path "git" #["rev-parse", "HEAD"]
    unless head.trimAscii.toString == pin.rev do
      throw <| IO.userError s!"provisioning: retained package {entry.path} has another revision"
    let url ← IO.ofExcept (json.getObjValAs? String "url")
    unless (← require entry.path "git" #["remote", "get-url", "origin"]).trimAscii == url do
      throw <| IO.userError s!"provisioning: retained package {entry.path} has another origin"
    for args in #[#["status", "--porcelain", "--untracked-files=all"], #["stash", "list"],
        #["rev-list", "-n", "1", "--branches", "--not", "HEAD", "--remotes"]] do
      unless (← require entry.path "git" args).trimAscii.isEmpty do
        throw <| IO.userError s!"provisioning: retained package {entry.path} has local work"

/-- Source mode reuses only a stage for this exact compiler/mode key with identical inputs whose
retained packages pass `requireRetainedPackages`. A stage with identical inputs that fails those
checks, such as one an interrupted clone left without a checked-out revision, is reported and left
untouched, and the search continues; with no admissible stage a new one is created. The exclusive
provisioning lock excludes a concurrent writer owned by this program. -/
private def prepareStage (parent : FilePath) (key : String) (mode : BuildMode) (pins : Pins)
    (expected : StageInputs) : IO FilePath := do
  if mode == .source then
    for entry in ← parent.readDir do
      if entry.fileName.startsWith s!"{key}.staging-" && (← kind? entry.path) == some .dir then
        if let some observed ← readStageInputs entry.path then
          if resumes mode expected observed then
            match ← (requireRetainedPackages entry.path pins).toBaseIO with
            | .error error =>
              say s!"leaving retained source stage {entry.path} untouched: {error}"
            | .ok () =>
              say s!"resuming source dependencies in {entry.path}"
              let _ ← require entry.path "chmod" #["-R", "u+w", entry.path.toString]
              return entry.path
  let staging := parent / s!"{key}.staging-{← nonce}"
  IO.FS.createDir staging
  IO.FS.writeFile (staging / "lakefile.toml") expected.configuration
  IO.FS.writeFile (staging / "lake-manifest.json") expected.manifest
  IO.FS.writeFile (staging / "lean-toolchain") expected.toolchain
  IO.FS.writeFile (staging / "RegulaMathlibSource.lean") expected.source
  IO.FS.writeFile (staging / "regula-artifact-policy.json")
    ((toJson expected.artifactPolicy).compress ++ "\n")
  return staging

/-- Create the shared directory `final` from a fresh or exact-input resumed staging directory,
run the complete selected build plan, record and seal it, and publish with one rename.
The caller holds the lock. -/
private def create (repo parent final : FilePath) (key : String) (manifest : Json)
    (pins : Pins) (mode : BuildMode) (source : String) : IO Unit := do
  let staging ← prepareStage parent key mode pins (← stageInputs repo manifest pins mode source)
  try
    let githash := (← require staging "lean" #["--githash"]).trimAscii.toString
    unless githash == Lean.githash do
      throw <|
          IO.userError
              s!"provisioning: the staged toolchain is {githash}, not the running {Lean.githash}"
    -- `cache get` unpacks into the workspace's default `.lake/packages` and ignores a custom
    -- packages directory, so the staging workspace keeps the default.
    -- An interpreter-supporting executable requests exported native objects for its complete
    -- transitive imports. The upstream route retains its complete-library build.
    buildMathlib staging mode true
    let packagesRoot := sharedPackages staging
    let mut held := #[]
    let mut dirs := #[]
    for entry in ← packagesRoot.readDir do
      let head := (← require entry.path "git" #["rev-parse", "HEAD"]).trimAscii.toString
      if let some (_, pin) := pins.git.find? (·.2.name == entry.fileName) then
        unless pin.rev == head do
          throw <|
              IO.userError
                  s!"provisioning: {entry.fileName} materialized at {head}, not the \
                    pinned {pin.rev}"
      held := held.push ⟨entry.fileName, head⟩
      dirs := dirs.push entry.path
    let receipt : Receipt := {
      schemaVersion := receiptSchema, mathlibRev := pins.mathlibRev,
      leanGithash := Lean.githash, leanVersion := Lean.versionString, mode,
      artifactPolicy := if mode == .source then sourceArtifactPolicy else 0, source, packages := held }
    IO.FS.writeFile (staging / receiptName) ((toJson receipt).pretty ++ "\n")
    makeReadOnly staging dirs
    IO.FS.rename staging final
  catch error =>
    if mode == .source then
      say s!"retained interrupted source dependencies in {staging}"
    else if (← kind? staging) matches some .dir then removeReadOnly staging
    throw error

/-- The admitted shared directory `parent/key` for these pins, created once. The caller holds
the lock. -/
private def ensureShared (repo parent : FilePath) (key : Component) (manifest : Json)
    (pins : Pins) (mode : BuildMode) (source : String) : IO (FilePath × Receipt) := do
  let pinned := pins.git.map (·.2)
  let final := parent / key.val
  let admitted? := fun (receipt? : Option Receipt) => receipt?.filter fun receipt =>
    admits receipt mode pins.mathlibRev Lean.githash pinned source
  if let some receipt := admitted? (← readReceipt final) then return (final, receipt)
  if (← kind? final) matches some _ then
    throw <| IO.userError s!"provisioning: {final} exists but its receipt does not admit \
      Mathlib {pins.mathlibRev} for Lean {Lean.githash} ({mode.spelling}); move it aside and \
      provision again"
  -- Source stages retain compilation work and are resumed only after exact-input admission.
  if mode == .upstreamCache then
    for entry in ← parent.readDir do
      if entry.fileName.startsWith s!"{key.val}.staging-" then
        if (← kind? entry.path) matches some .dir then removeReadOnly entry.path
  say s!"creating the shared Mathlib {pins.mathlibRev} for Lean {Lean.versionString} \
    ({mode.spelling}) in {final}"
  let started ← IO.monoMsNow
  create repo parent final key.val manifest pins mode source
  say s!"created {final} in {((← IO.monoMsNow) - started) / 1000} s"
  let some receipt := admitted? (← readReceipt final)
    | throw <| IO.userError s!"provisioning: {final} was created but its receipt is not admitted"
  return (final, receipt)

/-- The lock under the shared parent that orders every creation, registration, link and
removal there; it is never removed. -/
def lockName : String := "regula-provision.lock"

/-- The registry of the shared directory `name`, beside it because the directory is
read-only. -/
private def registryPath (parent : FilePath) (name : String) : FilePath :=
  parent / s!"{name}.copies.json"

/-- A registry's copies: none registered when it is absent, `none` when it is unreadable. -/
private def readRegistry (path : FilePath) : IO (Option (Array String)) := do
  unless ← path.pathExists do return some #[]
  try
    let .ok json := Json.parse (← IO.FS.readFile path) | return none
    return (fromJson? json : Except String (Array String)).toOption
  catch _ => return none

/-- Replace a registry with one rename, so a reader sees the old or the new one. -/
private def writeRegistry (path : FilePath) (copies : Array String) : IO Unit := do
  let staged := path.withFileName s!".{path.fileName.getD "registry"}.{← nonce}"
  IO.FS.writeFile staged ((toJson copies).pretty ++ "\n")
  IO.FS.rename staged path

/-- Record `copy`, the path of a copy's Mathlib link, in the registry of the shared directory
`name`, before the copy links it. -/
private def registerCopy (parent : FilePath) (name copy : String) : IO Unit := do
  let path := registryPath parent name
  let some registry ← readRegistry path
    | throw <| IO.userError s!"provisioning: the registry {path} is unreadable; repair or remove it"
  writeRegistry path (register copy registry)

/-- Whether `copy` is a symbolic link that resolves to `target`. -/
private def links (copy target : String) : IO Bool := do
  unless (← kind? copy) == some .symlink do return false
  try return (← IO.FS.realPath copy).toString == target catch _ => return false

/-- Remove every shared directory under `parent`, other than `current`, that no registered
copy still links, and finish every removal an interrupted run began; drop from each kept
registry the copies that no longer link its directory. Only directories that their receipt
identifies are touched, and a failure is reported, not fatal. The caller holds the lock. -/
private def prune (parent : FilePath) (current : String) : IO Unit := do
  for entry in ← parent.readDir do
    try
      if (← kind? entry.path) == some .dir then
        match found entry.fileName (← readReceipt entry.path) with
        | .foreign => pure ()
        | .removing => removeShared entry.path
        | .shared =>
          let registry := registryPath parent entry.fileName
          let some copies ← readRegistry registry
            | say s!"left {entry.path} as it is: its registry {registry} is unreadable"
          let target ← try
              pure (some (← IO.FS.realPath (sharedPackages entry.path / "mathlib")).toString)
            catch _ => pure none
          let observed ← copies.mapM fun copy => do
            return (copy, ← match target with
              | some target => links copy target
              | none => pure false)
          if prunes current entry.fileName observed then
            if ← registry.pathExists then IO.FS.removeFile registry
            let removing := parent / s!"{removingPrefix entry.fileName}{← nonce}"
            IO.FS.rename entry.path removing
            removeShared removing
            say s!"removed {entry.path}: no registered copy links it"
          else
            let kept := stillLinked observed
            unless kept == copies do writeRegistry registry kept
    catch error =>
      IO.eprintln s!"provisioning: could not prune {entry.path}: {error}"

/-! ## One copy -/

/-- The packages directory the Mathlib package's manifest names, created when absent and
resolved to its canonical path, which must lie inside the repository. A linked packages
directory belongs to another checkout; it is refused, never provisioned through. -/
private def packagesPath (repo : FilePath) (pins : Pins) : IO FilePath := do
  let packages := repo / mathlibPackage / pins.packagesDir
  if (← kind? packages) matches some .symlink then
    throw <| IO.userError s!"provisioning: {packages} is a link; provision the checkout it names"
  IO.FS.createDirAll packages
  let resolved ← IO.FS.realPath packages
  unless (repo.toString ++ "/").isPrefixOf resolved.toString do
    throw <| IO.userError s!"provisioning: the packages directory {resolved} of {mathlibPackage} \
      is outside the repository {repo}"
  return resolved

/-- Link or clone every pinned package of the shared closure into the packages directory. -/
private def provisionPackages (packages shared : FilePath) (receipt : Receipt) (pins : Pins) :
    IO Unit := do
  let source := sharedPackages shared
  let target := (← IO.FS.realPath (source / "mathlib")).toString
  let mathlibPath := packages / "mathlib"
  let observed ← observe mathlibPath
  match mathlibStep target observed with
  | .keep => pure ()
  | .install => installLink mathlibPath target; say s!"linked {mathlibPath} to {target}"
  | .replace =>
    removeObserved mathlibPath observed
    installLink mathlibPath target
    let what := if observed matches .link _ then "the stale link" else "the per-copy checkout"
    say s!"replaced {what} {mathlibPath} with a link to {target}"
  | .leave reason | .refuse reason =>
    throw <| IO.userError s!"provisioning: refusing to replace {mathlibPath}: {reason}"
  let mut cloned := #[]
  for (_, pin) in pins.git do
    if pin.name == "mathlib" || !receipt.packages.contains pin then continue
    let path := packages / pin.name
    let observed ← observe path
    match cloneStep pin.rev observed with
    | .keep => pure ()
    | .install => installClone path (source / pin.name); cloned := cloned.push pin.name
    | .replace =>
      removeObserved path observed
      installClone path (source / pin.name)
      cloned := cloned.push pin.name
    | .leave reason => say s!"left {path} as it is: {reason}"
    | .refuse reason => throw <| IO.userError s!"provisioning: refusing to replace {path}: {reason}"
  unless cloned.isEmpty do
    say s!"cloned {", ".intercalate cloned.toList} (writable copy-on-write clones)"

/-- Refuse a process or Mathlib workspace using a different compiler from this program. -/
def requireCompiler (repo : FilePath) : IO Unit := do
  let githash := (← require repo "lean" #["--githash"]).trimAscii.toString
  unless githash == Lean.githash do
    throw <| IO.userError s!"provisioning: this repository's toolchain is {githash}, \
      but this program runs on {Lean.githash}"
  -- The shared directory is built with the root toolchain, so the Mathlib package must pin it.
  unless (← IO.FS.readFile (repo / "lean-toolchain")) ==
      (← IO.FS.readFile (repo / mathlibPackage / "lean-toolchain")) do
    throw <| IO.userError s!"provisioning: {mathlibPackage}/lean-toolchain differs from the \
      repository's lean-toolchain"

/-- Provision this copy. -/
def provision (repo : FilePath) : IO Unit := do
  let mode ← readBuildMode repo
  requireCompiler repo
  let some (manifest, pins) ← readPins repo
    | say s!"{mathlibPackage}/lake-manifest.json pins no Mathlib; nothing to share"
  let source ← sourceModule repo mode
  let key ← admitComponent "shared directory"
    (sharedKey mode pins.mathlibRev Lean.githash sourceArtifactPolicy source)
  let packages ← packagesPath repo pins
  let parent := (← cacheBase) / "mathlib-packages"
  IO.FS.createDirAll parent
  let lock ← IO.FS.Handle.mk (parent / lockName) .append
  unless ← lock.tryLock do
    say s!"waiting for another copy that is provisioning from {parent}"
    lock.lock
  let shared ← try
      let (shared, receipt) ← ensureShared repo parent key manifest pins mode source
      registerCopy parent key.val (packages / "mathlib").toString
      provisionPackages packages shared receipt pins
      prune parent key.val
      pure shared
    finally
      lock.unlock
  say s!"Mathlib {pins.mathlibRev} is shared read-only from {shared}"

/-- Provision the website's pinned Verso with the same artifact mode as Mathlib. -/
def provisionVerso (repo : FilePath) : IO Unit := do
  requireCompiler repo
  unless (← IO.FS.readFile (repo / "lean-toolchain")) ==
      (← IO.FS.readFile (repo / "website" / "lean-toolchain")) do
    throw <| IO.userError "provisioning: website/lean-toolchain differs from the root"
  let mode ← readBuildMode repo
  stream (repo / "website") "lake"
    (lakeOptions mode ++ #["build", "verso/VersoManual"]) (← freshBuildEnvironment repo mode)

/-- Emit compiler, artifact policy and discovered source scope for CI cache keys. Cache hits
still run source receipt admission. GitHub's output and environment protocols are trusted IO. -/
def ciIdentity (repo : FilePath) : IO Unit := do
  requireCompiler repo
  let mode ← readBuildMode repo
  unless isObjectName Lean.githash do
    throw <| IO.userError "provisioning: the compiler commit is not a full Git object name"
  let policy := if mode == .source then s!"-v{sourceArtifactPolicy}" else ""
  let source ← sourceModule repo mode
  let value := s!"{Lean.githash}-{mode.spelling}{policy}"
  say s!"dependency identity {value}"
  if let some path ← IO.getEnv "GITHUB_OUTPUT" then
    let handle ← IO.FS.Handle.mk path .append
    handle.putStr s!"identity={value}\n"
    handle.putStr s!"mode={mode.spelling}\n"
    handle.putStr s!"scope={if mode == .source then toString (hash source) else "full"}\n"
  if let some path ← IO.getEnv "GITHUB_ENV" then
    let handle ← IO.FS.Handle.mk path .append
    for (name, value) in ← freshBuildEnvironment repo mode do
      if let some value := value then handle.putStr s!"{name}={value}\n"

/-- Run an argv command with the repository's artifact policy inherited by its descendants.
The caller chooses the process; no shell interprets its arguments. -/
def execute (repo dir : FilePath) (command : String) (args : Array String) : IO Unit := do
  let mode ← readBuildMode repo
  stream (repo / dir) command args (← freshBuildEnvironment repo mode)

end RegulaProvision

/-- Standalone entrypoint for local sharing, CI dependency setup, Verso and commands that
must inherit the selected artifact mode. Every invocation starts at the repository root. -/
def main (args : List String) : IO Unit := do
  let repo ← IO.FS.realPath (← IO.currentDir)
  unless ← (repo / "lakefile.lean").pathExists do
    throw <| IO.userError "provisioning: run from the repository root"
  match args with
  | [] =>
    if (← IO.getEnv "GITHUB_ACTIONS") == some "true" then
      IO.println "provisioning: local sharing skipped on GitHub Actions (CI uses the Mathlib plan)"
    else if System.Platform.isWindows then
      if (← RegulaProvision.readBuildMode repo) == .source then
        throw <| IO.userError "provisioning: source dependency mode is not supported on Windows"
      IO.println "provisioning: not supported on Windows; provision with `lake -d audit exe cache \
        get`"
    else RegulaProvision.provision repo
  | ["mathlib"] =>
    RegulaProvision.requireCompiler repo
    let mode ← RegulaProvision.readBuildMode repo
    if mode == .source then RegulaProvision.provision repo
    else RegulaProvision.buildMathlib repo mode false #["-d", "audit"]
  | ["verso"] => RegulaProvision.provisionVerso repo
  | ["identity"] => RegulaProvision.ciIdentity repo
  | "exec" :: dir :: command :: rest =>
    RegulaProvision.execute repo dir command rest.toArray
  | _ =>
    throw <| IO.userError "usage: lean --run lean/RegulaProvision.lean \
      [mathlib | verso | identity | exec DIR COMMAND ARGS...]"
