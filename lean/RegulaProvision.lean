import Lean.Data.Json

/-! # Dependency provisioning

Default setup checks the released compiler and acquires no dependencies. Only the explicit
Mathlib integration command provisions Mathlib; the website's Verso has its own command.
The root package, the example library and the website require no Mathlib.

Local Mathlib provisioning reuses one read-only store per pinned Mathlib revision and exact
compiler commit. It fetches upstream artifacts and builds missing modules and exported native
objects before sealing the store. The integration package links its Mathlib checkout there;
its other dependencies are writable copy-on-write clones. CI instead fetches the published
artifacts into its own writable integration workspace.

Creation and publication use a staging directory, an exclusive store lock and one rename.
Existing upstream-cache receipts and directory names remain compatible. The receipt origin
has only the upstream-cache constructor: historical source receipts fail decoding and their
stores are neither admitted nor pruned. Registered copies protect shared stores from removal.
Git, Lake, Mathlib's cache tool, compiler reports, copying, locking and filesystem effects are
trusted; the pure decisions below carry their execution-linked contracts.

The integration preflight requires the integration package's toolchain to match the root and,
with --require, requires provisioned Mathlib as the first step inside the timed integration check.
-/
namespace RegulaProvision
open System Lean

/-! ## Pure decisions -/

/-- The only artifact origin accepted by a shared-store receipt. The constructor spelling
preserves the existing JSON format; source-origin receipts cannot decode to this type. -/
inductive ReceiptOrigin where
  /-- Published artifacts with missing native objects built before read-only sharing. -/
  | upstreamCache
  deriving DecidableEq, Repr, ToJson, FromJson

/-- Fetch published Mathlib artifacts; a read-only store also needs every exported native object. -/
def mathlibCommands (readOnly : Bool) : List (Array String) :=
  #["exe", "cache", "get"] ::
    if readOnly then [#["build", "Mathlib", "Mathlib:static.export"]] else []

/-- Native objects are built exactly when the workspace will be sealed read-only. -/
theorem upstream_plan (readOnly : Bool) :
    mathlibCommands readOnly =
      if readOnly then [#["exe", "cache", "get"], #["build", "Mathlib", "Mathlib:static.export"]]
      else [#["exe", "cache", "get"]] := by
  cases readOnly <;> rfl

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

/-- The stable shared directory name for one Mathlib revision and compiler commit. -/
def sharedKey (mathlibRev githash : String) : String := s!"{mathlibRev}-lean-{githash}"

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
  mode : ReceiptOrigin := .upstreamCache
  /-- Legacy wire field; a stable receipt must record zero. -/
  artifactPolicy : Nat := 0
  /-- Legacy wire field; a stable receipt must record no generated source. -/
  source : String := ""
  /-- Each package checkout in the shared directory, at the commit it was materialized at. -/
  packages : Array Pin
  deriving Repr, ToJson, FromJson

/-- Receipt schema this program writes and accepts. -/
def receiptSchema : Nat := 1

/-- The stable directory identified by the receipt's pinned revisions. -/
def Receipt.key (receipt : Receipt) : String := sharedKey receipt.mathlibRev receipt.leanGithash

/-- Admit only a stable receipt for these exact revisions and compatible package pins. -/
def admits (receipt : Receipt) (mathlibRev githash : String) (pins : Array Pin) : Bool :=
  receipt.schemaVersion == receiptSchema && receipt.mathlibRev == mathlibRev &&
    receipt.leanGithash == githash && receipt.artifactPolicy == 0 && receipt.source == "" &&
    pins.all fun pin => receipt.packages.all fun held => held.name != pin.name || held.rev == pin.rev

/-- An admitted receipt has the requested revisions, empty legacy source markers, and no
recorded package at a different revision from a pin with the same name. -/
theorem admits_sound (receipt : Receipt) (mathlibRev githash : String) (pins : Array Pin)
    (h : admits receipt mathlibRev githash pins = true) :
    receipt.mathlibRev = mathlibRev ∧ receipt.leanGithash = githash ∧
      receipt.artifactPolicy = 0 ∧ receipt.source = "" ∧
      ∀ pin ∈ pins, ∀ held ∈ receipt.packages, held.name = pin.name → held.rev = pin.rev := by
  simp only [admits, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨_, hRev⟩, hGithash⟩, hPolicy⟩, hSource⟩, hPins⟩ := h
  refine ⟨hRev, hGithash, hPolicy, hSource, fun pin hPin held hHeld hName => ?_⟩
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hPin
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hHeld
  exact ((hPins i hi) j hj).resolve_left (fun h => h hName)

/-- Admission fixes the requested stable store key. -/
theorem admits_key (receipt : Receipt) (mathlibRev githash : String) (pins : Array Pin)
    (h : admits receipt mathlibRev githash pins = true) :
    receipt.key = sharedKey mathlibRev githash := by
  obtain ⟨hRev, hGithash, _⟩ := admits_sound receipt mathlibRev githash pins h
  simp [Receipt.key, hRev, hGithash]

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
directory whose receipt identifies it is ever removed. A copy provisioned while the root package's
packages directory held Mathlib still has its registered link there (`retiredLink`); a run removes
that link while it links a shared directory, so the directory is kept only by links in use. -/

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

/-- Where a copy linked Mathlib while the root package's packages directory held it, relative to
the repository root. No package of this repository pins Mathlib there any more. -/
def retiredLink : FilePath := ".lake/packages/mathlib"

/-- A registered link is removed from its copy when it still links the shared directory whose
registry records it and is the copy's retired link, not the link this run provisions. -/
def retires (link retired copy : String) (linked : Bool) : Bool :=
  linked && copy == retired && copy != link

/-- Only the retired link is removed, only while it links the shared directory, and never the
link this run provisions. -/
theorem retires_iff (link retired copy : String) (linked : Bool) :
    retires link retired copy linked = true ↔ linked = true ∧ copy = retired ∧ copy ≠ link := by
  simp [retires, and_assoc]

/-! ### Applicability of the Mathlib integration check -/

/-- The integration package must select the same toolchain as the repository. -/
def mathlibApplies (toolchain integration : String) : Bool := toolchain == integration

/-- The integration preflight accepts exactly equal selectors. -/
theorem mathlibApplies_iff (toolchain integration : String) :
    mathlibApplies toolchain integration = true ↔ toolchain = integration := by
  simp [mathlibApplies]

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
  let out ← IO.Process.output {
    cmd, args, cwd := some cwd, env := #[("GHCR_TOKEN", none)], stdin := .null }
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
    cmd, args, env := env.push ("GHCR_TOKEN", none), cwd := some cwd,
    stdin := .null, stdout := .inherit, stderr := .inherit }
  let exit ← child.wait
  unless exit == 0 do
    throw <|
        IO.userError
            s!"provisioning: `{cmd} {" ".intercalate args.toList}` in {cwd} failed ({exit})"

private def say (line : String) : IO Unit := IO.println s!"provisioning: {line}"

private def nonce : IO String := do
  let bytes ← IO.getRandomBytes 8
  return s!"{← IO.Process.getPID}-{bytes.foldl (fun value byte => value * 256 + byte.toNat) 0}"

/-- Execute the released Mathlib plan in the workspace whose packages receive the artifacts. -/
private def buildMathlib (cwd : FilePath) (readOnly : Bool) : IO Unit := do
  for command in mathlibCommands readOnly do
    stream cwd "lake" command

private def admitComponent (what text : String) : IO Component := do
  let some name := component? text
    | throw <| IO.userError s!"provisioning: {what} '{text}' is not a single path component"
  return name

/-- Kind of the path itself, without following a final symbolic link. -/
private def kind? (path : FilePath) : IO (Option IO.FS.FileType) := do
  try return some (← path.symlinkMetadata).type catch _ => return none

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
Mathlib: the Mathlib integration package, which requires the root `regula` package by relative
path and keeps its own packages directory. -/
def mathlibPackage : FilePath := "integration/mathlib"

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
      json.setObjVal! "mode" (toJson ReceiptOrigin.upstreamCache)
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

/-- Create the shared directory `final` from a fresh staging directory, run the stable build
plan, record and seal it, and publish with one rename.
The caller holds the lock. -/
private def create (repo parent final : FilePath) (key : String) (manifest : Json)
    (pins : Pins) : IO Unit := do
  let staging := parent / s!"{key}.staging-{← nonce}"
  IO.FS.createDir staging
  IO.FS.writeFile (staging / "lakefile.toml")
    ("name = \"regula_mathlib_packages\"\n\n[[require]]\nname = \"mathlib\"\n" ++
      s!"git = \"{pins.mathlibUrl}\"\nrev = \"{pins.mathlibRev}\"\n")
  IO.FS.writeFile (staging / "lake-manifest.json") ((manifest
    |>.setObjVal! "name" (.str "regula_mathlib_packages")
    |>.setObjVal! "packagesDir" (.str ".lake/packages")
    |>.setObjVal! "packages" (.arr (pins.git.map (·.1)))).pretty ++ "\n")
  IO.FS.writeFile (staging / "lean-toolchain") (← IO.FS.readFile (repo / "lean-toolchain"))
  try
    let githash := (← require staging "lean" #["--githash"]).trimAscii.toString
    unless githash == Lean.githash do
      throw <|
          IO.userError
              s!"provisioning: the staged toolchain is {githash}, not the running {Lean.githash}"
    -- `cache get` unpacks into the workspace's default `.lake/packages` and ignores a custom
    -- packages directory, so the staging workspace keeps the default.
    buildMathlib staging true
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
      leanGithash := Lean.githash, leanVersion := Lean.versionString, packages := held }
    IO.FS.writeFile (staging / receiptName) ((toJson receipt).pretty ++ "\n")
    makeReadOnly staging dirs
    IO.FS.rename staging final
  catch error =>
    if (← kind? staging) matches some .dir then removeReadOnly staging
    throw error

/-- The admitted shared directory `parent/key` for these pins, created once. The caller holds
the lock. -/
private def ensureShared (repo parent : FilePath) (key : Component) (manifest : Json)
    (pins : Pins) : IO (FilePath × Receipt) := do
  let pinned := pins.git.map (·.2)
  let final := parent / key.val
  let admitted? := fun (receipt? : Option Receipt) => receipt?.filter fun receipt =>
    admits receipt pins.mathlibRev Lean.githash pinned
  if let some receipt := admitted? (← readReceipt final) then return (final, receipt)
  if (← kind? final) matches some _ then
    throw <| IO.userError s!"provisioning: {final} exists but its receipt does not admit \
      Mathlib {pins.mathlibRev} for Lean {Lean.githash}; move it aside and \
      provision again"
  -- Under the lock, only abandoned stable stages have this exact stable-key prefix.
  for entry in ← parent.readDir do
    if entry.fileName.startsWith s!"{key.val}.staging-" then
      if (← kind? entry.path) matches some .dir then removeReadOnly entry.path
  say s!"creating the shared Mathlib {pins.mathlibRev} for Lean {Lean.versionString} \
    in {final}"
  let started ← IO.monoMsNow
  create repo parent final key.val manifest pins
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
registry the copies that no longer link its directory. First remove this copy's `retired` link
where a registry records it and it still links that registry's directory (`retires`), so it
keeps no directory; `link` is the link this run provisions. Only a symbolic link is removed from
a copy, never a directory. Only directories that their receipt identifies are touched, and a
failure is reported, not fatal. The caller holds the lock. -/
private def prune (parent : FilePath) (current link retired : String) : IO Unit := do
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
            let linked ← match target with
              | some target => links copy target
              | none => pure false
            unless retires link retired copy linked do return (copy, linked)
            IO.FS.removeFile copy
            say s!"removed the retired link {copy} to {entry.path}"
            return (copy, false)
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

/-- Refuse a package link unless its actual target belongs to an identified stable store.
Source receipts cannot decode as `Receipt`; `admits_sound` also excludes source markers in a
stable receipt. Unknown or dangling links are preserved. Filesystem observations are trusted. -/
private def requireStablePackageLink (path : FilePath) : IO Unit := do
  unless (← kind? path) == some .symlink do return
  let refusal := IO.userError s!"provisioning: preserving {path}: its link does not identify a \
    stable shared store; source-origin and unknown package links require manual disposition"
  let target ← try IO.FS.realPath path catch _ => throw refusal
  let store := target.parent.bind (·.parent) |>.bind (·.parent)
  let some store := store | throw refusal
  let some name := store.fileName | throw refusal
  let some package := target.fileName | throw refusal
  unless target == sharedPackages store / package do throw refusal
  let receipt ← readReceipt store
  unless found name receipt == .shared do throw refusal
  let some receipt := receipt | throw refusal
  unless admits receipt receipt.mathlibRev receipt.leanGithash #[] do throw refusal

/-- Check every pinned link before acquiring a store or changing registrations and packages. -/
private def requireStablePackageLinks (packages : FilePath) (pins : Pins) : IO Unit := do
  for (_, pin) in pins.git do
    requireStablePackageLink (packages / pin.name)

/-- Link or clone every pinned package of the shared closure into the packages directory. -/
private def provisionPackages (packages shared : FilePath) (receipt : Receipt) (pins : Pins) :
    IO Unit := do
  requireStablePackageLinks packages pins
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

/-- Refuse a process using a different compiler from this program. -/
def requireCompiler (repo : FilePath) : IO Unit := do
  let githash := (← require repo "lean" #["--githash"]).trimAscii.toString
  unless githash == Lean.githash do
    throw <| IO.userError s!"provisioning: this repository's toolchain is {githash}, \
      but this program runs on {Lean.githash}"

/-- Observe whether the integration package selects the root's toolchain. -/
def mathlibApplicability (repo : FilePath) : IO (Bool × String) := do
  let applies := mathlibApplies (← IO.FS.readFile (repo / "lean-toolchain"))
    (← IO.FS.readFile (repo / mathlibPackage / "lean-toolchain"))
  return (applies, s!"{mathlibPackage}/lean-toolchain differs from the repository's lean-toolchain")

/-- Refuse a copy to which the Mathlib integration check does not apply: the check is qualified
only for the toolchain and Mathlib revision the integration package pins, so nothing is
provisioned or checked for another compiler. -/
def requireMathlibApplies (repo : FilePath) : IO Unit := do
  let (applies, reason) ← mathlibApplicability repo
  unless applies do
    throw <| IO.userError s!"provisioning: the Mathlib integration check does not apply to this \
      copy: {reason}. It is qualified only for the toolchain and Mathlib revision that \
      {mathlibPackage} pins; not run, so nothing Mathlib-specific is claimed"

/-- Provision this copy. -/
def provision (repo : FilePath) : IO Unit := do
  requireCompiler repo
  requireMathlibApplies repo
  let some (manifest, pins) ← readPins repo
    | say s!"{mathlibPackage}/lake-manifest.json pins no Mathlib; nothing to share"
  let key ← admitComponent "shared directory" (sharedKey pins.mathlibRev Lean.githash)
  let packages ← packagesPath repo pins
  let parent := (← cacheBase) / "mathlib-packages"
  IO.FS.createDirAll parent
  let lock ← IO.FS.Handle.mk (parent / lockName) .append
  unless ← lock.tryLock do
    say s!"waiting for another copy that is provisioning from {parent}"
    lock.lock
  let shared ← try
      requireStablePackageLinks packages pins
      let (shared, receipt) ← ensureShared repo parent key manifest pins
      let link := (packages / "mathlib").toString
      registerCopy parent key.val link
      provisionPackages packages shared receipt pins
      prune parent key.val link (repo / retiredLink).toString
      pure shared
    finally
      lock.unlock
  say s!"Mathlib {pins.mathlibRev} is shared read-only from {shared}"

/-- The commit that the Lake manifest of `package` pins for the Git package `name`. -/
def manifestRevision (repo : FilePath) (package name : String) : IO String := do
  let manifest ← IO.ofExcept
    (Json.parse (← IO.FS.readFile (repo / package / "lake-manifest.json")))
  for entry in ← IO.ofExcept (manifest.getObjValAs? (Array Json) "packages") do
    if let some (_, pin, _) ← IO.ofExcept (gitPin entry) then
      if pin.name == name then return pin.rev
  throw <| IO.userError s!"provisioning: {package}/lake-manifest.json pins no Git package {name}"

/-- Provision the website's pinned Verso with the released compiler. -/
def provisionVerso (repo : FilePath) : IO Unit := do
  requireCompiler repo
  -- The standard's examples import the `audit/` package's modules in the website's workspace.
  for package in #["audit", "website"] do
    unless (← IO.FS.readFile (repo / "lean-toolchain")) ==
        (← IO.FS.readFile (repo / package / "lean-toolchain")) do
      throw <| IO.userError s!"provisioning: {package}/lean-toolchain differs from the root"
  -- The `markdown/` package pins MD4Lean in its own manifest, and the website's manifest pins it
  -- through Verso. Lake has one lock manifest for each workspace, so the commit has two sources.
  -- The two workspaces keep one checkout in the root `.lake/packages`: two commits would make
  -- each workspace move that checkout and build it again during the timed documentation step.
  let reader ← manifestRevision repo "markdown" "MD4Lean"
  let verso ← manifestRevision repo "website" "MD4Lean"
  unless reader == verso do
    throw <| IO.userError s!"provisioning: markdown/lake-manifest.json pins MD4Lean {reader} \
      and website/lake-manifest.json pins MD4Lean {verso}; the two packages keep one checkout, \
      so pin the same commit in the two manifests"
  stream (repo / "website") "lake" #["build", "verso/VersoManual"]

/-- Check the exact supported compiler before provisioning any dependency artifacts. -/
def requireReleasedCompiler (repo : FilePath) : IO Unit := do
  requireCompiler repo
  let out ← IO.Process.output {
    cmd := "lean", args := #["lean/RegulaPolicy/Compiler.lean"], cwd := some repo,
    env := #[("REGULA_COMPILER_GUARD", some "1"), ("GHCR_TOKEN", none)], stdin := .null }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"provisioning: released compiler guard failed:\n{out.stdout}{out.stderr}"
  unless out.stdout.replace "\r" "" == s!"{Lean.versionString}\n{Lean.githash}\n" do
    throw <| IO.userError "provisioning: the policy guard and provisioning program report different compiler identities"

/-- Refuse retired acquisition settings without installing, restoring or rewriting anything. -/
def requireReleasedSetup (repo : FilePath) : IO Unit := do
  for path in #["dependency-build-mode", ".github/compiler-source.json",
      ".github/snapshot-preparation.json", ".github/snapshot-compiler.json",
      ".github/compiler-snapshot.json"] do
    if ← (repo / path).pathExists then
      throw <| IO.userError s!"provisioning: retired compiler setup {path}; use a clean released-toolchain checkout"
  requireReleasedCompiler repo

end RegulaProvision

/-- Standalone released-toolchain setup and explicit Mathlib or Verso provisioning. -/
def main (args : List String) : IO Unit := do
  let repo ← IO.FS.realPath (← IO.currentDir)
  unless ← (repo / "lakefile.lean").pathExists do
    throw <| IO.userError "provisioning: run from the repository root"
  RegulaProvision.requireReleasedSetup repo
  match args with
  | [] =>
    IO.println "provisioning: default verification needs no dependency acquisition"
  | ["mathlib"] =>
    RegulaProvision.requireMathlibApplies repo
    if (← IO.getEnv "GITHUB_ACTIONS") == some "true" then
      RegulaProvision.buildMathlib (repo / RegulaProvision.mathlibPackage) false
    else if System.Platform.isWindows then
      IO.println s!"provisioning: sharing is not supported on Windows; provision with \
        lake exe cache get in {RegulaProvision.mathlibPackage}"
    else RegulaProvision.provision repo
  | ["mathlib-applies"] =>
    RegulaProvision.requireMathlibApplies repo
    IO.println "Mathlib integration check: applies (the integration package selects this toolchain)"
  | ["mathlib-applies", "--require"] =>
    RegulaProvision.requireMathlibApplies repo
    let mathlib := repo / RegulaProvision.mathlibPackage / ".lake" / "packages" / "mathlib"
    unless ← mathlib.pathExists do
      throw <| IO.userError s!"provisioning: {mathlib} is absent; run \
        lean --run lean/RegulaProvision.lean mathlib before scripts/verify.sh mathlib"
  | ["verso"] => RegulaProvision.provisionVerso repo
  | _ =>
    throw <| IO.userError "usage: lean --run lean/RegulaProvision.lean \
      [mathlib | mathlib-applies [--require] | verso]"
