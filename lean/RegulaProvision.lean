import Lean.Data.Json
import Lean.Util.Path

/-! # Dependency provisioning

Default setup checks the released compiler and acquires no dependencies. Only the explicit
Mathlib integration command provisions Mathlib; the website's Verso has its own command.
The root package, the example library and the website require no Mathlib.

Local Mathlib provisioning reuses one read-only store per pinned Mathlib revision and exact
compiler commit. It fetches upstream artifacts and builds missing modules and exported native
objects before sealing the store. The integration package links its Mathlib checkout there;
its other dependencies are writable independent copies. CI instead fetches the published
artifacts into its own writable integration workspace.

Creation and publication use a staging directory, an exclusive store lock and one rename.
Existing upstream-cache receipts and directory names remain compatible. The receipt origin
has only the upstream-cache constructor: historical source receipts fail decoding and their
stores are neither admitted nor pruned. Registered copies protect shared stores from removal.
Git, Lake, Mathlib's cache tool, compiler reports, copying, locking and filesystem effects are
trusted; the pure decisions below carry their execution-linked contracts. The link installation
(`installLinkWith`) is written over its operations, and `RegulaProvision.Link` states its runs in
the filesystem model of `RegulaCore.Filesystem`.

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

/-- Shared constructor source embedded by Lean; the cold provisioner imports only the toolchain.
Assumes: Lean v4.34.1 `Lean/Elab/BuiltinTerm.lean:437-445` elabIncludeStr reads this source at elaboration,
and the pinned Lean interpreter executes it before project artifacts exist. -/
def constructionSource : String := include_str "RegulaCore/CopyProgram.lean"

/-- Run the shared construction source's entrypoint (`Construction.sourceMain`) with `args` before
cold artifacts exist, and decode the JSON it prints; `what` names the observation in an error.
The interpreter reads its source from stdin, without a temporary file or removal.

Assumes: Lean v4.34.1 `IO.Process.output` supplies stdin and waits for the child
(`Init/System/IO.lean:1544-1557`);
`Lean/Util/Path.lean:85-86` identifies the running toolchain. `--stdin --run`
(`Lean/Shell.lean:497-518,552-560`) faithfully executes constructionSource. -/
private def construction {α : Type} [FromJson α] (what : String) (args : Array String) : IO α := do
  let out ← IO.Process.output {
    cmd := ((← Lean.getBuildDir) / "bin/lean").toString
    args := #["--stdin", "--run", "Construction.lean"] ++ args
    env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none)] }
    (constructionSource ++ "\n/-- Cold construction entrypoint. -/\n" ++
      "def main := Regula.Filesystem.Construction.sourceMain\n")
  unless out.exitCode == 0 do
    throw <| IO.userError s!"provisioning {what} unavailable: {out.stderr}"
  IO.ofExcept (fromJson? (← IO.ofExcept (Json.parse out.stdout)))

/-- Obtain the shared Git environment observation before cold artifacts exist. This runs the
same gitEnvironment definition as the copy adapter, without a second Git policy or launcher.
Construction.gitEnvironment documents the Git and OS assumptions. -/
private def gitEnvironment : IO (Array (String × Option String)) :=
  construction "Git environment" #["git-environment", "", ""]

/-- The entries of the directory `path`, listed by the shared construction source
(`Construction.listNames`), so a failed read of the directory stops instead of returning fewer
entries. `Construction.ReadsNames` names the listing programs it admits and their sources. -/
private def listDirectory (path : FilePath) : IO (Array IO.FS.DirEntry) := do
  let names : Array String ← construction s!"listing of {path}" #["list", path.toString, ""]
  return names.map fun name => { root := path, fileName := name }

private def run (cwd : FilePath) (cmd : String) (args : Array String) : IO Ran := do
  let (args, env) ← if cmd == "git" then
      pure (#["-c", "core.symlinks=false"] ++ args, ← gitEnvironment)
    else pure (args, #[])
  let out ← IO.Process.output {
    cmd, args, cwd := some cwd, env := env.push ("GHCR_TOKEN", none), stdin := .null }
  return ⟨out.exitCode, out.stdout, out.stderr⟩

private def require (cwd : FilePath) (cmd : String) (args : Array String) : IO String := do
  let ran ← run cwd cmd args
  unless ran.exitCode == 0 do
    throw <| IO.userError s!"provisioning: `{cmd} {" ".intercalate args.toList}` in {cwd} \
      failed ({ran.exitCode}): {ran.stderr.trimAscii}"
  return ran.stdout

/-- The Git isolation of the Lake commands this program starts
(`Regula.Filesystem.Construction.isolationEnvironment`), obtained as `gitEnvironment` obtains the
Git environment, from the same embedded source (`construction`). Each Lake command receives it
(`stream`), so the Git commands that Lake starts for it, and those of the programs it runs,
inherit it.

Assumes: as for `gitEnvironment`; Construction.isolationEnvironment documents the Git and OS
assumptions. -/
private def isolationEnvironment : IO (Array (String × Option String)) :=
  construction "Git isolation" #["process-environment", "", ""]

/-- Run a Lake command with inherited output, for long steps whose progress the user should see,
under the Git isolation `isolation` (`isolationEnvironment`). -/
private def stream (isolation : Array (String × Option String)) (cwd : FilePath) (cmd : String)
    (args : Array String) : IO Unit := do
  let child ← IO.Process.spawn {
    cmd, args, env := isolation.push ("GHCR_TOKEN", none), cwd := some cwd,
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
  let isolation ← isolationEnvironment
  for command in mathlibCommands readOnly do
    stream isolation cwd "lake" command

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

/-! ### The installation of a link

`installLinkWith` is written once over the operations `LinkOps`. The driver runs it at `linkOps`,
and `RegulaProvision.Link` states its runs in the filesystem model of `RegulaCore.Filesystem`. -/

/-- The operations of a link installation in a monad `m`. The driver supplies them in `IO`
(`linkOps`); a model supplies them as actions on its states (`RegulaProvision.LinkModel`). -/
structure LinkOps (m : Type → Type) where
  /-- What `lstat(2)` reports of a path, which follows no link at its last component. -/
  metadata : FilePath → m IO.FS.Metadata
  /-- Create an empty directory with `mkdir(2)`. -/
  directory : FilePath → m Unit
  /-- Make a symbolic link whose text is the first argument at the path. -/
  link : String → FilePath → m Unit
  /-- Move the entry at the first path to the second, replacing what is there: `rename(2)`. -/
  rename : FilePath → FilePath → m Unit
  /-- Remove the entry at the path, which is not a directory: `unlink(2)`. -/
  removeFile : FilePath → m Unit
  /-- Remove the directory at the path when it is empty: `rmdir(2)`. -/
  removeDir : FilePath → m Unit

/-- The type of the entry at `path`, read without following a link there, or `none` when nothing
is there. Any other failure of the read is thrown, never read as absence. -/
def entryKindWith {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : LinkOps m)
    (path : FilePath) : m (Option IO.FS.FileType) :=
  tryCatchThe IO.Error (do return some (← ops.metadata path).type) fun
    | .noFileOrDirectory .. => pure none
    | error => throw error

/-- Where the link for `path` is made: the new directory, the hidden sibling of `path` that
`nonce` names, and the link's place in it, under the name of `path`. `none` when `path` has no
parent or no name. -/
def linkStage (path : FilePath) (nonce : String) : Option (FilePath × FilePath) := do
  let parent ← path.parent
  let name ← path.fileName
  let stage := parent / s!".{name}.{nonce}"
  return (stage, stage / name)

/-- Make the new directory `stage`, make the link to `target` at `staged` in it, move the link
over `path`, and remove `stage`.

The creation of `stage` is the step that refuses an occupied place: `mkdir(2)` fails when any
entry is at `stage` and follows no link there. Nothing reads `stage` before it, so no earlier
check can go stale, and nothing runs after it fails. The link is then made in the empty
directory that this run made. When the link or the move fails, the link is removed when a link
is at `staged`, and then `stage` is removed, which `rmdir(2)` does only when it is empty. A
failure of that cleanup leaves them, and the first failure is reported. -/
def placeLinkWith {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : LinkOps m)
    (stage staged path : FilePath) (target : String) : m Unit := do
  ops.directory stage
  tryCatchThe IO.Error (do ops.link target staged; ops.rename staged path) fun error => do
    tryCatchThe IO.Error
      (do
        if (← entryKindWith ops staged) == some .symlink then ops.removeFile staged
        ops.removeDir stage)
      fun _ => pure ()
    throw error
  ops.removeDir stage

/-- Fail unless a symbolic link is at `path` and nothing is at `stage`. -/
def confirmLinkWith {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : LinkOps m)
    (path stage : FilePath) : m Unit := do
  let placed ← entryKindWith ops path
  let left ← entryKindWith ops stage
  match placed, left with
  | some .symlink, none => pure ()
  | _, _ => throw <| IO.userError s!"provisioning: after the link's installation, {path} is not \
      a link or {stage} is still there"

/-- Replace `path` by a symbolic link to `target`, so that readers see the old entry or the
link. The link is made in a new directory beside `path` (`linkStage`), whose creation refuses
any entry already at its place (`placeLinkWith`), and moved over `path` with one rename. The run
then fails unless a link is at `path` and the directory is gone (`confirmLinkWith`).

`RegulaProvision.installLink_refused` states that a run from a state where an entry is at the
directory's place fails and changes nothing, under `RegulaProvision.RefusesOccupied`;
`RegulaProvision.installLink_placed` states the result of a run that succeeds, under
`Regula.Filesystem.ReadsEntry`. -/
def installLinkWith {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : LinkOps m)
    (path : FilePath) (target nonce : String) : m Unit := do
  let some (stage, staged) := linkStage path nonce
    | throw <| IO.userError s!"provisioning: {path} has no parent or no name"
  placeLinkWith ops stage staged path target
  confirmLinkWith ops path stage

/-- `mkdir(2)` of the directory in which the link is made, and then its mode 0700, so that only
this user can write in it.

Assumes: Lean v4.34.1 `IO.FS.createDir` (`Init/System/IO.lean:895-900`) calls `mkdir` once and
reports its error (`runtime/io.cpp:1181-1195`); `mkdir` fails with `EEXIST` when any entry is at
the path, and follows no symbolic link there (POSIX.1-2024 `mkdir()`). This is
`RegulaProvision.RefusesOccupied`. `IO.Prim.setAccessRights` (`Init/System/IO.lean:1650`,
`runtime/io.cpp:381-392`) calls `chmod` only after `mkdir` made the directory, and no other process
replaces it in between. -/
@[noinline] private def makeStage (stage : FilePath) : IO Unit := do
  IO.FS.createDir stage
  IO.Prim.setAccessRights stage 448

/-- `ln -s -- TARGET NAME`, run in the directory of `staged`, where `NAME` is the last component of
`staged`: a symbolic link with the text `target` at `staged`. The operand is that name alone, so a
relative `staged` is not resolved twice, once for the working directory and once for the operand.

Assumes: with two operands, the last of which names nothing, `ln -s` makes the link at exactly
that path with `symlink(2)`, which fails when an entry is there (POSIX.1-2024 `symlink()`). Apple
file_cmds-479 `ln/ln.c:145-146,253-265,307,353` adds the source's name to the last operand only
when that operand names a directory or ends in `/` or `/.`. GNU coreutils 9.4
`src/ln.c:160-164,604-633` calls `symlinkat` at the operand first, and makes the link inside it
only when that fails and a directory is there. Trusted: the installed macOS `/bin/ln` reports
file_cmds-487.0.1, whose source is not published, and keeps this behaviour; `ln` is found on
`PATH` (issue 388); `ln` starts in the directory of `staged`, which a relative path names from
this process's working directory, as for `IO.FS.createDir`.
`installLinkWith` gives `staged` a name in a directory that this run made, so it names nothing
when no other process writes there. -/
@[noinline] private def makeLink (target : String) (staged : FilePath) : IO Unit := do
  let some name := staged.fileName
    | throw <| IO.userError s!"provisioning: {staged} has no name"
  let _ ← require (staged.parent.getD ".") "ln" #["-s", "--", target, name]

/-- `IO.FS.rename`: the move of the link that `installLinkWith` made over its place.

Assumes: Lean v4.34.1 `IO.FS.rename` (`Init/System/IO.lean:903-909`) calls `rename(2)`
(`runtime/io.cpp:1209-1238`), which moves a symbolic link itself and replaces a link or a file at
the destination, not its target. -/
@[noinline] private def moveLink (source destination : FilePath) : IO Unit :=
  IO.FS.rename source destination

/-- `IO.FS.removeFile`: the removal of a link that `installLinkWith` made and did not move.

Assumes: Lean v4.34.1 `IO.FS.removeFile` (`Init/System/IO.lean:881-886`) calls `unlink(2)`
(`runtime/io.cpp:1351-1364`), which removes a symbolic link, not its target. -/
@[noinline] private def removeLink (path : FilePath) : IO Unit :=
  IO.FS.removeFile path

/-- `IO.FS.removeDir`: the removal of the directory that `installLinkWith` made.

Assumes: Lean v4.34.1 `IO.FS.removeDir` (`Init/System/IO.lean:888-894`) calls `rmdir(2)`
(`runtime/io.cpp:1197-1207`), which removes only an empty directory. -/
@[noinline] private def removeStage (path : FilePath) : IO Unit :=
  IO.FS.removeDir path

/-- The operations of the link installation that the driver runs. The driver provisions nothing
on Windows (`main`), where `symlinkMetadata` follows a link at the path. -/
def linkOps : LinkOps IO where
  metadata := System.FilePath.symlinkMetadata
  directory := makeStage
  link := makeLink
  rename := moveLink
  removeFile := removeLink
  removeDir := removeStage

/-- Replace `path` by a symbolic link to `target` with `installLinkWith` at `linkOps`, in a
directory named with a new nonce. -/
private def installLink (path : FilePath) (target : String) : IO Unit := do
  installLinkWith linkOps path target (← nonce)

/-- Interpret the one shared constructor in a cold driver. The wrapper is this run's
exclusive file in a private staging parent, and is removed when the interpreter ends.
Assumes: the running Lean executable owns its installation (`Lean/Util/Path.lean:85-86`);
Lean's interpreter executes the embedded source faithfully. -/
private def runConstruction (parent : FilePath) (domain source : String) (target : FilePath) :
    IO Unit := do
  let wrapper := parent / s!".regula-copy-{← nonce}.lean"
  let handle ← IO.FS.Handle.mk wrapper .writeNew
  handle.putStr (constructionSource ++ "\n/-- Cold construction entrypoint. -/\n" ++
    "def main := Regula.Filesystem.Construction.sourceMain\n")
  handle.flush
  try
    let result ← IO.Process.output {
      cmd := ((← Lean.getBuildDir) / "bin/lean").toString
      args := #["--run", wrapper.toString, domain, source, target.toString]
      env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none)] }
    unless result.exitCode == 0 do
      throw <| IO.userError s!"provisioning construction failed: {result.stdout}{result.stderr}"
  finally IO.FS.removeFile wrapper

/-- Install an independently writable indexed worktree, its regular `.lake/build` outputs and plain Git metadata through the
shared constructor. Untracked links and special source entries fail before installation. Tracked
index mode 120000 entries become target-text regular files, and the generated Git config sets
core.symlinks=false. Every provisioner Git command removes the shared observer's repository-local
environment and disables system/global config, with command-scope core.symlinks=false. Extensions,
includes, redirects, alternates and indexed/stored spelling differences refuse. Files use 0644
except indexed 100755 files use 0755; directories use 0755.
Index modes and target text come from Git's ls-files and blob protocols, never a followed link.
`Construction.gitConstruct_io` describes the executed index/build account's exact plain tree.
This does not place
a packages link. `installLink` is the separate shared-cache registration mechanism, outside this
copy operation. -/
private def installClone (path source : FilePath) : IO Unit := do
  let some parent := path.parent | throw <| IO.userError s!"provisioning: {path} has no parent"
  let staged := parent / s!".{path.fileName.getD "clone"}.{← nonce}"
  try
    runConstruction parent "git" source.toString staged
    -- New inodes require index refresh; executable rights already agree with the index.
    let _ ← require staged "git" #["update-index", "-q", "--refresh"]
    IO.FS.rename staged path
  catch error =>
    if (← kind? staged) == some .dir then IO.FS.removeDirAll staged
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
  unless entry.getObjValD "subDir" matches .null do
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
  for entry in ← listDirectory path do
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
  let lakefile := "name = \"regula_mathlib_packages\"\n\n[[require]]\nname = \"mathlib\"\n" ++
    s!"git = \"{pins.mathlibUrl}\"\nrev = \"{pins.mathlibRev}\"\n"
  let lock := (manifest
    |>.setObjVal! "name" (.str "regula_mathlib_packages")
    |>.setObjVal! "packagesDir" (.str ".lake/packages")
    |>.setObjVal! "packages" (.arr (pins.git.map (·.1)))).pretty ++ "\n"
  let instructions := Json.arr #[
    Json.mkObj [("relative", toJson (["lakefile.toml"] : List String)), ("text", toJson lakefile)],
    Json.mkObj [("relative", toJson (["lake-manifest.json"] : List String)), ("text", toJson lock)],
    Json.mkObj [("relative", toJson (["lean-toolchain"] : List String)),
      ("source", toJson (repo / "lean-toolchain").toString)]]
  let descriptor := parent / s!".regula-instructions-{← nonce}.json"
  let handle ← IO.FS.Handle.mk descriptor .writeNew
  handle.putStr instructions.compress
  handle.flush
  try runConstruction parent "generated" descriptor.toString staging
  finally IO.FS.removeFile descriptor
  -- This new shared-store workspace deliberately fetches the manifest's pinned Git packages.
  -- It has a closed generated configuration, not an existing-project relocation or override
  -- load. Lake and Git's new checkout contents remain trusted (libraryRemovals).
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
    for entry in ← listDirectory packagesRoot do
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
  for entry in ← listDirectory parent do
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
  for entry in ← listDirectory parent do
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
    say s!"cloned {", ".intercalate cloned.toList} (writable independent copies)"

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
  stream (← isolationEnvironment) (repo / "website") "lake" #["build", "verso/VersoManual"]

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
