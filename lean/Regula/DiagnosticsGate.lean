module

public section

namespace Regula.DiagnosticsGate

def fullVariable : String := "REGULA_FULL"

def proofVariable : String := "REGULA_PROOF"

def noCommentsVersion : String := "v0.2.0"

def noCommentsArgs : List String := ["check"]

inductive NoCommentsTarget where
  | darwinArm64
  | linuxX86_64
  deriving DecidableEq, Repr

def NoCommentsTarget.asset : NoCommentsTarget → String
  | .darwinArm64 => "no-comments-darwin-arm64"
  | .linuxX86_64 => "no-comments-linux-x86_64"

def NoCommentsTarget.sha256 : NoCommentsTarget → String
  | .darwinArm64 => "4c610e1b0f0f93f54e89f33acb13c5120ed4e7ecfc3bb5db85e562aba637fe2a"
  | .linuxX86_64 => "f1a5d5cee2214515f9d36d3bb7245beee3856c06a85f6593ac0b23c4a0c6941e"

def NoCommentsTarget.url (t : NoCommentsTarget) : String :=
  s!"https://github.com/rbeauchamp/lean-no-comments/releases/download/{noCommentsVersion}/{t.asset}"

def hostNoCommentsTarget? : Option NoCommentsTarget :=
  if System.Platform.isOSX && System.Platform.target.startsWith "arm64-" then
    some .darwinArm64
  else if !System.Platform.isOSX && System.Platform.isLinux && System.Platform.target.startsWith "x86_64-" then
    some .linuxX86_64
  else
    none

def executableRight : IO.FileRight where
  user := { read := true, write := true, execution := true }
  group := { read := true, execution := true }
  other := { read := true, execution := true }

def pathParts (p : System.FilePath) : List String :=
  p.normalize.components.filter fun c => c != "" && c != "."

def samePath (a b : System.FilePath) : Bool :=
  a.isAbsolute == b.isAbsolute && pathParts a == pathParts b

def isSingleFileLine (cs : List Char) : Bool :=
  match cs.reverse with
  | '\n' :: rname => !rname.isEmpty && !rname.contains '\n'
  | _ => false

def sha256Request (target : NoCommentsTarget) (path : System.FilePath) : IO.Process.SpawnArgs :=
  match target with
  | .darwinArm64 => { cmd := "shasum", args := #["-a", "256", "--", path.toString], stdin := .null }
  | .linuxX86_64 => { cmd := "sha256sum", args := #["--", path.toString], stdin := .null }

def sha256Matches (expected : String) (out : IO.Process.Output) : Bool :=
  let cs := out.stdout.toList
  let pref := (expected ++ "  ").toList
  out.exitCode == 0 &&
    ((pref.isPrefixOf cs && isSingleFileLine (cs.drop pref.length)) ||
     (('\\' :: pref).isPrefixOf cs && isSingleFileLine (cs.drop (pref.length + 1))))

def verifySha256 (target : NoCommentsTarget) (path : System.FilePath) : IO Unit := do
  let out ← IO.Process.output (sha256Request target path)
  if sha256Matches target.sha256 out then
    pure ()
  else
    throw <| IO.userError s!"local gate: SHA-256 verification failed for {path} (expected {target.sha256})"

def symlinkType? (p : System.FilePath) : IO (Option IO.FS.FileType) :=
  try
    let m ← p.symlinkMetadata
    pure (some m.type)
  catch
    | .noFileOrDirectory .. => pure none
    | e => throw e

def requireExactRealPath (label : String) (p : System.FilePath) : IO System.FilePath := do
  let real ← IO.FS.realPath p
  if samePath real p then
    pure real
  else
    throw <| IO.userError s!"local gate: {label} resolves outside expected location: {p} -> {real}"

def ensureSubdir (parent : System.FilePath) (name : String) : IO System.FilePath := do
  let p := parent / name
  match ← symlinkType? p with
  | some .dir => requireExactRealPath "cache directory" p
  | some _ =>
    throw <| IO.userError s!"local gate: cache directory component is not a directory: {p}"
  | none =>
    try
      IO.FS.createDir p
    catch e =>
      match ← symlinkType? p with
      | some .dir => pure ()
      | _ => throw e
    requireExactRealPath "cache directory" p

def ensureNoCommentsCacheDir : IO System.FilePath := do
  let root ← IO.FS.realPath "."
  let d1 ← ensureSubdir root ".cache"
  let d2 ← ensureSubdir d1 "no-comments"
  ensureSubdir d2 noCommentsVersion

def stageNoComments (target : NoCommentsTarget) (cachePath tmpPath : System.FilePath) : IO Unit := do
  IO.println s!"local gate: downloading {target.asset} ({noCommentsVersion})"
  (← IO.getStdout).flush
  let out ← IO.Process.output {
    cmd := "curl"
    args := #["-fsSL", "--retry", "3", "--retry-delay", "2", "-o", tmpPath.toString, target.url]
    stdin := .null
  }
  if out.exitCode != 0 then
    throw <| IO.userError s!"local gate: failed to download {target.url}: {out.stderr.trimAscii.toString}"
  else
    let tmpMeta ← tmpPath.symlinkMetadata
    if tmpMeta.type != .file then
      throw <| IO.userError s!"local gate: downloaded file is not a regular file: {tmpPath}"
    else
      let realTmp ← requireExactRealPath "downloaded file" tmpPath
      verifySha256 target realTmp
      IO.setAccessRights realTmp executableRight
      IO.FS.rename realTmp cachePath

def downloadNoComments (target : NoCommentsTarget) (cacheDir : System.FilePath) : IO System.FilePath := do
  let cachePath := cacheDir / target.asset
  let pid ← IO.Process.getPID
  let tmpPath := cacheDir / s!"{target.asset}.download.{pid}"
  match ← symlinkType? tmpPath with
  | some .file => IO.FS.removeFile tmpPath
  | some _ =>
    throw <| IO.userError s!"local gate: download staging path is not a regular file: {tmpPath}"
  | none => pure ()
  try
    stageNoComments target cachePath tmpPath
  finally
    match ← symlinkType? tmpPath with
    | some .file => IO.FS.removeFile tmpPath
    | _ => pure ()
  pure cachePath

def resolveCachedNoCommentsBin (target : NoCommentsTarget) : IO System.FilePath := do
  let cacheDir ← ensureNoCommentsCacheDir
  let cachePath := cacheDir / target.asset
  match ← symlinkType? cachePath with
  | some .file => requireExactRealPath "cache path" cachePath
  | some _ =>
    throw <| IO.userError s!"local gate: cache path is not a regular file: {cachePath}"
  | none =>
    downloadNoComments target cacheDir

def resolveNoCommentsBin (target : NoCommentsTarget) : IO System.FilePath := do
  match ← IO.getEnv "NO_COMMENTS_BIN" with
  | some raw =>
    if raw == "" then
      throw <| IO.userError "local gate: NO_COMMENTS_BIN is empty"
    else
      pure (System.FilePath.mk raw)
  | none =>
    resolveCachedNoCommentsBin target

def noCommentsRequest (bin : System.FilePath) : IO.Process.SpawnArgs where
  cmd := bin.toString
  args := noCommentsArgs.toArray
  cwd := some (System.FilePath.mk ".")
  stdin := .null
  env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none),
    ("LAKE_ARTIFACT_CACHE", some "false"), (fullVariable, none), (proofVariable, none)]

def announceNoComments : IO Unit := do
  IO.println s!"local gate: no-comments {" ".intercalate noCommentsArgs} (in .)"
  (← IO.getStdout).flush

def runNoCommentsStep (bin : System.FilePath) : IO UInt32 := do
  let child ← IO.Process.spawn (noCommentsRequest bin)
  child.wait

def runNoComments : IO UInt32 := do
  match hostNoCommentsTarget? with
  | none =>
    throw <| IO.userError s!"local gate: unsupported platform for no-comments {noCommentsVersion}: {System.Platform.target}"
  | some target =>
    let binPath ← resolveNoCommentsBin target
    let meta_ ← binPath.metadata
    if meta_.type == .file then
      let realBin ← IO.FS.realPath binPath
      announceNoComments
      verifySha256 target realBin
      runNoCommentsStep realBin
    else
      throw <| IO.userError s!"local gate: no-comments path is not a regular file: {binPath}"

structure Step where
  arguments : List String
  dir : String
  full : Option String
  deriving DecidableEq, Repr

def localSteps (checker root : String) : List Step :=
  [⟨["clean"], "specification", none⟩,
    ⟨["build", "lint"], checker, none⟩,
    ⟨["exe", "lint", "standard-logical"], checker, some root⟩,
    ⟨["build", "--wfail"], ".", none⟩,
    ⟨["build", "--wfail", "Regula", "lint"], ".", none⟩,
    ⟨["lint"], ".", none⟩,
    ⟨["build", "--wfail"], "specification", none⟩,
    ⟨["lint"], "specification", none⟩]

def runSteps {m : Type → Type} [Monad m] (run : Step → m UInt32) :
    List Step → m (Option (Step × UInt32))
  | [] => pure none
  | step :: rest => do
    let code ← run step
    if code == 0 then runSteps run rest else pure (some (step, code))

theorem runSteps_cons (code : Step → UInt32) (step : Step) (rest : List Step) :
    runSteps (m := Id) (fun s => pure (code s)) (step :: rest) =
      if code step == 0 then runSteps (m := Id) (fun s => pure (code s)) rest
      else some (step, code step) := by
  rfl

theorem runSteps_eq_none_iff (code : Step → UInt32) (steps : List Step) :
    runSteps (m := Id) (fun s => pure (code s)) steps = none ↔ ∀ s ∈ steps, code s = 0 := by
  induction steps with
  | nil => exact ⟨(fun _ _ m => nomatch m), fun _ => rfl⟩
  | cons step rest ih =>
    rw [runSteps_cons]
    by_cases h : code step = 0
    · simp [h, ih]
    · simp [h]

def exitOf : Option (Step × UInt32) → UInt32
  | some _ => 1
  | none => 0

theorem exitOf_eq_zero_iff (r : Option (Step × UInt32)) : exitOf r = 0 ↔ r = none := by
  cases r <;> simp [exitOf]

def announce (step : Step) : IO Unit := do
  IO.println s!"local gate: lake {" ".intercalate step.arguments} (in {step.dir}){(step.full.map (s!", on {·}")).getD ""}"
  (← IO.getStdout).flush

def runStep (step : Step) : IO UInt32 := do
  announce step
  let child ← IO.Process.spawn
    { cmd := "lake", args := step.arguments.toArray, cwd := some (System.FilePath.mk step.dir),
      stdin := .null,
      env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none),
        ("LAKE_ARTIFACT_CACHE", some "false"), (fullVariable, step.full), (proofVariable, none)] }
  child.wait

def regularFiles : List System.FilePath → IO (List System.FilePath)
  | [] => pure []
  | p :: rest => do
    let dir ← p.isDir
    let others ← regularFiles rest
    pure (if dir then others else p :: others)

def checkerFiles : IO (List System.FilePath) := do
  let sources ← System.FilePath.walkDir "lean"
  let files ← regularFiles sources.toList
  pure (["lakefile.toml", "lake-manifest.json", "lean-toolchain"].map System.FilePath.mk ++ files)

def copyFile (target file : System.FilePath) : IO Unit := do
  let to := target / file
  if let some dir := to.parent then IO.FS.createDirAll dir
  IO.FS.writeBinFile to (← IO.FS.readBinFile file)

def copyAll (target : System.FilePath) : List System.FilePath → IO Unit
  | [] => pure ()
  | file :: rest => do
    copyFile target file
    copyAll target rest

def copyChecker (target : System.FilePath) : IO Unit := do
  copyAll target (← checkerFiles)

def sayResult (steps : List Step) : Option (Step × UInt32) → IO Unit
  | some (step, code) =>
    IO.eprintln s!"local gate: lake {" ".intercalate step.arguments} (in {step.dir}) ended with \
      exit code {code}, so the local gate refuses the change"
  | none =>
    IO.println s!"local gate: each of its {steps.length} lake steps and no-comments ({noCommentsVersion}) ended with exit code 0"

def sayNoCommentsResult (steps : List Step) (ncCode : UInt32) : IO Unit :=
  if ncCode == 0 then
    sayResult steps none
  else
    IO.eprintln s!"local gate: no-comments {" ".intercalate noCommentsArgs} ended with \
      exit code {ncCode}, so the local gate refuses the change"

def runIn (target root : String) : IO UInt32 := do
  let steps := localSteps target root
  let result ← runSteps runStep steps
  match result with
  | some _ =>
    sayResult steps result
    return exitOf result
  | none =>
    let ncCode ← runNoComments
    sayNoCommentsResult steps ncCode
    return if ncCode == 0 then 0 else 1

def runLocal : IO UInt32 := do
  let target ← IO.FS.createTempDir
  try
    copyChecker target
    runIn target.toString (← IO.currentDir).toString
  finally
    IO.FS.removeDirAll target

end Regula.DiagnosticsGate

def main (args : List String) : IO UInt32 := do
  match args with
  | ["local"] => Regula.DiagnosticsGate.runLocal
  | _ =>
    IO.eprintln "usage: lean --run lean/Regula/DiagnosticsGate.lean local"
    return 2
