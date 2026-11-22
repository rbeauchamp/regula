module

public section

namespace Regula.DiagnosticsGate

def fullVariable : String := "REGULA_FULL"

def noCommentsVersion : String := "v0.2.0"

def noCommentsArgs : List String := ["check", "--bootstrap"]

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
  else if System.Platform.isLinux && System.Platform.target.startsWith "x86_64-" then
    some .linuxX86_64
  else
    none

def noCommentsCacheDir : System.FilePath :=
  System.FilePath.mk ".cache" / "no-comments" / noCommentsVersion

def executableRight : IO.FileRight where
  user := { read := true, write := true, execution := true }
  group := { read := true, execution := true }
  other := { read := true, execution := true }

def isLowerHexChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

def parseSha256Line (cs : List Char) : Option String :=
  let digest := cs.take 64
  let sep := (cs.drop 64).take 2
  if digest.length == 64 && digest.all isLowerHexChar && (sep == [' ', ' '] || sep == [' ', '*']) then
    some (String.ofList digest)
  else
    none

def parseSha256Output (stdout : String) : Option String :=
  parseSha256Line ((stdout.splitOn "\n").headD "").toList

def sha256Request (path : System.FilePath) : IO.Process.SpawnArgs where
  cmd := if System.Platform.isOSX then "shasum" else "sha256sum"
  args := if System.Platform.isOSX then #["-a", "256", "--", path.toString] else #["--", path.toString]
  stdin := .null

def sha256Matches (expected : String) (out : IO.Process.Output) : Bool :=
  out.exitCode == 0 && parseSha256Output out.stdout == some expected

def verifySha256 (path : System.FilePath) (expected : String) : IO Unit := do
  let out ← IO.Process.output (sha256Request path)
  if sha256Matches expected out then
    pure ()
  else
    throw <| IO.userError s!"local gate: SHA-256 verification failed for {path} (expected {expected})"

def downloadNoComments (target : NoCommentsTarget) (cachePath : System.FilePath) : IO Unit := do
  if let some dir := cachePath.parent then
    IO.FS.createDirAll dir
  let pid ← IO.Process.getPID
  let tmpPath := System.FilePath.mk s!"{cachePath.toString}.download.{pid}"
  if (← tmpPath.pathExists) then
    IO.FS.removeFile tmpPath
  try
    IO.println s!"local gate: downloading {target.asset} ({noCommentsVersion})"
    (← IO.getStdout).flush
    let out ← IO.Process.output {
      cmd := "curl"
      args := #["-fsSL", "--retry", "3", "--retry-delay", "2", "-o", tmpPath.toString, target.url]
      stdin := .null
    }
    if out.exitCode != 0 then
      throw <| IO.userError s!"local gate: failed to download {target.url}: {out.stderr.trimAscii.toString}"
    verifySha256 tmpPath target.sha256
    IO.setAccessRights tmpPath executableRight
    IO.FS.rename tmpPath cachePath
  finally
    if (← tmpPath.pathExists) then
      IO.FS.removeFile tmpPath

def resolveNoCommentsBin (target : NoCommentsTarget) : IO System.FilePath := do
  match ← IO.getEnv "NO_COMMENTS_BIN" with
  | some raw =>
    if raw != "" then
      let p := System.FilePath.mk raw
      unless (← p.pathExists) do
        throw <| IO.userError s!"local gate: NO_COMMENTS_BIN does not exist: {raw}"
      return p
  | none => pure ()
  let cachePath := noCommentsCacheDir / target.asset
  if (← cachePath.pathExists) then
    let realCache ← IO.FS.realPath cachePath
    let meta_ ← realCache.metadata
    if meta_.type == .dir then
      throw <| IO.userError s!"local gate: cache path is a directory: {cachePath}"
    if meta_.type == .file then
      let out ← IO.Process.output (sha256Request realCache)
      if sha256Matches target.sha256 out then
        IO.setAccessRights realCache executableRight
        return realCache
    IO.eprintln s!"local gate: cached {cachePath} failed SHA-256 verification; re-downloading"
    IO.FS.removeFile cachePath
  downloadNoComments target cachePath
  return cachePath

def noCommentsRequest (bin : System.FilePath) : IO.Process.SpawnArgs where
  cmd := bin.toString
  args := noCommentsArgs.toArray
  cwd := some (System.FilePath.mk ".")
  stdin := .null
  env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none),
    ("LAKE_ARTIFACT_CACHE", some "false"), (fullVariable, none)]

def announceNoComments : IO Unit := do
  IO.println s!"local gate: no-comments {" ".intercalate noCommentsArgs} (in .)"
  (← IO.getStdout).flush

def runNoCommentsStep (bin : System.FilePath) : IO UInt32 := do
  announceNoComments
  let child ← IO.Process.spawn (noCommentsRequest bin)
  child.wait

def runNoComments : IO UInt32 := do
  match hostNoCommentsTarget? with
  | none =>
    throw <| IO.userError s!"local gate: unsupported platform for no-comments {noCommentsVersion}: {System.Platform.target}"
  | some target =>
    let binPath ← resolveNoCommentsBin target
    let realBin ← IO.FS.realPath binPath
    let meta_ ← realBin.metadata
    if meta_.type == .file then
      verifySha256 realBin target.sha256
      runNoCommentsStep realBin
    else
      throw <| IO.userError s!"local gate: no-comments path is not a regular file: {realBin}"

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
        ("LAKE_ARTIFACT_CACHE", some "false"), (fullVariable, step.full)] }
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
