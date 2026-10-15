import Regula.Qualification.Support

/-! # Diagnostic receipt boundary qualification

Execute the public diagnostic boundary with stale completed evidence and actual
timeout discovery/spawn failures. These are operational observations, not OS proofs. Each started
program finds Git through a `PATH` that holds only a link to the Git of this process (`pathGit`).
When that Git is outside the cases that `pathGit` models, or when the guard's query of Git fails
under that `PATH` (`probeGuard`), the controls stop as unsupported, which is neither a pass nor a
failure of the program under test. -/
namespace Regula.Qualification.ReceiptBoundary
open Lean System

/-- Test-only timeout substitute: discovery succeeds, then the selected executable
disappears before spawn. No production timeout selection hook is needed. -/
def worker (args : List String) : IO UInt32 := do
  requireChecks [⟨"timeout version probe", args == ["--version"]⟩]
  Regula.Filesystem.removePath .file (← IO.appPath)
  IO.println "GNU coreutils qualification substitute"
  return 0

/-- Stop the receipt-boundary controls as unsupported for `reason`: the Git that a started program
runs is outside the cases that `pathGit` models. The controls then neither pass nor report a
failure of the program under test. -/
private def unsupported {α : Type} (reason : String) : IO α :=
  throw <| IO.userError s!"receipt boundaries: UNSUPPORTED, not PASS, and no failure of the \
    program under test: {reason}"

/-- The Git that a program started as `git` with the search path `path` (the value of `PATH`) runs,
as an absolute path: `<entry>/git` for the first entry of `path`, split at each `:`, that holds a regular file named `git`, which must run with
`--version` and exit 0. Each case outside that rule is reported as unsupported (`unsupported`).

Assumes: Lean v4.34.1 starts a child with `execvp` (`src/runtime/process.cpp:510`), and the
search is the libc's. This function models only these cases of it. With `PATH` set and nonempty,
the search tries `<entry>/git` for each entry in order. An entry whose `git` is absent (`ENOENT`)
is skipped: macOS 27 `exec(3)` (DESCRIPTION, the paragraph on ambiguous errors: a stat that finds
no file continues the search) and glibc 2.39 `posix/execvpe.c:145-170`. The first regular file
named `git` that runs is the one executed. Reported as unsupported: an unset `PATH`, whose default
differs (macOS `/usr/bin:/bin`, glibc `CS_PATH` at `posix/execvpe.c:92-94`); an empty `PATH`; an
empty or relative entry, which the search reads from the working directory
(`posix/execvpe.c:117-134`); and a `git` that cannot be read, is not a regular file, cannot be
executed or exits with another code, whose handling differs between the two libraries and by
error. -/
private def pathGit (path : Option String) : IO FilePath := do
  let path ← match path with
    | some path => if path.isEmpty then unsupported "PATH is empty" else pure path
    | none => unsupported "PATH is unset"
  for entry in path.splitOn ":" do
    let directory := FilePath.mk entry
    unless directory.isAbsolute do
      unsupported s!"the PATH entry '{entry}' is empty or relative"
    let candidate := directory / "git"
    match ← candidate.metadata.toBaseIO with
    | .error (.noFileOrDirectory ..) => continue
    | .error error => unsupported s!"{candidate} cannot be read: {error}"
    | .ok metadata =>
      unless metadata.type == .file do unsupported s!"{candidate} is not a regular file"
      let out ← IO.Process.output {
        cmd := candidate.toString, args := #["--version"], stdin := .null }
      unless out.exitCode == 0 do
        unsupported s!"{candidate} --version exited {out.exitCode}: {out.stderr}"
      return candidate
  unsupported s!"no entry of PATH holds a file named git: {path}"

/-- Make `bin/git` a link to `git`, so a program started with `bin` as its only `PATH` entry runs
that Git, which its guard runs (`Regula.GitIsolation.enter`), and nothing else of the directory
that holds Git, such as a GNU timeout. -/
private def linkGit (git bin : FilePath) : IO Unit := do
  let linked ← IO.Process.output {
    cmd := "ln", args := #["-s", git.toString, (bin / "git").toString], stdin := .null }
  unless linked.exitCode == 0 do
    throw <| IO.userError s!"could not link {git} into {bin}: {linked.stderr}"

/-- The value of `REGULA_QUALIFICATION_WRAPPER` with which `probeGuard` starts `qualify`: a mode that
`qualify` does not know, so its guard runs and then the program refuses the mode, with no command
and no file written (`Regula.Qualification.Main`). -/
private def probeMode : String := "receipt-boundary-git-probe"

/-- Start `executable`, this `qualify`, with `bin` as its only `PATH` entry, as each control starts
it, and report the controls as unsupported (`unsupported`) when the guard's own query of Git
(`Regula.Filesystem.Construction.isolationEnvironment`) is unavailable there. A Git that runs with
`--version` under the search path of this process can still fail under `bin`, for example a
wrapper that starts a program found on that search path. The guard runs before the program, which
then refuses the unknown mode `probeMode`. -/
private def probeGuard (executable bin : FilePath) : IO Unit := do
  let out ← IO.Process.output {
    cmd := executable.toString,
    env := #[("PATH", some bin.toString), ("REGULA_QUALIFICATION_WRAPPER", some probeMode),
      ("REGULA_RECEIPT_TIMER", none)],
    stdin := .null }
  if out.stderr.contains "unknown qualification wrapper mode" then return
  if out.stderr.contains "Git isolation is unavailable" then
    unsupported s!"the guard's query of Git fails with {bin} as the only PATH entry: {out.stderr}"
  throw <| IO.userError s!"receipt boundaries: the probe of the guard's query of Git exited \
    {out.exitCode}: {out.stdout}{out.stderr}"

/-- Link the Git of the search path `path` (`pathGit`) into `bin` (`linkGit`), and require the
guard's query of Git to run with `bin` as the only `PATH` entry (`probeGuard`). -/
private def prepareGit (executable : FilePath) (path : Option String) (bin : FilePath) :
    IO Unit := do
  linkGit (← pathGit path) bin
  probeGuard executable bin

/-- Preserve existing completed evidence only until the next public invocation starts. First, a
Git stand-in that runs with `--version` and fails the guard's query, a link to `/usr/bin/true`, is
reported unsupported (`probeGuard`).

Assumes: `/usr/bin/true` exits with 0 and prints no line for arguments other than `--help` and
`--version` alone, as POSIX true(1) and GNU coreutils `true` do, so the guard reads an empty list
of Git's names, which it refuses (`Regula.Filesystem.Construction.gitLocalNames`). -/
def check : IO Unit := do
  let root ← rootDirectory
  let executable ← IO.appPath
  let path ← IO.getEnv "PATH"
  withScratch root "receipt-boundary" fun scratch => do
    let standIn := scratch / "stand-in"
    IO.FS.createDir standIn
    linkGit (FilePath.mk "/usr/bin/true") standIn
    let standInBin := scratch / "stand-in-bin"
    IO.FS.createDir standInBin
    match ← (prepareGit executable (some standIn.toString) standInBin).toBaseIO with
    | .ok _ => throw <| IO.userError "receipt boundaries: a Git stand-in that fails the guard's \
        query was accepted"
    | .error error =>
      requireChecks [⟨s!"a Git stand-in that fails the guard's query is unsupported: {error}",
        (toString error).contains "UNSUPPORTED" &&
          (toString error).contains "the guard's query of Git fails"⟩]
    IO.println "receipt boundary Git stand-in: UNSUPPORTED as intended"
    for route in #[#["acceptance", "fences"], #["environments"]] do
      let evidence := scratch / "evidence.json"
      for fault in #["missing", "unusable", "spawn"] do
        let bin := scratch / s!"{route[0]!}-{fault}"
        IO.FS.createDir bin
        -- The started program's guard runs Git before the command (`Regula.TaskManager.guard`).
        prepareGit executable path bin
        if fault == "unusable" then
          IO.FS.writeFile (bin / "gtimeout") "not an executable\n"
        if fault == "spawn" then
          -- This native timeout stand-in is executed by path in the process-boundary control.
          Regula.Filesystem.copyFile executable (bin / "gtimeout") 493
        -- Completed evidence of an earlier attempt, with the members of a receipt and of a
        -- census, which the run may replace (`Regula.Destination.regulaDocument`).
        writeJson evidence (Json.mkObj [("status", toJson "completed"),
          ("attemptId", toJson "old"), ("schemaVersion", toJson (1 : Nat)),
          ("group", toJson "fences"), ("inputs", Json.mkObj []),
          ("records", toJson (#[] : Array Json)), ("packets", toJson (#[] : Array Json)),
          ("controls", toJson (#[] : Array Json))])
        let result ← IO.Process.output {
          cmd := executable.toString, args := route ++ #["--evidence", evidence.toString],
          env := #[("PATH", some bin.toString),
            ("REGULA_QUALIFICATION_WRAPPER", none),
            ("REGULA_RECEIPT_TIMER", if fault == "spawn" then some "1" else none)] }
        let current ← readJson evidence
        let status ← IO.ofExcept (current.getObjValAs? String "status")
        let attempt ← IO.ofExcept (current.getObjValAs? String "attemptId")
        let log := result.stdout ++ result.stderr
        requireChecks [⟨"failure really occurred", result.exitCode != 0⟩,
          ⟨"old completion invalidated", status == "incomplete" && attempt != "old" &&
              !attempt.isEmpty⟩,
          ⟨"intended timeout discovery refusal", fault == "spawn" ||
              log.contains "requires GNU coreutils timeout"⟩,
          ⟨"selected timer disappeared before spawn", fault != "spawn" ||
            (!(← Regula.Filesystem.isPresent (bin / "gtimeout")) &&
              !log.contains "requires GNU coreutils timeout")⟩]
        IO.println s!"receipt boundary {route[0]!}/{fault}: PASS"
end Regula.Qualification.ReceiptBoundary
