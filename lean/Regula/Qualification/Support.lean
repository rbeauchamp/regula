import Regula.Checker.Common
import Regula.Process
import RegulaQualification.Checks
import Regula.Scratch
import Regula.SharedExecution
import Regula.Checker.ResultProtocol
import Lean

/-! # Operational qualification support

Operational qualification support. Pure assertions go through `checked_evaluation`.
Filesystem observations, process execution, GNU timeout, and cleanup are trusted IO;
none is advertised as a kernel theorem about the operating system. Commands use argv,
not shell programs. Public entrypoints own one group-wide deadline. Under acceptance,
all commands inherit `scripts/verify.sh`'s process group; no inner timer detaches them. -/

namespace Regula.Qualification
open Lean System RegulaQualification

/-- Operational attempt identity, carried unchanged across the deadline wrapper. -/
def freshAttempt : IO String := do
  return (← IO.getRandomBytes 16).foldl (fun s b => s ++ s!"{b.toNat}-") ""

/-- Fail with the first unsatisfied assertion from the proved evaluator. -/
def requireChecks (checks : List Check) : IO Unit :=
  IO.ofExcept (checked_evaluation.run checks)

/-- Select and authenticate the existing GNU timeout dependency. -/
def timeoutCommand : IO String := do
  for command in #["gtimeout", "timeout"] do
    try
      let result ← Regula.Process.output (.stated command "Select and authenticate the external GNU timeout utility")
        { cmd := "", args := #["--version"] }
      if result.exitCode == 0 && result.stdout.contains "GNU coreutils" then return command
    catch _ => pure ()
  throw <| IO.userError "qualification requires GNU coreutils timeout"

/-- Run within the public entrypoint's timed process group. Do not detach a nested
process group: the enclosing deadline must kill descendants holding output pipes too. -/
def run (root : FilePath) (command : Regula.Process.Program) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  let options ← Regula.Filesystem.Construction.gitProcessArgs
    { cmd := command.statedCommand.getD "", args, cwd := some root, env }
  let result ← Regula.Process.output command options
  if #[124, 125, 126, 127, 137].contains result.exitCode then
    throw <|
        IO.userError s!"qualification process failed/timed \
          out: {command} {args}\n{result.stdout}{result.stderr}"
  return result

/-- One group-wide deadline for a standalone public entrypoint. This is only used at
the outer boundary, never for commands already under acceptance. SIGKILL terminates
the timer, child, and descendants in its group, closing inherited output handles. -/
def runBounded (root : FilePath) (seconds : Nat) (command : Regula.Process.Program) (args : Array String) :
    IO UInt32 := do
  let timer ← timeoutCommand
  let options ← Regula.Filesystem.Construction.gitProcessArgs
    {cmd := command.statedCommand.getD "", args}
  let selected ← Regula.Process.prepare command
    {options with cwd := some root, stdin := .null, stdout := .inherit, stderr := .inherit}
  let child ← Regula.Process.spawn (.stated timer "The authenticated GNU timeout owns this diagnostic\'s deadline") {
    cmd := "", args := #["--signal=KILL", s!"{seconds}s", selected.emit.cmd] ++ selected.emit.args,
    env := selected.env,
    cwd := some root, stdin := .null, stdout := .inherit, stderr := .inherit }
  child.wait

/-- Witness that `withScratchCleaned` removed its owned scratch directory after the
action returned normally. Only this module can construct it, so a value exists only
after that removal returned without error. It says nothing about processes the
action did not join, and a killed process never obtains one. -/
structure Cleaned where
  private mk ::
  /-- The scratch directory that was removed. -/
  path : FilePath

/-- Fresh scratch under the worktree, with cleanup on normal or exceptional return; orphans
of dead runs are reclaimed (`Regula.Scratch`). On normal return it also yields the cleanup
witness, constructed only after the finalizer's removal returned. Random naming and OS
directory operations are not logical freshness proofs. -/
def withScratchCleaned {α : Type} (root : FilePath) (stem : String) (action : FilePath → IO α) :
    IO (α × Cleaned) := do
  let (value, path) ← Regula.Scratch.withScratch root stem action
  return (value, ⟨path⟩)

/-- Fresh scratch under the worktree, with cleanup on normal or exceptional return. -/
def withScratch {α : Type} (root : FilePath) (stem : String) (action : FilePath → IO α) : IO α :=
  return (← withScratchCleaned root stem action).1

/-- Parse using the pinned Lean JSON implementation; malformed output is an error. -/
def readJson (path : FilePath) : IO Json := do
  Regula.Checker.requireAuditDocument (← IO.ofExcept (Json.parse (← IO.FS.readFile path)))

/-- Read a result file (`--json-out`) as a logical result document
(`Regula.Checker.ResultProtocol.readDocument`: parsed with `Regula.Checker.PolicyCodec.parse` and
admitted with `Regula.Checker.ResultProtocol.admitDocument`), so each `sourceText` member holds its
text and each `execution` member its roots' accounts. For the text a result writer wrote for a
document, the parse is the value the writer wrote and admission returns the writer's document
(`Regula.Checker.ResultProtocol.admitDocument_parse_encodeDocument`). A file that is not a written
result document is an error. -/
def readResult (path : FilePath) : IO Json :=
  Regula.Checker.ResultProtocol.readDocument path

/-- The first line of the runtime's own message for a failed read of `path`: the `IO.Error` text
before its `file:` line. A control compares a checker's IO refusal with this, the wording of the
toolchain and platform it runs on, instead of a copied operating-system message. The control
passes a path whose read fails the same way as the checker's (an absent file, or a directory in
a file's place), not the path the checker read; that the first line does not depend on the path
is trusted runtime behavior, not established here. A readable `path` or an empty first line
refuses. -/
def readFailure (path : FilePath) : IO String := do
  match ← (IO.FS.readFile path).toBaseIO with
  | .ok _ => throw <| IO.userError s!"control requires an unreadable path: {path}"
  | .error error =>
      let line := ((toString error).splitOn "\n").headD ""
      requireChecks [⟨"runtime read failure has a reason", !line.isEmpty⟩]
      return line

/-- Pretty JSON is an output format, not a claim of byte-canonical serialization. -/
def writeJson (path : FilePath) (value : Json) : IO Unit :=
  IO.FS.writeFile path (value.pretty ++ "\n")

/-- Root-relative entrypoints must be run in the package root, never inferred from
source-file text or another checkout's executable location. -/
def rootDirectory : IO FilePath := do
  let root ← IO.FS.realPath (← Regula.Process.currentDir)
  requireChecks [⟨"run qualification from the Regula package root",
    (← (root / "lean-toolchain").pathExists) && (← (root / "lakefile.lean").pathExists)⟩]
  return root

end Regula.Qualification
