import RegulaQualification.Checks
import Regula.Scratch
import Lean

/-! Operational qualification support. Pure assertions go through `checkedEvaluation`.
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
  IO.ofExcept (checkedEvaluation.run checks)

/-- Select and authenticate the existing GNU timeout dependency. -/
def timeoutCommand : IO String := do
  for command in #["gtimeout", "timeout"] do
    try
      let result ← IO.Process.output { cmd := command, args := #["--version"] }
      if result.exitCode == 0 && result.stdout.contains "GNU coreutils" then return command
    catch _ => pure ()
  throw <| IO.userError "qualification requires GNU coreutils timeout"

/-- Run within the public entrypoint's timed process group. Do not detach a nested
process group: the enclosing deadline must kill descendants holding output pipes too. -/
def run (root : FilePath) (command : String) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  let result ← IO.Process.output { cmd := command, args, cwd := some root, env }
  if #[124, 125, 126, 127, 137].contains result.exitCode then
    throw <| IO.userError s!"qualification process failed/timed out: {command} {args}\n{result.stdout}{result.stderr}"
  return result

/-- One group-wide deadline for a standalone public entrypoint. This is only used at
the outer boundary, never for commands already under acceptance. SIGKILL terminates
the timer, child, and descendants in its group, closing inherited output handles. -/
def runBounded (root : FilePath) (seconds : Nat) (command : String) (args : Array String) : IO UInt32 := do
  let timer ← timeoutCommand
  let child ← IO.Process.spawn {
    cmd := timer, args := #["--signal=KILL", s!"{seconds}s", command] ++ args,
    cwd := some root, stdin := .null, stdout := .inherit, stderr := .inherit }
  child.wait

/-- Witness that `withScratchCleaned` removed its owned scratch directory after the
action returned normally. Only this module can construct it, so a value exists only
after that removal returned without error. It says nothing about processes the
action did not join, and a killed process never obtains one. -/
structure Cleaned where
  private mk ::
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
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

/-- Pretty JSON is an output format, not a claim of byte-canonical serialization. -/
def writeJson (path : FilePath) (value : Json) : IO Unit :=
  IO.FS.writeFile path (value.pretty ++ "\n")

/-- Root-relative entrypoints must be run in the package root, never inferred from
source-file text or another checkout's executable location. -/
def rootDirectory : IO FilePath := do
  let root ← IO.FS.realPath (← IO.currentDir)
  requireChecks [⟨"run qualification from the Regula package root",
    (← (root / "lean-toolchain").pathExists) && (← (root / "lakefile.lean").pathExists)⟩]
  return root

end Regula.Qualification
