import RegulaQualification.Checks
import Regula.Filesystem

/-! # Support of the site's programs

The assertions, the process starts and the root directory that the site's builder, its renderer
controls and its deployment check share. Assertions go through the proved evaluator
(`RegulaQualification.checked_evaluation`); process execution and the filesystem are trusted IO.
-/

namespace Regula.Site

open System RegulaQualification

/-- Fail with the first unsatisfied assertion from the proved evaluator. -/
def requireChecks (checks : List Check) : IO Unit :=
  IO.ofExcept (checked_evaluation.run checks)

/-- Run `command` with `args` in `root` under the shared Git isolation of a process
(`Regula.Filesystem.Construction.gitProcessArgs`), and give its output. A status that says the
command did not run or was killed at a deadline (124 to 127, and 137) is an error. -/
def run (root : FilePath) (command : String) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  let result ← IO.Process.output (← Regula.Filesystem.Construction.gitProcessArgs
    { cmd := command, args, cwd := some root, env })
  if #[124, 125, 126, 127, 137].contains result.exitCode then
    throw <| IO.userError s!"process failed or timed out: {command} {args}\n\
      {result.stdout}{result.stderr}"
  return result

/-- The environment changes of a Lake command in the website package: the root package's search
paths removed, so the two workspaces never mix. -/
def cleanEnv : Array (String × Option String) := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none)]

/-- The root of the Regula checkout, which the site's programs run in: the real path of the
working directory, refused unless it has a `lean-toolchain` and a `lakefile.lean`. -/
def rootDirectory : IO FilePath := do
  let root ← IO.FS.realPath (← IO.currentDir)
  requireChecks [⟨"run the site's programs from the Regula package root",
    (← Regula.Filesystem.isPresent (root / "lean-toolchain")) &&
      (← Regula.Filesystem.isPresent (root / "lakefile.lean"))⟩]
  return root

end Regula.Site
