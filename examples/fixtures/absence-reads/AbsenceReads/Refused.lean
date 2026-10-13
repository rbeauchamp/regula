/-! # Reads of absence that the self-audit refuses

A control input, outside every library of the package, so that no audited module names Lean's two
readers that take a path which cannot be read for an absent one (issue 430). The self-audit's
absence rule must refuse `legacyPresent`, which calls `System.FilePath.pathExists`, and
`legacyDirectory`, which is `System.FilePath.isDir` itself, without an argument, and nothing else
here (`Regula.Qualification.SelfAudit.absenceFixtureFindings`). `Regula.AbsenceControls` runs
`main` with `lean --run` on a path that cannot be read, which prints what the two give for it. -/

namespace AbsenceReads

/-- Lean's read of whether an entry is at `path`. -/
def legacyPresent (path : System.FilePath) : BaseIO Bool :=
  path.pathExists

/-- Lean's read of whether a directory is at a path, named without an argument. -/
def legacyDirectory : System.FilePath → BaseIO Bool :=
  System.FilePath.isDir

end AbsenceReads

/-- Print what `legacyPresent` and `legacyDirectory` give for the path that is the one argument,
separated by a space. -/
def main : List String → IO UInt32
  | [path] => do
    IO.println s!"{← AbsenceReads.legacyPresent path} {← AbsenceReads.legacyDirectory path}"
    return 0
  | _ => do
    IO.eprintln "usage: lean --run Refused.lean PATH"
    return 2
