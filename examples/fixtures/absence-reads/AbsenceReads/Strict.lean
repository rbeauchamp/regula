/-! # A read of absence that the self-audit accepts

The positive control of the self-audit's absence rule: `strictPresent` reads
`System.FilePath.metadata` and gives absence only for `noFileOrDirectory`, as
`Regula.Filesystem.isPresent` does, and names neither of Lean's two readers, so the rule refuses
nothing here (`Regula.Qualification.SelfAudit.absenceFixtureFindings`). -/

namespace AbsenceReads

/-- Whether an entry is at `path`: `false` only when the read fails with `noFileOrDirectory`, and
the read's error for every other error. -/
def strictPresent (path : System.FilePath) : IO Bool := do
  match ← path.metadata.toBaseIO with
  | .ok _ => return true
  | .error (.noFileOrDirectory ..) => return false
  | .error error => throw error

end AbsenceReads
