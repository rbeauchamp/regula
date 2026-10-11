import Regula.Contract
import Regula.Decision

/-! # Removal of a directory or a file at its own place

The decision by which the site executable (`Regula.Site`) removes a directory or a file. The
operation `Regula.Removal.removeOwn` observes the place and removes it only when this decision
decided to remove it.

`IO.FS.removeDirAll` reads the entries of the path it is given, also when that path is a symbolic
link to a directory, and then removes the entries of the link's target. A removal that first asks
`System.FilePath.pathExists` or `System.FilePath.isDir`, which follow a link, can therefore remove
the content of a directory outside the place it names. This decision takes an observation that
follows no link at the place (`Place`) and the comparison of the place's real path with the
place itself, and it removes only the kind of entry the caller removes, found at its own place
(`removal_remove_iff`).

The verification driver decides its own removals with `RegulaVerification.removal`, which it
cannot import from here: `scripts/verify.sh` runs it with `lean --run` before any module of the
package is built. `RegulaVerification.Decisions` proves that the driver's decision agrees with
this one for a directory.

**Outside this decision:** a process that replaces an entry below the directory with a link while
the removal runs, and a process that changes the place between the observation and the removal.
`IO.FS.removeDirAll` examines each entry and then opens it by its path, so such a process can make
it remove the entries of a different directory. -/

namespace Regula.Removal

/-- The kind of entry a caller removes. -/
inductive Kind where
  /-- A directory, which is removed with all its entries. -/
  | directory
  /-- A file. -/
  | file
  deriving DecidableEq, Repr

/-- What is at a path, observed without following a symbolic link at the path itself. -/
inductive Place where
  /-- Nothing is there. -/
  | absent
  /-- A directory or a regular file is there. -/
  | present (kind : Kind)
  /-- Something else is there: a symbolic link, or an entry that is neither a directory nor a
  regular file. -/
  | other
  deriving DecidableEq, Repr

/-- What was observed of a path before a removal of it. -/
structure Observed where
  /-- What is at the path. -/
  place : Place
  /-- Whether the real path of what is there is the path itself. -/
  sameLocation : Bool
  deriving DecidableEq, Repr

/-- What is done about an entry that is to be removed. -/
inductive Removal where
  /-- Nothing is there: there is nothing to remove. -/
  | nothing
  /-- An entry of the kind is there, at its own place: it is removed. -/
  | remove
  /-- Something else is there: nothing is removed, and the caller stops. -/
  | refuse
  deriving DecidableEq, Repr

/-- Remove only an entry of `kind` at its own place; there is nothing to remove when nothing is
there; refuse in every other case, which is each case with a symbolic link at the path, an
entry of the other kind, and a real path that is not the path. -/
@[regula_decision]
def removal (kind : Kind) (observed : Observed) : Removal :=
  match observed.place with
  | .absent => .nothing
  | .present found => if found = kind ∧ observed.sameLocation then .remove else .refuse
  | .other => .refuse

/-- The decision removes exactly when an entry of `kind` is at the path, by a read that follows
no link, and its real path is that path. -/
theorem removal_remove_iff (kind : Kind) (observed : Observed) :
    removal kind observed = .remove ↔
      observed.place = .present kind ∧ observed.sameLocation = true := by
  obtain ⟨place, sameLocation⟩ := observed
  cases place <;> cases sameLocation <;> simp [removal]

/-- The decision has nothing to remove exactly when nothing is at the path. -/
theorem removal_nothing_iff (kind : Kind) (observed : Observed) :
    removal kind observed = .nothing ↔ observed.place = .absent := by
  obtain ⟨place, sameLocation⟩ := observed
  cases place <;> cases sameLocation <;> simp [removal] <;> split <;> simp

/-- `removal` removes exactly an entry of the caller's kind at its own place
(`removal_remove_iff`). It removes a directory at its own place, and it does not remove a
directory when the caller removes a file. -/
theorem checked_removal : Regula.ExecutableContract removal (fun decide =>
    Regula.Decides (· = .remove)
      (fun input : Kind × Observed =>
        input.2.place = .present input.1 ∧ input.2.sameLocation = true)
      (Function.uncurry decide)) :=
  ⟨.of_iff (fun input => removal_remove_iff input.1 input.2)
    ⟨(.directory, ⟨.present .directory, true⟩), rfl⟩
    ⟨(.file, ⟨.present .directory, true⟩), by decide⟩⟩

end Regula.Removal
