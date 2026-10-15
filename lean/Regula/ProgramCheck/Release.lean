import Regula.Release
import Regula.Removal
import Regula.Filesystem

/-! # The removal and write check and the presence read of the release program

`lean --run lean/Regula/Release.lean` runs the release program before the package is built, so it
imports only Lean and does not run the check itself. This module imports it, and its build fails
when the compiled code of the program reaches a removal or a write outside the filesystem
observer and the places that `Regula.Removal.sharedPairs` lists or that it names here
(`Regula.Removal.checkProgram`).

It also proves the program's own presence read, which the program defines because it cannot import
`Regula.Filesystem`, equal to the filesystem observer's (`isPresent_eq`). -/

run_cmd Regula.Removal.checkProgram (named := [
  -- The notes and the edition of a release in `tmp/`, and the output and summary of the step,
  -- appended to the files that GitHub Actions names.
  (`Regula.Release.output, ``IO.FS.Handle.mk),
  (`Regula.Release.summarize, ``IO.FS.Handle.mk),
  (``Regula.Release.adopt, ``IO.FS.writeFile),
  (``Regula.Release.publish, ``IO.FS.createDirAll),
  (``Regula.Release.publish, ``IO.FS.writeFile)])

/-- The presence read of the program is the filesystem observer's (`Regula.Filesystem.isPresent`,
whose match form `Regula.Filesystem.isPresent_eq_match` states). -/
theorem Regula.ProgramCheck.Release.isPresent_eq :
    Regula.Release.isPresent = Regula.Filesystem.isPresent :=
  Regula.Filesystem.isPresent_eq_match.symm
