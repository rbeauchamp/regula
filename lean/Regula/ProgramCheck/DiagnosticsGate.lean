import Regula.DiagnosticsGate
import Regula.Removal
import Regula.Filesystem

/-! # The observer reach check and the presence read of the diagnostics gate

`lean --run lean/Regula/DiagnosticsGate.lean` runs the diagnostics gate before the package is
built, so it imports only the toolchain and does not run the check itself. This module imports it,
and its build fails when the compiled code of the program reaches a primitive that the check
refuses (`Regula.Removal.checkProgram`): a process start or an environment read other than the
bootstrap pairs of its process source (`Regula.Removal.bootstrap`), or a removal or a write outside
the filesystem observer and the places that `Regula.Removal.sharedPairs` lists or that it names
here.

It also proves the program's own presence read, which the program defines because it cannot import
`Regula.Filesystem`, equal to the filesystem observer's (`isPresent_eq`). -/

run_cmd Regula.Removal.checkProgram (bootstrap := `Regula.DiagnosticsGate.Process) (named := [
    -- The output of the step, appended to the file that GitHub Actions names.
    (Regula.Removal.privateIn `Regula.DiagnosticsGate
      `Regula.DiagnosticsGate.output, ``IO.FS.Handle.mk)])

/-- The presence read of the program is the filesystem observer's (`Regula.Filesystem.isPresent`,
whose match form `Regula.Filesystem.isPresent_eq_match` states). -/
theorem Regula.ProgramCheck.DiagnosticsGate.isPresent_eq :
    Regula.DiagnosticsGate.isPresent = Regula.Filesystem.isPresent :=
  Regula.Filesystem.isPresent_eq_match.symm
