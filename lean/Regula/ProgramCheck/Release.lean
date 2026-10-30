import Regula.Release
import Regula.Filesystem

/-! # The presence read of the release program

The CI workflows run the release program with `lean --run`, so it imports only Lean and defines its
own presence read. This module proves that read the filesystem observer's (`isPresent_eq`). -/

/-- The presence read of the program is the filesystem observer's (`Regula.Filesystem.isPresent`,
whose match form `Regula.Filesystem.isPresent_eq_match` states). -/
theorem Regula.ProgramCheck.Release.isPresent_eq :
    Regula.Release.isPresent = Regula.Filesystem.isPresent :=
  Regula.Filesystem.isPresent_eq_match.symm
