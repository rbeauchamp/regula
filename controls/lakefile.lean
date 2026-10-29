import Lake
open Lake DSL

-- The package of the controls of the check that each program of the `regula` package runs
-- (`Regula.Removal.checkProgram`, `Regula.TaskManagerCheck.checkProgram`): planted programs that
-- the checks must refuse or accept. It requires `regula` by relative path. It is a package of its
-- own because Regula's checker loads each module of each target of the root package, and the
-- compile of these controls needs about 30 GiB (issue #497): the local gate builds it in a step of
-- its own, outside the 420-second acceptance step.
package «regula_controls» where
  -- Build warnings are failures, and no automatic implicits (standard §7.1).
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib «RegulaControls» where
  globs := #[.one `RegulaControls]

require regula from ".."
