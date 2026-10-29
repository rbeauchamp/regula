import Lake
open Lake DSL

-- The package of the standard's example library: the `Audit` modules that the standard's
-- `lean` blocks import, and the refinement of the `AuditApp` limiter. It imports only Lean's
-- core libraries and adopts the `regula` package by relative path, exactly as an adopting
-- project would, so it requires nothing else. The Mathlib-specific behaviour Regula supports
-- is checked by the separate package in `integration/mathlib/`.
package «regula_audit» where
  lintDriver := "regula/lint"
  -- Build warnings are failures, no automatic implicits (standard §7.1, RG2006) and every
  -- public definition has a docstring (standard §6.7, RG2006).
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩, ⟨`linter.missingDocs, true⟩]

@[default_target]
lean_lib «Audit» where
  -- The claimed surface is every module at or below `Audit`, not only the
  -- transitive imports of the umbrella module. Lake's elaborated module
  -- inventory is the semantic inventory consumed by the declaration gate.
  globs := #[.andSubmodules `Audit]

require regula from ".."
