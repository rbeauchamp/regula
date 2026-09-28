import Lake
open Lake DSL

-- The Mathlib-dependent package of this repository: the standard's Mathlib examples (the
-- `Audit` library that its `lean` blocks import) and the Mathlib-based refinement of the
-- `AuditApp` limiter. It adopts the `regula` package by relative path, exactly as a Mathlib
-- project would, so requiring `regula` alone adds no Mathlib. It shares the root's packages
-- directory with the website package (`scripts/provision.sh` links the shared Mathlib there).
package «regula_audit» where
  lintDriver := "regula/lint"
  packagesDir := "../.lake/packages"
  -- Build warnings are failures, no automatic implicits (standard §7.1, RG2006) and every
  -- public definition has a docstring (standard §6.7, RG2006).
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩, ⟨`linter.missingDocs, true⟩]

/-- Mathlib's standard linter set without its three Mathlib-repository linters (standard §6.7),
for the claimed targets whose surfaces import Mathlib; RG2006 checks it. -/
def mathlibLinters : Array LeanOption := #[⟨`weak.linter.mathlibStandardSet, true⟩,
  ⟨`weak.linter.style.header, false⟩, ⟨`weak.linter.hashCommand, false⟩,
  ⟨`weak.linter.style.longFile, .ofNat 0⟩]

@[default_target]
lean_lib «Audit» where
  -- The claimed surface is every module at or below `Audit`, not only the
  -- transitive imports of the umbrella module. Lake's elaborated module
  -- inventory is the semantic inventory consumed by the declaration gate.
  globs := #[.andSubmodules `Audit]
  leanOptions := mathlibLinters

require regula from ".."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "5ed2965256430c3649e86755f9576b54eca72435"
