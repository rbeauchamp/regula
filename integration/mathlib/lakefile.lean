import Lake
open Lake DSL

-- The Mathlib integration package: a Mathlib adopter of the `regula` package, required by
-- relative path exactly as a Mathlib project would. Its `MathlibAudit` library holds the
-- Mathlib-specific behaviour Regula supports (Mathlib's community-linter configuration,
-- foundation labels through Mathlib dependencies, Mathlib syntax and tactics). Nothing else
-- in this repository requires it: `./scripts/verify.sh mathlib` checks it, after
-- `lean --run lean/RegulaProvision.lean mathlib` has provisioned its pinned Mathlib into this
-- package's own `.lake/packages`.
package «regula_mathlib» where
  lintDriver := "regula/lint"
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
lean_lib «MathlibAudit» where
  -- The claimed surface is every module at or below `MathlibAudit`, not only the
  -- transitive imports of the umbrella module. Lake's elaborated module
  -- inventory is the semantic inventory consumed by the declaration gate.
  globs := #[.andSubmodules `MathlibAudit]
  leanOptions := mathlibLinters

require regula from "../.."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "5ed2965256430c3649e86755f9576b54eca72435"
