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
  -- transitive imports of the umbrella module. Lake's module inventory
  -- is the inventory that Regula's checker reads.
  globs := #[.andSubmodules `MathlibAudit]
  leanOptions := mathlibLinters
  -- Mathlib v4.35.0 sets `requiresModuleSystem`, so Lake v4.35.0 warns when a file without a
  -- `module` header imports it (`Lake/Build/Module.lean:416-424`). These files cannot be modules:
  -- `MathlibAudit.Refinement` imports the root package's `AuditApp.Limiter`, which is not one, and
  -- a `module` file cannot import a file that is not. So the library declares that it mixes the
  -- two, Lake's own opt-out (`Lake/Config/LeanConfig.lean:282-299`).
  allowNonModules := true

require regula from "../.."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"
