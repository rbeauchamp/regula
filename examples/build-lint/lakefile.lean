import Lake
open Lake DSL

package build_lint_adopter where
  -- `lake lint` runs Regula's checker over the finished build of every manifested surface.
  lintDriver := "regula/lint"
  -- The community linters of standard §6.7 and the options of §7.1. A library that
  -- imports Mathlib also enables Mathlib's standard set, as the adoption guide shows.
  leanOptions := #[⟨`linter.missingDocs, true⟩, ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

require regula from "../.."

@[default_target]
lean_lib Widget where
  globs := #[.andSubmodules `Widget]
