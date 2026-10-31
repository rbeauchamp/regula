import Lake
open Lake DSL

package rule_examples where
  leanOptions := #[⟨`linter.missingDocs, true⟩, ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

require unavailable from "./missing"

@[default_target]
lean_lib Example
