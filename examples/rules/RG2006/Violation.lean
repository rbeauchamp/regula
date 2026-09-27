import Lake
open Lake DSL

package rule_examples where
  leanOptions := #[⟨`linter.missingDocs, true⟩]

@[default_target]
lean_lib Example
