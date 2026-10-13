import Lake
open Lake DSL

package rule_examples where
  leanOptions := #[⟨`linter.missingDocs, true⟩, ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]
  plugins := #[`@regula/RegulaObserver:shared]

@[default_target]
lean_lib Example
