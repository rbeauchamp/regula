import Lake
open Lake DSL

package rule_examples where
  plugins := #[`@regula/RegulaObserver:shared]

@[default_target]
lean_lib Example
