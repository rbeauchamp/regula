import Lake
open Lake DSL

package rule_examples

@[default_target]
lean_lib Example where
  plugins := #[`@regula/RegulaObserver:shared]
  needs := #[`@regula/RegulaObserver:shared]
