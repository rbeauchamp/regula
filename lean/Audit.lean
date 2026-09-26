import Audit.DocPrelude
import Audit.Basic
import Audit.DocClaims
import Audit.Economy
import Audit.Research
import Audit.Server

/-!
Umbrella for the complete positive `Audit` Lake surface. It imports
`Audit.DocPrelude` (shared types and abstraction API), `Audit.Basic` (arithmetic
and subtype controls), `Audit.DocClaims` (the decay and discrete-time models
the standard's examples import), `Audit.Economy` (cost-domain and lawful-mixin
examples and a proof-bearing closed-form sum), `Audit.Research` (an open `Prop` target with
conditional results and a bounded-search reduction), and `Audit.Server`
(proof-bearing admission and finite-prefix service state). This module owns no
declarations; its formal result is the exact transitive import surface checked by
`lake build` and `leanchecker --fresh Audit`. The declaration gate and fresh checker
discover the `Audit` surface from Lake's inventory, not from this import list.
-/
