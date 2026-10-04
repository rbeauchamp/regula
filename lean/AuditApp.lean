import AuditApp.Limiter
import AuditApp.Demo

/-!
# AuditApp surface umbrella

Umbrella for the complete-application `AuditApp` Lake surface. It imports
`AuditApp.Limiter` (the proof-bearing limiter core: admission, updates, and
fold-level composition contracts) and `AuditApp.Demo` (the fixed demonstration
script and its kernel-checked end state). This module owns no
declarations. The claimed surface is the library's Lake inventory
(`lake query AuditApp:modules`), which the declaration gate inspects whether or
not a module is imported here; the imports make that inventory the transitive
surface of the claimed `auditApp` executable, whose root module `Main` is
claimed alongside this library in `foundation_manifest.json`. The surface imports
only Lean's core libraries and the published checker interfaces; the limiter's
refinement to an abstract capacity model is `Audit.Refinement` in the `audit/`
package, which requires this package by relative path.
-/
