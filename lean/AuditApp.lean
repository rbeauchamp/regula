import AuditApp.Limiter
import AuditApp.Demo
import AuditApp.Refinement

/-!
# AuditApp surface umbrella

Umbrella for the complete-application `AuditApp` Lake surface. It imports
`AuditApp.Limiter` (the proof-bearing limiter core: admission, updates, and
fold-level composition contracts), `AuditApp.Demo` (the fixed demonstration
script and its kernel-checked end state), and `AuditApp.Refinement` (the
abstract capacity specification, the forward simulation from the executable
dispatcher, and finite-prefix safety transfer). This module owns no
declarations. The claimed surface is the library's Lake inventory
(`lake query AuditApp:modules`), which the declaration gate inspects whether or
not a module is imported here; the imports make that inventory the transitive
surface of the claimed `auditApp` executable, whose root module `Main` is
claimed alongside this library in `foundation_manifest.json`.
-/
