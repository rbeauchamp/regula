import AuditApp

/-!
# Audit application entry point

Standalone root module of the claimed `auditApp` executable: the honest
effectful boundary of the `AuditApp` dogfooding surface. `main` reads an
optional capacity argument, passes it through the admission boundary, runs
`AuditApp.demoScript` through the strict proved core, and describes the outcome
as an IO action: admission rejection returns 1; a refused grant retains the
successful prefix and returns 2; completion returns 0.

Every behavioral property this program relies on — admission soundness,
update post-conditions, and boundedness of the composed run — is stated and
proved in `AuditApp.Limiter` and `AuditApp.Demo` about the same computable
definitions executed here. `executeChecked` requires the `RequiredContracts` evidence
provided by `required_contracts`, keeping these explicit obligations load-bearing. The `IO`
boundary itself is trusted execution substrate: the axiom gate reports it in this surface's
execution coverage at the default `report` mode, and nothing in this module claims more. Counts are
rendered as tick strings (`String.ofList` over `List.replicate`) rather than
through `Nat.repr`, whose `Nat.reprFast` runtime replacement has no checked
correspondence: a `Nat.repr` call would appear in the report as a trusted
boundary, which `report` mode accepts and a `checked` claim rejects
(`execution-trusted-boundary`). This surface's report contains no such
boundary. The report separately records the runtime externs beneath the
shell (`IO`, `String`, `Char`, `Nat`/`UInt` primitives) and any reached imported
runtime replacements or partial computations. None of those implementations
is established by the pure core's contracts.
-/

/-- Describe the demo's output actions and exit code using the proved strict
core: failed admission returns 1, a refused grant returns 2 with its retained
state, and completion returns 0. Actual terminal effects and compiled runtime
behavior remain trusted boundaries. -/
def main (args : List String) : IO UInt32 := do
  let capacity := AuditApp.requestedCapacity args
  match AuditApp.checked_executable.run AuditApp.required_contracts capacity
      AuditApp.demoScript with
  | none =>
    IO.eprintln "capacity rejected: admission requires a positive capacity"
    return 1
  | some (result, final) =>
    let capacityTicks := String.ofList (List.replicate final.capacity '#')
    let inUseTicks := String.ofList (List.replicate final.inUse '|')
    match result with
    | .ok () =>
      IO.println s!"admitted capacity={capacityTicks}; completed: inUse={inUseTicks}"
      return 0
    | .error () =>
      IO.eprintln s!"grant refused; retained capacity={capacityTicks}; inUse={inUseTicks}"
      return 2
