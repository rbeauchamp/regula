module

public import Regula.Rule

/-!
# RG1004: native proofs

A constant of a claimed module depends on a native proof's axiom or on an axiom by which the kernel
trusts the compiler. `specification/RegulaSpecification/Rules/RG1004.lean` states the rule and proves
this check against it.
-/

public section

namespace Regula.Rules.RG1004

open Regula.Closed

/-- The constants of claimed modules that depend on a native proof's axiom or on an axiom by which the
kernel trusts the compiler. -/
def check {i : Input} (t : Tables i) : List Violation :=
  t.claimed.filterMap fun d =>
    let compiler := (t.axiomSet d.name).filter fun a =>
      nativeProofAxiom a || compilerAxioms.contains a
    if !compiler.isEmpty then
      some (violation d s!"depends on the native-proof axioms {compiler}")
    else none

/-- RG1004, for the registry. Its body is exposed so that the registry reads its spelling (`Regula.Closed.spellings_nodup`). -/
@[expose] def rule : Rule := { spelling := "RG1004", check := check }

end Regula.Rules.RG1004
