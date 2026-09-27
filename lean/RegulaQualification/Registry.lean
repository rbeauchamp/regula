import RegulaQualification.Checks

/-! # Malformed registry CLI observation contract

Exact observation contract for malformed registry CLI invocations: nonzero exit,
a JSON object explicitly marked incomplete, and removal of the seeded `old` key.
JSON parsing and field access mean Lean's pinned `Json` APIs. No theorem asserts that
a process ran or that the supplied object came from the requested output file. -/

namespace RegulaQualification.Registry
open Lean

/-- Check the root shape separately: an array's missing field is not invalidation. -/
def isObject : Json → Bool
  | .obj _ => true
  | _ => false

/-- Recognize actual field membership, including an old key whose value is null. -/
def oldPresent (report : Json) : Bool := (report.getObjVal? "old").isOk

/-- The exact three requirements plus the object-shape guard used by the CLI driver. -/
def checks (exitCode : Nat) (report : Json) : List Check := [
  ⟨"configuration failure must exit nonzero", exitCode != 0⟩,
  ⟨"output must be a JSON object", isObject report⟩,
  ⟨"current output must explicitly be incomplete",
    (report.getObjValAs? String "status").toOption == some "incomplete"⟩,
  ⟨"seeded stale output must be removed", !oldPresent report⟩]

/-- Independent statement of the required meaning; there are no defaults for a
missing status and no exception for a present-but-null stale marker. -/
def Invalidated (exitCode : Nat) (report : Json) : Prop :=
  exitCode ≠ 0 ∧ isObject report = true ∧
    (report.getObjValAs? String "status").toOption = some "incomplete" ∧ oldPresent report = false

/-- Run the same generic proof-backed evaluator consumed by the operational driver. -/
def validate (exitCode : Nat) (report : Json) : Except String Unit :=
  checked_evaluation.run (checks exitCode report)

/-- For every exit code and JSON tree, validation succeeds exactly when the failed
invocation invalidated its output in the stated sense. Runtime/authenticity excluded. -/
theorem validate_exact (exitCode : Nat) (report : Json) :
    validate exitCode report = .ok () ↔ Invalidated exitCode report := by
  simp [validate, Regula.ExecutableContract.run, evaluate_success, Satisfied,
    checks, Invalidated]

/-- Closed executable contract: deleting the equivalence proof breaks this registration. -/
theorem checked_validation : Regula.ExecutableContract validate
    (fun run => ∀ code report, run code report = .ok () ↔ Invalidated code report) :=
  ⟨validate_exact⟩

/-- Non-vacuity: a nonzero exit and a clean incomplete object can pass. -/
theorem positive_control :
    validate 2 (Json.mkObj [("status", .str "incomplete")]) = .ok () := rfl

/-- A stale marker is rejected even if the new status is otherwise correct. -/
theorem stale_control :
    validate 2 (Json.mkObj [("status", .str "incomplete"), ("old", .null)]) =
      .error "seeded stale output must be removed" := rfl

/-- A successful process cannot qualify a configuration failure. -/
theorem zero_control (report : Json) :
    validate 0 report = .error "configuration failure must exit nonzero" := rfl

end RegulaQualification.Registry
