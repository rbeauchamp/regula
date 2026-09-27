import RegulaQualification.Checks

/-! Pure decoder/evaluator composition. Mandatory JSON accesses use the pinned Lean
APIs in each protocol module; missing or malformed observations refuse before the
assertions are evaluated. No defaults stand in for unavailable evidence. -/
namespace RegulaQualification

/-- Convert decoded assertions into the same checked decision. A decoding failure is
always refusal; successful decoding is admitted exactly when all assertions hold. -/
def validateDecoded (decoded : Except String (List Check)) : Except String Unit :=
  decoded.bind checked_evaluation.run

/-- Exact decoder/evaluator composition, including rejection and successful admission.
The decoder's own definition specifies the required fields and their meaning. -/
theorem validateDecoded_exact (decoded : Except String (List Check)) :
    validateDecoded decoded = .ok () ↔
      ∃ checks, decoded = .ok checks ∧ Satisfied checks := by
  cases decoded with
  | error error => simp [validateDecoded, Except.bind]
  | ok checks => simp [validateDecoded, Except.bind, Regula.ExecutableContract.run, evaluate_success]

/-- Registered contract used by report adapters, not an IO authenticity assertion. -/
theorem checked_decoded : Regula.ExecutableContract validateDecoded
    (fun run => ∀ decoded, run decoded = .ok () ↔
      ∃ checks, decoded = .ok checks ∧ Satisfied checks) := ⟨validateDecoded_exact⟩

end RegulaQualification
