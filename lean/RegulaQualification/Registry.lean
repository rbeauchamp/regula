import RegulaQualification.Checks
import Regula.Decision

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

/-- The root is a JSON object exactly when `isObject` accepts it. -/
theorem isObject_iff (report : Json) :
    isObject report = true ↔ ∃ members, report = .obj members := by
  cases report <;> simp [isObject]

/-- Lean's accessor reads the text `text` for `key` exactly when the report is an object whose
member `key` is that text. -/
theorem textMember_iff (report : Json) (key text : String) :
    (report.getObjValAs? String key).toOption = some text ↔
      ∃ members, report = .obj members ∧ members[key]? = some (.str text) := by
  cases report with
  | obj members =>
    cases found : members[key]? with
    | none =>
      simp [Json.getObjValAs?, Json.getObjValD, Json.getObjVal?, found, fromJson?, Json.getStr?,
        Except.toOption, throw, throwThe, MonadExceptOf.throw]
    | some value =>
      cases value <;>
        simp [Json.getObjValAs?, Json.getObjValD, Json.getObjVal?, found, fromJson?, Json.getStr?,
          Except.toOption, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  | _ =>
    simp [Json.getObjValAs?, Json.getObjValD, Json.getObjVal?, fromJson?, Json.getStr?,
      Except.toOption, throw, throwThe, MonadExceptOf.throw]

/-- `oldPresent` refuses the report exactly when the report, if it is an object, has no member
`old`. -/
theorem oldPresent_eq_false_iff (report : Json) :
    oldPresent report = false ↔ ∀ members, report = .obj members → members["old"]? = none := by
  unfold oldPresent
  cases report with
  | obj members =>
    cases found : members["old"]? with
    | none =>
      simp [Json.getObjVal?, found, Except.isOk, Except.toBool, throw, throwThe,
        MonadExceptOf.throw]
    | some value => simp [Json.getObjVal?, found, Except.isOk, Except.toBool, pure, Except.pure]
  | _ => simp [Json.getObjVal?, Except.isOk, Except.toBool, throw, throwThe, MonadExceptOf.throw]

/-- Independent statement of the required meaning; there are no defaults for a
missing status and no exception for a present-but-null stale marker. It is stated over the
members of the JSON object and has no accessor and no test of this module: the exit code is not
zero, the report is an object, its member `status` is the text `incomplete`, and it has no
member `old`. -/
def Invalidated (exitCode : Nat) (report : Json) : Prop :=
  exitCode ≠ 0 ∧ ∃ members, report = .obj members ∧
    members["status"]? = some (.str "incomplete") ∧ members["old"]? = none

/-- Run the same generic proof-backed evaluator consumed by the operational driver. -/
@[regula_decision]
def validate (exitCode : Nat) (report : Json) : Except String Unit :=
  checked_evaluation.run (checks exitCode report)

/-- For every exit code and JSON tree, validation succeeds exactly when the failed
invocation invalidated its output in the stated sense. Runtime/authenticity excluded. -/
theorem validate_exact (exitCode : Nat) (report : Json) :
    validate exitCode report = .ok () ↔ Invalidated exitCode report := by
  simp only [validate, Regula.ExecutableContract.run, evaluate_success, Satisfied, checks,
    Invalidated, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    bne_iff_ne, ne_eq, isObject_iff, beq_iff_eq, textMember_iff, Bool.not_eq_true',
    oldPresent_eq_false_iff]
  constructor
  · rintro ⟨nonzero, ⟨members, rfl⟩, ⟨members', same, status⟩, absent⟩
    cases same
    exact ⟨nonzero, members, rfl, status, absent members rfl⟩
  · rintro ⟨nonzero, members, rfl, status, absent⟩
    exact ⟨nonzero, ⟨members, rfl⟩, ⟨members, rfl, status⟩, fun members' same => by
      cases same
      exact absent⟩

/-- Closed executable contract: deleting the equivalence proof breaks this registration. It is a
two-way decision (`validate_exact`) that accepts a nonzero exit with a clean incomplete object
and refuses a zero exit. -/
theorem checked_validation : Regula.ExecutableContract validate (fun run =>
    Regula.Decides (· = .ok ()) (fun input : Nat × Json => Invalidated input.1 input.2)
      (Function.uncurry run)) :=
  ⟨.of_iff (fun input => validate_exact input.1 input.2)
    ⟨(2, Json.mkObj [("status", .str "incomplete")]), rfl⟩
    ⟨(0, .null), fun accepted => ((validate_exact 0 .null).mp accepted).1 rfl⟩⟩

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
