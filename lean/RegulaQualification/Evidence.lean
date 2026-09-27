import RegulaQualification.Json

/-! # Source-bound evidence contracts

Supplied-data contracts for source-bound qualification. Required fields decode
strictly. The oracles establish exact exit, diagnostic, status and transcript predicates;
they do not establish that an OS process or filesystem supplied authentic observations. -/
namespace RegulaQualification.Evidence
open Lean

/-- Required JSON field; unavailable evidence refuses rather than defaulting. -/
def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
/-- Required text field. -/
def text (j : Json) (key : String) : Except String String := j.getObjValAs? _ key
/-- Required array field. -/
def array (j : Json) (key : String) : Except String (Array Json) := j.getObjValAs? _ key
/-- Required nested object text. -/
def detail (j : Json) : Except String String := do text (← field j "arguments") "detail"
/-- Diagnostic IDs in their actual order, retaining duplicates. -/
def ids (j : Json) : Except String (List String) := do
  (← array j "diagnostics").toList.mapM (text · "id")

/-- Fixed expectation, selected before the public command runs. -/
structure Expected where
  failure : Bool := false
  mode : Option String := none
  status : String := "completed"
  ids : List String := []
  reason : String := ""
  grouped : Bool := false
  positiveText : String := "PASS"
  impact : Option String := none
  diagnosticMode : Option String := none
  evidenceSubject : Option String := none

/-- Exact observable requirements shared by fence and failed-operation controls.
A missing result is permitted only for the standalone text-only documentation command. -/
def requirements (expected : Expected) (code : Nat) (transcript : String)
    (result : Option Json) : Except String (List Check) := do
  let mut checks := [
    Check.mk "exit agrees with expected refusal" ((code != 0) == expected.failure),
    ⟨"intended transcript reason", transcript.contains expected.reason⟩,
    ⟨"inspection group retained", !expected.grouped || transcript.contains "inspection group 1/1: 1 fence(s)"⟩,
    ⟨"positive transcript", expected.failure || transcript.contains expected.positiveText⟩,
    ⟨"all expected transcript diagnostics", expected.ids.all (fun id => transcript.contains id)⟩,
    ⟨"no invented evidence refusal", expected.ids.contains "RG2005" || !(transcript.contains "RG2005")⟩]
  if let some result := result then
    checks := checks ++ [
      ⟨"exact diagnostic sequence", (← ids result) == expected.ids⟩,
      ⟨"exact terminal status", (← text result "status") == expected.status⟩]
    if let some mode := expected.mode then
      checks := checks ++ [⟨"exact invocation mode", (← text result "mode") == mode⟩]
    for diagnostic in ← array result "diagnostics" do
      if let some impact := expected.impact then
        checks := checks ++ [⟨"diagnostic impact", (← text diagnostic "impact") == impact⟩]
      if let some mode := expected.diagnosticMode then
        checks := checks ++ [⟨"diagnostic mode", (← text diagnostic "mode") == mode⟩]
      if (← text diagnostic "id") == "RG2005" then
        checks := checks ++ [
          ⟨"typed evidence reason", (← detail diagnostic).contains expected.reason⟩,
          ⟨"evidence project location", (← text (← field diagnostic "location") "kind") == "project"⟩]
        if let some subject := expected.evidenceSubject then
          checks := checks ++ [⟨"evidence subject", (← text (← field diagnostic "arguments") "subject") == subject⟩]
  return checks

/-- This is the actual supplied-observation oracle used by the IO adapter. -/
def validate (expected : Expected) (code : Nat) (transcript : String) (result : Option Json) : Except String Unit :=
  checked_decoded.run (requirements expected code transcript result)

/-- Successful admission iff decoding succeeds and every specified requirement holds;
this also rules out an always-refusing replacement. -/
theorem checked_validation : Regula.ExecutableContract validate
    (fun run => ∀ expected code transcript result, run expected code transcript result = .ok () ↔
      ∃ checks, requirements expected code transcript result = .ok checks ∧ Satisfied checks) :=
  ⟨fun _ _ _ _ => validateDecoded_exact _⟩

/-- Original documentation mutation transcript requirements, including two distinct
admission diagnostics (fence and project), and exactly one compilation diagnostic. -/
def documentationChecks (transcript scope reason phase : String) : List Check :=
  let lines := transcript.splitOn "\n"
  let admission := lines.filter (·.startsWith "RG2005 [")
  let unavailable := ["source-missing", "source-unreadable", "configuration-unreadable"].contains phase
  [⟨"snapshot refusal", transcript.contains reason⟩,
   ⟨"fence compilation evidence", transcript.contains "fence compilation: "⟩,
   ⟨"two distinct admission diagnostics", admission.length == 2 && admission.eraseDups.length == 2⟩,
   ⟨"one fence admission diagnostic", (admission.filter (·.contains "project/configuration control.md:1]")).length == 1⟩,
   ⟨"one project admission diagnostic", (admission.filter (·.contains s!"project/configuration {scope}]")).length == 1⟩,
   ⟨"one fence compilation diagnostic", (lines.filter (·.startsWith "RG4002 [")).length == 1⟩,
   ⟨"IO failure detail", !unavailable || transcript.toLower.contains
     (if phase == "source-missing" then "no such file or directory" else "is a directory")⟩,
   ⟨"IO failure path", !unavailable || transcript.contains
     (if phase == "configuration-unreadable" then "foundation_manifest.json" else "Example.lean")⟩]

/-- Reusable exact contract for the source-mutation transcript predicates. -/
def validateDocumentation (transcript scope reason phase : String) : Except String Unit :=
  checked_evaluation.run (documentationChecks transcript scope reason phase)

/-- Transcript success and refusal are governed by all requirements, not an exit alone. -/
theorem checked_documentation : Regula.ExecutableContract validateDocumentation
    (fun run => ∀ transcript scope reason phase,
      run transcript scope reason phase = .ok () ↔ Satisfied (documentationChecks transcript scope reason phase)) :=
  ⟨fun _ _ _ _ => evaluate_success _⟩
end RegulaQualification.Evidence
