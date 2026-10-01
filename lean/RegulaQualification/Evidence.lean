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
  /-- Whether the command must exit with a nonzero code. -/
  failure : Bool := false
  /-- When set, the result's exact `mode`. -/
  mode : Option String := none
  /-- The result's exact terminal `status`. -/
  status : String := "completed"
  /-- The exact sequence of diagnostic IDs in the result; each must also occur in the
  transcript. -/
  ids : List String := []
  /-- Text the transcript must contain; for an RG2005 diagnostic, also its detail. -/
  reason : String := ""
  /-- Whether the transcript must report a single inspection group of one fence. -/
  grouped : Bool := false
  /-- Text a successful transcript must contain. -/
  positiveText : String := "PASS"
  /-- When set, the `impact` every diagnostic must have. -/
  impact : Option String := none
  /-- When set, the `mode` every diagnostic must have. -/
  diagnosticMode : Option String := none
  /-- When set, the `subject` argument every RG2005 diagnostic must have. -/
  evidenceSubject : Option String := none

/-- Exact observable requirements shared by fence and failed-operation controls.
A missing result is permitted only for the standalone text-only documentation command. -/
def requirements (expected : Expected) (code : Nat) (transcript : String)
    (result : Option Json) : Except String (List Check) := do
  let mut checks := [
    Check.mk "exit agrees with expected refusal" ((code != 0) == expected.failure),
    ⟨"intended transcript reason", transcript.contains expected.reason⟩,
    ⟨"inspection group retained", !expected.grouped ||
        transcript.contains "inspection group 1/1: 1 fence(s)"⟩,
    ⟨"positive transcript", expected.failure || transcript.contains expected.positiveText⟩,
    ⟨"all expected transcript diagnostics", expected.ids.all (fun id => transcript.contains id)⟩,
    ⟨"no invented evidence refusal", expected.ids.contains "RG2005" ||
        !(transcript.contains "RG2005")⟩]
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
          ⟨"evidence project location", (← text (← field diagnostic "location") "kind") ==
              "project"⟩]
        if let some subject := expected.evidenceSubject then
          checks := checks ++
              [⟨"evidence subject", (← text (← field diagnostic "arguments") "subject") == subject⟩]
  return checks

/-- This is the actual supplied-observation oracle used by the IO adapter. -/
def validate (expected : Expected) (code : Nat) (transcript : String) (result : Option Json) :
    Except String Unit :=
  checked_decoded.run (requirements expected code transcript result)

/-- Successful admission iff decoding succeeds and every specified requirement holds;
this also rules out an always-refusing replacement. -/
theorem checked_validation : Regula.ExecutableContract validate
    (fun run => ∀ expected code transcript result, run expected code transcript result = .ok () ↔
      ∃ checks, requirements expected code transcript result = .ok checks ∧ Satisfied checks) :=
  ⟨fun _ _ _ _ => validateDecoded_exact _⟩

/-- Original documentation mutation transcript requirements, including two distinct
admission diagnostics (fence and project), and exactly one compilation diagnostic. For a phase
that makes an input unavailable, the transcript must also contain the supplied IO reason, which
must be nonempty (`missing` for a removed source, otherwise `directory`), and the input's file
name. The caller supplies the reasons the runtime reports for reads that fail those two ways (an
absent file, a directory in a file's place), of other paths than the checker's; that the reasons
do not depend on the path is trusted runtime behavior, and these checks do not relate the
supplied strings to any read. -/
def documentationChecks (transcript scope reason phase missing directory : String) :
    List Check :=
  let lines := transcript.splitOn "\n"
  let admission := lines.filter (·.startsWith "RG2005 [")
  let unavailable :=
      ["source-missing", "source-unreadable", "configuration-unreadable"].contains phase
  let io := if phase == "source-missing" then missing else directory
  [⟨"snapshot refusal", transcript.contains reason⟩,
   ⟨"fence compilation evidence", transcript.contains "fence compilation: "⟩,
   ⟨"two distinct admission diagnostics", admission.length == 2 && admission.eraseDups.length == 2⟩,
   ⟨"one fence admission diagnostic",
       (admission.filter (·.contains "project/configuration control.md:1]")).length == 1⟩,
   ⟨"one project admission diagnostic",
       (admission.filter (·.contains s!"project/configuration {scope}]")).length == 1⟩,
   ⟨"one fence compilation diagnostic", (lines.filter (·.startsWith "RG4002 [")).length == 1⟩,
   ⟨"IO failure detail", !unavailable || (!io.isEmpty && transcript.contains io)⟩,
   ⟨"IO failure path", !unavailable || transcript.contains
     (if phase == "configuration-unreadable" then "foundation_manifest.json" else "Example.lean")⟩]

/-- Reusable exact contract for the source-mutation transcript predicates. -/
def validateDocumentation (transcript scope reason phase missing directory : String) :
    Except String Unit :=
  checked_evaluation.run (documentationChecks transcript scope reason phase missing directory)

/-- Transcript success and refusal are governed by all requirements, not an exit alone. -/
theorem checked_documentation : Regula.ExecutableContract validateDocumentation
    (fun run => ∀ transcript scope reason phase missing directory,
      run transcript scope reason phase missing directory = .ok () ↔ Satisfied
          (documentationChecks transcript scope reason phase missing directory)) :=
  ⟨fun _ _ _ _ _ _ => evaluate_success _⟩
end RegulaQualification.Evidence
