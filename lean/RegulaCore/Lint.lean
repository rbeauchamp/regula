import RegulaCore.Account

/-! # Audit result classification

The recorded result of one audit invocation and every exit class, count and status derived
from it. An audit keeps at most one `Observation`, a later record replacing an earlier one: an
accepted run's account, a classified file inspection, or the rule and impact of each finding of a
run that did not accept. Its result status (`Observation.status`), the summary counts it prints
(`Observation.tally`) and the exit code `axiomGate` returns (`Observation.exitCode`, through
`gateExitCode`) are functions of that one value: each count is the number of findings of its own
impact (`tally_eq`), so a violation count never includes an incomplete finding, and a run with an
incomplete finding never exits as a violation (`exitCode_incomplete`). `completed` carries an accepted account
(`Account.Status.completed_accepted`).

The `lint` driver reads the observation back with the audit's exit code and classifies it
(`classify`): exit 0 requires an accepted run of the requested project mode
(`accepted_sound`), and for the audit's own recorded result the driver reports the exit code the
audit returned (`classify_gateExitCode`). The observation's authenticity, that it is this
invocation's audit rather than another's, is the driver's binding, checked by inspection. -/

namespace Regula.Checker.Lint

open RegulaPolicy
open Regula.Checker.Account (Status)

/-- Exit classes. Only `accepted` is success; the others distinguish an established
violation, invalid configuration or invocation, and incomplete evidence. -/
inductive Outcome where
  /-- The audit completed and accepted the requested mode. -/
  | accepted
  /-- The audit rejected the project with at least one finding that is not configuration. -/
  | violation
  /-- The audit rejected the project and every finding is configuration (RG2002); the driver
  also returns it for an invalid invocation. -/
  | configuration
  /-- Anything else: no recorded status, an exit code that disagrees with the recorded status,
  or a completed run of another mode. -/
  | incomplete
  deriving DecidableEq, Repr

/-- The driver's process exit code: 0 accepted, 1 violation, 2 invalid configuration, 3
incomplete. -/
def Outcome.exitCode : Outcome → UInt32
  | .accepted => 0 | .violation => 1 | .configuration => 2 | .incomplete => 3

/-- The upper-case class name the driver prints. -/
def Outcome.label : Outcome → String
  | .accepted => "ACCEPTED" | .violation => "VIOLATION"
  | .configuration => "INVALID CONFIGURATION" | .incomplete => "INCOMPLETE"

/-- Distinct classes have distinct exit codes. -/
theorem Outcome.exitCode_injective {a b : Outcome} (h : a.exitCode = b.exitCode) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [Outcome.exitCode] at h)

/-- A run's findings counted by impact: the counts its summary line prints. -/
structure Tally where
  /-- Findings that establish a violation. -/
  violations : Nat
  /-- Findings that leave the run incomplete. -/
  incomplete : Nat
  deriving DecidableEq, Repr

/-- The tally of findings with these impacts, one count per impact. -/
def tally : List Impact → Tally
  | [] => ⟨0, 0⟩
  | .violation :: rest => ⟨(tally rest).violations + 1, (tally rest).incomplete⟩
  | .incomplete :: rest => ⟨(tally rest).violations, (tally rest).incomplete + 1⟩

/-- Each count is the number of findings of its impact. -/
theorem tally_eq (impacts : List Impact) :
    tally impacts = ⟨(impacts.filter (· == .violation)).length,
      (impacts.filter (· == .incomplete)).length⟩ := by
  induction impacts with
  | nil => rfl
  | cons i rest ih =>
    cases i <;> simp only [tally, ih, List.filter_cons] <;> rfl

/-- Every finding is counted exactly once. -/
theorem tally_total (impacts : List Impact) :
    (tally impacts).violations + (tally impacts).incomplete = impacts.length := by
  induction impacts with
  | nil => rfl
  | cons i rest ih => cases i <;> simp only [tally, List.length_cons] <;> omega

/-- No finding is counted as incomplete exactly when none is incomplete. -/
theorem tally_incomplete_eq_zero (impacts : List Impact) :
    (tally impacts).incomplete = 0 ↔ .incomplete ∉ impacts := by
  induction impacts with
  | nil => simp [tally]
  | cons i rest ih => cases i <;> simp [tally, ih]

/-- Some finding is counted as a violation exactly when one is a violation. -/
theorem tally_violations_pos (impacts : List Impact) :
    0 < (tally impacts).violations ↔ .violation ∈ impacts := by
  induction impacts with
  | nil => simp [tally]
  | cons i rest ih => cases i <;> simp [tally, ih]

/-- The summary counts: `N violation(s), M incomplete finding(s)`. -/
def Tally.text (t : Tally) : String :=
  s!"{t.violations} violation(s), {t.incomplete} incomplete finding(s)"

/-- The recorded result of one audit invocation. An accepted run carries its report account;
a classified run (a file inspection without a conforming claim) found nothing and conforms to
no claim; any other run carries the rule and impact of each finding it reported, in report
order, and whether it also left evidence unresolved that no finding reports (`unresolved`). -/
inductive Observation where
  /-- The run was accepted; `account` is its report account. -/
  | accepted (account : Account)
  /-- The run found nothing, but classifies rather than conforms. -/
  | classified
  /-- The run did not accept: its findings' rules and impacts, and whether evidence was left
  unresolved without a finding. -/
  | refused (findings : List (RuleId × Impact)) (unresolved : Bool)

namespace Observation

/-- The rule and impact of each finding the run reported; accepted and classified runs report
none. -/
def findings : Observation → List (RuleId × Impact)
  | .refused findings _ => findings
  | _ => []

/-- The run's findings counted by impact. -/
def tally (o : Observation) : Tally := Lint.tally (o.findings.map (·.2))

/-- The run reported at least one finding, and every one is a configuration (RG2002)
rejection. -/
def configurationOnly (o : Observation) : Bool :=
  !o.findings.isEmpty && o.findings.all (·.1 == .configuration)

/-- The result status. A run that did not accept is `rejected` exactly when it reported a
violation, no incomplete finding and nothing unresolved, and `incomplete` otherwise
(`status_rejected_iff`). -/
def status : Observation → Status
  | .accepted account => .completed account
  | .classified => .classified
  | o@(.refused _ unresolved) =>
      if unresolved = false ∧ o.tally.incomplete = 0 ∧ 0 < o.tally.violations then .rejected
      else .incomplete

/-- A refused run is rejected or incomplete. -/
theorem status_refused (findings : List (RuleId × Impact)) (unresolved : Bool) :
    (refused findings unresolved).status = .rejected ∨
      (refused findings unresolved).status = .incomplete := by
  simp only [status]
  split <;> simp

/-- The status reads `completed` exactly for an accepted run, with its own account. -/
theorem status_completed_iff (o : Observation) (a : Account) :
    o.status = .completed a ↔ o = .accepted a := by
  cases o with
  | accepted b => simp [status]
  | classified => simp [status]
  | refused fs u => rcases status_refused fs u with h | h <;> simp [h]

/-- A refused run is rejected exactly when it left nothing unresolved and its findings include
a violation and no incomplete finding. -/
theorem status_rejected_iff (o : Observation) :
    o.status = .rejected ↔ (∃ fs, o = .refused fs false) ∧ o.tally.incomplete = 0 ∧
      0 < o.tally.violations := by
  cases o with
  | accepted a => simp [status]
  | classified => simp [status]
  | refused fs u =>
    simp only [status]
    split <;> rename_i h <;> cases u <;> simp_all

/-- The exit code of the run's own result, which `axiomGate` returns: 0 accepted or
classified, 1 violation, 2 invalid configuration (every finding RG2002), 3 incomplete. -/
def exitCode (o : Observation) : UInt32 :=
  match o.status with
  | .completed _ | .classified => 0
  | .rejected => if o.configurationOnly then 2 else 1
  | .incomplete => 3

/-- Exit 0 exactly for an accepted or classified run. -/
theorem exitCode_eq_zero_iff (o : Observation) :
    o.exitCode = 0 ↔ (∃ a, o = .accepted a) ∨ o = .classified := by
  cases o with
  | accepted a => simp [exitCode, status]
  | classified => simp [exitCode, status]
  | refused fs u =>
    rcases status_refused fs u with h | h
    · cases hc : (refused fs u).configurationOnly <;> simp [exitCode, h, hc]
    · simp [exitCode, h]

/-- Exit 1 exactly for a rejection with a finding that is not configuration: a violation, no
incomplete finding and nothing unresolved (`status_rejected_iff`). -/
theorem exitCode_eq_one_iff (o : Observation) :
    o.exitCode = 1 ↔ o.status = .rejected ∧ o.configurationOnly = false := by
  cases o with
  | accepted a => simp [exitCode, status]
  | classified => simp [exitCode, status]
  | refused fs u =>
    rcases status_refused fs u with h | h
    · cases hc : (refused fs u).configurationOnly <;> simp [exitCode, h, hc]
    · simp [exitCode, h]

/-- Exit 2 exactly for a rejection whose every finding is configuration. -/
theorem exitCode_eq_two_iff (o : Observation) :
    o.exitCode = 2 ↔ o.status = .rejected ∧ o.configurationOnly = true := by
  cases o with
  | accepted a => simp [exitCode, status]
  | classified => simp [exitCode, status]
  | refused fs u =>
    rcases status_refused fs u with h | h
    · cases hc : (refused fs u).configurationOnly <;> simp [exitCode, h, hc]
    · simp [exitCode, h]

/-- Exit 3 exactly when the status is incomplete. -/
theorem exitCode_eq_three_iff (o : Observation) :
    o.exitCode = 3 ↔ o.status = .incomplete := by
  cases o with
  | accepted a => simp [exitCode, status]
  | classified => simp [exitCode, status]
  | refused fs u =>
    rcases status_refused fs u with h | h
    · cases hc : (refused fs u).configurationOnly <;> simp [exitCode, h, hc]
    · simp [exitCode, h]

/-- An incomplete finding makes the run incomplete, whatever violations it also reported. -/
theorem exitCode_incomplete (o : Observation) (h : 0 < o.tally.incomplete) : o.exitCode = 3 := by
  rw [exitCode_eq_three_iff]
  cases o with
  | accepted a => simp [tally, findings, Lint.tally] at h
  | classified => simp [tally, findings, Lint.tally] at h
  | refused fs u =>
    simp only [status]
    split
    · rename_i hr
      exact absurd hr.2.1 (Nat.pos_iff_ne_zero.mp h)
    · rfl

/-- A violation exit reports at least one violation and no incomplete finding. -/
theorem exitCode_violation (o : Observation) (h : o.exitCode = 1) :
    0 < o.tally.violations ∧ o.tally.incomplete = 0 := by
  have := (status_rejected_iff o).mp ((exitCode_eq_one_iff o).mp h).1
  exact ⟨this.2.2, this.2.1⟩

end Observation

/-- `axiomGate`'s exit code for an invocation whose audit body returned `code` after recording
`observed`: the recorded result's exit code (`Observation.exitCode`), except that a run that
recorded no result, or recorded a success its body did not complete (`code ≠ 0`), is
incomplete. -/
def gateExitCode (code : UInt32) : Option Observation → UInt32
  | some o => if code ≠ 0 ∧ o.exitCode = 0 then Outcome.incomplete.exitCode else o.exitCode
  | none => Outcome.incomplete.exitCode

/-- When the body completed every success it recorded, the invocation exits with the recorded
result's own exit code. -/
theorem gateExitCode_some (code : UInt32) (o : Observation) (h : o.exitCode = 0 → code = 0) :
    gateExitCode code (some o) = o.exitCode := by
  simp only [gateExitCode]
  split
  · rename_i hc
    exact absurd (h hc.2) hc.1
  · rfl

/-- The invocation exits 0 only when its body completed and it recorded an accepted or
classified result. -/
theorem gateExitCode_eq_zero (code : UInt32) (observed : Option Observation)
    (h : gateExitCode code observed = 0) :
    code = 0 ∧ ∃ o, observed = some o ∧ ((∃ a, o = .accepted a) ∨ o = .classified) := by
  cases observed with
  | none => simp [gateExitCode, Outcome.exitCode] at h
  | some o =>
    simp only [gateExitCode] at h
    split at h
    · simp [Outcome.exitCode] at h
    · rename_i hc
      refine ⟨?_, o, rfl, (Observation.exitCode_eq_zero_iff o).mp h⟩
      by_cases hcode : code = 0
      · exact hcode
      · exact absurd ⟨hcode, h⟩ hc

/-- Required meaning of the classification, for every requested mode, audit exit code and
recorded observation. Accepted exactly when the audit exited zero and recorded `completed`
with an account of the requested mode; violation or configuration exactly when it exited
nonzero after recording a rejection with non-configuration or only configuration findings.
Every other combination, including no recorded status, a zero exit without `completed`, a
nonzero exit after `completed`, a classified file inspection and a completed account of another
mode, is incomplete. -/
def ClassifyContract (classify : EvidenceMode → UInt32 → Option Observation → Outcome) : Prop :=
  ∀ mode code observed,
    (classify mode code observed = .accepted ↔
      code = 0 ∧ ∃ a, observed = some (.accepted a) ∧ a.val.mode = mode) ∧
    (classify mode code observed = .violation ↔ code ≠ 0 ∧ ∃ o, observed = some o ∧
      o.status = .rejected ∧ o.configurationOnly = false) ∧
    (classify mode code observed = .configuration ↔ code ≠ 0 ∧ ∃ o, observed = some o ∧
      o.status = .rejected ∧ o.configurationOnly = true)

private def classifyImpl (mode : EvidenceMode) (code : UInt32) : Option Observation → Outcome
  | none => .incomplete
  | some o =>
      match o.status with
      | .completed a => if code = 0 ∧ a.val.mode = mode then .accepted else .incomplete
      | .rejected =>
          if code = 0 then .incomplete else if o.configurationOnly then .configuration
          else .violation
      | _ => .incomplete

/-- Registers `ClassifyContract` about the executed classification; callers use `classify`. -/
theorem checked_classify : Regula.ExecutableContract classifyImpl ClassifyContract :=
  ⟨fun mode code observed => by
    rcases observed with _ | o
    · simp [classifyImpl]
    · cases o with
      | accepted a =>
        by_cases hc : code = 0 <;> by_cases hm : a.val.mode = mode <;>
          simp [classifyImpl, Observation.status, hc, hm]
      | classified => simp [classifyImpl, Observation.status]
      | refused fs u =>
        rcases Observation.status_refused fs u with h | h <;> by_cases hc : code = 0 <;>
          cases hco : (Observation.refused fs u).configurationOnly <;>
          simp [classifyImpl, h, hc, hco]⟩

/-- The exit class, through `checked_classify`. -/
def classify (mode : EvidenceMode) (code : UInt32) (observed : Option Observation) : Outcome :=
  checked_classify.run mode code observed

/-- Exit code zero requires a zero audit exit and an accepted run of the requested mode: a
run complete for its plan that meets every stage policy (`RegulaPolicy.accept_iff`). -/
theorem accepted_sound (mode : EvidenceMode) (code : UInt32) (observed : Option Observation)
    (h : (classify mode code observed).exitCode = 0) :
    code = 0 ∧ ∃ c, ∃ run : AcceptedRun c, c.val.mode = mode ∧
      CompleteFor run.plan run.result.table ∧ AllPolicyOK run.plan run.roles run.result.table := by
  have accepted : classify mode code observed = .accepted :=
    Outcome.exitCode_injective (b := .accepted) h
  obtain ⟨hcode, a, _, hmode⟩ := ((checked_classify.evidence mode code observed).1).mp accepted
  obtain ⟨c, run, hrun, complete, policy⟩ := a.accepted
  refine ⟨hcode, c, run, ?_, complete, policy⟩
  rw [← hmode, ← hrun]
  exact ((Account.checked_account.evidence c run).1).symm

/-- For the audit's own recorded result and that result's exit code, the driver reports that exit
code, unless the result is a classified file inspection or an account of another mode than the
requested one (`classify_gateExitCode` covers the exit code the audit actually returns). -/
theorem classify_exitCode (mode : EvidenceMode) (o : Observation)
    (hmode : ∀ a, o = .accepted a → a.val.mode = mode) (hc : o ≠ .classified) :
    (classify mode o.exitCode (some o)).exitCode = o.exitCode := by
  simp only [classify, Regula.ExecutableContract.run]
  cases o with
  | accepted a =>
    simp [classifyImpl, Observation.exitCode, Observation.status, hmode a rfl, Outcome.exitCode]
  | classified => exact absurd rfl hc
  | refused fs u =>
    rcases Observation.status_refused fs u with h | h
    · cases hco : (Observation.refused fs u).configurationOnly <;>
        simp [classifyImpl, Observation.exitCode, h, hco, Outcome.exitCode]
    · simp [classifyImpl, Observation.exitCode, h, Outcome.exitCode]

/-- `lake lint` reports the exit code its own `axiomGate` audit returned for the result that audit
recorded (`gateExitCode`), whatever the audit's body returned, unless the result is a classified
file inspection or an account of another mode than the requested one. This concerns the driver's
in-process audit only: a separate `axiomGate` run builds with other Lean options and can record
another result. -/
theorem classify_gateExitCode (mode : EvidenceMode) (code : UInt32)
    (observed : Option Observation)
    (hmode : ∀ a, observed = some (.accepted a) → a.val.mode = mode)
    (hc : observed ≠ some .classified) :
    (classify mode (gateExitCode code observed) observed).exitCode =
      gateExitCode code observed := by
  cases observed with
  | none =>
    simp [classify, Regula.ExecutableContract.run, classifyImpl, gateExitCode, Outcome.exitCode]
  | some o =>
    by_cases h : code ≠ 0 ∧ o.exitCode = 0
    · have hg : gateExitCode code (some o) = 3 := by
        simp only [gateExitCode]
        split
        · rfl
        · contradiction
      rw [hg]
      rcases (Observation.exitCode_eq_zero_iff o).mp h.2 with ⟨a, rfl⟩ | rfl
      · simp [classify, Regula.ExecutableContract.run, classifyImpl, Observation.status,
          Outcome.exitCode]
      · exact absurd rfl hc
    · have hg : gateExitCode code (some o) = o.exitCode := by
        simp only [gateExitCode]
        split
        · contradiction
        · rfl
      rw [hg]
      exact classify_exitCode mode o (fun a ha => hmode a (by rw [ha]))
        (fun hcl => hc (by rw [hcl]))

/-- Whole-project stages shown by `--explain-config`. -/
def projectStages : List Stage :=
  [.configuration, .discovery, .build, .admission, .declarationPolicy, .execution,
   .transcript, .history, .origin, .documentationPresence]

/-- The displayed list is the policy's own derived requirement for either project mode. -/
theorem projectStages_required (c : Claim)
    (h : c.val.mode = .incrementalProject ∨ c.val.mode = .freshProject) :
    requiredStages c = projectStages := by
  unfold requiredStages
  rcases h with h | h <;> simp [h, projectStages]

/-- Whether the driver's working-directory workspace, with package library directories
`workspace`, is the workspace that dispatched it, given the `LEAN_PATH` the driver received
and the library directory `lakeLib` of the dispatching Lake. Lake v4.34.0 (`Package.lint`,
`env`, `Workspace.augmentedLeanPath`) passes the dispatching workspace's `leanPath`, then
`lakeLib`, then any inherited `LEAN_PATH`. -/
def dispatchedFrom (workspace : List String) (lakeLib : String) (leanPath : List String) : Bool :=
  decide (lakeLib ∉ workspace) && (workspace ++ [lakeLib]).isPrefixOf leanPath

/-- For every `LEAN_PATH` of Lake's composition, whatever its inherited entries, the check
holds exactly when the working-directory workspace has the dispatching workspace's library
directories, provided Lake's own library directory is not one of the latter. -/
theorem dispatchedFrom_iff {workspace dispatching inherited : List String} {lakeLib : String}
    (h : lakeLib ∉ dispatching) :
    dispatchedFrom workspace lakeLib (dispatching ++ lakeLib :: inherited) = true ↔
      workspace = dispatching := by
  unfold dispatchedFrom
  constructor
  · intro hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hw, hp⟩ := hc
    induction workspace generalizing dispatching with
    | nil =>
      cases dispatching with
      | nil => rfl
      | cons b d => simp_all [List.isPrefixOf]
    | cons a w ih =>
      cases dispatching with
      | nil => simp_all [List.isPrefixOf]
      | cons b d =>
        simp only [List.cons_append, List.isPrefixOf, Bool.and_eq_true, beq_iff_eq] at hp
        obtain ⟨rfl, hp⟩ := hp
        simp only [List.mem_cons, not_or] at hw h
        rw [ih h.2 hw.2 hp]
  · rintro rfl
    simp [h, List.isPrefixOf_iff_prefix]

end Regula.Checker.Lint
