import RegulaCore.Account

/-! # Lint driver exit classification

The `lint` driver's exit classification. The driver runs the project audit and reads
back the terminal status that audit recorded; this module decides the exit class from that
status and the audit's exit code. `completed` carries an accepted account
(`Account.Status.completed_accepted`), so exit 0 requires an accepted run of the requested
project mode (`accepted_sound`). The observation's authenticity, that it is this
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

/-- The terminal status the audit decided for one invocation, and whether its findings are
all configuration (RG2002) rejections. It is the `status` the result output renders, kept in
memory without serialization. -/
structure Observation where
  /-- The terminal status the audit recorded. -/
  status : Status
  /-- Every finding of the run is a configuration (RG2002) rejection. -/
  configurationOnly : Bool

/-- Required meaning of the classification, for every requested mode, audit exit code and
recorded observation. Accepted exactly when the audit exited zero and recorded `completed`
with an account of the requested mode; violation or configuration exactly when it exited
nonzero after recording a rejection with non-configuration or only configuration findings.
Every other combination, including no recorded status, a zero exit without `completed`, a
nonzero exit after `completed`, and a completed account of another mode, is incomplete. -/
def ClassifyContract (classify : EvidenceMode → UInt32 → Option Observation → Outcome) : Prop :=
  ∀ mode code observed,
    (classify mode code observed = .accepted ↔
      code = 0 ∧ ∃ a b, observed = some ⟨.completed a, b⟩ ∧ a.val.mode = mode) ∧
    (classify mode code observed = .violation ↔ code ≠ 0 ∧ ∃ o, observed = some o ∧
      o.status matches .rejected ∧ o.configurationOnly = false) ∧
    (classify mode code observed = .configuration ↔ code ≠ 0 ∧ ∃ o, observed = some o ∧
      o.status matches .rejected ∧ o.configurationOnly = true)

private def classifyImpl (mode : EvidenceMode) (code : UInt32) : Option Observation → Outcome
  | some ⟨.completed a, _⟩ => if code = 0 ∧ a.val.mode = mode then .accepted else .incomplete
  | some ⟨.rejected, configurationOnly⟩ =>
      if code = 0 then .incomplete else if configurationOnly then .configuration else .violation
  | _ => .incomplete

/-- Registers `ClassifyContract` about the executed classification; callers use `classify`. -/
theorem checked_classify : Regula.ExecutableContract classifyImpl ClassifyContract :=
  ⟨fun mode code observed => by
    rcases observed with _ | ⟨status, configurationOnly⟩
    · simp [classifyImpl]
    · cases status <;> cases configurationOnly <;> by_cases hc : code = 0 <;>
        simp_all [classifyImpl] <;> split <;> simp_all⟩

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
  obtain ⟨hcode, a, _, _, hmode⟩ := ((checked_classify.evidence mode code observed).1).mp accepted
  obtain ⟨c, run, hrun, complete, policy⟩ := a.accepted
  refine ⟨hcode, c, run, ?_, complete, policy⟩
  rw [← hmode, ← hrun]
  exact ((Account.checked_account.evidence c run).1).symm

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
