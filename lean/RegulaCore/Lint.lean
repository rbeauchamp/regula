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
invocation's audit rather than another's, is the driver's binding, checked by inspection.

The driver reads its arguments once (`read`, through the shared `tokenize`, which never reads an
option's value as an option) into one `Reading`: its options and the result destinations it marks
incomplete, exactly the parsed `--json-out` when they parse (`read_destinations`). Lake prepends
the package's `lintDriverArgs` to them. Before it writes any result destination or audited
artifact, the driver decides what it does (`decision`) from that reading and what it observed
(`Observed`, read from a load of the root configuration alone, which resolves no dependency and
may write only Lake's configuration directory, lock file, trace and compiled configuration):
an argument refusal is decided from `parseArgs` alone (`decision_of_parse_error`), a run audits
the dispatching workspace with the parsed options (`decision_run`), and a refusal keeps the
configuration class whatever marking then fails (`Decision.settled`, `settled_refuse`).
`configuredRefusal` is an extra refusal of
`lintDriverArgs` that give an option outside `Options.packageConfigurable`, read from the default
configuration (`configuredRefusal_eq_none`); none of the driver's guarantees rests on it. The
workspace owner's assertion of ordinary lakefiles comes from the caller's environment
(`ownerAssertion`), which Lake's own additions to the driver's environment do not set. -/

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

/-- Whether the driver's working directory is the root of the workspace that dispatched it: the
library directory `root` of the working directory's root package is the entry of the `LEAN_PATH`
the driver received just before the first entry `lakeLib`, the library directory of the
dispatching Lake. Lake v4.35.0 (`Package.lint`, `env`, `Workspace.augmentedLeanPath`) passes the
dispatching workspace's `leanPath`, then `lakeLib`, then any inherited `LEAN_PATH`
(`Config/Workspace.lean:391-392`, `Config/Env.lean:254`), and that `leanPath` ends with the root
package's library directory, since it puts each package before the ones loaded ahead of it and the
root comes first (`Config/Workspace.lean:356-357`).

The driver reads `root` from the root configuration alone and resolves no dependency, so it no
longer compares the library directories of the dependencies. The guarantee changes only for two
workspaces whose root packages have one library directory, which a build directory that names
another package's can give.

Assumes: no package configuration sets its build directory so that its library directory is that
of another package. -/
def dispatchedFrom (root lakeLib : String) (leanPath : List String) : Bool :=
  decide ((leanPath.takeWhile (· ≠ lakeLib)).getLast? = some root) &&
    decide (lakeLib ∈ leanPath)

/-- For every `LEAN_PATH` of Lake's composition, whatever its inherited entries, the check holds
exactly when `root` is the last library directory of the dispatching workspace, provided Lake's
own library directory is not one of those. -/
theorem dispatchedFrom_iff {root lakeLib : String} {dispatching inherited : List String}
    (h : lakeLib ∉ dispatching) :
    dispatchedFrom root lakeLib (dispatching ++ lakeLib :: inherited) = true ↔
      dispatching.getLast? = some root := by
  have hall : ∀ a ∈ dispatching, decide (a ≠ lakeLib) = true := by
    intro a ha
    simp only [ne_eq, decide_eq_true_eq]
    exact fun hal => h (hal ▸ ha)
  have htake : (dispatching ++ lakeLib :: inherited).takeWhile (fun a => decide (a ≠ lakeLib)) =
      dispatching := by
    rw [List.takeWhile_append_of_pos hall]
    simp
  simp only [dispatchedFrom, htake, Bool.and_eq_true, decide_eq_true_eq]
  simp

/-- One command-line argument as a program's parser reads it, for the options `α` of that
program. Each program reads its arguments once, through `tokenize`, and takes from that one
reading both what it parses and every destination it writes. -/
inductive Arg (α : Type) where
  /-- `--`, which separates Lake's arguments from the program's and is otherwise ignored. -/
  | separator
  /-- An option that takes a value, with the argument that follows it as that value. -/
  | value (option : α) (value : String)
  /-- An option that takes no value. -/
  | flag (option : α)
  /-- An argument that names no option, or an option that takes a value with none left. -/
  | unknown (argument : String)
  deriving DecidableEq

/-- Read `args` as the options `spelling` names: `spelling argument` is the option an argument
spells and whether it takes a value. The argument after an option that takes a value is its value
whatever it spells, so a value is never read as an option (`tokenize_value`), and every other
argument is read on its own. -/
def tokenize {α : Type} (spelling : String → Option (α × Bool)) : List String → List (Arg α)
  | [] => []
  | argument :: rest =>
    if argument = "--" then .separator :: tokenize spelling rest
    else match spelling argument, rest with
      | some (option, true), value :: rest => .value option value :: tokenize spelling rest
      | some (option, false), rest => .flag option :: tokenize spelling rest
      | _, rest => .unknown argument :: tokenize spelling rest

/-- `--` is read as the separator. -/
theorem tokenize_separator {α : Type} {spelling : String → Option (α × Bool)} (rest : List String) :
    tokenize spelling ("--" :: rest) = .separator :: tokenize spelling rest := by
  rw [tokenize.eq_def]; simp

/-- An option that takes a value consumes the next argument as its value, whatever it spells. -/
theorem tokenize_value {α : Type} {spelling : String → Option (α × Bool)} {argument value : String}
    {option : α} (rest : List String) (hsep : argument ≠ "--")
    (h : spelling argument = some (option, true)) :
    tokenize spelling (argument :: value :: rest) =
      .value option value :: tokenize spelling rest := by
  rw [tokenize.eq_2 _ _ _ _ _ h]; simp [hsep]

/-- An option that takes no value is read on its own. -/
theorem tokenize_flag {α : Type} {spelling : String → Option (α × Bool)} {argument : String}
    {option : α} (rest : List String) (hsep : argument ≠ "--")
    (h : spelling argument = some (option, false)) :
    tokenize spelling (argument :: rest) = .flag option :: tokenize spelling rest := by
  rw [tokenize.eq_3 _ _ _ _ h]; simp [hsep]

/-- Any other argument is read as `unknown` on its own. -/
theorem tokenize_unknown {α : Type} {spelling : String → Option (α × Bool)} {argument : String}
    {rest : List String} (hsep : argument ≠ "--")
    (hvalue : ∀ (option : α) (value : String) (rest' : List String),
      spelling argument = some (option, true) → rest = value :: rest' → False)
    (hflag : ∀ (option : α), spelling argument = some (option, false) → False) :
    tokenize spelling (argument :: rest) = .unknown argument :: tokenize spelling rest := by
  rw [tokenize.eq_4 _ _ _ hflag hvalue]; simp [hsep]

/-- Reading a list whose reading has no `unknown` argument, then more arguments, reads the two
apart: no option of the first takes its value from the second. -/
theorem tokenize_append {α : Type} {spelling : String → Option (α × Bool)} {l : List String}
    (r : List String) (h : ∀ argument, Arg.unknown argument ∉ tokenize spelling l) :
    tokenize spelling (l ++ r) = tokenize spelling l ++ tokenize spelling r := by
  induction l using tokenize.induct spelling with
  | case1 => rfl
  | case2 rest ih =>
    simp only [tokenize_separator, List.mem_cons, reduceCtorEq, false_or] at h
    rw [List.cons_append, tokenize_separator, tokenize_separator, ih h, List.cons_append]
  | case3 argument hsep option value rest hs ih =>
    simp only [tokenize_value _ hsep hs, List.mem_cons, reduceCtorEq, false_or] at h
    rw [List.cons_append, List.cons_append, tokenize_value _ hsep hs, tokenize_value _ hsep hs,
      ih h, List.cons_append]
  | case4 argument hsep option rest hs ih =>
    simp only [tokenize_flag _ hsep hs, List.mem_cons, reduceCtorEq, false_or] at h
    rw [List.cons_append, tokenize_flag _ hsep hs, tokenize_flag _ hsep hs, ih h, List.cons_append]
  | case5 argument hsep rest hvalue hflag _ =>
    exact absurd (by rw [tokenize_unknown hsep hvalue hflag]; exact List.mem_cons_self)
      (h argument)

/-- The options of the `lake lint` driver. -/
inductive Setting where
  /-- `--project DIR`. -/
  | project
  /-- `--manifest PATH`. -/
  | manifest
  /-- `--json-out PATH`. -/
  | jsonOut
  /-- `--fresh`. -/
  | fresh
  /-- `--verbose`. -/
  | verbose
  /-- `--explain-config`. -/
  | explain
  /-- `--help` or `-h`. -/
  | help
  deriving DecidableEq

/-- How the driver spells each of its options. -/
def Setting.spelling : Setting → String
  | .project => "--project" | .manifest => "--manifest" | .jsonOut => "--json-out"
  | .fresh => "--fresh" | .verbose => "--verbose" | .explain => "--explain-config"
  | .help => "--help"

/-- The option an argument spells, and whether it takes a value. -/
def Setting.ofSpelling : String → Option (Setting × Bool)
  | "--project" => some (.project, true)
  | "--manifest" => some (.manifest, true)
  | "--json-out" => some (.jsonOut, true)
  | "--fresh" => some (.fresh, false)
  | "--verbose" => some (.verbose, false)
  | "--explain-config" => some (.explain, false)
  | "--help" | "-h" => some (.help, false)
  | _ => none

/-- The driver's reading of its arguments. -/
def arguments (args : List String) : List (Arg Setting) :=
  tokenize Setting.ofSpelling args

/-- The command-line options of one `lake lint` run of this driver, as `parseArgs` reads them. -/
structure Options where
  /-- `--project DIR`: the project to audit; it must be the dispatching workspace. -/
  project : Option String := none
  /-- `--manifest PATH`: the surface manifest instead of `foundation_manifest.json`. -/
  manifest : Option String := none
  /-- `--json-out PATH`: where the audit writes its versioned result JSON. -/
  jsonOut : Option String := none
  /-- `--fresh`: audit an isolated copy built from empty output instead of incrementally. -/
  fresh : Bool := false
  /-- `--verbose`: pass `--verbose` to the audit, which then also prints every classified
  declaration, the execution roots and toolchain trusted-base entries it lists on request, and
  its timing spans. -/
  verbose : Bool := false
  /-- `--explain-config`: print the configuration an audit would use, run no audit and exit
  with the configuration class. -/
  explain : Bool := false
  /-- `--help` or `-h`: print the usage text, run no audit and exit with the configuration
  class. -/
  help : Bool := false
  deriving DecidableEq

/-- The refusal of a second occurrence of an option. -/
private def duplicate (option : Setting) : Except String Options :=
  .error s!"duplicate {option.spelling} option"

/-- Apply one argument. Unknown, duplicate and incomplete arguments are refused. -/
def Options.apply (o : Options) : Arg Setting → Except String Options
  | .separator => .ok o
  | .value .project value =>
    if o.project.isSome then duplicate .project else .ok { o with project := some value }
  | .value .manifest value =>
    if o.manifest.isSome then duplicate .manifest else .ok { o with manifest := some value }
  | .value .jsonOut value =>
    if o.jsonOut.isSome then duplicate .jsonOut else .ok { o with jsonOut := some value }
  | .flag .fresh => if o.fresh then duplicate .fresh else .ok { o with fresh := true }
  | .flag .verbose => if o.verbose then duplicate .verbose else .ok { o with verbose := true }
  | .flag .explain => if o.explain then duplicate .explain else .ok { o with explain := true }
  | .flag .help => .ok { o with help := true }
  | .value option _ | .flag option =>
    .error s!"unknown or incomplete argument: {option.spelling}"
  | .unknown argument => .error s!"unknown or incomplete argument: {argument}"

/-- Apply each argument in order, stopping at the first refusal. -/
def Options.applyAll : List (Arg Setting) → Options → Except String Options
  | [], o => .ok o
  | a :: rest, o => do Options.applyAll rest (← o.apply a)

/-- The driver's options: its one reading of `args` (`arguments`), applied in order. No option
narrows the claim. -/
def parseArgs (args : List String) (o : Options) : Except String Options :=
  Options.applyAll (arguments args) o

/-- The result destination an argument names: the value of `--json-out`. -/
def Arg.destination : Arg Setting → Option String
  | .value .jsonOut path => some path
  | _ => none

/-- The driver's one reading of the arguments it received. The parse and every result
destination come from the same `arguments`, and each step of the driver uses this value instead
of reading the arguments again. -/
structure Reading where
  /-- The arguments as received, which `configuredRefusal` compares with the package's
  `lintDriverArgs`. -/
  args : List String
  /-- The options they parse to, or the reason they do not. -/
  parsed : Except String Options
  /-- Each `--json-out` value, whether or not the arguments parse. The driver marks each
  incomplete. -/
  destinations : List String
  /-- Whether an argument is `--ordinary-lakefiles`, which the driver reads as unknown. -/
  ownerArgument : Bool

/-- Read `args` once. -/
def read (args : List String) : Reading :=
  let arguments := arguments args
  { args, parsed := Options.applyAll arguments {}, destinations := arguments.filterMap Arg.destination
    ownerArgument := arguments.contains (.unknown "--ordinary-lakefiles") }

/-- Applying arguments that apply: no `unknown` argument among them. -/
private theorem applyAll_known {ts : List (Arg Setting)} {o o' : Options}
    (h : Options.applyAll ts o = .ok o') : ∀ argument, Arg.unknown argument ∉ ts := by
  induction ts generalizing o with
  | nil => simp
  | cons a rest ih =>
    simp only [Options.applyAll, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i o₁ ha
      intro argument hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp [Options.apply] at ha
      · exact ih h argument hmem

/-- Applying a concatenation applies its parts in turn. -/
private theorem applyAll_append (ts us : List (Arg Setting)) (o : Options) :
    Options.applyAll (ts ++ us) o = (Options.applyAll ts o >>= Options.applyAll us) := by
  induction ts generalizing o with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.cons_append, Options.applyAll, bind, Except.bind]
    split
    · rfl
    · exact ih _

/-- Parsing continues from the options of a prefix that parses alone. -/
theorem parseArgs_append {l : List String} {o o' : Options} (r : List String)
    (h : parseArgs l o = .ok o') : parseArgs (l ++ r) o = parseArgs r o' := by
  unfold parseArgs arguments at *
  rw [tokenize_append r (applyAll_known h), applyAll_append, h]
  rfl

/-- One argument adds its destination, if any, to the destination of the options it applies
to. -/
private theorem apply_destination {s s' : Options} {a : Arg Setting} (h : s.apply a = .ok s') :
    s.jsonOut.toList ++ a.destination.toList = s'.jsonOut.toList := by
  rcases s with ⟨p, m, j, f, v, e, hp⟩
  cases a with
  | separator => simp only [Options.apply, Except.ok.injEq] at h; subst h; simp [Arg.destination]
  | unknown => simp [Options.apply] at h
  | value k path =>
    cases k <;> simp only [Options.apply] at h <;> (try split at h) <;>
      simp_all [duplicate, Arg.destination] <;> (subst h; simp_all)
  | flag k =>
    cases k <;> simp only [Options.apply] at h <;> (try split at h) <;>
      simp_all [duplicate, Arg.destination] <;> (subst h; simp_all)

/-- When the arguments parse, the reading's destinations are exactly the parsed `--json-out`. -/
theorem read_destinations {args : List String} {options : Options}
    (h : (read args).parsed = .ok options) : (read args).destinations = options.jsonOut.toList := by
  suffices ∀ (ts : List (Arg Setting)) (s : Options), Options.applyAll ts s = .ok options →
      s.jsonOut.toList ++ ts.filterMap Arg.destination = options.jsonOut.toList by
    simpa [read] using this (arguments args) {} h
  intro ts
  induction ts with
  | nil => intro s h; simp only [Options.applyAll, Except.ok.injEq] at h; subst h; simp
  | cons a rest ih =>
    intro s h
    simp only [Options.applyAll, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i s' ha
      rw [← ih s' h, ← apply_destination ha, List.filterMap_cons]
      cases a.destination <;> simp

/-- The options a package's `lintDriverArgs` may give: the evidence mode, `--verbose`,
`--explain-config` and `--help`. Every other field has its default here, including a field added
to `Options` later, so an option is refused in `lintDriverArgs` unless it is added here. -/
def Options.packageConfigurable (o : Options) : Options :=
  { fresh := o.fresh, verbose := o.verbose, explain := o.explain, help := o.help }

/-- What a run audits, how it builds and where its result goes: every field but the four of
`packageConfigurable`, which this resets. -/
def Options.target (o : Options) : Options :=
  { o with fresh := false, verbose := false, explain := false, help := false }

/-- The options that `configured` gives with a value, for the refusal message. -/
def namedOptions (configured : List String) : List String :=
  (arguments configured).filterMap fun
    | .value option _ => some option.spelling
    | _ => none

/-- An extra refusal, for the package's `lintDriverArgs` `configured` as the driver reads them
from the default configuration of the working-directory workspace, given the arguments `args`
the driver received. Lake v4.35.0 (`Package.lint`) passes `configured ++ caller`, where `caller`
holds the arguments after `--` on the `lake lint` command line. The configured arguments must
begin `args`, parse alone, and give only options of `packageConfigurable`
(`configuredRefusal_eq_none`). The driver's guarantees do not rest on it: whatever the
configuration gives, `--project` must be the dispatching workspace, a relative `--json-out`
resolves there, and the success line and the result name the manifest (`decision`).

Assumes: Lake loaded the default configuration file of that workspace, without `-f`/`--file`
or `-K` options, and that file gives the same `lintDriverArgs` when the driver loads it again.
Lake v4.35.0 passes neither option to the driver: `CLI/Main.lean:232` and `:361-363` set
`configFile` only for the load (`:138`, `:1133-1146`), `CLI/Actions.lean:20-21` spawns the driver
with the augmented environment of `Config/Workspace.lean:417-431` and `Config/Env.lean:287-305`,
which names no package configuration, and `CLI/Main.lean:365-367` drops the `--` separator. The
file can change between the two loads: `Load/Lean/Elab.lean:231-281` hashes the file as it is at
each load and releases the configuration lock after it. -/
def configuredRefusal (configured args : List String) : Option String :=
  if !configured.isPrefixOf args then
    some "the arguments do not begin with the package's lintDriverArgs, so Lake did not \
      compose them"
  else match parseArgs configured {} with
    | .error message => some s!"the package's lintDriverArgs do not parse alone: {message}"
    | .ok given =>
      if given = given.packageConfigurable then none
      else
        some s!"the package's lintDriverArgs give {" ".intercalate (namedOptions configured)}: \
          the project, manifest and result destination come only from the lake lint command \
          line, and lintDriverArgs cannot give them"

/-- One argument keeps two option sets with the same `target` in step, the second refusing no
flag of `packageConfigurable` that the first accepts. -/
private theorem apply_target {s t s' : Options} {a : Arg Setting}
    (htarget : s.target = t.target)
    (hfresh : t.fresh = true → s.fresh = true) (hverbose : t.verbose = true → s.verbose = true)
    (hexplain : t.explain = true → s.explain = true) (h : s.apply a = .ok s') :
    ∃ t', t.apply a = .ok t' ∧ s'.target = t'.target ∧ (t'.fresh = true → s'.fresh = true) ∧
      (t'.verbose = true → s'.verbose = true) ∧ (t'.explain = true → s'.explain = true) := by
  rcases s with ⟨sp, sm, sj, sf, sv, se, sh⟩
  rcases t with ⟨tp, tm, tj, tf, tv, te, th⟩
  simp only [Options.target, Options.mk.injEq] at htarget
  obtain ⟨rfl, rfl, rfl, -⟩ := htarget
  cases a with
  | separator =>
    simp only [Options.apply, Except.ok.injEq] at h
    subst h
    exact ⟨_, rfl, by simp [Options.target], hfresh, hverbose, hexplain⟩
  | unknown => simp [Options.apply] at h
  | value k value =>
    cases k <;> simp only [Options.apply] at h ⊢
    all_goals first
      | (simp at h)
      | (split at h
         · simp [duplicate] at h
         · rename_i hnone
           simp only [Except.ok.injEq] at h
           subst h
           simp only [hnone, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, exists_eq_left']
           simp only [Options.target] at hfresh hverbose hexplain ⊢
           exact ⟨by simp, hfresh, hverbose, hexplain⟩)
  | flag k =>
    cases k <;> simp only [Options.apply] at h ⊢
    case help =>
      simp only [Except.ok.injEq] at h
      subst h
      exact ⟨_, rfl, by simp [Options.target], hfresh, hverbose, hexplain⟩
    all_goals first
      | (simp at h)
      | (cases sf <;> cases tf <;> cases sv <;> cases tv <;> cases se <;> cases te <;>
          simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, duplicate, reduceCtorEq]
            at h hfresh hverbose hexplain ⊢ <;>
          first
          | (exfalso; simp_all; done)
          | (subst h; refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩ <;> simp [Options.target]))

/-- From two option sets that give the same `target`, where the second sets no flag of
`packageConfigurable` that the first leaves unset, the same arguments parse to options with the
same `target`, the second whenever the first does. -/
theorem parseArgs_target {args : List String} {s t o : Options}
    (htarget : s.target = t.target)
    (hfresh : t.fresh = true → s.fresh = true) (hverbose : t.verbose = true → s.verbose = true)
    (hexplain : t.explain = true → s.explain = true) (h : parseArgs args s = .ok o) :
    ∃ o₀, parseArgs args t = .ok o₀ ∧ o.target = o₀.target := by
  unfold parseArgs at *
  generalize arguments args = ts at *
  induction ts generalizing s t with
  | nil =>
    simp only [Options.applyAll, Except.ok.injEq] at h
    subst h
    exact ⟨t, rfl, htarget⟩
  | cons a rest ih =>
    simp only [Options.applyAll, bind, Except.bind] at h ⊢
    split at h
    · simp at h
    · rename_i s' ha
      obtain ⟨t', ht', htarget', hf', hv', he'⟩ :=
        apply_target htarget hfresh hverbose hexplain ha
      rw [ht']
      exact ih htarget' hf' hv' he' h

/-- When `configuredRefusal` admits the package's `lintDriverArgs` `configured`, and the arguments
Lake composes from them and the command line's `caller` (`configured ++ caller`) parse, then
`caller` alone parses too, and to the same `Options.target`: the project, the manifest, the
`--json-out` destination and every option outside `packageConfigurable` come from the command
line alone. That the driver receives `configured ++ caller`, with `configured` from the
configuration Lake loaded, is what `configuredRefusal` assumes, not proved here. -/
theorem configuredRefusal_eq_none {configured caller : List String} {o : Options}
    (h : configuredRefusal configured (configured ++ caller) = none)
    (hparse : parseArgs (configured ++ caller) {} = .ok o) :
    ∃ o₀, parseArgs caller {} = .ok o₀ ∧ o.target = o₀.target := by
  have hprefix : configured.isPrefixOf (configured ++ caller) = true :=
    List.isPrefixOf_iff_prefix.mpr (List.prefix_append _ _)
  simp only [configuredRefusal, hprefix, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · simp at h
  · rename_i given hgiven
    split at h
    · rename_i hconfigurable
      rw [parseArgs_append caller hgiven] at hparse
      refine parseArgs_target ?_ (fun h => by simp at h) (fun h => by simp at h)
        (fun h => by simp at h) hparse
      rw [hconfigurable]
      rfl
    · simp at h

/-- The environment variable that carries the workspace owner's assertion that the workspace's
lakefiles are ordinary configuration. -/
def ordinaryLakefilesVariable : String := "REGULA_ORDINARY_LAKEFILES"

/-- The owner's assertion, read from the value of `ordinaryLakefilesVariable` in the environment
the driver received: unset is no assertion, `1` asserts, and any other value is refused. With it
the claimed build omits the audit-build marker when the plain-shape guard
`Lake.auditMarkerNeeded` admits the workspace, and prints whether it omits the marker or keeps it
and why (`Lake.buildAuditTargets`); without it the build always has the marker.

Assumes: the variable comes from the caller of `lake lint`, never from a package configuration.
Lake v4.35.0 spawns the driver with `IO.Process.spawn` and `env := ← getAugmentedEnv`
(`CLI/Actions.lean:20-21`), which keeps the environment Lake received and sets only the
variables of `Config/Workspace.lean:417-431` and `Config/Env.lean:287-305`, none of them this
one. A package configuration can decide some of those, such as `LAKE_ARTIFACT_CACHE`
(`Config/Workspace.lean:133-134` and `:420`), but not this one. Configuration code
that changes the Lake process's own environment is outside this boundary, as is any other
deliberate manipulation of the build. -/
def ownerAssertion : Option String → Except String Bool
  | none => .ok false
  | some "1" => .ok true
  | some other => .error s!"{ordinaryLakefilesVariable} must be 1 or unset, not '{other}'"

/-- The owner asserts ordinary lakefiles exactly when the variable is `1`. -/
theorem ownerAssertion_eq_true_iff (value : Option String) :
    ownerAssertion value = .ok true ↔ value = some "1" := by
  unfold ownerAssertion
  split <;> simp_all


/-- What the driver reads before it decides. It writes no result destination and no audited
artifact to read it, and it loads only the root configuration of the working directory, so it
resolves no dependency and writes no manifest.

Assumes: that load writes only what Lake v4.35.0's `importConfigFile` writes for a `lakefile.lean`
whose compiled configuration is not up to date, and nothing for a `lakefile.toml`: the
configuration directory and `.lake` when absent (`Load/Lean/Elab.lean:184` and `:293`), the
configuration's lock file (`:207`), its trace (`:223`, `:246-253` and `:294`, removed again at
`:262` when elaboration fails) and its compiled configuration (`:244` and `:256`). Elaborating the
configuration also runs its own commands, as Lake's own load of it does. -/
structure Observed where
  /-- The project root of the working directory, which builds the audit worker and is the
  dispatching workspace when `dispatched` holds. -/
  dispatching : String
  /-- Whether the working-directory workspace is the one `lake lint` was dispatched from
  (`dispatchedFrom` over the `LEAN_PATH` the driver received). -/
  dispatched : Bool
  /-- The `lintDriverArgs` of that workspace's default configuration. -/
  configured : List String
  /-- The project root of the arguments' `--project`, when they give one and it has one. -/
  named : Option String
  /-- The value of `ordinaryLakefilesVariable` in the driver's environment. -/
  owner : Option String

/-- What the driver does, decided before it writes any result destination or audited
artifact. -/
inductive Decision where
  /-- Refuse the invocation with this reason: the configuration class. -/
  | refuse (reason : String)
  /-- Print the usage text: the configuration class. -/
  | help
  /-- An observation failed: the incomplete class. -/
  | incomplete (reason : String)
  /-- Explain the configuration of these options; no audit runs. -/
  | explain (options : Options)
  /-- Audit with these options, with the owner's assertion of ordinary lakefiles or without. -/
  | run (options : Options) (ordinary : Bool)

/-- The reason for an argument refusal, with a note when an argument is the owner's assertion,
which comes only from the environment. -/
def argumentRefusal (reading : Reading) (message : String) : String :=
  if reading.ownerArgument then
    s!"{message}; the workspace owner gives that assertion as {ordinaryLakefilesVariable}=1 in \
      the environment of lake lint"
  else message

/-- The reason for a working directory that is not the dispatching workspace. -/
def dispatchRefusal : String :=
  "the working directory is not the workspace `lake lint` was dispatched from; run lake lint from \
    the project root without -d/--dir"

/-- The reason for a `--project` that names a root other than the dispatching one. -/
def projectRefusal (project dispatching : String) : String :=
  s!"--project {project} is not the project lake lint runs in ({dispatching}); lake lint audits \
    only that project, and `lake exe axiomGate --project DIR` audits another one"

/-- The driver's decision from its one reading of its arguments and what it observed, in
this order: an argument refusal, `--json-out` or `--verbose` with `--help` or `--explain-config`,
`--help`, a failed observation, a working directory that is not the dispatching workspace, the
extra `configuredRefusal`, a `--project` whose root is not the dispatching one, `--explain-config`,
and an owner's assertion other than `1`. Otherwise it runs. -/
def decision (reading : Reading) (observed : Except String Observed) : Decision :=
  match reading.parsed with
  | .error message => .refuse (argumentRefusal reading message)
  | .ok options =>
    if (options.help || options.explain) && (options.jsonOut.isSome || options.verbose) then
      .refuse "--json-out and --verbose apply only to an audit"
    else if options.help then .help
    else match observed with
      | .error reason => .incomplete reason
      | .ok seen =>
        if !seen.dispatched then .refuse dispatchRefusal
        else match configuredRefusal seen.configured reading.args with
          | some reason => .refuse reason
          | none =>
            match options.project with
            | some project =>
              if seen.named = some seen.dispatching then
                if options.explain then .explain options
                else match ownerAssertion seen.owner with
                  | .error reason => .refuse reason
                  | .ok ordinary => .run options ordinary
              else .refuse (projectRefusal project seen.dispatching)
            | none =>
              if options.explain then .explain options
              else match ownerAssertion seen.owner with
                | .error reason => .refuse reason
                | .ok ordinary => .run options ordinary

/-- An argument refusal is decided from the parse alone, whatever the driver observed. -/
theorem decision_of_parse_error {reading : Reading} {message : String}
    (h : reading.parsed = .error message) (observed : Except String Observed) :
    decision reading observed = .refuse (argumentRefusal reading message) := by
  simp [decision, h]

/-- A run's options are those of the one reading of the arguments `args`, its result
destinations are exactly their `--json-out`, its project, when it names one, has the dispatching
root, and the owner's assertion holds exactly when the variable is `1`. -/
theorem decision_run {args : List String} {seen : Observed} {options : Options}
    {ordinary : Bool} (h : decision (read args) (.ok seen) = .run options ordinary) :
    (read args).parsed = .ok options ∧ (read args).destinations = options.jsonOut.toList ∧
      (options.project.isSome → seen.named = some seen.dispatching) ∧ seen.dispatched = true ∧
      (ordinary = true ↔ seen.owner = some "1") := by
  unfold decision at h
  split at h
  · simp at h
  · rename_i parsed hparsed
    split at h
    · simp at h
    split at h
    · simp at h
    simp only at h
    split at h
    · simp at h
    rename_i hdispatched
    split at h
    · simp at h
    split at h
    · rename_i project hproject
      split at h
      · rename_i hnamed
        split at h
        · simp at h
        split at h
        · simp at h
        · rename_i asserted hasserted
          simp only [Decision.run.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨hparsed, read_destinations hparsed, fun _ => hnamed, by simpa using
            hdispatched, ?_⟩
          rw [← ownerAssertion_eq_true_iff]
          cases asserted <;> simp [hasserted]
      · simp at h
    · rename_i hproject
      split at h
      · simp at h
      split at h
      · simp at h
      · rename_i asserted hasserted
        simp only [Decision.run.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hparsed, read_destinations hparsed, by simp [hproject], by simpa using
          hdispatched, ?_⟩
        rw [← ownerAssertion_eq_true_iff]
        cases asserted <;> simp [hasserted]

/-- What the driver does after it marks the result destinations, when it acts. -/
inductive Action where
  /-- Explain the configuration of these options; no audit runs. -/
  | explain (options : Options)
  /-- Audit with these options, with the owner's assertion of ordinary lakefiles or without. -/
  | run (options : Options) (ordinary : Bool)

/-- The exit class settled before the driver acts, from its decision and the destinations it
could not mark incomplete (`failed`), or the action it takes: a refusal and `--help` keep the
configuration class whatever failed, a failed observation is incomplete, and a failed mark stops
an explanation or a run as incomplete before it acts. -/
def Decision.settled : Decision → List String → Except Outcome Action
  | .refuse _, _ | .help, _ => .error .configuration
  | .incomplete _, _ => .error .incomplete
  | .explain _, _ :: _ | .run _ _, _ :: _ => .error .incomplete
  | .explain options, [] => .ok (.explain options)
  | .run options ordinary, [] => .ok (.run options ordinary)

/-- A refusal keeps the configuration class whatever marking failed. -/
theorem settled_refuse (reason : String) (failed : List String) :
    (Decision.refuse reason).settled failed = .error .configuration := rfl

/-- A refused invocation exits with the configuration class, whatever the driver observed and
whatever marking failed. -/
theorem settled_of_parse_error {reading : Reading} {message : String}
    (h : reading.parsed = .error message) (observed : Except String Observed)
    (failed : List String) : (decision reading observed).settled failed = .error .configuration := by
  rw [decision_of_parse_error h]
  rfl

/-- The driver acts only on a decision it made with no failed mark: a run that it acts on is the
run it decided. -/
theorem settled_run {decided : Decision} {failed : List String} {options : Options}
    {ordinary : Bool} (h : decided.settled failed = .ok (.run options ordinary)) :
    decided = .run options ordinary ∧ failed = [] := by
  cases decided <;> cases failed <;> simp_all [Decision.settled]

end Regula.Checker.Lint
