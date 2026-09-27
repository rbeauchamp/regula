import RegulaPolicy.Observation
import RegulaPolicy.ResultState

/-! # Fixed-plan acceptance

Acceptance of the concrete fixed policy plan. Every required slot is completed and
meets its named stage relation. These are conditional guarantees about observations and
exact report identity, not claims that IO acquisition or semantic intent is verified. -/
namespace RegulaPolicy
open Std

/-- Nat slots are only an ordered implementation of the exact frozen JobKey array. -/
def requiredSlots {c : Claim} {i : Census} (p : Plan c i) : CanonicalSet Nat :=
  CanonicalSet.normalize (List.range p.jobs.size)

/-- Payload admission binds each slot to its exact full JobKey and source/config snapshot. -/
def ResultBound {c : Claim} {i : Census} (p : Plan c i) (slot : Nat) (o : JobObservation) : Prop :=
  p.jobs[slot]? = some o.key ∧ o.snapshot = c.val.snapshot
instance {c : Claim} {i : Census} (p : Plan c i) (slot : Nat) (o : JobObservation) :
    Decidable (ResultBound p slot o) := by unfold ResultBound; infer_instance

/-- The result table of plan `p`: observations keyed by the plan's job slots, each occupied slot
bound to its planned job key and the claim's snapshot (`ResultBound`). -/
abbrev ResultTable {c : Claim} {i : Census} (p : Plan c i) := ResultState (requiredSlots p) (ResultBound p)

/-- Completeness quantifies the independent plan, including discovery/build/scan slots when
subject inventories are empty. Unique lookup and absence of extra keys come from ResultState. -/
def CompleteFor {c : Claim} {i : Census} (p : Plan c i) (s : ResultTable p) : Prop :=
  PlanOK c i ∧ ∀ slot ∈ List.range p.jobs.size,
    ∃ o ∈ s.entries[slot]?, o.completion = .completed
/-- The exact admitted plan already proves validity; result completion still checks every
required slot, optional lookup and status. No observation or serialized verdict supplies it. -/
theorem completeFor_iff_slots {c : Claim} {i : Census} (p : Plan c i) (s : ResultTable p) :
    CompleteFor p s ↔ ∀ slot ∈ List.range p.jobs.size,
      ∃ o ∈ s.entries[slot]?, o.completion = .completed :=
  ⟨And.right, fun hs => ⟨p.valid, hs⟩⟩

instance {c : Claim} {i : Census} (p : Plan c i) (s : ResultTable p) :
    Decidable (CompleteFor p s) :=
  decidable_of_iff _ (completeFor_iff_slots p s).symm

/-- Same Boolean outcome as the former structural decision, universally over the exact
indexed inputs. Proof irrelevance changes neither the proposition nor its truth value. -/
theorem completeFor_decide_eq_previous {c : Claim} {i : Census}
    (p : Plan c i) (s : ResultTable p) :
    decide (CompleteFor p s) = @decide (CompleteFor p s)
      (by unfold CompleteFor; infer_instance) := by
  congr

/-- Every planned job, rather than every merely returned success, meets its own policy. -/
def AllPolicyOK {c : Claim} {i : Census} (p : Plan c i) (roles : CensusRoles i)
    (s : ResultTable p) : Prop :=
  ∀ slot ∈ List.range p.jobs.size, ∃ o ∈ s.entries[slot]?, PolicyOK c i roles o
instance {c : Claim} {i : Census} (p : Plan c i) (roles : CensusRoles i) (s : ResultTable p) :
    Decidable (AllPolicyOK p roles s) := by unfold AllPolicyOK; infer_instance

/-- Why `accept` refuses a result table. -/
inductive AcceptanceFailure where
  /-- Some planned slot has no completed observation (`CompleteFor` fails). -/
  | incomplete
  /-- Every slot completed, but some planned job's observation fails its policy
  (`AllPolicyOK` fails). -/
  | policyViolation
  deriving Repr, DecidableEq

/-- Mechanical acceptance for these exact claim, census, plan and result inputs. A negative
or teaching example remains an accepted expectation, not a conforming positive program.
No serialized accepted flag can construct either proof. The structure is a `Type`, not a
`Prop`, although its fields are propositions: `accept` returns it as the success value of an
`Except`, whose value type is a `Type`. -/
structure Accepted {c : Claim} {i : Census} (p : Plan c i) (roles : CensusRoles i) (s : ResultTable p) : Type where
  /-- Every planned slot holds a completed observation. -/
  complete : CompleteFor p s
  /-- Every planned slot's observation meets its policy. -/
  policy : AllPolicyOK p roles s

/-- Recompute completeness and actual pure policy relations after payload admission. -/
def accept {c : Claim} {i : Census} (p : Plan c i) (roles : CensusRoles i)
    (s : ResultTable p) : Except AcceptanceFailure (Accepted p roles s) :=
  if hc : CompleteFor p s then
    if hp : AllPolicyOK p roles s then .ok ⟨hc, hp⟩ else .error .policyViolation
  else .error .incomplete

/-- Any decision of the same completeness proposition gives the identical success value
or exact refusal, with incompleteness before policy failure. This includes the former
structural decision, not merely the successful cases. -/
theorem accept_decision_eq {c : Claim} {i : Census} (p : Plan c i) (roles : CensusRoles i)
    (s : ResultTable p) (decision : Decidable (CompleteFor p s)) :
    accept p roles s = @dite (Except AcceptanceFailure (Accepted p roles s))
      (CompleteFor p s) decision
      (fun hc => if hp : AllPolicyOK p roles s then .ok ⟨hc, hp⟩ else .error .policyViolation)
      (fun _ => .error .incomplete) := by
  by_cases hc : CompleteFor p s <;> simp [accept, hc]

/-- Soundness holds for every admitted plan, role receipt and result table. It does not
assert that any external worker actually completed or that its observation is truthful. -/
theorem accept_sound {c : Claim} {i : Census} (p : Plan c i) (roles : CensusRoles i)
    (s : ResultTable p) (a : Accepted p roles s) (_ : accept p roles s = .ok a) :
    CompleteFor p s ∧ AllPolicyOK p roles s := ⟨a.complete, a.policy⟩

/-- Every complete table satisfying all concrete policy predicates is accepted. Completeness
is over the supported finite observed data, not theorem search, extraction or external liveness. -/
theorem accept_complete {c : Claim} {i : Census} (p : Plan c i) (roles : CensusRoles i)
    (s : ResultTable p) (h : CompleteFor p s ∧ AllPolicyOK p roles s) :
    ∃ a, accept p roles s = .ok a := by
  exact ⟨⟨h.1, h.2⟩, by simp [accept, h.1, h.2]⟩

/-- No refusal can discard a missing, crashed, pending, or wrong-policy job. -/
theorem accept_iff {c : Claim} {i : Census} (p : Plan c i) (roles : CensusRoles i)
    (s : ResultTable p) :
    (∃ a, accept p roles s = .ok a) ↔ CompleteFor p s ∧ AllPolicyOK p roles s := by
  constructor
  · rintro ⟨a, ha⟩; exact accept_sound p roles s a ha
  · exact accept_complete p roles s

/-- Explicit incomplete refusal; no error path produces an Accepted replacement value. -/
theorem accept_incomplete {c : Claim} {i : Census} (p : Plan c i) (roles : CensusRoles i)
    (s : ResultTable p) (h : ¬ CompleteFor p s) :
    accept p roles s = .error .incomplete := by simp [accept, h]

/-- Once every worker completed, an unsatisfied policy relation is a policy refusal. -/
theorem accept_policyViolation {c : Claim} {i : Census} (p : Plan c i) (roles : CensusRoles i)
    (s : ResultTable p) (hc : CompleteFor p s) (hp : ¬ AllPolicyOK p roles s) :
    accept p roles s = .error .policyViolation := by simp [accept, hc, hp]

/-- Report projection carries the exact accepted inputs; it cannot substitute a different
scope, inventory, job order, or payload table. Renderers and audit exits consume this in #7. -/
structure AcceptedReport where
  /-- The accepted claim. -/
  claim : Claim
  /-- The census the plan was built from. -/
  census : Census
  /-- The plan's job keys in slot order. -/
  jobs : Array JobKey
  /-- The accepted observation of each slot, keyed by slot index. -/
  results : ExtTreeMap Nat JobObservation

/-- The report of an acceptance: its claim, census, plan jobs and result entries, unchanged
(`accepted_report_identity`). -/
def Accepted.report {c : Claim} {i : Census} {p : Plan c i} {roles : CensusRoles i}
    {s : ResultTable p} (_ : Accepted p roles s) : AcceptedReport :=
  ⟨c, i, p.jobs, s.entries⟩

/-- Exact report identity is by construction, not reconstructed from diagnostics or counts. -/
theorem accepted_report_identity {c : Claim} {i : Census} {p : Plan c i} {roles : CensusRoles i}
    {s : ResultTable p} (a : Accepted p roles s) :
    a.report.claim = c ∧ a.report.census = i ∧ a.report.jobs = p.jobs ∧ a.report.results = s.entries :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Every populated entry is an exact planned key, with no out-of-plan observations. -/
theorem result_bound {c : Claim} {i : Census} (p : Plan c i) (s : ResultTable p)
    (slot : Nat) (o : JobObservation) (h : s.entries[slot]? = some o) :
    slot < p.jobs.size ∧ p.jobs[slot]? = some o.key ∧ o.snapshot = c.val.snapshot := by
  have hv := s.valid slot o h
  exact ⟨by simpa [requiredSlots] using hv.1, hv.2⟩

/-- Each required slot has exactly one completed, correctly bound policy observation. -/
theorem accepted_covers_slot {c : Claim} {i : Census} {p : Plan c i} {roles : CensusRoles i}
    {s : ResultTable p} (a : Accepted p roles s) (slot : Nat) (hs : slot < p.jobs.size) :
    ∃ o, s.entries[slot]? = some o ∧ p.jobs[slot]? = some o.key ∧ PolicyOK c i roles o ∧
      ∀ other, s.entries[slot]? = some other → other = o := by
  rcases a.policy slot (by simpa using hs) with ⟨o, ho, hp⟩
  have lookup : s.entries[slot]? = some o := by simpa using ho
  refine ⟨o, lookup, (result_bound p s slot o lookup).2.1, hp, ?_⟩
  intro other hother
  rw [lookup] at hother
  exact (Option.some.inj hother).symm
/-- Collection failures and completed-policy refusals remain distinct. -/
inductive FinalizationFailure where
  /-- A response could not be admitted into the result table (`ResultState.collect`). -/
  | collection (reason : AdmissionFailure)
  /-- The collected table was refused by `accept`. -/
  | acceptance (reason : AcceptanceFailure)
  deriving Repr, DecidableEq

/-- The executable collector's result and acceptance travel together. The input index
retains the full response sequence, including multiplicity, instead of trusting wire flags.
This follows con-leche's checked-record/collection architecture without importing it. -/
structure Finalized {c : Claim} {i : Census} (p : Plan c i) (roles : CensusRoles i)
    (inputs : List (Nat × JobObservation)) where
  /-- The result table collected from `inputs`. -/
  table : ResultTable p
  /-- `table` is what collecting every input into the empty table returns. -/
  collected : ResultState.collect .empty inputs = .ok table
  /-- The acceptance of `table`. -/
  accepted : Accepted p roles table

/-- The sole pure finalization path collects every response, then recomputes the approved
policies for every independently required slot. Neither stage can supply a shorter plan. -/
def finalize {c : Claim} {i : Census} (p : Plan c i) (roles : CensusRoles i)
    (inputs : List (Nat × JobObservation)) : Except FinalizationFailure (Finalized p roles inputs) :=
  match hc : ResultState.collect (bound := ResultBound p) .empty inputs with
  | .error failure => .error (.collection failure)
  | .ok table => match accept p roles table with
    | .error failure => .error (.acceptance failure)
    | .ok accepted => .ok ⟨table, hc, accepted⟩

/-- A collector refusal is the exact finalization refusal, before policy evaluation. -/
theorem finalize_collection_error {c : Claim} {i : Census} (p : Plan c i)
    (roles : CensusRoles i) (inputs : List (Nat × JobObservation)) (failure : AdmissionFailure)
    (hc : ResultState.collect (required := requiredSlots p) (bound := ResultBound p) .empty inputs = .error failure) :
    finalize p roles inputs = .error (.collection failure) := by
  unfold finalize
  split
  next reason he => rw [hc] at he; cases he; rfl
  next table he => rw [hc] at he; contradiction

/-- Once the exact collector returns a table, finalization uses precisely its acceptance.
This equality also binds IO phase attribution to the sole pure finalizer. -/
theorem finalize_of_collected {c : Claim} {i : Census} (p : Plan c i)
    (roles : CensusRoles i) (inputs : List (Nat × JobObservation)) (table : ResultTable p)
    (hc : ResultState.collect .empty inputs = .ok table) :
    finalize p roles inputs = (match accept p roles table with
      | .error failure => .error (.acceptance failure)
      | .ok accepted => .ok ⟨table, hc, accepted⟩) := by
  unfold finalize
  split
  next failure he => rw [hc] at he; contradiction
  next observed he =>
    have eq : observed = table := Except.ok.inj (he.symm.trans hc)
    subst observed
    rfl

/-- Changing only the completeness decision preserves the whole finalizer, including
collection errors, their precedence, the collected table and the exact accepted report.
Instantiate `decision` with the former structural decision for old/new correspondence. -/
theorem finalize_decision_eq {c : Claim} {i : Census} (p : Plan c i) (roles : CensusRoles i)
    (inputs : List (Nat × JobObservation))
    (decision : ∀ s : ResultTable p, Decidable (CompleteFor p s)) :
    finalize p roles inputs =
      (match hc : ResultState.collect (bound := ResultBound p) .empty inputs with
      | .error failure => .error (.collection failure)
      | .ok table =>
        match @dite (Except AcceptanceFailure (Accepted p roles table))
          (CompleteFor p table) (decision table)
          (fun complete => if hp : AllPolicyOK p roles table then .ok ⟨complete, hp⟩
            else .error .policyViolation)
          (fun _ => .error .incomplete) with
        | .error failure => .error (.acceptance failure)
        | .ok accepted => .ok ⟨table, hc, accepted⟩) := by
  simp only [← accept_decision_eq]
  rfl

/-- A finalized report is projected from its actual Accepted evidence. -/
def Finalized.report {c : Claim} {i : Census} {p : Plan c i} {roles : CensusRoles i}
    {inputs : List (Nat × JobObservation)} (result : Finalized p roles inputs) : AcceptedReport :=
  result.accepted.report

/-- Independent specification over the raw response sequence: no duplicate, unknown,
or misbound observations, and actual policy evidence for each required plan position. -/
def InputsOK {c : Claim} {i : Census} (p : Plan c i) (roles : CensusRoles i)
    (inputs : List (Nat × JobObservation)) : Prop :=
  ResultState.BatchOK (ResultState.empty : ResultTable p) inputs ∧
  ∀ slot ∈ List.range p.jobs.size,
    ∃ o, (slot, o) ∈ inputs ∧ PolicyOK c i roles o

/-- Finalized coverage refers to actual supplied observations, not just abstract state
invariants. Exact report identity and the full required domain are retained. -/
theorem finalized_covers_input {c : Claim} {i : Census} {p : Plan c i}
    {roles : CensusRoles i} {inputs : List (Nat × JobObservation)}
    (result : Finalized p roles inputs) (slot : Nat) (hs : slot < p.jobs.size) :
    ∃ o, (slot, o) ∈ inputs ∧ p.jobs[slot]? = some o.key ∧ PolicyOK c i roles o := by
  obtain ⟨o, lookup, key, policy, _⟩ := accepted_covers_slot result.accepted slot hs
  exact ⟨o, (ResultState.collect_empty_lookup inputs result.table result.collected slot o).mp lookup,
    key, policy⟩

/-- Completeness and policies on a collected table correspond exactly to the supplied
observations for every required slot. External producer truth is not assumed by this lemma. -/
private theorem collected_policy_iff {c : Claim} {i : Census} (p : Plan c i)
    (roles : CensusRoles i) (inputs : List (Nat × JobObservation)) (table : ResultTable p)
    (hc : ResultState.collect .empty inputs = .ok table) :
    CompleteFor p table ∧ AllPolicyOK p roles table ↔
      ∀ slot ∈ List.range p.jobs.size, ∃ o, (slot, o) ∈ inputs ∧ PolicyOK c i roles o := by
  constructor
  · rintro ⟨_, policy⟩ slot member
    obtain ⟨o, ho, hp⟩ := policy slot member
    exact ⟨o, (ResultState.collect_empty_lookup inputs table hc slot o).mp ho, hp⟩
  · intro policy
    have actual : AllPolicyOK p roles table := by
      intro slot member
      obtain ⟨o, ho, hp⟩ := policy slot member
      exact ⟨o, (ResultState.collect_empty_lookup inputs table hc slot o).mpr ho, hp⟩
    refine ⟨⟨p.valid, ?_⟩, actual⟩
    intro slot member
    obtain ⟨o, ho, hp⟩ := actual slot member
    exact ⟨o, ho, hp.2.2.1⟩

/-- Exact whole-domain success theorem for the executable collector/finalizer. This is
universal over response count/order/payloads and the independently supplied claim/plan;
no worker-success, failure-array, or producer-completeness premise is used. -/
theorem finalize_iff {c : Claim} {i : Census} (p : Plan c i) (roles : CensusRoles i)
    (inputs : List (Nat × JobObservation)) :
    (∃ result, finalize p roles inputs = .ok result) ↔ InputsOK p roles inputs := by
  constructor
  · rintro ⟨result, _⟩
    refine ⟨(ResultState.collect_success_iff inputs (ResultState.empty : ResultTable p)).mp
      ⟨result.table, result.collected⟩, ?_⟩
    exact (collected_policy_iff p roles inputs result.table result.collected).mp
      ⟨result.accepted.complete, result.accepted.policy⟩
  · rintro ⟨batch, policy⟩
    obtain ⟨table, hc⟩ := (ResultState.collect_success_iff inputs (ResultState.empty : ResultTable p)).mpr batch
    obtain ⟨accepted, ha⟩ := accept_complete p roles table
      ((collected_policy_iff p roles inputs table hc).mpr policy)
    refine ⟨⟨table, hc, accepted⟩, ?_⟩
    unfold finalize
    split
    next failure he => rw [hc] at he; contradiction
    next observed he =>
      have eq : observed = table := Except.ok.inj (he.symm.trans hc)
      subst observed
      rw [ha]

/-- Whole-run transfer from retained source occurrences to the actual new input list.
An aggregate admission/root observation may supply several environment slots. Every
source occurrence supplies at least one output, and the exact output occurrence list
covers each required slot once. Local transfer assumes old local judgments and explicit
data coherence; global stages retain their actual predicates. This is the existing
collector/finalizer, not a second acceptance evaluator. -/
theorem finalize_reindexed {c : Claim} {i : Census} (p : Plan c i) (roles : CensusRoles i)
    (original inputs : List (Nat × JobObservation))
    (reindex : (Nat × JobObservation) → List (Nat × JobObservation))
    (exactInputs : inputs = original.flatMap reindex)
    (retained : ∀ source ∈ original, reindex source ≠ [])
    (positions : inputs.map Prod.fst = List.range p.jobs.size)
    (sourceStatus : ∀ source ∈ original,
      source.2.key.claim = c ∧ source.2.snapshot = c.val.snapshot ∧ source.2.completion = .completed)
    (binding : ∀ source ∈ original, ∀ entry ∈ reindex source,
      p.jobs[entry.1]? = some entry.2.key ∧ entry.2.key.claim = c ∧
      entry.2.snapshot = source.2.snapshot ∧ entry.2.completion = source.2.completion ∧
      entry.2.key.stage = source.2.key.stage)
    (localTransfer : ∀ source ∈ original, ∀ entry ∈ reindex source,
      ∀ environment subject, entry.2.key.subject = .environment environment subject →
      ∃ slot : Fin i.environments.size, i.environments[slot].request.key = environment ∧
        ∃ flattened : EnvironmentCensus, ∃ oldRoles : Roles flattened.policy,
          LocalEvidenceTransfer c i.environments[slot] flattened (roles slot) oldRoles
            entry.2.key.stage subject source.2.evidence entry.2.evidence ∧
          LocalStageOK c flattened oldRoles source.2.key.stage subject source.2.evidence)
    (globalTransfer : ∀ source ∈ original, ∀ entry ∈ reindex source,
      (∀ environment subject, entry.2.key.subject ≠ .environment environment subject) →
      ∃ previous : Census, ∃ oldRoles : CensusRoles previous,
        GlobalEvidenceTransfer previous i entry.2.key.stage entry.2.key.subject
          source.2.evidence entry.2.evidence ∧
        StageOK c previous oldRoles entry.2.key source.2.evidence) :
    (∀ source ∈ original, ∃ entry ∈ inputs, entry ∈ reindex source) ∧
      ∃ result, finalize p roles inputs = .ok result := by
  have provenance (entry) (member : entry ∈ inputs) :
      ∃ source ∈ original, entry ∈ reindex source := by
    rw [exactInputs] at member
    exact List.mem_flatMap.mp member
  have policies (entry) (member : entry ∈ inputs) : PolicyOK c i roles entry.2 := by
    obtain ⟨source, hs, he⟩ := provenance entry member
    obtain ⟨_, claim, snapshot, completion, stage⟩ := binding source hs entry he
    refine ⟨claim, snapshot.trans (sourceStatus source hs).2.1,
      completion.trans (sourceStatus source hs).2.2, ?_⟩
    cases subjectEq : entry.2.key.subject with
    | environment environment subject =>
      obtain ⟨slot, key, flattened, oldRoles, transfer, old⟩ :=
        localTransfer source hs entry he environment subject subjectEq
      rw [← stage] at old
      have localOK := transfer.sound old
      have index := census_environment_index c i p.valid.2.2.1 slot
      have environmentOK := (environmentStageOK_at c i roles slot index
        entry.2.key.stage subject entry.2.evidence).mpr localOK
      rw [key] at environmentOK
      simpa only [StageOK, subjectEq] using environmentOK
    | scope =>
      obtain ⟨previous, oldRoles, transfer, valid⟩ :=
        globalTransfer source hs entry he (by simp [subjectEq])
      exact transfer.sound oldRoles roles entry.2.key valid
    | fence fence =>
      obtain ⟨previous, oldRoles, transfer, valid⟩ :=
        globalTransfer source hs entry he (by simp [subjectEq])
      exact transfer.sound oldRoles roles entry.2.key valid
  refine ⟨?_, (finalize_iff p roles inputs).mpr ⟨?_, ?_⟩⟩
  · intro source hs
    have nonempty := retained source hs
    cases output : reindex source with
    | nil => exact False.elim (nonempty output)
    | cons entry rest =>
      have he : entry ∈ reindex source := by simp [output]
      exact ⟨entry, by rw [exactInputs]; exact List.mem_flatMap.mpr ⟨source, hs, he⟩, by simp⟩
  · refine ⟨by rw [positions]; exact List.nodup_range, ?_⟩
    intro entry member
    have slotMember : entry.1 ∈ List.range p.jobs.size := by
      rw [← positions]
      exact List.mem_map.mpr ⟨entry, member, rfl⟩
    obtain ⟨source, hs, he⟩ := provenance entry member
    have bound := binding source hs entry he
    exact ⟨by simpa [requiredSlots] using slotMember, by simp [ResultState.empty],
      bound.1, bound.2.2.1.trans (sourceStatus source hs).2.1⟩
  · intro slot member
    rw [← positions] at member
    obtain ⟨entry, he, position⟩ := List.mem_map.mp member
    refine ⟨entry.2, ?_, policies entry he⟩
    simpa only [← position] using he

/-- Whole singleton compatibility: identical observations and slot occurrences preserve
all former local judgments and the unchanged global obligations through finalize. -/
theorem finalize_singleton_transfer {c : Claim} {i : Census} (p : Plan c i) (roles : CensusRoles i)
    (singleton : i.environments.size = 1)
    (inputs : List (Nat × JobObservation))
    (positions : inputs.map Prod.fst = List.range p.jobs.size)
    (status : ∀ entry ∈ inputs, entry.2.snapshot = c.val.snapshot ∧ entry.2.completion = .completed)
    (binding : ∀ entry ∈ inputs, p.jobs[entry.1]? = some entry.2.key ∧ entry.2.key.claim = c)
    (localJudgments : ∀ entry ∈ inputs, ∀ environment subject,
      entry.2.key.subject = .environment environment subject →
      let slot : Fin i.environments.size := ⟨0, by rw [singleton]; exact Nat.zero_lt_one⟩
      environment = i.environments[slot].request.key ∧
        LocalStageOK c i.environments[slot] (roles slot) entry.2.key.stage subject entry.2.evidence)
    (globalJudgments : ∀ entry ∈ inputs,
      (∀ environment subject, entry.2.key.subject ≠ .environment environment subject) →
      StageOK c i roles entry.2.key entry.2.evidence) :
    ∃ result, finalize p roles inputs = .ok result := by
  apply (finalize_reindexed p roles inputs inputs (fun entry => [entry])
    (by simp) (by simp) positions (fun entry he => ⟨(binding entry he).2, status entry he⟩) ?_ ?_ ?_).2
  · intro source hs entry he
    simp only [List.mem_singleton] at he
    subst entry
    exact ⟨(binding source hs).1, (binding source hs).2, rfl, rfl, rfl⟩
  · intro source hs entry he environment subject subjectEq
    simp only [List.mem_singleton] at he
    subst entry
    obtain ⟨key, judgment⟩ := localJudgments source hs environment subject subjectEq
    exact ⟨⟨0, by rw [singleton]; exact Nat.zero_lt_one⟩, key.symm, _, _, LocalEvidenceTransfer.refl judgment, judgment⟩
  · intro source hs entry he global
    simp only [List.mem_singleton] at he
    subst entry
    have judgment := globalJudgments source hs global
    exact ⟨i, roles, GlobalEvidenceTransfer.refl roles source.2.key source.2.evidence global judgment,
      judgment⟩

/-- The request index remains fixed through the operational boundary. The census is
obtained externally, while its plan, roles, collected observations and acceptance are
all checked here. Constructors require every proof; serialized reports carry none. -/
structure AcceptedRun (c : Claim) where
  /-- The census the external collector reported for `c`. -/
  census : Census
  /-- The admitted plan of `c` over `census`. -/
  plan : Plan c census
  /-- The generated-role observations (`Roles`) of each environment of `census`. -/
  roles : CensusRoles census
  /-- Every worker response as a slot and its observation, in arrival order, duplicates kept. -/
  inputs : List (Nat × JobObservation)
  /-- The collection and acceptance of `inputs` under `plan` and `roles`. -/
  result : Finalized plan roles inputs

/-- Renderers receive the report of the same accepted request, never an independently
constructed report or a status inferred from an empty diagnostic array. -/
def AcceptedRun.report {c : Claim} (run : AcceptedRun c) : AcceptedReport := run.result.report

/-- Projection cannot replace the requested scope/mode/snapshot. -/
theorem acceptedRun_claim {c : Claim} (run : AcceptedRun c) : run.report.claim = c := rfl

/-- The report carries every original environment packet unchanged, with the exact
coordinator request occurrences validated by the one full-project plan. -/
theorem acceptedRun_environment_inventory {c : Claim} (run : AcceptedRun c) :
    run.report.census = run.census ∧
    run.census.environments.map (·.request) = run.census.requests ∧
    run.census.modules = run.census.environments.flatMap (·.modules) :=
  ⟨rfl, (census_exact_requests c run.census run.plan.valid.2.2.1),
    (census_exact_modules c run.census run.plan.valid.2.2.1).1⟩

/-- Every accepted environment observation uses that environment's inventory and roles.
Full job/snapshot binding and occurrence uniqueness remain the original collector theorem. -/
theorem accepted_environment_resolves {c : Claim} {i : Census} {p : Plan c i}
    {roles : CensusRoles i} {s : ResultTable p} (accepted : Accepted p roles s)
    (slot : Nat) (bound : slot < p.jobs.size) (observation : JobObservation)
    (observed : s.entries[slot]? = some observation)
    (environment : EnvironmentKey) (subject : LocalJobSubject)
    (subjectEq : observation.key.subject = .environment environment subject) :
    ∃ localSlot : Fin i.environments.size, localSlot.val = environment.index ∧
      i.environments[localSlot].request.key = environment ∧
      LocalStageOK c i.environments[localSlot] (roles localSlot)
        observation.key.stage subject observation.evidence := by
  obtain ⟨o, ho, _, policy, _⟩ := accepted_covers_slot accepted slot bound
  have same : o = observation := Option.some.inj (ho.symm.trans observed)
  subst o
  have stage := policy.2.2.2
  simp only [StageOK, subjectEq] at stage
  exact environmentStageOK_resolves c i roles environment observation.key.stage subject observation.evidence stage

/-- Even roots with identical imported names must be the exact structural root of the
bound environment and satisfy every execution mode requested by that environment. -/
theorem accepted_execution_resolves {c : Claim} {i : Census} {p : Plan c i}
    {roles : CensusRoles i} {s : ResultTable p} (accepted : Accepted p roles s)
    (slot : Nat) (bound : slot < p.jobs.size) (observation : JobObservation)
    (observed : s.entries[slot]? = some observation)
    (environment : EnvironmentKey) (key : RootKey) (root : ExecutionRoot)
    (subjectEq : observation.key.subject = .environment environment (.root key))
    (stageEq : observation.key.stage = .execution) (evidenceEq : observation.evidence = .execution root) :
    ∃ localSlot : Fin i.environments.size, localSlot.val = environment.index ∧
      i.environments[localSlot].request.key = environment ∧
      root ∈ i.environments[localSlot].execution.roots ∧
      root.name = key.name.name ∧ root.module = key.moduleKey.name.name ∧
      ∀ request ∈ rootRequests c i.environments[localSlot] root.name,
        root.unresolved = #[] ∧ ∀ boundary ∈ root.boundaries, BoundaryOK request boundary := by
  obtain ⟨localSlot, position, identity, policy⟩ :=
    accepted_environment_resolves accepted slot bound observation observed environment (.root key) subjectEq
  rw [stageEq, evidenceEq] at policy
  exact ⟨localSlot, position, identity, policy⟩

/-- Combined ordinary acceptance retains both independently complete plans, indexed by
one exact snapshot and the requested Markdown inventory. Neither component is promoted
to the other's scope; negative/teaching fences remain expectation evidence. -/
structure CombinedAccepted (projectClaim documentClaim : Claim) (documents : Array SourceSnapshot) where
  /-- The accepted whole-project run. -/
  project : AcceptedRun projectClaim
  /-- The accepted documentation-example run. -/
  documentation : AcceptedRun documentClaim
  /-- The project run's claim has the whole-project scope. -/
  projectScope : projectClaim.val.scope = .project
  /-- The project run's claim is a fresh project audit. -/
  projectMode : projectClaim.val.mode = .freshProject
  /-- The documentation run's claim covers exactly `documents`. -/
  documentScope : documentClaim.val.scope = .documentation documents
  /-- The documentation run's claim checks documentation examples. -/
  documentMode : documentClaim.val.mode = .documentationExample
  /-- Both claims name the same source snapshot. -/
  sameSnapshot : projectClaim.val.snapshot = documentClaim.val.snapshot

/-- Pair a project run and a documentation run when their claims have the required scopes and
modes and the same snapshot; otherwise an error naming the mismatch classes. -/
def combineAccepted {pc dc : Claim} (documents : Array SourceSnapshot)
    (project : AcceptedRun pc) (documentation : AcceptedRun dc) :
    Except String (CombinedAccepted pc dc documents) :=
  if h : pc.val.scope = .project ∧ pc.val.mode = .freshProject ∧
      dc.val.scope = .documentation documents ∧ dc.val.mode = .documentationExample ∧
      pc.val.snapshot = dc.val.snapshot then
    .ok ⟨project, documentation, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  else .error "combined acceptance scope, mode, document inventory or snapshot mismatch"

/-- Composition preserves both exact accepted reports and their common snapshot. -/
theorem combined_reports_same_snapshot {pc dc : Claim} {documents : Array SourceSnapshot}
    (accepted : CombinedAccepted pc dc documents) :
    accepted.project.report.claim = pc ∧ accepted.documentation.report.claim = dc ∧
      accepted.project.report.claim.val.snapshot = accepted.documentation.report.claim.val.snapshot :=
  ⟨rfl, rfl, accepted.sameSnapshot⟩

/-- Both whole-domain capstones remain available at the composed public success boundary. -/
theorem combined_policy {pc dc : Claim} {documents : Array SourceSnapshot}
    (accepted : CombinedAccepted pc dc documents) :
    (CompleteFor accepted.project.plan accepted.project.result.table ∧
      AllPolicyOK accepted.project.plan accepted.project.roles accepted.project.result.table) ∧
    (CompleteFor accepted.documentation.plan accepted.documentation.result.table ∧
      AllPolicyOK accepted.documentation.plan accepted.documentation.roles accepted.documentation.result.table) :=
  ⟨⟨accepted.project.result.accepted.complete, accepted.project.result.accepted.policy⟩,
    ⟨accepted.documentation.result.accepted.complete, accepted.documentation.result.accepted.policy⟩⟩

end RegulaPolicy
