import Regula.Contract
import Regula.MaterialClaim

/-!
Proof-bearing core of the `AuditApp` complete-application dogfooding surface:
a bounded-slot limiter (a rate limiter without time). The module owns the
`Limiter` state whose single invariant — `inUse ≤ capacity` — is a proof
field, the admission boundary that validates a requested capacity before any
state exists, the update boundaries `grant`/`release`/`reset`, and the
fold-level composition `run` of finite update scripts, and `runChecked`,
a strict state/error interpreter that retains the successful prefix on refusal.

The theorems concern these exact computable definitions. The `auditApp`
executable calls `executeChecked` and the strict interpreter; `run` remains
the total fold used to specify successful prefixes. No declaration is promoted
to a native-runtime or external-system claim, and no hypothesis is hidden:
assumptions appear as binders or proof fields. This module directly imports only the two
published checker interfaces: the proof-requiring executable-contract type and the
`@[regula_material]` registration attribute, whose import closure brings in Lean's attribute
framework; no definition or proof here uses it. Its material
claims `RequiredContracts`, `requiredContracts` and `checkedExecutable` are registered with
`@[regula_material]`, so RG5002/RG5003 require each to carry a docstring with a nonempty Intent
section (standard §5.2); whether each Intent states the right requirement remains
semantic review.

Reuse account (standard §1.4, §3.2.5): the state, interpreter, and
monad stack reuse `Option`, `List.foldl`, `ExceptT`, and `StateM` from the
prelude. The bespoke types are `Limiter` (the proof-bearing state), `Op`,
`Fits` (this application's per-prefix precondition, which no Core/Std/Mathlib
declaration states), `CheckedRun` (an abbreviation for the checked run type),
and `RequiredContracts` (the `Prop`-valued bundle of this application's
required contract propositions, consumed through `Regula.Contract`);
the operations and their theorems are this application's own semantics.
Mathlib is deliberately not imported by this module: its pure limiter operations
and proofs use the prelude and the contract interface, with arithmetic discharged
by `omega`. The separately claimed `AuditApp.Refinement` imports Mathlib for
finite-path relations. `Glossary.Server` is the corresponding teaching model;
this module supplies the application definitions the executable runs. Every theorem is
stated against the exported API; the script-indexed theorems are proved by
induction on the script or on its length, the single-operation theorems by
unfolding and case analysis, and no proof replays an enumeration.
-/

namespace AuditApp

/-- A limiter state whose single documented invariant — at most `capacity`
slots in use — is a proof field. Every value that type-checks satisfies the
invariant, so no caller can construct a state that violates it. -/
structure Limiter where
  capacity : Nat
  inUse : Nat
  bounded : inUse ≤ capacity

/-- Admission boundary: a requested capacity becomes a state only when it is
positive. A zero capacity is rejected, so an admitted state satisfies
`0 < capacity` (proved in `admit_sound`) in addition to the structural
invariant. -/
def admit (capacity : Nat) : Option Limiter :=
  if _h : 0 < capacity then
    some { capacity, inUse := 0, bounded := Nat.zero_le _ }
  else
    none

/-- Admission establishes the invariant and positivity: every state obtained
from `admit` is fresh (no slots in use) over a positive capacity. -/
theorem admit_sound {capacity : Nat} {l : Limiter} (h : admit capacity = some l) :
    0 < l.capacity ∧ l.inUse = 0 := by
  unfold admit at h
  split at h
  next hpos =>
    injection h with hl
    subst hl
    exact ⟨hpos, rfl⟩
  next => nomatch h

/-- Admission rejects a zero capacity; `admit_exact` states the converse. -/
theorem admit_none {capacity : Nat} (h : capacity = 0) : admit capacity = none := by
  subst h
  unfold admit
  rw [dite_eq_right (Nat.lt_irrefl 0)]

/-- Admission preserves the requested capacity and succeeds exactly for positive
requests, returning the fresh state. This also rules out rejecting every request. -/
theorem admit_exact (capacity : Nat) :
    admit capacity = if 0 < capacity then
      some ⟨capacity, 0, Nat.zero_le capacity⟩ else none := rfl

/-- Update boundary: grant one slot while one is free. The new proof field is
exactly the guard `inUse < capacity`, which is `inUse + 1 ≤ capacity` by
definition of `Nat.lt`; a full limiter grants nothing. -/
def grant (l : Limiter) : Option Limiter :=
  if h : l.inUse < l.capacity then
    some { l with inUse := l.inUse + 1, bounded := h }
  else
    none

/-- Exact post-state of a successful grant: the capacity is untouched and the
in-use count grows by one. Together with the structure's proof field this
gives invariant preservation, stated here as observable behavior rather than
as a projection. -/
theorem grant_some {l l' : Limiter} (h : grant l = some l') :
    l'.capacity = l.capacity ∧ l'.inUse = l.inUse + 1 := by
  unfold grant at h
  split at h
  next =>
    injection h with hl
    subst hl
    exact ⟨rfl, rfl⟩
  next => nomatch h

/-- A grant is refused exactly when the limiter is full. -/
theorem grant_none {l : Limiter} : grant l = none ↔ l.inUse = l.capacity := by
  unfold grant
  split
  next hlt =>
    constructor
    · intro h
      nomatch h
    · intro h
      exact absurd h (Nat.ne_of_lt hlt)
  next hnl =>
    have hb : l.inUse ≤ l.capacity := l.bounded
    have heq : l.inUse = l.capacity := by omega
    exact ⟨fun _ => heq, fun _ => rfl⟩

/-- Update boundary: release one slot while one is in use; releasing an idle
limiter leaves it unchanged. The invariant is preserved because
`inUse - 1 ≤ inUse ≤ capacity`. -/
def release (l : Limiter) : Limiter :=
  if l.inUse = 0 then l
  else { l with inUse := l.inUse - 1, bounded := Nat.le_trans (Nat.sub_le _ _) l.bounded }

/-- Releasing a busy limiter frees exactly one slot. -/
theorem release_of_pos {l : Limiter} (h : 0 < l.inUse) :
    (release l).inUse = l.inUse - 1 := by
  unfold release
  rw [ite_eq_right (by omega : ¬ l.inUse = 0)]

/-- Releasing an idle limiter is the identity transition. -/
theorem release_of_zero {l : Limiter} (h : l.inUse = 0) : release l = l := by
  unfold release
  rw [ite_eq_left h]

/-- Update boundary: reset to idle, keeping the capacity. -/
def reset (l : Limiter) : Limiter :=
  { l with inUse := 0, bounded := Nat.zero_le _ }

/-- A reset limiter has no slots in use. -/
theorem reset_inUse (l : Limiter) : (reset l).inUse = 0 := rfl

/-- Reset preserves the capacity. -/
theorem reset_capacity (l : Limiter) : (reset l).capacity = l.capacity := rfl

/-- The update vocabulary a caller can apply to a limiter. A `grant` can be
refused; `release` and `reset` are total. -/
inductive Op where
  | grant
  | release
  | reset
  deriving DecidableEq

/-- One state transition: a refused grant leaves the state untouched, the
total updates apply directly. -/
def step (l : Limiter) : Op → Limiter
  | .grant => (grant l).getD l
  | .release => release l
  | .reset => reset l

/-- Total interpreter: run a finite script left-to-right, continuing after a
refused grant. This ordinary `List.foldl` also specifies successful prefixes
of the strict `runChecked` interpreter used by the shell. -/
def run (ops : List Op) (l : Limiter) : Limiter := ops.foldl step l

/-- No single update ever changes the capacity. -/
theorem step_capacity (l : Limiter) (op : Op) : (step l op).capacity = l.capacity := by
  cases op
  · change ((grant l).getD l).capacity = l.capacity
    by_cases hlt : l.inUse < l.capacity
    · unfold grant
      rw [dite_eq_left hlt]
      rfl
    · unfold grant
      rw [dite_eq_right hlt]
      rfl
  · change (release l).capacity = l.capacity
    unfold release
    split <;> rfl
  · rfl

/-- Running any finite script preserves the capacity. -/
theorem run_capacity (l : Limiter) (ops : List Op) :
    (run ops l).capacity = l.capacity := by
  induction ops generalizing l with
  | nil => rfl
  | cons op rest ih =>
    change (run rest (step l op)).capacity = l.capacity
    exact (ih (step l op)).trans (step_capacity l op)

/-- Checked composition: running any finite sequence of updates preserves the
admitted invariant — the in-use count never exceeds the fixed capacity. This
is a safety property of the actual executable `run`, proved by induction
over the fold, not a proof-field projection. -/
theorem run_bounded (l : Limiter) (ops : List Op) :
    (run ops l).inUse ≤ l.capacity := by
  induction ops generalizing l with
  | nil => exact l.bounded
  | cons op rest ih =>
    change (run rest (step l op)).inUse ≤ l.capacity
    rw [← step_capacity l op]
    exact ih (step l op)

/-- Exact composed specification for a burst of grants: while the burst fits
in the remaining capacity, every grant succeeds and the in-use count grows by
exactly the burst length. -/
theorem run_replicate_grant (l : Limiter) (n : Nat) (h : l.inUse + n ≤ l.capacity) :
    (run (List.replicate n Op.grant) l).inUse = l.inUse + n := by
  induction n generalizing l with
  | zero => rfl
  | succ k ih =>
    have hlt : l.inUse < l.capacity := by omega
    have hin : (step l Op.grant).inUse = l.inUse + 1 := by
      change ((grant l).getD l).inUse = l.inUse + 1
      unfold grant
      rw [dite_eq_left hlt]
      rfl
    have hcap : (step l Op.grant).capacity = l.capacity := step_capacity l Op.grant
    have h' : (step l Op.grant).inUse + k ≤ (step l Op.grant).capacity := by
      rw [hin, hcap]
      omega
    change (run (List.replicate k Op.grant) (step l Op.grant)).inUse = l.inUse + (k + 1)
    rw [ih _ h', hin]
    omega

/-- The strict interpreter reports a full grant as an error. `ExceptT` outside
`StateM` retains the last state on error; `Unit` is the sole refusal reason. -/
abbrev CheckedRun := ExceptT Unit (StateM Limiter) Unit

/-- Execute one operation, retaining the input state on a refused grant. -/
def checkedStep (op : Op) : CheckedRun := fun l =>
  match op with
  | .grant => match grant l with
    | none => (.error (), l)
    | some next => (.ok (), next)
  | .release => (.ok (), release l)
  | .reset => (.ok (), reset l)

/-- Execute left-to-right and stop at the first refusal. Earlier successful
updates remain visible; the unprocessed suffix has no effect. -/
def runChecked : List Op → CheckedRun
  | [] => pure ()
  | op :: rest => do
    checkedStep op
    runChecked rest

/-- Exact one-step result: the only refusal is a grant at capacity; every
successful operation performs the existing `step`, including its frame. -/
theorem checkedStep_exact (op : Op) (l : Limiter) :
    checkedStep op l = if op = .grant ∧ l.inUse = l.capacity then
      (.error (), l) else (.ok (), step l op) := by
  cases op with
  | grant =>
    by_cases h : l.inUse = l.capacity
    · rw [ite_eq_left ⟨rfl, h⟩]
      simp [checkedStep, grant_none.mpr h]
    · rw [ite_eq_right (by simp [h])]
      have hn : grant l ≠ none := fun he => h (grant_none.mp he)
      cases hg : grant l with
      | none => exact False.elim (hn hg)
      | some next => simp [checkedStep, step, hg]
  | release => simp [checkedStep, step]
  | reset => simp [checkedStep, step]

/-- Pure bind's exact state/error semantics, specialized to this interpreter.
An error retains its state and skips the continuation. -/
theorem runChecked_cons (op : Op) (ops : List Op) (l : Limiter) :
    runChecked (op :: ops) l = if op = .grant ∧ l.inUse = l.capacity then
      (.error (), l) else runChecked ops (step l op) := by
  change (ExceptT.bindCont (fun _ => runChecked ops) (checkedStep op l).1)
    (checkedStep op l).2 = _
  rw [checkedStep_exact]
  split <;> rfl

/-- A script fits when each grant has space at its own prefix state. This
precondition uses the original total `step`; it does not just restate success. -/
def Fits : List Op → Limiter → Prop
  | [], _ => True
  | op :: ops, l => (op = .grant → l.inUse < l.capacity) ∧ Fits ops (step l op)

/-- Success is equivalent to space at every grant's prefix, and returns exactly
`run ops l`. Thus an always-failing or idle interpreter cannot meet the contract. -/
theorem runChecked_success (ops : List Op) (l final : Limiter) :
    runChecked ops l = (.ok (), final) ↔ Fits ops l ∧ final = run ops l := by
  induction ops generalizing l with
  | nil =>
    change (Except.ok (), l) = (Except.ok (), final) ↔ True ∧ final = l
    simp only [Prod.mk.injEq, true_and, eq_comm]
  | cons op ops ih =>
    rw [runChecked_cons]
    by_cases h : op = .grant ∧ l.inUse = l.capacity
    · rw [ite_eq_left h]
      have hn : ¬ (op = .grant → l.inUse < l.capacity) := by
        intro hf
        have := hf h.1
        omega
      change (Except.error (), l) = (Except.ok (), final) ↔
        ((op = .grant → l.inUse < l.capacity) ∧ Fits ops (step l op)) ∧ _
      simp only [Prod.mk.injEq, hn, false_and]
      constructor
      · intro he; cases he.1
      · intro he; exact False.elim he
    · rw [ite_eq_right h, ih]
      have hp : op = .grant → l.inUse < l.capacity := by
        intro ho
        have hb := l.bounded
        have hn : l.inUse ≠ l.capacity := fun he => h ⟨ho, he⟩
        omega
      exact ⟨fun ⟨hf, he⟩ => ⟨⟨hp, hf⟩, he⟩, fun ⟨⟨_, hf⟩, he⟩ => ⟨hf, he⟩⟩

/-- Concatenation is monadic composition: successful prefix state feeds the
suffix; prefix error and its state are retained without executing the suffix. -/
theorem runChecked_append (xs ys : List Op) (l : Limiter) :
    runChecked (xs ++ ys) l = match runChecked xs l with
      | (.error e, s) => (.error e, s)
      | (.ok _, s) => runChecked ys s := by
  induction xs generalizing l with
  | nil => rfl
  | cons op xs ih =>
    simp only [List.cons_append, runChecked_cons]
    split
    · rfl
    · exact ih _

/-- The first post-state supplies the second precondition. Both fitting scripts
compose to exactly the successive total runs, for every initial admitted value. -/
theorem runChecked_compose_success (xs ys : List Op) (l : Limiter)
    (hx : Fits xs l) (hy : Fits ys (run xs l)) :
    runChecked (xs ++ ys) l = (.ok (), run ys (run xs l)) := by
  rw [runChecked_append, (runChecked_success xs l _).mpr ⟨hx, rfl⟩]
  exact (runChecked_success ys (run xs l) _).mpr ⟨hy, rfl⟩

/-- Every refusal identifies a successful prefix followed by a grant at full
capacity. The returned state is precisely that prefix's state, not the initial
state and not the result of executing the remaining suffix. -/
theorem runChecked_error (ops : List Op) (l final : Limiter) :
    runChecked ops l = (.error (), final) ↔
      ∃ before after, ops = before ++ .grant :: after ∧
        Fits before l ∧ final = run before l ∧ final.inUse = final.capacity := by
  induction ops generalizing l with
  | nil =>
    constructor
    · intro h
      cases (Prod.mk.inj h).1
    · rintro ⟨before, after, he, _⟩
      have := congrArg List.length he
      simp at this
  | cons op ops ih =>
    constructor
    · rw [runChecked_cons]
      split
      next h =>
        intro he
        have hf : l = final := (Prod.mk.inj he).2
        subst final
        exact ⟨[], ops, by simp [h.1], trivial, rfl, h.2⟩
      next h =>
        intro he
        obtain ⟨before, after, hs, fits, hf, full⟩ := (ih _).mp he
        have hp : op = .grant → l.inUse < l.capacity := by
          intro ho
          have hb := l.bounded
          have hn : l.inUse ≠ l.capacity := fun he => h ⟨ho, he⟩
          omega
        exact ⟨op :: before, after, by simp [hs], ⟨hp, fits⟩, hf, full⟩
    · rintro ⟨before, after, hs, fits, hf, full⟩
      rw [hs, runChecked_append]
      rw [(runChecked_success before l final).mpr ⟨fits, hf⟩]
      change runChecked (.grant :: after) final = _
      rw [runChecked_cons, ite_eq_left ⟨rfl, full⟩]

/-- Capacity is framed on success and error, including every successful prefix. -/
theorem runChecked_capacity (ops : List Op) (l : Limiter) :
    (runChecked ops l).2.capacity = l.capacity := by
  induction ops generalizing l with
  | nil => rfl
  | cons op ops ih =>
    rw [runChecked_cons]
    split
    · rfl
    · exact (ih _).trans (step_capacity l op)

/-- CLI input policy: parse only the first argument with Lean's `String.toNat?`;
missing or unparsable input selects 2. Admission separately rejects zero. -/
def requestedCapacity (args : List String) : Nat :=
  (args.head?.bind String.toNat?).getD 2

/-- Exact input meaning and fallback. Parsing is Lean's existing natural-number
parser, with no additional normalization; trailing arguments are ignored. -/
theorem requestedCapacity_exact (args : List String) :
    requestedCapacity args = match args with
      | [] => 2
      | arg :: _ => arg.toNat?.getD 2 := by
  cases args <;> rfl

/-- Explicit required propositions for the actual application definitions. These
fields specify admission, each update, dispatch, and composition; their adequacy
is reviewed against the application's intended behavior. The state's bound is
already enforced by `Limiter`, so it needs no duplicate field theorem; with the frame fields
it bounds every script's end state by the created capacity (`within_capacity`).

# Intent
- A slot limiter must never hand out more slots than the capacity it was created with. (discharged by `AuditApp.RequiredContracts.within_capacity`)
- Creation must refuse a zero capacity and start idle.
- A grant must take exactly one free slot, and must be refused only when none is free.
- A release must free one slot when any is in use.
- A reset must free every slot.
- No operation may change the capacity.
- A script must apply its operations in order.
- The strict runner must stop at the first refused grant, keeping exactly the state reached
  before it.
- The command-line capacity is the first argument read as a natural number, defaulting to 2.
- Timing, fairness and the IO shell are deliberately out of scope. -/
@[regula_material]
structure RequiredContracts : Prop where
  admission : ∀ capacity, admit capacity = if 0 < capacity then
    some ⟨capacity, 0, Nat.zero_le capacity⟩ else none
  grant_success : ∀ {l l' : Limiter}, grant l = some l' →
    l'.capacity = l.capacity ∧ l'.inUse = l.inUse + 1
  grant_refusal : ∀ {l : Limiter}, grant l = none ↔ l.inUse = l.capacity
  release_busy : ∀ {l : Limiter}, 0 < l.inUse → (release l).inUse = l.inUse - 1
  release_idle : ∀ {l : Limiter}, l.inUse = 0 → release l = l
  reset_empty : ∀ l, (reset l).inUse = 0
  reset_frame : ∀ l, (reset l).capacity = l.capacity
  dispatch : ∀ l op, step l op = match op with
    | .grant => (grant l).getD l
    | .release => release l
    | .reset => reset l
  composition : ∀ ops l, run ops l = ops.foldl step l
  capacity_frame : ∀ l op, (step l op).capacity = l.capacity
  run_frame : ∀ l ops, (run ops l).capacity = l.capacity
  input_meaning : ∀ args, requestedCapacity args = match args with
    | [] => 2
    | arg :: _ => arg.toNat?.getD 2
  checked_step : ∀ op l, checkedStep op l =
    if op = .grant ∧ l.inUse = l.capacity then
      (.error (), l) else (.ok (), step l op)
  checked_success : ∀ ops l final,
    runChecked ops l = (.ok (), final) ↔ Fits ops l ∧ final = run ops l
  checked_error : ∀ ops l final,
    runChecked ops l = (.error (), final) ↔
      ∃ before after, ops = before ++ .grant :: after ∧
        Fits before l ∧ final = run before l ∧ final.inUse = final.capacity
  checked_composition : ∀ xs ys l,
    runChecked (xs ++ ys) l = match runChecked xs l with
      | (.error e, s) => (.error e, s)
      | (.ok _, s) => runChecked ys s
  checked_frame : ∀ ops l, (runChecked ops l).2.capacity = l.capacity
  burst : ∀ l n, l.inUse + n ≤ l.capacity →
    (run (List.replicate n Op.grant) l).inUse = l.inUse + n

/-- The required contracts bound every script's end state, total or strict, by the capacity
the limiter was created with: the `admission` field fixes the created limiter's capacity,
the frame fields `run_frame` and `checked_frame` preserve it, and the `Limiter` field bounds
each end state by its own capacity. This is the formal statement of the first
`RequiredContracts` Intent clause. -/
theorem RequiredContracts.within_capacity (contracts : RequiredContracts) :
    ∀ (capacity : Nat) (created : Limiter), admit capacity = some created →
      ∀ ops : List Op,
        (run ops created).inUse ≤ capacity ∧ (runChecked ops created).2.inUse ≤ capacity := by
  intro capacity created admitted ops
  have created_capacity : created.capacity = capacity := by
    rw [contracts.admission] at admitted
    split at admitted
    · cases admitted; rfl
    · cases admitted
  have := (run ops created).bounded
  have := (runChecked ops created).2.bounded
  have := contracts.run_frame created ops
  have := contracts.checked_frame ops created
  omega

/-- Evidence required by the application entrypoint. Deleting or weakening an
assigned proof cannot inhabit its unchanged field proposition. Equivalent
proofs are welcome; neither theorem names nor declaration counts are the rule.

# Intent
Every required behavior of the limiter must be proved about the exact definitions the
application executes. -/
@[regula_material]
theorem requiredContracts : RequiredContracts where
  admission := admit_exact
  grant_success := grant_some
  grant_refusal := grant_none
  release_busy := release_of_pos
  release_idle := release_of_zero
  reset_empty := reset_inUse
  reset_frame := reset_capacity
  dispatch := fun _ op => by cases op <;> rfl
  composition := fun _ _ => rfl
  capacity_frame := step_capacity
  run_frame := run_capacity
  input_meaning := requestedCapacity_exact
  checked_step := checkedStep_exact
  checked_success := runChecked_success
  checked_error := runChecked_error
  checked_composition := runChecked_append
  checked_frame := runChecked_capacity
  burst := run_replicate_grant

/-- Pure application boundary: admission followed by the exact fold. Calling it
requires all explicit contracts about these definitions. Proof erasure changes
no computation; native execution and the caller's IO remain trusted boundaries. -/
def execute (_contracts : RequiredContracts) (capacity : Nat) (ops : List Op) :
    Option Limiter :=
  (admit capacity).map (run ops)

/-- Admission composes with the total fold without substituting inputs or
states: every positive capacity starts idle at exactly that capacity. -/
theorem execute_exact (contracts : RequiredContracts) (capacity : Nat)
    (ops : List Op) :
    execute contracts capacity ops = if 0 < capacity then
      some (run ops ⟨capacity, 0, Nat.zero_le capacity⟩) else none := by
  unfold execute
  rw [contracts.admission]
  split <;> rfl

/-- Pure strict application boundary. `none` is failed admission; `some` retains
both the success/refusal result and the final state of the admitted script. -/
def executeChecked (_contracts : RequiredContracts) (capacity : Nat) (ops : List Op) :
    Option (Except Unit Unit × Limiter) :=
  (admit capacity).map (runChecked ops)

/-- Admission composes with the strict runner without substituting inputs or
states: every positive capacity starts idle at exactly that capacity. -/
theorem executeChecked_exact (contracts : RequiredContracts) (capacity : Nat)
    (ops : List Op) :
    executeChecked contracts capacity ops = if 0 < capacity then
      some (runChecked ops ⟨capacity, 0, Nat.zero_le capacity⟩) else none := by
  unfold executeChecked
  rw [contracts.admission]
  split <;> rfl

/-- Register the actual executable and require its complete admission/runner
relation. This reuses `executeChecked_exact`; no second implementation is used.
The build linter also checks executability and compiler/runtime boundaries.

# Intent
The function the executable calls must admit exactly the positive capacities, start
each admitted limiter idle at that capacity, and then run the script strictly. -/
@[regula_material]
theorem checkedExecutable : Regula.ExecutableContract executeChecked
    (fun execute => ∀ (contracts : RequiredContracts) capacity ops,
      execute contracts capacity ops = if 0 < capacity then
        some (runChecked ops ⟨capacity, 0, Nat.zero_le capacity⟩) else none) :=
  ⟨executeChecked_exact⟩

end AuditApp
