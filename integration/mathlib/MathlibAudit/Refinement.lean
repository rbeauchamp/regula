import AuditApp.Limiter
import Mathlib.Logic.Relation

/-!
# Limiter refinement to a free-slot model

Stateful refinement of the actual limiter transitions to a nondeterministic
free-slot model. `Relation.ReflTransGen` means finitely many steps, including
zero. The general transfer theorem quantifies over every concrete path and
every related starting abstract state; matching abstract successors are
existential. The worked instance covers `step`, `run`, and the returned state
of `runChecked`, including refusal. It observes only capacity and occupancy,
not operation labels, error outputs, timing, or native execution. Natural
counts have exact unbounded Lean semantics; compiler/runtime execution remains
trusted. No fairness, progress, or liveness result is claimed. `reachable_safe` and `prefix_safe`
are material claims registered with `@[regula_material]`, so RG5002/RG5003 require their Intent
sections. The declarations keep the `AuditApp.Refinement` namespace of the application
they refine; this module belongs to the `MathlibAudit` library of the Mathlib integration
package, because the Core-only `AuditApp` surface in the `regula` package does not import
Mathlib. The standard's own example is the Lean/Std `audit/Audit/Refinement.lean`, which states
the refinement over core's `Relation.TransGen`: its paths have one or more edges, and an idle
abstract edge there takes the place of this closure's zero-step case.
-/

namespace AuditApp.Refinement

/-- Forward simulation transfers an invariant along every finite concrete path.
Initialization supplies a related abstract state satisfying `Inv`; each concrete
edge has a finite abstract match; `sound` transfers the invariant to `Safe`.
No abstract determinism or choice of a globally executable matching path is assumed. -/
theorem finite_transfer {C A : Type*} {StepC : C → C → Prop}
    {StepA : A → A → Prop} {R : C → A → Prop} {Inv : A → Prop}
    {Safe : C → Prop}
    (simulation : ∀ {c a c'}, R c a → StepC c c' →
      ∃ a', Relation.ReflTransGen StepA a a' ∧ R c' a')
    (preserve : ∀ {a a'}, Inv a → StepA a a' → Inv a')
    (sound : ∀ {c a}, R c a → Inv a → Safe c)
    {c₀ c : C} {a₀ : A} (related : R c₀ a₀) (initial : Inv a₀)
    (path : Relation.ReflTransGen StepC c₀ c) :
    ∃ a, Relation.ReflTransGen StepA a₀ a ∧ R c a ∧ Inv a ∧ Safe c := by
  have invariant : ∀ {a a'}, Relation.ReflTransGen StepA a a' → Inv a → Inv a' := by
    intro a a' h
    induction h with
    | refl => exact id
    | tail _ edge ih => exact fun hi => preserve (ih hi) edge
  induction path with
  | refl => exact ⟨a₀, .refl, related, initial, sound related initial⟩
  | @tail c' c'' _ edge ih =>
    obtain ⟨a, initialPath, hr, hi, _⟩ := ih
    obtain ⟨a', suffix, hr'⟩ := simulation hr edge
    have hi' := invariant suffix hi
    exact ⟨a', initialPath.trans suffix, hr', hi', sound hr' hi'⟩

/-- Abstract free slots change by one: allocate a positive free slot, or free
one below capacity. Both choices may be enabled; reset is not an atomic edge. -/
def StepA (cap a a' : Nat) : Prop :=
  (0 < a ∧ a' = a - 1) ∨ (a < cap ∧ a' = a + 1)

/-- The raw abstract domain is `Nat`; reachability, not every raw number,
establishes this upper bound. Raw numbers permit a simple closure argument. -/
def Inv (cap a : Nat) : Prop := a ≤ cap

/-- Concrete capacity is fixed and occupied plus abstract free slots equals it. -/
def R (cap : Nat) (c : Limiter) (a : Nat) : Prop :=
  c.capacity = cap ∧ c.inUse + a = cap

/-- Concrete edges use the actual total dispatcher, with an arbitrary operation. -/
def StepC (c c' : Limiter) : Prop := ∃ op, c' = step c op

/-- Every admitted capacity starts with all slots free in the abstract model. -/
theorem initial_related {cap : Nat} {c : Limiter} (h : admit cap = some c) :
    R cap c cap ∧ Inv cap cap := by
  rw [admit_exact] at h
  split at h
  · cases h
    exact ⟨⟨rfl, Nat.zero_add _⟩, Nat.le_refl _⟩
  · contradiction

/-- Every abstract edge preserves the free-slot bound. -/
theorem preserve {cap a a' : Nat} (h : Inv cap a) (edge : StepA cap a a') :
    Inv cap a' := by
  rcases edge with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> unfold Inv at * <;> omega

/-- Releasing the remaining occupied slots takes finitely many abstract edges.
The induction is on the number of releases, not a finite-state enumeration. -/
theorem free_to_capacity {a cap : Nat} (h : a ≤ cap) :
    Relation.ReflTransGen (StepA cap) a cap := by
  have grow : ∀ n, a + n ≤ cap → Relation.ReflTransGen (StepA cap) a (a + n) := by
    intro n
    induction n with
    | zero => intro _; exact .refl
    | succ n ih =>
      intro hn
      exact (ih (by omega)).tail (Or.inr ⟨by omega, by omega⟩)
  simpa [Nat.add_sub_of_le h] using grow (cap - a) (by omega)

/-- For every related pair and every actual concrete step there exists a finite
abstract match. Refused grants and idle releases may use zero abstract steps;
a reset frees all occupied slots through the abstract closure. -/
theorem simulation {cap : Nat} {c c' : Limiter} {a : Nat}
    (hr : R cap c a) (edge : StepC c c') :
    ∃ a', Relation.ReflTransGen (StepA cap) a a' ∧ R cap c' a' := by
  obtain ⟨op, rfl⟩ := edge
  obtain ⟨hc, ha⟩ := hr
  have frame := step_capacity c op
  cases op with
  | grant =>
    by_cases h : c.inUse < c.capacity
    · have hs : (step c .grant).inUse = c.inUse + 1 := by
        simp [step, grant, h]
      exact ⟨a - 1, .single (Or.inl ⟨by omega, rfl⟩),
        frame.trans hc, by omega⟩
    · have hs : step c .grant = c := by simp [step, grant, h]
      exact ⟨a, .refl, by simpa [hs, R] using And.intro hc ha⟩
  | release =>
    by_cases h : c.inUse = 0
    · have hs : step c .release = c := release_of_zero h
      exact ⟨a, .refl, by simpa [hs, R] using And.intro hc ha⟩
    · have hs : (step c .release).inUse = c.inUse - 1 :=
        release_of_pos (by omega)
      exact ⟨a + 1, .single (Or.inr ⟨by omega, rfl⟩),
        frame.trans hc, by omega⟩
  | reset =>
    exact ⟨cap, free_to_capacity (by omega), frame.trans hc, by simp [step, reset]⟩

/-- The relation transfers the abstract invariant to the fixed concrete bound.
The relation already implies this bound; the invariant is retained to expose
the general transfer interface. The intrinsic bound alone does not fix capacity. -/
theorem sound {cap a : Nat} {c : Limiter} (h : R cap c a) (_ : Inv cap a) :
    c.capacity = cap ∧ c.inUse ≤ cap := ⟨h.1, by have := h.2; omega⟩

/-- Observations agree at related endpoints: capacity and occupied count only.
This is not equality of error outputs, labelled traces, or intermediate states. -/
theorem observations {cap a : Nat} {c : Limiter} (h : R cap c a) :
    (c.capacity, c.inUse) = (cap, cap - a) := by
  have := h.2
  exact Prod.ext h.1 (by omega)

/-- Every finite reachable concrete endpoint has a reachable, invariant-satisfying
abstract witness and respects the original admitted capacity.

# Intent
However many operations run after admission, the limiter keeps its admitted capacity
and never has more slots in use than that capacity. Only finite runs are covered;
progress and liveness are not required. -/
@[regula_material]
theorem reachable_safe {cap : Nat} {c₀ c : Limiter} (admission : admit cap = some c₀)
    (path : Relation.ReflTransGen StepC c₀ c) :
    ∃ a, Relation.ReflTransGen (StepA cap) cap a ∧ R cap c a ∧ Inv cap a ∧
      (c.capacity = cap ∧ c.inUse ≤ cap) :=
  finite_transfer (StepC := StepC) (StepA := StepA cap) (R := R cap)
    (Inv := Inv cap) (Safe := fun s => s.capacity = cap ∧ s.inUse ≤ cap)
    (c₀ := c₀) (c := c) (a₀ := cap) simulation preserve sound
    (initial_related admission).1
    (initial_related admission).2 path

/-- Every finite total script is a path of the same concrete transitions. -/
theorem run_path (ops : List Op) (c : Limiter) :
    Relation.ReflTransGen StepC c (run ops c) := by
  induction ops generalizing c with
  | nil => exact .refl
  | cons op ops ih => exact (ih (step c op)).head ⟨op, rfl⟩

/-- The strict interpreter's returned state is also reachable, on both success
and refusal. This uses its exact bind/error equation; no runner is duplicated. -/
theorem runChecked_path (ops : List Op) (c : Limiter) :
    Relation.ReflTransGen StepC c (runChecked ops c).2 := by
  induction ops generalizing c with
  | nil => exact .refl
  | cons op ops ih =>
    rw [runChecked_cons]
    split
    · exact .refl
    · exact (ih (step c op)).head ⟨op, rfl⟩

/-- Safety transfer applies to every prefix length of every script, including
its returned refusal state. Lengths beyond the script select the whole script.

# Intent
Every state the strict runner can return, after any prefix of any script and whether
it completes or stops at a refused grant, must keep the admitted capacity unchanged and
stay within it. -/
@[regula_material]
theorem prefix_safe {cap : Nat} {c : Limiter} (admission : admit cap = some c)
    (ops : List Op) (n : Nat) :
    ∃ a, Relation.ReflTransGen (StepA cap) cap a ∧
      R cap (runChecked (ops.take n) c).2 a ∧ Inv cap a ∧
      ((runChecked (ops.take n) c).2.capacity = cap ∧
        (runChecked (ops.take n) c).2.inUse ≤ cap) :=
  reachable_safe admission (runChecked_path _ _)

end AuditApp.Refinement
