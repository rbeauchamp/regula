import RegulaPolicy.Admission
import Regula.Contract

/-! # Execution decisions

Executable execution decisions and their exact finite-observation specification.
Neither policy equivalence nor admitted origin data proves extraction or native runtime correctness. -/
namespace RegulaPolicy
/-- Which execution rule a failure belongs to. -/
inductive ExecutionFailureKind where
  /-- An unresolved path, or a boundary whose correspondence is unresolved (RG3001). -/
  | executionUnresolved
  /-- A trusted boundary that a checked-correspondence claim does not admit (RG3002). -/
  | executionBoundary
  deriving Repr, DecidableEq

/-- Execution-claim failures over the typed coverage account. Unresolved
paths and unclassified boundaries block in every mode; a trusted boundary
blocks a checked-correspondence claim unless it is a toolchain native-runtime
primitive. -/
structure ExecutionFailure where
  /-- The rule the failure belongs to. -/
  id : ExecutionFailureKind
  /-- The execution root whose closure reaches the failing path or boundary. -/
  root : ExecutionRoot
  /-- Human-readable text naming the root and the unresolved path or reached boundary. -/
  detail : String

/-- A resolved boundary in checked mode has checked evidence or the typed native-runtime
origin account. Report mode retains trusted boundaries; unresolved never passes. -/
def BoundaryOK (claim : ExecutionClaim) (b : ExecutionBoundary) : Prop :=
  b.correspondence ≠ .unresolved ∧
  (claim = .report ∨ b.correspondence = .checked ∨ b.boundary = .nativeRuntime)
instance (claim : ExecutionClaim) (b : ExecutionBoundary) : Decidable (BoundaryOK claim b) := by
  unfold BoundaryOK; infer_instance

/-- The finite closure account has no unresolved paths and every boundary meets its claim.
Completeness of actual execution-root/closure extraction is a separate operational obligation. -/
def ExecutionOK (inventory : ExecutionInventory) (claim : ExecutionClaim) : Prop :=
  ∀ r ∈ inventory.roots, r.unresolved = #[] ∧ ∀ b ∈ r.boundaries, BoundaryOK claim b
instance (inventory : ExecutionInventory) (claim : ExecutionClaim) : Decidable (ExecutionOK inventory claim) := by
  unfold ExecutionOK; infer_instance

/-- One boundary's deterministic diagnostic, retaining unresolved-before-trusted precedence. -/
def boundaryFailures (root : ExecutionRoot) (claim : ExecutionClaim)
    (b : ExecutionBoundary) : Array ExecutionFailure :=
  if b.correspondence == .unresolved then
    #[⟨.executionUnresolved, root,
      s!"{root.name} reaches {b.name} ({b.boundary}): {b.evidence.getD "unclassified"}"⟩]
  else if claim == .checked && b.correspondence != .checked && b.boundary != .nativeRuntime then
    #[⟨.executionBoundary, root, s!"{root.name} reaches {b.name} ({b.boundary})"⟩]
  else #[]

/-- Preserve root order, each unresolved path, and then every boundary's failure. -/
def rootFailures (root : ExecutionRoot) (claim : ExecutionClaim) : Array ExecutionFailure :=
  root.unresolved.map (fun item => ⟨.executionUnresolved, root, s!"{root.name}: {item}"⟩) ++
    root.boundaries.flatMap (boundaryFailures root claim)

/-- Every execution failure of the inventory under `claim`: each root's failures
(`rootFailures`), in root order. It is empty exactly when `ExecutionOK` holds
(`executionFailureRecords_empty_iff`). -/
def executionFailureRecords (inventory : ExecutionInventory)
    (claim : ExecutionClaim) : Array ExecutionFailure :=
  inventory.roots.flatMap (fun root => rootFailures root claim)

/-- All and only boundary-policy violations produce a failure. -/
theorem boundaryFailures_empty_iff (r : ExecutionRoot) (c : ExecutionClaim) (b : ExecutionBoundary) :
    boundaryFailures r c b = #[] ↔ BoundaryOK c b := by
  unfold boundaryFailures BoundaryOK
  cases c <;> cases hb : b.correspondence <;> simp

/-- Every unresolved path and boundary is included; an empty failure array is equivalent
to the independent execution predicate, for every admitted finite inventory and mode. -/
theorem executionFailureRecords_empty_iff (i : ExecutionInventory) (c : ExecutionClaim) :
    executionFailureRecords i c = #[] ↔ ExecutionOK i c := by
  simp [executionFailureRecords, rootFailures, ExecutionOK, Array.flatMap_eq_empty_iff,
    boundaryFailures_empty_iff]

/-- Failure kind of one boundary: an unresolved boundary is `executionUnresolved` in every
mode; otherwise only a checked claim over a non-checked, non-native-runtime boundary fails,
as `executionBoundary`. A report claim never fails a resolved boundary. -/
theorem boundaryFailures_ids (r : ExecutionRoot) (c : ExecutionClaim) (b : ExecutionBoundary) :
    (boundaryFailures r c b).map (·.id) =
      if b.correspondence = .unresolved then #[.executionUnresolved]
      else if c = .checked ∧ b.correspondence ≠ .checked ∧ b.boundary ≠ .nativeRuntime then
        #[.executionBoundary]
      else #[] := by
  unfold boundaryFailures
  by_cases hu : b.correspondence = .unresolved <;> simp [hu]
  by_cases hc : c = .checked <;> simp [hc]
  by_cases hk : b.correspondence = .checked <;> simp [hk]
  by_cases hn : b.boundary = .nativeRuntime <;> simp [hn]

/-- A root's failure kinds: one `executionUnresolved` per unresolved path, in order, then
each boundary's kinds. -/
theorem rootFailures_ids (r : ExecutionRoot) (c : ExecutionClaim) :
    (rootFailures r c).map (·.id) =
      r.unresolved.map (fun _ => ExecutionFailureKind.executionUnresolved) ++
        r.boundaries.flatMap (fun b => (boundaryFailures r c b).map (·.id)) := by
  simp only [rootFailures, Array.map_append, Array.map_flatMap, Array.map_map]
  rfl

/-- Named execution-coverage counts rendered by gate output. -/
structure ExecutionSummary where
  /-- The number of execution-root observations. -/
  roots : Nat
  /-- The number of boundary observations over all roots. -/
  boundaries : Nat
  /-- The number of boundary observations with checked correspondence. -/
  checked : Nat
  /-- The number of boundary observations with trusted correspondence. -/
  trusted : Nat
  /-- The number of unresolved diagnostics: unresolved root paths plus unresolved boundaries. -/
  unresolved : Nat
  deriving Repr, DecidableEq

/-- Every boundary observation of the account, in root order, without deduplication. -/
def ExecutionInventory.boundaries (inventory : ExecutionInventory) : Array ExecutionBoundary :=
  inventory.roots.flatMap (·.boundaries)

/-- Required meaning of the rendered counts. Roots and boundaries count observations, not
distinct runtime paths; `unresolved` is the number of unresolved diagnostics the execution
decision reports, for every claim: each unresolved root path and each unresolved boundary. -/
def SummaryContract (summary : ExecutionInventory → ExecutionSummary) : Prop :=
  ∀ inventory, (summary inventory).roots = inventory.roots.size ∧
    (summary inventory).boundaries = inventory.boundaries.size ∧
    (summary inventory).checked =
      (inventory.boundaries.filter (·.correspondence = .checked)).size ∧
    (summary inventory).trusted =
      (inventory.boundaries.filter (·.correspondence = .trusted)).size ∧
    ∀ claim, (summary inventory).unresolved =
      ((executionFailureRecords inventory claim).filter (·.id = .executionUnresolved)).size

/-- Execution-coverage counts over the admitted account. -/
def executionSummary (inventory : ExecutionInventory) : ExecutionSummary :=
  let boundaries := inventory.boundaries
  { roots := inventory.roots.size, boundaries := boundaries.size
    checked := boundaries.countP (·.correspondence == .checked)
    trusted := boundaries.countP (·.correspondence == .trusted)
    unresolved := (inventory.roots.map (·.unresolved.size)).sum +
      boundaries.countP (·.correspondence == .unresolved) }

/-- One boundary contributes one unresolved diagnostic exactly when it is unresolved. -/
private theorem boundaryFailures_unresolved (root : ExecutionRoot) (claim : ExecutionClaim)
    (b : ExecutionBoundary) :
    (boundaryFailures root claim b).countP (·.id = .executionUnresolved) =
      if b.correspondence = .unresolved then 1 else 0 := by
  unfold boundaryFailures
  cases claim <;> cases b.correspondence <;> simp

private theorem sum_indicator (xs : Array ExecutionBoundary) (f : ExecutionBoundary → Nat)
    (h : ∀ b, f b = if b.correspondence = .unresolved then 1 else 0) :
    (xs.map f).sum = xs.countP (·.correspondence == .unresolved) := by
  rcases xs with ⟨xs⟩
  induction xs with
  | nil => simp
  | cons x xs ih => simp_all [List.countP_cons]; split <;> omega

private theorem sum_map_add (xs : Array ExecutionRoot) (f g : ExecutionRoot → Nat) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  rcases xs with ⟨xs⟩
  induction xs with
  | nil => simp
  | cons x xs ih => simp_all; omega

/-- A root reports each unresolved path and each unresolved boundary once. -/
private theorem rootFailures_unresolved (root : ExecutionRoot) (claim : ExecutionClaim) :
    (rootFailures root claim).countP (·.id = .executionUnresolved) =
      root.unresolved.size + root.boundaries.countP (·.correspondence == .unresolved) := by
  simp only [rootFailures, Array.countP_append, Array.countP_map, Array.countP_flatMap]
  congr 1
  · simp [Function.comp_def]
  · exact sum_indicator _ _ (boundaryFailures_unresolved root claim)

/-- The unresolved count is every root path plus every unresolved boundary, which is
exactly the number of unresolved diagnostics in the decision's failure records. -/
theorem executionSummary_unresolved (inventory : ExecutionInventory) (claim : ExecutionClaim) :
    (executionSummary inventory).unresolved =
      ((executionFailureRecords inventory claim).filter (·.id = .executionUnresolved)).size := by
  rw [← Array.countP_eq_size_filter]
  simp only [executionSummary, ExecutionInventory.boundaries, executionFailureRecords,
    Array.countP_flatMap, Function.comp_def, rootFailures_unresolved, sum_map_add]

/-- Every boundary has exactly one of the three correspondence categories. -/
theorem executionSummary_partition (inventory : ExecutionInventory) :
    (executionSummary inventory).checked + (executionSummary inventory).trusted +
      (inventory.boundaries.filter (·.correspondence = .unresolved)).size =
      (executionSummary inventory).boundaries := by
  simp only [executionSummary, ← Array.countP_eq_size_filter]
  generalize inventory.boundaries = xs
  rcases xs with ⟨xs⟩
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.size_toArray, List.countP_toArray, List.countP_cons, List.length_cons] at *
    cases x.correspondence <;> simp <;> omega

/-- The gate renders these counts through this registration, whose `run` is exactly
`executionSummary`. It does not count distinct runtime paths or authenticate extraction. -/
theorem checked_summary : Regula.ExecutableContract executionSummary SummaryContract :=
  ⟨fun inventory => ⟨rfl, rfl, Array.countP_eq_size_filter .., Array.countP_eq_size_filter ..,
    executionSummary_unresolved inventory⟩⟩

end RegulaPolicy
