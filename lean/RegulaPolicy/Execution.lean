import RegulaPolicy.Admission
import Regula.Contract

/-! # Execution decisions

Executable execution decisions and their exact finite-observation specification, and the
toolchain trusted-base report that lists each toolchain-owned boundary once across an audit's
environments.
Neither policy equivalence nor admitted origin data proves extraction or native runtime
correctness. -/
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
blocks a checked-correspondence claim unless the toolchain owns it. -/
structure ExecutionFailure where
  /-- The rule the failure belongs to. -/
  id : ExecutionFailureKind
  /-- The execution root whose closure reaches the failing path or boundary. -/
  root : ExecutionRoot
  /-- Human-readable text naming the root and the unresolved path or reached boundary. -/
  detail : String

/-- A resolved boundary in checked mode has checked evidence or is toolchain-owned: its
declaring module's origin was admitted as the toolchain's own (`ToolchainOrigin`), so it is part
of the toolchain's trusted base. Report mode retains trusted boundaries; unresolved never
passes. -/
def BoundaryOK (claim : ExecutionClaim) (b : ExecutionBoundary) : Prop :=
  b.correspondence ≠ .unresolved ∧
  (claim = .report ∨ b.correspondence = .checked ∨ b.toolchainOrigin?.isSome)
instance (claim : ExecutionClaim) (b : ExecutionBoundary) : Decidable (BoundaryOK claim b) := by
  unfold BoundaryOK; infer_instance

/-- The finite closure account has no unresolved paths and every boundary meets its claim.
Completeness of actual execution-root/closure extraction is a separate operational obligation. -/
def ExecutionOK (inventory : ExecutionInventory) (claim : ExecutionClaim) : Prop :=
  ∀ r ∈ inventory.roots, r.unresolved = #[] ∧ ∀ b ∈ r.boundaries, BoundaryOK claim b
instance (inventory : ExecutionInventory) (claim : ExecutionClaim) : Decidable
    (ExecutionOK inventory claim) := by
  unfold ExecutionOK; infer_instance

/-- One boundary's deterministic diagnostic, retaining unresolved-before-trusted precedence. -/
def boundaryFailures (root : ExecutionRoot) (claim : ExecutionClaim)
    (b : ExecutionBoundary) : Array ExecutionFailure :=
  if b.correspondence == .unresolved then
    #[⟨.executionUnresolved, root,
      s!"{root.name} reaches {b.name} ({b.boundary}): {b.evidence.getD "unclassified"}"⟩]
  else if claim == .checked && b.correspondence != .checked && b.toolchainOrigin?.isNone then
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
theorem boundaryFailures_empty_iff (r : ExecutionRoot) (c : ExecutionClaim)
    (b : ExecutionBoundary) :
    boundaryFailures r c b = #[] ↔ BoundaryOK c b := by
  unfold boundaryFailures BoundaryOK
  cases c <;> cases hb : b.correspondence <;> cases ho : b.toolchainOrigin? <;> simp

/-- Every unresolved path and boundary is included; an empty failure array is equivalent
to the independent execution predicate, for every admitted finite inventory and mode. -/
theorem executionFailureRecords_empty_iff (i : ExecutionInventory) (c : ExecutionClaim) :
    executionFailureRecords i c = #[] ↔ ExecutionOK i c := by
  simp [executionFailureRecords, rootFailures, ExecutionOK, Array.flatMap_eq_empty_iff,
    boundaryFailures_empty_iff]

/-- Failure kind of one boundary: an unresolved boundary is `executionUnresolved` in every
mode; otherwise only a checked claim over a non-checked boundary the toolchain does not own
fails, as `executionBoundary`. A report claim never fails a resolved boundary. -/
theorem boundaryFailures_ids (r : ExecutionRoot) (c : ExecutionClaim) (b : ExecutionBoundary) :
    (boundaryFailures r c b).map (·.id) =
      if b.correspondence = .unresolved then #[.executionUnresolved]
      else if c = .checked ∧ b.correspondence ≠ .checked ∧ b.toolchainOrigin? = none then
        #[.executionBoundary]
      else #[] := by
  unfold boundaryFailures
  by_cases hu : b.correspondence = .unresolved <;> simp [hu]
  by_cases hc : c = .checked <;> simp [hc]
  by_cases hk : b.correspondence = .checked <;> simp [hk]
  cases hn : b.toolchainOrigin? <;> simp

/-- A root's failure kinds: one `executionUnresolved` per unresolved path, in order, then
each boundary's kinds. -/
theorem rootFailures_ids (r : ExecutionRoot) (c : ExecutionClaim) :
    (rootFailures r c).map (·.id) =
      r.unresolved.map (fun _ => ExecutionFailureKind.executionUnresolved) ++
        r.boundaries.flatMap (fun b => (boundaryFailures r c b).map (·.id)) := by
  simp only [rootFailures, Array.map_append, Array.map_flatMap, Array.map_map]
  rfl

/-- A boundary's failures are among the decision's records whenever its root is. -/
theorem boundaryFailures_mem_records {i : ExecutionInventory} {r : ExecutionRoot}
    (hr : r ∈ i.roots) {b : ExecutionBoundary} (hb : b ∈ r.boundaries) (c : ExecutionClaim)
    {f : ExecutionFailure} (hf : f ∈ boundaryFailures r c b) :
    f ∈ executionFailureRecords i c := by
  simp only [executionFailureRecords, rootFailures, Array.mem_flatMap, Array.mem_append]
  exact ⟨r, hr, Or.inr ⟨b, hb, hf⟩⟩

/-- A toolchain-owned boundary never fails, under either claim: it is trusted, so it is
resolved, and it is part of the toolchain's trusted base. -/
theorem boundaryFailures_toolchain (r : ExecutionRoot) (c : ExecutionClaim)
    (b : ExecutionBoundary) {o : ToolchainOrigin} (h : b.toolchainOrigin? = some o) :
    boundaryFailures r c b = #[] := by
  have trusted : b.correspondence = .trusted :=
    BoundaryEvidence.correspondence_of_toolchainOrigin h
  unfold boundaryFailures
  simp [trusted, h]

/-- Every boundary the toolchain does not own and no checked evidence covers is still reported
under a checked claim: the decision's records contain exactly its own one failure, of kind
`executionUnresolved` when it is unresolved and `executionBoundary` otherwise, naming its root. -/
theorem project_boundary_reported {i : ExecutionInventory} {r : ExecutionRoot}
    (hr : r ∈ i.roots) {b : ExecutionBoundary} (hb : b ∈ r.boundaries)
    (owner : b.toolchainOrigin? = none) (unchecked : b.correspondence ≠ .checked) :
    ∃ f, boundaryFailures r .checked b = #[f] ∧ f ∈ executionFailureRecords i .checked ∧
      f.root = r ∧
      f.id = if b.correspondence = .unresolved then .executionUnresolved
        else .executionBoundary := by
  have single : ∃ f, boundaryFailures r .checked b = #[f] ∧ f.root = r ∧
      f.id = if b.correspondence = .unresolved then .executionUnresolved
        else .executionBoundary := by
    unfold boundaryFailures
    by_cases hu : b.correspondence = .unresolved
    · exact ⟨⟨.executionUnresolved, r,
        s!"{r.name} reaches {b.name} ({b.boundary}): {b.evidence.getD "unclassified"}"⟩,
        by simp [hu], rfl, by simp [hu]⟩
    · exact ⟨⟨.executionBoundary, r, s!"{r.name} reaches {b.name} ({b.boundary})"⟩,
        by simp [hu, unchecked, owner], rfl, by simp [hu]⟩
  obtain ⟨f, hf, hroot, hid⟩ := single
  exact ⟨f, hf, boundaryFailures_mem_records hr hb .checked (by simp [hf]), hroot, hid⟩

/-! ## A `partial` implementation is reported with the boundary that runs it

A root's account can hold two boundaries for one replaced implementation: the boundary of the
constant whose compiled code is a `partial` definition, and that definition's own
partial-computation boundary. The first already trusts, without checked correspondence, that the
definition's code runs in the constant's place; the second adds that the definition is `partial`.
Three recorded relations give such a pair: a constant-equality (`csimp`) candidate whose target is
a `partial` definition (the implementation Mathlib's `compile_inductive%` registers for a
recursor), an `implemented_by` replacement whose target is one, and an opaque constant with the
`partial` helper Lean compiles it through (an author's `partial def` and its `_unsafe_rec`).

The account keeps both boundaries, and the decision's records (`executionFailureRecords`) one
failure for each. The findings (`executionFindings`) and the coverage counts (`executionSummary`)
report the implementation with the boundary that runs it: one finding that names both, and one
counted boundary. The relation is read from the account's own edges, which the collector takes
from the simplification-candidate state, the `implemented_by` attribute and the compiler's helper
lookup; no name is parsed. Both boundaries are trusted and neither is toolchain-owned, so they
fail and pass together (`executionFindings_empty_iff`). -/

/-- `b` is the boundary of a `partial` definition that the project or a dependency owns: a
trusted partial-computation boundary with no toolchain origin, whose constant is the source of no
helper edge. The account records an opaque constant compiled through a partial helper under the
same kind (`BoundaryKind.partialComputation`), with a helper edge from it
(`ExecutionClosure.helperEdges`); that boundary is not foldable. -/
def ExecutionRoot.foldable (r : ExecutionRoot) (b : ExecutionBoundary) : Bool :=
  b.boundary == .partialComputation && b.correspondence == .trusted &&
    b.toolchainOrigin?.isNone && !r.closure.helperEdges.any (·.1 == b.name)

/-- Boundary `a` of root `r` carries boundary `b`: `a` names `b`'s constant as the code that
runs in its place, by its replacement or, for an opaque constant, by a helper edge; `a` is
trusted, has no toolchain origin and is not itself foldable; and `b` is foldable. -/
def ExecutionRoot.carries (r : ExecutionRoot) (a b : ExecutionBoundary) : Bool :=
  (a.replacement == some b.name ||
      (a.boundary == .partialComputation && r.closure.helperEdges.contains (a.name, b.name))) &&
    a.correspondence == .trusted && a.toolchainOrigin?.isNone && !r.foldable a && r.foldable b

/-- Boundary `b` of root `r` is reported with a boundary of `r` that carries it, not by a
finding or a count of its own. -/
def ExecutionRoot.folded (r : ExecutionRoot) (b : ExecutionBoundary) : Bool :=
  r.foldable b && r.boundaries.any (r.carries · b)

/-- The boundaries of `r` that boundary `a` carries, in the account's order: the `partial`
implementations its finding names. -/
def ExecutionRoot.implementations (r : ExecutionRoot) (a : ExecutionBoundary) :
    Array ExecutionBoundary :=
  r.boundaries.filter (r.carries a)

/-- The boundaries of `r` reported on their own, in the account's order: every boundary that is
not folded. -/
def ExecutionRoot.reported (r : ExecutionRoot) : Array ExecutionBoundary :=
  r.boundaries.filter (!r.folded ·)

/-- A foldable boundary is a trusted partial-computation boundary the toolchain does not own. -/
theorem ExecutionRoot.foldable_spec {r : ExecutionRoot} {b : ExecutionBoundary}
    (h : r.foldable b = true) :
    b.boundary = .partialComputation ∧ b.correspondence = .trusted ∧
      b.toolchainOrigin? = none := by
  simp only [ExecutionRoot.foldable, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

/-- What carrying requires of both boundaries: the carried one is foldable; the carrying one is
trusted, not toolchain-owned and not foldable; and it names the carried constant by its
replacement or, as a partial-computation boundary, by a helper edge. -/
theorem ExecutionRoot.carries_spec {r : ExecutionRoot} {a b : ExecutionBoundary}
    (h : r.carries a b = true) :
    r.foldable b = true ∧ r.foldable a = false ∧ a.correspondence = .trusted ∧
      a.toolchainOrigin? = none ∧
      (a.replacement = some b.name ∨
        (a.boundary = .partialComputation ∧
          r.closure.helperEdges.contains (a.name, b.name) = true)) := by
  simp only [ExecutionRoot.carries, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    Option.isNone_iff_eq_none, Bool.not_eq_true'] at h
  exact ⟨h.2, h.1.2, h.1.1.1.2, h.1.1.2, h.1.1.1.1⟩

/-- A boundary that carries another is reported on its own: it is never folded. -/
theorem ExecutionRoot.carries_not_folded {r : ExecutionRoot} {a b : ExecutionBoundary}
    (h : r.carries a b = true) : r.folded a = false := by
  simp [ExecutionRoot.folded, (ExecutionRoot.carries_spec h).2.1]

/-- Every boundary of a root is reported on its own or folded. -/
theorem ExecutionRoot.reported_or_folded (r : ExecutionRoot) {b : ExecutionBoundary}
    (hb : b ∈ r.boundaries) : b ∈ r.reported ∨ r.folded b = true := by
  cases h : r.folded b
  · exact Or.inl (Array.mem_filter.mpr ⟨hb, by simp [h]⟩)
  · exact Or.inr rfl

/-- **Nothing but a carried `partial` implementation is folded.** A folded boundary is a trusted
partial-computation boundary the toolchain does not own, and some boundary reported on its own
in the same root carries it, itself trusted and not toolchain-owned. -/
theorem ExecutionRoot.folded_carried {r : ExecutionRoot} {b : ExecutionBoundary}
    (h : r.folded b = true) :
    b.boundary = .partialComputation ∧ b.correspondence = .trusted ∧
      b.toolchainOrigin? = none ∧
      ∃ a ∈ r.reported, r.carries a b = true ∧ a.correspondence = .trusted ∧
        a.toolchainOrigin? = none := by
  simp only [ExecutionRoot.folded, Bool.and_eq_true, Array.any_eq_true'] at h
  obtain ⟨foldable, a, ha, carried⟩ := h
  have spec := ExecutionRoot.carries_spec carried
  refine ⟨(ExecutionRoot.foldable_spec foldable).1, (ExecutionRoot.foldable_spec foldable).2.1,
    (ExecutionRoot.foldable_spec foldable).2.2, a, ?_, carried, spec.2.2.1, spec.2.2.2.1⟩
  exact Array.mem_filter.mpr ⟨ha, by simp [ExecutionRoot.carries_not_folded carried]⟩

/-- The text a finding adds for the implementations its boundary carries: each one's constant
and kind, in order; empty when there is none. -/
def implementationsText (implementations : Array ExecutionBoundary) : String :=
  String.join (implementations.toList.map fun b =>
    s!", with its implementation {b.name} ({b.boundary})")

/-- One boundary's findings: none for a folded boundary, and otherwise its failure
(`boundaryFailures`) with the implementations it carries named after its detail. -/
def boundaryFindings (root : ExecutionRoot) (claim : ExecutionClaim)
    (b : ExecutionBoundary) : Array ExecutionFailure :=
  if root.folded b then #[]
  else (boundaryFailures root claim b).map fun f =>
    { f with detail := f.detail ++ implementationsText (root.implementations b) }

/-- A root's findings: each unresolved path, then each boundary's findings, in the order of
`rootFailures`. -/
def rootFindings (root : ExecutionRoot) (claim : ExecutionClaim) : Array ExecutionFailure :=
  root.unresolved.map (fun item => ⟨.executionUnresolved, root, s!"{root.name}: {item}"⟩) ++
    root.boundaries.flatMap (boundaryFindings root claim)

/-- The findings the gate reports for the inventory under `claim`: the decision's records
(`executionFailureRecords`) with each folded boundary's record reported in the finding of a
boundary that carries it (`failure_reported`). They are empty exactly when `ExecutionOK` holds
(`executionFindings_empty_iff`). -/
def executionFindings (inventory : ExecutionInventory)
    (claim : ExecutionClaim) : Array ExecutionFailure :=
  inventory.roots.flatMap (fun root => rootFindings root claim)

/-- The failure of a trusted boundary the toolchain does not own: one `executionBoundary` record
under a checked claim, and none under a report claim. -/
private theorem boundaryFailures_trusted (r : ExecutionRoot) (c : ExecutionClaim)
    {b : ExecutionBoundary} (trusted : b.correspondence = .trusted)
    (owner : b.toolchainOrigin? = none) :
    boundaryFailures r c b =
      if c = .checked then
        #[⟨.executionBoundary, r, s!"{r.name} reaches {b.name} ({b.boundary})"⟩]
      else #[] := by
  unfold boundaryFailures
  cases c <;> simp [trusted, owner]

/-- A root whose boundaries have no findings has no boundary failure: a folded boundary passes
with the boundary that carries it. -/
private theorem boundaryFailures_empty_of_findings {r : ExecutionRoot} {c : ExecutionClaim}
    (h : ∀ b ∈ r.boundaries, boundaryFindings r c b = #[]) {b : ExecutionBoundary}
    (hb : b ∈ r.boundaries) : boundaryFailures r c b = #[] := by
  cases hf : r.folded b
  · simpa [boundaryFindings, hf] using h b hb
  · obtain ⟨-, trusted, owner, a, ha, -, trustedA, ownerA⟩ := ExecutionRoot.folded_carried hf
    obtain ⟨ha, unfolded⟩ := Array.mem_filter.mp ha
    have unfolded : r.folded a = false := by simpa using unfolded
    have passes : boundaryFailures r c a = #[] := by
      simpa [boundaryFindings, unfolded] using h a ha
    rw [boundaryFailures_trusted r c trustedA ownerA] at passes
    rw [boundaryFailures_trusted r c trusted owner]
    cases c <;> simp_all

/-- **The findings decide exactly what the records decide.** They are empty exactly when the
execution predicate holds, for every admitted inventory and claim, so folding hides no failure:
a folded boundary fails only with a boundary that carries it, which is reported. -/
theorem executionFindings_empty_iff (i : ExecutionInventory) (c : ExecutionClaim) :
    executionFindings i c = #[] ↔ ExecutionOK i c := by
  rw [← executionFailureRecords_empty_iff]
  simp only [executionFindings, executionFailureRecords, rootFindings, rootFailures,
    Array.flatMap_eq_empty_iff, Array.append_eq_empty_iff, Array.map_eq_empty_iff]
  constructor
  · intro h r hr
    exact ⟨(h r hr).1, fun b hb => boundaryFailures_empty_of_findings (h r hr).2 hb⟩
  · intro h r hr
    exact ⟨(h r hr).1, fun b hb => by simp [boundaryFindings, (h r hr).2 b hb]⟩

/-- A boundary's failures name its root. -/
theorem boundaryFailures_root {r : ExecutionRoot} {c : ExecutionClaim} {b : ExecutionBoundary}
    {f : ExecutionFailure} (hf : f ∈ boundaryFailures r c b) : f.root = r := by
  unfold boundaryFailures at hf
  split at hf
  · simp only [Array.mem_singleton] at hf
    rw [hf]
  · split at hf
    · simp only [Array.mem_singleton] at hf
      rw [hf]
    · simp at hf

/-- A boundary's findings are among the gate's whenever its root is. -/
theorem boundaryFindings_mem {i : ExecutionInventory} {r : ExecutionRoot} (hr : r ∈ i.roots)
    {b : ExecutionBoundary} (hb : b ∈ r.boundaries) (c : ExecutionClaim)
    {g : ExecutionFailure} (hg : g ∈ boundaryFindings r c b) : g ∈ executionFindings i c := by
  simp only [executionFindings, rootFindings, Array.mem_flatMap, Array.mem_append]
  exact ⟨r, hr, Or.inr ⟨b, hb, hg⟩⟩

/-- **Every failure record is reported.** For each failure of a boundary `b` of a root of the
inventory, some boundary `a` of that root, `b` itself or one whose implementations include `b`,
has a failure of the same kind and root whose finding is among the gate's: that failure with
the implementations `a` carries named after its detail (`implementationsText`). -/
theorem failure_reported {i : ExecutionInventory} {r : ExecutionRoot} (hr : r ∈ i.roots)
    {b : ExecutionBoundary} (hb : b ∈ r.boundaries) (c : ExecutionClaim)
    {f : ExecutionFailure} (hf : f ∈ boundaryFailures r c b) :
    ∃ a ∈ r.boundaries, (a = b ∨ b ∈ r.implementations a) ∧
      ∃ g ∈ boundaryFailures r c a, g.id = f.id ∧ g.root = r ∧
        { g with detail := g.detail ++ implementationsText (r.implementations a) } ∈
          executionFindings i c := by
  cases folded : r.folded b
  · refine ⟨b, hb, Or.inl rfl, f, hf, rfl, boundaryFailures_root hf, ?_⟩
    apply boundaryFindings_mem hr hb c
    simp only [boundaryFindings, folded, Bool.false_eq_true, ite_false, Array.mem_map]
    exact ⟨f, hf, rfl⟩
  · obtain ⟨-, trusted, owner, a, ha, carried, trustedA, ownerA⟩ :=
      ExecutionRoot.folded_carried folded
    obtain ⟨ha, unfolded⟩ := Array.mem_filter.mp ha
    have unfolded : r.folded a = false := by simpa using unfolded
    rw [boundaryFailures_trusted r c trusted owner] at hf
    have checked : c = .checked := by
      cases c
      · simp at hf
      · rfl
    subst checked
    simp only [ite_true, Array.mem_singleton] at hf
    have failure : (⟨.executionBoundary, r, s!"{r.name} reaches {a.name} ({a.boundary})"⟩ :
        ExecutionFailure) ∈ boundaryFailures r .checked a := by
      simp [boundaryFailures_trusted r .checked trustedA ownerA]
    refine ⟨a, ha, Or.inr (Array.mem_filter.mpr ⟨hb, carried⟩), _, failure, by rw [hf], rfl, ?_⟩
    apply boundaryFindings_mem hr ha .checked
    simp only [boundaryFindings, unfolded, Bool.false_eq_true, ite_false, Array.mem_map]
    exact ⟨_, failure, rfl⟩

/-- Every unresolved path of a root of the inventory is a finding, unchanged. -/
theorem unresolved_reported {i : ExecutionInventory} {r : ExecutionRoot} (hr : r ∈ i.roots)
    {item : String} (hitem : item ∈ r.unresolved) (c : ExecutionClaim) :
    (⟨.executionUnresolved, r, s!"{r.name}: {item}"⟩ : ExecutionFailure) ∈
      executionFindings i c := by
  simp only [executionFindings, rootFindings, Array.mem_flatMap, Array.mem_append, Array.mem_map]
  exact ⟨r, hr, Or.inl ⟨item, hitem, rfl⟩⟩

/-- **Every finding is a record.** Each finding has the kind and root of a failure record of
the decision, and that record's detail, followed by the text of the implementations its
boundary carries. -/
theorem executionFindings_sound {i : ExecutionInventory} {c : ExecutionClaim}
    {g : ExecutionFailure} (hg : g ∈ executionFindings i c) :
    ∃ f ∈ executionFailureRecords i c, g.id = f.id ∧ g.root = f.root ∧
      ∃ suffix, g.detail = f.detail ++ suffix := by
  simp only [executionFindings, rootFindings, Array.mem_flatMap, Array.mem_append,
    Array.mem_map] at hg
  obtain ⟨r, hr, path | ⟨b, hb, hg⟩⟩ := hg
  · refine ⟨g, ?_, rfl, rfl, "", by simp⟩
    simp only [executionFailureRecords, rootFailures, Array.mem_flatMap, Array.mem_append,
      Array.mem_map]
    exact ⟨r, hr, Or.inl path⟩
  · unfold boundaryFindings at hg
    split at hg
    · simp at hg
    · obtain ⟨f, hf, rfl⟩ := Array.mem_map.mp hg
      exact ⟨f, boundaryFailures_mem_records hr hb c hf, rfl, rfl, _, rfl⟩

private theorem flatMap_unless {α β : Type} (xs : Array α) (p : α → Bool) (f : α → Array β) :
    xs.flatMap (fun x => if p x then #[] else f x) = (xs.filter (!p ·)).flatMap f := by
  apply Array.toList_inj.mp
  simp only [Array.toList_flatMap, Array.toList_filter]
  induction xs.toList with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [h, ih]

/-- A root's finding kinds: one `executionUnresolved` per unresolved path, in order, then the
failure kinds of each boundary reported on its own. A folded boundary has no finding. -/
theorem rootFindings_ids (r : ExecutionRoot) (c : ExecutionClaim) :
    (rootFindings r c).map (·.id) =
      r.unresolved.map (fun _ => ExecutionFailureKind.executionUnresolved) ++
        r.reported.flatMap (fun b => (boundaryFailures r c b).map (·.id)) := by
  simp only [rootFindings, Array.map_append, Array.map_flatMap, Array.map_map]
  congr 1
  rw [ExecutionRoot.reported, ← flatMap_unless]
  congr 1
  funext b
  unfold boundaryFindings
  split <;> simp [Function.comp_def]

/-- Named execution-coverage counts rendered by gate output. -/
structure ExecutionSummary where
  /-- The number of execution-root observations. -/
  roots : Nat
  /-- The number of boundary observations reported on their own, over all roots
  (`ExecutionRoot.reported`). -/
  boundaries : Nat
  /-- The number of those boundary observations with checked correspondence. -/
  checked : Nat
  /-- The number of those boundary observations with trusted correspondence. -/
  trusted : Nat
  /-- The number of unresolved diagnostics: unresolved root paths plus unresolved boundaries. -/
  unresolved : Nat
  deriving Repr, DecidableEq

/-- Every boundary observation of the account, in root order, without deduplication. -/
def ExecutionInventory.boundaries (inventory : ExecutionInventory) : Array ExecutionBoundary :=
  inventory.roots.flatMap (·.boundaries)

/-- Every boundary observation reported on its own (`ExecutionRoot.reported`), in root order,
without deduplication: the account's boundaries without each `partial` implementation that is
reported with the boundary that runs it. -/
def ExecutionInventory.reported (inventory : ExecutionInventory) : Array ExecutionBoundary :=
  inventory.roots.flatMap (·.reported)

/-- Required meaning of the rendered counts. Roots and boundaries count observations, not
distinct runtime paths, and a `partial` implementation reported with the boundary that runs it
is counted with that boundary, not again (`ExecutionInventory.reported`). `unresolved` is the
number of unresolved diagnostics the execution decision reports, for every claim: each
unresolved root path and each unresolved boundary. -/
def SummaryContract (summary : ExecutionInventory → ExecutionSummary) : Prop :=
  ∀ inventory, (summary inventory).roots = inventory.roots.size ∧
    (summary inventory).boundaries = inventory.reported.size ∧
    (summary inventory).checked =
      (inventory.reported.filter (·.correspondence = .checked)).size ∧
    (summary inventory).trusted =
      (inventory.reported.filter (·.correspondence = .trusted)).size ∧
    ∀ claim, (summary inventory).unresolved =
      ((executionFailureRecords inventory claim).filter (·.id = .executionUnresolved)).size

/-- Execution-coverage counts over the admitted account. -/
def executionSummary (inventory : ExecutionInventory) : ExecutionSummary :=
  let reported := inventory.reported
  { roots := inventory.roots.size, boundaries := reported.size
    checked := reported.countP (·.correspondence == .checked)
    trusted := reported.countP (·.correspondence == .trusted)
    unresolved := (inventory.roots.map (·.unresolved.size)).sum +
      inventory.boundaries.countP (·.correspondence == .unresolved) }

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

/-- Every boundary reported on its own has exactly one of the three correspondence
categories. -/
theorem executionSummary_partition (inventory : ExecutionInventory) :
    (executionSummary inventory).checked + (executionSummary inventory).trusted +
      (inventory.reported.filter (·.correspondence = .unresolved)).size =
      (executionSummary inventory).boundaries := by
  simp only [executionSummary, ← Array.countP_eq_size_filter]
  generalize inventory.reported = xs
  rcases xs with ⟨xs⟩
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.size_toArray, List.countP_toArray, List.countP_cons, List.length_cons] at *
    cases x.correspondence <;> simp <;> omega

/-- **Every boundary of the account is counted or carried by a counted one.** Each boundary
of a root of the inventory is among the reported boundaries the counts range over, or is folded:
a trusted `partial` implementation that a reported boundary of its root carries
(`ExecutionRoot.folded_carried`). -/
theorem ExecutionInventory.reported_or_folded (inventory : ExecutionInventory)
    {r : ExecutionRoot} (hr : r ∈ inventory.roots) {b : ExecutionBoundary}
    (hb : b ∈ r.boundaries) : b ∈ inventory.reported ∨ r.folded b = true :=
  (r.reported_or_folded hb).imp_left fun reported =>
    Array.mem_flatMap.mpr ⟨r, hr, reported⟩

/-- The unresolved findings are as many as the unresolved records: folding removes only trusted
boundaries, so `unresolved` is also the number of unresolved findings the gate reports. -/
theorem executionFindings_unresolved (inventory : ExecutionInventory) (claim : ExecutionClaim) :
    ((executionFindings inventory claim).filter (·.id = .executionUnresolved)).size =
      ((executionFailureRecords inventory claim).filter (·.id = .executionUnresolved)).size := by
  simp only [← Array.countP_eq_size_filter, executionFindings, executionFailureRecords,
    Array.countP_flatMap]
  congr 2
  funext root
  simp only [Function.comp_def, rootFindings, rootFailures, Array.countP_append,
    Array.countP_flatMap]
  congr 3
  funext b
  unfold boundaryFindings
  split
  next folded =>
    obtain ⟨-, trusted, owner, -⟩ := ExecutionRoot.folded_carried folded
    rw [boundaryFailures_trusted root claim trusted owner]
    cases claim <;> simp
  next => simp [Array.countP_map, Function.comp_def]

/-- The gate renders these counts through this registration, whose `run` is exactly
`executionSummary`. It does not count distinct runtime paths or authenticate extraction. -/
theorem checked_summary : Regula.ExecutableContract executionSummary SummaryContract :=
  ⟨fun inventory => ⟨rfl, rfl, Array.countP_eq_size_filter .., Array.countP_eq_size_filter ..,
    executionSummary_unresolved inventory⟩⟩


/-! ## The toolchain trusted base

A toolchain-owned boundary passes every claim, so it never becomes a failure record. The
report lists it instead once across every audited environment, with every environment and root
that reaches it, rather than once per root or once per environment. -/

/-- A toolchain boundary's identity in the trusted-base report: its constant and kind. -/
abbrev ToolchainKey := Lean.Name × BoundaryKind

/-- The toolchain key of a boundary observation. -/
def ExecutionBoundary.toolchainKey (b : ExecutionBoundary) : ToolchainKey := (b.name, b.boundary)

/-- One root that reaches a toolchain boundary: the label of the environment whose account
contains the root, and the root's name. -/
abbrev ToolchainReach := String × Lean.Name

/-- One toolchain-owned boundary of the audited execution accounts, reported once. -/
structure ToolchainBoundary where
  /-- The constant at the boundary. -/
  name : Lean.Name
  /-- The toolchain module that declares it. -/
  «module» : Lean.Name
  /-- What kind of boundary it is. -/
  boundary : BoundaryKind
  /-- For a runtime replacement, the constant run in its place. -/
  replacement : Option Lean.Name
  /-- The admitted origin that makes its module the toolchain's own. -/
  origin : ToolchainOrigin
  /-- Every environment and root whose account reaches it, sorted and without duplicates. -/
  reachedBy : Array ToolchainReach
  deriving Repr, DecidableEq

/-- The report's key of an entry: its constant and kind. -/
def ToolchainBoundary.key (t : ToolchainBoundary) : ToolchainKey := (t.name, t.boundary)

/-- Every toolchain-owned boundary observation of the labeled accounts, with the environment and
root that reach it and its admitted origin, in environment and root order. -/
def toolchainObservations (environments : Array (String × ExecutionInventory)) :
    Array (ToolchainReach × ExecutionBoundary × ToolchainOrigin) :=
  environments.flatMap fun environment => environment.2.roots.flatMap fun root =>
    root.boundaries.filterMap fun b =>
      b.toolchainOrigin?.map fun o => ((environment.1, root.name), b, o)

/-- Toolchain keys as a sorted array without duplicates. -/
def canonicalToolchainKeys (keys : Array ToolchainKey) : Array ToolchainKey :=
  letI : Ord ToolchainKey := lexOrd
  (CanonicalSet.normalize keys.toList).toList.toArray

@[simp] theorem mem_canonicalToolchainKeys (keys : Array ToolchainKey) (k : ToolchainKey) :
    k ∈ canonicalToolchainKeys keys ↔ k ∈ keys := by
  let : Ord ToolchainKey := lexOrd
  simp [canonicalToolchainKeys, Std.ExtTreeSet.mem_toList]

theorem canonicalToolchainKeys_nodup (keys : Array ToolchainKey) :
    (canonicalToolchainKeys keys).toList.Nodup := by
  let : Ord ToolchainKey := lexOrd
  exact (CanonicalSet.unique (CanonicalSet.normalize keys.toList)).imp
    Std.ReflCmp.ne_of_cmp_ne_eq

/-- Reaches as a sorted array without duplicates. -/
def canonicalToolchainReaches (reaches : Array ToolchainReach) : Array ToolchainReach :=
  letI : Ord ToolchainReach := lexOrd
  (CanonicalSet.normalize reaches.toList).toList.toArray

@[simp] theorem mem_canonicalToolchainReaches (reaches : Array ToolchainReach)
    (x : ToolchainReach) : x ∈ canonicalToolchainReaches reaches ↔ x ∈ reaches := by
  let : Ord ToolchainReach := lexOrd
  simp [canonicalToolchainReaches, Std.ExtTreeSet.mem_toList]

/-- The report entry of one key: the constant, module, kind, replacement and origin of the
key's first observation, with every environment and root that reaches the key; `none` when
nothing is observed under the key. -/
def toolchainEntry (observations : Array (ToolchainReach × ExecutionBoundary × ToolchainOrigin))
    (key : ToolchainKey) : Option ToolchainBoundary :=
  let reaching := observations.filter (·.2.1.toolchainKey == key)
  reaching[0]?.map fun (_, b, origin) =>
    { name := b.name, «module» := b.module, boundary := b.boundary
      replacement := b.replacement, origin
      reachedBy := canonicalToolchainReaches (reaching.map (·.1)) }

/-- The toolchain trusted base of the labeled execution accounts of one audit: each
toolchain-owned boundary once, in key order, with every environment and root that reaches it
(`checked_toolchainBase`). -/
def toolchainBase (environments : Array (String × ExecutionInventory)) :
    Array ToolchainBoundary :=
  let observations := toolchainObservations environments
  (canonicalToolchainKeys (observations.map (·.2.1.toolchainKey))).filterMap
    (toolchainEntry observations)

theorem mem_toolchainObservations {environments : Array (String × ExecutionInventory)}
    {x : ToolchainReach × ExecutionBoundary × ToolchainOrigin} :
    x ∈ toolchainObservations environments ↔
      ∃ e ∈ environments, ∃ r ∈ e.2.roots, x.1 = (e.1, r.name) ∧ x.2.1 ∈ r.boundaries ∧
        x.2.1.toolchainOrigin? = some x.2.2 := by
  rcases x with ⟨reach, b, o⟩
  simp only [toolchainObservations, Array.mem_flatMap, Array.mem_filterMap,
    Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨e, he, r, hr, b', hb', o', ho', rfl, rfl, rfl⟩
    exact ⟨e, he, r, hr, rfl, hb', ho'⟩
  · rintro ⟨e, he, r, hr, rfl, hb, ho⟩
    exact ⟨e, he, r, hr, b, hb, o, ho, rfl, rfl, rfl⟩

/-- What an entry reports: its key, the fields of an observation under that key, and reaches
that each reach the key. -/
theorem toolchainEntry_sound {observations : Array (ToolchainReach × ExecutionBoundary ×
    ToolchainOrigin)} {key : ToolchainKey} {t : ToolchainBoundary}
    (h : toolchainEntry observations key = some t) :
    t.key = key ∧
      (∃ x ∈ observations, x.2.1.toolchainKey = key ∧ t.module = x.2.1.module ∧
        t.replacement = x.2.1.replacement ∧ t.origin = x.2.2) ∧
      ∀ reach ∈ t.reachedBy, ∃ y ∈ observations, y.1 = reach ∧ y.2.1.toolchainKey = key := by
  unfold toolchainEntry at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨n, b, o⟩, hfirst, rfl⟩ := h
  have hmem := Array.mem_filter.mp (Array.mem_of_getElem? hfirst)
  have hkey : b.toolchainKey = key := beq_iff_eq.mp hmem.2
  refine ⟨hkey, ⟨(n, b, o), hmem.1, hkey, rfl, rfl, rfl⟩, ?_⟩
  intro m hm
  obtain ⟨y, hy, rfl⟩ := Array.mem_map.mp ((mem_canonicalToolchainReaches _ _).mp hm)
  have hy := Array.mem_filter.mp hy
  exact ⟨y, hy.1, rfl, beq_iff_eq.mp hy.2⟩

/-- Every observation under a key yields that key's entry, which lists the observation's
environment and root. -/
theorem toolchainEntry_complete {observations : Array (ToolchainReach × ExecutionBoundary ×
    ToolchainOrigin)} {x : ToolchainReach × ExecutionBoundary × ToolchainOrigin}
    (hx : x ∈ observations) :
    ∃ t, toolchainEntry observations x.2.1.toolchainKey = some t ∧ x.1 ∈ t.reachedBy := by
  have hreach : x ∈ observations.filter (·.2.1.toolchainKey == x.2.1.toolchainKey) :=
    Array.mem_filter.mpr ⟨hx, beq_self_eq_true _⟩
  obtain ⟨⟨n, b, o⟩, hfirst⟩ : ∃ y,
      (observations.filter (·.2.1.toolchainKey == x.2.1.toolchainKey))[0]? = some y := by
    cases h : (observations.filter (·.2.1.toolchainKey == x.2.1.toolchainKey))[0]? with
    | none =>
        have := Array.getElem?_eq_none_iff.mp h
        have := Array.size_pos_of_mem hreach
        omega
    | some y => exact ⟨y, rfl⟩
  refine ⟨_, by simp only [toolchainEntry, hfirst, Option.map_some]; rfl, ?_⟩
  exact (mem_canonicalToolchainReaches _ _).mpr (Array.mem_map.mpr ⟨x, hreach, rfl⟩)

private theorem nodup_map_filterMap {α β : Type} {f : α → Option β} {g : β → α} {l : List α}
    (hl : l.Nodup) (hf : ∀ a b, f a = some b → g b = a) : ((l.filterMap f).map g).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    cases h : f a with
    | none => simpa [List.filterMap_cons, h] using ih hl.2
    | some b =>
      simp only [List.filterMap_cons, h, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih hl.2⟩
      intro hmem
      obtain ⟨c, hc, hgc⟩ := List.mem_map.mp hmem
      obtain ⟨a', ha', hfa'⟩ := List.mem_filterMap.mp hc
      have : a' = a := by rw [← hf a' c hfa', hgc, hf a b h]
      exact hl.1 (this ▸ ha')

private theorem eq_of_nodup_map {α β : Type} {f : α → β} {l : List α} (h : (l.map f).Nodup)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hab : f a = f b) : a = b := by
  induction l with
  | nil => cases ha
  | cons x l ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact (h.1 (hab ▸ List.mem_map_of_mem hb')).elim
    · exact (h.1 (hab ▸ List.mem_map_of_mem ha')).elim
    · exact ih h.2 ha' hb'

/-- No two entries of the toolchain trusted base share a constant and kind. -/
theorem toolchainBase_keys_nodup (environments : Array (String × ExecutionInventory)) :
    ((toolchainBase environments).map (·.key)).toList.Nodup := by
  simp only [toolchainBase, Array.toList_map, Array.toList_filterMap]
  exact nodup_map_filterMap (canonicalToolchainKeys_nodup _)
    (fun _ _ h => (toolchainEntry_sound h).1)

/-- Required meaning of the toolchain trusted-base report over the labeled execution accounts
of one audit: each toolchain-owned boundary of every account appears in exactly one entry, under
its constant and kind, which records the environment and root that reach it; every entry is such
a boundary with that boundary's module, replacement and origin, and every environment and root
it lists reaches it. -/
def ToolchainBaseContract
    (base : Array (String × ExecutionInventory) → Array ToolchainBoundary) : Prop :=
  ∀ environments,
    ((base environments).map (·.key)).toList.Nodup ∧
    (∀ e ∈ environments, ∀ r ∈ e.2.roots, ∀ b ∈ r.boundaries, b.toolchainOrigin?.isSome →
      ∃ t ∈ base environments, t.key = b.toolchainKey ∧ (e.1, r.name) ∈ t.reachedBy ∧
        ∀ t' ∈ base environments, t'.key = b.toolchainKey → t' = t) ∧
    (∀ t ∈ base environments, ∃ e ∈ environments, ∃ r ∈ e.2.roots, ∃ b ∈ r.boundaries,
      b.toolchainKey = t.key ∧ b.module = t.module ∧ b.replacement = t.replacement ∧
        b.toolchainOrigin? = some t.origin) ∧
    (∀ t ∈ base environments, ∀ reach ∈ t.reachedBy, ∃ e ∈ environments, e.1 = reach.1 ∧
      ∃ r ∈ e.2.roots, r.name = reach.2 ∧
        ∃ b ∈ r.boundaries, b.toolchainKey = t.key ∧ b.toolchainOrigin?.isSome)

/-- The gate reports the toolchain trusted base through this registration, whose `run` is
exactly `toolchainBase`. It does not establish that the toolchain's code is correct. -/
theorem checked_toolchainBase : Regula.ExecutableContract toolchainBase ToolchainBaseContract := by
  refine ⟨fun environments => ⟨toolchainBase_keys_nodup environments, ?_, ?_, ?_⟩⟩
  · intro e he r hr b hb ho
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp ho
    have hx : ((e.1, r.name), b, o) ∈ toolchainObservations environments :=
      mem_toolchainObservations.mpr ⟨e, he, r, hr, rfl, hb, ho⟩
    obtain ⟨t, ht, hreach⟩ := toolchainEntry_complete hx
    have hkey := (toolchainEntry_sound ht).1
    have hmem : t ∈ toolchainBase environments :=
      Array.mem_filterMap.mpr ⟨b.toolchainKey,
        (mem_canonicalToolchainKeys _ _).mpr (Array.mem_map.mpr ⟨_, hx, rfl⟩), ht⟩
    refine ⟨t, hmem, hkey, hreach, fun t' ht' hkey' => ?_⟩
    have nodup := toolchainBase_keys_nodup environments
    rw [Array.toList_map] at nodup
    exact eq_of_nodup_map nodup (Array.mem_toList_iff.mpr ht') (Array.mem_toList_iff.mpr hmem)
      (hkey'.trans hkey.symm)
  · intro t ht
    obtain ⟨key, -, hentry⟩ := Array.mem_filterMap.mp ht
    obtain ⟨hkey, ⟨x, hx, hxkey, hmodule, hreplacement, horigin⟩, -⟩ := toolchainEntry_sound hentry
    obtain ⟨e, he, r, hr, -, hb, ho⟩ := mem_toolchainObservations.mp hx
    exact ⟨e, he, r, hr, x.2.1, hb, hxkey.trans hkey.symm, hmodule.symm, hreplacement.symm,
      horigin ▸ ho⟩
  · intro t ht reach hreach
    obtain ⟨key, -, hentry⟩ := Array.mem_filterMap.mp ht
    obtain ⟨hkey, -, hreaches⟩ := toolchainEntry_sound hentry
    obtain ⟨y, hy, rfl, hykey⟩ := hreaches reach hreach
    obtain ⟨e, he, r, hr, hname, hb, ho⟩ := mem_toolchainObservations.mp hy
    exact ⟨e, he, by rw [hname], r, hr, by rw [hname], y.2.1, hb, hykey.trans hkey.symm,
      by simp [ho]⟩

end RegulaPolicy
