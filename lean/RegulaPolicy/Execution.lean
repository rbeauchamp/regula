import RegulaPolicy.Admission
import Regula.Contract
import Regula.Decision

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
@[regula_decision]
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
@[regula_decision]
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

/-- `boundaryFailures` reports nothing exactly when the boundary meets `BoundaryOK` under the
claim, whatever the root (`boundaryFailures_empty_iff`): nothing for an opaque constant run
through its kernel-checked body, and a failure for an unresolved boundary. The decision is over
one supplied boundary record; that the account lists every boundary a root reaches is the
collector's, and is not claimed. -/
theorem checked_boundaryFailures : Regula.ExecutableContract boundaryFailures (fun failures =>
    Regula.Decides (· = #[])
      (fun input : (ExecutionRoot × ExecutionClaim) × ExecutionBoundary =>
        BoundaryOK input.1.2 input.2)
      (Function.uncurry (Function.uncurry failures))) :=
  let root : ExecutionRoot :=
    { name := `root, «module» := `Module, boundaries := #[], unresolved := #[]
      closure := { nodes := #[`root]
                   visits := #[{ name := `root, moduleName := none, parent := none }] } }
  let body (account : BoundaryEvidence .opaqueComputation) : ExecutionBoundary :=
    { occurrence := 0, name := `body, «module» := `Module, owned := true
      boundary := .opaqueComputation, account, replacement := none }
  ⟨.of_iff (fun input => boundaryFailures_empty_iff input.1.1 input.1.2 input.2)
    ⟨((root, .checked), body (.checked .opaqueBody)), by decide⟩
    ⟨((root, .report), body (.unresolved none)), by decide⟩⟩

/-- A root with one unresolved path and no boundary: the refused input of
`checked_executionFailureRecords`. -/
private def unresolvedRoot : ExecutionRoot :=
  { name := `root, «module» := `Module, boundaries := #[], unresolved := #["path"]
    closure := { nodes := #[`root]
                 visits := #[{ name := `root, moduleName := none, parent := none }] } }

/-- `unresolvedRoot` alone is a valid inventory. Proved from the definition of validity, not by
evaluating its decision procedure, whose hashed name sets the kernel does not evaluate. -/
private theorem unresolvedRoot_valid : ExecutionValid #[unresolvedRoot] := by
  refine ⟨by simp [UniqueNames, unresolvedRoot], fun r member => ?_⟩
  obtain rfl := Array.mem_singleton.mp member
  have discovery : unresolvedRoot.closure.DiscoveryOK `root #[] := by
    intro k
    have first : k = ⟨0, by decide⟩ :=
      Fin.ext (by have := k.isLt; simp [unresolvedRoot] at this; omega)
    subst first
    simp [unresolvedRoot]
  have sorted : Std.ExtTreeSet.toList (CanonicalSet.normalize [`root]) = [`root] := by
    decide +kernel
  simp only [unresolvedRoot] at discovery
  simp [ExecutionRoot.Valid, ExecutionClosure.Valid, unresolvedRoot, Named, canonicalNames,
    canonicalEdges, sorted, discovery, ExecutionClosure.edges]
  exact ⟨rfl, rfl⟩

/-- `executionFailureRecords` reports nothing exactly when the inventory meets `ExecutionOK`
under the claim (`executionFailureRecords_empty_iff`): nothing for an inventory with no root, and
a failure for a root with an unresolved path. The decision is over the supplied account; that the
account covers every root and closure is the collector's, and is not claimed. -/
theorem checked_executionFailureRecords :
    Regula.ExecutableContract executionFailureRecords (fun records =>
      Regula.Decides (· = #[])
        (fun input : ExecutionInventory × ExecutionClaim => ExecutionOK input.1 input.2)
        (Function.uncurry records)) :=
  ⟨.of_iff (fun input => executionFailureRecords_empty_iff input.1 input.2)
    ⟨(⟨#[], by simp [ExecutionValid, UniqueNames]⟩, .report),
      (executionFailureRecords_empty_iff _ _).mpr (by simp [ExecutionOK])⟩
    ⟨(⟨#[unresolvedRoot], unresolvedRoot_valid⟩, .report), fun accepted => absurd
      (((executionFailureRecords_empty_iff _ _).mp accepted) _ (Array.mem_singleton.mpr rfl)).1
      (by simp [unresolvedRoot])⟩⟩

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

/-! ## One finding and one count for one trusted step

A root's account can hold several boundary records for one trusted step, in two ways.

*A restated boundary.* The collector records a constant-equality (`csimp`) candidate boundary for
each constant whose type is that equality, so two such constants give two records of one
replacement: the same constant, kind, replacement, correspondence and toolchain origin, differing
only in the candidate they cite as evidence.

*A `partial` implementation.* A `partial` implementation is a constant of `partial` definition
safety (`DefinitionSafety.partial`): the implementation a metaprogram such as Mathlib's
`compile_inductive%` adds for a recursor, or the `_unsafe_rec` helper Lean generates for a
`partial def`. The account records one as a partial-computation boundary whose constant is the
source of no helper edge (`ExecutionRoot.foldable`). The boundary of a constant whose compiled
code is such an implementation already trusts, without checked correspondence, that the
implementation's code runs in the constant's place; the implementation's own boundary adds that
it is `partial`. Three recorded relations give such a pair: a `csimp` candidate whose target is a
`partial` implementation, an `implemented_by` replacement whose target is one, and an opaque
constant with the `partial` helper Lean compiles it through (an author's `partial def` and its
`_unsafe_rec`). An author's `partial def` is not itself a `partial` implementation: it is that
opaque constant, recorded under the same kind with a helper edge from it. Named as the target of
a `csimp` candidate or an `implemented_by` replacement, it keeps its own finding and count, and
only its helper is reported with it.

The account keeps every record, and the decision's records (`executionFailureRecords`) one failure
for each. The findings (`executionFindings`) and the coverage counts (`executionSummary`) report a
restated boundary with the first record of it and a `partial` implementation with the boundary
that runs it, where both are trusted and have the same owner (both the toolchain's, with one
admitted origin, or neither): one finding, which names the implementation, and one counted
boundary. A toolchain-owned pair has no finding, and the toolchain trusted base lists it as one
entry that names the implementation (`toolchainBase`). Both relations are read
from the account's own members and edges, which the collector takes from the declared equalities,
the `implemented_by` attribute and the compiler's helper lookup; no name is parsed. Only trusted
records are folded, and a folded record fails and passes with the record it is reported with
(`executionFindings_empty_iff`). -/

/-- `a` and `b` record the same trusted boundary: both are trusted and they agree on the
constant, the kind, the replacement and the toolchain origin. They can differ in the evidence
they cite. -/
def ExecutionBoundary.restates (a b : ExecutionBoundary) : Bool :=
  a.correspondence == .trusted && b.correspondence == .trusted && a.name == b.name &&
    a.boundary == b.boundary && a.replacement == b.replacement &&
    a.toolchainOrigin? == b.toolchainOrigin?

/-- Boundary `b` of root `r` repeats an earlier record: a boundary of `r` with a smaller
occurrence number records the same trusted boundary (`ExecutionBoundary.restates`). -/
def ExecutionRoot.repeated (r : ExecutionRoot) (b : ExecutionBoundary) : Bool :=
  b.correspondence == .trusted &&
    r.boundaries.any fun a => a.occurrence < b.occurrence && a.restates b

/-- `b` is the boundary the account records for a `partial` implementation (a constant of
`partial` definition safety), whoever owns it: a trusted partial-computation boundary whose
constant is the source of no helper edge. The account records an opaque constant compiled through
a partial helper (a `partial def`) under the same kind (`BoundaryKind.partialComputation`), with a
helper edge from it (`ExecutionClosure.helperEdges`); that boundary is not foldable, whichever
boundary names its constant. -/
def ExecutionRoot.foldable (r : ExecutionRoot) (b : ExecutionBoundary) : Bool :=
  b.boundary == .partialComputation && b.correspondence == .trusted &&
    !r.closure.helperEdges.any (·.1 == b.name)

/-- Boundary `a` of root `r` carries boundary `b`: `a` names `b`'s constant as the code that
runs in its place, by its replacement or, for an opaque constant, by a helper edge; `a` is
trusted, has the same toolchain origin as `b` (both the toolchain's under one admitted origin, or
neither) and is not itself foldable; and `b` is foldable. A boundary whose replacement names a
`partial def` does not carry it, because that opaque constant's boundary is not foldable; the
`partial def`'s own boundary carries its helper. -/
def ExecutionRoot.carries (r : ExecutionRoot) (a b : ExecutionBoundary) : Bool :=
  (a.replacement == some b.name ||
      (a.boundary == .partialComputation && r.closure.helperEdges.contains (a.name, b.name))) &&
    a.correspondence == .trusted && a.toolchainOrigin? == b.toolchainOrigin? && !r.foldable a &&
      r.foldable b

/-- Boundary `b` of root `r` has no finding and no count of its own: it repeats an earlier
record (`ExecutionRoot.repeated`), or it is a `partial` implementation that a boundary of `r`
carries (`ExecutionRoot.carries`). -/
def ExecutionRoot.folded (r : ExecutionRoot) (b : ExecutionBoundary) : Bool :=
  r.repeated b || (r.foldable b && r.boundaries.any (r.carries · b))

/-- The later records of `r` that restate boundary `a`, in the account's order. -/
def ExecutionRoot.restatements (r : ExecutionRoot) (a : ExecutionBoundary) :
    Array ExecutionBoundary :=
  r.boundaries.filter fun b => a.occurrence < b.occurrence && a.restates b

/-- The boundaries of `r` that boundary `a` carries, each once, in the account's order: the
`partial` implementations its finding names. -/
def ExecutionRoot.implementations (r : ExecutionRoot) (a : ExecutionBoundary) :
    Array ExecutionBoundary :=
  r.boundaries.filter fun b => r.carries a b && !r.repeated b

/-- The boundaries of `r` reported on their own, in the account's order: every boundary that is
not folded. -/
def ExecutionRoot.reported (r : ExecutionRoot) : Array ExecutionBoundary :=
  r.boundaries.filter (!r.folded ·)

/-- What restating requires: both records are trusted and they agree on the constant, the kind,
the replacement and the toolchain origin. -/
theorem ExecutionBoundary.restates_spec {a b : ExecutionBoundary} (h : a.restates b = true) :
    a.correspondence = .trusted ∧ b.correspondence = .trusted ∧ a.name = b.name ∧
      a.boundary = b.boundary ∧ a.replacement = b.replacement ∧
      a.toolchainOrigin? = b.toolchainOrigin? := by
  simp only [ExecutionBoundary.restates, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- Restating is transitive. -/
theorem ExecutionBoundary.restates_trans {a b c : ExecutionBoundary} (ab : a.restates b = true)
    (bc : b.restates c = true) : a.restates c = true := by
  obtain ⟨ta, -, n, k, p, o⟩ := ExecutionBoundary.restates_spec ab
  obtain ⟨-, tc, n', k', p', o'⟩ := ExecutionBoundary.restates_spec bc
  simp [ExecutionBoundary.restates, ta, tc, n.trans n', k.trans k', p.trans p', o.trans o']

/-- Records of the same trusted boundary have the same failures, for every root and claim. -/
theorem boundaryFailures_restates (r : ExecutionRoot) (c : ExecutionClaim)
    {a b : ExecutionBoundary} (h : a.restates b = true) :
    boundaryFailures r c a = boundaryFailures r c b := by
  obtain ⟨ta, tb, n, k, -, o⟩ := ExecutionBoundary.restates_spec h
  simp [boundaryFailures, ta, tb, n, k, o]

/-- A foldable boundary is a trusted partial-computation boundary. -/
theorem ExecutionRoot.foldable_spec {r : ExecutionRoot} {b : ExecutionBoundary}
    (h : r.foldable b = true) :
    b.boundary = .partialComputation ∧ b.correspondence = .trusted := by
  simp only [ExecutionRoot.foldable, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2⟩

/-- What carrying requires of both boundaries: the carried one is foldable; the carrying one is
trusted, has the carried one's toolchain origin and is not foldable; and it names the carried
constant by its replacement or, as a partial-computation boundary, by a helper edge. -/
theorem ExecutionRoot.carries_spec {r : ExecutionRoot} {a b : ExecutionBoundary}
    (h : r.carries a b = true) :
    r.foldable b = true ∧ r.foldable a = false ∧ a.correspondence = .trusted ∧
      a.toolchainOrigin? = b.toolchainOrigin? ∧
      (a.replacement = some b.name ∨
        (a.boundary = .partialComputation ∧
          r.closure.helperEdges.contains (a.name, b.name) = true)) := by
  simp only [ExecutionRoot.carries, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at h
  exact ⟨h.2, h.1.2, h.1.1.1.2, h.1.1.2, h.1.1.1.1⟩

/-- A record of the same trusted boundary carries what the boundary carries. -/
theorem ExecutionRoot.carries_restates (r : ExecutionRoot) {a a' : ExecutionBoundary}
    (b : ExecutionBoundary) (h : a'.restates a = true) : r.carries a' b = r.carries a b := by
  obtain ⟨t', t, n, k, p, o⟩ := ExecutionBoundary.restates_spec h
  simp [ExecutionRoot.carries, ExecutionRoot.foldable, t', t, n, k, p, o]

/-- Every boundary of a root is reported on its own or folded. -/
theorem ExecutionRoot.reported_or_folded (r : ExecutionRoot) {b : ExecutionBoundary}
    (hb : b ∈ r.boundaries) : b ∈ r.reported ∨ r.folded b = true := by
  cases h : r.folded b
  · exact Or.inl (Array.mem_filter.mpr ⟨hb, by simp [h]⟩)
  · exact Or.inr rfl

/-- Every boundary of a root is, or restates, a boundary of the root that repeats no earlier
record: the first record of that trusted boundary. -/
theorem ExecutionRoot.first_record (r : ExecutionRoot) {b : ExecutionBoundary}
    (hb : b ∈ r.boundaries) :
    ∃ a ∈ r.boundaries, r.repeated a = false ∧ (a = b ∨ a.restates b = true) := by
  induction h : b.occurrence using Nat.strongRecOn generalizing b with
  | ind n ih =>
    cases repeated : r.repeated b
    · exact ⟨b, hb, repeated, Or.inl rfl⟩
    · simp only [ExecutionRoot.repeated, Bool.and_eq_true, Array.any_eq_true',
        decide_eq_true_eq] at repeated
      obtain ⟨-, a', ha', earlier, restates⟩ := repeated
      obtain ⟨a, ha, first, same⟩ := ih a'.occurrence (h ▸ earlier) ha' rfl
      refine ⟨a, ha, first, Or.inr ?_⟩
      rcases same with rfl | same
      · exact restates
      · exact ExecutionBoundary.restates_trans same restates

/-- **What is folded, and with what it is reported.** Every boundary `b` of a root is, or
restates, a boundary `b'` of the root that is itself reported on its own or is an implementation
of a boundary reported on its own. So a boundary without a finding or a count of its own is a
later record of a trusted boundary that has them, or a trusted `partial` implementation
(`ExecutionRoot.foldable`), or a later record of one, carried by a boundary with the same owner
that has them. -/
theorem ExecutionRoot.boundary_reported (r : ExecutionRoot) {b : ExecutionBoundary}
    (hb : b ∈ r.boundaries) :
    ∃ a ∈ r.reported, ∃ b' ∈ r.boundaries, (b' = b ∨ b'.restates b = true) ∧
      (a = b' ∨ b' ∈ r.implementations a) := by
  obtain ⟨b', hb', first, same⟩ := r.first_record hb
  cases folded : r.folded b'
  · exact ⟨b', Array.mem_filter.mpr ⟨hb', by simp [folded]⟩, b', hb', same, Or.inl rfl⟩
  · simp only [ExecutionRoot.folded, first, Bool.false_or, Bool.and_eq_true,
      Array.any_eq_true'] at folded
    obtain ⟨-, a', ha', carried⟩ := folded
    obtain ⟨a, ha, firstA, sameA⟩ := r.first_record ha'
    have carries : r.carries a b' = true := by
      rcases sameA with rfl | sameA
      · exact carried
      · rw [r.carries_restates b' sameA]; exact carried
    have unfolded : r.folded a = false := by
      simp [ExecutionRoot.folded, firstA, (ExecutionRoot.carries_spec carries).2.1]
    exact ⟨a, Array.mem_filter.mpr ⟨ha, by simp [unfolded]⟩, b', hb', same,
      Or.inr (Array.mem_filter.mpr ⟨hb', by simp [carries, first]⟩)⟩

/-- A folded boundary is trusted: an unresolved or checked boundary is always reported on its
own. -/
theorem ExecutionRoot.folded_trusted {r : ExecutionRoot} {b : ExecutionBoundary}
    (h : r.folded b = true) : b.correspondence = .trusted := by
  simp only [ExecutionRoot.folded, ExecutionRoot.repeated, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at h
  rcases h with ⟨trusted, -⟩ | ⟨foldable, -⟩
  · exact trusted
  · exact (ExecutionRoot.foldable_spec foldable).2

/-- The text a finding adds for the implementations its boundary carries: each one's constant
and kind, in order; empty when there is none. -/
def implementationsText (implementations : Array ExecutionBoundary) : String :=
  String.join (implementations.toList.map fun b =>
    s!", with its implementation {b.name} ({b.boundary})")

/-- One boundary's findings: none for a folded boundary, and otherwise its failure
(`boundaryFailures`) with the implementations it carries named after its detail. -/
def boundaryFindings (root : ExecutionRoot) (claim : ExecutionClaim)
    (b : ExecutionBoundary) : Array ExecutionFailure :=
  let failures := boundaryFailures root claim b
  if failures.isEmpty then #[]
  else if root.folded b then #[]
  else failures.map fun f =>
    { f with detail := f.detail ++ implementationsText (root.implementations b) }

/-- Skipping folding when there are no failures preserves every finding and its detail,
in order, for arbitrary supplied accounts. -/
theorem boundaryFindings_eq (root : ExecutionRoot) (claim : ExecutionClaim)
    (b : ExecutionBoundary) :
    boundaryFindings root claim b =
      if root.folded b then #[]
      else (boundaryFailures root claim b).map fun f =>
        { f with detail := f.detail ++ implementationsText (root.implementations b) } := by
  by_cases empty : (boundaryFailures root claim b).isEmpty = true
  · have failures : boundaryFailures root claim b = #[] := Array.isEmpty_iff.mp empty
    simp [boundaryFindings, failures]
  · simp [boundaryFindings, empty]

/-- A root's findings: each unresolved path, then each boundary's findings, in the order of
`rootFailures`. -/
def rootFindings (root : ExecutionRoot) (claim : ExecutionClaim) : Array ExecutionFailure :=
  root.unresolved.map (fun item => ⟨.executionUnresolved, root, s!"{root.name}: {item}"⟩) ++
    root.boundaries.flatMap (boundaryFindings root claim)

/-- The findings the gate reports for the inventory under `claim`: the decision's records
(`executionFailureRecords`) with each folded boundary's record reported in the finding of the
boundary it is reported with (`failure_reported`). They are empty exactly when `ExecutionOK`
holds (`executionFindings_empty_iff`). -/
@[regula_decision]
def executionFindings (inventory : ExecutionInventory)
    (claim : ExecutionClaim) : Array ExecutionFailure :=
  inventory.roots.flatMap (fun root => rootFindings root claim)

/-- The failure of a trusted boundary: one `executionBoundary` record under a checked claim when
the toolchain does not own it, and none otherwise. -/
private theorem boundaryFailures_trusted (r : ExecutionRoot) (c : ExecutionClaim)
    {b : ExecutionBoundary} (trusted : b.correspondence = .trusted) :
    boundaryFailures r c b =
      if c = .checked ∧ b.toolchainOrigin? = none then
        #[⟨.executionBoundary, r, s!"{r.name} reaches {b.name} ({b.boundary})"⟩]
      else #[] := by
  unfold boundaryFailures
  cases c <;> cases owner : b.toolchainOrigin? <;> simp [trusted]

/-- The findings of a boundary reported on its own are its failures, each with the
implementations it carries named after its detail. -/
private theorem boundaryFindings_reported {r : ExecutionRoot} (c : ExecutionClaim)
    {a : ExecutionBoundary} (ha : a ∈ r.reported) :
    boundaryFindings r c a = (boundaryFailures r c a).map fun f =>
      { f with detail := f.detail ++ implementationsText (r.implementations a) } := by
  have unfolded : r.folded a = false := by simpa using (Array.mem_filter.mp ha).2
  simp [boundaryFindings_eq, unfolded]

/-- A root whose boundaries have no findings has no boundary failure: a folded boundary passes
with the boundary it is reported with. -/
private theorem boundaryFailures_empty_of_findings {r : ExecutionRoot} {c : ExecutionClaim}
    (h : ∀ b ∈ r.boundaries, boundaryFindings r c b = #[]) {b : ExecutionBoundary}
    (hb : b ∈ r.boundaries) : boundaryFailures r c b = #[] := by
  obtain ⟨a, ha, b', hb', same, place⟩ := r.boundary_reported hb
  have passes : boundaryFailures r c a = #[] := by
    simpa [boundaryFindings_reported c ha] using h a (Array.mem_filter.mp ha).1
  have passes' : boundaryFailures r c b' = #[] := by
    rcases place with rfl | implementation
    · exact passes
    · have carried : r.carries a b' = true := by
        have := (Array.mem_filter.mp implementation).2
        simp only [Bool.and_eq_true] at this
        exact this.1
      obtain ⟨foldable, -, trusted, owner, -⟩ := ExecutionRoot.carries_spec carried
      obtain ⟨-, trusted'⟩ := ExecutionRoot.foldable_spec foldable
      rw [boundaryFailures_trusted r c trusted] at passes
      rw [boundaryFailures_trusted r c trusted', ← owner]
      by_cases fails : c = .checked ∧ a.toolchainOrigin? = none <;> simp_all
  rcases same with rfl | same
  · exact passes'
  · rw [← boundaryFailures_restates r c same]; exact passes'

/-- **The findings decide exactly what the records decide.** They are empty exactly when the
execution predicate holds, for every admitted inventory and claim, so folding hides no failure:
a folded boundary fails only with the boundary it is reported with, which has a finding.

# Intent

The gate decides an execution claim from the findings it prints, and the findings leave out the
record of a boundary that is reported with another. That must never turn a failing account into
a passing one, or a passing one into a failing one: for every account the checker admits and
for both claims, the gate must print no finding exactly when the account has no unresolved path
and every boundary of every root meets the claim, the folded ones included.

The requirement concerns the account as supplied. It does not require that the account lists
every boundary the program reaches, that the collector recorded which constant is compiled to
which definition truthfully, or that any trusted code is correct. -/
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

/-- `executionFindings`, the findings the checker reports, are none exactly when the inventory
meets `ExecutionOK` under the claim (`executionFindings_empty_iff`), with the witnesses of
`checked_executionFailureRecords`. The decision is over the supplied account; that the account
covers every root and closure is the collector's, and is not claimed. -/
theorem checked_executionFindings :
    Regula.ExecutableContract executionFindings (fun findings =>
      Regula.Decides (· = #[])
        (fun input : ExecutionInventory × ExecutionClaim => ExecutionOK input.1 input.2)
        (Function.uncurry findings)) :=
  ⟨.of_iff (fun input => executionFindings_empty_iff input.1 input.2)
    ⟨(⟨#[], by simp [ExecutionValid, UniqueNames]⟩, .report),
      (executionFindings_empty_iff _ _).mpr (by simp [ExecutionOK])⟩
    ⟨(⟨#[unresolvedRoot], unresolvedRoot_valid⟩, .report), fun accepted => absurd
      (((executionFindings_empty_iff _ _).mp accepted) _ (Array.mem_singleton.mpr rfl)).1
      (by simp [unresolvedRoot])⟩⟩

/-- A root's findings are none exactly when it has no unresolved path and each of its boundaries
meets the claim (`BoundaryOK`). -/
theorem rootFindings_empty_iff (r : ExecutionRoot) (c : ExecutionClaim) :
    rootFindings r c = #[] ↔ r.unresolved = #[] ∧ ∀ b ∈ r.boundaries, BoundaryOK c b := by
  simp only [rootFindings, Array.flatMap_eq_empty_iff, Array.append_eq_empty_iff,
    Array.map_eq_empty_iff]
  constructor
  · intro h
    exact ⟨h.1, fun b hb =>
      (boundaryFailures_empty_iff r c b).mp (boundaryFailures_empty_of_findings h.2 hb)⟩
  · intro h
    exact ⟨h.1, fun b hb => by
      simp [boundaryFindings, (boundaryFailures_empty_iff r c b).mpr (h.2 b hb)]⟩

/-- The strongest of the execution claims `requests`: checked when one of them is, and report
otherwise. -/
def strongestClaim (requests : Array ExecutionClaim) : ExecutionClaim :=
  if ExecutionClaim.checked ∈ requests then .checked else .report

/-- A boundary meets the strongest of some execution claims exactly when it meets each of them:
a boundary that meets checked meets report (`BoundaryOK`). -/
theorem boundaryOK_strongestClaim {requests : Array ExecutionClaim} (nonempty : requests ≠ #[])
    (b : ExecutionBoundary) :
    BoundaryOK (strongestClaim requests) b ↔ ∀ request ∈ requests, BoundaryOK request b := by
  unfold strongestClaim
  split
  · rename_i checked
    refine ⟨fun ok request _ => ?_, fun all => all _ checked⟩
    cases request
    · exact ⟨ok.1, .inl rfl⟩
    · exact ok
  · rename_i unchecked
    have report : ∀ request ∈ requests, request = .report := by
      intro request member
      cases request
      · rfl
      · exact absurd member unchecked
    refine ⟨fun ok request member => by rw [report request member]; exact ok, fun all => ?_⟩
    obtain ⟨request, member⟩ : ∃ request, request ∈ requests := by
      rcases requests with ⟨_ | ⟨request, _⟩⟩
      · exact absurd rfl nonempty
      · exact ⟨request, by simp⟩
    have ok := all request member
    rwa [report request member] at ok

/-- The findings the gate reports for the inventory when each root is held to the strongest of
the execution claims that `requests` asks of it (`strongestClaim`, `rootFindings`), as a project
audit asks each root's requests of its declarations' modules (`rootRequestsAmong`). -/
def executionFindingsFor (inventory : ExecutionInventory)
    (requests : ExecutionRoot → Array ExecutionClaim) : Array ExecutionFailure :=
  inventory.roots.flatMap fun root => rootFindings root (strongestClaim (requests root))

/-- With each root's requests nonempty, `executionFindingsFor` reports nothing exactly when each
root has no unresolved path and each of its boundaries meets each claim requested of it, the
execution condition of a project's acceptance (`LocalStageOK`). -/
theorem executionFindingsFor_empty_iff (inventory : ExecutionInventory)
    (requests : ExecutionRoot → Array ExecutionClaim)
    (nonempty : ∀ r ∈ inventory.roots, requests r ≠ #[]) :
    executionFindingsFor inventory requests = #[] ↔
      ∀ r ∈ inventory.roots, ∀ request ∈ requests r,
        r.unresolved = #[] ∧ ∀ b ∈ r.boundaries, BoundaryOK request b := by
  simp only [executionFindingsFor, Array.flatMap_eq_empty_iff, rootFindings_empty_iff]
  constructor
  · intro h r hr request member
    exact ⟨(h r hr).1, fun b hb =>
      (boundaryOK_strongestClaim (nonempty r hr) b).mp ((h r hr).2 b hb) request member⟩
  · intro h r hr
    obtain ⟨request, member⟩ : ∃ request, request ∈ requests r := by
      rcases hreq : requests r with ⟨_ | ⟨request, _⟩⟩
      · exact absurd hreq (nonempty r hr)
      · exact ⟨request, by simp⟩
    exact ⟨(h r hr request member).1, fun b hb =>
      (boundaryOK_strongestClaim (nonempty r hr) b).mpr fun other otherMember =>
        (h r hr other otherMember).2 b hb⟩

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
inventory, a boundary `a` reported on its own in that root has a failure of the same kind and
root whose finding is among the gate's: that failure with the implementations `a` carries named
after its detail (`implementationsText`). And `a` accounts for `b`: some boundary `b'` of the
root is `b` or a record of the same trusted boundary, with `b`'s constant and kind, and `a` is
`b'` or has `b'` among its implementations.

# Intent

A finding is what tells the author that a boundary fails a checked execution claim. When one
trusted step has several boundary records in a root's account, the gate prints one finding for
it. Every failure the decision records must still reach the author: the failing boundary must
be the subject of a printed finding of the same rule and root, or be named by constant and kind
in the text of one, or be another record of a boundary that is. No failure may be dropped
because its boundary was grouped with another.

The requirement concerns the account as supplied: it does not require that the collector
recorded the grouped boundaries truthfully or completely. It also does not require a separate
line per record; one finding for one trusted step is the purpose. -/
theorem failure_reported {i : ExecutionInventory} {r : ExecutionRoot} (hr : r ∈ i.roots)
    {b : ExecutionBoundary} (hb : b ∈ r.boundaries) (c : ExecutionClaim)
    {f : ExecutionFailure} (hf : f ∈ boundaryFailures r c b) :
    ∃ a ∈ r.reported, ∃ b' ∈ r.boundaries, (b' = b ∨ b'.restates b = true) ∧
      (a = b' ∨ b' ∈ r.implementations a) ∧
      ∃ g ∈ boundaryFailures r c a, g.id = f.id ∧ g.root = r ∧
        { g with detail := g.detail ++ implementationsText (r.implementations a) } ∈
          executionFindings i c := by
  obtain ⟨a, ha, b', hb', same, place⟩ := r.boundary_reported hb
  have hf' : f ∈ boundaryFailures r c b' := by
    rcases same with rfl | same
    · exact hf
    · rw [boundaryFailures_restates r c same]; exact hf
  have reported : ∀ g ∈ boundaryFailures r c a,
      { g with detail := g.detail ++ implementationsText (r.implementations a) } ∈
        executionFindings i c := fun g hg => by
    apply boundaryFindings_mem hr (Array.mem_filter.mp ha).1 c
    rw [boundaryFindings_reported c ha]
    exact Array.mem_map.mpr ⟨g, hg, rfl⟩
  refine ⟨a, ha, b', hb', same, place, ?_⟩
  rcases place with rfl | implementation
  · exact ⟨f, hf', rfl, boundaryFailures_root hf', reported f hf'⟩
  · have carried : r.carries a b' = true := by
      have := (Array.mem_filter.mp implementation).2
      simp only [Bool.and_eq_true] at this
      exact this.1
    obtain ⟨foldable, -, trusted, owner, -⟩ := ExecutionRoot.carries_spec carried
    obtain ⟨-, trusted'⟩ := ExecutionRoot.foldable_spec foldable
    rw [boundaryFailures_trusted r c trusted'] at hf'
    split at hf'
    next fails =>
      obtain ⟨rfl, unowned⟩ := fails
      rw [Array.mem_singleton] at hf'
      have failure : (⟨.executionBoundary, r, s!"{r.name} reaches {a.name} ({a.boundary})"⟩ :
          ExecutionFailure) ∈ boundaryFailures r .checked a := by
        simp [boundaryFailures_trusted r .checked trusted, owner.trans unowned]
      exact ⟨_, failure, by rw [hf'], rfl, reported _ failure⟩
    next => simp at hf'

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
  · rw [boundaryFindings_eq] at hg
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
  rw [boundaryFindings_eq]
  split <;> simp [Function.comp_def]

/-- Named execution-coverage counts rendered by gate output. -/
structure ExecutionSummary where
  /-- The number of execution-root observations. -/
  roots : Nat
  /-- The number of boundary observations reported on their own, over all roots
  (`ExecutionRoot.reported`). A folded observation (`ExecutionRoot.folded`), a later record of
  one trusted boundary of its root or a `partial` implementation reported with the boundary that
  runs it, is counted with the boundary it is reported with, not again. -/
  boundaries : Nat
  /-- The number of those boundary observations with checked correspondence. -/
  checked : Nat
  /-- The number of those boundary observations with trusted correspondence. Every folded
  observation is trusted (`ExecutionRoot.folded_trusted`). -/
  trusted : Nat
  /-- The number of unresolved diagnostics: unresolved root paths plus unresolved boundaries. -/
  unresolved : Nat
  deriving Repr, DecidableEq

/-- Every boundary observation of the account, in root order, without deduplication. -/
def ExecutionInventory.boundaries (inventory : ExecutionInventory) : Array ExecutionBoundary :=
  inventory.roots.flatMap (·.boundaries)

/-- Every boundary observation reported on its own (`ExecutionRoot.reported`), in root order,
without deduplication across roots: the account's boundaries without each folded one
(`ExecutionRoot.folded`), which is a later record of one trusted boundary of its root, reported
with the first, or a `partial` implementation reported with the boundary that runs it. -/
def ExecutionInventory.reported (inventory : ExecutionInventory) : Array ExecutionBoundary :=
  inventory.roots.flatMap (·.reported)

/-- Required meaning of the rendered counts. Roots and boundaries count observations, not
distinct runtime paths. The boundary counts range over the boundaries reported on their own
(`ExecutionInventory.reported`): a later record of one trusted boundary of a root is counted
with the first, and a `partial` implementation reported with the boundary that runs it is
counted with that boundary, not again. `unresolved` is the
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

/-- **Every boundary of the account is counted or reported with a counted one.** Each boundary
of a root of the inventory is among the reported boundaries the counts range over, or is folded:
a later record of a trusted boundary, or a trusted `partial` implementation that a boundary of
its root carries, and in either case accounted for by a reported boundary of the root
(`ExecutionRoot.boundary_reported`). -/
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
  rw [boundaryFindings_eq]
  split
  next folded =>
    have count := boundaryFailures_unresolved root claim b
    rw [ExecutionRoot.folded_trusted folded] at count
    exact (Array.countP_empty ..).trans count.symm
  next => simp [Array.countP_map, Function.comp_def]

/-- The gate renders these counts through this registration, whose `run` is exactly
`executionSummary`. It does not count distinct runtime paths or authenticate extraction. -/
theorem checked_summary : Regula.ExecutableContract executionSummary SummaryContract :=
  ⟨fun inventory => ⟨rfl, rfl, Array.countP_eq_size_filter .., Array.countP_eq_size_filter ..,
    executionSummary_unresolved inventory⟩⟩


/-! ## The toolchain trusted base

A toolchain-owned boundary passes every claim, so it never becomes a failure record. The
report lists it instead once across every audited environment, with every environment and root
that reaches it, rather than once per root or once per environment. A `partial` implementation
the toolchain owns (the `_unsafe_rec` helper Lean compiles a toolchain `partial def` through) is
one trusted step with the boundary that carries it (`ExecutionRoot.carries`): when every root of
the audit that reaches the implementation also holds a boundary that carries it there, the
implementation has no entry of its own, and the entry of each boundary that carries it names it
(`ToolchainBoundary.implementations`). Otherwise it keeps its own entry. -/

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
  /-- The constants of the `partial` implementations this boundary carries
  (`ExecutionRoot.carries`) that have no entry of their own, because every root that reaches one
  holds a boundary that carries it there (`toolchainFolded`), sorted and without duplicates: a
  toolchain `partial def`'s entry names the `_unsafe_rec` helper Lean compiles it through. -/
  implementations : Array Lean.Name
  deriving Repr, DecidableEq

/-- The report's key of an entry: its constant and kind. -/
def ToolchainBoundary.key (t : ToolchainBoundary) : ToolchainKey := (t.name, t.boundary)

/-- One toolchain-owned boundary observation of the labeled accounts. -/
structure ToolchainObservation where
  /-- The environment and root that reach the boundary. -/
  reach : ToolchainReach
  /-- The boundary record. -/
  boundary : ExecutionBoundary
  /-- Its admitted toolchain origin. -/
  origin : ToolchainOrigin
  /-- The keys of the boundaries of the same root that carry it (`ExecutionRoot.carries`), in
  the root's order; empty when no boundary of the root carries it. -/
  carriers : Array ToolchainKey

/-- Every toolchain-owned boundary observation of the labeled accounts, with the environment and
root that reach it, its admitted origin and the boundaries of its root that carry it, in
environment and root order. -/
def toolchainObservations (environments : Array (String × ExecutionInventory)) :
    Array ToolchainObservation :=
  environments.flatMap fun environment => environment.2.roots.flatMap fun root =>
    root.boundaries.filterMap fun b =>
      b.toolchainOrigin?.map fun o =>
        { reach := (environment.1, root.name), boundary := b, origin := o
          carriers := if root.foldable b then
            (root.boundaries.filter (root.carries · b)).map (·.toolchainKey) else #[] }

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

/-- The report entry of the observations `reaching` under one key, naming `implementations`:
the constant, module, kind, replacement and origin of the first, with every environment and root
among them; `none` when there is none. -/
def toolchainEntryOf (reaching : Array ToolchainObservation)
    (implementations : Array Lean.Name) : Option ToolchainBoundary :=
  reaching[0]?.map fun x =>
    { name := x.boundary.name, «module» := x.boundary.module, boundary := x.boundary.boundary
      replacement := x.boundary.replacement, origin := x.origin
      reachedBy := canonicalToolchainReaches (reaching.map (·.reach))
      implementations := implementations }

/-- The key has no entry of its own: every observation under it is carried in its root, so every
root that reaches the boundary also holds a boundary that carries it. -/
def toolchainFolded (observations : Array ToolchainObservation) (key : ToolchainKey) : Bool :=
  (observations.filter (·.boundary.toolchainKey == key)).all (!·.carriers.isEmpty)

/-- The constants an entry of the key names as its implementations: those of the observations
under a folded key (`toolchainFolded`) that a boundary under the key carries, sorted and without
duplicates. -/
def toolchainImplementations (observations : Array ToolchainObservation) (key : ToolchainKey) :
    Array Lean.Name :=
  canonicalNames
    ((((observations.filter (toolchainFolded observations ·.boundary.toolchainKey)).flatMap
      fun x => x.carriers.map (·, x.boundary.name)).filter (·.1 == key)).map (·.2))

/-- The report entry of one key: `none` when the key is folded (`toolchainFolded`) or nothing is
observed under it, and otherwise the constant, module, kind, replacement and origin of the key's
first observation, with every environment and root that reaches the key and the implementations
it carries (`toolchainImplementations`). -/
def toolchainEntry (observations : Array ToolchainObservation) (key : ToolchainKey) :
    Option ToolchainBoundary :=
  if toolchainFolded observations key then none
  else toolchainEntryOf (observations.filter (·.boundary.toolchainKey == key))
    (toolchainImplementations observations key)

/-- The elements under each key, in their order (`groupByKey_getD`), gathered in one pass
instead of one pass for each key, each key's array updated in place. -/
def groupByKey {α : Type} (key : α → ToolchainKey) (xs : Array α) :
    Std.HashMap ToolchainKey (Array α) :=
  xs.foldl (init := {}) fun byKey x => byKey.alter (key x) fun a? => some ((a?.getD #[]).push x)

private theorem foldl_groupByKey_getD {α : Type} (key : α → ToolchainKey) (l : List α)
    (byKey : Std.HashMap ToolchainKey (Array α)) (k : ToolchainKey) :
    (l.foldl (fun byKey x => byKey.alter (key x) fun a? => some ((a?.getD #[]).push x))
        byKey).getD k #[] =
      byKey.getD k #[] ++ (l.filter (key · == k)).toArray := by
  induction l generalizing byKey with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, Std.HashMap.getD_alter]
    by_cases same : key x = k
    · subst same
      simp [Std.HashMap.getD_eq_getD_getElem?]
    · simp [same]

/-- The elements `groupByKey` gathers under a key are exactly those under it, in their order. -/
theorem groupByKey_getD {α : Type} (key : α → ToolchainKey) (xs : Array α) (k : ToolchainKey) :
    (groupByKey key xs).getD k #[] = xs.filter (key · == k) := by
  rw [groupByKey, ← Array.foldl_toList, foldl_groupByKey_getD]
  rw [Std.HashMap.getD_empty, Array.empty_append, ← Array.toList_filter, Array.toArray_toList]

/-- The toolchain trusted base of the labeled execution accounts of one audit: each
toolchain-owned boundary once, in key order, with every environment and root that reaches it,
except a `partial` implementation that every root reaching it carries, which the entry of each
boundary carrying it names instead (`checked_toolchainBase`). Each key's entry is built from the
observations gathered under it (`toolchainBase_eq`). -/
def toolchainBase (environments : Array (String × ExecutionInventory)) :
    Array ToolchainBoundary :=
  let observations := toolchainObservations environments
  let byKey := groupByKey (·.boundary.toolchainKey) observations
  let foldedKeys := byKey.map fun _ xs => xs.all (!·.carriers.isEmpty)
  let folded (key : ToolchainKey) : Bool := foldedKeys.getD key true
  let named := groupByKey (·.1) ((observations.filter (folded ·.boundary.toolchainKey)).flatMap
    fun x => x.carriers.map (·, x.boundary.name))
  (canonicalToolchainKeys (observations.map (·.boundary.toolchainKey))).filterMap fun key =>
    if folded key then none
    else toolchainEntryOf (byKey.getD key #[]) (canonicalNames ((named.getD key #[]).map (·.2)))

/-- Testing each key's group once gives the test of the group under any key, absent ones
included. -/
private theorem getD_map_all {α : Type} (byKey : Std.HashMap ToolchainKey (Array α))
    (p : α → Bool) (k : ToolchainKey) :
    (byKey.map fun _ xs => xs.all p).getD k true = (byKey.getD k #[]).all p := by
  simp only [Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getElem?_map]
  cases byKey[k]? <;> simp

/-- Each entry of `toolchainBase` is `toolchainEntry` of its key over all the observations. -/
theorem toolchainBase_eq (environments : Array (String × ExecutionInventory)) :
    toolchainBase environments =
      (canonicalToolchainKeys
        ((toolchainObservations environments).map (·.boundary.toolchainKey))).filterMap
        (toolchainEntry (toolchainObservations environments)) := by
  simp only [toolchainBase, getD_map_all, groupByKey_getD]
  rfl

/-- Only a foldable boundary has a carrier (`ExecutionRoot.carries_spec`), so gathering the
carriers of a foldable boundary alone gathers them all. -/
theorem ExecutionRoot.carriers_eq (r : ExecutionRoot) (b : ExecutionBoundary) :
    (if r.foldable b then (r.boundaries.filter (r.carries · b)).map (·.toolchainKey) else #[]) =
      (r.boundaries.filter (r.carries · b)).map (·.toolchainKey) := by
  split
  · rfl
  · next unfoldable =>
    rw [Array.filter_eq_empty_iff.mpr fun a _ h => unfoldable (ExecutionRoot.carries_spec h).1,
      Array.map_empty]

theorem mem_toolchainObservations {environments : Array (String × ExecutionInventory)}
    {x : ToolchainObservation} :
    x ∈ toolchainObservations environments ↔
      ∃ e ∈ environments, ∃ r ∈ e.2.roots, x.reach = (e.1, r.name) ∧ x.boundary ∈ r.boundaries ∧
        x.boundary.toolchainOrigin? = some x.origin ∧
        x.carriers = (r.boundaries.filter (r.carries · x.boundary)).map (·.toolchainKey) := by
  rcases x with ⟨reach, b, o, carriers⟩
  simp only [toolchainObservations, ExecutionRoot.carriers_eq, Array.mem_flatMap,
    Array.mem_filterMap, Option.map_eq_some_iff, ToolchainObservation.mk.injEq]
  constructor
  · rintro ⟨e, he, r, hr, b', hb', o', ho', rfl, rfl, rfl, rfl⟩
    exact ⟨e, he, r, hr, rfl, hb', ho', rfl⟩
  · rintro ⟨e, he, r, hr, rfl, hb, ho, rfl⟩
    exact ⟨e, he, r, hr, b, hb, o, ho, rfl, rfl, rfl, rfl⟩

/-- An observation's carriers are empty exactly when no boundary of its root carries it. -/
theorem carriers_isEmpty {x : ToolchainObservation} {r : ExecutionRoot}
    (hcarriers : x.carriers = (r.boundaries.filter (r.carries · x.boundary)).map
      (·.toolchainKey)) :
    x.carriers.isEmpty = true ↔ ∀ a ∈ r.boundaries, r.carries a x.boundary = false := by
  rw [hcarriers, Array.isEmpty_iff, Array.map_eq_empty_iff, Array.filter_eq_empty_iff]
  simp

/-- A key is folded exactly when every observation under it has a carrier. -/
theorem toolchainFolded_eq_false {observations : Array ToolchainObservation}
    {key : ToolchainKey} :
    toolchainFolded observations key = false ↔
      ∃ x ∈ observations, x.boundary.toolchainKey = key ∧ x.carriers.isEmpty = true := by
  simp only [toolchainFolded, Array.all_eq_false', Array.mem_filter, beq_iff_eq,
    Bool.not_eq_true']
  constructor
  · rintro ⟨x, ⟨hx, hkey⟩, empty⟩
    exact ⟨x, hx, hkey, by simpa using empty⟩
  · rintro ⟨x, hx, hkey, empty⟩
    exact ⟨x, ⟨hx, hkey⟩, by simpa using empty⟩

/-- The implementations of a key are the constants of the observations under folded keys that
a boundary under the key carries. -/
theorem mem_toolchainImplementations {observations : Array ToolchainObservation}
    {key : ToolchainKey} {n : Lean.Name} :
    n ∈ toolchainImplementations observations key ↔
      ∃ x ∈ observations, toolchainFolded observations x.boundary.toolchainKey = true ∧
        key ∈ x.carriers ∧ x.boundary.name = n := by
  simp only [toolchainImplementations, mem_canonicalNames, Array.mem_map, Array.mem_filter,
    Array.mem_flatMap, beq_iff_eq]
  constructor
  · rintro ⟨⟨k, m⟩, ⟨⟨x, ⟨hx, folded⟩, c, hc, same⟩, rfl⟩, rfl⟩
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨x, hx, folded, hc, rfl⟩
  · rintro ⟨x, hx, folded, hc, rfl⟩
    exact ⟨(key, x.boundary.name), ⟨⟨x, ⟨hx, folded⟩, key, hc, rfl⟩, rfl⟩, rfl⟩

/-- What an entry reports: its key, which is not folded, the fields of an observation under that
key, reaches that each reach the key, and the key's implementations. -/
theorem toolchainEntry_sound {observations : Array ToolchainObservation} {key : ToolchainKey}
    {t : ToolchainBoundary} (h : toolchainEntry observations key = some t) :
    t.key = key ∧ toolchainFolded observations key = false ∧
      (∃ x ∈ observations, x.boundary.toolchainKey = key ∧ t.module = x.boundary.module ∧
        t.replacement = x.boundary.replacement ∧ t.origin = x.origin) ∧
      (∀ reach ∈ t.reachedBy, ∃ y ∈ observations, y.reach = reach ∧
        y.boundary.toolchainKey = key) ∧
      t.implementations = toolchainImplementations observations key := by
  unfold toolchainEntry at h
  split at h
  · cases h
  next unfolded =>
    unfold toolchainEntryOf at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨x, hfirst, rfl⟩ := h
    have hmem := Array.mem_filter.mp (Array.mem_of_getElem? hfirst)
    have hkey : x.boundary.toolchainKey = key := beq_iff_eq.mp hmem.2
    refine ⟨hkey, by simpa using unfolded, ⟨x, hmem.1, hkey, rfl, rfl, rfl⟩, ?_, rfl⟩
    intro m hm
    obtain ⟨y, hy, rfl⟩ := Array.mem_map.mp ((mem_canonicalToolchainReaches _ _).mp hm)
    have hy := Array.mem_filter.mp hy
    exact ⟨y, hy.1, rfl, beq_iff_eq.mp hy.2⟩

/-- Every observation under a key that is not folded yields that key's entry, which lists the
observation's environment and root. -/
theorem toolchainEntry_complete {observations : Array ToolchainObservation}
    {x : ToolchainObservation} (hx : x ∈ observations)
    (unfolded : toolchainFolded observations x.boundary.toolchainKey = false) :
    ∃ t, toolchainEntry observations x.boundary.toolchainKey = some t ∧ x.reach ∈ t.reachedBy := by
  have hreach :
      x ∈ observations.filter (·.boundary.toolchainKey == x.boundary.toolchainKey) :=
    Array.mem_filter.mpr ⟨hx, beq_self_eq_true _⟩
  obtain ⟨y, hfirst⟩ : ∃ y,
      (observations.filter (·.boundary.toolchainKey == x.boundary.toolchainKey))[0]? =
        some y := by
    cases h : (observations.filter (·.boundary.toolchainKey == x.boundary.toolchainKey))[0]? with
    | none =>
        have := Array.getElem?_eq_none_iff.mp h
        have := Array.size_pos_of_mem hreach
        omega
    | some y => exact ⟨y, rfl⟩
  refine ⟨_, by simp only [toolchainEntry, unfolded, toolchainEntryOf, hfirst, Option.map_some,
    Bool.false_eq_true, ↓reduceIte]; rfl, ?_⟩
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
  simp only [toolchainBase_eq, Array.toList_map, Array.toList_filterMap]
  exact nodup_map_filterMap (canonicalToolchainKeys_nodup _)
    (fun _ _ h => (toolchainEntry_sound h).1)

/-- Every entry of the toolchain trusted base is the entry of its own key. -/
theorem toolchainBase_entry {environments : Array (String × ExecutionInventory)}
    {t : ToolchainBoundary} (ht : t ∈ toolchainBase environments) :
    toolchainEntry (toolchainObservations environments) t.key = some t := by
  obtain ⟨key, -, hentry⟩ := Array.mem_filterMap.mp (toolchainBase_eq environments ▸ ht)
  exact (toolchainEntry_sound hentry).1 ▸ hentry

/-- The entry of an observation's key that is not folded is in the toolchain trusted base, and
lists the observation's environment and root. -/
theorem toolchainBase_complete {environments : Array (String × ExecutionInventory)}
    {x : ToolchainObservation} (hx : x ∈ toolchainObservations environments)
    (unfolded : toolchainFolded (toolchainObservations environments)
      x.boundary.toolchainKey = false) :
    ∃ t ∈ toolchainBase environments, t.key = x.boundary.toolchainKey ∧ x.reach ∈ t.reachedBy := by
  obtain ⟨t, ht, hreach⟩ := toolchainEntry_complete hx unfolded
  exact ⟨t, toolchainBase_eq environments ▸ Array.mem_filterMap.mpr ⟨x.boundary.toolchainKey,
    (mem_canonicalToolchainKeys _ _).mpr (Array.mem_map.mpr ⟨_, hx, rfl⟩), ht⟩,
    (toolchainEntry_sound ht).1, hreach⟩

/-- The observation of a toolchain-owned boundary of a root of the labeled accounts. -/
theorem observation_of_boundary {environments : Array (String × ExecutionInventory)}
    {e : String × ExecutionInventory} (he : e ∈ environments) {r : ExecutionRoot}
    (hr : r ∈ e.2.roots) {b : ExecutionBoundary} (hb : b ∈ r.boundaries)
    {o : ToolchainOrigin} (ho : b.toolchainOrigin? = some o) :
    ({ reach := (e.1, r.name), boundary := b, origin := o
       carriers := (r.boundaries.filter (r.carries · b)).map (·.toolchainKey) } :
        ToolchainObservation) ∈ toolchainObservations environments :=
  mem_toolchainObservations.mpr ⟨e, he, r, hr, rfl, hb, ho, rfl⟩

/-- Required meaning of the toolchain trusted-base report over the labeled execution accounts
of one audit. No two entries share a constant and kind. Each toolchain-owned boundary of every
account is in the report for the environment and root that reach it, in exactly one of two ways:
as the boundary of the one entry under its constant and kind, which lists that environment and
root; or, when no entry has its constant and kind, as an implementation named by the entry of a
boundary of the same root that carries it (`ExecutionRoot.carries`), which lists that
environment and root. Its constant and kind have no entry exactly when every root of the audit
that reaches it holds a boundary that carries it. Every entry is such a boundary with that
boundary's module, replacement and origin, every environment and root it lists reaches it, and
every implementation it names is a toolchain-owned boundary without an entry that a boundary
under the entry's key carries in some root. -/
def ToolchainBaseContract
    (base : Array (String × ExecutionInventory) → Array ToolchainBoundary) : Prop :=
  ∀ environments,
    ((base environments).map (·.key)).toList.Nodup ∧
    (∀ e ∈ environments, ∀ r ∈ e.2.roots, ∀ b ∈ r.boundaries, b.toolchainOrigin?.isSome →
      (∃ t ∈ base environments, t.key = b.toolchainKey ∧ (e.1, r.name) ∈ t.reachedBy ∧
        ∀ t' ∈ base environments, t'.key = b.toolchainKey → t' = t) ∨
      ((∀ t ∈ base environments, t.key ≠ b.toolchainKey) ∧
        ∃ t ∈ base environments, (e.1, r.name) ∈ t.reachedBy ∧ b.name ∈ t.implementations ∧
          ∃ a ∈ r.boundaries, a.toolchainKey = t.key ∧ r.carries a b = true)) ∧
    (∀ e ∈ environments, ∀ r ∈ e.2.roots, ∀ b ∈ r.boundaries, b.toolchainOrigin?.isSome →
      ((∃ t ∈ base environments, t.key = b.toolchainKey) ↔
        ∃ e' ∈ environments, ∃ r' ∈ e'.2.roots, ∃ b' ∈ r'.boundaries,
          b'.toolchainOrigin?.isSome ∧ b'.toolchainKey = b.toolchainKey ∧
            ∀ a ∈ r'.boundaries, r'.carries a b' = false)) ∧
    (∀ t ∈ base environments, ∃ e ∈ environments, ∃ r ∈ e.2.roots, ∃ b ∈ r.boundaries,
      b.toolchainKey = t.key ∧ b.module = t.module ∧ b.replacement = t.replacement ∧
        b.toolchainOrigin? = some t.origin) ∧
    (∀ t ∈ base environments, ∀ reach ∈ t.reachedBy, ∃ e ∈ environments, e.1 = reach.1 ∧
      ∃ r ∈ e.2.roots, r.name = reach.2 ∧
        ∃ b ∈ r.boundaries, b.toolchainKey = t.key ∧ b.toolchainOrigin?.isSome) ∧
    (∀ t ∈ base environments, ∀ n ∈ t.implementations, ∃ e ∈ environments, ∃ r ∈ e.2.roots,
      ∃ a ∈ r.boundaries, ∃ b ∈ r.boundaries, a.toolchainKey = t.key ∧ b.name = n ∧
        b.toolchainOrigin?.isSome ∧ r.carries a b = true ∧
          ∀ t' ∈ base environments, t'.key ≠ b.toolchainKey)

/-- No entry of the toolchain trusted base has a folded key. -/
private theorem toolchainBase_unfolded {environments : Array (String × ExecutionInventory)}
    {t : ToolchainBoundary} (ht : t ∈ toolchainBase environments) :
    toolchainFolded (toolchainObservations environments) t.key = false :=
  (toolchainEntry_sound (toolchainBase_entry ht)).2.1

/-- The gate reports the toolchain trusted base through this registration, whose `run` is
exactly `toolchainBase`. It does not establish that the toolchain's code is correct, or that
the collector recorded which constant Lean compiles through which helper truthfully. -/
theorem checked_toolchainBase : Regula.ExecutableContract toolchainBase ToolchainBaseContract := by
  refine ⟨fun environments => ⟨toolchainBase_keys_nodup environments, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro e he r hr b hb ho
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp ho
    have hx := observation_of_boundary he hr hb ho
    cases hfolded : toolchainFolded (toolchainObservations environments) b.toolchainKey
    · obtain ⟨t, hmem, hkey, hreach⟩ := toolchainBase_complete hx hfolded
      refine Or.inl ⟨t, hmem, hkey, hreach, fun t' ht' hkey' => ?_⟩
      have nodup := toolchainBase_keys_nodup environments
      rw [Array.toList_map] at nodup
      exact eq_of_nodup_map nodup (Array.mem_toList_iff.mpr ht') (Array.mem_toList_iff.mpr hmem)
        (hkey'.trans hkey.symm)
    · refine Or.inr ⟨fun t ht same => ?_, ?_⟩
      · have := toolchainBase_unfolded ht
        rw [same, hfolded] at this
        cases this
      -- The observation is carried: its key is folded, so it has a carrier `a`.
      have carried : ((r.boundaries.filter (r.carries · b)).map (·.toolchainKey)).isEmpty =
          false := by
        cases empty : ((r.boundaries.filter (r.carries · b)).map (·.toolchainKey)).isEmpty
        · rfl
        · have := toolchainFolded_eq_false.mpr ⟨_, hx, rfl, empty⟩
          rw [hfolded] at this
          cases this
      obtain ⟨k, hk⟩ := Array.isEmpty_eq_false_iff_exists_mem.mp carried
      obtain ⟨a, ha, rfl⟩ := Array.mem_map.mp hk
      obtain ⟨ha, carries⟩ := Array.mem_filter.mp ha
      obtain ⟨-, unfoldable, -, owner, -⟩ := ExecutionRoot.carries_spec carries
      -- The carrier has the same origin, and nothing carries it, since it is not foldable.
      have hxa := observation_of_boundary he hr ha (owner.trans ho)
      have uncarried : ∀ a' ∈ r.boundaries, r.carries a' a = false := fun a' _ => by
        cases h : r.carries a' a
        · rfl
        · rw [(ExecutionRoot.carries_spec h).1] at unfoldable
          cases unfoldable
      have aUnfolded := toolchainFolded_eq_false.mpr ⟨_, hxa, rfl,
        (carriers_isEmpty (r := r) rfl).mpr uncarried⟩
      obtain ⟨t, hmem, hkey, hreach⟩ := toolchainBase_complete hxa aUnfolded
      refine ⟨t, hmem, hreach, ?_, a, ha, hkey.symm, carries⟩
      rw [(toolchainEntry_sound (toolchainBase_entry hmem)).2.2.2.2, hkey]
      exact mem_toolchainImplementations.mpr ⟨_, hx, hfolded, hk, rfl⟩
  · intro e he r hr b hb ho
    constructor
    · rintro ⟨t, ht, hkey⟩
      obtain ⟨y, hy, hykey, empty⟩ := toolchainFolded_eq_false.mp (toolchainBase_unfolded ht)
      obtain ⟨e', he', r', hr', -, hb', ho', hcarriers⟩ := mem_toolchainObservations.mp hy
      exact ⟨e', he', r', hr', y.boundary, hb', by simp [ho'], hykey.trans hkey,
        (carriers_isEmpty hcarriers).mp empty⟩
    · rintro ⟨e', he', r', hr', b', hb', ho', hkey, uncarried⟩
      obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.mp ho'
      have hy := observation_of_boundary he' hr' hb' ho'
      have unfolded := toolchainFolded_eq_false.mpr ⟨_, hy, rfl,
        (carriers_isEmpty (r := r') rfl).mpr uncarried⟩
      obtain ⟨t, ht, htkey, -⟩ := toolchainBase_complete hy unfolded
      exact ⟨t, ht, htkey.trans hkey⟩
  · intro t ht
    obtain ⟨hkey, -, ⟨x, hx, hxkey, hmodule, hreplacement, horigin⟩, -⟩ :=
      toolchainEntry_sound (toolchainBase_entry ht)
    obtain ⟨e, he, r, hr, -, hb, ho, -⟩ := mem_toolchainObservations.mp hx
    exact ⟨e, he, r, hr, x.boundary, hb, hxkey, hmodule.symm, hreplacement.symm, horigin ▸ ho⟩
  · intro t ht reach hreach
    obtain ⟨-, -, -, hreaches, -⟩ := toolchainEntry_sound (toolchainBase_entry ht)
    obtain ⟨y, hy, rfl, hykey⟩ := hreaches reach hreach
    obtain ⟨e, he, r, hr, hname, hb, ho, -⟩ := mem_toolchainObservations.mp hy
    exact ⟨e, he, by rw [hname], r, hr, by rw [hname], y.boundary, hb, hykey, by simp [ho]⟩
  · intro t ht n hn
    obtain ⟨-, -, -, -, himpl⟩ := toolchainEntry_sound (toolchainBase_entry ht)
    rw [himpl] at hn
    obtain ⟨x, hx, folded, hk, rfl⟩ := mem_toolchainImplementations.mp hn
    obtain ⟨e, he, r, hr, -, hb, ho, hcarriers⟩ := mem_toolchainObservations.mp hx
    rw [hcarriers] at hk
    obtain ⟨a, ha, hakey⟩ := Array.mem_map.mp hk
    obtain ⟨ha, carries⟩ := Array.mem_filter.mp ha
    refine ⟨e, he, r, hr, a, ha, x.boundary, hb, hakey, rfl, by simp [ho], carries,
      fun t' ht' same => ?_⟩
    have := toolchainBase_unfolded ht'
    rw [same, folded] at this
    cases this

end RegulaPolicy
