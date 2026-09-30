import RegulaPolicy.Admission
import Regula.Contract

/-! # Execution decisions

Executable execution decisions and their exact finite-observation specification, and the
toolchain trusted-base report that lists each toolchain-owned boundary once.
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


/-! ## The toolchain trusted base

A toolchain-owned boundary passes every claim, so it never becomes a failure record. The
account reports it instead once, with every root that reaches it, rather than once per root. -/

/-- A toolchain boundary's identity in the trusted-base report: its constant and kind. -/
abbrev ToolchainKey := Lean.Name × BoundaryKind

/-- The toolchain key of a boundary observation. -/
def ExecutionBoundary.toolchainKey (b : ExecutionBoundary) : ToolchainKey := (b.name, b.boundary)

/-- One toolchain-owned boundary of an execution account, reported once. -/
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
  /-- Every root whose closure reaches it, sorted and without duplicates. -/
  roots : Array Lean.Name
  deriving Repr, DecidableEq

/-- The report's key of an entry: its constant and kind. -/
def ToolchainBoundary.key (t : ToolchainBoundary) : ToolchainKey := (t.name, t.boundary)

/-- Every toolchain-owned boundary observation of the account, with its root's name and
admitted origin, in root order. -/
def ExecutionInventory.toolchainObservations (inventory : ExecutionInventory) :
    Array (Lean.Name × ExecutionBoundary × ToolchainOrigin) :=
  inventory.roots.flatMap fun root =>
    root.boundaries.filterMap fun b => b.toolchainOrigin?.map fun o => (root.name, b, o)

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

/-- The report entry of one key: the constant, module, kind, replacement and origin of the
key's first observation, with every root that reaches the key; `none` when nothing is
observed under the key. -/
def toolchainEntry (observations : Array (Lean.Name × ExecutionBoundary × ToolchainOrigin))
    (key : ToolchainKey) : Option ToolchainBoundary :=
  let reaching := observations.filter (·.2.1.toolchainKey == key)
  reaching[0]?.map fun (_, b, origin) =>
    { name := b.name, «module» := b.module, boundary := b.boundary
      replacement := b.replacement, origin, roots := canonicalNames (reaching.map (·.1)) }

/-- The toolchain trusted base of an execution account: each toolchain-owned boundary once, in
key order, with every root that reaches it (`checked_toolchainBase`). -/
def toolchainBase (inventory : ExecutionInventory) : Array ToolchainBoundary :=
  let observations := inventory.toolchainObservations
  (canonicalToolchainKeys (observations.map (·.2.1.toolchainKey))).filterMap
    (toolchainEntry observations)

theorem mem_toolchainObservations {inventory : ExecutionInventory}
    {x : Lean.Name × ExecutionBoundary × ToolchainOrigin} :
    x ∈ inventory.toolchainObservations ↔
      ∃ r ∈ inventory.roots, x.1 = r.name ∧ x.2.1 ∈ r.boundaries ∧
        x.2.1.toolchainOrigin? = some x.2.2 := by
  rcases x with ⟨n, b, o⟩
  simp only [ExecutionInventory.toolchainObservations, Array.mem_flatMap, Array.mem_filterMap,
    Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨r, hr, b', hb', o', ho', rfl, rfl, rfl⟩
    exact ⟨r, hr, rfl, hb', ho'⟩
  · rintro ⟨r, hr, rfl, hb, ho⟩
    exact ⟨r, hr, b, hb, o, ho, rfl, rfl, rfl⟩

/-- What an entry reports: its key, the fields of an observation under that key, and roots that
each reach the key. -/
theorem toolchainEntry_sound {observations : Array (Lean.Name × ExecutionBoundary ×
    ToolchainOrigin)} {key : ToolchainKey} {t : ToolchainBoundary}
    (h : toolchainEntry observations key = some t) :
    t.key = key ∧
      (∃ x ∈ observations, x.2.1.toolchainKey = key ∧ t.module = x.2.1.module ∧
        t.replacement = x.2.1.replacement ∧ t.origin = x.2.2) ∧
      ∀ n ∈ t.roots, ∃ y ∈ observations, y.1 = n ∧ y.2.1.toolchainKey = key := by
  unfold toolchainEntry at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨n, b, o⟩, hfirst, rfl⟩ := h
  have hmem := Array.mem_filter.mp (Array.mem_of_getElem? hfirst)
  have hkey : b.toolchainKey = key := beq_iff_eq.mp hmem.2
  refine ⟨hkey, ⟨(n, b, o), hmem.1, hkey, rfl, rfl, rfl⟩, ?_⟩
  intro m hm
  obtain ⟨y, hy, rfl⟩ := Array.mem_map.mp ((mem_canonicalNames _ _).mp hm)
  have hy := Array.mem_filter.mp hy
  exact ⟨y, hy.1, rfl, beq_iff_eq.mp hy.2⟩

/-- Every observation under a key yields that key's entry, which lists the observation's root. -/
theorem toolchainEntry_complete {observations : Array (Lean.Name × ExecutionBoundary ×
    ToolchainOrigin)} {x : Lean.Name × ExecutionBoundary × ToolchainOrigin}
    (hx : x ∈ observations) :
    ∃ t, toolchainEntry observations x.2.1.toolchainKey = some t ∧ x.1 ∈ t.roots := by
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
  exact (mem_canonicalNames _ _).mpr (Array.mem_map.mpr ⟨x, hreach, rfl⟩)

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

/-- Required meaning of the toolchain trusted-base report: each toolchain-owned boundary of the
account appears exactly once, under its constant and kind, with every root that reaches it;
every entry is such a boundary with that boundary's module, replacement and origin, and every
root it lists reaches it. -/
def ToolchainBaseContract (base : ExecutionInventory → Array ToolchainBoundary) : Prop :=
  ∀ inventory,
    ((base inventory).map (·.key)).toList.Nodup ∧
    (∀ r ∈ inventory.roots, ∀ b ∈ r.boundaries, b.toolchainOrigin?.isSome →
      ∃ t ∈ base inventory, t.key = b.toolchainKey ∧ r.name ∈ t.roots) ∧
    (∀ t ∈ base inventory, ∃ r ∈ inventory.roots, ∃ b ∈ r.boundaries,
      b.toolchainKey = t.key ∧ b.module = t.module ∧ b.replacement = t.replacement ∧
        b.toolchainOrigin? = some t.origin) ∧
    (∀ t ∈ base inventory, ∀ n ∈ t.roots, ∃ r ∈ inventory.roots, r.name = n ∧
      ∃ b ∈ r.boundaries, b.toolchainKey = t.key ∧ b.toolchainOrigin?.isSome)

/-- The gate reports the toolchain trusted base through this registration, whose `run` is
exactly `toolchainBase`. It does not establish that the toolchain's code is correct. -/
theorem checked_toolchainBase : Regula.ExecutableContract toolchainBase ToolchainBaseContract := by
  refine ⟨fun inventory => ⟨?_, ?_, ?_, ?_⟩⟩
  · simp only [toolchainBase, Array.toList_map, Array.toList_filterMap]
    exact nodup_map_filterMap (canonicalToolchainKeys_nodup _)
      (fun _ _ h => (toolchainEntry_sound h).1)
  · intro r hr b hb ho
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp ho
    have hx : (r.name, b, o) ∈ inventory.toolchainObservations :=
      mem_toolchainObservations.mpr ⟨r, hr, rfl, hb, ho⟩
    obtain ⟨t, ht, hroot⟩ := toolchainEntry_complete hx
    refine ⟨t, ?_, (toolchainEntry_sound ht).1, hroot⟩
    refine Array.mem_filterMap.mpr ⟨b.toolchainKey, ?_, ht⟩
    exact (mem_canonicalToolchainKeys _ _).mpr (Array.mem_map.mpr ⟨_, hx, rfl⟩)
  · intro t ht
    obtain ⟨key, -, hentry⟩ := Array.mem_filterMap.mp ht
    obtain ⟨hkey, ⟨x, hx, hxkey, hmodule, hreplacement, horigin⟩, -⟩ := toolchainEntry_sound hentry
    obtain ⟨r, hr, -, hb, ho⟩ := mem_toolchainObservations.mp hx
    exact ⟨r, hr, x.2.1, hb, hxkey.trans hkey.symm, hmodule.symm, hreplacement.symm,
      horigin ▸ ho⟩
  · intro t ht n hn
    obtain ⟨key, -, hentry⟩ := Array.mem_filterMap.mp ht
    obtain ⟨hkey, -, hroots⟩ := toolchainEntry_sound hentry
    obtain ⟨y, hy, rfl, hykey⟩ := hroots n hn
    obtain ⟨r, hr, hname, hb, ho⟩ := mem_toolchainObservations.mp hy
    exact ⟨r, hr, hname.symm, y.2.1, hb, hykey.trans hkey.symm, by simp [ho]⟩

end RegulaPolicy
