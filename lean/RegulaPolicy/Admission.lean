module

public import RegulaPolicy.Domain
public import Std.Data.ExtHashSet.Lemmas

/-! Admission of observations before policy. These proofs establish data validity,
not the truth of compiler extraction. Generated roles remain bound to this entire
inventory; all policy decisions consume a member of that same admitted inventory. -/

@[expose] public section

namespace RegulaPolicy

/-- Hash-set cardinality detects precisely pairwise distinct inputs. Hash collisions
are resolved by lawful equality; this does not equate hashes with identities. -/
theorem distinct_iff {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (xs : List α) : (Std.ExtHashSet.ofList xs).size = xs.length ↔ xs.Pairwise (· ≠ ·) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have cons : Std.ExtHashSet.ofList (x :: xs) = (Std.ExtHashSet.ofList xs).insert x := by
      ext a
      simp only [Std.ExtHashSet.mem_ofList, List.contains_eq_mem, List.mem_cons,
        List.decide_mem_cons, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
        Std.ExtHashSet.mem_insert]
      exact or_congr eq_comm Iff.rfl
    rw [cons, Std.ExtHashSet.size_insert]
    by_cases h : x ∈ xs
    · have bound := Std.ExtHashSet.size_ofList_le (l := xs)
      have no : ¬ (Std.ExtHashSet.ofList xs).size = xs.length + 1 := by
        omega
      simp [Std.ExtHashSet.mem_ofList, h, no, List.pairwise_cons, List.forall_mem_ne]
    · simp [Std.ExtHashSet.mem_ofList, h, List.pairwise_cons, ih, List.forall_mem_ne]

/-- Decide the original distinctness proposition without comparing every pair. -/
def distinctDecidable {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (xs : List α) : Decidable (xs.Pairwise (· ≠ ·)) :=
  decidable_of_iff ((Std.ExtHashSet.ofList xs).size = xs.length) (distinct_iff xs)

/-- Structural key validity. Anonymous prefixes are legal; complete keys are not. -/
def named (n : Lean.Name) : Prop := n ≠ .anonymous
instance (n : Lean.Name) : Decidable (named n) := inferInstanceAs (Decidable (n ≠ .anonymous))

/-- Repeated observations are refused even when their payloads agree. -/
def uniqueNames (names : Array Lean.Name) : Prop := names.toList.Pairwise (· ≠ ·)
instance (names : Array Lean.Name) : Decidable (uniqueNames names) :=
  distinctDecidable names.toList

/-- Every policy-relevant declaration reference is structural and nonanonymous.
A failed executable-contract observation may lack a root; it remains a refusal. -/
def Declaration.Valid (d : Declaration) : Prop :=
  named d.name ∧ named d.module ∧
  d.safety = (if d.isPartial then some .partial else if d.isUnsafe then some .unsafe else none) ∧
  canonicalNames d.axioms = d.axioms ∧ canonicalNames d.valueConstants = d.valueConstants ∧
  (∀ ns ∈ d.unsafeRecEquationAxioms, canonicalNames ns = ns ∧ ∀ n ∈ ns, named n) ∧
  (∀ n ∈ d.axioms, named n) ∧ (∀ n ∈ d.valueConstants, named n) ∧
  (∀ n ∈ d.all, named n) ∧ (∀ n ∈ d.nativeUseParents, named n) ∧
  (∀ n ∈ d.implementedBy, named n) ∧ (∀ n ∈ d.unsafeRecBase, named n) ∧
  (∀ c ∈ d.executableContract, c.failure.isSome = true ∨ named c.root)
instance instDecidableDeclarationValid (d : Declaration) : Decidable d.Valid := by
  unfold Declaration.Valid
  infer_instance

/-- Codepoint coordinates select an existing line and a boundary on that line.
The operational bridge separately checks correspondence with Lean's FileMap. -/
def Position.validForLines (p : Position) (lines : List String) : Bool :=
  p.line > 0 && (lines[p.line - 1]?).any (fun line => p.column ≤ line.length)

def Position.validFor (p : Position) (source : String) : Bool :=
  p.validForLines (source.splitOn "\n")

def positionLE (a b : Position) : Bool :=
  a.line < b.line || (a.line == b.line && a.column ≤ b.column)

def utf16ColumnLines (p : Position) (lines : List String) : Nat :=
  (((lines[p.line - 1]?).getD "").toList.take p.column).foldl
    (fun n c => n + if c.toNat > 65535 then 2 else 1) 0

def utf16Column (p : Position) (source : String) : Nat :=
  utf16ColumnLines p (source.splitOn "\n")

def Range.validForLines (r : Range) (lines : List String) : Bool :=
  r.start.validForLines lines && r.end.validForLines lines && positionLE r.start r.end &&
  r.startUtf16 == utf16ColumnLines r.start lines && r.endUtf16 == utf16ColumnLines r.end lines

def Range.validFor (r : Range) (source : String) : Bool :=
  r.validForLines (source.splitOn "\n")

def Ranges.validForLines (r : Ranges) (lines : List String) : Bool :=
  r.range.validForLines lines && r.selectionRange.validForLines lines &&
  positionLE r.range.start r.selectionRange.start && positionLE r.selectionRange.end r.range.end

def Ranges.validFor (r : Ranges) (source : String) : Bool :=
  r.validForLines (source.splitOn "\n")

/-- The source-derived line list preserves codepoint/UTF16 bounds and containment. -/
theorem Ranges.validForLines_eq (r : Ranges) (source : String) :
    r.validForLines (source.splitOn "\n") =
      (r.range.validFor source && r.selectionRange.validFor source &&
        positionLE r.range.start r.selectionRange.start &&
        positionLE r.selectionRange.end r.range.end) := rfl

def Frontend.SyntaxRange.validForLines (r : Frontend.SyntaxRange) (lines : List String) : Bool :=
  r.start.validForLines lines && r.end.validForLines lines && positionLE r.start r.end

def Frontend.SyntaxRange.validFor (r : Frontend.SyntaxRange) (source : String) : Bool :=
  r.validForLines (source.splitOn "\n")

/-- Split this immutable source once, shared by every command, evaluator and binding.
The line list is derived here; a caller cannot supply an unrelated coordinate index. -/
def Frontend.Transcript.validCoordinates (t : Frontend.Transcript) : Bool :=
  let lines := t.sourceContent.splitOn "\n"
  t.commands.all fun command =>
    command.commandRange.all (·.validForLines lines) &&
    command.evaluators.all (fun e => e.range.all (·.validForLines lines)) &&
    command.bindings.all (fun b => b.range.all (·.validForLines lines)) &&
    command.added == command.addedDeclarations.map (·.name) &&
    command.added.all (· != .anonymous)

/-- Sharing the source split preserves the original per-range check for every transcript,
including missing ranges, invalid positions, reversed spans and declaration identities. -/
theorem Frontend.Transcript.validCoordinates_eq (t : Frontend.Transcript) :
    t.validCoordinates = (t.commands.all fun command =>
      command.commandRange.all (·.validFor t.sourceContent) &&
      command.evaluators.all (fun e => e.range.all (·.validFor t.sourceContent)) &&
      command.bindings.all (fun b => b.range.all (·.validFor t.sourceContent)) &&
      command.added == command.addedDeclarations.map (·.name) &&
      command.added.all (· != .anonymous)) := rfl

/-- Admitted inventories have one declaration per name and one transcript per module.
Ordered evaluator and mutual-group sequences are intentionally not normalized. -/
def InventoryValid (decls : Array Declaration) (transcripts : Array Frontend.Transcript) : Prop :=
  uniqueNames (decls.map (·.name)) ∧
  (∀ d ∈ decls, d.Valid) ∧
  uniqueNames (transcripts.map (·.module)) ∧
  (∀ t ∈ transcripts, named t.module ∧ t.source ≠ "" ∧
    t.sourceBytes = t.sourceContent.utf8ByteSize ∧
    t.leanVersion = "4.34.0" ∧ t.leanGitHash = "293d5d0c0c3f3dded4688b3ccd6a33939ac5102b" ∧
    t.validCoordinates = true ∧
    ∀ d ∈ decls, d.module = t.module → d.ranges.all (·.validFor t.sourceContent) = true)
/-- Decide the unchanged declaration-coordinate relation using one supplied line list. -/
def declarationCoordinatesDecidable (decls : Array Declaration)
    (moduleName : Lean.Name) (lines : List String) : Decidable
    (∀ d ∈ decls, d.module = moduleName → d.ranges.all (·.validForLines lines) = true) :=
  inferInstance

instance instDecidableInventoryValid (decls : Array Declaration) (transcripts : Array Frontend.Transcript) :
    Decidable (InventoryValid decls transcripts) := by
  unfold InventoryValid
  -- A let in the proposition is reduced during instance synthesis. Bind the
  -- derived lines in the executable decision so all declarations share them.
  letI (t : Frontend.Transcript) : Decidable
      (∀ d ∈ decls, d.module = t.module → d.ranges.all (·.validFor t.sourceContent) = true) :=
    declarationCoordinatesDecidable decls t.module (t.sourceContent.splitOn "\n")
  infer_instance

/-- A shared declaration name prevents concatenated inventories from being valid,
regardless of module identities, other declaration fields or supplied transcripts.
This concerns the actual admission predicate; it does not establish that external
producers returned either inventory or that a collision occurred in a running audit. -/
theorem inventoryValid_append_false_of_shared_name
    (left right : Array Declaration) (transcripts : Array Frontend.Transcript)
    (a b : Declaration) (ha : a ∈ left) (hb : b ∈ right) (sameName : a.name = b.name) :
    ¬ InventoryValid (left ++ right) transcripts := by
  intro valid
  have distinct : (left.toList.map (·.name) ++ right.toList.map (·.name)).Pairwise (· ≠ ·) := by
    simpa only [uniqueNames, Array.map_append, Array.toList_append, Array.toList_map] using valid.1
  have leftMember : a.name ∈ left.toList.map (·.name) :=
    List.mem_map.mpr ⟨a, by simpa using ha, rfl⟩
  have rightMember : b.name ∈ right.toList.map (·.name) :=
    List.mem_map.mpr ⟨b, by simpa using hb, rfl⟩
  exact (List.pairwise_append.mp distinct).2.2 a.name leftMember b.name rightMember sameName

/-- No raw constructor or decoder can omit the inventory-validity proof. -/
structure Inventory where
  declarations : Array Declaration
  transcripts : Array Frontend.Transcript
  valid : InventoryValid declarations transcripts
  deriving DecidableEq

/-- Validate without dropping, substituting, or deduplicating result observations. -/
def admitInventory (decls : Array Declaration) (transcripts : Array Frontend.Transcript) :
    Except String Inventory :=
  if h : InventoryValid decls transcripts then .ok ⟨decls, transcripts, h⟩
  else .error "invalid policy inventory: anonymous, duplicate, or malformed identity"

/-- Every valid inventory is admitted with exactly its input fields. -/
theorem admitInventory_exact (ds : Array Declaration) (ts : Array Frontend.Transcript)
    (h : InventoryValid ds ts) : admitInventory ds ts = .ok ⟨ds, ts, h⟩ := by
  simp [admitInventory, h]
/-- Boundary origin receipts must refer to this observation's module. -/
def ExecutionBoundary.Valid (b : ExecutionBoundary) : Prop :=
  named b.name ∧ named b.module ∧
  (∀ n ∈ b.replacement, named n) ∧ (∀ n ∈ b.compilerCallers, named n) ∧
  (∀ o ∈ b.account.nativeOrigin?, o.moduleName = b.module)
instance instDecidableExecutionBoundaryValid (b : ExecutionBoundary) : Decidable b.Valid := by
  unfold ExecutionBoundary.Valid
  infer_instance

/-- The first visit is the root. Every later visit has an edge from an earlier visit.
An index bounds the witness check; no second graph search or assumed reachability is used. -/
def ExecutionClosure.DiscoveryOK (c : ExecutionClosure) (root : Lean.Name)
    (compilerEdges : Array (Lean.Name × Lean.Name)) : Prop :=
  ∀ k : Fin c.visits.size, match c.visits[k].parent with
    | none => k.val = 0 ∧ c.visits[k].name = root
    | some parent => if h : parent < k.val then
        (c.visits[parent]'(Nat.lt_trans h k.isLt) |>.name, c.visits[k].name) ∈ c.edges compilerEdges
      else False
instance (c : ExecutionClosure) (root : Lean.Name) (edges : Array (Lean.Name × Lean.Name)) :
    Decidable (c.DiscoveryOK root edges) := by
  unfold ExecutionClosure.DiscoveryOK
  let edgeSet := Std.ExtHashSet.ofList (c.edges edges).toList
  letI (edge : Lean.Name × Lean.Name) : Decidable (edge ∈ c.edges edges) :=
    decidable_of_iff (edge ∈ edgeSet) (by simp [edgeSet, Std.ExtHashSet.mem_ofList])
  exact @Nat.decidableForallFin _ _ (fun k => by split <;> infer_instance)

/-- The checked discovery witnesses support induction from the actual root along the
recorded traversal edges. This establishes reachability of every visit without a
second graph walk; edge extraction and its completeness remain observational. -/
theorem ExecutionClosure.discovery_induction (c : ExecutionClosure) (root : Lean.Name)
    (edges : Array (Lean.Name × Lean.Name)) (valid : c.DiscoveryOK root edges)
    (P : Lean.Name → Prop) (base : P root)
    (step : ∀ edge ∈ c.edges edges, P edge.1 → P edge.2)
    (k : Fin c.visits.size) : P c.visits[k].name := by
  have all : ∀ n, ∀ hn : n < c.visits.size, P c.visits[n].name := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      have witness := valid ⟨n, hn⟩
      change (match c.visits[n].parent with
        | none => n = 0 ∧ c.visits[n].name = root
        | some parent => if h : parent < n then
            (c.visits[parent]'(Nat.lt_trans h hn) |>.name, c.visits[n].name) ∈ c.edges edges
          else False) at witness
      cases hparent : c.visits[n].parent with
      | none =>
        simp only [hparent] at witness
        exact witness.2.symm ▸ base
      | some parent =>
        simp only [hparent] at witness
        split at witness
        next earlier => exact step _ witness (ih parent earlier (Nat.lt_trans earlier hn))
        next => contradiction
  exact all k.val k.isLt

/-- Reconcile the independently recorded reached census with every traversal channel.
This finite relation checks the supplied account; truthful and complete extraction still
depends on the actual Lean collector. Missing code cannot accompany a resolved root. -/
def ExecutionClosure.Valid (c : ExecutionClosure) (root : Lean.Name)
    (compilerEdges : Array (Lean.Name × Lean.Name)) (unresolved : Array String) : Prop :=
  canonicalNames c.nodes = c.nodes ∧ root ∈ c.nodes ∧ (∀ n ∈ c.nodes, named n) ∧
  c.nodes = canonicalNames (c.visits.map (·.name)) ∧ c.visits.size = c.nodes.size ∧
  c.DiscoveryOK root compilerEdges ∧
  (∀ visit ∈ c.visits, ∀ m ∈ visit.moduleName, named m) ∧
  (∀ edges ∈ #[c.logicalEdges, c.candidateEdges, c.historyEdges,
      c.currentReplacementEdges, c.activeSimplificationEdges, c.helperEdges],
    canonicalEdges edges = edges) ∧
  (∀ edge ∈ c.edges compilerEdges, edge.1 ∈ c.nodes ∧ edge.2 ∈ c.nodes) ∧
  (∀ edge ∈ c.activeSimplificationEdges, edge ∈ c.candidateEdges) ∧
  canonicalNames c.requiredCode = c.requiredCode ∧
  canonicalNames c.unavailableCode = c.unavailableCode ∧
  (∀ n ∈ c.requiredCode, n ∈ c.nodes) ∧
  (∀ edge ∈ compilerEdges, edge.2 ∈ c.requiredCode) ∧
  (∀ n ∈ c.unavailableCode, n ∈ c.requiredCode) ∧
  (c.unavailableCode ≠ #[] → unresolved ≠ #[])
instance (c : ExecutionClosure) (root : Lean.Name) (edges : Array (Lean.Name × Lean.Name))
    (unresolved : Array String) : Decidable (c.Valid root edges unresolved) := by
  unfold ExecutionClosure.Valid
  -- Index each repeatedly queried array once; membership equivalence supplies
  -- decisions for the unchanged predicate, without a second validity definition.
  let nodes := Std.ExtHashSet.ofList c.nodes.toList
  let candidates := Std.ExtHashSet.ofList c.candidateEdges.toList
  let required := Std.ExtHashSet.ofList c.requiredCode.toList
  letI (n : Lean.Name) : Decidable (n ∈ c.nodes) :=
    decidable_of_iff (n ∈ nodes) (by simp [nodes, Std.ExtHashSet.mem_ofList])
  letI (edge : Lean.Name × Lean.Name) : Decidable (edge ∈ c.candidateEdges) :=
    decidable_of_iff (edge ∈ candidates) (by simp [candidates, Std.ExtHashSet.mem_ofList])
  letI (n : Lean.Name) : Decidable (n ∈ c.requiredCode) :=
    decidable_of_iff (n ∈ required) (by simp [required, Std.ExtHashSet.mem_ofList])
  infer_instance

/-- Every admitted reached name follows from the root by the reported traversal
relation. The census is connected, not merely an endpoint-closed set of names. -/
theorem ExecutionClosure.nodes_induction (c : ExecutionClosure) (root : Lean.Name)
    (edges : Array (Lean.Name × Lean.Name)) (unresolved : Array String)
    (valid : c.Valid root edges unresolved) (P : Lean.Name → Prop) (base : P root)
    (step : ∀ edge ∈ c.edges edges, P edge.1 → P edge.2)
    (name : Lean.Name) (member : name ∈ c.nodes) : P name := by
  rw [valid.2.2.2.1, mem_canonicalNames] at member
  obtain ⟨visit, hv, rfl⟩ := Array.mem_map.mp member
  obtain ⟨index, hi, heq⟩ := Array.mem_iff_getElem.mp hv
  subst visit
  exact c.discovery_induction root edges valid.2.2.2.2.2.1 P base step ⟨index, hi⟩

/-- Occurrence numbers distinguish repeated evidence, while roots have unique keys.
Every boundary and retained caller must belong to the complete reached census. -/
def ExecutionRoot.Valid (r : ExecutionRoot) : Prop :=
  named r.name ∧ named r.module ∧
  canonicalEdges r.compilerEdges = r.compilerEdges ∧
  (∀ b ∈ r.boundaries, b.Valid) ∧
  (r.boundaries.map (·.occurrence)).toList.Pairwise (· ≠ ·) ∧
  (∀ e ∈ r.compilerEdges, named e.1 ∧ named e.2) ∧
  r.closure.Valid r.name r.compilerEdges r.unresolved ∧
  (∀ b ∈ r.boundaries, b.name ∈ r.closure.nodes ∧
    (∀ n ∈ b.replacement, n ∈ r.closure.nodes) ∧
    canonicalNames b.compilerCallers = canonicalNames (r.compilerEdges.filterMap
      (fun (caller, callee) => if callee == b.name then some caller else none)))
instance instDecidableExecutionRootValid (r : ExecutionRoot) : Decidable r.Valid := by
  unfold ExecutionRoot.Valid
  let nodes := Std.ExtHashSet.ofList r.closure.nodes.toList
  letI (n : Lean.Name) : Decidable (n ∈ r.closure.nodes) :=
    decidable_of_iff (n ∈ nodes) (by simp [nodes, Std.ExtHashSet.mem_ofList])
  infer_instance

def ExecutionValid (roots : Array ExecutionRoot) : Prop :=
  uniqueNames (roots.map (·.name)) ∧ ∀ r ∈ roots, r.Valid
instance instDecidableExecutionValid (roots : Array ExecutionRoot) : Decidable (ExecutionValid roots) := by
  unfold ExecutionValid
  infer_instance

structure ExecutionInventory where
  roots : Array ExecutionRoot
  valid : ExecutionValid roots
  deriving DecidableEq

def admitExecution (roots : Array ExecutionRoot) : Except String ExecutionInventory :=
  if h : ExecutionValid roots then .ok ⟨roots, h⟩
  else .error "invalid execution inventory: identity, occurrence, or origin binding"

theorem admitExecution_exact (roots : Array ExecutionRoot) (h : ExecutionValid roots) :
    admitExecution roots = .ok ⟨roots, h⟩ := by simp [admitExecution, h]

/-- Every successful admission retains all supplied roots and establishes their exact
structural relation, including closure coverage. It does not authenticate extraction. -/
theorem admitExecution_preserves (roots : Array ExecutionRoot) (i : ExecutionInventory)
    (h : admitExecution roots = .ok i) : i.roots = roots ∧ ExecutionValid roots := by
  unfold admitExecution at h
  split at h
  next valid => cases h; exact ⟨rfl, valid⟩
  next => cases h
end RegulaPolicy
