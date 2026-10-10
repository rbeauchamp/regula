module

public import RegulaPolicy.Domain
public import RegulaPolicy.Compiler
public import Std.Data.ExtHashSet.Lemmas
meta import Regula.Decision

/-! # Observation admission

Admission of observations before policy. These proofs establish data validity,
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
def Named (n : Lean.Name) : Prop := n ≠ .anonymous
instance (n : Lean.Name) : Decidable (Named n) := inferInstanceAs (Decidable (n ≠ .anonymous))

/-- Repeated observations are refused even when their payloads agree. -/
def UniqueNames (names : Array Lean.Name) : Prop := names.toList.Pairwise (· ≠ ·)
instance (names : Array Lean.Name) : Decidable (UniqueNames names) :=
  distinctDecidable names.toList

/-- Every policy-relevant declaration reference is structural and nonanonymous.
A failed executable-contract observation may lack a root; it remains a refusal. Each axiom the
record says Lean's `collectAxioms` omits is one of its axioms. -/
def Declaration.Valid (d : Declaration) : Prop :=
  Named d.name ∧ Named d.module ∧
  d.safety = (if d.isPartial then some .partial else if d.isUnsafe then some .unsafe else none) ∧
  canonicalNames d.axioms = d.axioms ∧ canonicalNames d.valueConstants = d.valueConstants ∧
  (∀ n ∈ d.axioms, Named n) ∧ (∀ n ∈ d.valueConstants, Named n) ∧
  (∀ n ∈ d.all, Named n) ∧
  (∀ n ∈ d.implementedBy, Named n) ∧ (∀ n ∈ d.unsafeRecBase, Named n) ∧
  (∀ c ∈ d.executableContract, c.failure.isSome = true ∨ Named c.root) ∧
  (∀ a ∈ d.tableOmissions, a ∈ d.axioms)
instance instDecidableDeclarationValid (d : Declaration) : Decidable d.Valid := by
  unfold Declaration.Valid
  infer_instance

/-- Codepoint coordinates select an existing line and a boundary on that line.
The operational bridge separately checks correspondence with Lean's FileMap. -/
def Position.validForLines (p : Position) (lines : List String) : Bool :=
  p.line > 0 && (lines[p.line - 1]?).any (fun line => p.column ≤ line.length)

/-- `Position.validForLines` over the lines of `source`, split at each `\n`. -/
def Position.validFor (p : Position) (source : String) : Bool :=
  p.validForLines (source.splitOn "\n")

/-- The UTF-16 column of `p`: the UTF-16 code units of the first `p.column` characters of
line `p.line` (a character above U+FFFF counts two). A missing line counts as empty. -/
def utf16ColumnLines (p : Position) (lines : List String) : Nat :=
  (((lines[p.line - 1]?).getD "").toList.take p.column).foldl
    (fun n c => n + if c.toNat > 65535 then 2 else 1) 0

/-- `utf16ColumnLines` over the lines of `source`, split at each `\n`. -/
def utf16Column (p : Position) (source : String) : Nat :=
  utf16ColumnLines p (source.splitOn "\n")

/-- Both ends select boundaries on existing lines, the start is not after the end, and the
recorded UTF-16 columns equal those `utf16ColumnLines` computes for the two ends. -/
def Range.validForLines (r : Range) (lines : List String) : Bool :=
  r.start.validForLines lines && r.end.validForLines lines && positionLE r.start r.end &&
  r.startUtf16 == utf16ColumnLines r.start lines && r.endUtf16 == utf16ColumnLines r.end lines

/-- `Range.validForLines` over the lines of `source`, split at each `\n`. -/
def Range.validFor (r : Range) (source : String) : Bool :=
  r.validForLines (source.splitOn "\n")

/-- Both ranges are valid for the lines and the selection range lies within the full range. -/
def Ranges.validForLines (r : Ranges) (lines : List String) : Bool :=
  r.range.validForLines lines && r.selectionRange.validForLines lines &&
  positionLE r.range.start r.selectionRange.start && positionLE r.selectionRange.end r.range.end

/-- `Ranges.validForLines` over the lines of `source`, split at each `\n`. -/
def Ranges.validFor (r : Ranges) (source : String) : Bool :=
  r.validForLines (source.splitOn "\n")

/-- The source-derived line list preserves codepoint/UTF16 bounds and containment. -/
theorem Ranges.validForLines_eq (r : Ranges) (source : String) :
    r.validForLines (source.splitOn "\n") =
      (r.range.validFor source && r.selectionRange.validFor source &&
        positionLE r.range.start r.selectionRange.start &&
        positionLE r.selectionRange.end r.range.end) := rfl

/-- Valid ranges have a valid full range and a valid selection range. -/
theorem Ranges.validForLines_parts {r : Ranges} {lines : List String}
    (valid : r.validForLines lines = true) :
    r.range.validForLines lines = true ∧ r.selectionRange.validForLines lines = true := by
  simp only [Ranges.validForLines, Bool.and_eq_true] at valid
  exact valid.1.1

theorem positionLE_refl (a : Position) : positionLE a a = true := by simp [positionLE]

/-- A recorded pair whose selection range lies within its full range is admitted as it is. -/
theorem Ranges.admitted_eq_self {r : Ranges} (nested : r.Nested) : r.admitted = r := by
  simp [Ranges.admitted, nested]

/-- The admitted pair keeps the recorded full range: nothing is enlarged. -/
theorem Ranges.admitted_range (r : Ranges) : r.admitted.range = r.range := by
  unfold Ranges.admitted
  split <;> rfl

/-- The admitted pair's selection range lies within its full range, whatever was recorded. -/
theorem Ranges.admitted_nested (r : Ranges) : r.admitted.Nested := by
  unfold Ranges.admitted
  split
  · assumption
  · exact ⟨.refl _, .refl _⟩

/-- What the admitted pair's validity requires of the recorded pair: all of
`Ranges.validForLines` when the recorded selection range lies within the recorded full range,
and otherwise the validity of the recorded full range. -/
theorem Ranges.admitted_validForLines (r : Ranges) (lines : List String) :
    r.admitted.validForLines lines =
      if r.Nested then r.validForLines lines else r.range.validForLines lines := by
  unfold Ranges.admitted
  split
  · rfl
  · simp [Ranges.validForLines, positionLE_refl]

/-- The requirement on a recorded pair before the admitted pair existed, `Ranges.validForLines`
of the recorded pair, is the present requirement (the admitted pair is valid and the recorded
selection range is valid) together with the recorded selection range lying within the recorded
full range. That last condition relates the two recorded ranges alone and does not read the
source. -/
theorem Ranges.validForLines_iff_admitted (r : Ranges) (lines : List String) :
    r.validForLines lines = true ↔
      (r.admitted.validForLines lines = true ∧ r.selectionRange.validForLines lines = true) ∧
        r.Nested := by
  rw [Ranges.admitted_validForLines]
  by_cases nested : r.Nested
  · simp only [nested, ↓reduceIte, and_true]
    exact ⟨fun valid => ⟨valid, (Ranges.validForLines_parts valid).2⟩, And.left⟩
  · simp only [nested, and_false, iff_false]
    intro valid
    simp only [Ranges.validForLines, Bool.and_eq_true, positionLE_iff] at valid
    exact nested ⟨valid.1.2, valid.2⟩

/-- Codepoint coordinates select an existing line and a boundary on that line, as equations over
the list of lines: `lines` is the lines `before`, the line `line` and the lines `after`, `line`
has the number `p.line` where the first line has the number 1, and the column is at most the
number of characters of `line`. The statement has no index expression and no test of
`Position.validForLines`, which decides it (`Position.validForLines_iff`). -/
def Position.ValidForLines (p : Position) (lines : List String) : Prop :=
  ∃ before line after, lines = before ++ line :: after ∧ p.line = before.length + 1 ∧
    p.column ≤ line.length

/-- The executed check accepts exactly the positions that are valid for the lines. -/
theorem Position.validForLines_iff (p : Position) (lines : List String) :
    p.validForLines lines = true ↔ p.ValidForLines lines := by
  unfold Position.validForLines Position.ValidForLines
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.any_eq_true]
  constructor
  · rintro ⟨positive, line, found, fits⟩
    obtain ⟨inside, rfl⟩ := List.getElem?_eq_some_iff.mp found
    refine ⟨lines.take (p.line - 1), _, lines.drop (p.line - 1 + 1), ?_, ?_, fits⟩
    · rw [List.getElem_cons_drop, List.take_append_drop]
    · rw [List.length_take]
      omega
  · rintro ⟨before, line, after, rfl, numbered, fits⟩
    exact ⟨by omega, line, by simp [numbered], fits⟩

/-- Both ends select boundaries on existing lines, the start is not after the end, and the
recorded UTF-16 columns are those of the two ends (`utf16ColumnLines`), as a proposition.
`Range.validForLines` decides it (`Range.validForLines_iff`). -/
def Range.ValidForLines (r : Range) (lines : List String) : Prop :=
  r.start.ValidForLines lines ∧ r.end.ValidForLines lines ∧ PositionLE r.start r.end ∧
    r.startUtf16 = utf16ColumnLines r.start lines ∧ r.endUtf16 = utf16ColumnLines r.end lines

/-- The executed check accepts exactly the ranges that are valid for the lines. -/
theorem Range.validForLines_iff (r : Range) (lines : List String) :
    r.validForLines lines = true ↔ r.ValidForLines lines := by
  simp [Range.validForLines, Range.ValidForLines, Position.validForLines_iff, positionLE_iff,
    and_assoc]

/-- `Range.ValidForLines` over the lines of `source`, split at each `\n`. -/
def Range.ValidFor (r : Range) (source : String) : Prop :=
  r.ValidForLines (source.splitOn "\n")

/-- The executed check accepts exactly the ranges that are valid for the source. -/
theorem Range.validFor_iff (r : Range) (source : String) :
    r.validFor source = true ↔ r.ValidFor source :=
  r.validForLines_iff _

/-- Both ranges are valid for the lines and the selection range lies within the full range, as
a proposition. `Ranges.validForLines` decides it (`Ranges.validForLines_iff`). -/
def Ranges.ValidForLines (r : Ranges) (lines : List String) : Prop :=
  r.range.ValidForLines lines ∧ r.selectionRange.ValidForLines lines ∧
    PositionLE r.range.start r.selectionRange.start ∧ PositionLE r.selectionRange.end r.range.end

/-- The executed check accepts exactly the pairs that are valid for the lines. -/
theorem Ranges.validForLines_iff (r : Ranges) (lines : List String) :
    r.validForLines lines = true ↔ r.ValidForLines lines := by
  simp [Ranges.validForLines, Ranges.ValidForLines, Range.validForLines_iff, positionLE_iff,
    and_assoc]

/-- `Ranges.ValidForLines` over the lines of `source`, split at each `\n`. -/
def Ranges.ValidFor (r : Ranges) (source : String) : Prop :=
  r.ValidForLines (source.splitOn "\n")

/-- The executed check accepts exactly the pairs that are valid for the source. -/
theorem Ranges.validFor_iff (r : Ranges) (source : String) :
    r.validFor source = true ↔ r.ValidFor source :=
  r.validForLines_iff _

/-- Every command's `added` names are exactly its `addedDeclarations` names, none anonymous. It
takes the observed part of a transcript, so it reads no source text and no runtime replacement. -/
def Frontend.Transcript.ToolchainObserved.validCoordinates
    (t : Frontend.Transcript.ToolchainObserved) : Bool :=
  t.commands.all fun command =>
    command.added == command.addedDeclarations.map (·.name) &&
    command.added.all (· != .anonymous)

/-- Every command's `added` names are exactly its `addedDeclarations` names, none anonymous, as a
proposition, over the observed part of a transcript. `validCoordinates` decides it
(`validCoordinates_iff`). -/
def Frontend.Transcript.ToolchainObserved.ValidCoordinates
    (t : Frontend.Transcript.ToolchainObserved) : Prop :=
  ∀ command ∈ t.commands, command.added = command.addedDeclarations.map (·.name) ∧
    ∀ name ∈ command.added, name ≠ .anonymous

/-- The executed check accepts exactly the transcripts with valid coordinates. -/
theorem Frontend.Transcript.ToolchainObserved.validCoordinates_iff
    (t : Frontend.Transcript.ToolchainObserved) :
    t.validCoordinates = true ↔ t.ValidCoordinates := by
  simp [Frontend.Transcript.ToolchainObserved.validCoordinates,
    Frontend.Transcript.ToolchainObserved.ValidCoordinates,
    -Array.all_eq_true, Array.all_eq_true']

/-- The executed check of a declaration's admitted ranges accepts exactly a declaration whose
admitted pair, if it has one, is valid for the lines. -/
theorem Declaration.ranges_all_validForLines_iff (d : Declaration) (lines : List String) :
    d.ranges.all (·.validForLines lines) = true ↔
      ∀ ranges ∈ d.ranges, ranges.ValidForLines lines := by
  cases d.ranges <;> simp [Ranges.validForLines_iff]

/-- Admitted inventories have one declaration per name and one transcript per module.
Ordered mutual-group sequences are intentionally not normalized. Each requirement of a transcript
reads one of its parts: its module, source path, toolchain identity and commands
(`ValidCoordinates`) are observed, and its size and the declarations' ranges are compared with
its source text, which the project writes. -/
def InventoryValid (decls : Array Declaration) (transcripts : Array Frontend.Transcript) : Prop :=
  UniqueNames (decls.map (·.name)) ∧
  (∀ d ∈ decls, d.Valid) ∧
  UniqueNames (transcripts.map (·.module)) ∧
  (∀ t ∈ transcripts, Named t.module ∧ t.source ≠ "" ∧
    t.sourceBytes = t.sourceContent.utf8ByteSize ∧
    t.leanVersion = Compiler.version ∧ t.leanGitHash = Compiler.commit ∧
    t.ValidCoordinates ∧
    ∀ d ∈ decls, d.module = t.module → ∀ ranges ∈ d.ranges, ranges.ValidFor t.sourceContent)
/-- Decide the unchanged declaration-coordinate relation using one supplied line list. -/
def declarationCoordinatesDecidable (decls : Array Declaration)
    (moduleName : Lean.Name) (lines : List String) : Decidable
    (∀ d ∈ decls, d.module = moduleName → d.ranges.all (·.validForLines lines) = true) :=
  inferInstance

instance instDecidableInventoryValid (decls : Array Declaration)
    (transcripts : Array Frontend.Transcript) :
    Decidable (InventoryValid decls transcripts) := by
  unfold InventoryValid
  -- A let in the proposition is reduced during instance synthesis. Bind the
  -- derived lines in the executable decision so all declarations share them.
  letI (t : Frontend.Transcript.ToolchainObserved) : Decidable t.ValidCoordinates :=
    decidable_of_iff _ t.validCoordinates_iff
  letI (t : Frontend.Transcript) : Decidable
      (∀ d ∈ decls, d.module = t.module →
        ∀ ranges ∈ d.ranges, ranges.ValidFor t.sourceContent) :=
    letI := declarationCoordinatesDecidable decls t.module (t.sourceContent.splitOn "\n")
    decidable_of_iff
      (∀ d ∈ decls, d.module = t.module →
        d.ranges.all (·.validForLines (t.sourceContent.splitOn "\n")) = true)
      (by simp only [Declaration.ranges_all_validForLines_iff, Ranges.ValidFor])
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
    simpa only [UniqueNames, Array.map_append, Array.toList_append, Array.toList_map] using valid.1
  have leftMember : a.name ∈ left.toList.map (·.name) :=
    List.mem_map.mpr ⟨a, by simpa using ha, rfl⟩
  have rightMember : b.name ∈ right.toList.map (·.name) :=
    List.mem_map.mpr ⟨b, by simpa using hb, rfl⟩
  exact (List.pairwise_append.mp distinct).2.2 a.name leftMember b.name rightMember sameName

/-- A recorded contract of a declaration of another claimed surface of the same project, which the
project's manifest counts toward the registered decisions of an inventory (RG1008): the surface
whose environment declares the registration, the registration, its module and its recorded
contract. A project census admits it only as the record that surface's own environment holds in
the same run (`EnvironmentCensusOK`, `countedContracts`). -/
structure CountedContract where
  /-- The claimed surface, by its Lake library's name, whose environment declares the
  registration. -/
  surface : String
  /-- The declaration that registers the contract. -/
  registration : Lean.Name
  /-- The module that declares the registration. -/
  «module» : Lean.Name
  /-- The registration's recorded contract. -/
  contract : ExecutableContract
  deriving Repr, DecidableEq

/-- No raw constructor or decoder can omit the inventory-validity proof. -/
structure Inventory where
  /-- The observed compiler capability, proved equal to this compiled policy's expectation. -/
  compiler : Compiler.Capability
  /-- The admitted declaration observations, in the order supplied. -/
  declarations : Array Declaration
  /-- The admitted frontend transcripts, one per module, in the order supplied. -/
  transcripts : Array Frontend.Transcript
  /-- Proof that the declarations and transcripts satisfy `InventoryValid`. -/
  valid : InventoryValid declarations transcripts
  /-- The recorded contracts of other claimed surfaces that the manifest counts toward the
  registered decisions of this inventory, each with the surface that declares it. Admission
  gives none (`admitInventory`); a project census binds them to the records of the related
  surfaces' environments (`EnvironmentCensusOK`). No other field reads them, and they enter only
  the implementations the inventory counts as decided (`Roles.decided`). -/
  counted : Array CountedContract := #[]
  deriving DecidableEq

/-- `i` with `counted` as the contracts counted from other surfaces, and every other field
unchanged. -/
def Inventory.withCounted (i : Inventory) (counted : Array CountedContract) : Inventory :=
  { i with counted }

/-- Validate without dropping, substituting, or deduplicating result observations. The inventory
counts no contract of another surface. -/
@[regula_decision]
def admitInventory (compiler : Compiler.Capability) (decls : Array Declaration)
    (transcripts : Array Frontend.Transcript) :
    Except String Inventory :=
  if h : InventoryValid decls transcripts then .ok ⟨compiler, decls, transcripts, h, #[]⟩
  else .error "invalid policy inventory: anonymous, duplicate, or malformed identity"

/-- Every valid inventory is admitted with exactly its input fields, counting no contract of
another surface. -/
theorem admitInventory_exact (compiler : Compiler.Capability)
    (ds : Array Declaration) (ts : Array Frontend.Transcript)
    (h : InventoryValid ds ts) :
    admitInventory compiler ds ts = .ok ⟨compiler, ds, ts, h, #[]⟩ := by
  simp [admitInventory, h]
/-- Boundary toolchain-origin receipts must refer to this observation's module. -/
def ExecutionBoundary.Valid (b : ExecutionBoundary) : Prop :=
  Named b.name ∧ Named b.module ∧
  (∀ n ∈ b.replacement, Named n) ∧ (∀ n ∈ b.compilerCallers, Named n) ∧
  (∀ o ∈ b.toolchainOrigin?, o.moduleName = b.module)
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
  canonicalNames c.nodes = c.nodes ∧ root ∈ c.nodes ∧ (∀ n ∈ c.nodes, Named n) ∧
  c.nodes = canonicalNames (c.visits.map (·.name)) ∧ c.visits.size = c.nodes.size ∧
  c.DiscoveryOK root compilerEdges ∧
  (∀ visit ∈ c.visits, ∀ m ∈ visit.moduleName, Named m) ∧
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
  Named r.name ∧ Named r.module ∧
  canonicalEdges r.compilerEdges = r.compilerEdges ∧
  (∀ b ∈ r.boundaries, b.Valid) ∧
  (r.boundaries.map (·.occurrence)).toList.Pairwise (· ≠ ·) ∧
  (∀ e ∈ r.compilerEdges, Named e.1 ∧ Named e.2) ∧
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

/-- Execution roots have pairwise distinct names and each satisfies `ExecutionRoot.Valid`. -/
def ExecutionValid (roots : Array ExecutionRoot) : Prop :=
  UniqueNames (roots.map (·.name)) ∧ ∀ r ∈ roots, r.Valid
instance instDecidableExecutionValid (roots : Array ExecutionRoot) : Decidable
    (ExecutionValid roots) := by
  unfold ExecutionValid
  infer_instance

/-- Execution-root observations bundled with the proof of their structural validity. -/
structure ExecutionInventory where
  /-- The admitted execution roots, in the order supplied. -/
  roots : Array ExecutionRoot
  /-- Proof that the roots satisfy `ExecutionValid`. -/
  valid : ExecutionValid roots
  deriving DecidableEq

/-- Admit the roots unchanged when `ExecutionValid` holds, and refuse them otherwise
(`admitExecution_exact`, `admitExecution_preserves`). -/
@[regula_decision]
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

/-- Inventory admission succeeds exactly for valid declarations and transcripts. -/
theorem admitInventory_isOk_iff (compiler : Compiler.Capability) (decls : Array Declaration)
    (transcripts : Array Frontend.Transcript) :
    (admitInventory compiler decls transcripts).isOk = true ↔
      InventoryValid decls transcripts := by
  unfold admitInventory
  split <;> simp_all [Except.isOk, Except.toBool]

/-- `admitInventory` accepts exactly the declarations and transcripts that satisfy
`InventoryValid`, whatever the capability: it accepts the empty inventory and refuses a
transcript of the anonymous module. Which inventory it returns is `admitInventory_exact`. -/
theorem checked_admitInventory : Regula.ExecutableContract admitInventory (fun admit =>
    Regula.Decides (·.isOk = true)
      (fun input : (Compiler.Capability × Array Declaration) × Array Frontend.Transcript =>
        InventoryValid input.1.2 input.2)
      (Function.uncurry (Function.uncurry admit))) :=
  ⟨.of_iff (fun input => admitInventory_isOk_iff input.1.1 input.1.2 input.2)
    ⟨((⟨Compiler.legacyCompilerTrust, rfl⟩, #[]), #[]),
      (admitInventory_isOk_iff _ _ _).mpr (by simp [InventoryValid, UniqueNames])⟩
    ⟨((⟨Compiler.legacyCompilerTrust, rfl⟩, #[]),
        #[{ «module» := .anonymous, source := "", sourceBytes := 0, sourceContent := "",
            leanVersion := "", leanGitHash := "", imports := #[], commands := #[] }]),
      fun accepted =>
        (((admitInventory_isOk_iff _ _ _).mp accepted).2.2.2 _ (Array.mem_singleton.mpr rfl)).1
          rfl⟩⟩

/-- Execution admission succeeds exactly for valid roots. -/
theorem admitExecution_isOk_iff (roots : Array ExecutionRoot) :
    (admitExecution roots).isOk = true ↔ ExecutionValid roots := by
  unfold admitExecution
  split <;> simp_all [Except.isOk, Except.toBool]

/-- `admitExecution` accepts exactly the roots that satisfy `ExecutionValid`: it accepts no
roots and refuses a root of the anonymous name. Which inventory it returns is
`admitExecution_exact` and `admitExecution_preserves`. -/
theorem checked_admitExecution : Regula.ExecutableContract admitExecution
    (Regula.Decides (·.isOk = true) ExecutionValid) :=
  ⟨.of_iff admitExecution_isOk_iff
    ⟨#[], (admitExecution_isOk_iff _).mpr (by simp [ExecutionValid, UniqueNames])⟩
    ⟨#[{ name := .anonymous, «module» := .anonymous, boundaries := #[], unresolved := #[]
         closure := { nodes := #[], visits := #[] } }],
      fun accepted =>
        (((admitExecution_isOk_iff _).mp accepted).2 _ (Array.mem_singleton.mpr rfl)).1 rfl⟩⟩
end RegulaPolicy
