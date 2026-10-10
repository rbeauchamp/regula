module

public import RegulaPolicy.Specification
public import RegulaPolicy.RoleSpecification
public import Regula.Contract
meta import Regula.Decision

/-! # Role validators and declaration decisions

Actual generated-role validators and declaration decisions over admitted observations.
Role receipts carry equality to these executed validators for the exact inventory.
Theorems below connect the actual public policy functions to the independent relations. -/

@[expose] public section

namespace RegulaPolicy

universe u
open Lean (Name)
open Frontend

/-- Execute the finite independent native relation; preserve inventory order. It takes the role
parts of the records (`roleRecords`), so it reads no project-written field but the three marks of
`Declaration.Role`. -/
def authorizedNativeAxioms (ds : Array Declaration.Role) (ts : Array Transcript := #[]) :
    Array Name :=
  (ds.filter (fun a => decide (NativeTeachingOK ds ts a))).map (·.name)

/-- Execute the finite independent recursive-helper relation; no caller whitelist. It takes the
role parts of the records. -/
def authorizedUnsafeRecHelpers (ds : Array Declaration.Role) : Array Name :=
  (ds.filter (fun h => decide (RecursiveHelperOK ds h))).map (·.name)

/-- Authorization is equivalent to existence of the complete native relation at this name. -/
theorem authorizedNativeAxioms_iff (ds : Array Declaration.Role) (ts : Array Transcript)
    (n : Name) :
    n ∈ authorizedNativeAxioms ds ts ↔ ∃ a ∈ ds, a.name = n ∧ NativeTeachingOK ds ts a := by
  simp [authorizedNativeAxioms, Array.mem_map, Array.mem_filter, and_left_comm, and_comm]

/-- Authorization is equivalent to existence of the complete helper relation at this name. -/
theorem authorizedUnsafeRecHelpers_iff (ds : Array Declaration.Role) (n : Name) :
    n ∈ authorizedUnsafeRecHelpers ds ↔ ∃ h ∈ ds, h.name = n ∧ RecursiveHelperOK ds h := by
  simp [authorizedUnsafeRecHelpers, Array.mem_map, Array.mem_filter, and_left_comm, and_comm]

/-- The marks of an inventory can remove a native role but never add one: every name the executed
validator admits, it admits with every mark of the inventory at its neutral value. -/
theorem authorizedNativeAxioms_neutral {ds : Array Declaration.Role} {ts : Array Transcript}
    {n : Name} (hn : n ∈ authorizedNativeAxioms ds ts) :
    n ∈ authorizedNativeAxioms (ds.map Declaration.Role.neutral) ts := by
  obtain ⟨a, ha, rfl, ok⟩ := (authorizedNativeAxioms_iff ds ts n).mp hn
  exact (authorizedNativeAxioms_iff _ ts _).mpr
    ⟨a.neutral, Array.mem_map_of_mem ha, rfl, ok.neutral⟩

/-- The marks of an inventory can remove a recursion helper but never add one: every name the
executed validator admits, it admits with every mark of the inventory at its neutral value. -/
theorem authorizedUnsafeRecHelpers_neutral {ds : Array Declaration.Role} {n : Name}
    (hn : n ∈ authorizedUnsafeRecHelpers ds) :
    n ∈ authorizedUnsafeRecHelpers (ds.map Declaration.Role.neutral) := by
  obtain ⟨h, hh, rfl, ok⟩ := (authorizedUnsafeRecHelpers_iff ds n).mp hn
  exact (authorizedUnsafeRecHelpers_iff _ _).mpr
    ⟨h.neutral, Array.mem_map_of_mem hh, rfl, ok.neutral⟩

/-- No name the native validator admits is a Standard-Logical axiom, for any inventory. -/
theorem authorizedNativeAxioms_not_logical (ds : Array Declaration.Role) (ts : Array Transcript)
    (n : Name) (hn : n ∈ authorizedNativeAxioms ds ts) : ¬ Permitted .standardLogical n := by
  rw [authorizedNativeAxioms_iff] at hn
  rcases hn with ⟨a, _, ha, hrole⟩
  rcases hrole.2.2 with ⟨_, _, _, hparent, _⟩
  obtain ⟨_, _, hshape⟩ := nativeAxiomOrigin?_shape hparent
  intro hp
  rcases hp with hp | hp | hp
  all_goals
    rw [ha, hp] at hshape
    simp at hshape

/-- The implementations the inventory's decision contracts decide: the implementation of every
recorded contract that states a decision kind and was not refused, in inventory order. It reads
the recorded contracts (`recordedContracts`) and no other field of the records. -/
def decidedImplementations (contracts : Array RecordedContract) : Array Name :=
  contracts.filterMap fun recorded => recorded.bind fun c =>
    if c.kind.isSome && c.failure.isNone then some c.root else none

/-- A name is among the decided implementations exactly when a decision contract of the inventory
decides it (`DecisionRegistered`). -/
theorem decidedImplementations_iff (contracts : Array RecordedContract) (n : Name) :
    n ∈ decidedImplementations contracts ↔ DecisionRegistered contracts n := by
  simp only [decidedImplementations, Array.mem_filterMap, DecisionRegistered, Option.mem_def]
  constructor
  · rintro ⟨r, hr, found⟩
    cases contract : r with
    | none => simp [contract] at found
    | some c =>
      simp only [contract, Option.bind_some, Option.ite_none_right_eq_some, Bool.and_eq_true,
        Option.isNone_iff_eq_none, Option.some.injEq] at found
      exact ⟨r, hr, c, contract, found.2, found.1.1, found.1.2⟩
  · rintro ⟨r, hr, c, contract, root, kind, failure⟩
    exact ⟨r, hr, by simp [contract, kind, failure, root]⟩

/-- The refusals of the recorded contracts can remove a decided implementation but do not add one:
each name the executed function gives, it gives with each contract refusing nothing. -/
theorem decidedImplementations_neutral {cs : Array RecordedContract} {n : Name}
    (hn : n ∈ decidedImplementations cs) :
    n ∈ decidedImplementations (cs.map RecordedContract.neutral) := by
  obtain ⟨r, hr, c, hc, root, kind, -⟩ := (decidedImplementations_iff cs n).mp hn
  exact (decidedImplementations_iff _ n).mpr
    ⟨RecordedContract.neutral r, Array.mem_map_of_mem hr, { c with failure := none, shared := {} },
      by simp [RecordedContract.neutral, Option.mem_def.mp hc], root, kind, rfl⟩

/-- Every name `authorizedUnsafeRecHelpers` admits is a helper for which the checker recorded that
Lean's own recursion compiler regenerated its base and that Lean's kernel checked the base's
recursion equation for the helper's value (`Declaration.unsafeRecRegenerated`), and whose
Lean-linked base (`Declaration.unsafeRecBase`) is an inventory definition of the same module and
type, neither `partial` nor `unsafe`, with every axiom within Standard-Logical. Where that
observation is truthful, the base is Lean's compilation of the helper's own recursion up to the
comparison the checker makes (`Erasure.reproduces`: compilation erasure, with a `match` that
passes a variable through taken as the direct one where the kernel checks the two equal), so its
kernel-checked value carries the decreasing proofs of the recursion Lean compiled, after its
well-founded preprocessing; those proofs rest on no `sorryAx` or project axiom. The theorem states
the recorded observations and nothing more: it does not prove the regeneration, its comparison or
the kernel's check of the recursion equation truthful, and it does not relate compiled code to
kernel values. -/
theorem authorizedUnsafeRecHelpers_base (ds : Array Declaration.Role) (n : Name)
    (hn : n ∈ authorizedUnsafeRecHelpers ds) :
    ∃ h ∈ ds, h.name = n ∧ h.unsafeRecRegenerated.isSome = true ∧ ∃ b ∈ ds,
      h.unsafeRecBase = some b.name ∧ b.kind = .definition ∧ b.module = h.module ∧
      b.type = h.type ∧ b.isPartial = false ∧ b.isUnsafe = false ∧
      ∀ a ∈ b.axioms, Permitted .standardLogical a := by
  obtain ⟨h, hd, rfl, hshape, _, b, hb, hbase, shape, _⟩ :=
    (authorizedUnsafeRecHelpers_iff ds n).mp hn
  obtain ⟨hkind, hmodule, hpartial, hunsafe, _, _, htype, _, _, haxioms⟩ := shape
  exact ⟨h, hd, rfl, hshape.2.2.2.2.2.2.2.2, b, hb, hbase, hkind, hmodule.symm, htype.symm,
    hpartial, hunsafe, haxioms⟩

/-- `p` is the declaration Lean compiles through the partial helper `h`: `h` is `partial` and its
Lean-linked base (`Declaration.unsafeRecBase`, Lean's own `Compiler.isUnsafeRecName?`) is `p`, an
opaque constant of the same module. Lean represents a `partial def`, written by the author or
generated by a deriving handler, as such an opaque constant, and its code generator runs the
helper in its place (`Compiler.LCNF.getDeclInfo?`, which also treats that opaque constant as
partial in `declIsNotUnsafe`). -/
def PartialParent (h p : Declaration) : Prop :=
  h.isPartial = true ∧ h.unsafeRecBase = some p.name ∧ p.module = h.module ∧ p.kind = .opaque
instance (h p : Declaration) : Decidable (PartialParent h p) := by
  unfold PartialParent; infer_instance

/-- The inventory declaration that is `h`'s partial parent, if any. -/
def partialParent? (ds : Array Declaration) (h : Declaration) : Option Declaration :=
  ds.find? fun p => decide (PartialParent h p)

/-- In a list with distinct names, a name determines the declaration. -/
private theorem list_eq_of_name_eq {l : List Declaration} (hl : (l.map (·.name)).Pairwise (· ≠ ·))
    {a b : Declaration} (ha : a ∈ l) (hb : b ∈ l) (hn : a.name = b.name) : a = b := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.map_cons, List.pairwise_cons] at hl
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd hn (hl.1 _ (List.mem_map_of_mem hb'))
    · exact absurd hn.symm (hl.1 _ (List.mem_map_of_mem ha'))
    · exact ih hl.2 ha' hb'

/-- In an inventory with distinct names, a name determines the declaration. -/
theorem eq_of_name_eq {ds : Array Declaration} (unique : UniqueNames (ds.map (·.name)))
    {a b : Declaration} (ha : a ∈ ds) (hb : b ∈ ds) (hn : a.name = b.name) : a = b :=
  list_eq_of_name_eq (by simpa only [UniqueNames, Array.toList_map] using unique)
    (Array.mem_toList_iff.mpr ha) (Array.mem_toList_iff.mpr hb) hn

/-- In an inventory with distinct names, `partialParent?` finds exactly `h`'s partial parent. -/
theorem partialParent?_eq_some_iff {ds : Array Declaration}
    (unique : UniqueNames (ds.map (·.name))) (h p : Declaration) :
    partialParent? ds h = some p ↔ p ∈ ds ∧ PartialParent h p := by
  constructor
  · intro found
    unfold partialParent? at found
    exact ⟨Array.mem_of_find?_eq_some found, by simpa using Array.find?_some found⟩
  · rintro ⟨hp, parent⟩
    cases found : partialParent? ds h with
    | none =>
      unfold partialParent? at found
      exact absurd (Array.find?_eq_none.mp found p hp) (by simpa using parent)
    | some q =>
      unfold partialParent? at found
      have hq := Array.mem_of_find?_eq_some found
      have parentQ : PartialParent h q := by simpa using Array.find?_some found
      have hname : q.name = p.name := Option.some.inj (parentQ.2.1.symm.trans parent.2.1)
      rw [eq_of_name_eq unique hq hp hname]

/-- The helper of a partial parent is never an authorized recursion helper: the finding about
it belongs to the declaration the author wrote (or derived). Its base is that opaque parent,
while an authorized helper's base is a definition (`authorizedUnsafeRecHelpers_base`). -/
theorem partialParent_not_authorized {ds : Array Declaration}
    (unique : UniqueNames (ds.map (·.name))) {h p : Declaration} (hh : h ∈ ds) (hp : p ∈ ds)
    (parent : PartialParent h p) : h.name ∉ authorizedUnsafeRecHelpers (roleRecords ds) := by
  intro authorized
  obtain ⟨h', hh', hname, _, b, hb, hbase, hkind, _⟩ :=
    authorizedUnsafeRecHelpers_base (roleRecords ds) h.name authorized
  obtain ⟨dh, hdh, rfl⟩ := mem_roleRecords.mp hh'
  obtain ⟨db, hdb, rfl⟩ := mem_roleRecords.mp hb
  have hname : dh.name = h.name := hname
  have hkind : db.kind = .definition := hkind
  cases eq_of_name_eq unique hdh hh hname
  have hbp : db.name = p.name := Option.some.inj (hbase.symm.trans parent.2.1)
  cases eq_of_name_eq unique hdb hp hbp
  exact absurd (hkind.symm.trans parent.2.2.2) (by decide)

/-- Raw membership calculation over a caller-supplied set; it authorizes no role. -/
def compilerAxiom (native : Array Name) (name : Name) : Bool :=
  builtinCompilerAxiom name || native.contains name

/-- Raw classification over supplied axiom sets. Use `foundationFor` for an
inventory-bound classification with recomputed generated-role evidence. -/
def labelOf (axioms : Array Name) (native : Array Name := #[]) : FoundationClass :=
  if axioms.contains `sorryAx then .hole
  else if axioms.any fun name => !standardLogicalAxiom name && !compilerAxiom native name then
    .unknownAxiom
  else if axioms.any (compilerAxiom native) then .compilerTrusting
  else if axioms.isEmpty then .kernelOnly
  else if axioms.all (ConformingProfile.permits .choiceFree) then .choiceFree
  else .standardLogical

/-- The decision of the shared-test requirement over the recorded contract of a declaration: the
failure where the record of its decision registration names a function with a result of `Bool`
or `BEq` that the specification shares with the implementation or the acceptance predicate, and
nothing otherwise (`checked_sharedTestFailure`). It reads the names alone, which are the collector's
observation (`sharedNames`), so it decides nothing about a function that the collector's search
does not name: a copy of a test under a second name, or a shared function of the other class. -/
@[regula_decision]
def sharedTestFailure (contract : RecordedContract) : Option DeclarationFailure :=
  if contract.any (!·.shared.booleans.isEmpty) then some .sharedTest else none

/-- Exact success relation of the executed shared-test decision, for every record. -/
theorem sharedTestFailure_none_iff (contract : RecordedContract) :
    sharedTestFailure contract = none ↔ SharedTestOK contract := by
  unfold sharedTestFailure SharedTestOK
  cases contract <;> simp

/-- The shared-test decision has one failure, reported exactly where the requirement is unmet. -/
theorem sharedTestFailure_eq_some_iff (contract : RecordedContract)
    (failure : DeclarationFailure) :
    sharedTestFailure contract = some failure ↔
      failure = .sharedTest ∧ ¬ SharedTestOK contract := by
  rw [← sharedTestFailure_none_iff]
  unfold sharedTestFailure
  split <;> simp [eq_comm]

/-- The shared-test decision reports a failure exactly where the requirement is unmet. -/
@[simp] theorem sharedTestFailure_isSome_iff (contract : RecordedContract) :
    (sharedTestFailure contract).isSome = true ↔ ¬ SharedTestOK contract := by
  rw [← sharedTestFailure_none_iff, Option.isSome_iff_ne_none]

/-- `sharedTestFailure` reports nothing exactly when the recorded contract meets `SharedTestOK`
(`sharedTestFailure_none_iff`): nothing for no recorded contract, and the failure for the record
of a decision registration that names one shared test. The decision is over the recorded
names. That the names are the functions that the two sides of the registration share is the
collector's, whose search compares constants by name. -/
theorem checked_sharedTestFailure : Regula.ExecutableContract sharedTestFailure
    (Regula.Decides (· = none) SharedTestOK) :=
  ⟨.of_iff sharedTestFailure_none_iff
    ⟨none, by simp [sharedTestFailure]⟩
    ⟨some { root := `check, requirement := "", failure := none
            kind := some .«soundAndComplete», shared := { booleans := #[`test] } },
      by simp [sharedTestFailure]⟩⟩

/-- Raw computational kernel over supplied role sets; callers can supply arbitrary
sets here. This is not an admission or authorization API. Production decisions
use `policyFor`, whose inventory and Roles arguments enforce the receipt boundary. It takes the
assessed part of the record (`Declaration.Assessed`): kernel-checked data, the observed axioms,
and the recorded contract with the names of its shared tests (`sharedTestFailure`), whose
refusals a mark the project writes can decide. -/
@[regula_decision]
def declarationFailure (decl : Declaration.Assessed) (claim : InspectionRequest)
    (native : Array Name := #[]) (unsafeHelpers : Array Name := #[]) :
    Option DeclarationFailure :=
  if decl.kind == .«axiom» then
    if native.contains decl.name then
      if claim == .teaching then none else some .compilerTrusting
    else some .projectAxiom
  else if decl.axioms.contains `sorryAx then some .proofHole
  else if decl.axioms.any fun name =>
      !standardLogicalAxiom name && !compilerAxiom native name then some .unknownAxiom
  else if (decl.isUnsafe || decl.isPartial) && !unsafeHelpers.contains decl.name then
    some .escapeHatch
  else if decl.axioms.any (compilerAxiom native) && claim != .teaching then
    some .compilerTrusting
  else if decl.executableContract.any (·.failure.isSome) then some .executableContract
  else if (sharedTestFailure decl.executableContract).isSome then some .sharedTest
  else match claim with
    | .conforming profile =>
        if decl.axioms.all fun name => compilerAxiom native name ||
                                        ConformingProfile.permits profile name
        then none else some .profileExceeded
    | .classification | .teaching => none

/-- Raw decision requirement over a supplied set of decided implementations: the failure of a
declaration registered as a decision whose result type is not `Decidable _` and whose name is
not in the set, and nothing otherwise. Callers can supply an arbitrary set here; production
decisions use `policyFor`, whose `Roles` argument binds the set to the inventory. It takes the
registration part of the record (`Declaration.Registration`) and no other field. -/
@[regula_decision]
def decisionFailure (decl : Declaration.Registration) (decided : Array Name) :
    Option DeclarationFailure :=
  if decl.decisionResult == some .«other» && !decided.contains decl.name then
    some .decisionContract
  else none

/-- Exact success relation of the executed decision requirement, for every observation and
supplied set. -/
theorem decisionFailure_none_iff (d : Declaration.Registration) (decided : Array Name) :
    decisionFailure d decided = none ↔ DecisionOK d decided := by
  unfold decisionFailure DecisionOK
  by_cases registered : d.decisionResult = some .«other» <;>
    by_cases member : d.name ∈ decided <;> simp [registered, member]

/-- The decision requirement has one failure, reported exactly where the requirement is unmet. -/
theorem decisionFailure_eq_some_iff (d : Declaration.Registration) (decided : Array Name)
    (failure : DeclarationFailure) :
    decisionFailure d decided = some failure ↔
      failure = .decisionContract ∧ ¬ DecisionOK d decided := by
  rw [← decisionFailure_none_iff]
  unfold decisionFailure
  split <;> simp [eq_comm]

/-- Inventory-bound observations of the actual role validators and of the inventory's decision
contracts. Supplying arbitrary name arrays cannot authorize a role or discharge a decision
requirement: every equation must be proved for this inventory. -/
structure Roles (inventory : Inventory) where
  /-- Names of the declarations that satisfy `NativeTeachingOK`: the native-proof axioms of
  `native_decide`, `decide +native` and `bv_decide` admitted as generated roles, in inventory
  order. -/
  native : Array Name
  /-- Names of the declarations that satisfy `RecursiveHelperOK`: the generated `_unsafe_rec`
  helpers admitted as generated roles, in inventory order. -/
  helpers : Array Name
  /-- The implementations the inventory's decision contracts decide (`DecisionRegistered`), in
  inventory order. -/
  decided : Array Name
  /-- `native` is what `authorizedNativeAxioms` computes from this inventory. -/
  native_exact :
    native = authorizedNativeAxioms (roleRecords inventory.declarations) inventory.transcripts
  /-- `helpers` is what `authorizedUnsafeRecHelpers` computes from this inventory. -/
  helpers_exact : helpers = authorizedUnsafeRecHelpers (roleRecords inventory.declarations)
  /-- `decided` is what `decidedImplementations` computes from this inventory. -/
  decided_exact : decided = decidedImplementations (recordedContracts inventory.declarations)

/-- A name is among an inventory's decided implementations exactly when a decision contract of
that inventory decides it. -/
theorem Roles.decided_iff {i : Inventory} (roles : Roles i) (n : Name) :
    n ∈ roles.decided ↔ DecisionRegistered (recordedContracts i.declarations) n := by
  rw [roles.decided_exact, decidedImplementations_iff]

/-- The generated declarations the safety policy admits: the recursion helpers. No unsafe
constructor-index wrapper is admitted (`RoleSpecification`). -/
def Roles.safetyHelpers {i : Inventory} (roles : Roles i) : Array Name :=
  roles.helpers

/-- Safety membership retains the relation of the recursion-helper family. -/
theorem Roles.safetyHelpers_iff {i : Inventory} (roles : Roles i) (n : Name) :
    n ∈ roles.safetyHelpers ↔
      ∃ h ∈ roleRecords i.declarations, h.name = n ∧
        RecursiveHelperOK (roleRecords i.declarations) h := by
  rw [Roles.safetyHelpers, roles.helpers_exact, authorizedUnsafeRecHelpers_iff]

/-- A partial parent's helper is not a generated safety exception. -/
theorem Roles.partialParent_not_safetyHelper {i : Inventory} (roles : Roles i)
    {h p : Declaration} (hh : h ∈ i.declarations) (hp : p ∈ i.declarations)
    (parent : PartialParent h p) : h.name ∉ roles.safetyHelpers := by
  rw [Roles.safetyHelpers, roles.helpers_exact]
  exact partialParent_not_authorized i.valid.1 hh hp parent

/-- Recompute every validator from the admitted data; no serialized proof is trusted. -/
def authorize (i : Inventory) : Roles i :=
  ⟨authorizedNativeAxioms (roleRecords i.declarations) i.transcripts,
   authorizedUnsafeRecHelpers (roleRecords i.declarations),
   decidedImplementations (recordedContracts i.declarations), rfl, rfl, rfl⟩

/-- Any role receipt for this exact inventory equals recomputation of every validator.
The equations in Roles determine the arrays; no producer verdict is assumed. -/
theorem Roles.eq_authorize {i : Inventory} (roles : Roles i) : roles = authorize i := by
  cases roles with
  | mk native helpers decided native_exact helpers_exact decided_exact =>
    cases native_exact
    cases helpers_exact
    cases decided_exact
    rfl

/-- The inventory's record with name `n`: the identity of a declaration in an inventory, whose
names are unique (`InventoryValid`). -/
def Inventory.record? (i : Inventory) (n : Name) : Option Declaration :=
  i.declarations.find? (·.name == n)

/-- The record with a name is the inventory's member with that name. -/
theorem Inventory.record?_eq_some_iff {i : Inventory} {n : Name} {d : Declaration} :
    i.record? n = some d ↔ d ∈ i.declarations ∧ d.name = n := by
  constructor
  · intro h
    exact ⟨Array.mem_of_find?_eq_some h, by simpa using Array.find?_some h⟩
  · rintro ⟨hd, rfl⟩
    cases h : i.record? d.name with
    | none =>
      unfold Inventory.record? at h
      rw [Array.find?_eq_none] at h
      exact absurd (by simp) (h d hd)
    | some e =>
      have he : e ∈ i.declarations := Array.mem_of_find?_eq_some h
      have hname : e.name = d.name := by simpa using Array.find?_some h
      rw [eq_of_name_eq i.valid.1 he hd hname]

/-- The record of a member is its own record. -/
theorem Inventory.record?_of_mem {i : Inventory} {d : Declaration} (hd : d ∈ i.declarations) :
    i.record? d.name = some d :=
  Inventory.record?_eq_some_iff.mpr ⟨hd, rfl⟩

/-- The policy decision keyed by identity: on the inventory's record with name `n`, the
declaration's own requirements (`declarationFailure`) and, where they are met, the decision
requirement against the inventory's decision contracts (`decisionFailure`); `.invalidInventory`
where the inventory has no record with that name. It takes the name and no supplied record, so
two records with one name get one decision (`policyForName_identity`). -/
@[regula_decision]
def policyForName (i : Inventory) (roles : Roles i) (n : Name) (request : InspectionRequest) :
    Option DeclarationFailure :=
  match i.record? n with
  | some d => (declarationFailure d request roles.native roles.safetyHelpers).or
      (decisionFailure d roles.decided)
  | none => some .invalidInventory

/-- The admission boundary of a supplied record: `.invalidInventory` for a record that is not one
of the inventory's records, and nothing for one that is. It compares the whole record, so a
difference in any field, project-written ones included, refuses the record here; the decision on
an admitted record is `policyForName`, which reads the record's identity alone. -/
@[regula_decision]
def recordFailure (i : Inventory) (d : Declaration) : Option DeclarationFailure :=
  if d ∈ i.declarations then none else some .invalidInventory

/-- The admission boundary refuses exactly the records that are not the inventory's. -/
theorem recordFailure_none_iff (i : Inventory) (d : Declaration) :
    recordFailure i d = none ↔ d ∈ i.declarations := by
  unfold recordFailure
  by_cases hd : d ∈ i.declarations <;> simp [hd]

/-- Public policy: the admission boundary of the supplied record (`recordFailure`), then the
policy decision on its identity (`policyForName`). -/
@[regula_decision]
def policyFor (i : Inventory) (roles : Roles i) (d : Declaration)
    (request : InspectionRequest) : Option DeclarationFailure :=
  (recordFailure i d).or (policyForName i roles d.name request)

/-- `policyFor` checks membership, then decides the record's own requirements and the decision
requirement: the boundary and the identity-keyed decision compose to that. -/
theorem policyFor_eq (i : Inventory) (roles : Roles i) (d : Declaration)
    (request : InspectionRequest) :
    policyFor i roles d request =
      if d ∈ i.declarations then
        (declarationFailure d request roles.native roles.safetyHelpers).or
          (decisionFailure d roles.decided)
      else some .invalidInventory := by
  by_cases hd : d ∈ i.declarations
  · simp [policyFor, recordFailure, hd, policyForName, Inventory.record?_of_mem hd]
  · simp [policyFor, recordFailure, hd]

/-- For a member, `policyFor` is the policy decision on its identity: the whole record enters
`policyFor` only through the admission boundary (`recordFailure`). -/
theorem policyFor_of_mem (i : Inventory) (roles : Roles i) {d : Declaration}
    (hd : d ∈ i.declarations) (request : InspectionRequest) :
    policyFor i roles d request = policyForName i roles d.name request := by
  simp [policyFor, recordFailure, hd]

/-- Foundation rendering uses the same inventory-bound generated-role result. -/
def foundationFor (i : Inventory) (roles : Roles i) (d : Declaration) :
    Except String FoundationClass :=
  if d ∈ i.declarations then .ok (labelOf d.axioms roles.native)
  else .error "declaration is not a member of the authenticated inventory"

/-- Required relation for the member-indexed decision: for every declaration proved to be a
member of the admitted inventory, it is exactly `policyFor`. Non-members cannot be supplied,
so invalid-inventory precedence remains with `policyFor` for arbitrary input. -/
def MemberFailureContract
    (decide : (i : Inventory) → Roles i → (d : Declaration) → d ∈ i.declarations →
      InspectionRequest → Option DeclarationFailure) : Prop :=
  ∀ i roles d (member : d ∈ i.declarations) request,
    decide i roles d member request = policyFor i roles d request

/-- The membership proof, typically supplied by iterating `i.declarations`, replaces
`policyFor`'s linear scan; it is never inspected. Callers use `checked_memberFailure.run`. -/
@[regula_decision]
def memberFailure (i : Inventory) (roles : Roles i) (d : Declaration)
    (_member : d ∈ i.declarations) (request : InspectionRequest) : Option DeclarationFailure :=
  (declarationFailure d request roles.native roles.safetyHelpers).or
    (decisionFailure d roles.decided)

/-- Registers `MemberFailureContract` about `memberFailure`. -/
theorem checked_memberFailure : Regula.ExecutableContract memberFailure MemberFailureContract :=
  ⟨fun i roles d member request => by simp [memberFailure, policyFor_eq, member]⟩

/-- Required relation for the member-indexed classification: for every inventory member,
`foundationFor` succeeds with exactly this class. The member form has no error case. -/
def MemberFoundationContract
    (classify : (i : Inventory) → Roles i → (d : Declaration) → d ∈ i.declarations →
      FoundationClass) : Prop :=
  ∀ i roles d (member : d ∈ i.declarations),
    foundationFor i roles d = .ok (classify i roles d member)

/-- Classification of a proved member; callers use `checked_memberFoundation.run`. -/
def memberFoundation (i : Inventory) (roles : Roles i) (d : Declaration)
    (_member : d ∈ i.declarations) : FoundationClass :=
  labelOf d.axioms roles.native

/-- Registers `MemberFoundationContract` about `memberFoundation`. -/
theorem checked_memberFoundation :
    Regula.ExecutableContract memberFoundation MemberFoundationContract :=
  ⟨fun i roles d member => by simp [memberFoundation, foundationFor, member]⟩

@[simp] theorem compilerAxiom_iff (native : Array Name) (n : Name) :
    compilerAxiom native n = true ↔ CompilerAxiom native n := by
  simp [compilerAxiom, builtinCompilerAxiom, legacyCompilerAxiom, CompilerAxiom, or_assoc]

@[simp] theorem permits_false_iff (p : ConformingProfile) (n : Name) :
    p.permits n = false ↔ ¬ Permitted p n := by
  simp only [Bool.eq_false_iff, ne_eq, permits_iff]

@[simp] theorem compilerAxiom_false_iff (native : Array Name) (n : Name) :
    compilerAxiom native n = false ↔ ¬ CompilerAxiom native n := by
  simp only [Bool.eq_false_iff, ne_eq, compilerAxiom_iff]

private theorem conditional_none {α : Type u} (p : Prop) [Decidable p] (a b : Option α) :
    (if p then a else b) = none ↔ (p ∧ a = none) ∨ (¬p ∧ b = none) := by
  by_cases h : p <;> simp [h]

/-- Exact success relation for the executable declaration decision, for every observation,
request and supplied role set. `policyFor` additionally requires inventory-bound Roles. Raw
computational helpers
do not establish that receipt or any whole-project acceptance claim. -/
theorem declarationFailure_none_iff (d : Declaration.Assessed) (r : InspectionRequest)
    (native helpers : Array Name) :
    declarationFailure d r native helpers = none ↔ DeclarationOK d r native helpers := by
  simp only [declarationFailure, DeclarationOK, KnownDependencies, SafetyOK,
    CompilerPolicyOK, ContractOK, ProfileOK, sharedTestFailure_isSome_iff]
  cases r <;>
    simp [standardLogicalAxiom, permits_iff, compilerAxiom_iff,
      -Array.any_eq_true, -Array.any_eq_false, -Array.all_eq_true, -Array.all_eq_false,
      Array.any_eq_true', Array.all_eq_true', Option.any_eq_true,
      conditional_none, Option.isSome_iff_ne_none] <;>
    grind

/-- `declarationFailure` reports nothing exactly when the recorded declaration meets
`DeclarationOK` for the request and the supplied role sets (`declarationFailure_none_iff`):
nothing for an axiom-free definition under Kernel-only, and a failure for an authored axiom. The
decision is over the recorded declaration and the supplied role sets. That the record is what
Lean holds is the collector's, and that the role sets are the inventory's is `policyFor`'s
`Roles` argument, whose type depends on the inventory (`checked_policyFor`). -/
theorem checked_declarationFailure : Regula.ExecutableContract @declarationFailure
    (fun (failure : Declaration.Assessed → InspectionRequest → Array Name → Array Name →
        Option DeclarationFailure) =>
    Regula.Decides (· = none)
      (fun input : ((Declaration.Assessed × InspectionRequest) × Array Name) × Array Name =>
        DeclarationOK input.1.1.1 input.1.1.2 input.1.2 input.2)
      (Function.uncurry (Function.uncurry (Function.uncurry failure)))) :=
  let recorded (kind : DeclarationKind) : Declaration.Assessed :=
    { name := `subject, «module» := `Module, kind, «type» := "", prettyType := "", isProp := false
      isUnsafe := false, isPartial := false, safety := none, internal := false
      «private» := false, unsafeRecBase := none, levelParams := #[], all := #[], hints := none
      valueConstants := #[], unsafeRecRegenerated := none, nativeStatement := none
      nativeReplay := none, axioms := #[], executableContract := none }
  ⟨.of_iff (fun input => declarationFailure_none_iff input.1.1.1 input.1.1.2 input.1.2 input.2)
    ⟨(((recorded .«definition», .conforming .«kernelOnly»), #[]), #[]),
      by simp [Function.uncurry, declarationFailure, SharedTestOK, recorded]⟩
    ⟨(((recorded .«axiom», .conforming .«kernelOnly»), #[]), #[]),
      by simp [Function.uncurry, declarationFailure, recorded]⟩⟩

/-- `decisionFailure` reports nothing exactly when the registration part of a record meets
`DecisionOK` for the supplied set (`decisionFailure_none_iff`): nothing for a declaration that is
not registered as a decision, and a failure for a registered one whose result type is not
`Decidable _` and that no supplied name decides. The decision is over the name, the recorded
registration and the supplied set. That the record is what Lean holds is the collector's, and
that the set is the inventory's decided implementations is `policyFor`'s `Roles` argument. -/
theorem checked_decisionFailure : Regula.ExecutableContract @decisionFailure
    (fun (failure : Declaration.Registration → Array Name → Option DeclarationFailure) =>
    Regula.Decides (· = none)
      (fun input : Declaration.Registration × Array Name => DecisionOK input.1 input.2)
      (Function.uncurry failure)) :=
  ⟨.of_iff (fun input => decisionFailure_none_iff input.1 input.2)
    ⟨(⟨`subject, none⟩, #[]), by simp [Function.uncurry, decisionFailure]⟩
    ⟨(⟨`subject, some .«other»⟩, #[]), by simp [Function.uncurry, decisionFailure]⟩⟩

/-- The declaration's own requirements never report the decision failure: `decisionFailure` is
its only source. -/
theorem declarationFailure_ne_decisionContract (d : Declaration.Assessed) (r : InspectionRequest)
    (native helpers : Array Name) :
    declarationFailure d r native helpers ≠ some .decisionContract := by
  unfold declarationFailure
  intro h
  repeat' split at h
  all_goals simp_all

/-- The actual public decision is sound and complete for the exact inventory member: the
declaration's own requirements and the decision requirement against this inventory's decided
implementations. -/
theorem policyFor_none_iff (i : Inventory) (roles : Roles i) (d : Declaration)
    (r : InspectionRequest) :
    policyFor i roles d r = none ↔
      d ∈ i.declarations ∧ DeclarationOK d r roles.native roles.safetyHelpers ∧
        DecisionOK d roles.decided := by
  by_cases hd : d ∈ i.declarations
  · simp [policyFor_eq, hd, declarationFailure_none_iff, decisionFailure_none_iff]
  · simp [policyFor_eq, hd]

/-- The refusals of the recorded contract can refuse a declaration but never admit one: whatever
the executed decision passes, it passes with the contract refusing nothing. -/
theorem declarationFailure_neutral {d : Declaration.Assessed} {r : InspectionRequest}
    {native helpers : Array Name} (h : declarationFailure d r native helpers = none) :
    declarationFailure d.neutral r native helpers = none :=
  (declarationFailure_none_iff _ _ _ _).mpr ((declarationFailure_none_iff _ _ _ _).mp h).neutral

/-- Smaller role sets make the executed decision pass nothing more (`DeclarationOK.of_subset`). -/
theorem declarationFailure_of_subset {d : Declaration.Assessed} {r : InspectionRequest}
    {native native' helpers helpers' : Array Name}
    (h : declarationFailure d r native' helpers' = none) (hn : ∀ n ∈ native', n ∈ native)
    (hh : ∀ n ∈ helpers', n ∈ helpers) (logical : ∀ n ∈ native, ¬ Permitted .standardLogical n) :
    declarationFailure d r native helpers = none :=
  (declarationFailure_none_iff _ _ _ _).mpr
    (((declarationFailure_none_iff _ _ _ _).mp h).of_subset hn hh logical)

/-- No mark of the role part and no refusal of the recorded contract admits a declaration under
the executed declaration decision. Take a record that the decision passes under the roles that an
inventory's validators compute. The decision also passes the record with its contract refusing
nothing. It does so under the roles computed with all marks of the inventory at their neutral
values. The decision requirement of RG1008 is `decisionFailure_marks_refuse_only`. -/
theorem declarationFailure_marks_refuse_only (ds : Array Declaration.Role)
    (ts : Array Transcript) {d : Declaration.Assessed} {r : InspectionRequest}
    (h : declarationFailure d r (authorizedNativeAxioms ds ts) (authorizedUnsafeRecHelpers ds) =
      none) :
    declarationFailure d.neutral r (authorizedNativeAxioms (ds.map Declaration.Role.neutral) ts)
      (authorizedUnsafeRecHelpers (ds.map Declaration.Role.neutral)) = none :=
  declarationFailure_neutral <| declarationFailure_of_subset h
    (fun _ => authorizedNativeAxioms_neutral) (fun _ => authorizedUnsafeRecHelpers_neutral)
    (authorizedNativeAxioms_not_logical _ _)

/-- A smaller decided set makes the executed decision requirement pass nothing more
(`DecisionOK.of_subset`). -/
theorem decisionFailure_of_subset {d : Declaration.Registration} {decided decided' : Array Name}
    (h : decisionFailure d decided' = none) (sub : ∀ n ∈ decided', n ∈ decided) :
    decisionFailure d decided = none :=
  (decisionFailure_none_iff _ _).mpr (((decisionFailure_none_iff _ _).mp h).of_subset sub)

/-- No refusal of a recorded contract admits a declaration under the executed decision requirement
of RG1008. Take a registration that the requirement passes under the implementations that the
contracts decide. The requirement also passes it with each contract refusing nothing
(`decidedImplementations_neutral`). -/
theorem decisionFailure_marks_refuse_only (cs : Array RecordedContract)
    {d : Declaration.Registration} (h : decisionFailure d (decidedImplementations cs) = none) :
    decisionFailure d (decidedImplementations (cs.map RecordedContract.neutral)) = none :=
  decisionFailure_of_subset h fun _ => decidedImplementations_neutral

/-- The policy decision takes the identity alone: two records with one name get one decision, so
no field of a record, project-written or not, changes it. -/
theorem policyForName_identity (i : Inventory) (roles : Roles i) {d d' : Declaration}
    (name : d'.name = d.name) (request : InspectionRequest) :
    policyForName i roles d'.name request = policyForName i roles d.name request := by
  rw [name]

/-- Exact success relation of the identity-keyed decision: the inventory has a record with the
name, and that record meets its own requirements and the decision requirement. -/
theorem policyForName_none_iff (i : Inventory) (roles : Roles i) (n : Name)
    (r : InspectionRequest) :
    policyForName i roles n r = none ↔
      ∃ d ∈ i.declarations, d.name = n ∧ DeclarationOK d r roles.native roles.safetyHelpers ∧
        DecisionOK d roles.decided := by
  constructor
  · intro h
    cases hr : i.record? n with
    | none => simp [policyForName, hr] at h
    | some d =>
      obtain ⟨hd, rfl⟩ := Inventory.record?_eq_some_iff.mp hr
      have ok := (policyFor_none_iff i roles d r).mp (by rw [policyFor_of_mem i roles hd]; exact h)
      exact ⟨d, hd, rfl, ok.2⟩
  · rintro ⟨d, hd, rfl, ok⟩
    rw [← policyFor_of_mem i roles hd]
    exact (policyFor_none_iff i roles d r).mpr ⟨hd, ok⟩

/-- `memberFailure` is the policy decision on the member's identity. -/
theorem memberFailure_eq_name (i : Inventory) (roles : Roles i) {d : Declaration}
    (hd : d ∈ i.declarations) (request : InspectionRequest) :
    memberFailure i roles d hd request = policyForName i roles d.name request := by
  simp [memberFailure, policyForName, Inventory.record?_of_mem hd]

/-- `memberFailure` depends on the member only through its name. -/
theorem memberFailure_identity (i : Inventory) (roles : Roles i) {d d' : Declaration}
    (hd : d ∈ i.declarations) (hd' : d' ∈ i.declarations) (name : d'.name = d.name)
    (r : InspectionRequest) : memberFailure i roles d' hd' r = memberFailure i roles d hd r := by
  cases eq_of_name_eq i.valid.1 hd' hd name
  rfl

/-- The record of the axiom-free declaration `subject` of module `Module` with the given kind,
which is registered as no decision: the declaration of the witnesses of `checked_policyFor`,
`checked_policyForName`, `checked_recordFailure`, `checked_memberFailure_decides` and the editor
decision's contract. -/
def witnessDeclaration (kind : DeclarationKind) : Declaration :=
  { name := `subject, «module» := `Module, kind, «type» := "", prettyType := "", isProp := false
    isUnsafe := false, isPartial := false, safety := none, «instance» := false
    «noncomputable» := false, implementedBy := none, «extern» := false, internal := false
    «private» := false, projection := false, matcher := false, recursive := false
    unsafeRecBase := none, levelParams := #[], all := #[], hints := none, valueConstants := #[]
    unsafeRecRegenerated := none, nativeStatement := none
    nativeReplay := none, recordedRanges := none, generatedFrom := none, axioms := #[] }

/-- The inventory of `witnessDeclaration kind` alone, with no transcript. -/
def witnessInventory (kind : DeclarationKind) : Inventory :=
  { compiler := ⟨Compiler.legacyCompilerTrust, rfl⟩
    declarations := #[witnessDeclaration kind]
    transcripts := #[]
    valid := by
      simp [InventoryValid, UniqueNames, Declaration.Valid, witnessDeclaration, Named,
        canonicalNames, CanonicalSet.normalize] }

/-- `witnessDeclaration kind` is the member of `witnessInventory kind`. -/
theorem witnessDeclaration_mem (kind : DeclarationKind) :
    witnessDeclaration kind ∈ (witnessInventory kind).declarations :=
  Array.mem_singleton.mpr rfl

/-- The definition `witnessDeclaration .definition` meets its own requirements under Kernel-only,
for every supplied role set, and the decision requirement for every supplied set: it rests on no
axiom and is registered as no decision. -/
theorem witnessDeclaration_definition_ok (native helpers decided : Array Name) :
    DeclarationOK (witnessDeclaration .«definition») (.conforming .«kernelOnly») native helpers ∧
      DecisionOK (witnessDeclaration .«definition») decided :=
  ⟨(declarationFailure_none_iff _ _ _ _).mp
      (by simp [declarationFailure, SharedTestOK, witnessDeclaration]),
    (decisionFailure_none_iff _ _).mp (by simp [decisionFailure, witnessDeclaration])⟩

/-- The axiom `witnessDeclaration .axiom` fails its own requirements under Kernel-only, for
every supplied role set: an authored axiom is a project axiom, and a native-proof axiom is
compiler-trusting. -/
theorem witnessDeclaration_axiom_not_ok (native helpers : Array Name) :
    ¬ DeclarationOK (witnessDeclaration .«axiom») (.conforming .«kernelOnly») native helpers :=
  fun ok => by
    have none := (declarationFailure_none_iff _ _ _ _).mpr ok
    simp [declarationFailure, witnessDeclaration] at none
    split at none <;> cases none

/-- The arguments of `policyFor`, as the fields of one structure, in the order of the
arguments. -/
structure PolicyInput where
  /-- The admitted inventory. -/
  inventory : Inventory
  /-- The role receipt of that inventory. -/
  roles : Roles inventory
  /-- The declaration to decide. -/
  declaration : Declaration
  /-- The inspection request. -/
  request : InspectionRequest

/-- The arguments of `memberFailure`, and of the editor decision, as the fields of one structure,
in the order of the arguments. -/
structure MemberInput where
  /-- The admitted inventory. -/
  inventory : Inventory
  /-- The role receipt of that inventory. -/
  roles : Roles inventory
  /-- The declaration to decide. -/
  declaration : Declaration
  /-- The declaration is a member of the inventory. -/
  member : declaration ∈ inventory.declarations
  /-- The inspection request. -/
  request : InspectionRequest

/-- The member input of `witnessDeclaration kind` in `witnessInventory kind`, under the
inventory's recomputed roles and Kernel-only: the witness of `checked_memberFailure_decides` and
of the editor decision's contract. -/
def witnessMember (kind : DeclarationKind) : MemberInput :=
  ⟨witnessInventory kind, authorize _, witnessDeclaration kind, witnessDeclaration_mem kind,
    .conforming .«kernelOnly»⟩

/-- `policyFor` reports nothing exactly for a member of the inventory that meets its own
requirements and the decision requirement, under the inventory's own roles
(`policyFor_none_iff`): nothing for an axiom-free definition of its inventory under Kernel-only,
and a failure for a declaration of another inventory. The type of the roles depends on the
inventory, so the kind is stated on the structure of the four arguments. -/
theorem checked_policyFor : Regula.ExecutableContract policyFor (fun decide =>
    Regula.Decides (· = none)
      (fun input : PolicyInput => input.declaration ∈ input.inventory.declarations ∧
        DeclarationOK input.declaration input.request input.roles.native
          input.roles.safetyHelpers ∧
        DecisionOK input.declaration input.roles.decided)
      (fun input => decide input.inventory input.roles input.declaration input.request)) :=
  ⟨.of_iff (fun input =>
      policyFor_none_iff input.inventory input.roles input.declaration input.request)
    ⟨⟨witnessInventory .«definition», authorize _, witnessDeclaration .«definition»,
        .conforming .«kernelOnly»⟩,
      (policyFor_none_iff (witnessInventory .«definition») (authorize _)
          (witnessDeclaration .«definition») (.conforming .«kernelOnly»)).mpr
        ⟨witnessDeclaration_mem _, witnessDeclaration_definition_ok _ _ _⟩⟩
    ⟨⟨witnessInventory .«definition», authorize _, witnessDeclaration .«axiom»,
        .conforming .«kernelOnly»⟩,
      fun accepted => witnessDeclaration_axiom_not_ok _ _
        ((policyFor_none_iff (witnessInventory .«definition») (authorize _)
          (witnessDeclaration .«axiom») (.conforming .«kernelOnly»)).mp accepted).2.1⟩⟩

/-- The arguments of `policyForName`, as the fields of one structure, in the order of the
arguments. -/
structure NameInput where
  /-- The admitted inventory. -/
  inventory : Inventory
  /-- The role receipt of that inventory. -/
  roles : Roles inventory
  /-- The identity of the declaration: its name. -/
  name : Name
  /-- The inspection request. -/
  request : InspectionRequest

/-- `policyForName` reports nothing exactly for a name of the inventory whose record meets its own
requirements and the decision requirement (`policyForName_none_iff`): nothing for the axiom-free
definition `subject` of its inventory under Kernel-only, and a failure for a name the inventory
does not have. The type of the roles depends on the inventory, so the kind is stated on the
structure of the four arguments. -/
theorem checked_policyForName : Regula.ExecutableContract policyForName (fun decide =>
    Regula.Decides (· = none)
      (fun input : NameInput => ∃ d ∈ input.inventory.declarations, d.name = input.name ∧
        DeclarationOK d input.request input.roles.native input.roles.safetyHelpers ∧
        DecisionOK d input.roles.decided)
      (fun input => decide input.inventory input.roles input.name input.request)) :=
  ⟨.of_iff (fun input =>
      policyForName_none_iff input.inventory input.roles input.name input.request)
    ⟨⟨witnessInventory .«definition», authorize _, `subject, .conforming .«kernelOnly»⟩,
      (policyForName_none_iff _ _ _ _).mpr ⟨witnessDeclaration .«definition»,
        witnessDeclaration_mem _, rfl, witnessDeclaration_definition_ok _ _ _⟩⟩
    ⟨⟨witnessInventory .«definition», authorize _, `other, .conforming .«kernelOnly»⟩,
      fun accepted => by
        obtain ⟨d, hd, hname, -⟩ := (policyForName_none_iff _ _ _ _).mp accepted
        simp only [witnessInventory, Array.mem_singleton] at hd
        subst hd
        simp [witnessDeclaration] at hname⟩⟩

/-- `recordFailure` reports nothing exactly for a record of the inventory
(`recordFailure_none_iff`): nothing for the definition of `witnessInventory .definition`, and a
failure for the axiom record of the same name, which the inventory does not hold. -/
theorem checked_recordFailure : Regula.ExecutableContract @recordFailure
    (fun (failure : Inventory → Declaration → Option DeclarationFailure) =>
    Regula.Decides (· = none)
      (fun input : Inventory × Declaration => input.2 ∈ input.1.declarations)
      (Function.uncurry failure)) :=
  ⟨.of_iff (fun input => recordFailure_none_iff input.1 input.2)
    ⟨(witnessInventory .«definition», witnessDeclaration .«definition»),
      (recordFailure_none_iff _ _).mpr (witnessDeclaration_mem _)⟩
    ⟨(witnessInventory .«definition», witnessDeclaration .«axiom»), fun accepted => by
      have hd := (recordFailure_none_iff _ _).mp accepted
      simp [witnessInventory, witnessDeclaration] at hd⟩⟩

/-- `memberFailure` reports nothing exactly for a member that meets its own requirements and the
decision requirement, under the inventory's own roles (`checked_memberFailure`,
`policyFor_none_iff`): nothing for the axiom-free definition of its inventory under Kernel-only,
and a failure for the authored axiom of its inventory. The membership proof is one of the five
arguments, each a field of `MemberInput`. -/
theorem checked_memberFailure_decides : Regula.ExecutableContract memberFailure (fun decide =>
    Regula.Decides (· = none)
      (fun input : MemberInput =>
        DeclarationOK input.declaration input.request input.roles.native
          input.roles.safetyHelpers ∧
        DecisionOK input.declaration input.roles.decided)
      (fun input =>
        decide input.inventory input.roles input.declaration input.member input.request)) :=
  have none_iff (input : MemberInput) :
      memberFailure input.inventory input.roles input.declaration input.member input.request =
          none ↔
        DeclarationOK input.declaration input.request input.roles.native
          input.roles.safetyHelpers ∧
        DecisionOK input.declaration input.roles.decided := by
    rw [checked_memberFailure.evidence, policyFor_none_iff]
    exact and_iff_right input.member
  ⟨.of_iff none_iff
    ⟨witnessMember .«definition»,
      (none_iff (witnessMember .«definition»)).mpr (witnessDeclaration_definition_ok _ _ _)⟩
    ⟨witnessMember .«axiom», fun accepted =>
      witnessDeclaration_axiom_not_ok _ _ ((none_iff (witnessMember .«axiom»)).mp accepted).1⟩⟩

/-- The public decision reports the decision failure exactly for an inventory member that meets
every requirement of its own record, is registered as a decision with a result type other than
`Decidable _`, and is the implementation of no decision contract of this inventory. So among the
declarations that pass their own requirements, the reported ones are exactly the registered
decisions without a `Decidable` result or a decision contract: no other field of the record
enters the requirement. The registration and the result type are the collector's observation,
and so is each recorded contract. -/
theorem policyFor_decisionContract_iff (i : Inventory) (roles : Roles i) (d : Declaration)
    (r : InspectionRequest) :
    policyFor i roles d r = some .decisionContract ↔
      d ∈ i.declarations ∧ DeclarationOK d r roles.native roles.safetyHelpers ∧
        d.decisionResult = some .«other» ∧
          ¬ DecisionRegistered (recordedContracts i.declarations) d.name := by
  have unmet : ¬ DecisionOK d roles.decided ↔
      d.decisionResult = some .«other» ∧
        ¬ DecisionRegistered (recordedContracts i.declarations) d.name := by
    rw [← roles.decided_iff]
    simp [DecisionOK]
  rw [← unmet, ← declarationFailure_none_iff]
  by_cases hd : d ∈ i.declarations
  · simp only [policyFor_eq, hd, ↓reduceIte, true_and]
    cases own : declarationFailure d r roles.native roles.safetyHelpers with
    | none => simp [decisionFailure_eq_some_iff]
    | some failure =>
      have distinct := declarationFailure_ne_decisionContract d r roles.native roles.safetyHelpers
      rw [own] at distinct
      simpa using distinct
  · simp [policyFor_eq, hd]

/-- Logical classification is an embedding of exactly the three conforming profiles. -/
def ConformingProfile.foundationClass : ConformingProfile → FoundationClass
  | .kernelOnly => .kernelOnly | .choiceFree => .choiceFree | .standardLogical => .standardLogical

/-- Authenticated native names cannot be any of the three standard logical axioms. -/
theorem native_not_logical (i : Inventory) (roles : Roles i) (n : Name)
    (hn : n ∈ roles.native) : ¬ Permitted .standardLogical n := by
  rw [roles.native_exact] at hn
  exact authorizedNativeAxioms_not_logical _ _ n hn

/-- The compiled classifier uses exactly the legacy capability retained by inventory admission. -/
theorem builtinCompilerAxiom_inventory (i : Inventory) (n : Name) :
    builtinCompilerAxiom n =
      (decide (i.compiler.legacy = .present) && legacyCompilerAxiom n) := by
  rw [i.compiler.agrees]
  rfl

/-- None of the legacy family has the name shape required of an authenticated native role. -/
theorem legacy_not_native (i : Inventory) (roles : Roles i) (n : Name)
    (legacy : legacyCompilerAxiom n = true) : n ∉ roles.native := by
  intro hn
  rw [roles.native_exact, authorizedNativeAxioms_iff] at hn
  rcases hn with ⟨a, _, ha, hrole⟩
  rcases hrole.2.2 with ⟨_, _, _, hparent, _⟩
  obtain ⟨_, _, hshape⟩ := nativeAxiomOrigin?_shape hparent
  simp only [legacyCompilerAxiom, Bool.or_eq_true, beq_iff_eq] at legacy
  rcases legacy with (legacy | legacy) | legacy
  all_goals
    rw [ha, legacy] at hshape
    simp at hshape

/-- A retired compiler name receives no compiler classification, including through generated roles. -/
theorem retired_not_compiler (i : Inventory) (roles : Roles i) (n : Name)
    (absent : i.compiler.legacy = .absent) (legacy : legacyCompilerAxiom n = true) :
    compilerAxiom roles.native n = false := by
  have h := builtinCompilerAxiom_absent (i.compiler.agrees.symm.trans absent) n
  simp [compilerAxiom, h, legacy_not_native i roles n legacy]

/-- Retired names are unknown axioms, never logical or compiler-trusting labels. -/
theorem retired_label (i : Inventory) (roles : Roles i) (n : Name)
    (absent : i.compiler.legacy = .absent) (legacy : legacyCompilerAxiom n = true) :
    labelOf #[n] roles.native = .unknownAxiom := by
  have hc := retired_not_compiler i roles n absent legacy
  simp only [legacyCompilerAxiom, Bool.or_eq_true, beq_iff_eq] at legacy
  rcases legacy with (rfl | rfl) | rfl <;>
    simp [labelOf, standardLogicalAxiom, ConformingProfile.permits, hc]

/-- An imported retired axiom is refused even for compiler-trust teaching. The earlier hole
and owned-axiom priorities are excluded explicitly; every remaining request has the same refusal. -/
theorem retired_dependency_failure (i : Inventory) (roles : Roles i) (d : Declaration.Assessed)
    (request : InspectionRequest) (n : Name) (absent : i.compiler.legacy = .absent)
    (legacy : legacyCompilerAxiom n = true) (used : n ∈ d.axioms)
    (notAxiom : d.kind ≠ .«axiom») (noHole : `sorryAx ∉ d.axioms) :
    declarationFailure d request roles.native roles.safetyHelpers = some .unknownAxiom := by
  have hc := retired_not_compiler i roles n absent legacy
  have logical : standardLogicalAxiom n = false := by
    simp only [legacyCompilerAxiom, Bool.or_eq_true, beq_iff_eq] at legacy
    rcases legacy with (rfl | rfl) | rfl <;>
      simp [standardLogicalAxiom, ConformingProfile.permits]
  have unknown : (d.axioms.any fun name =>
      !standardLogicalAxiom name && !compilerAxiom roles.native name) = true :=
    Array.any_eq_true'.mpr ⟨n, used, by simp [logical, hc]⟩
  simp [declarationFailure, notAxiom, noHole, unknown]

/-- Every authenticated native role is a name the `nativeEqTrue` scheme generates for a native
tactic, under a generated prefix of an inventory declaration in that declaration's own module
(`GeneratedPrefix`, characterized by `generatedPrefix_iff`). -/
theorem native_generated (i : Inventory) (roles : Roles i) (n : Name) (hn : n ∈ roles.native) :
    ∃ p ∈ i.declarations, ∃ pfx t idxs, GeneratedPrefix p.module p.name pfx ∧
      NativeGenerated pfx idxs ∧ n = nativeAxiomName pfx t idxs := by
  rw [roles.native_exact, authorizedNativeAxioms_iff] at hn
  rcases hn with ⟨a, _, rfl, hrole⟩
  rcases hrole.2.2 with ⟨p, hp, ⟨pfx, t⟩, hparent, _, hprefix, _⟩
  obtain ⟨idxs, hg, h⟩ := nativeAxiomOrigin?_sound hparent
  obtain ⟨dp, hdp, rfl⟩ := mem_roleRecords.mp hp
  exact ⟨dp, hdp, pfx, t, idxs, hprefix, hg, h⟩

/-- The execution probe's name-level classification agrees on every authenticated native role. -/
theorem native_compilerTrustingAxiomName (i : Inventory) (roles : Roles i) (n : Name)
    (hn : n ∈ roles.native) : compilerTrustingAxiomName n = true := by
  rw [roles.native_exact, authorizedNativeAxioms_iff] at hn
  rcases hn with ⟨a, _, rfl, hrole⟩
  rcases hrole.2.2 with ⟨_, _, _, hparent, _⟩
  simp [compilerTrustingAxiomName, Option.mem_def.mp hparent]

/-- Every authenticated native role is an inventory axiom whose asserted statement an independent
native evaluation confirmed, and some command of its module's fresh transcripts adds an axiom of
the same generated origin and statement while no `axiom` declaration occurs in its recorded
syntax. -/
theorem native_provenance (i : Inventory) (roles : Roles i) (n : Name) (hn : n ∈ roles.native) :
    ∃ a ∈ i.declarations, a.name = n ∧ a.nativeReplay = some true ∧
      ∃ c ∈ moduleCommands i.transcripts a.module,
        (∃ d ∈ c.addedDeclarations, nativeAxiomOrigin? d.name = nativeAxiomOrigin? n ∧
          d.kind = .«axiom» ∧ d.nativeStatement = a.nativeStatement) ∧
        c.declaresAxiom = false := by
  rw [roles.native_exact, authorizedNativeAxioms_iff] at hn
  rcases hn with ⟨a, ha, rfl, hshape, _, _, _, o, ho, _, _, c, _, hintro, hundecl⟩
  obtain ⟨-, -, -, -, -, -, -, -, hreplay, -⟩ := hshape
  have hc : c ∈ (moduleCommands i.transcripts a.module).filter (fun cmd =>
      cmd.addedDeclarations.any (fun d => nativeAxiomOrigin? d.name == some (o.1, o.2) &&
        d.kind == .«axiom» && d.nativeStatement == a.nativeStatement)) := by
    rw [hintro]; simp
  obtain ⟨hmem, hany⟩ := Array.mem_filter.mp hc
  obtain ⟨d, hd, hmatch⟩ := Array.any_eq_true'.mp hany
  simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
  have ho' : nativeAxiomOrigin? a.name = some (o.1, o.2) := Option.mem_def.mp ho
  obtain ⟨da, hda, rfl⟩ := mem_roleRecords.mp ha
  refine ⟨da, hda, rfl, hreplay, c, hmem, ⟨d, hd, ?_, hmatch.1.2, hmatch.2⟩, hundecl⟩
  rw [hmatch.1.1, ho']

/-- The compiler-trusting and logical sets are disjoint for actual inventory-bound roles. -/
theorem compiler_not_logical (i : Inventory) (roles : Roles i) (n : Name)
    (hc : CompilerAxiom roles.native n) : ¬ Permitted .standardLogical n := by
  rcases hc with ⟨_, hc | hc | hc⟩ | hc
  · subst n; simp [Permitted]
  · subst n; simp [Permitted]
  · subst n; simp [Permitted]
  · exact native_not_logical i roles n hc

/-- For any logically admissible observed set, the actual diagnostic classifier returns
its least profile. The role argument is bound to the same admitted inventory. -/
theorem labelOf_logical (i : Inventory) (roles : Roles i) (a : Array Name)
    (ha : ContainsFoundation .standardLogical a) :
    labelOf a roles.native = (leastFoundation a).foundationClass := by
  have hole : `sorryAx ∉ a := by
    intro h
    have := ha _ h
    simp [Permitted] at this
  have known : (a.any fun n => !standardLogicalAxiom n && !compilerAxiom roles.native n) =
      false := by
    rw [Array.any_eq_false']
    intro n hn
    have hp := (permits_iff .standardLogical n).mpr (ha n hn)
    simp [standardLogicalAxiom, hp]
  have comp : (a.any (compilerAxiom roles.native)) = false := by
    rw [Array.any_eq_false']
    intro n hn hc
    exact compiler_not_logical i roles n ((compilerAxiom_iff _ _).mp hc) (ha n hn)
  have empty : ContainsFoundation .kernelOnly a ↔ a = #[] := by
    simp [ContainsFoundation, Permitted, Array.eq_empty_iff_forall_not_mem]
  simp only [labelOf, Array.contains_eq_mem, decide_eq_true_eq, hole, ↓reduceIte, known,
    Bool.false_eq_true, comp, leastFoundation, empty, Array.isEmpty_iff]
  split
  · rfl
  · simp only [Array.all_eq_true', permits_iff]
    change
        (if ContainsFoundation .choiceFree a then FoundationClass.choiceFree else
                                                   .standardLogical) = _
    split <;> rfl

/-- Foundation output is both the least containing profile and bound to the supplied record. -/
theorem foundationFor_least (i : Inventory) (roles : Roles i) (d : Declaration)
    (hd : d ∈ i.declarations) (ha : ContainsFoundation .standardLogical d.axioms) :
    foundationFor i roles d = .ok (leastFoundation d.axioms).foundationClass ∧
      LeastFoundation d.axioms (leastFoundation d.axioms) := by
  exact ⟨by simp [foundationFor, hd, labelOf_logical i roles _ ha], leastFoundation_spec _ ha⟩

/-- Decision instances used by acceptance execute the same proved checker function. -/
instance (d : Declaration.Assessed) (r : InspectionRequest) (native helpers : Array Name) :
    Decidable (DeclarationOK d r native helpers) :=
  decidable_of_iff (declarationFailure d r native helpers = none)
    (declarationFailure_none_iff d r native helpers)


/-- Each conforming profile is contained in Standard-Logical. -/
theorem permitted_standard (p : ConformingProfile) (n : Name) (h : Permitted p n) :
    Permitted .standardLogical n := by
  cases p with
  | kernelOnly => exact False.elim h
  | choiceFree =>
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  | standardLogical => exact h

/-- Positive inspection is exactly the permitted foundation, safety exception, recorded contract
and shared-test requirements. Teaching authorization never relaxes a conforming profile. -/
theorem conforming_iff (i : Inventory) (roles : Roles i) (d : Declaration) (p : ConformingProfile) :
    DeclarationOK d (.conforming p) roles.native roles.safetyHelpers ↔
      FoundationOK d p ∧ SafetyOK d roles.safetyHelpers ∧ ContractOK d.executableContract ∧
        SharedTestOK d.executableContract := by
  constructor
  · intro h
    rcases h with h | ⟨ha, _, _, hs, hc, ht, hshared, hp⟩
    · cases h.2.2
    · refine ⟨⟨ha, ?_⟩, hs, ht, hshared⟩
      have free : ∀ n ∈ d.axioms, ¬ CompilerAxiom roles.native n := by
        rcases hc with hc | hc
        · cases hc
        · exact hc
      intro n hn
      rcases hp n hn with hcomp | hperm
      · exact False.elim (free n hn hcomp)
      · exact hperm
  · rintro ⟨⟨ha, hp⟩, hs, ht, hshared⟩
    have logical : ContainsFoundation .standardLogical d.axioms :=
      fun n hn => permitted_standard p n (hp n hn)
    have free : ∀ n ∈ d.axioms, ¬ CompilerAxiom roles.native n :=
      fun n hn hc => compiler_not_logical i roles n hc (logical n hn)
    refine Or.inr ⟨ha, ?_, ?_, hs, Or.inr free, ht, hshared, ?_⟩
    · intro hh
      have := logical _ hh
      simp [Permitted] at this
    · exact fun n hn => Or.inl (logical n hn)
    · exact fun n hn => Or.inr (hp n hn)

/-- The actual public checker decision proves all positive declaration requirements and
refuses exactly when membership or one of those requirements fails. -/
theorem policyFor_conforming_iff (i : Inventory) (roles : Roles i) (d : Declaration)
    (p : ConformingProfile) :
    policyFor i roles d (.conforming p) = none ↔ d ∈ i.declarations ∧
      (FoundationOK d p ∧ SafetyOK d roles.safetyHelpers ∧ ContractOK d.executableContract ∧
        SharedTestOK d.executableContract) ∧
        DecisionOK d roles.decided := by
  rw [policyFor_none_iff, conforming_iff]

/-- Every actual classifier outcome has exactly its independent six-way meaning, including
hole-before-unknown-before-compiler precedence. This holds even for raw role-name arrays. -/
theorem labelOf_iff (axioms native : Array Name) (label : FoundationClass) :
    labelOf axioms native = label ↔ ClassificationOK axioms native label := by
  cases label <;>
    simp only [labelOf, Array.contains_eq_mem, decide_eq_true_eq, standardLogicalAxiom,
      Array.any_eq_true', Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      permits_false_iff, compilerAxiom_false_iff, compilerAxiom_iff, Array.isEmpty_iff,
      Array.all_eq_true', permits_iff, ClassificationOK, not_exists, not_and, ne_eq,
      ContainsFoundation, Classical.not_forall, ite_eq_left_iff, not_or] <;>
    (repeat' split) <;> (try simp_all) <;> grind

/-- Public foundation output retains exact classification and inventory membership for all
six outcomes, not only the three permitted logical profiles. -/
theorem foundationFor_iff (i : Inventory) (roles : Roles i) (d : Declaration)
    (label : FoundationClass) :
    foundationFor i roles d = .ok label ↔ d ∈ i.declarations ∧
        ClassificationOK d.axioms roles.native label := by
  by_cases hd : d ∈ i.declarations <;> simp [foundationFor, hd, labelOf_iff]

/-- The actual declaration diagnostic is the first failed independent requirement. All
success and refusal outputs, including their precedence, follow this same relation. -/
theorem declarationFailure_ordered (d : Declaration.Assessed) (r : InspectionRequest)
    (native helpers : Array Name) :
    OrderedDecision (declarationRequirements d r native helpers)
        (declarationFailure d r native helpers) := by
  by_cases hd : d.kind = .«axiom» <;> cases r <;>
    simp only [declarationRequirements, hd, ↓reduceIte, reduceCtorEq, declarationFailure,
      BEq.rfl, Array.contains_eq_mem, decide_eq_true_eq, beq_iff_eq, orderedDecision_cons,
      ite_eq_right_iff, Option.some.injEq, imp_false, and_self, not_false_eq_true,
      ite_eq_left_iff, Decidable.not_not, true_and, orderedDecision_nil, false_and, or_false,
      not_true_eq_false, Option.ite_none_left_eq_some, and_false, false_or, KnownDependencies,
      SafetyOK, CompilerPolicyOK, ContractOK, Option.mem_def, ProfileOK, standardLogicalAxiom,
      Array.any_eq_true', Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      permits_false_iff, compilerAxiom_false_iff, Bool.or_eq_true, decide_eq_false_iff_not,
      compilerAxiom_iff, bne_iff_ne, ne_eq, and_true, Option.any_eq_true,
      Option.isSome_iff_ne_none, Classical.not_forall, not_or, not_and,
      Bool.not_eq_false, true_or, bne_self_eq_false, Bool.and_false, Bool.false_eq_true,
      Array.all_eq_true', permits_iff, sharedTestFailure_none_iff] <;>
    (repeat' split) <;> (try simp_all) <;> grind

/-- Exact outcome equivalence follows from existence and uniqueness of the first failure. -/
theorem declarationFailure_iff (d : Declaration.Assessed) (r : InspectionRequest)
    (native helpers : Array Name)
    (result : Option DeclarationFailure) :
    declarationFailure d r native helpers = result ↔
      OrderedDecision (declarationRequirements d r native helpers) result := by
  constructor
  · intro h; rw [← h]; exact declarationFailure_ordered d r native helpers
  · intro h; exact (declarationFailure_ordered d r native helpers).unique h

/-- Invalid inventory membership precedes all declaration-policy diagnostics, and the decision
requirement follows every requirement of the declaration's own record (`policyRequirements`). -/
theorem policyFor_ordered (i : Inventory) (roles : Roles i) (d : Declaration)
    (r : InspectionRequest) :
    (d ∉ i.declarations ∧ policyFor i roles d r = some .invalidInventory) ∨
    (d ∈ i.declarations ∧
      OrderedDecision (policyRequirements d r roles.native roles.safetyHelpers roles.decided)
        (policyFor i roles d r)) := by
  by_cases hd : d ∈ i.declarations
  · refine Or.inr ⟨hd, ?_⟩
    have own := declarationFailure_ordered d r roles.native roles.safetyHelpers
    simp only [policyFor_eq, hd, ↓reduceIte, policyRequirements, orderedDecision_append_singleton]
    cases found : declarationFailure d r roles.native roles.safetyHelpers with
    | some failure => exact Or.inl ⟨failure, found ▸ own, rfl⟩
    | none =>
      refine Or.inr ⟨found ▸ own, ?_⟩
      by_cases met : DecisionOK d roles.decided
      · exact Or.inr ⟨met, by simp [(decisionFailure_none_iff d roles.decided).mpr met]⟩
      · exact Or.inl ⟨met, by
          simp [(decisionFailure_eq_some_iff d roles.decided .decisionContract).mpr ⟨rfl, met⟩]⟩
  · exact Or.inl ⟨hd, by simp [policyFor_eq, hd]⟩

end RegulaPolicy
