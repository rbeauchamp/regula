import Regula.Checker.ProducerReport
import Lean.Replay
import Regula.Probe
import Regula.Checker.SharedName
import Std.Data.HashMap.Lemmas
import Regula.Decision
import RegulaPolicy.KernelAxioms

/-!
# Checked logical admission

Checked logical admission before report construction. The replay base contains
only imported modules outside the replayed inventory. Unsafe and partial entries
remain subject to generated-role policy; they cannot supply logical evidence.
An owned module that an earlier environment of the same audit admitted over the
identical, frozen import closure is reused instead of replayed again (`reusedModules`,
`offers`, `reuseJustified_frozen`); every other owned module is replayed (`mem_replaySet`). A
member's import closure lies within the closure (`importClosure_trans`), so one pass decides
which candidates have every owned module of their closure reused too.
Replay reads each replayed module's own constants (`Copy`), so a name that several
modules contain, such as an equation lemma Lean realizes in each module that needs it,
has every owned copy checked (`replayMap_sound`, `checkCopies_sound`).
`validate` is an observing pass around three registered decisions: `checkHeader` on the module
data of the header (`checked_checkHeader`), `admitReplay` on the replayed kernel
(`checked_admitReplay`), which returns the receipt, and `checkTable` on the axioms of the owned
declarations. Those axioms are the ones each declaration reaches in the replayed kernel
(`KernelAxioms.axiomTable`), which `validate` returns with the receipt for the foundation rules;
`checkTable` refuses a declaration for which Lean's `collectAxioms` reports an axiom outside them.
-/

namespace Regula.Checker.Admission

open Lean
open RegulaPolicy.Guards (forM_eq_ok)
open RegulaPolicy.KernelAxioms
-- Names cross the worker boundary in the report's own encoding, which reads back every name,
-- including the hygienic names Lean generates (`RegistryCodec.printedNameJson_roundtrip`).
open scoped Regula.Report

/-- An earlier environment's completed admission in the same audit, as the coordinator offers it
to a later environment: the owned modules it replayed and offers for reuse, the declaration keys
its replay admitted in them, and the origin of every module it loaded
(`Probe.loadedModuleOrigins`). -/
structure PriorAdmission where
  /-- Owned modules the earlier environment replayed and admitted, offered for reuse. -/
  modules : Array Name
  /-- The `(module, declaration)` keys the earlier environment's replay admitted in `modules`. -/
  admitted : Array (Name × Name)
  /-- The name, canonical `.olean` path and direct imports of every module it loaded. -/
  origins : Array RegulaPolicy.ModuleOrigin
  deriving ToJson

instance : FromJson PriorAdmission := ⟨fun j => do
  Regula.Checker.PolicyCodec.exactFields j ["modules", "admitted", "origins"]
  return { modules := ← j.getObjValAs? _ "modules", admitted := ← j.getObjValAs? _ "admitted"
           origins := ← j.getObjValAs? _ "origins" }⟩


/-- One environment's module origins, by module name. -/
def originIndex (origins : Array RegulaPolicy.ModuleOrigin) :
    Std.HashMap Name RegulaPolicy.ModuleOrigin :=
  origins.foldl (fun index origin => index.insert origin.name origin) {}

/-- Whether `index` holds every origin under that origin's own name. -/
def Keyed (index : Std.HashMap Name RegulaPolicy.ModuleOrigin) : Prop :=
  ∀ (n : Name) (origin : RegulaPolicy.ModuleOrigin), index[n]? = some origin → origin.name = n

/-- `originIndex` holds every origin under its own name. -/
theorem originIndex_keyed (origins : Array RegulaPolicy.ModuleOrigin) :
    Keyed (originIndex origins) := by
  unfold originIndex
  rw [← Array.foldl_toList]
  suffices step : ∀ (rest : List RegulaPolicy.ModuleOrigin)
      (index : Std.HashMap Name RegulaPolicy.ModuleOrigin), Keyed index →
      Keyed (rest.foldl (fun index origin => index.insert origin.name origin) index) by
    exact step origins.toList {} (by simp [Keyed])
  intro rest
  induction rest with
  | nil => intro index hindex; exact hindex
  | cons head rest ih =>
    intro index hindex
    simp only [List.foldl_cons]
    refine ih _ fun n origin hn => ?_
    rw [Std.HashMap.getElem?_insert] at hn
    split at hn
    · rename_i heq
      obtain rfl := Option.some.inj hn
      exact beq_iff_eq.mp heq
    · exact hindex n origin hn

/-- Settle the `pending` modules, recording in `seen` every name ever pushed: the origin of each
goes into `closure` and its imports not yet seen become pending. It returns the closure once
nothing is pending, or `none` when a pending module has no origin or `fuel` runs out first. -/
def closureLoop (origins : Std.HashMap Name RegulaPolicy.ModuleOrigin) :
    Nat → List Name → Std.HashSet Name → Array RegulaPolicy.ModuleOrigin →
      Option (Array RegulaPolicy.ModuleOrigin)
  | _, [], _, closure => some closure
  | 0, _ :: _, _, _ => none
  | fuel + 1, name :: rest, seen, closure =>
    match origins[name]? with
    | none => none
    | some origin =>
      let next := origin.imports.toList.foldl pushNew (rest, seen)
      closureLoop origins fuel next.1 next.2 (closure.push origin)

/-- The import closure of `m` in one environment: the origin of `m` and of every module it
transitively imports, ordered by name, or `none` when a reached module has no origin. Two
environments have equal closures of `m` exactly when they loaded `m` and every module below it
under the same names, from the same canonical `.olean` files, with the same import edges.
`importClosure_some` and `importClosure_trans` state what a closure holds. -/
def importClosure (origins : Std.HashMap Name RegulaPolicy.ModuleOrigin) (m : Name) :
    Option (Array RegulaPolicy.ModuleOrigin) :=
  -- Each step settles one name and each name is pushed once, so a closure whose every module
  -- has an origin is settled within `origins.size` steps.
  (closureLoop origins origins.size [m] (({} : Std.HashSet Name).insert m) #[]).map
    (·.mergeSort fun a b => !Name.quickLt b.name a.name)

/-- What `closureLoop` maintains, for a property `P` of names. -/
private structure ClosureInv (origins : Std.HashMap Name RegulaPolicy.ModuleOrigin)
    (P : Name → Prop) (pending : List Name) (seen : Std.HashSet Name)
    (closure : Array RegulaPolicy.ModuleOrigin) : Prop where
  /-- Every pending name satisfies `P`. -/
  ofPending : ∀ x ∈ pending, P x
  /-- Every seen name is pending or the name of a settled origin. -/
  ofSeen : ∀ x ∈ seen, x ∈ pending ∨ ∃ origin ∈ closure, origin.name = x
  /-- Every settled origin is the one `origins` holds under its name, has a name satisfying `P`,
  and has every import seen. -/
  ofSettled : ∀ origin ∈ closure, origins[origin.name]? = some origin ∧ P origin.name ∧
    ∀ imported ∈ origin.imports, imported ∈ seen

/-- With nothing pending, every import of a settled origin is the name of a settled origin. -/
private theorem ClosureInv.done {origins : Std.HashMap Name RegulaPolicy.ModuleOrigin}
    {P : Name → Prop} {seen : Std.HashSet Name} {closure : Array RegulaPolicy.ModuleOrigin}
    (h : ClosureInv origins P [] seen closure) :
    ∀ origin ∈ closure, origins[origin.name]? = some origin ∧ P origin.name ∧
      ∀ imported ∈ origin.imports, ∃ other ∈ closure, other.name = imported := by
  intro origin horigin
  obtain ⟨hself, hP, himports⟩ := h.ofSettled origin horigin
  refine ⟨hself, hP, fun imported himported => ?_⟩
  rcases h.ofSeen imported (himports imported himported) with hpending | hsettled
  · simp at hpending
  · exact hsettled

/-- One step of `closureLoop` keeps `ClosureInv`, where `origins` holds every origin under its
own name and `P` passes from a name to the imports of its origin. -/
private theorem ClosureInv.step {origins : Std.HashMap Name RegulaPolicy.ModuleOrigin}
    (hkey : Keyed origins) {P : Name → Prop}
    (hstep : ∀ (n : Name) (origin : RegulaPolicy.ModuleOrigin), P n →
      origins[n]? = some origin → ∀ imported ∈ origin.imports, P imported)
    {name : Name} {rest : List Name} {seen : Std.HashSet Name}
    {closure : Array RegulaPolicy.ModuleOrigin} {origin : RegulaPolicy.ModuleOrigin}
    (h : ClosureInv origins P (name :: rest) seen closure) (ho : origins[name]? = some origin) :
    ClosureInv origins P (origin.imports.toList.foldl pushNew (rest, seen)).1
      (origin.imports.toList.foldl pushNew (rest, seen)).2 (closure.push origin) := by
  have hname : origin.name = name := hkey name origin ho
  have hPname : P name := h.ofPending name List.mem_cons_self
  obtain ⟨f1, f2, f3, f4⟩ := foldl_pushNew origin.imports.toList rest seen
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun other hother => ?_⟩
  · rcases f2 x hx with hx | hx
    · exact h.ofPending x (List.mem_cons_of_mem _ hx)
    · exact hstep name origin hPname ho x (Array.mem_toList_iff.mp hx)
  · rcases f4 x hx with hx | hx
    · rcases h.ofSeen x hx with hpending | ⟨held, hheld, hx⟩
      · rcases List.mem_cons.mp hpending with hx | hpending
        · exact .inr ⟨origin, Array.mem_push_self, hname.trans hx.symm⟩
        · exact .inl (f3 x hpending)
      · exact .inr ⟨held, Array.mem_push_of_mem _ hheld, hx⟩
    · exact .inl hx
  · rcases Array.mem_push.mp hother with hother | hother
    · obtain ⟨hself, hP, himports⟩ := h.ofSettled other hother
      exact ⟨hself, hP, fun imported himported =>
        (f1 imported).mpr (.inl (himports imported himported))⟩
    · subst hother
      exact ⟨by rw [hname]; exact ho, by rw [hname]; exact hPname, fun imported himported =>
        (f1 imported).mpr (.inr (Array.mem_toList_iff.mpr himported))⟩

/-- A completed `closureLoop` that started from a state satisfying `ClosureInv` returns only
origins that `origins` holds under their names, whose names satisfy `P`, and whose imports are
all names of returned origins. -/
private theorem closureLoop_some {origins : Std.HashMap Name RegulaPolicy.ModuleOrigin}
    (hkey : Keyed origins) {P : Name → Prop}
    (hstep : ∀ (n : Name) (origin : RegulaPolicy.ModuleOrigin), P n →
      origins[n]? = some origin → ∀ imported ∈ origin.imports, P imported) :
    ∀ (fuel : Nat) (pending : List Name) (seen : Std.HashSet Name)
      (closure result : Array RegulaPolicy.ModuleOrigin),
      ClosureInv origins P pending seen closure →
      closureLoop origins fuel pending seen closure = some result →
      ∀ origin ∈ result, origins[origin.name]? = some origin ∧ P origin.name ∧
        ∀ imported ∈ origin.imports, ∃ other ∈ result, other.name = imported := by
  intro fuel
  induction fuel with
  | zero =>
    intro pending seen closure result hinv h
    cases pending with
    | nil =>
      simp only [closureLoop, Option.some.injEq] at h
      subst h
      exact hinv.done
    | cons name rest => simp [closureLoop] at h
  | succ fuel ih =>
    intro pending seen closure result hinv h
    cases pending with
    | nil =>
      simp only [closureLoop, Option.some.injEq] at h
      subst h
      exact hinv.done
    | cons name rest =>
      simp only [closureLoop] at h
      cases ho : origins[name]? with
      | none => simp [ho] at h
      | some origin =>
        simp only [ho] at h
        exact ih _ _ _ result (hinv.step hkey hstep ho) h

/-- What a closure holds, where `origins` holds every origin under its own name (`Keyed`,
`originIndex_keyed`): each of its origins is the one `origins` holds under its name; that name
satisfies every property `P` that `m` has and that passes from a name to the imports of its
origin, so it is `m` or a module `m` transitively imports; and every import of one of its origins
is the name of one of its origins. -/
theorem importClosure_some {origins : Std.HashMap Name RegulaPolicy.ModuleOrigin}
    (hkey : Keyed origins) {P : Name → Prop} {m : Name}
    (hm : P m)
    (hstep : ∀ (n : Name) (origin : RegulaPolicy.ModuleOrigin), P n →
      origins[n]? = some origin → ∀ imported ∈ origin.imports, P imported)
    {closure : Array RegulaPolicy.ModuleOrigin} (h : importClosure origins m = some closure) :
    ∀ origin ∈ closure, origins[origin.name]? = some origin ∧ P origin.name ∧
      ∀ imported ∈ origin.imports, ∃ other ∈ closure, other.name = imported := by
  unfold importClosure at h
  obtain ⟨settled, hloop, rfl⟩ := Option.map_eq_some_iff.mp h
  have hinv : ClosureInv origins P [m] (({} : Std.HashSet Name).insert m) #[] := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun origin horigin => ?_⟩
    · rw [List.mem_singleton.mp hx]
      exact hm
    · rcases Std.HashSet.mem_insert.mp hx with hx | hx
      · exact .inl (List.mem_singleton.mpr (beq_iff_eq.mp hx).symm)
      · simp at hx
    · simp at horigin
  intro origin horigin
  obtain ⟨hself, hP, himports⟩ :=
    closureLoop_some hkey hstep _ _ _ _ settled hinv hloop origin (Array.mem_mergeSort.mp horigin)
  refine ⟨hself, hP, fun imported himported => ?_⟩
  obtain ⟨other, hother, hname⟩ := himports imported himported
  exact ⟨other, Array.mem_mergeSort.mpr hother, hname⟩

/-- A member's closure lies within the closure: where `origins` holds every origin under its own
name (`Keyed`, `originIndex_keyed`), the closure of the name of an origin of `m`'s closure holds
only origins of `m`'s closure. -/
theorem importClosure_trans {origins : Std.HashMap Name RegulaPolicy.ModuleOrigin}
    (hkey : Keyed origins) {m : Name}
    {closure : Array RegulaPolicy.ModuleOrigin} (h : importClosure origins m = some closure)
    {origin : RegulaPolicy.ModuleOrigin} (ho : origin ∈ closure)
    {inner : Array RegulaPolicy.ModuleOrigin}
    (hi : importClosure origins origin.name = some inner) :
    ∀ other ∈ inner, other ∈ closure := by
  have outer := importClosure_some hkey (P := fun _ => True) trivial
    (fun _ _ _ _ _ _ => trivial) h
  have within := importClosure_some hkey (P := fun n => ∃ held ∈ closure, held.name = n)
    ⟨origin, ho, rfl⟩ (fun n found ⟨held, hheld, hn⟩ hfound imported himported => by
      obtain ⟨hself, -, himports⟩ := outer held hheld
      rw [hn, hfound] at hself
      obtain rfl := Option.some.inj hself
      exact himports imported himported) hi
  intro other hother
  obtain ⟨hself, ⟨held, hheld, hn⟩, -⟩ := within other hother
  obtain ⟨hheldSelf, -, -⟩ := outer held hheld
  rw [hn, hself] at hheldSelf
  obtain rfl := Option.some.inj hheldSelf
  exact hheld

-- Structural equality for the constant records Lean derives none for, so that `identical`
-- covers every kind of constant.
deriving instance BEq for QuotKind, QuotVal, InductiveVal

/-- Whether two constants are the same constant: the same kind with equal fields, expressions
compared by `Expr.eqv`. -/
def identical : ConstantInfo → ConstantInfo → Bool
  | .axiomInfo a, .axiomInfo b => a == b
  | .defnInfo a, .defnInfo b => a == b
  | .thmInfo a, .thmInfo b => a == b
  | .opaqueInfo a, .opaqueInfo b => a == b
  | .quotInfo a, .quotInfo b => a == b
  | .inductInfo a, .inductInfo b => a == b
  | .ctorInfo a, .ctorInfo b => a == b
  | .recInfo a, .recInfo b => a == b
  | _, _ => false

/-- The constant data of two constants agree: the same name, the same universe parameters, and
types that Lean's own comparison of expressions equates (`==`, which is `Expr.eqv`). Lean has no
lawful equality of expressions, so that test of one expression stays. -/
def SameData (a b : ConstantVal) : Prop :=
  a.name = b.name ∧ a.levelParams = b.levelParams ∧ (a.type == b.type) = true

/-- Two rules of a recursor agree: the same constructor, the same number of fields, and
right-hand sides that Lean's own comparison of expressions equates. -/
def SameRule (a b : RecursorRule) : Prop :=
  a.ctor = b.ctor ∧ a.nfields = b.nfields ∧ (a.rhs == b.rhs) = true

/-- Two constants are the same constant, stated field by field: the two are of the same kind,
their constant data agree (`SameData`), Lean's own comparison of expressions equates each other
expression field, and each remaining field is equal. The rules of two recursors agree one by
one (`SameRule`). The statement has no comparison of a whole record: the only test in it is the
comparison of one expression. `identical` decides it (`identical_iff`). -/
def Identical : ConstantInfo → ConstantInfo → Prop
  | .axiomInfo a, .axiomInfo b =>
      SameData a.toConstantVal b.toConstantVal ∧ a.isUnsafe = b.isUnsafe
  | .defnInfo a, .defnInfo b =>
      SameData a.toConstantVal b.toConstantVal ∧ (a.value == b.value) = true ∧
        a.hints = b.hints ∧ a.safety = b.safety ∧ a.all = b.all
  | .thmInfo a, .thmInfo b =>
      SameData a.toConstantVal b.toConstantVal ∧ (a.value == b.value) = true ∧ a.all = b.all
  | .opaqueInfo a, .opaqueInfo b =>
      SameData a.toConstantVal b.toConstantVal ∧ (a.value == b.value) = true ∧
        a.isUnsafe = b.isUnsafe ∧ a.all = b.all
  | .quotInfo a, .quotInfo b => SameData a.toConstantVal b.toConstantVal ∧ a.kind = b.kind
  | .inductInfo a, .inductInfo b =>
      SameData a.toConstantVal b.toConstantVal ∧ a.numParams = b.numParams ∧
        a.numIndices = b.numIndices ∧ a.all = b.all ∧ a.ctors = b.ctors ∧
        a.numNested = b.numNested ∧ a.isRec = b.isRec ∧ a.isUnsafe = b.isUnsafe ∧
        a.isReflexive = b.isReflexive
  | .ctorInfo a, .ctorInfo b =>
      SameData a.toConstantVal b.toConstantVal ∧ a.induct = b.induct ∧ a.cidx = b.cidx ∧
        a.numParams = b.numParams ∧ a.numFields = b.numFields ∧ a.isUnsafe = b.isUnsafe
  | .recInfo a, .recInfo b =>
      SameData a.toConstantVal b.toConstantVal ∧ a.all = b.all ∧ a.numParams = b.numParams ∧
        a.numIndices = b.numIndices ∧ a.numMotives = b.numMotives ∧
        a.numMinors = b.numMinors ∧
        (a.rules.length = b.rules.length ∧
          ∀ (i : Nat) x y, a.rules[i]? = some x → b.rules[i]? = some y → SameRule x y) ∧
        a.k = b.k ∧ a.isUnsafe = b.isUnsafe
  | _, _ => False

/-- The derived comparison of the constant data compares the name, the universe parameters and
the type. -/
private theorem constantVal_beq_iff (a b : ConstantVal) : (a == b) = true ↔ SameData a b := by
  have unfolded : (a == b) =
      (a.name == b.name && (a.levelParams == b.levelParams && a.type == b.type)) := by
    cases a; cases b; rfl
  rw [unfolded]
  simp only [SameData, Bool.and_eq_true, beq_iff_eq]

/-- The derived comparison of two quotient kinds accepts exactly equal kinds. -/
private theorem quotKind_beq_iff (a b : QuotKind) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> first
    | exact ⟨fun _ => rfl, fun _ => rfl⟩
    | exact ⟨fun h => absurd h (by decide), fun h => nomatch h⟩

/-- The derived comparison of two safety classes accepts exactly equal classes. -/
private theorem safety_beq_iff (a b : DefinitionSafety) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> first
    | exact ⟨fun _ => rfl, fun _ => rfl⟩
    | exact ⟨fun h => absurd h (by decide), fun h => nomatch h⟩

/-- The derived comparison of two reducibility hints accepts exactly equal hints. -/
private theorem hints_beq_iff (a b : ReducibilityHints) : (a == b) = true ↔ a = b := by
  cases a <;> cases b
  case regular.regular x y =>
    have unfolded : (ReducibilityHints.regular x == .regular y) = (x == y) := rfl
    rw [unfolded, beq_iff_eq, ReducibilityHints.regular.injEq]
  all_goals first
    | exact ⟨fun _ => rfl, fun _ => rfl⟩
    | exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩

/-- The derived comparison of two recursor rules compares the three fields. -/
private theorem recursorRule_beq_iff (a b : RecursorRule) : (a == b) = true ↔ SameRule a b := by
  have unfolded : (a == b) = (a.ctor == b.ctor && (a.nfields == b.nfields && a.rhs == b.rhs)) := by
    cases a; cases b; rfl
  rw [unfolded]
  simp only [SameRule, Bool.and_eq_true, beq_iff_eq]

private theorem axiomVal_beq_iff (a b : AxiomVal) :
    (a == b) = true ↔ SameData a.toConstantVal b.toConstantVal ∧ a.isUnsafe = b.isUnsafe := by
  have unfolded : (a == b) = (a.toConstantVal == b.toConstantVal && a.isUnsafe == b.isUnsafe) := by
    cases a; cases b; rfl
  rw [unfolded]
  simp only [Bool.and_eq_true, constantVal_beq_iff, beq_iff_eq]

private theorem definitionVal_beq_iff (a b : DefinitionVal) :
    (a == b) = true ↔
      SameData a.toConstantVal b.toConstantVal ∧ (a.value == b.value) = true ∧
        a.hints = b.hints ∧ a.safety = b.safety ∧ a.all = b.all := by
  have unfolded : (a == b) = (a.toConstantVal == b.toConstantVal && (a.value == b.value &&
      (a.hints == b.hints && (a.safety == b.safety && a.all == b.all)))) := by
    cases a; cases b; rfl
  rw [unfolded]
  simp only [Bool.and_eq_true, constantVal_beq_iff, hints_beq_iff, safety_beq_iff, beq_iff_eq]

private theorem theoremVal_beq_iff (a b : TheoremVal) :
    (a == b) = true ↔
      SameData a.toConstantVal b.toConstantVal ∧ (a.value == b.value) = true ∧ a.all = b.all := by
  have unfolded : (a == b) =
      (a.toConstantVal == b.toConstantVal && (a.value == b.value && a.all == b.all)) := by
    cases a; cases b; rfl
  rw [unfolded]
  simp only [Bool.and_eq_true, constantVal_beq_iff, beq_iff_eq]

private theorem opaqueVal_beq_iff (a b : OpaqueVal) :
    (a == b) = true ↔
      SameData a.toConstantVal b.toConstantVal ∧ (a.value == b.value) = true ∧
        a.isUnsafe = b.isUnsafe ∧ a.all = b.all := by
  have unfolded : (a == b) = (a.toConstantVal == b.toConstantVal && (a.value == b.value &&
      (a.isUnsafe == b.isUnsafe && a.all == b.all))) := by
    cases a; cases b; rfl
  rw [unfolded]
  simp only [Bool.and_eq_true, constantVal_beq_iff, beq_iff_eq]

/-- The derived comparison of two quotient records compares the constant data and the kind. -/
private theorem quotVal_beq_iff (a b : QuotVal) :
    (a == b) = true ↔ SameData a.toConstantVal b.toConstantVal ∧ a.kind = b.kind := by
  have unfolded : (a == b) = (a.toConstantVal == b.toConstantVal && a.kind == b.kind) := by
    cases a; cases b; rfl
  rw [unfolded, Bool.and_eq_true, quotKind_beq_iff, constantVal_beq_iff]

/-- The derived comparison of two inductive records compares the constant data and each other
field. -/
private theorem inductiveVal_beq_iff (a b : InductiveVal) :
    (a == b) = true ↔
      SameData a.toConstantVal b.toConstantVal ∧ a.numParams = b.numParams ∧
        a.numIndices = b.numIndices ∧ a.all = b.all ∧ a.ctors = b.ctors ∧
        a.numNested = b.numNested ∧ a.isRec = b.isRec ∧ a.isUnsafe = b.isUnsafe ∧
        a.isReflexive = b.isReflexive := by
  have unfolded : (a == b) = (a.toConstantVal == b.toConstantVal &&
      (a.numParams == b.numParams && (a.numIndices == b.numIndices && (a.all == b.all &&
      (a.ctors == b.ctors && (a.numNested == b.numNested && (a.isRec == b.isRec &&
      (a.isUnsafe == b.isUnsafe && a.isReflexive == b.isReflexive)))))))) := by
    cases a; cases b; rfl
  rw [unfolded]
  simp only [Bool.and_eq_true, constantVal_beq_iff, beq_iff_eq]

private theorem constructorVal_beq_iff (a b : ConstructorVal) :
    (a == b) = true ↔
      SameData a.toConstantVal b.toConstantVal ∧ a.induct = b.induct ∧ a.cidx = b.cidx ∧
        a.numParams = b.numParams ∧ a.numFields = b.numFields ∧ a.isUnsafe = b.isUnsafe := by
  have unfolded : (a == b) = (a.toConstantVal == b.toConstantVal && (a.induct == b.induct &&
      (a.cidx == b.cidx && (a.numParams == b.numParams && (a.numFields == b.numFields &&
      a.isUnsafe == b.isUnsafe))))) := by
    cases a; cases b; rfl
  rw [unfolded]
  simp only [Bool.and_eq_true, constantVal_beq_iff, beq_iff_eq]

private theorem recursorVal_beq_iff (a b : RecursorVal) :
    (a == b) = true ↔
      SameData a.toConstantVal b.toConstantVal ∧ a.all = b.all ∧ a.numParams = b.numParams ∧
        a.numIndices = b.numIndices ∧ a.numMotives = b.numMotives ∧
        a.numMinors = b.numMinors ∧
        (a.rules.length = b.rules.length ∧
          ∀ (i : Nat) x y, a.rules[i]? = some x → b.rules[i]? = some y → SameRule x y) ∧
        a.k = b.k ∧ a.isUnsafe = b.isUnsafe := by
  have unfolded : (a == b) = (a.toConstantVal == b.toConstantVal && (a.all == b.all &&
      (a.numParams == b.numParams && (a.numIndices == b.numIndices &&
      (a.numMotives == b.numMotives && (a.numMinors == b.numMinors && (a.rules == b.rules &&
      (a.k == b.k && a.isUnsafe == b.isUnsafe)))))))) := by
    cases a; cases b; rfl
  rw [unfolded]
  simp only [Bool.and_eq_true, constantVal_beq_iff,
    RegulaPolicy.Erasure.beq_iff_pointwise recursorRule_beq_iff, beq_iff_eq]

/-- The executed comparison accepts exactly the pairs that `Identical` relates. -/
theorem identical_iff (a b : ConstantInfo) : identical a b = true ↔ Identical a b := by
  cases a <;> cases b <;>
    simp only [identical, Identical, Bool.false_eq_true, axiomVal_beq_iff, definitionVal_beq_iff,
      theoremVal_beq_iff, opaqueVal_beq_iff, quotVal_beq_iff, inductiveVal_beq_iff,
      constructorVal_beq_iff, recursorVal_beq_iff]

/-- Whether every constant of module `m` is attributed to `m` in `env` and is the constant `env`
keeps under its name (`identical`). Lean's import attributes a name to the first module declaring
it and keeps the last copy that replaces the others (read from `Lean.finalizeImport`), so this
fails when another module of `env` declares a copy of one of `m`'s names that is not identical. -/
def uniquelyKept (env : Environment) (m : Name) : Bool := Id.run do
  let some owner := env.getModuleIdx? m | return false
  for info in env.header.moduleData[(owner : Nat)]!.constants do
    unless env.getModuleIdxFor? info.name == some owner do return false
    let some keptInfo := env.find? info.name | return false
    unless identical keptInfo info do return false
  return true

/-- Whether every constant a declaration of `m` refers to (`ConstantInfo.getUsedConstantsAsSet`,
the dependencies `Kernel.Environment.replay` replays first) is declared in a module of
`closure`. -/
def referencesWithin (env : Environment) (m : Name)
    (closure : Array RegulaPolicy.ModuleOrigin) : Bool := Id.run do
  let some owner := env.getModuleIdx? m | return false
  let allowed := closure.foldl (fun names origin => names.insert origin.name) ({} : NameSet)
  for info in env.header.moduleData[(owner : Nat)]!.constants do
    for used in info.getUsedConstantsAsSet do
      let some idx := env.getModuleIdxFor? used | return false
      unless allowed.contains env.header.modules[(idx : Nat)]!.module do return false
  return true


/-- Each prior with its admission's origins indexed by module name. -/
def indexPriors (priors : Array PriorAdmission) :
    Array (PriorAdmission × Std.HashMap Name RegulaPolicy.ModuleOrigin) :=
  priors.map fun prior => (prior, originIndex prior.origins)

/-- The import closure of `m` in the environment whose origins are `here`, when an `earlier`
admission offers `m` over the identical closure. -/
def offeredClosure
    (earlier : Array (PriorAdmission × Std.HashMap Name RegulaPolicy.ModuleOrigin))
    (here : Std.HashMap Name RegulaPolicy.ModuleOrigin) (m : Name) :
    Option (Array RegulaPolicy.ModuleOrigin) :=
  match importClosure here m with
  | none => none
  | some closure =>
      if earlier.any (fun entry =>
          entry.1.modules.contains m && importClosure entry.2 m == some closure)
      then some closure else none

/-- `offeredClosure` returns a closure exactly for a module that an earlier admission offers over
that same closure. -/
theorem offeredClosure_eq_some {earlier : Array (PriorAdmission × Std.HashMap Name
      RegulaPolicy.ModuleOrigin)} {here : Std.HashMap Name RegulaPolicy.ModuleOrigin}
    {m : Name} {closure : Array RegulaPolicy.ModuleOrigin} :
    offeredClosure earlier here m = some closure ↔
      importClosure here m = some closure ∧
      ∃ entry ∈ earlier, m ∈ entry.1.modules ∧ importClosure entry.2 m = some closure := by
  unfold offeredClosure
  cases hc : importClosure here m with
  | none => simp
  | some found =>
    simp only [Array.contains_eq_mem, Option.some.injEq, Array.any_eq_true', Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq]
    by_cases hany : ∃ entry ∈ earlier, m ∈ entry.1.modules ∧
        importClosure entry.2 m = some found
    · simp only [hany, ↓reduceIte, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨rfl, hany⟩
      · rintro ⟨rfl, -⟩; rfl
    · simp only [hany, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      rintro rfl
      exact hany

/-- Whether every `owned` module of the entry's closure is one of `names`. -/
def closureWithin (owned names : Std.HashSet Name)
    (entry : Name × Array RegulaPolicy.ModuleOrigin) : Bool :=
  entry.2.all fun origin => !owned.contains origin.name || names.contains origin.name

/-- `closureWithin` holds exactly when every `owned` module of the entry's closure is one of
`names`. -/
theorem closureWithin_iff {owned names : Std.HashSet Name}
    {entry : Name × Array RegulaPolicy.ModuleOrigin} :
    closureWithin owned names entry = true ↔
      ∀ origin ∈ entry.2, origin.name ∈ owned → origin.name ∈ names := by
  simp only [closureWithin, Array.all_eq_true', Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, Std.HashSet.mem_iff_contains]
  constructor
  · intro h origin horigin howned
    exact (h origin horigin).resolve_left (by simp [howned])
  · intro h origin horigin
    cases howned : owned.contains origin.name
    · exact .inl rfl
    · exact .inr (h origin horigin howned)

/-- The reuse candidates of `env`: each owned module that an earlier environment of the same
audit replayed and offers over the import closure the module has here (`offeredClosure`), whose
declarations refer only to constants of that closure (`referencesWithin`) and whose constants
are attributed to it and are the copies this environment keeps (`uniquelyKept`), with that
closure. -/
def candidates (env : Environment) (origins : Array RegulaPolicy.ModuleOrigin)
    (owned : Array Name) (priors : Array PriorAdmission) :
    Array (Name × Array RegulaPolicy.ModuleOrigin) :=
  let here := originIndex origins
  let earlier := indexPriors priors
  owned.filterMap fun m =>
    (offeredClosure earlier here m).bind fun closure =>
      if referencesWithin env m closure && uniquelyKept env m then some (m, closure) else none

/-- Every candidate is an owned module with the import closure it has here, which some prior
offers it over, whose declarations refer only to that closure and whose constants are uniquely
kept here. -/
theorem mem_candidates {env : Environment} {origins : Array RegulaPolicy.ModuleOrigin}
    {owned : Array Name} {priors : Array PriorAdmission}
    {entry : Name × Array RegulaPolicy.ModuleOrigin}
    (h : entry ∈ candidates env origins owned priors) :
    entry.1 ∈ owned ∧ importClosure (originIndex origins) entry.1 = some entry.2 ∧
      referencesWithin env entry.1 entry.2 = true ∧ uniquelyKept env entry.1 = true ∧
      ∃ prior ∈ priors, entry.1 ∈ prior.modules ∧
        importClosure (originIndex prior.origins) entry.1 = some entry.2 := by
  unfold candidates at h
  simp only at h
  obtain ⟨a, ha, hf⟩ := Array.mem_filterMap.mp h
  cases ho : offeredClosure (indexPriors priors) (originIndex origins) a with
  | none => simp [ho] at hf
  | some found =>
    simp only [ho, Option.bind_some] at hf
    split at hf
    · rename_i hrefs
      obtain ⟨hrefs, hunique⟩ := Bool.and_eq_true_iff.mp hrefs
      obtain rfl := Option.some.inj hf
      obtain ⟨hclosure, offering, hoffering, hm, hc⟩ := offeredClosure_eq_some.mp ho
      obtain ⟨prior, hprior, rfl⟩ := Array.mem_map.mp hoffering
      exact ⟨ha, hclosure, hrefs, hunique, prior, hprior, hm, hc⟩
    · simp at hf

/-- The owned modules of `env` whose kernel admission this environment reuses instead of
replaying: an earlier environment of the same audit replayed and offers each one over the
identical import closure (`offeredClosure`), every declaration of every owned module in that
closure refers only to constants of its own closure (`referencesWithin`), every constant of the
module is attributed to it and is the copy this environment keeps (`uniquelyKept`), and every
owned module the closure contains is reused too. The last condition removes each candidate
(`candidates`) whose closure contains an owned module that is not a candidate; the closure of
every owned module of a kept candidate's closure lies within that closure
(`importClosure_trans`), so that module is kept as well and one pass settles the set. Every other
owned module is replayed. A module of this environment's own request is reused under the same
conditions, which happens only when an earlier environment loaded it before its own did (claimed
libraries that import one another). `mem_reusedModules` states this contract. -/
def reusedModules (env : Environment) (origins : Array RegulaPolicy.ModuleOrigin)
    (owned : Array Name) (priors : Array PriorAdmission) : Array Name :=
  let settled := candidates env origins owned priors
  let ownedSet := Std.HashSet.ofList owned.toList
  (settled.filter
    (closureWithin ownedSet (Std.HashSet.ofList (settled.map (·.1)).toList))).map (·.1)

/-- Every reused module is an owned module that some prior offers over the import closure it has
here, whose declarations refer only to that closure, whose constants are uniquely kept here, and
whose closure's owned modules are all reused too, so reuse never leaves an owned import to
replay. -/
theorem mem_reusedModules {env : Environment} {origins : Array RegulaPolicy.ModuleOrigin}
    {owned : Array Name} {priors : Array PriorAdmission} {m : Name}
    (h : m ∈ reusedModules env origins owned priors) :
    m ∈ owned ∧ ∃ closure,
      importClosure (originIndex origins) m = some closure ∧
      referencesWithin env m closure = true ∧ uniquelyKept env m = true ∧
      (∃ prior ∈ priors, m ∈ prior.modules ∧
        importClosure (originIndex prior.origins) m = some closure) ∧
      ∀ origin ∈ closure, origin.name ∈ owned →
        origin.name ∈ reusedModules env origins owned priors := by
  unfold reusedModules at h ⊢
  simp only at h ⊢
  obtain ⟨entry, hkept, rfl⟩ := Array.mem_map.mp h
  obtain ⟨hsettled, hwithin⟩ := Array.mem_filter.mp hkept
  obtain ⟨ha, hclosure, hrefs, hunique, hprior⟩ := mem_candidates hsettled
  refine ⟨ha, entry.2, hclosure, hrefs, hunique, hprior, fun origin horigin howned => ?_⟩
  have hname := closureWithin_iff.mp hwithin origin horigin
    (Std.HashSet.mem_ofList.mpr (by simpa using howned))
  rw [Std.HashSet.mem_ofList, List.contains_iff_mem, Array.mem_toList_iff] at hname
  obtain ⟨other, hother, hotherName⟩ := Array.mem_map.mp hname
  refine Array.mem_map.mpr ⟨other, Array.mem_filter.mpr ⟨hother, ?_⟩, hotherName⟩
  obtain ⟨-, hotherClosure, -⟩ := mem_candidates hother
  simp only [hotherName] at hotherClosure
  exact closureWithin_iff.mpr fun inner hinner hinnerOwned =>
    closureWithin_iff.mp hwithin inner
      (importClosure_trans (originIndex_keyed origins) hclosure horigin hotherClosure inner
        hinner) hinnerOwned

/-- Whether a report's admission reused only what `priors` offered: each reused module is one a
prior offers over the import closure the report's own module origins give it, and each key the
receipt requires in a reused module (a module of the report's own request) is one such a prior
admitted. The priors offering a module over that closure are selected once, and their admitted
keys are collected only for a module the receipt requires a key in. -/
def reuseJustified (priors : Array PriorAdmission) (report : ProducerReport.Environment) :
    Bool :=
  let here := originIndex report.moduleOrigins
  let earlier := indexPriors priors
  match report.admission with
  | none => true
  | some receipt => receipt.reused.all fun m =>
      match importClosure here m with
      | none => false
      | some closure =>
        let offering := earlier.filter fun entry =>
          entry.1.modules.contains m && importClosure entry.2 m == some closure
        let keys := receipt.required.filter (·.1 == m)
        !offering.isEmpty && (keys.isEmpty ||
          let admitted := Std.HashSet.ofList (offering.flatMap (·.1.admitted)).toList
          keys.all admitted.contains)

/-- An accepted report reused only modules that some prior offers over the import closure the
report's own module origins give them, and every key its receipt requires in a reused module is
one that such a prior admitted. -/
theorem reuseJustified_sound {priors : Array PriorAdmission} {report : ProducerReport.Environment}
    (h : reuseJustified priors report = true) {receipt : ProducerReport.AdmissionReceipt}
    (hr : report.admission = some receipt) {m : Name} (hm : m ∈ receipt.reused) :
    ∃ closure, importClosure (originIndex report.moduleOrigins) m = some closure ∧
      (∃ prior ∈ priors, m ∈ prior.modules ∧
        importClosure (originIndex prior.origins) m = some closure) ∧
      ∀ key ∈ receipt.required, key.1 = m → ∃ prior ∈ priors, m ∈ prior.modules ∧
        importClosure (originIndex prior.origins) m = some closure ∧ key ∈ prior.admitted := by
  unfold reuseJustified at h
  simp only [hr, Array.all_eq_true'] at h
  have hmod := h m hm
  cases hc : importClosure (originIndex report.moduleOrigins) m with
  | none => simp [hc] at hmod
  | some closure =>
    simp only [hc, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
      at hmod
    obtain ⟨hoffering, hkeys⟩ := hmod
    have offered : ∀ entry ∈ (indexPriors priors).filter (fun entry =>
        entry.1.modules.contains m && importClosure entry.2 m == some closure),
        ∃ prior ∈ priors, entry.1 = prior ∧ m ∈ prior.modules ∧
          importClosure (originIndex prior.origins) m = some closure := by
      intro entry hentry
      obtain ⟨hentry, hoffers⟩ := Array.mem_filter.mp hentry
      obtain ⟨prior, hprior, rfl⟩ := Array.mem_map.mp hentry
      simp only [Bool.and_eq_true, Array.contains_eq_mem, decide_eq_true_eq, beq_iff_eq]
        at hoffers
      exact ⟨prior, hprior, rfl, hoffers.1, hoffers.2⟩
    obtain ⟨entry, hentry⟩ := Array.isEmpty_eq_false_iff_exists_mem.mp hoffering
    obtain ⟨prior, hprior, -, hmem, hsame⟩ := offered entry hentry
    refine ⟨closure, rfl, ⟨prior, hprior, hmem, hsame⟩, fun key hkey hkm => ?_⟩
    have hkeyOf : key ∈ receipt.required.filter (·.1 == m) :=
      Array.mem_filter.mpr ⟨hkey, beq_iff_eq.mpr hkm⟩
    rcases hkeys with hnone | hall
    · rw [Array.isEmpty_iff.mp hnone] at hkeyOf
      simp at hkeyOf
    · have hadmitted := Array.all_eq_true'.mp hall key hkeyOf
      rw [Std.HashSet.contains_ofList, List.contains_iff_mem, Array.mem_toList_iff] at hadmitted
      obtain ⟨entry, hentry, hadmitted⟩ := Array.mem_flatMap.mp hadmitted
      obtain ⟨prior, hprior, hsource, hmem, hsame⟩ := offered entry hentry
      exact ⟨prior, hprior, hmem, hsame, hsource ▸ hadmitted⟩

/-! ## What an environment offers the environments after it

Every environment of an audit reuses an earlier one's admission under one contract, a library's
and an executable's alike. The coordinator offers a completed admission only for a module that
admission replayed, outside its `shared` modules, whose own `.olean` and whose import closure's
owned modules load from artifacts frozen before the first inspection and read again, with the
frozen parts, when the offer is made (`Unchanged`, `currentOffers`). It accepts a report only
when everything the report reused was offered that way (`reuseJustified`) and every owned module
the report's environment loaded was replayed or reused there (`accountsFor`). -/

/-- A claimed library module's `.olean` parts, frozen before any environment is inspected. -/
structure FrozenArtifact where
  /-- The module. -/
  moduleName : Name
  /-- The canonical path of its `.olean` file. -/
  canonical : String
  /-- Its `.olean` path under the root package's output directory. -/
  path : System.FilePath
  /-- The bytes of each part Lean reads for the module, `none` for an absent part: the `.olean`,
  the `.olean.server` and the `.olean.private`. -/
  parts : Array (Option ByteArray)

/-- A later reading of a frozen artifact's parts; `none` when they could not be read. -/
abbrev Reading := FrozenArtifact × Option (Array (Option ByteArray))

/-- A frozen artifact with a later reading of its parts that is the frozen one: each of the
`.olean`, `.olean.server` and `.olean.private` present or absent as it was frozen, with the
frozen bytes. An offer is made only over values of this type (`frozenIndex`), so an artifact that
was not read again, or whose reading differs, cannot support one. -/
structure Unchanged where
  /-- The frozen artifact. -/
  artifact : FrozenArtifact
  /-- Its parts as read again. -/
  current : Array (Option ByteArray)
  /-- The reading is the frozen parts. -/
  same : current = artifact.parts

/-- The comparison of a reading with the frozen parts: the reading as an `Unchanged` artifact
exactly when it equals them. -/
def unchanged? (reading : Reading) : Option Unchanged :=
  match reading.2 with
  | some parts => if h : parts = reading.1.parts then some ⟨reading.1, parts, h⟩ else none
  | none => none

/-- `unchanged?` succeeds only on a reading that is its artifact's frozen parts. -/
theorem unchanged?_eq_some {reading : Reading} {found : Unchanged}
    (h : unchanged? reading = some found) :
    found.artifact = reading.1 ∧ reading.2 = some reading.1.parts := by
  unfold unchanged? at h
  split at h
  · rename_i parts hparts
    split at h
    · rename_i hsame
      obtain rfl := Option.some.inj h
      exact ⟨rfl, by rw [hparts, hsame]⟩
    · simp at h
  · simp at h

/-- `unchanged?` refuses a reading that is not its artifact's frozen parts. -/
theorem unchanged?_eq_none {reading : Reading} (h : reading.2 ≠ some reading.1.parts) :
    unchanged? reading = none := by
  cases hfound : unchanged? reading with
  | none => rfl
  | some found => exact absurd (unchanged?_eq_some hfound).2 h

/-- The artifacts whose readings are their frozen parts (`unchanged?`). -/
def unchangedOf (readings : Array Reading) : Array Unchanged :=
  readings.filterMap unchanged?

/-- Every artifact of `unchangedOf` was read with its frozen parts. -/
theorem mem_unchangedOf {readings : Array Reading} {found : Unchanged}
    (h : found ∈ unchangedOf readings) :
    (found.artifact, some found.artifact.parts) ∈ readings := by
  unfold unchangedOf at h
  obtain ⟨⟨artifact, current⟩, hmem, hsome⟩ := Array.mem_filterMap.mp h
  obtain ⟨hartifact, hparts⟩ := unchanged?_eq_some hsome
  simp only at hartifact hparts
  subst hartifact
  subst hparts
  exact hmem

/-- The canonical `.olean` path of each unchanged artifact's module. -/
def frozenIndex (artifacts : Array Unchanged) : Std.HashMap Name String :=
  artifacts.foldl (fun paths found =>
    paths.insert found.artifact.moduleName found.artifact.canonical) {}

/-- Every path of `frozenIndex` is the canonical path of an unchanged artifact of that module. -/
theorem frozenIndex_sound {artifacts : Array Unchanged} {m : Name} {path : String}
    (h : (frozenIndex artifacts)[m]? = some path) :
    ∃ found ∈ artifacts, found.artifact.moduleName = m ∧ found.artifact.canonical = path := by
  unfold frozenIndex at h
  rw [← Array.foldl_toList] at h
  suffices step : ∀ (rest : List Unchanged) (paths : Std.HashMap Name String),
      (rest.foldl (fun paths found =>
        paths.insert found.artifact.moduleName found.artifact.canonical) paths)[m]? = some path →
      paths[m]? = some path ∨
        ∃ found ∈ rest, found.artifact.moduleName = m ∧ found.artifact.canonical = path by
    rcases step artifacts.toList {} h with h | ⟨found, hmem, h⟩
    · simp at h
    · exact ⟨found, Array.mem_toList_iff.mp hmem, h⟩
  intro rest
  induction rest with
  | nil => intro paths h; exact .inl h
  | cons found rest ih =>
    intro paths h
    simp only [List.foldl_cons] at h
    rcases ih _ h with h | ⟨other, hmem, h⟩
    · rw [Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i heq
        exact .inr ⟨found, List.mem_cons_self, beq_iff_eq.mp heq, Option.some.inj h⟩
      · exact .inl h
    · exact .inr ⟨other, List.mem_cons_of_mem _ hmem, h⟩

/-- Every path the index of the unchanged readings holds for a module is the canonical path of
an artifact of that module whose reading was its frozen parts. -/
theorem frozenIndex_unchanged {readings : Array Reading} {m : Name} {path : String}
    (h : (frozenIndex (unchangedOf readings))[m]? = some path) :
    ∃ artifact, (artifact, some artifact.parts) ∈ readings ∧ artifact.moduleName = m ∧
      artifact.canonical = path := by
  obtain ⟨found, hfound, hname, hpath⟩ := frozenIndex_sound h
  exact ⟨found.artifact, mem_unchangedOf hfound, hname, hpath⟩

/-- A completed kernel admission as its environment publishes it for the environments after it:
the receipt and the origin of every module the environment loaded. -/
structure Completed where
  /-- The environment's admission receipt. -/
  receipt : ProducerReport.AdmissionReceipt
  /-- The name, canonical `.olean` path and direct imports of every module it loaded. -/
  origins : Array RegulaPolicy.ModuleOrigin
  deriving DecidableEq, ToJson

instance : FromJson Completed := ⟨fun j => do
  Regula.Checker.PolicyCodec.exactFields j ["receipt", "origins"]
  return { receipt := ← j.getObjValAs? _ "receipt", origins := ← j.getObjValAs? _ "origins" }⟩

/-- The completed admission a report records, when it has a receipt. -/
def Completed.ofReport (report : ProducerReport.Environment) : Option Completed :=
  report.admission.map fun receipt => { receipt, origins := report.moduleOrigins }

/-- Whether the environment whose origins are `index` loaded `m` from the canonical `.olean` path
`frozen` records for it, and every `owned` module of `m`'s import closure there from the path
`frozen` records for that module. -/
def frozenClosure (owned : NameSet) (frozen : Std.HashMap Name String)
    (index : Std.HashMap Name RegulaPolicy.ModuleOrigin) (m : Name) : Bool :=
  (match index[m]? with
    | some origin => frozen[m]? == some origin.olean
    | none => false) &&
  match importClosure index m with
  | none => false
  | some closure => closure.all fun origin =>
      !owned.contains origin.name || frozen[origin.name]? == some origin.olean

/-- `frozenClosure` holds only for a module loaded from its frozen path whose import closure
exists and loads every owned module from that module's frozen path. -/
theorem frozenClosure_sound {owned : NameSet} {frozen : Std.HashMap Name String}
    {index : Std.HashMap Name RegulaPolicy.ModuleOrigin} {m : Name}
    (h : frozenClosure owned frozen index m = true) :
    (∃ origin, index[m]? = some origin ∧ frozen[m]? = some origin.olean) ∧
    ∃ closure, importClosure index m = some closure ∧
      ∀ origin ∈ closure, owned.contains origin.name = true →
        frozen[origin.name]? = some origin.olean := by
  unfold frozenClosure at h
  obtain ⟨hself, hclosure⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨?_, ?_⟩
  · cases hi : index[m]? with
    | none => simp [hi] at hself
    | some origin => exact ⟨origin, rfl, by simpa [hi] using hself⟩
  · cases hc : importClosure index m with
    | none => simp [hc] at hclosure
    | some closure =>
      refine ⟨closure, rfl, fun origin horigin howned => ?_⟩
      simp only [hc, Array.all_eq_true', Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        beq_iff_eq] at hclosure
      exact (hclosure origin horigin).resolve_left (by simp [howned])

/-- What a completed admission offers the environments after it: the modules it replayed (its
receipt's `modules` outside `reused`), other than its `shared` ones (a copy of a name another
module also declares, whose admission depends on which copy an environment keeps), that it
loaded with their import closure from the frozen paths (`frozenClosure`), with the keys it
admitted in them. An admission that offers nothing is not handed on. -/
def offer (owned : NameSet) (frozen : Std.HashMap Name String) (completed : Completed) :
    Option PriorAdmission :=
  let index := originIndex completed.origins
  let offered := completed.receipt.modules.filter fun m =>
    !completed.receipt.shared.contains m && !completed.receipt.reused.contains m &&
      frozenClosure owned frozen index m
  if offered.isEmpty then none else
    let names := Std.HashSet.ofList offered.toList
    some {
      modules := offered
      admitted := completed.receipt.admitted.filter fun key => names.contains key.1
      origins := completed.origins }

/-- The offers of several completed admissions (`offer`). -/
def offers (owned : NameSet) (frozen : Std.HashMap Name String) (completed : Array Completed) :
    Array PriorAdmission :=
  completed.filterMap (offer owned frozen)

/-- Every offer comes from a completed admission whose module origins it carries: each offered
module is one that admission replayed, outside its `shared` and `reused` modules, over a frozen
import closure, and each offered key is one that admission admitted. -/
theorem mem_offers {owned : NameSet} {frozen : Std.HashMap Name String}
    {completed : Array Completed} {prior : PriorAdmission}
    (hp : prior ∈ offers owned frozen completed) :
    ∃ source ∈ completed, prior.origins = source.origins ∧
      (∀ key ∈ prior.admitted, key ∈ source.receipt.admitted) ∧
      ∀ m ∈ prior.modules, m ∈ source.receipt.modules ∧ m ∉ source.receipt.shared ∧
        m ∉ source.receipt.reused ∧
        frozenClosure owned frozen (originIndex source.origins) m = true := by
  unfold offers at hp
  obtain ⟨source, hsource, hoffer⟩ := Array.mem_filterMap.mp hp
  refine ⟨source, hsource, ?_⟩
  unfold offer at hoffer
  simp only at hoffer
  split at hoffer
  · simp at hoffer
  · obtain rfl := Option.some.inj hoffer
    refine ⟨rfl, fun key hkey => (Array.mem_filter.mp hkey).1, fun m hm => ?_⟩
    obtain ⟨hmem, hkeep⟩ := Array.mem_filter.mp hm
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Array.contains_eq_mem,
      decide_eq_false_iff_not] at hkeep
    exact ⟨hmem, hkeep.1.1, hkeep.1.2, hkeep.2⟩

/-- What the coordinator offers an environment as it starts: the offers of the `completed`
admissions over the artifacts whose `readings`, taken then, are their frozen parts. -/
def currentOffers (owned : NameSet) (readings : Array Reading) (completed : Array Completed) :
    Array PriorAdmission :=
  offers owned (frozenIndex (unchangedOf readings)) completed

/-- A report accepted against the current offers reused only modules that a completed admission
replayed, outside that admission's `shared` modules, over the import closure the report's own
module origins give them, where the module and every owned module of that closure load from the
canonical path of an artifact that was read again with its frozen parts. -/
theorem reuseJustified_frozen {owned : NameSet} {readings : Array Reading}
    {completed : Array Completed} {report : ProducerReport.Environment}
    (h : reuseJustified (currentOffers owned readings completed) report = true)
    {receipt : ProducerReport.AdmissionReceipt} (hr : report.admission = some receipt)
    {m : Name} (hm : m ∈ receipt.reused) :
    ∃ closure, importClosure (originIndex report.moduleOrigins) m = some closure ∧
      ∃ source ∈ completed, m ∈ source.receipt.modules ∧ m ∉ source.receipt.shared ∧
        m ∉ source.receipt.reused ∧
        importClosure (originIndex source.origins) m = some closure ∧
        (∃ artifact, (artifact, some artifact.parts) ∈ readings ∧ artifact.moduleName = m) ∧
        ∀ origin ∈ closure, owned.contains origin.name = true →
          ∃ artifact, (artifact, some artifact.parts) ∈ readings ∧
            artifact.moduleName = origin.name ∧ artifact.canonical = origin.olean := by
  obtain ⟨closure, hclosure, ⟨prior, hprior, hoffered, hsame⟩, _⟩ := reuseJustified_sound h hr hm
  obtain ⟨source, hsource, horigins, _, hmodules⟩ := mem_offers hprior
  obtain ⟨hreplayed, hshared, hreused, hfrozen⟩ := hmodules m hoffered
  obtain ⟨⟨origin, _, hself⟩, found, hfound, hall⟩ := frozenClosure_sound hfrozen
  rw [horigins] at hsame
  have hfound : found = closure := Option.some.inj (hfound.symm.trans hsame)
  rw [hfound] at hall
  obtain ⟨artifact, hartifact, hname, _⟩ := frozenIndex_unchanged hself
  exact ⟨closure, hclosure, source, hsource, hreplayed, hshared, hreused, hsame,
    ⟨artifact, hartifact, hname⟩, fun origin horigin howned =>
      frozenIndex_unchanged (hall origin horigin howned)⟩

/-- Every key an accepted report's receipt requires in a module it reused (a module of its own
request, whose declarations it reports without replaying them) is a key that a completed
admission admitted in a module that admission replayed. -/
theorem reuseJustified_admitted {owned : NameSet} {readings : Array Reading}
    {completed : Array Completed} {report : ProducerReport.Environment}
    (h : reuseJustified (currentOffers owned readings completed) report = true)
    {receipt : ProducerReport.AdmissionReceipt} (hr : report.admission = some receipt)
    {key : Name × Name} (hkey : key ∈ receipt.required) (hm : key.1 ∈ receipt.reused) :
    ∃ source ∈ completed, key.1 ∈ source.receipt.modules ∧ key.1 ∉ source.receipt.reused ∧
      key ∈ source.receipt.admitted := by
  obtain ⟨_, _, _, hkeys⟩ := reuseJustified_sound h hr hm
  obtain ⟨prior, hprior, hoffered, _, hadmitted⟩ := hkeys key hkey rfl
  obtain ⟨source, hsource, _, hadmit, hmodules⟩ := mem_offers hprior
  obtain ⟨hreplayed, _, hreused, _⟩ := hmodules key.1 hoffered
  exact ⟨source, hsource, hreplayed, hreused, hadmit key hadmitted⟩

/-- Whether the report's admission accounts for every `owned` module its environment loaded: the
receipt lists it as replayed there (`modules`) or as reused. -/
def accountsFor (owned : NameSet) (report : ProducerReport.Environment) : Bool :=
  match report.admission with
  | none => false
  | some receipt => report.modules.all fun m =>
      !owned.contains m || receipt.modules.contains m || receipt.reused.contains m

/-- No accepted report rests on an owned module that no environment replayed: every owned module
its environment loaded is in its own replay set (its receipt's `modules`), so that environment
replays it, or is one that a completed admission lists as replayed, not as reused, in an
environment that loaded it (it has an import closure there, which `importClosure` gives only for
a module with an origin). A receipt's `modules` alone does not show a replay: it lists every
owned module the environment did not reuse, whether or not it loaded the module. The modules the
environment owns (`owned`) need not be those the offers were made over (`offered`): the project
audit offers over every source-bound module and checks each report against the modules its own
environment owns. -/
theorem replayed_of_loaded {owned offered : NameSet} {readings : Array Reading}
    {completed : Array Completed} {report : ProducerReport.Environment}
    (hc : accountsFor owned report = true)
    (hj : reuseJustified (currentOffers offered readings completed) report = true)
    {m : Name} (hm : m ∈ report.modules) (ho : owned.contains m = true) :
    (∃ receipt, report.admission = some receipt ∧ m ∈ receipt.modules) ∨
      ∃ source ∈ completed, m ∈ source.receipt.modules ∧ m ∉ source.receipt.reused ∧
        ∃ closure, importClosure (originIndex source.origins) m = some closure := by
  unfold accountsFor at hc
  cases hr : report.admission with
  | none => simp [hr] at hc
  | some receipt =>
    simp only [hr, Array.all_eq_true', Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      Array.contains_eq_mem, decide_eq_true_eq] at hc
    rcases hc m hm with (hnot | hreplayed) | hreused
    · simp [ho] at hnot
    · exact .inl ⟨receipt, rfl, hreplayed⟩
    · obtain ⟨closure, _, source, hsource, hreplayed, _, hnotReused, hsame, _⟩ :=
        reuseJustified_frozen hj hr hreused
      exact .inr ⟨source, hsource, hreplayed, hnotReused, closure, hsame⟩

/-! ## Several copies of one name

Lean realizes some constants in the module that first needs them: equation, unfolding and
match-equation lemmas, functional induction and case principles, congruence and injectivity
lemmas. Two modules that do not import each other can each contain the same one, and Lean's
import (`Lean.finalizeImport`) keeps a single copy of the name when the two are theorems of the
same statement: `Environment.find?` returns the last one loaded, while the name stays attributed
to the first, whose own copy's precomputed axioms `collectAxioms` reports (or, where that
module did not export the name, the kept copy's, walked). The audited environment therefore
shows one copy, and `Kernel.Environment.replay` skips a theorem whose name it already holds with
that statement without checking its proof. Replay therefore reads each
replayed module's own constants, replays the copy `find?` returns under each name the replay base
lacks, and admits every other copy only under `sameTheorem` (`Regula.Checker.SharedName`) when it
is identical to the held constant or its own proof is checked, does not reach its own name, and
reaches exactly the held constant's axioms. -/

/-- A constant that a replayed module's own `.olean` data contains, with that module. -/
structure Copy where
  /-- The replayed module whose data contains the constant. -/
  «module» : Name
  /-- The constant as that module's data stores it. -/
  info : ConstantInfo

/-- The name the copy declares, which Lean's import and the kernel key it by. -/
abbrev Copy.name (copy : Copy) : Name := copy.info.name

/-! ### The replayed constants -/

/-- The constants replayed under their own names: every name of a copy that the replay base
`base` lacks, mapped to the constant the audited environment `kept` holds under it. That is the
copy `Environment.find?` returns (the last one loaded, `Lean.finalizeImport`), whose statement
and value reports read, so on these names the replayed kernel holds exactly the audited
environment's constants. -/
def replayMap (base kept : Name → Option ConstantInfo) (copies : Array Copy) :
    Std.HashMap Name ConstantInfo :=
  copies.foldl (init := {}) fun replay copy =>
    if (base copy.name).isSome then replay
    else match kept copy.name with
      | some info => replay.insert copy.name info
      | none => replay

/-- What `replayMap` maintains over the copies `seen` so far. -/
private structure ReplayMapInv (base kept : Name → Option ConstantInfo) (seen : List Copy)
    (replay : Std.HashMap Name ConstantInfo) : Prop where
  /-- Every entry is the kept constant of a name of a copy seen that the base lacks. -/
  sound : ∀ n info, replay[n]? = some info →
    base n = none ∧ kept n = some info ∧ ∃ c ∈ seen, c.name = n
  /-- Every copy seen whose name the base lacks has its name mapped to the kept constant. -/
  complete : ∀ c ∈ seen, base c.name = none → replay[c.name]? = kept c.name

/-- One step of `replayMap` keeps `ReplayMapInv`. -/
private theorem ReplayMapInv.step {base kept : Name → Option ConstantInfo} {seen : List Copy}
    {replay : Std.HashMap Name ConstantInfo} (h : ReplayMapInv base kept seen replay)
    (copy : Copy) :
    ReplayMapInv base kept (seen ++ [copy])
      (if (base copy.name).isSome then replay
       else match kept copy.name with
        | some info => replay.insert copy.name info
        | none => replay) := by
  have old : ∀ n info, replay[n]? = some info →
      base n = none ∧ kept n = some info ∧ ∃ c ∈ seen ++ [copy], c.name = n := by
    intro n info hr
    obtain ⟨h1, h2, c, hc, hcn⟩ := h.sound n info hr
    exact ⟨h1, h2, c, List.mem_append_left _ hc, hcn⟩
  by_cases hb : (base copy.name).isSome
  · simp only [hb, ↓reduceIte]
    refine ⟨old, fun c hc hbc => ?_⟩
    rcases List.mem_append.mp hc with hc | hc
    · exact h.complete c hc hbc
    · rw [List.mem_singleton.mp hc] at hbc
      simp [hbc] at hb
  · have hbn : base copy.name = none := Option.not_isSome_iff_eq_none.mp hb
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    cases hk : kept copy.name with
    | none =>
      refine ⟨old, fun c hc hbc => ?_⟩
      rcases List.mem_append.mp hc with hc | hc
      · exact h.complete c hc hbc
      · rw [List.mem_singleton.mp hc, hk]
        cases hr : replay[copy.name]? with
        | none => rfl
        | some info =>
          obtain ⟨-, h2, -⟩ := h.sound _ info hr
          rw [hk] at h2
          cases h2
    | some e =>
      refine ⟨fun n info hr => ?_, fun c hc hbc => ?_⟩
      · rw [Std.HashMap.getElem?_insert] at hr
        split at hr
        · rename_i heq
          have hn : copy.name = n := beq_iff_eq.mp heq
          obtain rfl := Option.some.inj hr
          subst hn
          exact ⟨hbn, hk, copy, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
        · exact old n info hr
      · rw [Std.HashMap.getElem?_insert]
        split
        · rename_i heq
          rw [← beq_iff_eq.mp heq, hk]
        · rename_i hne
          rcases List.mem_append.mp hc with hc | hc
          · exact h.complete c hc hbc
          · rw [List.mem_singleton.mp hc] at hne
            simp at hne

/-- `replayMap` satisfies `ReplayMapInv` over all copies. -/
private theorem replayMap_inv (base kept : Name → Option ConstantInfo) (copies : Array Copy) :
    ReplayMapInv base kept copies.toList (replayMap base kept copies) := by
  unfold replayMap
  rw [← Array.foldl_toList]
  suffices step : ∀ (rest seen : List Copy) (replay : Std.HashMap Name ConstantInfo),
      ReplayMapInv base kept seen replay →
      ReplayMapInv base kept (seen ++ rest) (rest.foldl (init := replay) fun replay copy =>
        if (base copy.name).isSome then replay
        else match kept copy.name with
          | some info => replay.insert copy.name info
          | none => replay) by
    simpa using step copies.toList [] {} ⟨by simp, by simp⟩
  intro rest
  induction rest with
  | nil => intro seen replay h; simpa using h
  | cons copy rest ih =>
    intro seen replay h
    simpa using ih (seen ++ [copy]) _ (h.step copy)

/-- Every replayed constant is the kept constant of a name of a copy that the base lacks. -/
theorem replayMap_sound {base kept : Name → Option ConstantInfo} {copies : Array Copy} {n : Name}
    {info : ConstantInfo} (h : (replayMap base kept copies)[n]? = some info) :
    base n = none ∧ kept n = some info ∧ ∃ c ∈ copies, c.name = n := by
  obtain ⟨h1, h2, c, hc, hcn⟩ := (replayMap_inv base kept copies).sound n info h
  exact ⟨h1, h2, c, Array.mem_toList_iff.mp hc, hcn⟩

/-- The name of every copy that the base lacks is replayed with its kept constant. -/
theorem replayMap_complete {base kept : Name → Option ConstantInfo} {copies : Array Copy}
    {copy : Copy} (hc : copy ∈ copies) (hb : base copy.name = none) :
    (replayMap base kept copies)[copy.name]? = kept copy.name :=
  (replayMap_inv base kept copies).complete copy (Array.mem_toList_iff.mpr hc) hb

/-- How many copies declare each name. -/
def nameCounts (copies : Array Copy) : Std.HashMap Name Nat :=
  copies.foldl (init := {}) fun counts copy =>
    counts.insert copy.name (counts.getD copy.name 0 + 1)

/-! ### The names a proof reaches

A copy that is not the constant the replayed kernel holds under its name is checked there under a
fresh name, where its own name still denotes the held constant. The search of
`KernelAxioms.reachSet` computes every name its proof reaches, through the types and values of the
constants it uses, so admission can refuse a proof that reaches its own name (a circular proof) or
axioms other than the held constant's. The axioms reported for a declaration are those it reaches
in the replayed kernel (`walkFind`, `KernelAxioms.axiomTable`), so replayed copies with the held
constant's axioms make that report right whichever of them a declaration used. -/

/-- The names of `seen` that `find` holds as axioms and `bound` lacks. -/
def extraAxioms (find : Name → Option ConstantInfo) (seen bound : Std.HashSet Name) : List Name :=
  seen.toList.filter fun a => isAxiomIn find a && !bound.contains a

/-- An empty `extraAxioms` puts every axiom of `seen` in `bound`. -/
theorem extraAxioms_nil {find : Name → Option ConstantInfo} {seen bound : Std.HashSet Name}
    (h : extraAxioms find seen bound = []) :
    ∀ a ∈ seen, isAxiomIn find a = true → a ∈ bound := by
  intro a ha hax
  have := List.filter_eq_nil_iff.mp h a (Std.HashSet.mem_toList.mpr ha)
  simp only [hax, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact Std.HashSet.mem_iff_contains.mpr (by simpa using this)

/-! ### Checking every copy -/

/-- Why a copy is not admitted; `subject` names the constant at fault. -/
inductive CopyFailure where
  /-- The replayed kernel or the audited environment holds no constant of the copy's name. -/
  | missing (copy : Copy)
  /-- The subject and the constant the replayed kernel holds under its name are not theorems
  Lean's import accepts together. -/
  | differs (subject : String)
  /-- The kernel rejected the subject, checked as the theorem `name`. -/
  | rejected (subject : String) (name : Name) (error : Kernel.Exception)
  /-- The subject's proof reaches its own name `name`, directly or through other constants. -/
  | circular (subject : String) (name : Name)
  /-- The subject's proof and the constant the replayed kernel holds under its name reach
  different axioms, the names `extra` reached by only one of them. -/
  | axioms (subject : String) (extra : List Name)
  /-- The search of the names the subject's proof reaches ran out of fuel. -/
  | exhausted (subject : String)

/-- The subject text of an owned copy. -/
def Copy.subject (copy : Copy) : String :=
  s!"owned declaration {copy.name} of module {copy.module}"

/-- The subject text of the constant the audited environment keeps under a copy's name. -/
def Copy.keptSubject (copy : Copy) : String :=
  s!"the constant {copy.name} that the audited environment keeps"

/-- The fresh name under which a theorem is checked while its own name denotes another copy. -/
def proofCheckName (n : Name) : Name := .num (.str n "regula_copy_proof") 0

/-- The kernel's theorem check of `info`, renamed to `proofCheckName`, in `checked`, with the zero
heartbeat and recursion limits `Kernel.Environment.replay` uses. -/
def checkRenamed (checked : Kernel.Environment) (subject : String) (info : ConstantInfo) :
    Except CopyFailure Unit := do
  let .thmInfo val := info | throw (.differs subject)
  match checked.addDeclCore 0 0 (.thmDecl { val with name := proofCheckName val.name }) none with
  | .ok _ => pure ()
  | .error error => throw (.rejected subject (proofCheckName val.name) error)

/-- The kernel accepted `info`, a theorem, renamed to `proofCheckName`, in `checked`. -/
def RenamedOK (checked : Kernel.Environment) (info : ConstantInfo) : Prop :=
  ∃ val, info = .thmInfo val ∧ ∃ env,
    checked.addDeclCore 0 0 (.thmDecl { val with name := proofCheckName val.name }) none = .ok env

/-- A successful `checkRenamed` is a kernel acceptance. -/
theorem checkRenamed_ok {checked : Kernel.Environment} {subject : String} {info : ConstantInfo}
    (h : checkRenamed checked subject info = .ok ()) : RenamedOK checked info := by
  unfold checkRenamed at h
  cases info with
  | thmInfo val =>
    refine ⟨val, rfl, ?_⟩
    simp only at h
    cases ha : checked.addDeclCore 0 0 (.thmDecl { val with name := proofCheckName val.name })
      none with
    | ok env => exact ⟨env, rfl⟩
    | error e => simp [ha] at h
  | _ => simp at h

/-- The proof of `info`, a copy of `name`, must be accepted by the kernel under a fresh name in
`checked`, must not reach `name` in `find`, and must reach in `find` exactly the axioms that `held`
reaches in `checked`. -/
def checkProof (checked : Kernel.Environment) (find : Name → Option ConstantInfo) (fuel : Nat)
    (subject : String) (name : Name) (held info : ConstantInfo) : Except CopyFailure Unit := do
  checkRenamed checked subject info
  let some seen := reachSet find fuel info | throw (.exhausted subject)
  if seen.contains name then throw (.circular subject name)
  let some bound := reachSet checked.find? fuel held | throw (.exhausted subject)
  let extra := extraAxioms find seen bound ++ extraAxioms checked.find? bound seen
  if !extra.isEmpty then throw (.axioms subject extra)

/-- What a successful `checkProof` establishes. -/
def ProofOK (checked : Kernel.Environment) (find : Name → Option ConstantInfo) (name : Name)
    (held info : ConstantInfo) : Prop :=
  RenamedOK checked info ∧ (∀ m ∈ successorsOf info, ¬ Reach (successors find) m name) ∧
    (∀ m ∈ successorsOf info, ∀ a, Reach (successors find) m a → IsAxiomIn find a →
      ∃ m' ∈ successorsOf held, Reach (successors checked.find?) m' a) ∧
    ∀ m' ∈ successorsOf held, ∀ a, Reach (successors checked.find?) m' a →
      IsAxiomIn checked.find? a → ∃ m ∈ successorsOf info, Reach (successors find) m a

/-- A successful `checkProof` gives `ProofOK`. -/
theorem checkProof_ok {checked : Kernel.Environment} {find : Name → Option ConstantInfo}
    {fuel : Nat} {subject : String} {name : Name} {held info : ConstantInfo}
    (h : checkProof checked find fuel subject name held info = .ok ()) :
    ProofOK checked find name held info := by
  unfold checkProof at h
  cases hr : checkRenamed checked subject info with
  | error e => simp [hr] at h
  | ok u =>
    cases u
    simp only [hr] at h
    cases hs : reachSet find fuel info with
    | none => simp [hs] at h
    | some seen =>
      simp only [hs] at h
      cases hc : seen.contains name
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
        cases hb : reachSet checked.find? fuel held with
        | none => simp [hb] at h
        | some bound =>
          simp only [hb] at h
          have hx : extraAxioms find seen bound = [] ∧
              extraAxioms checked.find? bound seen = [] := by
            cases hx : extraAxioms find seen bound ++ extraAxioms checked.find? bound seen with
            | nil => exact List.append_eq_nil_iff.mp hx
            | cons a rest => simp [hx] at h
          obtain ⟨complete, sound⟩ := reachSet_some hs
          obtain ⟨completeHeld, soundHeld⟩ := reachSet_some hb
          refine ⟨checkRenamed_ok hr, fun m hm hreach => ?_, fun m hm a ha hax => ?_,
            fun m hm a ha hax => ?_⟩
          · have := complete m hm _ hreach
            rw [Std.HashSet.mem_iff_contains, hc] at this
            cases this
          · exact soundHeld a (extraAxioms_nil hx.1 a (complete m hm a ha)
              ((isAxiomIn_iff _ _).mpr hax))
          · exact sound a (extraAxioms_nil hx.2 a (completeHeld m hm a ha)
              ((isAxiomIn_iff _ _).mpr hax))
      · simp [hc] at h

/-- A copy of a `shared` name and the constant `held` under it must be theorems Lean's import
accepts together. -/
def checkShared (shared : Copy → Bool) (held : ConstantInfo) (copy : Copy) :
    Except CopyFailure Unit :=
  if shared copy && !sameTheorem held copy.info then throw (.differs copy.subject) else pure ()

/-- A successful `checkShared` gives `sameTheorem` for a shared name. -/
theorem checkShared_ok {shared : Copy → Bool} {held : ConstantInfo} {copy : Copy}
    (h : checkShared shared held copy = .ok ()) (hs : shared copy = true) :
    sameTheorem held copy.info = true := by
  unfold checkShared at h
  cases hst : sameTheorem held copy.info
  · simp [hs, hst] at h
  · rfl

/-- A copy that is not the constant `held` must pass `checkProof` in the replayed kernel. -/
def checkOwn (checked : Kernel.Environment) (fuel : Nat) (held : ConstantInfo) (copy : Copy) :
    Except CopyFailure Unit :=
  if identical held copy.info then pure ()
  else checkProof checked checked.find? fuel copy.subject copy.name held copy.info

/-- A successful `checkOwn`: the copy is the held constant, or it passed `checkProof` in the
replayed kernel. -/
theorem checkOwn_ok {checked : Kernel.Environment} {fuel : Nat} {held : ConstantInfo}
    {copy : Copy} (h : checkOwn checked fuel held copy = .ok ()) :
    identical held copy.info = true ∨ ProofOK checked checked.find? copy.name held copy.info := by
  unfold checkOwn at h
  cases hi : identical held copy.info
  · simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
    exact .inr (checkProof_ok h)
  · exact .inl rfl

/-- When the audited environment's constant `keptInfo` of the copy's name is not `held`, it must
be a theorem Lean's import accepts beside `held` and pass `checkProof` in the audited environment
`kept`. -/
def checkKept (checked : Kernel.Environment) (kept : Name → Option ConstantInfo) (fuel : Nat)
    (held keptInfo : ConstantInfo) (copy : Copy) : Except CopyFailure Unit :=
  if identical held keptInfo then pure ()
  else do
    if !sameTheorem held keptInfo then throw (.differs copy.keptSubject)
    checkProof checked kept fuel copy.keptSubject copy.name held keptInfo

/-- A successful `checkKept`: the audited environment holds `held`, or a theorem Lean's import
accepts beside it that passed `checkProof` in the audited environment. -/
theorem checkKept_ok {checked : Kernel.Environment} {kept : Name → Option ConstantInfo}
    {fuel : Nat} {held keptInfo : ConstantInfo} {copy : Copy}
    (h : checkKept checked kept fuel held keptInfo copy = .ok ()) :
    identical held keptInfo = true ∨
      sameTheorem held keptInfo = true ∧ ProofOK checked kept copy.name held keptInfo := by
  unfold checkKept at h
  cases hi : identical held keptInfo
  · simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
    cases hst : sameTheorem held keptInfo
    · simp [hst] at h
    · simp only [hst, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      exact .inr ⟨rfl, checkProof_ok h⟩
  · exact .inl rfl

/-- Check one safe, total copy against the replayed kernel `checked` and the audited environment
`kept` (`checkShared`, `checkOwn`, `checkKept`, against the constant each holds under its name). -/
def checkSafeCopy (checked : Kernel.Environment) (kept : Name → Option ConstantInfo) (fuel : Nat)
    (shared : Copy → Bool) (copy : Copy) : Except CopyFailure Unit := do
  let some held := checked.find? copy.name | throw (.missing copy)
  let some keptInfo := kept copy.name | throw (.missing copy)
  checkShared shared held copy
  checkOwn checked fuel held copy
  checkKept checked kept fuel held keptInfo copy

/-- Check one copy. `Kernel.Environment.replay` does not check an `unsafe` or `partial` constant
and admission does not require one, so such a copy only must not share its name; every other
copy passes `checkSafeCopy`. -/
def checkCopy (checked : Kernel.Environment) (kept : Name → Option ConstantInfo) (fuel : Nat)
    (shared : Copy → Bool) (copy : Copy) : Except CopyFailure Unit :=
  if copy.info.isUnsafe || copy.info.isPartial then
    if shared copy then throw (.differs copy.subject) else pure ()
  else checkSafeCopy checked kept fuel shared copy

/-- What a successful `checkCopy` establishes for one copy. -/
def CopyAdmitted (checked : Kernel.Environment) (kept : Name → Option ConstantInfo)
    (shared : Copy → Bool) (copy : Copy) : Prop :=
  (copy.info.isUnsafe || copy.info.isPartial) = true ∧ shared copy = false ∨
  ∃ held keptInfo, checked.find? copy.name = some held ∧ kept copy.name = some keptInfo ∧
    (shared copy = true → SameTheorem held copy.info) ∧
    (Identical held copy.info ∨ ProofOK checked checked.find? copy.name held copy.info) ∧
    (Identical held keptInfo ∨
      SameTheorem held keptInfo ∧ ProofOK checked kept copy.name held keptInfo)

/-- A successful `checkCopy` admits its copy. -/
theorem checkCopy_ok {checked : Kernel.Environment} {kept : Name → Option ConstantInfo}
    {fuel : Nat} {shared : Copy → Bool} {copy : Copy}
    (h : checkCopy checked kept fuel shared copy = .ok ()) :
    CopyAdmitted checked kept shared copy := by
  unfold checkCopy at h
  cases hu : (copy.info.isUnsafe || copy.info.isPartial)
  · simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
    right
    unfold checkSafeCopy at h
    cases hh : checked.find? copy.name with
    | none => simp [hh] at h
    | some held =>
      cases hk : kept copy.name with
      | none => simp [hh, hk] at h
      | some keptInfo =>
        simp only [hh, hk] at h
        obtain ⟨⟨⟩, h1, h⟩ := RegulaPolicy.Guards.bind_eq_ok.mp h
        obtain ⟨⟨⟩, h2, h3⟩ := RegulaPolicy.Guards.bind_eq_ok.mp h
        exact ⟨held, keptInfo, rfl, rfl,
          fun isShared => (sameTheorem_iff _ _).mp (checkShared_ok h1 isShared),
          (checkOwn_ok h2).imp (identical_iff _ _).mp id,
          (checkKept_ok h3).imp (identical_iff _ _).mp (And.imp (sameTheorem_iff _ _).mp id)⟩
  · left
    refine ⟨hu, ?_⟩
    cases hs : shared copy
    · rfl
    · simp [hu, hs] at h

/-- Check every copy (`checkCopy`), stopping at the first refusal. -/
@[regula_decision]
def checkCopies (checked : Kernel.Environment) (kept : Name → Option ConstantInfo) (fuel : Nat)
    (shared : Copy → Bool) (copies : Array Copy) : Except CopyFailure Unit :=
  forM copies (checkCopy checked kept fuel shared)

/-- A successful `checkCopies` admits every copy. -/
theorem checkCopies_sound {checked : Kernel.Environment} {kept : Name → Option ConstantInfo}
    {fuel : Nat} {shared : Copy → Bool} {copies : Array Copy}
    (h : checkCopies checked kept fuel shared copies = .ok ()) :
    ∀ copy ∈ copies, CopyAdmitted checked kept shared copy :=
  fun copy hc => checkCopy_ok (forM_eq_ok.mp h copy hc)

/-- `checkCopies` is a sound decision (`checkCopies_sound`): when it succeeds, every copy is
admitted, and it succeeds for no copies, the accepted witness. The kind is one-way by design. A
refusal fails closed: the search for a proof's axioms is bounded by `fuel`, so `checkCopies` may
refuse copies that satisfy `CopyAdmitted`.

`checkProof` has `checkProof_ok` and no kind. Its only theorem is soundness, and a sound kind
requires an input it accepts; it succeeds only after `checkRenamed`, which asks Lean's kernel to
accept a declaration (`Kernel.Environment.addDeclCore`), and no proof evaluates that call. -/
theorem checked_checkCopies : Regula.ExecutableContract checkCopies (fun check =>
    Regula.DecidesSoundly (· = .ok ())
      (fun input : (((Kernel.Environment × (Name → Option ConstantInfo)) × Nat) ×
          (Copy → Bool)) × Array Copy =>
        ∀ copy ∈ input.2, CopyAdmitted input.1.1.1.1 input.1.1.1.2 input.1.2 copy)
      (Function.uncurry (Function.uncurry (Function.uncurry (Function.uncurry check))))) :=
  ⟨{ sound := fun _ accepted => checkCopies_sound accepted
     accepted := (inferInstance : Nonempty Kernel.Environment).elim fun checked =>
       ⟨((((checked, fun _ => none), 0), fun _ => false), #[]), rfl⟩ }⟩

/-- The detail of a copy failure. -/
def CopyFailure.describe : CopyFailure → IO String
  | .missing copy => pure s!"no constant {copy.name} of module {copy.module} after replay"
  | .differs subject => pure s!"{subject} shares its name with another constant of the replay \
      base, of a replayed module or of the audited environment, and the two are not theorems of \
      the same statement, universe parameters and mutual block, the only shared name admission \
      admits"
  | .rejected subject name error => do
    return s!"the kernel rejected {subject}, checked as {name} because another copy of that name \
      takes its place: {← (error.toMessageData {}).toString}"
  | .circular subject name => pure s!"{subject} has a proof that uses the name {name} itself, \
      directly or through other constants, while another copy of that name takes its place"
  | .axioms subject extra => pure s!"{subject} has a proof whose axioms differ from those of the \
      constant of its name in the replayed kernel, by {extra}, so a report of that name, which \
      shows one copy's axioms, would not show another's"
  | .exhausted subject => pure s!"the search of the names that the proof of {subject} reaches \
      did not finish"

/-- The tag of every kernel-admission failure detail. An admission failure leaves the affected
claim incomplete (RG2005), so the tag does not call it a violation. -/
def failureTag : String := "[INCOMPLETE[kernel-admission]]"

/-- The checker's infrastructure modules (`RegulaPolicy.infrastructureModuleNames`), which the
force-loaded reporter brings into every audited environment. An environment owns none of them,
so `replaySet` replays each one that imports a replayed module. -/
def reporterModules : Array Name :=
  RegulaPolicy.infrastructureModuleNames

/-- One pass over the `candidates`, adding each one that imports a module of `replay`. -/
def addReporters (candidates : Array (Name × ModuleData)) (replay : Array Name) : Array Name :=
  candidates.foldl (fun replay entry =>
    if !replay.contains entry.1 &&
        entry.2.imports.any (fun imp => replay.contains imp.module) then replay.push entry.1
    else replay) replay

/-- The modules `validate` replays in an environment that loaded `loaded`: every `owned` module
that is not `reused`, then every reporter module and every module of `checker`, the modules of
the owned dependencies under the checker's reserved prefixes that the environment does not own
(`EnvironmentOwnership.reporterOnly`), that imports one of them, directly or through other such
modules. Each pass over those candidates that changes the set adds one of them, so as many passes
as there are candidates reach every such importer. -/
def replaySet (loaded : Array (Name × ModuleData)) (owned reused : Array Name)
    (checker : Array Name := #[]) : Array Name :=
  let candidates := loaded.filter fun entry =>
    reporterModules.contains entry.1 || checker.contains entry.1
  (List.range candidates.size).foldl (fun replay _ => addReporters candidates replay)
    (owned.filter (!reused.contains ·))

/-- A pass of `addReporters` keeps every module already replayed. -/
private theorem mem_addReporters {loaded : Array (Name × ModuleData)} {replay : Array Name}
    {m : Name} (h : m ∈ replay) : m ∈ addReporters loaded replay := by
  unfold addReporters
  rw [← Array.foldl_toList]
  generalize loaded.toList = entries
  induction entries generalizing replay with
  | nil => simpa using h
  | cons entry rest ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact Array.mem_push_of_mem _ h
    · exact h

/-- Every owned module that is not reused is replayed. With `mem_reusedModules`, an owned module
is therefore kept out of the replay only under the reuse contract. -/
theorem mem_replaySet {loaded : Array (Name × ModuleData)} {owned reused checker : Array Name}
    {m : Name} (ho : m ∈ owned) (hr : m ∉ reused) : m ∈ replaySet loaded owned reused checker := by
  have start : m ∈ owned.filter (!reused.contains ·) := by
    simp [Array.mem_filter, Array.contains_eq_mem, ho, hr]
  have passes : ∀ (candidates : Array (Name × ModuleData)) (passes : List Nat)
      (replay : Array Name), m ∈ replay →
        m ∈ passes.foldl (fun replay _ => addReporters candidates replay) replay := by
    intro candidates passes
    induction passes with
    | nil => exact fun _ h => h
    | cons _ rest ih => exact fun _ h => ih _ (mem_addReporters h)
  exact passes _ _ _ start

/-- A changed import forces a replay: an owned module is replayed unless an offer covers it over
exactly the import closure it has here, that is, the same modules below it, loaded from the same
canonical `.olean` paths, with the same import edges (`importClosure`). -/
theorem replayed_unless_offered {env : Environment} {origins : Array RegulaPolicy.ModuleOrigin}
    {owned : Array Name} {priors : Array PriorAdmission}
    {loaded : Array (Name × ModuleData)} {checker : Array Name} {m : Name} (ho : m ∈ owned)
    (h : ∀ closure, importClosure (originIndex origins) m = some closure →
      ∀ prior ∈ priors, m ∈ prior.modules →
        importClosure (originIndex prior.origins) m ≠ some closure) :
    m ∈ replaySet loaded owned (reusedModules env origins owned priors) checker :=
  mem_replaySet ho fun hr => by
    obtain ⟨_, closure, hc, _, _, ⟨prior, hp, hm, hpc⟩, _⟩ := mem_reusedModules hr
    exact h closure hc prior hp hm hpc

/-- A changed `.olean`, `.olean.server` or `.olean.private` forces a replay: an owned module is
replayed when every reading of its artifact, taken as the environment starts, differs from the
frozen parts or failed (`Inspection.readings`), whatever was completed. -/
theorem replayed_of_changed {env : Environment} {origins : Array RegulaPolicy.ModuleOrigin}
    {owned : Array Name} {ownedSet : NameSet} {readings : Array Reading}
    {completed : Array Completed} {loaded : Array (Name × ModuleData)} {checker : Array Name}
    {m : Name}
    (ho : m ∈ owned)
    (h : ∀ reading ∈ readings, reading.1.moduleName = m → reading.2 ≠ some reading.1.parts) :
    m ∈ replaySet loaded owned (reusedModules env origins owned
      (currentOffers ownedSet readings completed)) checker :=
  mem_replaySet ho fun hr => by
    obtain ⟨_, _, _, _, _, ⟨prior, hp, hm, _⟩, _⟩ := mem_reusedModules hr
    obtain ⟨_, _, _, _, hmodules⟩ := mem_offers hp
    obtain ⟨⟨_, _, hself⟩, _⟩ := frozenClosure_sound (hmodules m hm).2.2.2
    obtain ⟨artifact, hartifact, hname, _⟩ := frozenIndex_unchanged hself
    exact h (artifact, some artifact.parts) hartifact hname rfl

/-- The same for an import: an owned module is replayed when every completed admission that
loaded it did so over an import closure with an owned module every reading of whose artifact
differs from the frozen parts or failed. -/
theorem replayed_of_changed_import {env : Environment}
    {origins : Array RegulaPolicy.ModuleOrigin} {owned : Array Name}
    {ownedSet : NameSet} {readings : Array Reading} {completed : Array Completed}
    {loaded : Array (Name × ModuleData)} {checker : Array Name} {m : Name} (ho : m ∈ owned)
    (h : ∀ source ∈ completed, ∀ closure,
      importClosure (originIndex source.origins) m = some closure →
      ∃ origin ∈ closure, ownedSet.contains origin.name = true ∧
        ∀ reading ∈ readings, reading.1.moduleName = origin.name →
          reading.2 ≠ some reading.1.parts) :
    m ∈ replaySet loaded owned (reusedModules env origins owned
      (currentOffers ownedSet readings completed)) checker :=
  mem_replaySet ho fun hr => by
    obtain ⟨_, _, _, _, _, ⟨prior, hp, hm, _⟩, _⟩ := mem_reusedModules hr
    obtain ⟨source, hsource, _, _, hmodules⟩ := mem_offers hp
    obtain ⟨_, closure, hclosure, hall⟩ := frozenClosure_sound (hmodules m hm).2.2.2
    obtain ⟨origin, horigin, howned, hchanged⟩ := h source hsource closure hclosure
    obtain ⟨artifact, hartifact, hname, _⟩ := frozenIndex_unchanged (hall origin horigin howned)
    exact hchanged (artifact, some artifact.parts) hartifact hname rfl

/-! ## The decisions of admission

`validate` is an observing pass around two pure decisions. `checkHeader` reads the module data of
the audited environment's header: each module that is replayed or reported lists its constants
under their own names, and no module of the replay base imports a replayed one. `admitReplay`
takes a header that `checkHeader` accepted and the kernel that the replay gave: it checks every
copy (`checkCopies`) and that the kernel holds a constant under the name of each required key,
without reading the module of the key, and it returns the receipt.
The copies, the required keys and the modules of the replay base are definitions of the header
(`ReplayRequest.copies`, `ReplayRequest.required`, `ReplayRequest.imports`). The import of the
replay base, the replay and the text of a failure are the pass. -/

/-- What admission reads from an audited environment: the modules of its header, the modules that `validate`
replays (`replaySet`), and the reused modules among the environment's requested modules that it
does not replay, whose keys the receipt requires. -/
structure ReplayRequest where
  /-- The modules of the audited environment's header with their data, in the order of the header
  (`EnvironmentHeader.moduleNames` beside `EnvironmentHeader.moduleData`). -/
  modules : Array (Name × ModuleData)
  /-- The modules that `validate` replays. -/
  replay : Array Name
  /-- The reused modules among the requested ones that are not replayed. -/
  reported : Array Name

/-- The copies that the replay checks: each constant of each replayed module's own data, with
that module. -/
def ReplayRequest.copies (request : ReplayRequest) : Array Copy :=
  request.modules.flatMap fun entry =>
    if request.replay.contains entry.1 then
      entry.2.constants.map fun info => { «module» := entry.1, info }
    else #[]

/-- The key of a copy that the receipt requires: a copy that is neither `unsafe` nor `partial`,
which `Kernel.Environment.replay` checks. -/
def requiredKey? (copy : Copy) : Option (Name × Name) :=
  if copy.info.isUnsafe || copy.info.isPartial then none else some (copy.module, copy.name)

/-- The keys of the reported modules: each constant of a reported module's own data that is
neither `unsafe` nor `partial`. -/
def ReplayRequest.referenced (request : ReplayRequest) : Array (Name × Name) :=
  request.modules.flatMap fun entry =>
    if !request.replay.contains entry.1 && request.reported.contains entry.1 then
      (entry.2.constants.filter fun info => !(info.isUnsafe || info.isPartial)).map
        fun info => (entry.1, info.name)
    else #[]

/-- The keys that the receipt requires: those of the copies, then those of the reported modules. -/
def ReplayRequest.required (request : ReplayRequest) : Array (Name × Name) :=
  request.copies.filterMap requiredKey? ++ request.referenced

/-- The modules of the replay base: each module that is not replayed, imported with all its data. -/
def ReplayRequest.imports (request : ReplayRequest) : Array Import :=
  request.modules.filterMap fun entry =>
    if request.replay.contains entry.1 then none else some { module := entry.1, importAll := true }

/-- The first place where the names listed for a module's constants and the constants differ:
the listed name and the constant. -/
def firstMislisted? : List Name → List ConstantInfo → Option (Name × ConstantInfo)
  | constName :: names, info :: infos =>
    if info.name == constName then firstMislisted? names infos else some (constName, info)
  | _, _ => none

/-- The listing of a module that admission reads: Lean's import keys each constant of the module
by the name listed beside it. -/
def checkListing (name : Name) (data : ModuleData) : Except String Unit := do
  unless data.constNames.size == data.constants.size do
    throw s!"{failureTag} module {name} lists {data.constNames.size} constant names for \
      {data.constants.size} constants"
  if let some (constName, info) := firstMislisted? data.constNames.toList data.constants.toList then
    throw s!"{failureTag} module {name} lists constant {info.name} under the name {constName}"

/-- A module of the replay base must not import a replayed module: importing it would put
unchecked owned declarations back in the trusted base. Ownership must be expanded or the claim
rejected. -/
def checkBase (replay : Array Name) (name : Name) (data : ModuleData) : Except String Unit :=
  if data.imports.any (fun imp => replay.contains imp.module) then
    throw s!"{failureTag} unreplayed module {name} imports a replayed module"
  else pure ()

/-- One module of the header: a replayed module has its listing checked; any other module has its
listing checked when it is reported, and then its imports. -/
def checkModule (replay reported : Array Name) (entry : Name × ModuleData) : Except String Unit :=
  if replay.contains entry.1 then checkListing entry.1 entry.2
  else do
    if reported.contains entry.1 then checkListing entry.1 entry.2
    checkBase replay entry.1 entry.2

/-- The decision on the header: each module in the order of the header (`checkModule`), stopping
at the first refusal. -/
@[regula_decision]
def checkHeader (request : ReplayRequest) : Except String Unit :=
  forM request.modules (checkModule request.replay request.reported)

/-- A module lists each of its constants under the constant's own name, as Lean's import keys
it. -/
def ListsOwnNames (data : ModuleData) : Prop :=
  data.constNames = data.constants.map ConstantInfo.name

/-- The header can be read for replay: each module that is replayed or reported lists its
constants under their own names, and no module that is not replayed imports a replayed one. -/
def HeaderOK (request : ReplayRequest) : Prop :=
  ∀ entry ∈ request.modules,
    (entry.1 ∈ request.replay ∨ entry.1 ∈ request.reported → ListsOwnNames entry.2) ∧
      (entry.1 ∉ request.replay → ∀ imp ∈ entry.2.imports, imp.module ∉ request.replay)

/-- `firstMislisted?` finds no difference exactly when the names are those of the constants, for
two lists of one length. -/
private theorem firstMislisted?_eq_none_iff :
    ∀ (names : List Name) (infos : List ConstantInfo), names.length = infos.length →
      (firstMislisted? names infos = none ↔ names = infos.map ConstantInfo.name)
  | [], [], _ => by simp [firstMislisted?]
  | [], _ :: _, same => by simp at same
  | _ :: _, [], same => by simp at same
  | constName :: names, info :: infos, same => by
    have rest := firstMislisted?_eq_none_iff names infos (by simpa using same)
    by_cases equal : info.name = constName
    · subst equal
      simp [firstMislisted?, rest]
    · have differs : (info.name == constName) = false := by simpa using equal
      simp only [firstMislisted?, differs, Bool.false_eq_true, ↓reduceIte, reduceCtorEq,
        false_iff, List.map_cons, List.cons.injEq, not_and]
      exact fun same => absurd same.symm equal

/-- `checkListing` accepts exactly a module that lists its constants under their own names. -/
theorem checkListing_eq_ok_iff (name : Name) (data : ModuleData) :
    checkListing name data = .ok () ↔ ListsOwnNames data := by
  unfold checkListing ListsOwnNames
  by_cases sized : data.constNames.size = data.constants.size
  · have none_iff := firstMislisted?_eq_none_iff data.constNames.toList data.constants.toList
      (by simpa using sized)
    have arrays : data.constNames = data.constants.map ConstantInfo.name ↔
        data.constNames.toList = data.constants.toList.map ConstantInfo.name := by
      rw [← Array.toList_map]
      exact ⟨fun h => by rw [h], fun h => Array.ext' h⟩
    rw [arrays, ← none_iff]
    cases found : firstMislisted? data.constNames.toList data.constants.toList with
    | none => simp [sized]
    | some pair => simp [sized]
  · have differ : ¬ data.constNames = data.constants.map ConstantInfo.name := fun same => by
      rw [same, Array.size_map] at sized
      exact sized rfl
    simp [sized, differ]

/-- `checkBase` accepts exactly a module that imports no replayed module. -/
theorem checkBase_eq_ok_iff (replay : Array Name) (name : Name) (data : ModuleData) :
    checkBase replay name data = .ok () ↔ ∀ imp ∈ data.imports, imp.module ∉ replay := by
  unfold checkBase
  by_cases found : data.imports.any (fun imp => replay.contains imp.module) = true
  · obtain ⟨imp, member, contained⟩ := Array.any_eq_true'.mp found
    simp only [found, ↓reduceIte]
    constructor
    · intro refused
      cases refused
    · intro none
      exact absurd (Array.contains_iff_mem.mp contained) (none imp member)
  · simp only [found, Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro _ imp member replayed
      exact found (Array.any_eq_true'.mpr ⟨imp, member, Array.contains_iff_mem.mpr replayed⟩)
    · intro _
      rfl

/-- `checkModule` accepts exactly a module that keeps the two conditions of `HeaderOK`. -/
theorem checkModule_eq_ok_iff (replay reported : Array Name) (entry : Name × ModuleData) :
    checkModule replay reported entry = .ok () ↔
      (entry.1 ∈ replay ∨ entry.1 ∈ reported → ListsOwnNames entry.2) ∧
        (entry.1 ∉ replay → ∀ imp ∈ entry.2.imports, imp.module ∉ replay) := by
  unfold checkModule
  by_cases replayed : entry.1 ∈ replay
  · simp [replayed, checkListing_eq_ok_iff]
  · have notContained : replay.contains entry.1 = false := by
      simpa [Array.contains_iff_mem] using replayed
    simp only [notContained, Bool.false_eq_true, ↓reduceIte, replayed, false_or, not_false_eq_true,
      forall_const]
    by_cases isReported : entry.1 ∈ reported
    · simp [isReported, checkListing_eq_ok_iff, checkBase_eq_ok_iff]
    · simp [isReported, checkBase_eq_ok_iff]

/-- **`checkHeader` accepts exactly a header that `HeaderOK` admits.** -/
theorem checkHeader_eq_ok_iff (request : ReplayRequest) :
    checkHeader request = .ok () ↔ HeaderOK request := by
  unfold checkHeader HeaderOK
  rw [RegulaPolicy.Guards.forM_eq_ok]
  exact forall₂_congr fun entry _ => checkModule_eq_ok_iff _ _ entry

/-- A module that lists the name `A` for no constant. -/
private def mislisted : ModuleData :=
  { isModule := false, imports := #[], constNames := #[`A], constants := #[],
    extraConstNames := #[], entries := #[] }

/-- `checkHeader` is a sound and complete decision of `HeaderOK` (`checkHeader_eq_ok_iff`). It
accepts the header of no module, and it refuses a header with a replayed module that lists a name
for no constant. -/
theorem checked_checkHeader : Regula.ExecutableContract checkHeader
    (Regula.Decides (· = .ok ()) HeaderOK) :=
  ⟨Regula.Decides.of_iff checkHeader_eq_ok_iff
    ⟨{ modules := #[], replay := #[], reported := #[] }, rfl⟩
    ⟨{ modules := #[(`A, mislisted)], replay := #[`A], reported := #[] }, fun accepted => by
      have listed := ((checkHeader_eq_ok_iff _).mp accepted (`A, mislisted) (by simp)).1
        (.inl (by simp))
      simp [ListsOwnNames, mislisted] at listed⟩⟩

/-- The keys that the receipt requires are the constants of the replayed and the reported modules
that are neither `unsafe` nor `partial`, one key for each module and constant. -/
theorem mem_required {request : ReplayRequest} {key : Name × Name} :
    key ∈ request.required ↔
      ∃ entry ∈ request.modules, (entry.1 ∈ request.replay ∨ entry.1 ∈ request.reported) ∧
        ∃ info ∈ entry.2.constants, info.isUnsafe = false ∧ info.isPartial = false ∧
          key = (entry.1, info.name) := by
  unfold ReplayRequest.required ReplayRequest.copies ReplayRequest.referenced
  simp only [Array.mem_append, Array.mem_filterMap, Array.mem_flatMap]
  constructor
  · rintro (⟨copy, ⟨entry, hentry, hcopy⟩, hkey⟩ | ⟨entry, hentry, hkey⟩)
    · by_cases replayed : request.replay.contains entry.1 = true
      · simp only [replayed, ↓reduceIte, Array.mem_map] at hcopy
        obtain ⟨info, hinfo, rfl⟩ := hcopy
        unfold requiredKey? at hkey
        by_cases unsafeOrPartial : (info.isUnsafe || info.isPartial) = true
        · simp [unsafeOrPartial] at hkey
        · simp only [unsafeOrPartial, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hkey
          simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at unsafeOrPartial
          exact ⟨entry, hentry, .inl (Array.contains_iff_mem.mp replayed), info, hinfo,
            unsafeOrPartial.1, unsafeOrPartial.2, hkey.symm⟩
      · simp only [replayed, Bool.false_eq_true, ↓reduceIte, Array.not_mem_empty] at hcopy
    · by_cases reported :
          (!request.replay.contains entry.1 && request.reported.contains entry.1) = true
      · simp only [reported, ↓reduceIte, Array.mem_map, Array.mem_filter] at hkey
        obtain ⟨info, ⟨hinfo, safe⟩, rfl⟩ := hkey
        simp only [Bool.not_or, Bool.and_eq_true, Bool.not_eq_true'] at safe
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at reported
        exact ⟨entry, hentry, .inr (Array.contains_iff_mem.mp reported.2), info, hinfo, safe.1,
          safe.2, rfl⟩
      · simp only [reported, Bool.false_eq_true, ↓reduceIte, Array.not_mem_empty] at hkey
  · rintro ⟨entry, hentry, which, info, hinfo, safe, total, rfl⟩
    by_cases replayed : entry.1 ∈ request.replay
    · refine .inl ⟨{ «module» := entry.1, info }, ⟨entry, hentry, ?_⟩, ?_⟩
      · simp [replayed, hinfo]
      · simp [requiredKey?, safe, total]
    · have reported : entry.1 ∈ request.reported := which.resolve_left replayed
      refine .inr ⟨entry, hentry, ?_⟩
      simp [replayed, reported]
      exact ⟨info, ⟨hinfo, safe, total⟩, rfl⟩

/-- Why `admitReplay` refuses. -/
inductive AdmitFailure where
  /-- A copy is not admitted. -/
  | copy (failure : CopyFailure)
  /-- The replayed kernel holds no constant of a required key's name. -/
  | missing (name : Name)

/-- What `admitReplay` reads: a header that `checkHeader` accepted, and the kernel that the replay
of its copies gave, with the audited environment's constants. The field `read` binds the request
to that acceptance, so no value of this type has a header that `checkHeader` refuses. -/
structure AdmitRequest where
  /-- The header and the modules that admission reads. -/
  request : ReplayRequest
  /-- `checkHeader` accepted the header. -/
  read : checkHeader request = .ok ()
  /-- The owned modules not replayed because an earlier environment admitted them. -/
  reused : Array Name
  /-- The kernel that the replay gave. -/
  checked : Kernel.Environment
  /-- The constants of the audited environment, by name. -/
  kept : Name → Option ConstantInfo
  /-- The bound of each search of the names that a proof reaches. -/
  fuel : Nat
  /-- The copies of a name that the replay base or another replayed module also declares. -/
  shared : Copy → Bool

/-- The receipt of an admission: the replayed modules, the required keys, admitted in the same
order, the reused modules and the replayed modules that contain a shared copy. -/
def AdmitRequest.receipt (admit : AdmitRequest) : ProducerReport.AdmissionReceipt :=
  { modules := RegulaPolicy.canonicalNames admit.request.replay
    required := admit.request.required
    admitted := admit.request.required
    reused := RegulaPolicy.canonicalNames admit.reused
    shared := RegulaPolicy.canonicalNames ((admit.request.copies.filter admit.shared).map (·.module)) }

/-- The decision of admission: every copy is checked (`checkCopies`), then the replayed kernel must
hold a constant under the name of each required key, without regard to the module of the key, and
the receipt is returned. -/
@[regula_decision]
def admitReplay (admit : AdmitRequest) : Except AdmitFailure ProducerReport.AdmissionReceipt := do
  if let .error failure :=
      checkCopies admit.checked admit.kept admit.fuel admit.shared admit.request.copies then
    throw (.copy failure)
  forM admit.request.required fun key =>
    if (admit.checked.find? key.2).isNone then throw (.missing key.2) else pure ()
  return admit.receipt

/-- What a receipt of `admitReplay` establishes: every copy is admitted (`CopyAdmitted`), and the
replayed kernel holds a constant under the name of each required key. -/
def AdmitOK (admit : AdmitRequest) : Prop :=
  (∀ copy ∈ admit.request.copies, CopyAdmitted admit.checked admit.kept admit.shared copy) ∧
    ∀ key ∈ admit.request.required, ∃ info, admit.checked.find? key.2 = some info

/-- **A receipt of `admitReplay` is the receipt of its request, and the request keeps
`AdmitOK`.** -/
theorem admitReplay_eq_ok {admit : AdmitRequest} {receipt : ProducerReport.AdmissionReceipt}
    (h : admitReplay admit = .ok receipt) : AdmitOK admit ∧ receipt = admit.receipt := by
  unfold admitReplay at h
  cases hc : checkCopies admit.checked admit.kept admit.fuel admit.shared
      admit.request.copies with
  | error failure => simp [hc] at h
  | ok u =>
    cases u
    simp only [hc] at h
    obtain ⟨⟨⟩, found, returned⟩ := RegulaPolicy.Guards.bind_eq_ok.mp h
    refine ⟨⟨checkCopies_sound hc, fun key member => ?_⟩, ?_⟩
    · have present := RegulaPolicy.Guards.forM_eq_ok.mp found key member
      cases hfind : admit.checked.find? key.2 with
      | none => simp [hfind] at present
      | some info => exact ⟨info, rfl⟩
    · cases returned
      rfl

/-- `admitReplay` is a sound decision of `AdmitOK` (`admitReplay_eq_ok`), and it accepts the
request of a header with no module. The kind is one-way, as for `checkCopies`: the search of a
proof's axioms is bounded by `fuel`, so a refusal fails closed. -/
theorem checked_admitReplay : Regula.ExecutableContract admitReplay
    (Regula.DecidesSoundly (fun result => result.isOk = true) AdmitOK) :=
  ⟨{ sound := fun admit accepted => by
       cases h : admitReplay admit with
       | error e => simp [h, Except.isOk, Except.toBool] at accepted
       | ok receipt => exact (admitReplay_eq_ok h).1
     accepted := (inferInstance : Nonempty Kernel.Environment).elim fun checked =>
       ⟨{ request := { modules := #[], replay := #[], reported := #[] }, read := rfl, reused := #[]
          checked, kept := fun _ => none, fuel := 0, shared := fun _ => false }, rfl⟩ }⟩

/-! ## The axioms of each owned declaration

The foundation rules decide on the axioms each owned declaration reaches in the replayed kernel
(`KernelAxioms.axiomTable` over `walkFind`), never on the axiom table `exportedAxiomsExt` that each
module writes when it is compiled and that Lean's `collectAxioms` reads first for a name an
imported module exported. Every step `collectAxioms` takes from a constant is a step of
`KernelAxioms.successors`, so on the constants a module was compiled from, every axiom its table
records for a declaration is reached in the replayed kernel too. A table that records an axiom the
replayed development does not reach therefore was not computed from the constants the kernel
checked, and admission refuses it (`checkTable`). A table may omit axioms that the replayed
development reaches: Lean's own computation of the table can stop early on an inductive type and
its constructors. The rules then decide on the replayed axioms, and the audit reports each axiom
the table omits for an owned declaration. -/

/-- The constants the search of each owned declaration's axioms reads: the replayed kernel's, and
under each name that `Kernel.Environment.replay` does not check, the `unsafe` or `partial` constant
that `replayed` maps it to, the one the audited environment keeps. A constant the replayed kernel
holds refers only to constants it holds, so the search from one of them reads the replayed kernel
alone. -/
def walkFind (checked : Kernel.Environment) (replayed : Std.HashMap Name ConstantInfo) (n : Name) :
    Option ConstantInfo :=
  match checked.find? n with
  | some info => some info
  | none => replayed[n]?.filter fun info => info.isUnsafe || info.isPartial

/-- The axioms that Lean's `collectAxioms` reports for `name` in `env`: for a name that an
imported module exported, those the module recorded when it was compiled. -/
def leanAxioms (env : Environment) (name : Name) : Array Name :=
  letI : MonadEnv (StateM Environment) := ⟨get, modify⟩
  (collectAxioms name : StateM Environment (Array Name)).run' env

/-- A declaration for which Lean's `collectAxioms` reports an axiom that its replayed development
does not reach: the declaration, the axioms `collectAxioms` reports and those it reaches in the
replayed kernel. -/
structure TableExcess where
  /-- The declaration. -/
  name : Name
  /-- The axioms Lean's `collectAxioms` reports for it (`leanAxioms`). -/
  lean : Array Name
  /-- The axioms it reaches in the replayed kernel (`KernelAxioms.ReachesAxiom`). -/
  replayed : Array Name

/-- The text of a `TableExcess`. -/
def TableExcess.describe (excess : TableExcess) : String :=
  s!"the axioms Lean's collectAxioms reports for {excess.name}, {excess.lean.toList}, include \
    one that its development in the replayed kernel does not reach; there it reaches \
    {excess.replayed.toList}"

/-- Every axiom Lean's `collectAxioms` reports for each declaration of `entries` (the second
component) is one the declaration reaches in the replayed kernel (the third). -/
def TableWithin (entries : Array (Name × Array Name × Array Name)) : Prop :=
  ∀ entry ∈ entries, ∀ a ∈ entry.2.1, a ∈ entry.2.2

/-- Refuse the first declaration for which Lean's `collectAxioms` reports an axiom outside those it
reaches in the replayed kernel. -/
@[regula_decision]
def checkTable (entries : Array (Name × Array Name × Array Name)) : Except TableExcess Unit :=
  forM entries fun (name, lean, replayed) =>
    if lean.all replayed.contains then pure () else throw ⟨name, lean, replayed⟩

/-- **`checkTable` accepts exactly the entries `TableWithin` admits.** -/
theorem checkTable_eq_ok_iff (entries : Array (Name × Array Name × Array Name)) :
    checkTable entries = .ok () ↔ TableWithin entries := by
  unfold checkTable TableWithin
  rw [RegulaPolicy.Guards.forM_eq_ok]
  refine forall₂_congr fun entry _ => ?_
  obtain ⟨name, lean, replayed⟩ := entry
  by_cases h : lean.all replayed.contains = true
  · simp only [h, ↓reduceIte]
    refine iff_of_true rfl fun a ha => ?_
    exact Array.contains_iff_mem.mp ((Array.all_eq_true'.mp h) a ha)
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    refine iff_of_false (fun hthrow => nomatch hthrow) fun within => ?_
    exact h (Array.all_eq_true'.mpr fun a ha => Array.contains_iff_mem.mpr (within a ha))

/-- `checkTable` is a sound and complete decision of `TableWithin` (`checkTable_eq_ok_iff`). It
accepts no entries, and it refuses a declaration with an axiom it does not reach. -/
theorem checked_checkTable : Regula.ExecutableContract checkTable
    (Regula.Decides (· = .ok ()) TableWithin) :=
  ⟨Regula.Decides.of_iff checkTable_eq_ok_iff ⟨#[], rfl⟩
    ⟨#[(`d, #[`a], #[])], fun accepted => by
      have := (checkTable_eq_ok_iff _).mp accepted (`d, #[`a], #[]) (by simp) `a (by simp)
      simp at this⟩⟩

/-- A completed kernel admission: its receipt, and what it computed in the replayed kernel, as the
audited environment names it (`Collect.Replayed`): the axioms each name of the owned declarations'
closure reaches there (`KernelAxioms.ReachesAxiom` over `walkFind`), which the foundation rules
decide on, and the axioms Lean's `collectAxioms` omits for an owned declaration, which the audit
reports. -/
structure Admitted where
  /-- The receipt of the admission. -/
  receipt : ProducerReport.AdmissionReceipt
  /-- The axioms of the closure and the omissions of the owned declarations. -/
  replayed : Regula.Collect.Replayed

/-- Replay the completed owned logical declarations against trusted imports, except those of
the `reused` modules, which stay in the replay base with the trusted imports (`replaySet`). This
is the observing pass of admission: `checkHeader` decides on the module data of the header, the
pass imports the replay base (`ReplayRequest.imports`) and replays every name of a copy that the
base lacks with the constant the audited environment `env` holds under it, the copy whose
statement and value reports read (`replayMap_sound`, `replayMap_complete`), and `admitReplay`
decides on the replayed kernel and returns the receipt (`admitReplay_eq_ok`). The copies are the
constants of each replayed module's own data (`ReplayRequest.copies`). The receipt's `shared`
modules contain a copy of a name that the base or another replayed module also declares; their
admission depends on which copy this environment keeps, so they are not offered for reuse. A
reused module among `requested` is one whose declarations this environment reports: the receipt
requires the key of each of its constants that is neither `unsafe` nor `partial`, read from the
module's own data as for a replayed module (`mem_required`), and the coordinator accepts those
keys only when the earlier environment that replayed the module admitted them
(`reuseJustified`). With the receipt, `validate` returns the axioms that each name of the closure of
the `ownedModules`' declarations (`Probe.ownedConstants`) reaches in the replayed kernel
(`KernelAxioms.axiomTable` over `walkFind`, `KernelAxioms.axiomTable_some`), after `checkTable`
admitted those of the owned declarations against the axioms Lean's `collectAxioms` reports, and,
for each owned declaration, the axioms `collectAxioms` omits. The original environment is retained
for compiler metadata only after replay succeeds. This is not a fresh replay of the imported dependency graph.
The modules of `checker`, those of the owned dependencies under the checker's reserved prefixes
that the environment does not own, are replayed only where one imports a replayed module
(`replaySet`). -/
unsafe def validate (env : Environment) (ownedModules : Array Name) (reused : Array Name := #[])
    (requested : Array Name := #[]) (checker : Array Name := #[]) :
    IO (Except ProducerReport.AdmissionFailure Admitted) := do
  -- The force-loaded reporter now depends on the positive policy library.
  -- Replay these exact checker implementation modules too; importing them into
  -- the base would reintroduce unchecked owned policy declarations. They do not
  -- become claimed surfaces, and arbitrary reverse imports remain forbidden.
  let modules := env.header.moduleNames.zip env.header.moduleData
  let replay := replaySet modules ownedModules reused checker
  let request : ReplayRequest :=
    { modules, replay
      reported := reused.filter fun name => requested.contains name && !replay.contains name }
  match read : checked_checkHeader.run request with
  | .error message => return .error ⟨message⟩
  | .ok () =>
    let counts := nameCounts request.copies
    -- Every search expands each name at most once; the audited environment declares no more
    -- names than its modules list constants.
    let fuel := env.header.moduleData.foldl (fun total data => total + data.constants.size) 0
    let base ← importModules request.imports {} 0 (loadExts := false) (level := .private)
    try
      let find := base.toKernelEnv.find?
      let shared (copy : Copy) : Bool := (find copy.name).isSome || 2 ≤ counts.getD copy.name 0
      let replayed := replayMap find env.find? request.copies
      let checked ← Lean.Kernel.Environment.replay replayed base.toKernelEnv
      match checked_admitReplay.run
          { request, read, reused, checked, kept := env.find?, fuel, shared } with
      | .ok receipt =>
        let roots := (Regula.Probe.ownedConstants env ownedModules.toList).map (·.1)
        let walk := walkFind checked replayed
        let some table := axiomTable walk (fuel + roots.size) roots
          | throw <| IO.userError "the search of the axioms that the owned declarations reach \
              in the replayed kernel ran out of fuel"
        -- The names the search found belong to the replay base's regions, which are released
        -- below, so each name is kept as the audited environment names it.
        let own (n : Name) : IO Name := match env.find? n with
          | some info => pure info.name
          | none => throw <| IO.userError s!"the constant {n} of the replayed kernel is not in \
              the audited environment"
        let mut axioms : Std.HashMap Name (Array Name) := {}
        for (n, reached) in table.toList do
          axioms := axioms.insert (← own n) (← reached.mapM own)
        let mut entries : Array (Name × Array Name × Array Name) := #[]
        let mut omissions : Std.HashMap Name (Array Name) := {}
        for root in roots do
          let some reached := axioms[root]?
            | throw <| IO.userError s!"no axioms were searched for {root} in the replayed kernel"
          let lean := leanAxioms env root
          entries := entries.push (root, lean, reached)
          let omitted := reached.filter fun a => !lean.contains a
          unless omitted.isEmpty do
            omissions := omissions.insert root omitted
        match checked_checkTable.run entries with
        | .ok () => return .ok { receipt, replayed := { axioms, omissions } }
        | .error excess => throw <| IO.userError excess.describe
      | .error (.copy failure) => throw <| IO.userError (← failure.describe)
      | .error (.missing name) => throw <| IO.userError s!"missing replayed declaration {name}"
    catch error =>
      return .error ⟨s!"{failureTag} {error}"⟩
    finally
      -- No replay environment escapes this function. Release its separately
      -- imported regions, as Lean's bundled replay checker does.
      base.freeRegions

end Regula.Checker.Admission
