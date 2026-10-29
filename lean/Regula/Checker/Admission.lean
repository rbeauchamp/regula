import Regula.Checker.ProducerReport
import Lean.Replay
import Regula.Probe
import Regula.Checker.SharedName
import Std.Data.HashMap.Lemmas
import Regula.Decision
import RegulaPolicy.KernelAxioms
import RegulaPolicy.Assumptions
import Regula.Assumption

/-!
# Checked logical admission

Checked logical admission before report construction. The replay base contains
only imported modules outside the replayed inventory. Unsafe and partial entries
remain subject to generated-role policy; they cannot supply logical evidence.
An owned module that an earlier environment of the same audit admitted over the
identical, frozen import closure is reused instead of replayed again (`reusedModules`,
`offers`, `reuseJustified_frozen`), also when another loaded module declares a copy of one of its
names, when the copies of each of its names agree (`agrees`, `copiesAgree`): every copy is
`Identical` to the kept constant, or `uniformUpToPrivate` and `declaredOwned` accept the name;
every other owned module is replayed (`mem_replaySet`). A
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

/-! ## Copies of one name in the loaded modules

Lean realizes some constants in the module that first needs them (equation, unfolding and
match-equation lemmas among them, see "Several copies of one name" below), so two loaded modules
can each declare the same name. Lean's import keeps one constant under the name and attributes the
name to the first module that lists it. One pass over the constants of every loaded module
(`duplicatesOf`) records each name some module declares with a constant that is not `identical`
to the kept one (`Duplicates.differing`) and, for each name, the modules that declare it other
than the module it is attributed to (`Duplicates.others`). For a name outside `differing`, every
copy is `Identical` to the kept constant (`Uniform`, `not_mem_differing_iff`), so which copy Lean
keeps, or which module it attributes the name to, changes the constant the kernel reads only up to
`Identical`. A name in `differing` can still have copies that agree up to exchanging names private
to the modules that declare it, in the narrow class that `UniformUpToPrivate` (below) admits, when
only owned modules declare it (`DeclaredOwned`). Reuse
rests on names whose copies agree in one of these two ways (`agrees`, `copiesAgree`,
`referencesWithin`), and so does the offer of a replayed module that holds a copy of one
(`ownedAgrees`). What these rest on about Lean is listed under `Assumes:` in the docstrings of
`duplicatesIn`, `renamedCopy` and `copiesAgree`. -/

/-- What `duplicatesOf` finds in the constants of the loaded modules. -/
structure Duplicates where
  /-- Each name that a loaded module declares with a constant not `identical` to the constant the
  environment keeps under it, or under which the environment keeps none. -/
  differing : Std.HashSet Name
  /-- For each name, the index of each loaded module that declares it, other than the module the
  name is attributed to. -/
  others : Std.HashMap Name (Array Nat)

/-- No name differs, and no name has a module beside the one it is attributed to. -/
def Duplicates.empty : Duplicates := { differing := {}, others := {} }

/-- Record the constant `info` of the module at index `idx`: its name is `differing` unless `find`
keeps a constant `identical` to it, and `idx` joins the name's `others` unless the name is
attributed to `idx`. -/
def Duplicates.record (find : Name → Option ConstantInfo) (attributed : Name → Option Nat)
    (idx : Nat) (dups : Duplicates) (info : ConstantInfo) : Duplicates :=
  { differing :=
      if (find info.name).any (identical · info) then dups.differing
      else dups.differing.insert info.name
    others :=
      if attributed info.name == some idx then dups.others
      else dups.others.insert info.name ((dups.others.getD info.name #[]).push idx) }

/-- One pass over the constants of every module of `modules`, the loaded modules' data at their
indices (`Duplicates.record`). `find` gives the constant the environment keeps under a name and
`attributed` the index of the module it attributes the name to. -/
def duplicatesOf (find : Name → Option ConstantInfo) (attributed : Name → Option Nat)
    (modules : Array ModuleData) : Duplicates :=
  modules.zipIdx.foldl (init := Duplicates.empty) fun dups entry =>
    entry.1.constants.foldl (Duplicates.record find attributed entry.2) dups

/-- The module at index `idx` of `modules` declares a constant named `n`. -/
def Declares (modules : Array ModuleData) (idx : Nat) (n : Name) : Prop :=
  ∃ data, modules[idx]? = some data ∧ ∃ info ∈ data.constants, info.name = n

/-- Every copy of `n` that a module of `modules` declares is `Identical` to the constant `find`
keeps under `n`. -/
def Uniform (find : Name → Option ConstantInfo) (modules : Array ModuleData) (n : Name) : Prop :=
  ∀ data ∈ modules, ∀ info ∈ data.constants, info.name = n →
    ∃ kept, find n = some kept ∧ Identical kept info

/-- What `duplicatesOf` maintains over the copies `seen` so far, each with its module's index. -/
private structure DuplicatesInv (find : Name → Option ConstantInfo)
    (attributed : Name → Option Nat) (seen : List (ConstantInfo × Nat)) (dups : Duplicates) :
    Prop where
  /-- A name differs exactly when a copy seen is not `identical` to the kept constant. -/
  differing : ∀ n, n ∈ dups.differing ↔
    ∃ copy ∈ seen, copy.1.name = n ∧ (find n).any (identical · copy.1) = false
  /-- A module is among a name's `others` exactly when it holds a copy seen and is not the module
  the name is attributed to. -/
  others : ∀ n idx, idx ∈ dups.others.getD n #[] ↔
    ∃ copy ∈ seen, copy.2 = idx ∧ copy.1.name = n ∧ attributed n ≠ some idx

/-- `Duplicates.record` keeps `DuplicatesInv`. -/
private theorem DuplicatesInv.record {find : Name → Option ConstantInfo}
    {attributed : Name → Option Nat} {seen : List (ConstantInfo × Nat)} {dups : Duplicates}
    (h : DuplicatesInv find attributed seen dups) (idx : Nat) (info : ConstantInfo) :
    DuplicatesInv find attributed (seen ++ [(info, idx)])
      (Duplicates.record find attributed idx dups info) := by
  refine ⟨fun n => ?_, fun n other => ?_⟩
  · simp only [Duplicates.record, List.mem_append, List.mem_singleton]
    by_cases hkept : (find info.name).any (identical · info) = true
    · simp only [hkept, ↓reduceIte, h.differing n]
      constructor
      · rintro ⟨copy, hcopy, hname, hany⟩
        exact ⟨copy, .inl hcopy, hname, hany⟩
      · rintro ⟨copy, hcopy | rfl, hname, hany⟩
        · exact ⟨copy, hcopy, hname, hany⟩
        · subst hname
          rw [hkept] at hany
          cases hany
    · simp only [hkept, Bool.false_eq_true, ↓reduceIte, Std.HashSet.mem_insert, beq_iff_eq,
        h.differing n]
      constructor
      · rintro (rfl | ⟨copy, hcopy, hname, hany⟩)
        · exact ⟨(info, idx), .inr rfl, rfl, by simpa using hkept⟩
        · exact ⟨copy, .inl hcopy, hname, hany⟩
      · rintro ⟨copy, hcopy | rfl, hname, hany⟩
        · exact .inr ⟨copy, hcopy, hname, hany⟩
        · exact .inl hname
  · simp only [Duplicates.record, List.mem_append, List.mem_singleton]
    by_cases hattr : (attributed info.name == some idx) = true
    · have hidx : attributed info.name = some idx := beq_iff_eq.mp hattr
      simp only [hattr, ↓reduceIte, h.others n other]
      constructor
      · rintro ⟨copy, hcopy, hidx', hname, hne⟩
        exact ⟨copy, .inl hcopy, hidx', hname, hne⟩
      · rintro ⟨copy, hcopy | rfl, hidx', hname, hne⟩
        · exact ⟨copy, hcopy, hidx', hname, hne⟩
        · simp only at hidx' hname
          subst hidx' hname
          exact absurd hidx hne
    · have hne : attributed info.name ≠ some idx := fun heq => hattr (beq_iff_eq.mpr heq)
      simp only [hattr, Bool.false_eq_true, ↓reduceIte, Std.HashMap.getD_insert, beq_iff_eq]
      by_cases hname : info.name = n
      · subst hname
        simp only [↓reduceIte, Array.mem_push, h.others info.name other]
        constructor
        · rintro (⟨copy, hcopy, hidx', hname', hne'⟩ | heq)
          · exact ⟨copy, .inl hcopy, hidx', hname', hne'⟩
          · exact ⟨(info, idx), .inr rfl, heq.symm, rfl, by rw [heq]; exact hne⟩
        · rintro ⟨copy, hcopy | rfl, hidx', hname', hne'⟩
          · exact .inl ⟨copy, hcopy, hidx', hname', hne'⟩
          · exact .inr hidx'.symm
      · simp only [hname, ↓reduceIte, h.others n other]
        constructor
        · rintro ⟨copy, hcopy, hidx', hname', hne'⟩
          exact ⟨copy, .inl hcopy, hidx', hname', hne'⟩
        · rintro ⟨copy, hcopy | rfl, hidx', hname', hne'⟩
          · exact ⟨copy, hcopy, hidx', hname', hne'⟩
          · exact absurd hname' hname

/-- The pass over all modules keeps `DuplicatesInv` over every copy, each with its module's
index. -/
private theorem duplicatesOf_inv (find : Name → Option ConstantInfo)
    (attributed : Name → Option Nat) (modules : Array ModuleData) :
    DuplicatesInv find attributed
      (modules.zipIdx.toList.flatMap fun entry => entry.1.constants.toList.map (·, entry.2))
      (duplicatesOf find attributed modules) := by
  have inner : ∀ (idx : Nat) (infos : List ConstantInfo) (seen : List (ConstantInfo × Nat))
      (dups : Duplicates), DuplicatesInv find attributed seen dups →
      DuplicatesInv find attributed (seen ++ infos.map (·, idx))
        (infos.foldl (Duplicates.record find attributed idx) dups) := by
    intro idx infos
    induction infos with
    | nil => intro seen dups h; simpa using h
    | cons info rest ih =>
      intro seen dups h
      simpa using ih _ _ (h.record idx info)
  have outer : ∀ (entries : List (ModuleData × Nat)) (seen : List (ConstantInfo × Nat))
      (dups : Duplicates), DuplicatesInv find attributed seen dups →
      DuplicatesInv find attributed
        (seen ++ entries.flatMap fun entry => entry.1.constants.toList.map (·, entry.2))
        (entries.foldl (fun dups entry =>
          entry.1.constants.foldl (Duplicates.record find attributed entry.2) dups) dups) := by
    intro entries
    induction entries with
    | nil => intro seen dups h; simpa using h
    | cons entry rest ih =>
      intro seen dups h
      have step := inner entry.2 entry.1.constants.toList seen dups h
      rw [Array.foldl_toList] at step
      simpa using ih _ _ step
  have start : DuplicatesInv find attributed [] Duplicates.empty :=
    ⟨fun n => by simp [Duplicates.empty], fun n idx => by simp [Duplicates.empty]⟩
  unfold duplicatesOf
  rw [← Array.foldl_toList]
  simpa using outer modules.zipIdx.toList [] _ start

/-- The copies the pass sees are exactly the constants of the modules, each with its module's
index. -/
private theorem mem_copies {modules : Array ModuleData} {info : ConstantInfo} {idx : Nat} :
    (info, idx) ∈ (modules.zipIdx.toList.flatMap fun entry =>
        entry.1.constants.toList.map (·, entry.2)) ↔
      ∃ data, modules[idx]? = some data ∧ info ∈ data.constants := by
  simp only [List.mem_flatMap, List.mem_map, Array.mem_toList_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨entry, hentry, found, hfound, rfl, rfl⟩
    exact ⟨entry.1, Array.mem_zipIdx_iff_getElem?.mp hentry, hfound⟩
  · rintro ⟨data, hdata, hinfo⟩
    exact ⟨(data, idx), Array.mem_zipIdx_iff_getElem?.mpr hdata, info, hinfo, rfl, rfl⟩

/-- **A name is outside `differing` exactly when every copy of it is `Identical` to the kept
constant.** -/
theorem not_mem_differing_iff {find : Name → Option ConstantInfo}
    {attributed : Name → Option Nat} {modules : Array ModuleData} {n : Name} :
    n ∉ (duplicatesOf find attributed modules).differing ↔ Uniform find modules n := by
  rw [(duplicatesOf_inv find attributed modules).differing n]
  constructor
  · intro hnone data hdata info hinfo hname
    obtain ⟨idx, hidx⟩ := Array.mem_iff_getElem?.mp hdata
    cases hkept : (find n).any (identical · info)
    · exact absurd ⟨(info, idx), mem_copies.mpr ⟨data, hidx, hinfo⟩, hname, hkept⟩ hnone
    · obtain ⟨kept, hfind, hsame⟩ := (Option.any_eq_true _ _).mp hkept
      exact ⟨kept, hfind, (identical_iff _ _).mp hsame⟩
  · rintro huniform ⟨⟨info, idx⟩, hcopy, hname, hkept⟩
    obtain ⟨data, hidx, hinfo⟩ := mem_copies.mp hcopy
    obtain ⟨kept, hfind, hsame⟩ :=
      huniform data (Array.mem_of_getElem? hidx) info hinfo hname
    simp only at hname hkept
    subst hname
    rw [hfind] at hkept
    simp [(identical_iff _ _).mpr hsame] at hkept

/-- **A module is among a name's `others` exactly when it declares the name and is not the module
the name is attributed to.** -/
theorem mem_others_iff {find : Name → Option ConstantInfo} {attributed : Name → Option Nat}
    {modules : Array ModuleData} {n : Name} {idx : Nat} :
    idx ∈ (duplicatesOf find attributed modules).others.getD n #[] ↔
      Declares modules idx n ∧ attributed n ≠ some idx := by
  rw [(duplicatesOf_inv find attributed modules).others n idx]
  constructor
  · rintro ⟨⟨info, idx'⟩, hcopy, hidx, hname, hne⟩
    simp only at hidx hname
    subst hidx
    obtain ⟨data, hdata, hinfo⟩ := mem_copies.mp hcopy
    exact ⟨⟨data, hdata, info, hinfo, hname⟩, hne⟩
  · rintro ⟨⟨data, hdata, info, hinfo, hname⟩, hne⟩
    exact ⟨(info, idx), mem_copies.mpr ⟨data, hdata, hinfo⟩, rfl, hname, hne⟩

/-- The index of the module `env` attributes each name to (`Environment.getModuleIdxFor?`). -/
def attributedIn (env : Environment) (n : Name) : Option Nat :=
  (env.getModuleIdxFor? n).map ModuleIdx.toNat

/-- The index of the module `m` in `env` (`Environment.getModuleIdx?`). -/
def ownerIn (env : Environment) (m : Name) : Option Nat :=
  (env.getModuleIdx? m).map ModuleIdx.toNat

/-- The copies of each name in the modules `env` loaded (`duplicatesOf`), read from the module
data of its header, its constant under each name and its attribution of each name.

Assumes:
- Lean v4.35.0, `src/lean/Lean/Environment.lean:155-160` and `179-183`: the index of a module in
  `EnvironmentHeader.modules`, and so in `moduleNames`, is its `ModuleIdx`; `finalizeImport`
  builds `moduleData` from the same array of modules (`2313-2317`) and records both in the header
  (`2369-2371`), so `env.header.moduleData` holds at each index the data of the module
  `getModuleIdx?` gives that index.
- Lean v4.35.0, `src/lean/Lean/Environment.lean:2333-2348` (`finalizeImport`): for each constant
  of each loaded module, in the order of the module indices, the import keeps under its name one
  of the copies it read (the first, replaced by a later one that `subsumesInfo` accepts over it),
  which `Environment.find?` returns, and attributes the name to the first module whose constants
  or `extraConstNames` list it (`const2ModIdx.insertIfNew`), which `getModuleIdxFor?` returns. -/
def duplicatesIn (env : Environment) : Duplicates :=
  duplicatesOf env.find? (attributedIn env) env.header.moduleData

/-! ### Copies renamed between the private constants of two modules

Lean gives the match equations and the splitter it realizes for a definition's `match` names
private to the module that realizes them (`Lean.Meta.Match.getEquationsForImpl`), and the equation
lemma it realizes in that module refers to them. Two modules that each realize `f.eq_2` for one `f`
therefore hold copies of it whose proofs differ in which module's private match equation they use,
and the name is `differing`. `renamedCopy` relates such a copy to the copy of the module the name is
attributed to under the conditions that follow. The two are theorems Lean's import accepts
together (`sameTheorem`), and the copy refers to no name private to the other module and turns
into a constant `Identical` to the other when the names private to its module are renamed to the
same names private to the other module (`renamedTo`). The names private to the copy's module that
the copy refers to, with every name private to that module linked to them by a reference
(`blockOf`), must each be `renameable`: declared by the copy's module alone and attributed to it,
free of a role and uniform under both names, and a theorem or a safe definition that `renamedTo`
renames into the other module's constant under the renamed name. Only the copies of the name and
these names, with their renamed names, may refer to them or to their renamed names, and none of
them may reach the name. The name itself must lie on no cycle, and no constant that reaches it may
reach `Lean.reduceBool` or `Lean.reduceNat` or be one of `kernelNames` (`uniformUpToPrivate`).
The copies of a name agree (`agrees`, `agrees_iff`) when the name is outside `differing`, or when
`UniformUpToPrivate` admits it and only owned modules declare it (`DeclaredOwned`); the three
decisions of reuse read that (`copiesAgree`, `referencesWithin`, `ownedAgrees`). `agrees` reads
the references backward only from the constants of the region of the owned modules (`regionOf`,
`linksOf`), and forward in one search from the names that pass the tests over the region and the
names that reach them (`nativeReaching`). `agrees_iff` holds when the modules outside the owned
ones meet `ImportScoped`. The docstring of `renamedCopy` argues why reuse gives the same results
for renamed copies as for identical ones. The `#guard` witnesses after `fixedIn_iff` run `agrees`
on module data with and without each of four exclusions: native reduction, also through a module
that is not owned and imports an owned one, a name of `kernelNames` that reaches the name, a
constant outside the copies that refers to a name of a copy's block, and a declaring module that
is not owned. -/

/-- The names a constant refers to: those `Kernel.Environment.replay` replays before it
(`ConstantInfo.getUsedConstantsAsSet`), listed. -/
def usedNames (info : ConstantInfo) : List Name :=
  Std.TreeSet.toList info.getUsedConstantsAsSet

/-- The prefix `_private.m.0` of the names private to the module `m`: Lean names the constant `n`
that `m` declares private `privatePrefix m ++ n` (`Lean.mkPrivateNameCore`). -/
def privatePrefix (m : Name) : Name := mkPrivateNameCore m .anonymous

/-- Whether the name `n` is private to the module `m`: `privatePrefix m` is a prefix of it. -/
def privateTo (m n : Name) : Bool := (privatePrefix m).isPrefixOf n

/-- The name `n` with the prefix `privatePrefix src` replaced by `privatePrefix dst` when `n` is
private to `src`, and `n` otherwise. -/
def renameName (src dst n : Name) : Name :=
  if privateTo src n then n.replacePrefix (privatePrefix src) (privatePrefix dst) else n

/-- The expression `e` with each constant private to `src` renamed by `renameName`, its universe
levels kept (`Expr.replace`). -/
def renameExpr (src dst : Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => if privateTo src n then some (.const (renameName src dst n) us) else none
    | _ => none

/-- A theorem or a safe definition with its name and the names of its mutual block renamed by
`renameName`, and its type and value by `renameExpr`; every other field is kept. Any other constant
is not renamed (`none`). -/
def renameConstant (src dst : Name) : ConstantInfo → Option ConstantInfo
  | .thmInfo v => some (.thmInfo { v with
      name := renameName src dst v.name, type := renameExpr src dst v.type
      value := renameExpr src dst v.value, all := v.all.map (renameName src dst) })
  | .defnInfo v => match v.safety with
    | .safe => some (.defnInfo { v with
        name := renameName src dst v.name, type := renameExpr src dst v.type
        value := renameExpr src dst v.value, all := v.all.map (renameName src dst) })
    | _ => none
  | _ => none

/-- Whether `x` refers to no name private to `dst`, and `renameConstant` renames `x` into a
constant `identical` to `y`. `renamedTo_iff` states the decision. -/
def renamedTo (src dst : Name) (x y : ConstantInfo) : Bool :=
  (usedNames x).all (fun n => !privateTo dst n) && (renameConstant src dst x).any (identical · y)

/-- No name `x` refers to is private to `dst`, and `renameConstant` renames `x` into a constant
`Identical` to `y`. -/
def RenamedTo (src dst : Name) (x y : ConstantInfo) : Prop :=
  (∀ n ∈ usedNames x, privateTo dst n = false) ∧
    ∃ renamed, renameConstant src dst x = some renamed ∧ Identical renamed y

/-- `renamedTo` accepts exactly the pairs that `RenamedTo` relates. -/
theorem renamedTo_iff {src dst : Name} {x y : ConstantInfo} :
    renamedTo src dst x y = true ↔ RenamedTo src dst x y := by
  unfold renamedTo RenamedTo
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    Option.any_eq_true, identical_iff]

/-! ### The references between the loaded constants -/

/-- A constant named `x` in a module of `modules` refers to `y`: `y` is among the names its type
and value use (`successorsOf`). -/
def Refers (modules : Array ModuleData) (x y : Name) : Prop :=
  ∃ data ∈ modules, ∃ c ∈ data.constants, c.name = x ∧ y ∈ successorsOf c

/-- `y` is reached from `x` along `Refers`, in zero or more steps. -/
inductive Leads (modules : Array ModuleData) : Name → Name → Prop
  /-- Every name reaches itself. -/
  | refl (x : Name) : Leads modules x x
  /-- A name reaches whatever a name it refers to reaches. -/
  | step {x m y : Name} : Refers modules x m → Leads modules m y → Leads modules x y

/-- Reaching extends by one more reference. -/
theorem Leads.tail {modules : Array ModuleData} {x m y : Name} (h : Leads modules x m)
    (hy : Refers modules m y) : Leads modules x y := by
  induction h with
  | refl => exact .step hy (.refl y)
  | step hm _ ih => exact .step hm (ih hy)

/-- A name reached from `x` is `x`, or a name that a name reached from `x` refers to. -/
theorem Leads.last {modules : Array ModuleData} {x y : Name} (h : Leads modules x y) :
    x = y ∨ ∃ m, Leads modules x m ∧ Refers modules m y := by
  induction h with
  | refl => exact .inl rfl
  | @step x m y hm _ ih =>
    rcases ih with rfl | ⟨m', hm', hr⟩
    · exact .inr ⟨x, .refl x, hm⟩
    · exact .inr ⟨m', .step hm hm', hr⟩

/-! ### The region of the owned modules

The references a renamed copy is checked against are read from the constants of one set of
modules only: the region of the owned modules (`InRegion`, which `regionOf` computes), the least
set that holds each owned module, each module that imports a module of the set and each module
that shares a name with a module of the set. When the modules outside the owned ones meet
`ImportScoped`, every constant that refers to a name a module of the region declares lies in the
region (`covers_regionOf`), so a search backward from such a name over the region's references
meets every constant that refers to it (`mem_before`). -/

/-- The module at index `j` imports the module whose name `names` gives at index `k`
(`ModuleData.imports`). -/
def Imports (modules : Array ModuleData) (names : Array Name) (j k : Nat) : Prop :=
  ∃ data, modules[j]? = some data ∧ ∃ imp ∈ data.imports, names[k]? = some imp.module

/-- The module at index `k` is in the import closure of the module at index `j`: it is `j`, or it
is in the import closure of a module that `j` imports. -/
inductive Imported (modules : Array ModuleData) (names : Array Name) : Nat → Nat → Prop
  /-- Every module is in its own import closure. -/
  | refl (j : Nat) : Imported modules names j j
  /-- The import closure of a module holds the import closure of each module it imports. -/
  | step {j k l : Nat} : Imports modules names j k → Imported modules names k l →
      Imported modules names j l

/-- Every constant of each module outside `owned` (a module whose name `names` does not give in
`owned`) refers only to names that a module of its import closure declares, the module itself
included.

Lean's import and kernel give this fact for a module whose declarations the kernel checked. It is
trusted of the modules outside `owned`, the trusted base, which may contain unchecked
declarations, as any trusted code may. It is not assumed of an owned module: `linksOf` reads the
references of every owned module in full, and `agrees_iff` takes this fact as a hypothesis.

Assumes:
- Lean v4.35.0, `src/lean/Lean/Environment.lean:2439-2450` (`importModules`) with `2178-2226`
  (`importModulesCore.go`): the environment a module is elaborated in loads each module of its
  import closure, following the `imports` of each loaded module's data, and `finalizeImport` at
  `2308-2363` holds exactly the constants of those modules' data (`2333-2344`).
- Lean v4.35.0, `src/kernel/type_checker.cpp:101-102` (`infer_constant`) with
  `src/kernel/environment.cpp:78-83` (`get`), trusted: the kernel's check of a declaration looks
  up each constant its type and value use and refuses one the environment does not hold
  (`unknown_constant_exception`). The constructors of an inductive type, a constructor's own name
  and the inductive types of a recursor, which `successorsOf` adds for a constant with no value
  (`src/lean/Lean/Util/FoldConsts.lean:67-74`), are declared with it, in its module. -/
def ImportScoped (modules : Array ModuleData) (names : Array Name) (owned : Std.HashSet Name) :
    Prop :=
  ∀ j data, modules[j]? = some data → (∀ name, names[j]? = some name → name ∉ owned) →
    ∀ c ∈ data.constants, ∀ y ∈ successorsOf c,
      ∃ k, Imported modules names j k ∧ Declares modules k y

/-- The module at index `j` is the module the name `x` is attributed to or one of its `others`. -/
def Shares (attributed : Name → Option Nat) (dups : Duplicates) (x : Name) (j : Nat) : Prop :=
  attributed x = some j ∨ j ∈ dups.others.getD x #[]

/-- The region of `owned`: the least set of indices of `modules` that holds each module named in
`owned`, each module that imports a module of the set, and each module that `Shares` a name with a
module of the set. -/
inductive InRegion (modules : Array ModuleData) (names : Array Name)
    (attributed : Name → Option Nat) (dups : Duplicates) (owned : Std.HashSet Name) : Nat → Prop
  /-- A module named in `owned` is in the region. -/
  | owned {j : Nat} {data : ModuleData} {name : Name} : modules[j]? = some data →
      names[j]? = some name → name ∈ owned → InRegion modules names attributed dups owned j
  /-- A module that imports a module of the region is in it. -/
  | imports {j k : Nat} : InRegion modules names attributed dups owned k →
      Imports modules names j k → InRegion modules names attributed dups owned j
  /-- A module that shares a name with a module of the region is in it. -/
  | shares {j k : Nat} {x : Name} {data : ModuleData} :
      InRegion modules names attributed dups owned k → Shares attributed dups x k →
      Shares attributed dups x j → modules[j]? = some data →
      InRegion modules names attributed dups owned j

/-- An index with an entry is below the size. -/
private theorem lt_size_of_getElem? {modules : Array ModuleData} {j : Nat} {data : ModuleData}
    (h : modules[j]? = some data) : j < modules.size := by
  obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp h
  exact hlt

/-- A module of the region is a module of `modules`. -/
theorem InRegion.lt_size {modules : Array ModuleData} {names : Array Name}
    {attributed : Name → Option Nat} {dups : Duplicates} {owned : Std.HashSet Name} {j : Nat}
    (h : InRegion modules names attributed dups owned j) : j < modules.size := by
  cases h with
  | owned hdata _ _ => exact lt_size_of_getElem? hdata
  | imports _ himp =>
    obtain ⟨_, hdata, -⟩ := himp
    exact lt_size_of_getElem? hdata
  | shares _ _ _ hdata => exact lt_size_of_getElem? hdata

/-- The name that stands for the module at index `j` in the search for the region. -/
def moduleNode (j : Nat) : Name := .num .anonymous j

theorem moduleNode_inj {j k : Nat} (h : moduleNode j = moduleNode k) : j = k :=
  (Name.num.inj h).2

/-- The indices below `size` of the modules that share `x`: the module it is attributed to and
its `others`. -/
def sharers (size : Nat) (attributed : Name → Option Nat) (dups : Duplicates) (x : Name) :
    List Nat :=
  ((attributed x).toList ++ (dups.others.getD x #[]).toList).filter (· < size)

theorem mem_sharers {size : Nat} {attributed : Name → Option Nat} {dups : Duplicates} {x : Name}
    {j : Nat} : j ∈ sharers size attributed dups x ↔ Shares attributed dups x j ∧ j < size := by
  simp only [sharers, Shares, List.mem_filter, List.mem_append, Option.mem_toList,
    Array.mem_toList_iff, decide_eq_true_eq]

/-- Under the name of each module, the nodes of the modules that import it. -/
def importersOf (modules : Array ModuleData) : Std.HashMap Name (List Name) :=
  predecessors (modules.zipIdx.toList.map fun e => (moduleNode e.2, e.1.imports.map (·.module)))

theorem mem_importersOf {modules : Array ModuleData} {m y : Name} :
    y ∈ (importersOf modules).getD m [] ↔
      ∃ j data, modules[j]? = some data ∧ y = moduleNode j ∧
        ∃ imp ∈ data.imports, imp.module = m := by
  unfold importersOf
  rw [mem_predecessors]
  constructor
  · rintro ⟨e, he, rfl, hm⟩
    obtain ⟨⟨data, j⟩, hentry, rfl⟩ := List.mem_map.mp he
    obtain ⟨imp, himp, rfl⟩ := Array.mem_map.mp hm
    exact ⟨j, data, Array.mem_zipIdx_iff_getElem?.mp (Array.mem_toList_iff.mp hentry), rfl, imp,
      himp, rfl⟩
  · rintro ⟨j, data, hdata, rfl, imp, himp, rfl⟩
    exact ⟨_, List.mem_map.mpr ⟨(data, j),
      Array.mem_toList_iff.mpr (Array.mem_zipIdx_iff_getElem?.mpr hdata), rfl⟩, rfl,
      Array.mem_map.mpr ⟨imp, himp, rfl⟩⟩

/-- Under the node of each module, the names with `others` that it shares. -/
def sharedOf (size : Nat) (attributed : Name → Option Nat) (dups : Duplicates) :
    Std.HashMap Name (List Name) :=
  predecessors (dups.others.toList.map fun e =>
    (e.1, ((sharers size attributed dups e.1).map moduleNode).toArray))

theorem mem_sharedOf {size : Nat} {attributed : Name → Option Nat} {dups : Duplicates} {k : Nat}
    {x : Name} :
    x ∈ (sharedOf size attributed dups).getD (moduleNode k) [] ↔
      (∃ v, dups.others[x]? = some v) ∧ k ∈ sharers size attributed dups x := by
  unfold sharedOf
  rw [mem_predecessors]
  constructor
  · rintro ⟨e, he, rfl, hk⟩
    obtain ⟨⟨x', v⟩, hentry, rfl⟩ := List.mem_map.mp he
    obtain ⟨k', hk', hnode⟩ := List.mem_map.mp (List.mem_toArray.mp hk)
    refine ⟨⟨v, Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hentry⟩, ?_⟩
    rw [← moduleNode_inj hnode]
    exact hk'
  · rintro ⟨⟨v, hv⟩, hk⟩
    exact ⟨_, List.mem_map.mpr ⟨(x, v), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hv, rfl⟩,
      rfl, List.mem_toArray.mpr (List.mem_map.mpr ⟨k, hk, rfl⟩)⟩

/-- One step of the search for the region, from the node of the module at index `k`: to the node
of each module that imports it (`importers`, under its name) and of each module that shares with
it a name that has `others` (`shared`, under its node). Any other name has no step. -/
def regionNext (size : Nat) (names : Array Name) (attributed : Name → Option Nat)
    (dups : Duplicates) (importers shared : Std.HashMap Name (List Name)) : Name → Array Name
  | .num .anonymous k =>
    ((match names[k]? with
      | some m => importers.getD m []
      | none => []) ++
      (shared.getD (moduleNode k) []).flatMap fun x =>
        (sharers size attributed dups x).map moduleNode).toArray
  | _ => #[]

/-- The steps from the node of the module at index `k`: to a module that imports it, and to a
module that shares with it a name that has `others`. -/
theorem mem_regionNext {modules : Array ModuleData} {names : Array Name}
    {attributed : Name → Option Nat} {dups : Duplicates} {k : Nat} {y : Name} :
    y ∈ regionNext modules.size names attributed dups (importersOf modules)
        (sharedOf modules.size attributed dups) (moduleNode k) ↔
      (∃ j data, modules[j]? = some data ∧ y = moduleNode j ∧ ∃ imp ∈ data.imports,
        names[k]? = some imp.module) ∨
      ∃ x j, (∃ v, dups.others[x]? = some v) ∧ k ∈ sharers modules.size attributed dups x ∧
        j ∈ sharers modules.size attributed dups x ∧ y = moduleNode j := by
  show y ∈ ((match names[k]? with
      | some m => (importersOf modules).getD m []
      | none => []) ++
      ((sharedOf modules.size attributed dups).getD (moduleNode k) []).flatMap fun x =>
        (sharers modules.size attributed dups x).map moduleNode).toArray ↔ _
  rw [List.mem_toArray, List.mem_append]
  refine or_congr ?_ ?_
  · cases hk : names[k]? with
    | none => simp
    | some m =>
      simp only [mem_importersOf, Option.some.injEq]
      constructor
      · rintro ⟨j, data, hdata, rfl, imp, himp, rfl⟩
        exact ⟨j, data, hdata, rfl, imp, himp, rfl⟩
      · rintro ⟨j, data, hdata, rfl, imp, himp, rfl⟩
        exact ⟨j, data, hdata, rfl, imp, himp, rfl⟩
  · simp only [List.mem_flatMap, List.mem_map, mem_sharedOf]
    constructor
    · rintro ⟨x, ⟨hkey, hk⟩, j, hj, rfl⟩
      exact ⟨x, j, hkey, hk, hj, rfl⟩
    · rintro ⟨x, j, hkey, hk, hj, rfl⟩
      exact ⟨x, ⟨hkey, hk⟩, j, hj, rfl⟩

/-- The nodes of the modules of the region of `owned` (`InRegion`): a search from the modules
named in `owned` along `regionNext`, with as fuel the number of modules. It reads the imports of
each module and the `others` of `dups`, and no constant. -/
def regionOf (modules : Array ModuleData) (names : Array Name) (attributed : Name → Option Nat)
    (dups : Duplicates) (owned : Std.HashSet Name) : Std.HashSet Name :=
  let start := ((List.range modules.size).filter fun j => names[j]?.any owned.contains).map
    moduleNode
  (search (regionNext modules.size names attributed dups (importersOf modules)
    (sharedOf modules.size attributed dups)) modules.size start).getD {}

/-- Two modules that share a name and are not the same module share a name that has `others`. -/
private theorem shares_key {attributed : Name → Option Nat} {dups : Duplicates} {x : Name}
    {j k : Nat} (hk : Shares attributed dups x k) (hj : Shares attributed dups x j)
    (hne : j ≠ k) : ∃ v, dups.others[x]? = some v := by
  have key : ∀ i, i ∈ dups.others.getD x #[] → ∃ v, dups.others[x]? = some v := by
    intro i hi
    rw [Std.HashMap.getD_eq_getD_getElem?] at hi
    cases hv : dups.others[x]? with
    | none => rw [hv] at hi; simp at hi
    | some v => exact ⟨v, rfl⟩
  rcases hk with hk | hk
  · rcases hj with hj | hj
    · exact absurd (Option.some.inj (hj.symm.trans hk)) hne
    · exact key j hj
  · exact key k hk

/-- **`regionOf` holds exactly the nodes of the modules of the region of `owned`**: the search
completes within its fuel, since each step leads to the node of a module (`search_isSome`). -/
theorem mem_regionOf {modules : Array ModuleData} {names : Array Name}
    {attributed : Name → Option Nat} {dups : Duplicates} {owned : Std.HashSet Name} {j : Nat} :
    moduleNode j ∈ regionOf modules names attributed dups owned ↔
      InRegion modules names attributed dups owned j := by
  have bound : ∀ x ∈ (List.range modules.size).map moduleNode,
      ∀ y ∈ regionNext modules.size names attributed dups (importersOf modules)
        (sharedOf modules.size attributed dups) x,
      y ∈ (List.range modules.size).map moduleNode := by
    intro x hx y hy
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    rcases mem_regionNext.mp hy with ⟨i, data, hdata, rfl, -⟩ | ⟨_, i, -, -, hi, rfl⟩
    · exact List.mem_map.mpr ⟨i, List.mem_range.mpr (lt_size_of_getElem? hdata), rfl⟩
    · exact List.mem_map.mpr ⟨i, List.mem_range.mpr (mem_sharers.mp hi).2, rfl⟩
  have hstart : ∀ s ∈ ((List.range modules.size).filter fun j => names[j]?.any owned.contains).map
      moduleNode, s ∈ (List.range modules.size).map moduleNode := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs
    exact List.mem_map.mpr ⟨i, (List.mem_filter.mp hi).1, rfl⟩
  obtain ⟨result, hresult⟩ := Option.isSome_iff_exists.mp
    (search_isSome (fuel := modules.size) hstart bound (by simp))
  obtain ⟨complete, sound⟩ := search_some hresult
  have eq : regionOf modules names attributed dups owned = result := by
    simp only [regionOf, hresult, Option.getD_some]
  rw [eq]
  constructor
  · intro h
    obtain ⟨s, hs, hr⟩ := sound _ h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hi, howned⟩ := List.mem_filter.mp hi
    obtain ⟨name, hname, hcontains⟩ := (Option.any_eq_true _ _).mp howned
    have hregion : InRegion modules names attributed dups owned i :=
      .owned (Array.getElem?_eq_getElem (List.mem_range.mp hi)) hname
        (Std.HashSet.contains_iff_mem.mp hcontains)
    -- Each step from the node of a module of the region leads to the node of one.
    suffices step : ∀ a b, Reach (regionNext modules.size names attributed dups
          (importersOf modules) (sharedOf modules.size attributed dups)) a b →
        ∀ i, a = moduleNode i → InRegion modules names attributed dups owned i →
        ∃ l, b = moduleNode l ∧ InRegion modules names attributed dups owned l by
      obtain ⟨l, hl, hregion⟩ := step _ _ hr i rfl hregion
      rw [moduleNode_inj hl]
      exact hregion
    intro a b hab
    induction hab with
    | refl => exact fun i hi hregion => ⟨i, hi, hregion⟩
    | step hm _ ih =>
      intro i hi hregion
      subst hi
      rcases mem_regionNext.mp hm with ⟨l, data, hdata, rfl, imp, himp, hname⟩ |
          ⟨x, l, -, hi, hl, rfl⟩
      · exact ih l rfl (.imports hregion ⟨data, hdata, imp, himp, hname⟩)
      · obtain ⟨hl, hlt⟩ := mem_sharers.mp hl
        exact ih l rfl (.shares hregion (mem_sharers.mp hi).1 hl
          (Array.getElem?_eq_getElem hlt))
  · intro h
    suffices reach : ∃ s ∈ ((List.range modules.size).filter
          fun j => names[j]?.any owned.contains).map moduleNode,
        Reach (regionNext modules.size names attributed dups (importersOf modules)
          (sharedOf modules.size attributed dups)) s (moduleNode j) by
      obtain ⟨s, hs, hr⟩ := reach
      exact complete s hs _ hr
    induction h with
    | @owned i data name hdata hname howned =>
      refine ⟨moduleNode i, List.mem_map.mpr ⟨i, List.mem_filter.mpr
        ⟨List.mem_range.mpr (lt_size_of_getElem? hdata), ?_⟩, rfl⟩, .refl _⟩
      simpa [hname] using Std.HashSet.contains_iff_mem.mpr howned
    | @imports i k _ himp ih =>
      obtain ⟨s, hs, hr⟩ := ih
      obtain ⟨data, hdata, imp, himp, hname⟩ := himp
      exact ⟨s, hs, hr.tail (mem_regionNext.mpr (.inl ⟨i, data, hdata, rfl, imp, himp, hname⟩))⟩
    | @shares i k x data hk hsk hsi hdata ih =>
      obtain ⟨s, hs, hr⟩ := ih
      by_cases hik : i = k
      · subst hik
        exact ⟨s, hs, hr⟩
      · exact ⟨s, hs, hr.tail (mem_regionNext.mpr (.inr ⟨x, i, shares_key hsk hsi hik,
          mem_sharers.mpr ⟨hsk, hk.lt_size⟩, mem_sharers.mpr ⟨hsi, lt_size_of_getElem? hdata⟩,
          rfl⟩))⟩

/-- Whether the module at index `j` is in `region`, a set of nodes such as `regionOf` gives. -/
def regionHas (region : Std.HashSet Name) (j : Nat) : Bool := region.contains (moduleNode j)

theorem regionHas_iff {modules : Array ModuleData} {names : Array Name}
    {attributed : Name → Option Nat} {dups : Duplicates} {owned : Std.HashSet Name} {j : Nat} :
    regionHas (regionOf modules names attributed dups owned) j = true ↔
      InRegion modules names attributed dups owned j := by
  rw [regionHas, Std.HashSet.contains_iff_mem, mem_regionOf]

/-- Every module that declares `y` is one that `inside` accepts. -/
def DeclaredIn (modules : Array ModuleData) (inside : Nat → Bool) (y : Name) : Prop :=
  ∀ k, Declares modules k y → inside k = true

/-- What the references of the modules that `inside` accepts give: a constant that refers to a
name `DeclaredIn` them is in one of them, each module that declares a name one of them declares is
accepted too, and a constant of a module that is not accepted refers only to declared names. -/
structure Covers (modules : Array ModuleData) (inside : Nat → Bool) : Prop where
  /-- A constant that refers to a name `DeclaredIn` the accepted modules is in one of them. -/
  refers : ∀ j data, modules[j]? = some data → ∀ c ∈ data.constants, ∀ y ∈ successorsOf c,
    DeclaredIn modules inside y → inside j = true
  /-- Each module that declares a name an accepted module declares is accepted. -/
  shares : ∀ k j y, inside k = true → Declares modules k y → Declares modules j y →
    inside j = true
  /-- A constant of a module that is not accepted refers only to names some module declares. -/
  declared : ∀ j data, modules[j]? = some data → inside j = false → ∀ c ∈ data.constants,
    ∀ y ∈ successorsOf c, ∃ k, Declares modules k y

/-- **Under `ImportScoped`, the region of `owned` covers the references to its names**: a
constant that refers to a name `DeclaredIn` the region is in a module of the region, which is
owned or imports one, through its import closure. -/
theorem covers_regionOf {find : Name → Option ConstantInfo} {attributed : Name → Option Nat}
    {modules : Array ModuleData} {names : Array Name} {owned : Std.HashSet Name}
    (hscoped : ImportScoped modules names owned) :
    Covers modules (regionHas
      (regionOf modules names attributed (duplicatesOf find attributed modules) owned)) := by
  have outside : ∀ j data, modules[j]? = some data →
      ¬ InRegion modules names attributed (duplicatesOf find attributed modules) owned j →
      ∀ name, names[j]? = some name → name ∉ owned :=
    fun _ _ hdata hout _ hname howned => hout (.owned hdata hname howned)
  have closure : ∀ j k, Imported modules names j k →
      InRegion modules names attributed (duplicatesOf find attributed modules) owned k →
      InRegion modules names attributed (duplicatesOf find attributed modules) owned j := by
    intro j k h
    induction h with
    | refl => exact id
    | step himp _ ih => exact fun hk => .imports (ih hk) himp
  have shares : ∀ x j, Declares modules j x →
      Shares attributed (duplicatesOf find attributed modules) x j := by
    intro x j hdecl
    by_cases hattr : attributed x = some j
    · exact .inl hattr
    · exact .inr (mem_others_iff.mpr ⟨hdecl, hattr⟩)
  refine ⟨fun j data hdata c hc y hy hall => ?_, fun k j y hk hdk hdj => ?_,
    fun j data hdata hout c hc y hy => ?_⟩
  · rw [regionHas_iff]
    exact Classical.byContradiction fun hout => by
      obtain ⟨k, himp, hdecl⟩ := hscoped j data hdata (outside j data hdata hout) c hc y hy
      exact hout (closure j k himp (regionHas_iff.mp (hall k hdecl)))
  · rw [regionHas_iff] at hk ⊢
    have hdj' := hdj
    obtain ⟨data, hdata, -⟩ := hdj'
    exact .shares hk (shares y k hdk) (shares y j hdj) hdata
  · have hnot :
        ¬ InRegion modules names attributed (duplicatesOf find attributed modules) owned j :=
      fun h => by rw [← regionHas_iff, hout] at h; exact Bool.false_ne_true h
    obtain ⟨k, -, hdecl⟩ := hscoped j data hdata (outside j data hdata hnot) c hc y hy
    exact ⟨k, hdecl⟩

/-! ### The references of the region -/

/-- Each constant of each module that `inside` accepts, by name, with the names it refers to. -/
def regionEdges (modules : Array ModuleData) (inside : Nat → Bool) : List (Name × Array Name) :=
  (modules.zipIdx.toList.filter (inside ·.2)).flatMap fun e =>
    e.1.constants.toList.map fun c => (c.name, successorsOf c)

/-- The edges are exactly the constants of the accepted modules, each with the names it refers
to. -/
theorem mem_regionEdges {modules : Array ModuleData} {inside : Nat → Bool}
    {e : Name × Array Name} :
    e ∈ regionEdges modules inside ↔
      ∃ j data, modules[j]? = some data ∧ inside j = true ∧
        ∃ c ∈ data.constants, e = (c.name, successorsOf c) := by
  unfold regionEdges
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨⟨data, j⟩, hentry, he⟩
    obtain ⟨hentry, hin⟩ := List.mem_filter.mp hentry
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
    exact ⟨j, data, Array.mem_zipIdx_iff_getElem?.mp (Array.mem_toList_iff.mp hentry), hin, c,
      Array.mem_toList_iff.mp hc, rfl⟩
  · rintro ⟨j, data, hdata, hin, c, hc, rfl⟩
    exact ⟨(data, j), List.mem_filter.mpr
      ⟨Array.mem_toList_iff.mpr (Array.mem_zipIdx_iff_getElem?.mpr hdata), hin⟩,
      List.mem_map.mpr ⟨c, Array.mem_toList_iff.mpr hc, rfl⟩⟩

/-- The names a search over the references of the modules that `inside` accepts can meet: the name
of each of their constants with the names it refers to. -/
def namesIn (modules : Array ModuleData) (inside : Nat → Bool) : List Name :=
  (regionEdges modules inside).flatMap fun e => e.1 :: e.2.toList

/-- The name of a constant of an accepted module is one of `namesIn`. -/
theorem name_mem_namesIn {modules : Array ModuleData} {inside : Nat → Bool} {j : Nat}
    {data : ModuleData} {c : ConstantInfo} (hdata : modules[j]? = some data)
    (hin : inside j = true) (hc : c ∈ data.constants) : c.name ∈ namesIn modules inside :=
  List.mem_flatMap.mpr
    ⟨_, mem_regionEdges.mpr ⟨j, data, hdata, hin, c, hc, rfl⟩, List.mem_cons_self⟩

/-- A name a constant of an accepted module refers to is one of `namesIn`. -/
theorem used_mem_namesIn {modules : Array ModuleData} {inside : Nat → Bool} {j : Nat}
    {data : ModuleData} {c : ConstantInfo} {y : Name} (hdata : modules[j]? = some data)
    (hin : inside j = true) (hc : c ∈ data.constants) (hy : y ∈ successorsOf c) :
    y ∈ namesIn modules inside :=
  List.mem_flatMap.mpr ⟨_, mem_regionEdges.mpr ⟨j, data, hdata, hin, c, hc, rfl⟩,
    List.mem_cons_of_mem _ (Array.mem_toList_iff.mpr hy)⟩

/-- The names of the constants of every module of `modules`. -/
def declaredNames (modules : Array ModuleData) : List Name :=
  modules.toList.flatMap fun data => data.constants.toList.map (·.name)

/-- A name some module declares is one of `declaredNames`. -/
theorem mem_declaredNames {modules : Array ModuleData} {k : Nat} {y : Name}
    (h : Declares modules k y) : y ∈ declaredNames modules := by
  obtain ⟨data, hdata, c, hc, rfl⟩ := h
  exact List.mem_flatMap.mpr ⟨data, Array.mem_toList_iff.mpr (Array.mem_of_getElem? hdata),
    List.mem_map.mpr ⟨c, Array.mem_toList_iff.mpr hc, rfl⟩⟩

/-- The references between the constants of a set of modules, read backward, with the fuel of a
search over them. -/
structure Links where
  /-- Under each name, the names of the constants that refer to it. -/
  back : Std.HashMap Name (List Name)
  /-- The fuel of a search over them: at least the number of names it can meet. -/
  fuel : Nat
  /-- The number of constants of all the loaded modules, which bounds the names outside the set a
  search forward meets (`nativeReaching`). -/
  declared : Nat

/-- The names of the constants that refer to `y`. -/
def Links.before (links : Links) (y : Name) : Array Name := (links.back.getD y []).toArray

/-- Every name reached along `next` from a name of `start`, within the fuel of `links`, or none
when the fuel runs out, which `mem_closure` shows a search over the names of the modules never
does. -/
def Links.closure (links : Links) (next : Name → Array Name) (start : List Name) :
    Std.HashSet Name :=
  (search next links.fuel start).getD {}

/-- The references between the constants of the modules of `modules` that `inside` accepts: under
each name the names of their constants that refer to it (`predecessors` of `regionEdges`), as fuel
the length of `namesIn`, and the number of constants of all the modules. `agreeing` gives as
`inside` the region of the owned modules (`regionOf`), and reads the references of no other
constant this way. -/
def linksOf (modules : Array ModuleData) (inside : Nat → Bool) : Links :=
  let edges := regionEdges modules inside
  { back := predecessors edges, fuel := (edges.map fun e => e.2.size + 1).sum
    declared := (modules.toList.map fun data => data.constants.size).sum }

/-- The fuel of `linksOf` is the number of entries of `namesIn`, and its count of constants the
number of entries of `declaredNames`. -/
theorem fuel_linksOf {modules : Array ModuleData} {inside : Nat → Bool} :
    (linksOf modules inside).fuel = (namesIn modules inside).length ∧
      (linksOf modules inside).declared = (declaredNames modules).length := by
  constructor <;>
    simp [linksOf, namesIn, declaredNames, List.length_flatMap]

/-- The names before `y` are exactly the names of the constants of accepted modules that refer to
`y`. -/
theorem mem_before_iff {modules : Array ModuleData} {inside : Nat → Bool} {x y : Name} :
    x ∈ (linksOf modules inside).before y ↔
      ∃ j data, modules[j]? = some data ∧ inside j = true ∧
        ∃ c ∈ data.constants, c.name = x ∧ y ∈ successorsOf c := by
  simp only [Links.before, linksOf, List.mem_toArray, mem_predecessors, mem_regionEdges]
  constructor
  · rintro ⟨e, ⟨j, data, hdata, hin, c, hc, rfl⟩, rfl, hy⟩
    exact ⟨j, data, hdata, hin, c, hc, rfl, hy⟩
  · rintro ⟨j, data, hdata, hin, c, hc, rfl, hy⟩
    exact ⟨_, ⟨j, data, hdata, hin, c, hc, rfl⟩, rfl, hy⟩

/-- A name before `y` refers to `y`. -/
theorem refers_of_before {modules : Array ModuleData} {inside : Nat → Bool} {x y : Name}
    (h : x ∈ (linksOf modules inside).before y) : Refers modules x y := by
  obtain ⟨_, data, hdata, -, c, hc, hx, hy⟩ := mem_before_iff.mp h
  exact ⟨data, Array.mem_of_getElem? hdata, c, hc, hx, hy⟩

/-- A name before another is `DeclaredIn` the accepted modules. -/
theorem declaredIn_of_before {modules : Array ModuleData} {inside : Nat → Bool}
    (hcovers : Covers modules inside) {x y : Name} (h : x ∈ (linksOf modules inside).before y) :
    DeclaredIn modules inside x := by
  obtain ⟨j, data, hdata, hin, c, hc, rfl, -⟩ := mem_before_iff.mp h
  exact fun k hk => hcovers.shares j k c.name hin ⟨data, hdata, c, hc, rfl⟩ hk

/-- A name before another is one of `namesIn`. -/
theorem before_mem_namesIn {modules : Array ModuleData} {inside : Nat → Bool} {x y : Name}
    (h : x ∈ (linksOf modules inside).before y) : x ∈ namesIn modules inside := by
  obtain ⟨j, data, hdata, hin, c, hc, rfl, -⟩ := mem_before_iff.mp h
  exact name_mem_namesIn hdata hin hc

/-- **The names before a name `DeclaredIn` the accepted modules are exactly the names of the
constants that refer to it**, when the accepted modules `Covers` the references. -/
theorem mem_before {modules : Array ModuleData} {inside : Nat → Bool}
    (hcovers : Covers modules inside) {x y : Name} (hy : DeclaredIn modules inside y) :
    x ∈ (linksOf modules inside).before y ↔ Refers modules x y := by
  refine ⟨refers_of_before, fun ⟨data, hdata, c, hc, hx, hyc⟩ => ?_⟩
  obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.mp hdata
  exact mem_before_iff.mpr ⟨j, data, hj, hcovers.refers j data hj c hc y hyc hy, c, hc, hx, hyc⟩

/-- Every name in a closure is reached from `start`. -/
theorem closure_sound {links : Links} {next : Name → Array Name} {start : List Name} {x : Name}
    (h : x ∈ links.closure next start) : ∃ s ∈ start, Reach next s x := by
  unfold Links.closure at h
  cases hs : search next links.fuel start with
  | none => simp [hs] at h
  | some result =>
    rw [hs, Option.getD_some] at h
    exact (search_some hs).2 x h

/-- **A closure over the references of the accepted modules holds exactly the names reached from
`start`**, when `start` and every step along `next` stay among `namesIn`: the search completes
within the fuel (`search_isSome`), and `search_some` describes what it returns. -/
theorem mem_closure {modules : Array ModuleData} {inside : Nat → Bool}
    {next : Name → Array Name} {start : List Name}
    (hstart : ∀ s ∈ start, s ∈ namesIn modules inside)
    (hnext : ∀ x, ∀ y ∈ next x, y ∈ namesIn modules inside) {x : Name} :
    x ∈ (linksOf modules inside).closure next start ↔ ∃ s ∈ start, Reach next s x := by
  obtain ⟨result, hresult⟩ := Option.isSome_iff_exists.mp
    (search_isSome hstart (fun x _ y hy => hnext x y hy) (Nat.le_of_eq fuel_linksOf.1.symm))
  obtain ⟨complete, sound⟩ := search_some hresult
  simp only [Links.closure, hresult, Option.getD_some]
  exact ⟨sound x, fun ⟨s, hs, hr⟩ => complete s hs x hr⟩

/-- A name reached backward from a name `DeclaredIn` the accepted modules is `DeclaredIn` them. -/
theorem declaredIn_of_reach {modules : Array ModuleData} {inside : Nat → Bool}
    (hcovers : Covers modules inside) {y x : Name} (hy : DeclaredIn modules inside y)
    (h : Reach (linksOf modules inside).before y x) : DeclaredIn modules inside x := by
  revert hy
  induction h with
  | refl => exact id
  | step hm _ ih => exact fun _ => ih (declaredIn_of_before hcovers hm)

/-- A path backward from a name `DeclaredIn` the accepted modules along `before` is a path forward
to it along `Refers`. -/
theorem reach_before_iff {modules : Array ModuleData} {inside : Nat → Bool}
    (hcovers : Covers modules inside) {y x : Name} (hy : DeclaredIn modules inside y) :
    Reach (linksOf modules inside).before y x ↔ Leads modules x y := by
  constructor
  · intro h
    clear hy
    induction h with
    | refl => exact .refl _
    | step hm _ ih => exact ih.tail (refers_of_before hm)
  · intro h
    revert hy
    induction h with
    | refl => exact fun _ => .refl _
    | step hm _ ih =>
      intro hy
      have hreach := ih hy
      exact hreach.tail
        ((mem_before hcovers (declaredIn_of_reach hcovers hy hreach)).mpr hm)

/-- The constants Lean's kernel can read in the check of a declaration although neither the
declaration nor a constant the check read refers to them: the types and constructors that a
literal stands for, the results of a reduced `Nat` comparison, and the constants of the check of
the quotient declaration.

Assumes:
- Lean v4.35.0, `src/kernel/inductive.cpp:1359-1402` (trusted): a `Nat` literal stands for
  `Nat.zero` or `Nat.succ`, and a `String` literal for `String.ofList` of `List.cons` and
  `List.nil` at `Char`, with `Char.ofNat`, which `src/kernel/inductive.h:95-97` and
  `src/kernel/type_checker.cpp:421-422` and `1107-1108` build.
- Lean v4.35.0, `src/kernel/type_checker.cpp:318-320` with `src/lean/Lean/Expr.lean:621-627`: the
  type of a literal is `Nat` or `String`.
- Lean v4.35.0, `src/kernel/type_checker.cpp:669` with `src/library/util.cpp:708-709` and
  `src/library/constants.cpp:147-150` (trusted): a reduced `Nat.beq` or `Nat.ble` gives `Bool.true`
  or `Bool.false`. The kernel of Lean v4.35.0 reduces no constant by running compiled code.
- Lean v4.35.0, `src/kernel/quot.cpp:41-113` (trusted): the check of the quotient declaration
  reads `Eq` and builds `Quot`, `Quot.mk`, `Quot.lift` and `Quot.ind`. -/
def kernelNames : List Name :=
  [``Nat, ``Nat.zero, ``Nat.succ, ``String, ``String.ofList, ``Char, ``Char.ofNat, ``List.nil,
    ``List.cons, ``Bool, ``Bool.true, ``Bool.false, ``Eq, ``Quot, ``Quot.mk, ``Quot.lift,
    ``Quot.ind]

/-- The names that reach `n` in one or more steps: the closure backward from the names of the
constants that refer to `n`. -/
def aboveIn (links : Links) (n : Name) : Std.HashSet Name :=
  links.closure links.before (links.before n).toList

/-- **`aboveIn` holds exactly the names that reach a constant referring to `n`**, for `n`
`DeclaredIn` modules that `Covers` the references. -/
theorem mem_aboveIn {modules : Array ModuleData} {inside : Nat → Bool}
    (hcovers : Covers modules inside) {n x : Name} (hn : DeclaredIn modules inside n) :
    x ∈ aboveIn (linksOf modules inside) n ↔ ∃ m, Refers modules m n ∧ Leads modules x m := by
  unfold aboveIn
  rw [mem_closure (fun _ hs => before_mem_namesIn (Array.mem_toList_iff.mp hs))
    (fun _ _ hy => before_mem_namesIn hy)]
  constructor
  · rintro ⟨s, hs, hr⟩
    have hs' := Array.mem_toList_iff.mp hs
    exact ⟨s, refers_of_before hs',
      (reach_before_iff hcovers (declaredIn_of_before hcovers hs')).mp hr⟩
  · rintro ⟨m, hm, hx⟩
    have hm' := (mem_before hcovers hn).mpr hm
    exact ⟨m, Array.mem_toList_iff.mpr hm',
      (reach_before_iff hcovers (declaredIn_of_before hcovers hm')).mpr hx⟩

/-- Whether `x` reaches `n`, read from the names `above` that reach it in one or more steps. -/
def reachesIn (above : Std.HashSet Name) (n x : Name) : Bool :=
  x == n || above.contains x

/-- With `above` the names that reach `n` in one or more steps, `reachesIn` decides `Leads`. -/
theorem reachesIn_iff {modules : Array ModuleData} {above : Std.HashSet Name} {n : Name}
    (habove : ∀ x, x ∈ above ↔ ∃ m, Refers modules m n ∧ Leads modules x m) {x : Name} :
    reachesIn above n x = true ↔ Leads modules x n := by
  unfold reachesIn
  rw [Bool.or_eq_true, beq_iff_eq, Std.HashSet.contains_iff_mem, habove]
  constructor
  · rintro (rfl | ⟨m, hm, hx⟩)
    · exact .refl x
    · exact hx.tail hm
  · intro h
    rcases h.last with rfl | ⟨m, hx, hm⟩
    · exact .inl rfl
    · exact .inr ⟨m, hm, hx⟩

/-- The constants of a module's data under each name: each constant of the data, in the list
under its name. -/
def copiesByName (data : ModuleData) : Std.HashMap Name (List ConstantInfo) :=
  data.constants.foldl (fun index c => index.insert c.name (c :: index.getD c.name [])) {}

/-- The constants `copiesByName` gives under `x` are exactly the module's constants named `x`. -/
theorem mem_copiesByName {data : ModuleData} {x : Name} {c : ConstantInfo} :
    c ∈ (copiesByName data).getD x [] ↔ c ∈ data.constants ∧ c.name = x := by
  suffices step : ∀ (rest : List ConstantInfo) (index : Std.HashMap Name (List ConstantInfo)),
      c ∈ (rest.foldl (fun index c => index.insert c.name (c :: index.getD c.name []))
        index).getD x [] ↔ c ∈ index.getD x [] ∨ (c ∈ rest ∧ c.name = x) by
    unfold copiesByName
    rw [← Array.foldl_toList, step]
    simp [Array.mem_toList_iff]
  intro rest
  induction rest with
  | nil => intro index; simp
  | cons head rest ih =>
    intro index
    simp only [List.foldl_cons]
    rw [ih, Std.HashMap.getD_insert]
    by_cases hx : head.name = x
    · subst hx
      simp only [beq_self_eq_true, ↓reduceIte, List.mem_cons]
      constructor
      · rintro ((rfl | h) | ⟨h, hn⟩)
        · exact .inr ⟨.inl rfl, rfl⟩
        · exact .inl h
        · exact .inr ⟨.inr h, hn⟩
      · rintro (h | ⟨rfl | h, hn⟩)
        · exact .inl (.inr h)
        · exact .inl (.inl rfl)
        · exact .inr ⟨h, hn⟩
    · have : (head.name == x) = false := beq_false_of_ne hx
      simp only [this, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (h | ⟨h, hn⟩)
        · exact .inl h
        · exact .inr ⟨.inr h, hn⟩
      · rintro (h | ⟨rfl | h, hn⟩)
        · exact .inl h
        · exact absurd hn hx
        · exact .inr ⟨h, hn⟩

/-- The constants of each module of `modules` by name (`copiesByName`), each computed when a search
first reads it, so a search reads the constants of only the modules that hold a copy it meets. -/
def copiesIndexes (modules : Array ModuleData) :
    Array (Thunk (Std.HashMap Name (List ConstantInfo))) :=
  modules.map fun data => Thunk.mk fun _ => copiesByName data

/-- The names the copies of `x` refer to: the copies that the module `x` is attributed to and each
of its `others` declare, read from the index of each such module (`copiesIndexes`). A name that no
module declares has none. -/
def copiesNext (indexes : Array (Thunk (Std.HashMap Name (List ConstantInfo))))
    (attributed : Name → Option Nat) (dups : Duplicates) (x : Name) : Array Name :=
  (((attributed x).toList ++ (dups.others.getD x #[]).toList).flatMap fun j =>
    match indexes[j]? with
    | some index => (index.get.getD x []).flatMap fun c => (successorsOf c).toList
    | none => []).toArray

/-- The names after `x` are exactly the names a copy of `x` refers to. -/
theorem mem_copiesNext {find : Name → Option ConstantInfo} {attributed : Name → Option Nat}
    {modules : Array ModuleData} {x y : Name} :
    y ∈ copiesNext (copiesIndexes modules) attributed (duplicatesOf find attributed modules) x ↔
      Refers modules x y := by
  unfold copiesNext Refers
  rw [List.mem_toArray, List.mem_flatMap]
  constructor
  · rintro ⟨j, -, hy⟩
    simp only [copiesIndexes, Array.getElem?_map] at hy
    cases hdata : modules[j]? with
    | none => simp [hdata] at hy
    | some data =>
      simp only [hdata, Option.map_some] at hy
      obtain ⟨c, hc, hyc⟩ := List.mem_flatMap.mp hy
      obtain ⟨hc, hcx⟩ := mem_copiesByName.mp hc
      exact ⟨data, Array.mem_of_getElem? hdata, c, hc, hcx, Array.mem_toList_iff.mp hyc⟩
  · rintro ⟨data, hdata, c, hc, hcx, hyc⟩
    obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.mp hdata
    refine ⟨j, ?_, ?_⟩
    · rw [List.mem_append, Option.mem_toList, Array.mem_toList_iff]
      by_cases hattr : attributed x = some j
      · exact .inl hattr
      · exact .inr (mem_others_iff.mpr ⟨⟨data, hj, c, hc, hcx⟩, hattr⟩)
    · simp only [copiesIndexes, Array.getElem?_map, hj, Option.map_some]
      exact List.mem_flatMap.mpr
        ⟨c, mem_copiesByName.mpr ⟨hc, hcx⟩, Array.mem_toList_iff.mpr hyc⟩

/-- A path along `copiesNext` is a path along `Refers`. -/
theorem reach_copiesNext_iff {find : Name → Option ConstantInfo} {attributed : Name → Option Nat}
    {modules : Array ModuleData} {x y : Name} :
    Reach (copiesNext (copiesIndexes modules) attributed (duplicatesOf find attributed modules))
        x y ↔ Leads modules x y := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl _
    | step hm _ ih => exact .step (mem_copiesNext.mp hm) ih
  · intro h
    induction h with
    | refl => exact .refl _
    | step hm _ ih => exact .step (mem_copiesNext.mpr hm) ih

/-- The names that reach `Lean.reduceBool` or `Lean.reduceNat`, among the names that one search
forward along `copiesNext` from `roots` meets: a search back from the two names along the
references that search recorded (`predecessors`). The two were the constants whose argument the
kernel of Lean v4.34.1 reduced by running compiled code. Lean v4.35.0 has neither, and its kernel
runs no compiled code, so a module can declare either name only as an ordinary constant; the
search still finds the names that reach one, as it did at Lean v4.34.1. The search forward reads
the copies of each name it meets, and so the constants of each module that holds one
(`copiesIndexes`). It meets a name that no module declares and follows no reference from it.
`none` when a search runs out of `fuel`. -/
def nativeReaching (modules : Array ModuleData) (attributed : Name → Option Nat)
    (dups : Duplicates) (fuel : Nat) (roots : List Name) : Option (Std.HashSet Name) :=
  match searchEdges (copiesNext (copiesIndexes modules) attributed dups) fuel roots with
  | some (_, edges) =>
    let preds := predecessors edges
    search (fun y => (preds.getD y []).toArray) fuel [`Lean.reduceBool, `Lean.reduceNat]
  | none => none

/-- Whether neither `n` nor a name of `above` is among the names that `native` gives as reaching
`Lean.reduceBool` or `Lean.reduceNat` (`nativeReaching`). When a search ran out of fuel, the name
is refused. -/
def nativeFree (native : Option (Std.HashSet Name)) (above : Std.HashSet Name) (n : Name) : Bool :=
  match native with
  | some reaching => (n :: above.toList).all fun d => !reaching.contains d
  | none => false

/-- **`nativeFree` over the one search `nativeReaching` from `roots` decides that no name reaching
`n` reaches `Lean.reduceBool` or `Lean.reduceNat`**, for `above` the names that reach `n` in one
or more steps, `n` and each name of `above` among `roots`, accepted modules that `Covers` the
references, and a fuel of at least the names a search can meet: the two primitives, `roots`,
`declaredNames` and `namesIn`. -/
theorem nativeFree_iff {find : Name → Option ConstantInfo} {attributed : Name → Option Nat}
    {modules : Array ModuleData} {inside : Nat → Bool} (hcovers : Covers modules inside)
    {above : Std.HashSet Name} {n : Name}
    (habove : ∀ x, x ∈ above ↔ ∃ m, Refers modules m n ∧ Leads modules x m) {roots : List Name}
    (hroots : ∀ d ∈ n :: above.toList, d ∈ roots) {fuel : Nat}
    (hfuel : 2 + roots.length + (declaredNames modules).length +
      (namesIn modules inside).length ≤ fuel) :
    nativeFree (nativeReaching modules attributed (duplicatesOf find attributed modules) fuel roots)
        above n = true ↔
      ∀ d, Leads modules d n →
        ¬ (Leads modules d `Lean.reduceBool ∨ Leads modules d `Lean.reduceNat) := by
  have start : ∀ s, s ∈ n :: above.toList ↔ Leads modules s n := fun s => by
    rw [← reachesIn_iff habove]
    simp only [reachesIn, List.mem_cons, Std.HashSet.mem_toList, Bool.or_eq_true, beq_iff_eq,
      Std.HashSet.contains_iff_mem]
  have closed : ∀ x ∈ roots ++ declaredNames modules ++ namesIn modules inside,
      ∀ y ∈ copiesNext (copiesIndexes modules) attributed (duplicatesOf find attributed modules) x,
      y ∈ roots ++ declaredNames modules ++ namesIn modules inside := by
    intro x _ y hy
    obtain ⟨data, hdata, c, hc, -, hyc⟩ := mem_copiesNext.mp hy
    obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.mp hdata
    cases hin : inside j with
    | true => exact List.mem_append_right _ (used_mem_namesIn hj hin hc hyc)
    | false =>
      obtain ⟨k, hk⟩ := hcovers.declared j data hj hin c hc y hyc
      exact List.mem_append_left _ (List.mem_append_right _ (mem_declaredNames hk))
  have forward := search_isSome (fuel := fuel)
    (fun s hs => List.mem_append_left _ (List.mem_append_left _ hs)) closed
    (by simp only [List.length_append]; omega)
  simp only [search, Option.isSome_map] at forward
  obtain ⟨⟨seen, edges⟩, hforward⟩ := Option.isSome_iff_exists.mp forward
  obtain ⟨complete, -, -, edgeOK⟩ := searchEdges_some hforward
  have backClosed : ∀ x ∈ `Lean.reduceBool :: `Lean.reduceNat :: declaredNames modules,
      ∀ y ∈ ((predecessors edges).getD x []).toArray,
      y ∈ `Lean.reduceBool :: `Lean.reduceNat :: declaredNames modules := by
    intro x _ y hy
    simp only [List.mem_toArray, mem_predecessors] at hy
    obtain ⟨e, he, rfl, hx⟩ := hy
    rw [edgeOK e he] at hx
    obtain ⟨data, hdata, c, hc, hcn, -⟩ := mem_copiesNext.mp hx
    obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.mp hdata
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_declaredNames ⟨data, hj, c, hc, hcn⟩))
  obtain ⟨reaching, hback⟩ := Option.isSome_iff_exists.mp
    (search_isSome (fuel := fuel) (start := [`Lean.reduceBool, `Lean.reduceNat])
      (fun s hs => by
        rcases List.mem_cons.mp hs with rfl | hs
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_singleton.mp hs ▸ List.mem_cons_self))
      backClosed (by simp only [List.length_cons]; omega))
  obtain ⟨backComplete, backSound⟩ := search_some hback
  have mem : ∀ d ∈ seen,
      d ∈ reaching ↔ Leads modules d `Lean.reduceBool ∨ Leads modules d `Lean.reduceNat := by
    intro d hd
    have back : ∀ a, Reach (fun y => ((predecessors edges).getD y []).toArray) a d ↔
        Leads modules d a := fun _ =>
      (reach_predecessors_iff hforward hd).trans reach_copiesNext_iff
    constructor
    · intro h
      obtain ⟨s, hs, hr⟩ := backSound d h
      rcases List.mem_cons.mp hs with rfl | hs
      · exact .inl ((back _).mp hr)
      · rw [List.mem_singleton.mp hs] at hr
        exact .inr ((back _).mp hr)
    · rintro (h | h)
      · exact backComplete _ List.mem_cons_self d ((back _).mpr h)
      · exact backComplete _ (List.mem_cons_of_mem _ List.mem_cons_self) d ((back _).mpr h)
  unfold nativeReaching nativeFree
  rw [hforward]
  dsimp only
  rw [hback]
  simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    Std.HashSet.contains_eq_false_iff_not_mem]
  constructor
  · intro h d hd
    have hs := (start d).mpr hd
    rw [← mem d (complete d (hroots d hs) d (.refl d))]
    exact h d hs
  · intro h d hs
    rw [mem d (complete d (hroots d hs) d (.refl d))]
    exact h d ((start d).mp hs)

/-! ### The block of a renamed copy -/

/-- The names private to `src` one reference away from `x`: those the constant `srcFind` gives
under `x` refers to, and the names of the constants that refer to `x`. -/
def linkedIn (links : Links) (src : Name) (srcFind : Name → Option ConstantInfo) (x : Name) :
    Array Name :=
  ((match srcFind x with
    | some c => successorsOf c
    | none => #[]) ++ links.before x).filter (privateTo src)

/-- `y` is private to `src` and one reference away from `x`: the constant `srcFind` gives under
`x` refers to it, or a constant named `y` refers to `x`. -/
def Linked (modules : Array ModuleData) (src : Name) (srcFind : Name → Option ConstantInfo)
    (x y : Name) : Prop :=
  privateTo src y = true ∧ ((∃ c, srcFind x = some c ∧ y ∈ successorsOf c) ∨ Refers modules y x)

/-- `y` is joined to `x` through names private to `src`, in zero or more `Linked` steps. -/
inductive Joined (modules : Array ModuleData) (src : Name) (srcFind : Name → Option ConstantInfo) :
    Name → Name → Prop
  /-- Every name is joined to itself. -/
  | refl (x : Name) : Joined modules src srcFind x x
  /-- A name is joined to whatever a name linked to it is joined to. -/
  | step {x m y : Name} : Linked modules src srcFind x m → Joined modules src srcFind m y →
      Joined modules src srcFind x y

/-- A name `linkedIn` gives is `Linked`. -/
theorem linkedIn_sound {modules : Array ModuleData} {inside : Nat → Bool} {src : Name}
    {srcFind : Name → Option ConstantInfo} {x y : Name}
    (h : y ∈ linkedIn (linksOf modules inside) src srcFind x) :
    Linked modules src srcFind x y := by
  unfold linkedIn at h
  unfold Linked
  rw [Array.mem_filter, Array.mem_append] at h
  obtain ⟨h, hp⟩ := h
  refine ⟨hp, ?_⟩
  revert h
  cases srcFind x with
  | none =>
    intro h
    rcases h with h | h
    · simp at h
    · exact .inr (refers_of_before h)
  | some a =>
    intro h
    rcases h with h | h
    · exact .inl ⟨a, rfl, h⟩
    · exact .inr (refers_of_before h)

/-- **The names `linkedIn` gives from a name `DeclaredIn` the accepted modules are exactly the
`Linked` ones**, when the accepted modules `Covers` the references. -/
theorem mem_linkedIn {modules : Array ModuleData} {inside : Nat → Bool}
    (hcovers : Covers modules inside) {src : Name} {srcFind : Name → Option ConstantInfo}
    {x y : Name} (hx : DeclaredIn modules inside x) :
    y ∈ linkedIn (linksOf modules inside) src srcFind x ↔ Linked modules src srcFind x y := by
  unfold linkedIn Linked
  rw [Array.mem_filter, Array.mem_append, mem_before hcovers hx]
  cases srcFind x with
  | none =>
    simp only [Array.not_mem_empty, false_or, reduceCtorEq, false_and, exists_false]
    exact And.comm
  | some c => simp only [Option.some.injEq, exists_eq_left']; exact And.comm

/-- A name `linkedIn` gives is one of `namesIn`, for constants `srcFind` from accepted modules. -/
theorem linkedIn_mem_namesIn {modules : Array ModuleData} {inside : Nat → Bool} {src : Name}
    {srcFind : Name → Option ConstantInfo}
    (hfind : ∀ x a, srcFind x = some a →
      ∃ j data, modules[j]? = some data ∧ inside j = true ∧ a ∈ data.constants)
    {x y : Name} (h : y ∈ linkedIn (linksOf modules inside) src srcFind x) :
    y ∈ namesIn modules inside := by
  unfold linkedIn at h
  rw [Array.mem_filter, Array.mem_append] at h
  obtain ⟨h, -⟩ := h
  revert h
  cases ha : srcFind x with
  | none =>
    intro h
    rcases h with h | h
    · simp at h
    · exact before_mem_namesIn h
  | some a =>
    intro h
    rcases h with h | h
    · obtain ⟨j, data, hdata, hin, hamem⟩ := hfind x a ha
      exact used_mem_namesIn hdata hin hamem h
    · exact before_mem_namesIn h

/-- A path along `linkedIn` through names `DeclaredIn` the accepted modules is a `Joined` chain:
`hinside` holds of each name the path from `x` can reach. -/
theorem reach_linkedIn_iff {modules : Array ModuleData} {inside : Nat → Bool}
    (hcovers : Covers modules inside) {src : Name} {srcFind : Name → Option ConstantInfo}
    {x y : Name}
    (hinside : ∀ z, Reach (linkedIn (linksOf modules inside) src srcFind) x z →
      DeclaredIn modules inside z) :
    Reach (linkedIn (linksOf modules inside) src srcFind) x y ↔ Joined modules src srcFind x y := by
  constructor
  · intro h
    clear hinside
    induction h with
    | refl => exact .refl _
    | step hm _ ih => exact .step (linkedIn_sound hm) ih
  · intro h
    revert hinside
    induction h with
    | refl => exact fun _ => .refl _
    | step hm _ ih =>
      intro hinside
      have hm' := (mem_linkedIn hcovers (hinside _ (.refl _))).mpr hm
      exact .step hm' (ih fun z hz => hinside z (.step hm' hz))

/-- The block of the copy `c` in the module `src` whose constants `srcFind` gives by name: the names
private to `src` joined, through names private to `src`, to one that `c` refers to. -/
def blockOf (links : Links) (src : Name) (srcFind : Name → Option ConstantInfo)
    (c : ConstantInfo) : Std.HashSet Name :=
  links.closure (linkedIn links src srcFind) ((successorsOf c).toList.filter (privateTo src))

/-- `y` is in the block of `c`: it is `Joined` to a name private to `src` that `c` refers to. -/
def InBlock (modules : Array ModuleData) (src : Name) (srcFind : Name → Option ConstantInfo)
    (c : ConstantInfo) (y : Name) : Prop :=
  ∃ s ∈ successorsOf c, privateTo src s = true ∧ Joined modules src srcFind s y

/-- Every name of `blockOf` is in the block (`InBlock`). -/
theorem blockOf_sound {modules : Array ModuleData} {inside : Nat → Bool} {src : Name}
    {srcFind : Name → Option ConstantInfo} {c : ConstantInfo} {y : Name}
    (h : y ∈ blockOf (linksOf modules inside) src srcFind c) : InBlock modules src srcFind c y := by
  obtain ⟨s, hs, hr⟩ := closure_sound h
  obtain ⟨hs', hp⟩ := List.mem_filter.mp hs
  refine ⟨s, Array.mem_toList_iff.mp hs', hp, ?_⟩
  clear h hs hs' hp
  induction hr with
  | refl => exact .refl _
  | step hm _ ih => exact .step (linkedIn_sound hm) ih

/-- **For a constant `c` of an accepted module and constants `srcFind` from accepted modules,
`blockOf` holds exactly the names `InBlock` admits**, when each name it holds is `DeclaredIn` the
accepted modules and they `Covers` the references. -/
theorem mem_blockOf {modules : Array ModuleData} {inside : Nat → Bool}
    (hcovers : Covers modules inside) {src : Name} {srcFind : Name → Option ConstantInfo}
    {c : ConstantInfo}
    (hc : ∃ j data, modules[j]? = some data ∧ inside j = true ∧ c ∈ data.constants)
    (hfind : ∀ x a, srcFind x = some a →
      ∃ j data, modules[j]? = some data ∧ inside j = true ∧ a ∈ data.constants)
    (hinside : ∀ z, z ∈ blockOf (linksOf modules inside) src srcFind c →
      DeclaredIn modules inside z) {y : Name} :
    y ∈ blockOf (linksOf modules inside) src srcFind c ↔ InBlock modules src srcFind c y := by
  obtain ⟨j, data, hdata, hin, hcd⟩ := hc
  have closure : ∀ z, z ∈ blockOf (linksOf modules inside) src srcFind c ↔
      ∃ s ∈ (successorsOf c).toList.filter (privateTo src),
        Reach (linkedIn (linksOf modules inside) src srcFind) s z := fun z =>
    mem_closure (fun _ hs => used_mem_namesIn hdata hin hcd
        (Array.mem_toList_iff.mp (List.mem_filter.mp hs).1))
      (fun _ _ hz => linkedIn_mem_namesIn hfind hz)
  rw [closure y]
  unfold InBlock
  constructor
  · rintro ⟨s, hs, hr⟩
    obtain ⟨hs', hp⟩ := List.mem_filter.mp hs
    exact ⟨s, Array.mem_toList_iff.mp hs', hp, (reach_linkedIn_iff hcovers
      (fun z hz => hinside z ((closure z).mpr ⟨s, hs, hz⟩))).mp hr⟩
  · rintro ⟨s, hs, hp, hj⟩
    have hs' : s ∈ (successorsOf c).toList.filter (privateTo src) :=
      List.mem_filter.mpr ⟨Array.mem_toList_iff.mpr hs, hp⟩
    exact ⟨s, hs', (reach_linkedIn_iff hcovers
      (fun z hz => hinside z ((closure z).mpr ⟨s, hs', hz⟩))).mpr hj⟩

/-- Whether `x`, a name of a block, is renamed with the copy: it is not private to `dst`, `alone`
(declared by `src` alone) and `fixed` accept it, `fixed` accepts its renamed name, and its constant
in `src` is `renamedTo` the constant `dstFind` gives under the renamed name. -/
def renameable (src dst : Name) (fixed alone : Name → Bool)
    (srcFind dstFind : Name → Option ConstantInfo) (x : Name) : Bool :=
  !privateTo dst x && alone x && fixed x && fixed (renameName src dst x) &&
    match srcFind x, dstFind (renameName src dst x) with
    | some a, some b => renamedTo src dst a b
    | _, _ => false

/-- `x` is not private to `dst`, `alone` and `fixed` hold of it, `fixed` holds of its renamed
name, and its constant in `src` is `RenamedTo` the constant of `dst` under the renamed name. -/
def Renameable (src dst : Name) (fixed alone : Name → Prop)
    (srcFind dstFind : Name → Option ConstantInfo) (x : Name) : Prop :=
  privateTo dst x = false ∧ alone x ∧ fixed x ∧ fixed (renameName src dst x) ∧
    ∃ a b, srcFind x = some a ∧ dstFind (renameName src dst x) = some b ∧ RenamedTo src dst a b

/-- `renameable` decides `Renameable` for tests that decide `fixed` and `alone`. -/
theorem renameable_iff {src dst : Name} {fixedB aloneB : Name → Bool} {fixed alone : Name → Prop}
    (hfixed : ∀ n, fixedB n = true ↔ fixed n) (halone : ∀ n, aloneB n = true ↔ alone n)
    {srcFind dstFind : Name → Option ConstantInfo} {x : Name} :
    renameable src dst fixedB aloneB srcFind dstFind x = true ↔
      Renameable src dst fixed alone srcFind dstFind x := by
  unfold renameable Renameable
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, hfixed, halone, and_assoc]
  cases srcFind x <;> cases dstFind (renameName src dst x) <;> simp [renamedTo_iff]

/-- `z` is in the block of `c` or is the renamed name of a name there. -/
def InJoined (modules : Array ModuleData) (src dst : Name) (srcFind : Name → Option ConstantInfo)
    (c : ConstantInfo) (z : Name) : Prop :=
  InBlock modules src srcFind c z ∨ ∃ y, InBlock modules src srcFind c y ∧ renameName src dst y = z

/-- Whether `c`, the copy of `n` in the module `src`, is the copy `r` of `dst` renamed, so that
reuse may hold either: the two are theorems Lean's import accepts together (`sameTheorem`), `c` is
`renamedTo` `r`, every name of the block of `c` (`blockOf`) is `renameable`, and each name of the
block or renamed from it (the joined names) reaches no `n` (`reachesIn` over `above`, the names
that reach `n` in one or more steps) and is referred to only by constants named `n` or by joined
names (`Links.before`). `renamedCopy_iff` states the decision.

Why reuse gives the same results with renamed copies as with identical ones. Let `σ` be
`renameName src dst` and `B` the block of `c`. Whether a module is reused or replayed changes only
which loaded copy of a name the replayed kernel holds (`copiesAgree`), so it can hold `c` under `n`
where a replay would hold `r`, or the reverse. Take two kernel environments that hold loaded
copies and differ only under `n`, the one holding `r` and the other `c`; any two environments
holding loaded copies are joined by such steps, one name at a time, through the attributed copy.
Let `τ` exchange each name of `B` with its name under `σ` and fix every other name: a bijection,
since `σ` replaces one prefix by another and no name of `B` is private to `dst`.

* `τ` carries the first environment onto the second, constant by constant, in each field the
  kernel reads: the name, the universe parameters, the type and the value, and the hints and
  safety of a definition. Under `n`, `r` renamed back is `c`. Under a name of `B`, its only copy
  (`alone`) is renamed into the constant of `dst` under the new name, which renames back into it,
  and both refer, among the names private to their modules, only to joined names. Every other
  constant refers to no joined name (the test on `Links.before`, which meets every constant that
  refers to a joined name when the modules outside the owned ones meet `ImportScoped`,
  `mem_before`), so `τ` fixes it. The field `all`
  of a theorem or definition, its mutual block, can differ, since `renameConstant` renames each
  name private to `src` there and `τ` only the names of `B`; the kernel does not read it, and the
  searches below read only types and values (`successorsOf`).
* The kernel reads a constant's name only to look the constant up, to compare it with another
  constant's name or a fixed name of Lean's core (none of them private), to hash it for caches
  keyed by equality, and to label diagnostics. It runs no compiled code: Lean v4.35.0 removed its
  native reduction with the constants `Lean.reduceBool` and `Lean.reduceNat`. So its check of a
  declaration `d` in the first environment is, name for name under `τ`, its check of `τ d` in the
  second, with the same verdict.
* A declaration that is not joined and is not a copy of `n` refers to no joined name, so `τ d` is
  `d`. If it reaches `n`, it reaches no constant named `Lean.reduceBool` or `Lean.reduceNat`
  (`uniformUpToPrivate`), a condition kept from Lean v4.34.1, whose kernel ran compiled code for
  the two, and the previous point gives its check the same verdict. If it does not reach `n`,
  both environments hold the same constant under every name its check reads: those it reaches and
  those that `kernelNames` reach, none of which reaches `n`.
* A joined declaration reaches no `n`, and neither does a copy of `n`, since `n` lies on no cycle
  (`uniformUpToPrivate`). Both environments hold the same constant under every name its check
  reads.

So every declaration receives the same verdict in both environments. The searches of the axioms and
assumptions each owned declaration reaches (`validate`), and the circularity and axiom tests of
`checkProof`, follow references through the held constants, and `τ` maps the names reached in the
one environment onto those reached in the other. A name of `B` and its name under `σ` are theorems
or safe definitions with no role (`fixed`), so the two reach the same axioms and roles.
`checkShared`, `checkOwn` and `checkKept` compare with `sameTheorem` and `identical`: a copy that is
not `identical` to the held constant has its proof checked by `checkProof`, which then reaches the
held constant's axioms by the previous sentence.

Assumes:
- Lean v4.35.0, `src/lean/Lean/Meta/Match/MatchEqs.lean:143-155`: the splitter and the match
  equations of a `match` are realized under `mkPrivateName` of the module being elaborated, the
  name private to that module (`src/lean/Lean/Modifiers.lean:23-26`, with `privatePrefix` as
  `src/lean/Lean/PrivateName.lean:27-30` builds it), in each module that needs them
  (`realizeConst`, `src/lean/Lean/Environment.lean:2710-2761`). This is why such copies arise; the
  decision does not rest on it.
- Lean v4.35.0, `src/lean/Lean/Util/ReplaceExpr.lean:16-20` with `src/kernel/replace_fn.cpp:97-145`
  (trusted: the C++ is not modeled): `Expr.replace f e` returns `f`'s result for a subterm where
  `f` returns one, keeps a constant, sort, literal or variable where it returns none, and
  otherwise rebuilds the node from its children, keeping the structure name and index of a
  projection. So `renameExpr` renames exactly the constants private to `src`, and the names a
  renamed constant refers to are those of the original with `σ` applied.
- Lean v4.35.0, `src/lean/Lean/Util/FoldConsts.lean:67-74` and `src/kernel` (trusted): the kernel's
  check of a declaration reads a constant only under a name that occurs in the declaration or in
  a constant it read (the names `ConstantInfo.getUsedConstantsAsSet` gives, `successorsOf`), under
  a name of `kernelNames`, or as the recursor of an inductive type it read, whose rules refer only
  to recursors of that type's block and to the constants of its constructors' types. No name of
  `kernelNames` is a theorem, a name private to a module, or `Lean.reduceBool` or
  `Lean.reduceNat`. A recursor is neither primitive and can have a name private to a module (the
  recursor of a private inductive type, `src/kernel/inductive.cpp:22-24` and `812-817`), but it
  is neither a theorem nor a definition: it is no copy of `n`, which `sameTheorem` admits only as
  a theorem, and no joined name, whose constant `renameConstant` renames only as a theorem or a
  safe definition and `identical` relates only to a constant of the same kind.
- Lean v4.35.0, `src/lean/Lean/Declaration.lean:124-130` and `144-146` (trusted): the kernel does
  not read the field `all` of a definition or a theorem: `src/kernel/declaration.h:104-146` gives
  `definition_val` and `theorem_val` no accessor of it, and `get_all` is read only for inductive
  types (`inductive.cpp:1100` and `1197`).
- Lean v4.35.0, `src/kernel/type_checker.cpp` (trusted): the kernel reduces no constant by running
  compiled code. Lean v4.35.0 removed `reduce_native` with its calls in `whnf` and
  `is_def_eq_core`, and the constants `Lean.reduceBool` and `Lean.reduceNat` from
  `src/Init/Core.lean`, so a module can declare a constant of either name only as an ordinary one.
- Lean v4.35.0, `src/kernel` (trusted): `const_name` and `is_constant` with a name, the kernel's
  access to the name of a constant, appear in `declaration.cpp:153`, `177-178` and `196-197`,
  `expr.cpp:351`, `expr.h:249-251` and `366-371`, `expr_eq_fn.cpp:83`, `inductive.cpp:55-57`,
  `91-118`, `147-157`, `315-317`, `414-416`, `922-966`, `1026-1072` and `1227`, `inductive.h:36`,
  `68`, `81-82` and `126-127`, `instantiate.cpp:238`, `quot.h:41-83` and
  `type_checker.cpp:102-116`, `254-256`, `425-427`, `529-530`, `557-566`, `686`, `858-859`,
  `1123-1125`, `1142-1143` and `1170`. Each looks the constant up, compares its name with
  another constant's name or a fixed name of Lean's core, rebuilds the constant with other
  universe levels, or prints the name, with one exception: `inductive.cpp:924` and `966` derive
  the names of the auxiliary types of a nested inductive declaration from names of inductive
  types, which are neither theorems nor definitions, and `1227` tests a name against the reserved
  prefix `_nested`, which no private name has. -/
def renamedCopy (links : Links) (src dst n : Name) (fixed alone : Name → Bool)
    (srcFind dstFind : Name → Option ConstantInfo) (above : Std.HashSet Name)
    (c r : ConstantInfo) : Bool :=
  sameTheorem r c && renamedTo src dst c r &&
    let block := blockOf links src srcFind c
    let joined := Std.HashSet.ofList (block.toList ++ block.toList.map (renameName src dst))
    block.toList.all (renameable src dst fixed alone srcFind dstFind) &&
      joined.toList.all fun z => !reachesIn above n z &&
        (links.before z).all fun x => x == n || joined.contains x

/-- `r` and `c` are theorems Lean's import accepts together (`SameTheorem`), `c` is `RenamedTo`
`r`, every name of the block of `c` is `Renameable`, and every joined name reaches no `n` and is
referred to only by constants named `n` or by joined names. -/
def RenamedCopy (modules : Array ModuleData) (src dst n : Name) (fixed alone : Name → Prop)
    (srcFind dstFind : Name → Option ConstantInfo) (c r : ConstantInfo) : Prop :=
  SameTheorem r c ∧ RenamedTo src dst c r ∧
    (∀ y, InBlock modules src srcFind c y → Renameable src dst fixed alone srcFind dstFind y) ∧
    ∀ z, InJoined modules src dst srcFind c z →
      ¬ Leads modules z n ∧ ∀ x, Refers modules x z → x = n ∨ InJoined modules src dst srcFind c x

/-- **`renamedCopy` over the references of the accepted modules accepts exactly the copies that
`RenamedCopy` relates**, when the accepted modules `Covers` the references, for a copy `c` of an
accepted module, constants `srcFind` from accepted modules, `dstFind` and `alone` that give only
names `DeclaredIn` them, `above` the names that reach `n` in one or more steps, and tests that
decide `fixed` and `alone`. Each name of a block that `renamedCopy` accepts is `alone`, so the
search over the references meets every constant that refers to a joined name. -/
theorem renamedCopy_iff {modules : Array ModuleData} {src dst n : Name}
    {fixedB aloneB : Name → Bool} {fixed alone : Name → Prop}
    (hfixed : ∀ n, fixedB n = true ↔ fixed n) (halone : ∀ n, aloneB n = true ↔ alone n)
    {inside : Nat → Bool} (hcovers : Covers modules inside)
    {srcFind dstFind : Name → Option ConstantInfo} {above : Std.HashSet Name} {c r : ConstantInfo}
    (hc : ∃ j data, modules[j]? = some data ∧ inside j = true ∧ c ∈ data.constants)
    (hfind : ∀ x a, srcFind x = some a →
      ∃ j data, modules[j]? = some data ∧ inside j = true ∧ a ∈ data.constants)
    (hdst : ∀ x b, dstFind x = some b → DeclaredIn modules inside x)
    (hlone : ∀ x, alone x → DeclaredIn modules inside x)
    (habove : ∀ x, x ∈ above ↔ ∃ m, Refers modules m n ∧ Leads modules x m) :
    renamedCopy (linksOf modules inside) src dst n fixedB aloneB srcFind dstFind above c r = true ↔
      RenamedCopy modules src dst n fixed alone srcFind dstFind c r := by
  -- Once every name of the block is renameable, `blockOf` gives the block and every joined name
  -- is `DeclaredIn` the accepted modules.
  have settle : (∀ y, InBlock modules src srcFind c y →
      Renameable src dst fixed alone srcFind dstFind y) →
      ∀ y, y ∈ blockOf (linksOf modules inside) src srcFind c ↔ InBlock modules src srcFind c y :=
    fun hren _ => mem_blockOf hcovers hc hfind (fun z hz => hlone z (hren z (blockOf_sound hz)).2.1)
  have declared : (∀ y, InBlock modules src srcFind c y →
      Renameable src dst fixed alone srcFind dstFind y) →
      ∀ z, InJoined modules src dst srcFind c z → DeclaredIn modules inside z := by
    rintro hren z (hz | ⟨y, hy, rfl⟩)
    · exact hlone z (hren z hz).2.1
    · obtain ⟨-, -, -, -, -, b, -, hb, -⟩ := hren y hy
      exact hdst _ b hb
  have mem_joined : ∀ z, z ∈ Std.HashSet.ofList
      ((blockOf (linksOf modules inside) src srcFind c).toList ++
        (blockOf (linksOf modules inside) src srcFind c).toList.map (renameName src dst)) ↔
      z ∈ blockOf (linksOf modules inside) src srcFind c ∨
        ∃ y, y ∈ blockOf (linksOf modules inside) src srcFind c ∧ renameName src dst y = z := by
    intro z
    simp only [Std.HashSet.mem_ofList, List.contains_iff_mem, List.mem_append,
      Std.HashSet.mem_toList, List.mem_map]
  have joined : (∀ y, y ∈ blockOf (linksOf modules inside) src srcFind c ↔
      InBlock modules src srcFind c y) →
      ∀ z, (z ∈ blockOf (linksOf modules inside) src srcFind c ∨
        ∃ y, y ∈ blockOf (linksOf modules inside) src srcFind c ∧ renameName src dst y = z) ↔
      InJoined modules src dst srcFind c z := fun hblock z => by
    unfold InJoined
    simp only [hblock]
  have reach : ∀ z, reachesIn above n z = false ↔ ¬ Leads modules z n := fun z => by
    rw [← reachesIn_iff habove]
    cases reachesIn above n z <;> simp
  unfold renamedCopy RenamedCopy
  simp only [Bool.and_eq_true, sameTheorem_iff, renamedTo_iff, List.all_eq_true,
    Std.HashSet.mem_toList, renameable_iff hfixed halone, Bool.not_eq_eq_eq_not,
    Bool.not_true, Array.all_eq_true', Bool.or_eq_true, beq_iff_eq, Std.HashSet.contains_iff_mem,
    mem_joined, reach]
  constructor
  · rintro ⟨⟨hsame, hto⟩, hren, hjoin⟩
    have hblock : ∀ y, y ∈ blockOf (linksOf modules inside) src srcFind c ↔
        InBlock modules src srcFind c y :=
      fun _ => mem_blockOf hcovers hc hfind (fun z hz => hlone z (hren z hz).2.1)
    have hren' : ∀ y, InBlock modules src srcFind c y →
        Renameable src dst fixed alone srcFind dstFind y := fun y hy => hren y ((hblock y).mpr hy)
    refine ⟨hsame, hto, hren', fun z hz => ?_⟩
    obtain ⟨hnot, hrefs⟩ := hjoin z ((joined (settle hren') z).mpr hz)
    refine ⟨hnot, fun x hx => ?_⟩
    rcases hrefs x ((mem_before hcovers (declared hren' z hz)).mpr hx) with rfl | hx'
    · exact .inl rfl
    · exact .inr ((joined (settle hren') x).mp hx')
  · rintro ⟨hsame, hto, hren, hjoin⟩
    have hblock := settle hren
    refine ⟨⟨hsame, hto⟩, fun y hy => hren y ((hblock y).mp hy), fun z hz => ?_⟩
    have hz' := (joined hblock z).mp hz
    obtain ⟨hnot, hrefs⟩ := hjoin z hz'
    refine ⟨hnot, fun x hx => ?_⟩
    rcases hrefs x ((mem_before hcovers (declared hren z hz')).mp hx) with rfl | hx'
    · exact .inl rfl
    · exact .inr ((joined hblock x).mpr hx')

/-- The constants of a module's data by name. -/
def constantsByName (data : ModuleData) : Std.HashMap Name ConstantInfo :=
  data.constants.foldl (fun index info => index.insert info.name info) {}

/-- `constantsByName` gives under each name a constant of the module's data with that name. -/
theorem constantsByName_sound {data : ModuleData} {n : Name} {y : ConstantInfo}
    (h : (constantsByName data)[n]? = some y) : y ∈ data.constants ∧ y.name = n := by
  unfold constantsByName at h
  rw [← Array.foldl_toList] at h
  suffices step : ∀ (rest : List ConstantInfo) (index : Std.HashMap Name ConstantInfo),
      (∀ n y, index[n]? = some y → y ∈ data.constants ∧ y.name = n) →
      (∀ x ∈ rest, x ∈ data.constants) → ∀ n y,
      (rest.foldl (fun index info => index.insert info.name info) index)[n]? = some y →
        y ∈ data.constants ∧ y.name = n from
    step data.constants.toList {} (by simp) (fun x hx => Array.mem_toList_iff.mp hx) n y h
  intro rest
  induction rest with
  | nil => intro index hindex _; exact hindex
  | cons head rest ih =>
    intro index hindex hrest
    simp only [List.foldl_cons]
    refine ih _ (fun n y hn => ?_) (fun x hx => hrest x (List.mem_cons_of_mem _ hx))
    rw [Std.HashMap.getElem?_insert] at hn
    split at hn
    · rename_i heq
      obtain rfl := Option.some.inj hn
      exact ⟨hrest _ List.mem_cons_self, beq_iff_eq.mp heq⟩
    · exact hindex n y hn

/-- Whether every copy of `n` is the copy `r` of the module `n` is attributed to or a copy that
`related` relates to it, in that module and in each of the name's `others`. `related` receives the
index, the data and the name of the copy's module, the name of `r`'s module and its constants by
name, the copy and `r`. `uniformBy_iff` states the decision. -/
def uniformBy (modules : Array ModuleData) (names : Array Name) (attributed : Name → Option Nat)
    (dups : Duplicates)
    (related : Nat → ModuleData → Name → Name → Std.HashMap Name ConstantInfo → ConstantInfo →
      ConstantInfo → Bool)
    (n : Name) : Bool :=
  match attributed n with
  | none => false
  | some i =>
    match modules[i]?, names[i]? with
    | some reference, some dst =>
      match reference.constants.find? (·.name == n) with
      | none => false
      | some r =>
        let index := constantsByName reference
        (i :: (dups.others.getD n #[]).toList).all fun j =>
          match modules[j]?, names[j]? with
          | some data, some src =>
            data.constants.all fun c =>
              c.name != n || identical r c || related j data src dst index c r
          | _, _ => false
    | _, _ => false

/-- The module `n` is attributed to has data and a name and declares `n`, with first copy `r`
(`Array.find?`), and every module that declares `n` has data and a name and every copy of `n` it
holds is `Identical` to `r` or `Related` to it. -/
def UniformBy (modules : Array ModuleData) (names : Array Name) (attributed : Name → Option Nat)
    (Related : Nat → ModuleData → Name → Name → Std.HashMap Name ConstantInfo → ConstantInfo →
      ConstantInfo → Prop)
    (n : Name) : Prop :=
  ∃ i reference dst r, attributed n = some i ∧ modules[i]? = some reference ∧
    names[i]? = some dst ∧ reference.constants.find? (·.name == n) = some r ∧
    ∀ j, Declares modules j n → ∃ data src, modules[j]? = some data ∧ names[j]? = some src ∧
      ∀ c ∈ data.constants, c.name = n →
        Identical r c ∨ Related j data src dst (constantsByName reference) c r

/-- **`uniformBy` over the pass of `duplicatesOf` accepts exactly a name that `UniformBy` admits**,
for a `related` test that decides `Related` on each copy of `n` in a loaded module, against the
copy `r` of the module `n` is attributed to, with that module's constants by name. -/
theorem uniformBy_iff {find : Name → Option ConstantInfo} {attributed : Name → Option Nat}
    {modules : Array ModuleData} {names : Array Name}
    {related : Nat → ModuleData → Name → Name → Std.HashMap Name ConstantInfo → ConstantInfo →
      ConstantInfo → Bool}
    {Related : Nat → ModuleData → Name → Name → Std.HashMap Name ConstantInfo → ConstantInfo →
      ConstantInfo → Prop}
    {n : Name}
    (hrelated : ∀ i reference j data src dst c r, attributed n = some i →
      modules[i]? = some reference → r ∈ reference.constants → r.name = n →
      modules[j]? = some data → c ∈ data.constants → c.name = n →
      (related j data src dst (constantsByName reference) c r = true ↔
        Related j data src dst (constantsByName reference) c r)) :
    uniformBy modules names attributed (duplicatesOf find attributed modules) related n = true ↔
      UniformBy modules names attributed Related n := by
  unfold uniformBy UniformBy
  cases hattr : attributed n with
  | none => simp
  | some i =>
    cases hmod : modules[i]? with
    | none => simp [hmod]
    | some reference =>
      cases hname : names[i]? with
      | none => simp [hmod, hname]
      | some dst =>
        cases hr : reference.constants.find? (·.name == n) with
        | none => simp [hmod, hname, hr]
        | some r =>
          have hrmem : r ∈ reference.constants := Array.mem_of_find?_eq_some hr
          have hrname : r.name = n :=
            beq_iff_eq.mp (Array.find?_some (p := fun (x : ConstantInfo) => x.name == n) hr)
          have hdecl : Declares modules i n := ⟨reference, hmod, r, hrmem, hrname⟩
          have copies : ∀ (j : Nat),
              (match modules[j]?, names[j]? with
                | some data, some src =>
                  data.constants.all fun c =>
                    c.name != n || identical r c ||
                      related j data src dst (constantsByName reference) c r
                | _, _ => false) = true ↔
              ∃ data src, modules[j]? = some data ∧ names[j]? = some src ∧
                ∀ c ∈ data.constants, c.name = n →
                  Identical r c ∨ Related j data src dst (constantsByName reference) c r := by
            intro j
            cases hdata : modules[j]? with
            | none => simp
            | some data =>
              cases names[j]? with
              | none => simp
              | some src =>
                have hrel := fun c hc hcn =>
                  hrelated i reference j data src dst c r hattr hmod hrmem hrname hdata hc hcn
                simp only [Array.all_eq_true', Bool.or_eq_true, bne_iff_ne, ne_eq, identical_iff,
                  Option.some.injEq, exists_and_left, exists_eq_left']
                constructor
                · intro h c hc hn
                  rcases h c hc with (h | h) | h
                  · exact absurd hn h
                  · exact .inl h
                  · exact .inr ((hrel c hc hn).mp h)
                · intro h c hc
                  by_cases hn : c.name = n
                  · rcases h c hc hn with h | h
                    · exact .inl (.inr h)
                    · exact .inr ((hrel c hc hn).mpr h)
                  · exact .inl (.inl hn)
          simp only [hmod, hname, hr, List.all_eq_true, List.mem_cons, Array.mem_toList_iff,
            copies]
          constructor
          · intro h
            refine ⟨i, reference, dst, r, rfl, hmod, hname, hr, fun j hj => ?_⟩
            by_cases hji : attributed n = some j
            · rw [hattr] at hji
              obtain rfl := Option.some.inj hji
              exact h _ (.inl rfl)
            · exact h j (.inr (mem_others_iff.mpr ⟨hj, hji⟩))
          · rintro ⟨i', reference', dst', r', hi, hm, hn, hr', h⟩
            obtain rfl := Option.some.inj hi
            rw [hmod] at hm
            obtain rfl := Option.some.inj hm
            rw [hname] at hn
            obtain rfl := Option.some.inj hn
            rw [hr] at hr'
            obtain rfl := Option.some.inj hr'
            rintro j (rfl | hj)
            · exact h _ hdecl
            · exact h j (mem_others_iff.mp hj).1

/-- `UniformBy` holds of any weaker relation. -/
theorem UniformBy.mono {modules : Array ModuleData} {names : Array Name}
    {attributed : Name → Option Nat}
    {R₁ R₂ : Nat → ModuleData → Name → Name → Std.HashMap Name ConstantInfo → ConstantInfo →
      ConstantInfo → Prop}
    (weaker : ∀ j data src dst index c r, R₁ j data src dst index c r → R₂ j data src dst index c r)
    {n : Name} (h : UniformBy modules names attributed R₁ n) :
    UniformBy modules names attributed R₂ n := by
  obtain ⟨i, reference, dst, r, hi, hm, hn, hr, hall⟩ := h
  refine ⟨i, reference, dst, r, hi, hm, hn, hr, fun j hj => ?_⟩
  obtain ⟨data, src, hd, hs, hcopies⟩ := hall j hj
  exact ⟨data, src, hd, hs, fun c hc hcn =>
    (hcopies c hc hcn).imp id (weaker _ _ _ _ _ _ _)⟩

/-- Whether the name `x` is attributed to the module at index `j` and declared by no other. -/
def aloneIn (attributed : Name → Option Nat) (dups : Duplicates) (j : Nat) (x : Name) : Bool :=
  attributed x == some j && (dups.others.getD x #[]).isEmpty

/-- The name `x` is attributed to the module at index `j`, and every module that declares it is
that module. -/
def Alone (modules : Array ModuleData) (attributed : Name → Option Nat) (j : Nat) (x : Name) :
    Prop :=
  attributed x = some j ∧ ∀ k, Declares modules k x → k = j

/-- `aloneIn` over the pass of `duplicatesOf` decides `Alone`. -/
theorem aloneIn_iff {find : Name → Option ConstantInfo} {attributed : Name → Option Nat}
    {modules : Array ModuleData} {j : Nat} {x : Name} :
    aloneIn attributed (duplicatesOf find attributed modules) j x = true ↔
      Alone modules attributed j x := by
  unfold aloneIn Alone
  simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff]
  constructor
  · rintro ⟨hattr, hnone⟩
    refine ⟨hattr, fun k hdecl => Classical.byContradiction fun hne => ?_⟩
    have hmem : k ∈ (duplicatesOf find attributed modules).others.getD x #[] :=
      mem_others_iff.mpr ⟨hdecl, fun h => hne (Option.some.inj (hattr.symm.trans h)).symm⟩
    rw [hnone] at hmem
    simp at hmem
  · rintro ⟨hattr, honly⟩
    refine ⟨hattr, Array.eq_empty_iff_forall_not_mem.mpr fun k hmem => ?_⟩
    obtain ⟨hdecl, hne⟩ := mem_others_iff.mp hmem
    exact hne (by rw [honly k hdecl]; exact hattr)

/-- Whether every copy of `n` is the attributed module's copy or a theorem with the same
statement whose renaming into it `renamedTo` accepts, the shape `renamedCopy` starts from. Only a
`differing` name of this shape starts the computation of the region of the owned modules and the
reading of its references (`agreeing`). -/
def renamedShape (modules : Array ModuleData) (names : Array Name)
    (attributed : Name → Option Nat) (dups : Duplicates) (n : Name) : Bool :=
  uniformBy modules names attributed dups
    (fun _ _ src dst _ c r => sameTheorem r c && renamedTo src dst c r) n

/-- The tests of `uniformUpToPrivate` that read the references of the region (`links`), for `above`
the names that reach `n` in one or more steps (`aboveIn`): `n` is not among them, none of
`kernelNames` reaches `n`, and every copy is the attributed module's copy or a `renamedCopy` of it,
with the constants of each name of a block declared by that copy's module alone (`aloneIn`) and
`fixed`. -/
def renamedUniform (modules : Array ModuleData) (names : Array Name)
    (attributed : Name → Option Nat) (dups : Duplicates) (fixed : Name → Bool) (links : Links)
    (above : Std.HashSet Name) (n : Name) : Bool :=
  !above.contains n && kernelNames.all (fun x => !reachesIn above n x) &&
    uniformBy modules names attributed dups (fun j data src dst index c r =>
      renamedCopy links src dst n fixed (aloneIn attributed dups j) ((constantsByName data)[·]?)
        (index[·]?) above c r) n

/-- The names of `shaped` whose copies agree up to the names private to the modules that declare
them. First, for each name, the tests that read the references of the region (`renamedUniform`),
with the names that reach it (`aboveIn`). Last, no name that reaches it reaches `Lean.reduceBool`
or `Lean.reduceNat` (`nativeFree`), read from one search forward from the names that passed the
first tests and the names that reach them (`nativeReaching`), so a name that the first tests refuse
adds no name to its starts. `uniformUpToPrivate_iff` states the decision. -/
def uniformUpToPrivate (modules : Array ModuleData) (names : Array Name)
    (attributed : Name → Option Nat) (dups : Duplicates) (fixed : Name → Bool) (links : Links)
    (shaped : List Name) : List Name :=
  let renamed := (shaped.map fun n => (n, aboveIn links n)).filter fun e =>
    renamedUniform modules names attributed dups fixed links e.2 e.1
  let roots := renamed.flatMap fun e => e.1 :: e.2.toList
  let native := nativeReaching modules attributed dups
    (links.fuel + links.declared + 2 + roots.length) roots
  (renamed.filter fun e => nativeFree native e.2 e.1).map (·.1)

/-- A name `uniformUpToPrivate` accepts is a name of `shaped`. -/
theorem mem_of_uniformUpToPrivate {modules : Array ModuleData} {names : Array Name}
    {attributed : Name → Option Nat} {dups : Duplicates} {fixed : Name → Bool} {links : Links}
    {shaped : List Name} {n : Name}
    (h : n ∈ uniformUpToPrivate modules names attributed dups fixed links shaped) : n ∈ shaped := by
  unfold uniformUpToPrivate at h
  dsimp only at h
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp (List.mem_filter.mp (List.mem_filter.mp he).1).1
  exact hm

/-- `n` reaches no constant that refers to it, no name that reaches `n` reaches `Lean.reduceBool`
or `Lean.reduceNat` or is one of `kernelNames`, and every copy of `n` is the attributed module's
copy or a `RenamedCopy` of it from the copy's module, whose names of a block are `Alone` in that
module and `fixed`. -/
def UniformUpToPrivate (modules : Array ModuleData) (names : Array Name)
    (attributed : Name → Option Nat) (fixed : Name → Prop) (n : Name) : Prop :=
  ¬ (∃ m, Refers modules m n ∧ Leads modules n m) ∧
    (∀ d, Leads modules d n →
      ¬ ((Leads modules d `Lean.reduceBool ∨ Leads modules d `Lean.reduceNat) ∨
        d ∈ kernelNames)) ∧
    UniformBy modules names attributed (fun j data src dst index c r =>
      RenamedCopy modules src dst n fixed (Alone modules attributed j) ((constantsByName data)[·]?)
        (index[·]?) c r) n

/-- **`uniformUpToPrivate` over the pass of `duplicatesOf` and the references of the accepted
modules accepts exactly the names of `shaped` that `UniformUpToPrivate` admits**, when the accepted
modules `Covers` the references and every module that declares a name of `shaped` is accepted
(`DeclaredIn`). -/
theorem uniformUpToPrivate_iff {find : Name → Option ConstantInfo}
    {attributed : Name → Option Nat} {modules : Array ModuleData} {names : Array Name}
    {fixedB : Name → Bool} {fixed : Name → Prop} (hfixed : ∀ n, fixedB n = true ↔ fixed n)
    {inside : Nat → Bool} (hcovers : Covers modules inside) {shaped : List Name}
    (hshaped : ∀ m ∈ shaped, DeclaredIn modules inside m) {n : Name} (hshape : n ∈ shaped) :
    n ∈ uniformUpToPrivate modules names attributed (duplicatesOf find attributed modules) fixedB
        (linksOf modules inside) shaped ↔
      UniformUpToPrivate modules names attributed fixed n := by
  have hn := hshaped n hshape
  have habove : ∀ x, x ∈ aboveIn (linksOf modules inside) n ↔
      ∃ m, Refers modules m n ∧ Leads modules x m := fun _ => mem_aboveIn hcovers hn
  have reach : ∀ x, reachesIn (aboveIn (linksOf modules inside) n) n x = true ↔
      Leads modules x n := fun _ => reachesIn_iff habove
  have kernel : (∀ x ∈ kernelNames, reachesIn (aboveIn (linksOf modules inside) n) n x = false) ↔
      ∀ d, Leads modules d n → d ∉ kernelNames := by
    constructor
    · intro h d hd hk
      have := h d hk
      rw [← Bool.not_eq_true, reach] at this
      exact this hd
    · intro h x hx
      cases hr : reachesIn (aboveIn (linksOf modules inside) n) n x
      · rfl
      · exact absurd hx (h x ((reach x).mp hr))
  have uniform := uniformBy_iff (find := find) (attributed := attributed) (names := names) (n := n)
    (related := fun j data src dst index c r =>
      renamedCopy (linksOf modules inside) src dst n fixedB
        (aloneIn attributed (duplicatesOf find attributed modules) j) ((constantsByName data)[·]?)
        (index[·]?) (aboveIn (linksOf modules inside) n) c r)
    (Related := fun j data src dst index c r =>
      RenamedCopy modules src dst n fixed (Alone modules attributed j) ((constantsByName data)[·]?)
        (index[·]?) c r)
    fun i reference j data src dst c r hi hm hrm hrn hdata hc hcn =>
      have hj : inside j = true := hn j ⟨data, hdata, c, hc, hcn⟩
      renamedCopy_iff hfixed (fun _ => aloneIn_iff) hcovers ⟨j, data, hdata, hj, hc⟩
        (fun _ _ ha => ⟨j, data, hdata, hj, (constantsByName_sound ha).1⟩)
        (fun x b hb k hk => hcovers.shares i k x (hn i ⟨reference, hm, r, hrm, hrn⟩)
          ⟨reference, hm, b, (constantsByName_sound hb).1, (constantsByName_sound hb).2⟩ hk)
        (fun x ⟨_, honly⟩ k hk => by rw [honly k hk]; exact hj)
        habove
  have tests : renamedUniform modules names attributed (duplicatesOf find attributed modules)
      fixedB (linksOf modules inside) (aboveIn (linksOf modules inside) n) n = true ↔
      ¬ (∃ m, Refers modules m n ∧ Leads modules n m) ∧
        (∀ d, Leads modules d n → d ∉ kernelNames) ∧
        UniformBy modules names attributed (fun j data src dst index c r =>
          RenamedCopy modules src dst n fixed (Alone modules attributed j)
            ((constantsByName data)[·]?) (index[·]?) c r) n := by
    unfold renamedUniform
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      Std.HashSet.contains_eq_false_iff_not_mem, habove, List.all_eq_true]
    rw [kernel, uniform]
    exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩
  unfold uniformUpToPrivate
  dsimp only
  generalize hrenamed : List.filter (fun e => renamedUniform modules names attributed
    (duplicatesOf find attributed modules) fixedB (linksOf modules inside) e.2 e.1)
    (shaped.map fun n => (n, aboveIn (linksOf modules inside) n)) = renamed
  -- The pairs stay as variables `a b` until the projections of `(a, b)` are reduced (`dsimp only`):
  -- unifying `(a, aboveIn _ a).2` with `aboveIn _ a` would unfold `aboveIn` before `Prod.snd`.
  have mem : ∀ a b, (a, b) ∈ renamed ↔ a ∈ shaped ∧ b = aboveIn (linksOf modules inside) a ∧
      renamedUniform modules names attributed (duplicatesOf find attributed modules) fixedB
        (linksOf modules inside) b a = true := by
    intro a b
    rw [← hrenamed, List.mem_filter, List.mem_map]
    dsimp only
    constructor
    · rintro ⟨⟨m, hm, he⟩, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨hm, rfl, h⟩
    · rintro ⟨hm, rfl, h⟩
      exact ⟨⟨a, hm, rfl⟩, h⟩
  have roots : ∀ a b, (a, b) ∈ renamed → ∀ d ∈ a :: b.toList,
      d ∈ renamed.flatMap fun e => e.1 :: e.2.toList :=
    fun _ _ he _ hd => List.mem_flatMap.mpr ⟨_, he, hd⟩
  have native := nativeFree_iff (find := find) (attributed := attributed) hcovers habove
    (roots := renamed.flatMap fun e => e.1 :: e.2.toList)
    (fuel := (linksOf modules inside).fuel + (linksOf modules inside).declared + 2 +
      (renamed.flatMap fun e => e.1 :: e.2.toList).length)
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, he, ha⟩
    obtain ⟨he, hfree⟩ := List.mem_filter.mp he
    dsimp only at ha hfree
    subst ha
    obtain ⟨-, rfl, hrenamed'⟩ := (mem _ _).mp he
    obtain ⟨hcycle, hkernel, huniform⟩ := tests.mp hrenamed'
    have hnative :=
      (native (roots _ _ he) (by rw [fuel_linksOf.1, fuel_linksOf.2]; omega)).mp hfree
    exact ⟨hcycle, fun d hd h => h.elim (hnative d hd) (hkernel d hd), huniform⟩
  · rintro ⟨hcycle, h, huniform⟩
    have he := (mem n (aboveIn (linksOf modules inside) n)).mpr
      ⟨hshape, rfl, tests.mpr ⟨hcycle, fun d hd hk => h d hd (.inr hk), huniform⟩⟩
    refine ⟨_, List.mem_filter.mpr ⟨he, ?_⟩, rfl⟩
    dsimp only
    exact (native (roots _ _ he) (by rw [fuel_linksOf.1, fuel_linksOf.2]; omega)).mpr
      fun d hd hx => h d hd (.inl hx)

/-- Whether the module `n` is attributed to and each of its `others`, the other modules that
declare `n`, are named in `owned`. `declaredOwned_iff` states the decision. -/
def declaredOwned (names : Array Name) (attributed : Name → Option Nat) (dups : Duplicates)
    (owned : Std.HashSet Name) (n : Name) : Bool :=
  (attributed n).any (fun idx => names[idx]?.any owned.contains) &&
    (dups.others.getD n #[]).all fun idx => names[idx]?.any owned.contains

/-- Every module that declares `n` is named in `owned`. -/
def DeclaredOwned (modules : Array ModuleData) (names : Array Name) (owned : Std.HashSet Name)
    (n : Name) : Prop :=
  ∀ idx, Declares modules idx n → ∃ name, names[idx]? = some name ∧ name ∈ owned

/-- **`declaredOwned` over the pass of `duplicatesOf` accepts exactly a name whose attributed
module is named in `owned` and that `DeclaredOwned` admits.** -/
theorem declaredOwned_iff {find : Name → Option ConstantInfo} {attributed : Name → Option Nat}
    {modules : Array ModuleData} {names : Array Name} {owned : Std.HashSet Name} {n : Name} :
    declaredOwned names attributed (duplicatesOf find attributed modules) owned n = true ↔
      (∃ idx name, attributed n = some idx ∧ names[idx]? = some name ∧ name ∈ owned) ∧
        DeclaredOwned modules names owned n := by
  unfold declaredOwned DeclaredOwned
  simp only [Bool.and_eq_true, Array.all_eq_true', Option.any_eq_true,
    Std.HashSet.contains_iff_mem, mem_others_iff]
  constructor
  · rintro ⟨⟨idx, hattr, name, hname, howned⟩, hothers⟩
    refine ⟨⟨idx, name, hattr, hname, howned⟩, fun other hdecl => ?_⟩
    by_cases hother : attributed n = some other
    · rw [hattr] at hother
      obtain rfl := Option.some.inj hother
      exact ⟨name, hname, howned⟩
    · exact hothers other ⟨hdecl, hother⟩
  · rintro ⟨⟨idx, name, hattr, hname, howned⟩, hall⟩
    exact ⟨⟨idx, hattr, name, hname, howned⟩, fun other ⟨hdecl, _⟩ => hall other hdecl⟩

/-- The `differing` names of `dups` whose copies agree up to the names private to the modules
that declare them (`uniformUpToPrivate`), among the names that only modules named in `owned`
declare (`declaredOwned`). The region of `owned` (`regionOf`), the references of its constants
(`linksOf`) and the one search forward of `uniformUpToPrivate` (`nativeReaching`) are computed
only when some such name has the shape of a renamed copy (`renamedShape`), and then at most one
time in each call. The region is the least set of modules that holds the owned modules, each module
that imports one of the set and each module that shares a name with one of the set (`InRegion`),
and `linksOf` reads the references of no constant outside it. The search forward starts from the
names that pass the tests over the region and the names that reach them, and reads the copies of
each name it meets, in any loaded module: the dependency cone of those names bounds it, not the
region. So a name that a module outside `owned` declares, such as a name that only toolchain
modules declare, never starts these searches.
`agrees_iff` takes `ImportScoped` as a hypothesis: then the region covers every constant that
refers to a name the searches read backward (`covers_regionOf`).

Why the restriction to `owned` costs no reuse that Regula had before it read renamed copies: then
no `differing` name agreed. Agreement up to renaming serves only the reuse of an owned module,
through the names of its constants and references (`candidates`) and through the offer of a
replayed module (`ownedAgrees`). That offer already refuses a replayed module that holds a shared
copy of a name a module outside `owned` also declares, so in an environment that loads such a
module, the name leads to no reuse through the offer either. An environment that loads such a
module replays an owned module that holds a renamed copy of the name, even if an environment that
did not load it offered the owned module. -/
def agreeing (modules : Array ModuleData) (names : Array Name) (attributed : Name → Option Nat)
    (dups : Duplicates) (owned : Std.HashSet Name) (fixed : Name → Bool) : Std.HashSet Name :=
  let shaped := dups.differing.toList.filter fun n =>
    declaredOwned names attributed dups owned n && renamedShape modules names attributed dups n
  if shaped.isEmpty then {} else
    let links := linksOf modules (regionHas (regionOf modules names attributed dups owned))
    Std.HashSet.ofList (uniformUpToPrivate modules names attributed dups fixed links shaped)

/-- Whether the copies of `n` agree: `n` is outside `differing`, or in `agreeing`. -/
def agrees (dups : Duplicates) (agreeing : Std.HashSet Name) (n : Name) : Bool :=
  !dups.differing.contains n || agreeing.contains n

/-- Every copy of `n` is `Identical` to the constant `find` keeps (`Uniform`), or `n` is uniform up
to the names private to the modules that declare it (`UniformUpToPrivate`) and every module that
declares it is named in `owned` (`DeclaredOwned`). The last condition costs no reuse that `Uniform`
alone gave, and the offer of a replayed module requires it too (`ownedAgrees`); the docstring of
`agreeing` gives the argument and the case it leaves out. -/
def Agrees (find : Name → Option ConstantInfo) (modules : Array ModuleData) (names : Array Name)
    (attributed : Name → Option Nat) (owned : Std.HashSet Name) (fixed : Name → Prop) (n : Name) :
    Prop :=
  Uniform find modules n ∨
    UniformUpToPrivate modules names attributed fixed n ∧ DeclaredOwned modules names owned n

/-- **`agrees` over the pass of `duplicatesOf` accepts exactly a name that `Agrees` admits**, when
the modules outside `owned` meet `ImportScoped`. -/
theorem agrees_iff {find : Name → Option ConstantInfo} {attributed : Name → Option Nat}
    {modules : Array ModuleData} {names : Array Name} {owned : Std.HashSet Name}
    {fixedB : Name → Bool} {fixed : Name → Prop} (hfixed : ∀ n, fixedB n = true ↔ fixed n)
    (hscoped : ImportScoped modules names owned) {n : Name} :
    agrees (duplicatesOf find attributed modules)
        (agreeing modules names attributed (duplicatesOf find attributed modules) owned fixedB) n =
        true ↔
      Agrees find modules names attributed owned fixed n := by
  -- A name that is uniform up to private names, declared only by owned modules, passes the
  -- filter that precedes the references: its attributed module declares it, and it has the shape
  -- of a renamed copy.
  have shaped : UniformUpToPrivate modules names attributed fixed n →
      DeclaredOwned modules names owned n →
      (declaredOwned names attributed (duplicatesOf find attributed modules) owned n &&
        renamedShape modules names attributed (duplicatesOf find attributed modules) n) = true := by
    intro h hdecl
    obtain ⟨i, reference, -, r, hi, hm, -, hr, -⟩ := h.2.2
    obtain ⟨name, hname, howned⟩ := hdecl i ⟨reference, hm, r, Array.mem_of_find?_eq_some hr,
      beq_iff_eq.mp (Array.find?_some (p := fun (x : ConstantInfo) => x.name == n) hr)⟩
    rw [Bool.and_eq_true, declaredOwned_iff]
    refine ⟨⟨⟨i, name, hi, hname, howned⟩, hdecl⟩, ?_⟩
    unfold renamedShape
    rw [uniformBy_iff (Related := fun _ _ src dst _ c r =>
      sameTheorem r c = true ∧ renamedTo src dst c r = true)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => Iff.of_eq (Bool.and_eq_true _ _))]
    refine h.2.2.mono fun _ _ _ _ _ c r hrel => ?_
    exact ⟨(sameTheorem_iff _ _).mpr hrel.1, renamedTo_iff.mpr hrel.2.1⟩
  -- Every module that declares a name only owned modules declare is in the region.
  have inside : ∀ {m}, DeclaredOwned modules names owned m →
      DeclaredIn modules (regionHas (regionOf modules names attributed
        (duplicatesOf find attributed modules) owned)) m := fun hdecl k hk => by
    obtain ⟨name, hname, howned⟩ := hdecl k hk
    obtain ⟨data, hdata, -⟩ := hk
    exact regionHas_iff.mpr (.owned hdata hname howned)
  have hcovers := covers_regionOf (find := find) (attributed := attributed) hscoped
  unfold agrees agreeing Agrees
  by_cases hd : n ∈ (duplicatesOf find attributed modules).differing
  · have hnot : ¬ Uniform find modules n := fun hu => not_mem_differing_iff.mpr hu hd
    simp only [Std.HashSet.contains_iff_mem.mpr hd, Bool.not_true, Bool.false_or, hnot, false_or]
    split
    · rename_i hempty
      simp only [Std.HashSet.contains_empty, Bool.false_eq_true, false_iff]
      rintro ⟨h, hdecl⟩
      have hmem : n ∈ (duplicatesOf find attributed modules).differing.toList.filter fun n =>
          declaredOwned names attributed (duplicatesOf find attributed modules) owned n &&
            renamedShape modules names attributed (duplicatesOf find attributed modules) n :=
        List.mem_filter.mpr ⟨Std.HashSet.mem_toList.mpr hd, shaped h hdecl⟩
      rw [List.isEmpty_iff.mp hempty] at hmem
      simp at hmem
    · have hshaped : ∀ m ∈ (duplicatesOf find attributed modules).differing.toList.filter fun n =>
            declaredOwned names attributed (duplicatesOf find attributed modules) owned n &&
              renamedShape modules names attributed (duplicatesOf find attributed modules) n,
          DeclaredIn modules (regionHas (regionOf modules names attributed
            (duplicatesOf find attributed modules) owned)) m := by
        intro m hm
        have hs := (List.mem_filter.mp hm).2
        rw [Bool.and_eq_true, declaredOwned_iff] at hs
        exact inside hs.1.2
      simp only [Std.HashSet.contains_ofList, List.contains_iff_mem]
      constructor
      · intro h
        have hs := mem_of_uniformUpToPrivate h
        have hdecl := (List.mem_filter.mp hs).2
        rw [Bool.and_eq_true, declaredOwned_iff] at hdecl
        exact ⟨(uniformUpToPrivate_iff hfixed hcovers hshaped hs).mp h, hdecl.1.2⟩
      · rintro ⟨h, hdecl⟩
        exact (uniformUpToPrivate_iff hfixed hcovers hshaped
          (List.mem_filter.mpr ⟨Std.HashSet.mem_toList.mpr hd, shaped h hdecl⟩)).mpr h
  · simp only [Std.HashSet.contains_eq_false_iff_not_mem.mpr hd, Bool.not_false, Bool.true_or,
      true_iff]
    exact .inl (not_mem_differing_iff.mp hd)

/-- Whether a constant that a renamed copy renames may have the name `n`: `n` has no role in
`roles` and is outside `differing`. -/
def fixedIn (roles : Std.HashSet Name) (dups : Duplicates) (n : Name) : Bool :=
  !roles.contains n && !dups.differing.contains n

/-- `n` has no role in `roles`, and every copy of it is `Identical` to the constant `find` keeps
(`Uniform`). -/
def Fixed (roles : Std.HashSet Name) (find : Name → Option ConstantInfo)
    (modules : Array ModuleData) (n : Name) : Prop :=
  n ∉ roles ∧ Uniform find modules n

/-- `fixedIn` over the pass of `duplicatesOf` decides `Fixed`. -/
theorem fixedIn_iff {roles : Std.HashSet Name} {find : Name → Option ConstantInfo}
    {attributed : Name → Option Nat} {modules : Array ModuleData} (n : Name) :
    fixedIn roles (duplicatesOf find attributed modules) n = true ↔
      Fixed roles find modules n := by
  unfold fixedIn Fixed
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    Std.HashSet.contains_eq_false_iff_not_mem, not_mem_differing_iff]

/-! ### Witnesses of the exclusions

Lean v4.35.0 declares no `Lean.reduceBool`, and Lean refuses a second declaration of a name of
`kernelNames` in a module that imports `Init`, so these witnesses run `agrees` on module data
written here, not on modules Lean built. `W.Dst` and `W.Src` import `W.Base`, and each declares
a private `flag` and a copy of `W.lemma` whose proof applies a function of `W.Base` to that
`flag`, so the two copies differ only in the private name. `W.Use` imports `W.Src` and is not owned, so it is in the region
of the owned modules (`regionOf`), and `W.Base` is not. No witness module declares
`Lean.reduceBool`, `Bool` or `W.prove`: the forward search of `nativeReaching` meets such a name,
which is how it meets `Lean.reduceBool`, and follows no reference from it, since it has no copy.
These module data do not meet `ImportScoped`, since `W.Base` refers to `Bool`, so the `#guard`
commands observe `agrees` as it runs, not an instance of `agrees_iff`. The last witnesses run
`agrees` with and without `W.Src` among the owned modules. -/

/-- The theorem `n` of `True` with the proof `value`. -/
private def witnessTheorem (n : Name) (value : Expr) : ConstantInfo :=
  .thmInfo { name := n, levelParams := [], type := .const ``True [], value, all := [n] }

/-- The definition `n` of `Bool → Bool`, or of `Bool` with `flag`, with the value `value`. -/
private def witnessDefinition (n : Name) (flag : Bool) (value : Expr) : ConstantInfo :=
  let bool : Expr := .const ``Bool []
  let type := if flag then bool else .forallE `b bool bool .default
  .defnInfo
    { name := n, levelParams := [], type, value, hints := .abbrev, safety := .safe, all := [n] }

/-- The data of a module that imports the modules `imports` and declares `constants`. -/
private def witnessModule (imports : Array Name) (constants : Array ConstantInfo) : ModuleData :=
  { isModule := false, imports := imports.map fun m => { module := m },
    constNames := constants.map (·.name), constants, extraConstNames := #[], entries := #[] }

/-- Whether `agrees` accepts `W.lemma` when each copy applies `apply` to its module's `flag`,
`W.Src` also declares `extra`, `W.Use` declares `importer`, and the modules named in `owned` are
owned. `W.Base` declares `W.rb`, which applies `Lean.reduceBool`, and `W.keep`, which does not.
Each name is attributed to the first module that declares it, and the environment keeps the last
copy. -/
private def witnessAgrees (apply : Name) (extra : Array ConstantInfo)
    (owned : Array Name := #[`W.Dst, `W.Src]) (importer : Array ConstantInfo := #[]) : Bool :=
  let flag (m : Name) := mkPrivateNameCore m `flag
  let proof (m : Name) : Expr :=
    .app (.const `W.prove []) (.app (.const apply []) (.const (flag m) []))
  let copy (m : Name) := #[witnessDefinition (flag m) true (.const ``Bool.true []),
    witnessTheorem `W.lemma (proof m)]
  let base := #[
    witnessDefinition `W.rb false
      (.lam `b (.const ``Bool []) (.app (.const `Lean.reduceBool []) (.bvar 0)) .default),
    witnessDefinition `W.keep false (.lam `b (.const ``Bool []) (.bvar 0) .default)]
  let modules := #[witnessModule #[] base, witnessModule #[`W.Base] (copy `W.Dst),
    witnessModule #[`W.Base] (copy `W.Src ++ extra), witnessModule #[`W.Src] importer]
  let attributed (x : Name) := modules.findIdx? (·.constNames.contains x)
  let find (x : Name) := modules.reverse.findSome? (·.constants.find? (·.name == x))
  let dups := duplicatesOf find attributed modules
  agrees dups (agreeing modules #[`W.Base, `W.Dst, `W.Src, `W.Use] attributed dups
    (Std.HashSet.ofList owned.toList) (fixedIn {} dups)) `W.lemma

-- The copies agree when no name that reaches `W.lemma` reaches `Lean.reduceBool` and only the
-- copies refer to each `flag`.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard witnessAgrees `W.keep #[]
-- Native reduction through an alias in the copies: each copy reaches `Lean.reduceBool` through
-- `W.rb`, a constant outside the copies that `W.Base`, outside the region, declares.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard !witnessAgrees `W.rb #[]
-- Native reduction through a name that refers to `W.lemma`: `W.use` refers to it and to `W.rb`.
-- With `W.keep` in its place, the copies agree.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard !witnessAgrees `W.keep
  #[witnessTheorem `W.use (mkApp2 (.const `W.prove []) (.const `W.lemma []) (.const `W.rb []))]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard witnessAgrees `W.keep
  #[witnessTheorem `W.use (mkApp2 (.const `W.prove []) (.const `W.lemma []) (.const `W.keep []))]
-- The same through a module that is not owned: `W.use` of `W.Use`, which imports `W.Src`, refers
-- to `W.lemma` and to `W.rb`. With `W.keep` in its place, the copies agree.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard !witnessAgrees `W.keep #[] (importer :=
  #[witnessTheorem `W.use (mkApp2 (.const `W.prove []) (.const `W.lemma []) (.const `W.rb []))])
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard witnessAgrees `W.keep #[] (importer :=
  #[witnessTheorem `W.use (mkApp2 (.const `W.prove []) (.const `W.lemma []) (.const `W.keep []))])
-- A name the kernel reads unasked: a constant under the name `Char.ofNat` refers to `W.lemma`.
-- Under a name outside `kernelNames`, the copies agree.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard !witnessAgrees `W.keep
  #[witnessTheorem ``Char.ofNat (.app (.const `W.prove []) (.const `W.lemma []))]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard witnessAgrees `W.keep
  #[witnessTheorem `W.ofNat (.app (.const `W.prove []) (.const `W.lemma []))]
-- A mixed context: `W.mixed` of `W.Src` refers to the `flag` of `W.Src` itself, so a check of it
-- would read the private names of both modules once `W.lemma` resolves to the copy of `W.Dst`.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard !witnessAgrees `W.keep
  #[witnessTheorem `W.mixed
    (.app (.const `W.prove []) (.const (mkPrivateNameCore `W.Src `flag) []))]
-- A declaring module that is not owned: the same copies agree when `W.Dst` and `W.Src` are both
-- owned, and do not when `W.Src` is not.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard witnessAgrees `W.keep #[] #[`W.Dst, `W.Src]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard !witnessAgrees `W.keep #[] #[`W.Dst]

/-! ### The constants of a reused module -/

/-- Whether the copies of the name of each constant of the module at index `owner` agree
(`agree`, which `candidates` gives as `agrees`: every copy is `Identical` to the constant Lean's
import keeps under the name, or `uniformUpToPrivate` accepts the name and only owned modules
declare it, so every copy is the attributed module's copy or a `renamedCopy` of it), and a
constant that is not a theorem has no copy in another module (its name is attributed to `owner`
and has no `others`). `none`, a module the environment did not load, is refused. `copiesAgree_iff`
states the decision.

This is the condition on a module's own constants under which an environment reuses an earlier
environment's replay of it (`candidates`), and why that is the replay this environment would
repeat. An environment that reuses the module imports it into the replay base and checks none of
its constants. Every other constant it holds under one of the module's names is one of the loaded
copies of the name: the replay base's (`finalizeImport`), the audited environment's (the kept
constant) and the replayed kernel's (the base's or the kept constant, `replayMap_sound`, or a
constructor or recursor record the kernel regenerated and replay accepted as `Identical` to the
stored one). Where the copies of a name are `Uniform`, that constant is `Identical` to the module's
own, so `replayMap`, `checkShared`, `checkOwn` and `checkKept` meet, under that name, a constant
`Identical` to the one they would meet if the module were replayed, and the kernel gives both the
same verdict. Where they are `UniformUpToPrivate`, each copy is the attributed module's copy or one
that exchanging the names of its block with their renamed names turns into that copy, while every
other loaded constant stays fixed; the docstring of `renamedCopy` argues that the kernel and every
check of Regula then give the same results whichever of the copies is held. A copy in a replayed
module passes `checkShared` against the held constant (two `Identical` theorems are a
`SameTheorem`, and so are two that `renamedCopy` relates), and `checkOwn` and `checkKept` either
without a proof check or with `checkProof`, as it would in a replay of both. A fresh replay would
admit the module's constants too: a shared copy of a theorem is `SameTheorem` with the held
constant, and a constant that is not a theorem has a single copy, so it is never shared; this is
why the condition requires a theorem where another module declares the name (two `Identical`
axioms, which Lean's import accepts, `checkShared` refuses). The receipt requires the key
`(module, name)` of each safe, total constant from the module's own data whichever module the name
is attributed to (`mem_required`), and `reuseJustified` accepts it only when the environment that
replayed the module admitted that key. That environment offered the module only when each of its
copies was admitted there with the copies of each shared name in agreement and every module
declaring that name owned (`ownedAgrees`). So each safe, total constant of a reused module was
admitted there (`CopyAdmitted`): its proof was checked by that environment's kernel, or it is
`Identical` to a constant that the kernel of an environment of the audit accepted (by induction on
the order in which the environments start, with the symmetry and transitivity of `Identical`).

Reuse changes no input of any other check of Regula: those checks read the audited environment and
the axiom and assumption tables that `validate` returns, which, as the following sentences show,
are the same whether a module is replayed or reused. The reuse set reaches only `validate`
(`Regula.Checker.Environment`, the `reused` that `reusedModules` gives), and the declaration report receives the receipt's `modules ++ reused`, the same set whether a
module is replayed or reused. Within `validate`, reuse changes only which copies `replayMap` hands
the kernel and which the replay base holds. `checkShared` compares with `sameTheorem`, and
`checkOwn` and `checkKept` with `identical` and `sameTheorem`, each of which compares expressions
with `Expr.eqv`. A receipt key is a module and a name read from the module's own data
(`requiredKey?`, `mem_required`), and the axiom and assumption searches read only the constant
names `KernelAxioms.successorsOf` gives (`ConstantInfo.getUsedConstantsAsSet`), which `Expr.eqv`
compares. From a renamed copy and the copy it is renamed into, those searches reach the same names
except the names the renaming exchanges, none of which is an axiom or has a role (`renamedCopy`).

An `unsafe` or `partial` constant of the module, such as the `_unsafe_rec` helper Lean adds for a
recursive definition, is outside that statement: no replay checks it, since
`Kernel.Environment.replay` skips it, and admission accepts it under `CopyAdmitted` with no
constant of the kernel to match. A fresh replay of the module would not check it either, so reuse
changes nothing for it, and it keeps the boundary admission states for such helpers.

Assumes:
- Lean v4.35.0, `src/lean/Lean/Environment.lean:2333-2348` (`finalizeImport`): the import, of the
  audited environment and of the replay base alike, keeps under each name one of the copies it
  read, so a constant held under a name is one of the loaded copies.
- Lean v4.35.0, `src/lean/Lean/Expr.lean:804-812`: `Expr.eqv`, Lean's `==` on expressions, is
  alpha-equivalence with binder annotations ignored, an equivalence relation, so `Identical` is
  symmetric and transitive. Trusted: the C++ `lean_expr_eqv` is not modeled.
- Lean v4.35.0, `src/kernel/expr_eq_fn.cpp:98-110` (trusted: the C++ is not modeled): the
  kernel's structural equality `expr_eq_fn<false>` ignores exactly the binder names and binder
  annotations of lambdas and foralls and the names of lets, and compares every other part (mdata,
  projections, constant names and universe levels at `81-84`, literals, bound variables, the
  nondep flag of a let). By `123-132` with `src/kernel/expr_eq_fn.h:14-15`, `lean_expr_eqv`, which
  is `Expr.eqv`, and the kernel's own `operator==` are both that function. By
  `src/lean/Lean/Expr.lean:488`, `497` and `506`, the hash of a binder or a let mixes only its
  subterms, so the hash test at `expr_eq_fn.cpp:46` does not separate alpha-equivalent
  expressions.
- Lean v4.35.0, `src/kernel/type_checker.h:26-42` with `src/kernel/expr_maps.h:15` and
  `src/kernel/expr.h:164-165` (trusted): the type checker's infer, whnf, unfold and
  definitional-equality caches are keyed by that `==`, so within one check the kernel already
  answers for an expression with the result it computed for any `Expr.eqv`-equal one.
- Lean v4.35.0, `src/kernel/type_checker.cpp:135`, `153`, `223`, `770`, `1222` and `1230`
  (trusted): binder names and annotations are read only to label a local declaration whose
  identity is a fresh name from `m_ngen`; `846` copies them into an eta-expanded lambda, and `219`
  uses a let name only in an error message. `src/kernel/local_ctx.cpp:104-113` and
  `src/kernel/inductive.cpp:227`, `707`, `934`, `1142` and `1167` copy them only into the binders,
  parameters and records they build. Outside `expr_eq_fn`, no file of `src/kernel` compares binder
  names or annotations except `src/kernel/expr_cache.cpp:12`, a cache whose stricter key can only
  miss more often. So no kernel decision branches on what `Expr.eqv` ignores: the kernel's check of
  a declaration, and of every declaration that consults it, gives the same verdict for two
  `Identical` constants, the boundary `checkOwn` already rests on.
- Lean v4.35.0, `src/lean/Lean/Replay.lean:120-128` and `148-163`: replay adds an inductive type
  through the kernel, which generates its constructors and recursors, and accepts the stored
  record of each when the derived `==`, which compares expressions with `Expr.eqv`, equates it
  with the generated one (`152`, `163`). So for a constructor or a recursor the kernel may hold a
  regenerated record that is `Identical` to the stored copy.
- Lean v4.35.0, `src/lean/Lean/Replay.lean:176-189` (trusted, as for every replay):
  `Kernel.Environment.replay` checks each constant it adds, and it adds only the constants that
  are neither `unsafe` nor `partial` (`180-183`), replaying a dependency only when it is one of
  them (`replayConstant`, `74-77`). -/
def copiesAgree (modules : Array ModuleData) (attributed : Name → Option Nat)
    (dups : Duplicates) (agree : Name → Bool) (owner? : Option Nat) : Bool :=
  match owner? with
  | none => false
  | some owner =>
    match modules[owner]? with
    | none => false
    | some data => data.constants.all fun info =>
        agree info.name &&
          (info.isTheorem || attributed info.name == some owner &&
            (dups.others.getD info.name #[]).isEmpty)

/-- The module at index `owner` has data, and for each of its constants the copies of the name
agree (`same`, which `Candidate` gives as `AgreesIn`), and the constant is a theorem or the only
copy of its name, in the module the name is attributed to. -/
def CopiesAgree (same : Name → Prop) (attributed : Name → Option Nat)
    (modules : Array ModuleData) (owner : Nat) : Prop :=
  ∃ data, modules[owner]? = some data ∧ ∀ info ∈ data.constants,
    same info.name ∧
      (info.isTheorem = true ∨ attributed info.name = some owner ∧
        ∀ idx, Declares modules idx info.name → idx = owner)

/-- **`copiesAgree` over the pass of `duplicatesOf` accepts exactly a loaded module that
`CopiesAgree` admits**, for an `agree` test that decides `same`. -/
theorem copiesAgree_iff {find : Name → Option ConstantInfo} {attributed : Name → Option Nat}
    {modules : Array ModuleData} {agree : Name → Bool} {same : Name → Prop}
    (hagree : ∀ n, agree n = true ↔ same n) {owner? : Option Nat} :
    copiesAgree modules attributed (duplicatesOf find attributed modules) agree owner? = true ↔
      ∃ owner, owner? = some owner ∧ CopiesAgree same attributed modules owner := by
  -- The name of a constant that is not a theorem has no `others` and is attributed to `owner`
  -- exactly when `owner` is its only declaring module.
  have single : ∀ (owner : Nat) (n : Name),
      (attributed n = some owner ∧
        (duplicatesOf find attributed modules).others.getD n #[] = #[]) ↔
      (attributed n = some owner ∧ ∀ idx, Declares modules idx n → idx = owner) := by
    intro owner n
    constructor
    · rintro ⟨hattr, hnone⟩
      refine ⟨hattr, fun idx hdecl => Classical.byContradiction fun hne => ?_⟩
      have hmem : idx ∈ (duplicatesOf find attributed modules).others.getD n #[] :=
        mem_others_iff.mpr ⟨hdecl, fun h => hne (Option.some.inj (hattr.symm.trans h)).symm⟩
      rw [hnone] at hmem
      simp at hmem
    · rintro ⟨hattr, honly⟩
      refine ⟨hattr, Array.eq_empty_iff_forall_not_mem.mpr fun idx hmem => ?_⟩
      obtain ⟨hdecl, hne⟩ := mem_others_iff.mp hmem
      exact hne (by rw [honly idx hdecl]; exact hattr)
  unfold copiesAgree CopiesAgree
  cases owner? with
  | none => simp
  | some owner =>
    cases hdata : modules[owner]? with
    | none => simp [hdata]
    | some data =>
      simp only [hdata, Array.all_eq_true', Bool.and_eq_true, hagree, Bool.or_eq_true, beq_iff_eq,
        Array.isEmpty_iff, Option.some.injEq, exists_eq_left', single]

/-! ### The references of a reused module -/

/-- Whether a reference to `used` stays within the modules named in `allowed`: the module the
name is attributed to is one of them, or the copies of the name agree (`agree`, which `candidates`
gives as `agrees`) and one of them declares a copy of it (`Duplicates.others`). `names` holds each
loaded module's name at its index. -/
def refersWithin (names : Array Name) (attributed : Name → Option Nat) (dups : Duplicates)
    (agree : Name → Bool) (allowed : Std.HashSet Name) (used : Name) : Bool :=
  (attributed used).any (fun idx => names[idx]?.any allowed.contains) ||
    agree used &&
      (dups.others.getD used #[]).any fun idx => names[idx]?.any allowed.contains

/-- Whether every name a constant of the module at index `owner` refers to (`usedNames`) is
declared in a module of `closure` (`refersWithin`): attributed to one, or with copies that agree
and a copy in one, as a module whose own copy of an equation lemma is attributed to a module
loaded before it, outside its closure, refers to its own copy. `none`, a module the environment did
not load, is refused. `referencesWithin_iff` states the decision. -/
def referencesWithin (modules : Array ModuleData) (names : Array Name)
    (attributed : Name → Option Nat) (dups : Duplicates) (agree : Name → Bool)
    (owner? : Option Nat) (closure : Array RegulaPolicy.ModuleOrigin) : Bool :=
  match owner? with
  | none => false
  | some owner =>
    match modules[owner]? with
    | none => false
    | some data =>
      let allowed := Std.HashSet.ofList (closure.toList.map (·.name))
      data.constants.all fun info =>
        (usedNames info).all (refersWithin names attributed dups agree allowed)

/-- A reference to `used` lands in `closure`: the module `used` is attributed to is a module of
`closure`, or the copies of `used` agree (`same`, which `Candidate` gives as `AgreesIn`) and a
module of `closure` declares one. -/
def RefersWithin (same : Name → Prop) (modules : Array ModuleData) (names : Array Name)
    (attributed : Name → Option Nat) (closure : Array RegulaPolicy.ModuleOrigin) (used : Name) :
    Prop :=
  (∃ idx, attributed used = some idx ∧ ∃ origin ∈ closure, names[idx]? = some origin.name) ∨
    same used ∧
      ∃ idx, Declares modules idx used ∧ ∃ origin ∈ closure, names[idx]? = some origin.name

/-- The module at index `owner` has data, and every name each of its constants refers to lands in
`closure` (`RefersWithin`). -/
def ReferencesWithin (same : Name → Prop) (modules : Array ModuleData) (names : Array Name)
    (attributed : Name → Option Nat) (owner : Nat) (closure : Array RegulaPolicy.ModuleOrigin) :
    Prop :=
  ∃ data, modules[owner]? = some data ∧ ∀ info ∈ data.constants, ∀ used ∈ usedNames info,
    RefersWithin same modules names attributed closure used

/-- `refersWithin` over the pass of `duplicatesOf` accepts exactly a reference that
`RefersWithin` admits, for an `agree` test that decides `same`. -/
theorem refersWithin_iff {find : Name → Option ConstantInfo} {attributed : Name → Option Nat}
    {modules : Array ModuleData} {names : Array Name} {agree : Name → Bool} {same : Name → Prop}
    (hagree : ∀ n, agree n = true ↔ same n) {closure : Array RegulaPolicy.ModuleOrigin}
    {used : Name} :
    refersWithin names attributed (duplicatesOf find attributed modules) agree
        (Std.HashSet.ofList (closure.toList.map (·.name))) used = true ↔
      RefersWithin same modules names attributed closure used := by
  have inClosure : ∀ idx : Nat, (names[idx]?.any
      (Std.HashSet.ofList (closure.toList.map (·.name))).contains = true) ↔
      ∃ origin ∈ closure, names[idx]? = some origin.name := by
    intro idx
    simp only [Option.any_eq_true, Std.HashSet.contains_ofList, List.contains_iff_mem,
      List.mem_map, Array.mem_toList_iff]
    constructor
    · rintro ⟨name, hname, origin, horigin, rfl⟩
      exact ⟨origin, horigin, hname⟩
    · rintro ⟨origin, horigin, hname⟩
      exact ⟨origin.name, hname, origin, horigin, rfl⟩
  unfold refersWithin RefersWithin
  simp only [Bool.or_eq_true, Bool.and_eq_true, hagree, Array.any_eq_true', Option.any_eq_true,
    inClosure, mem_others_iff]
  constructor
  · rintro (⟨idx, hattr, hin⟩ | ⟨hsame, idx, ⟨hdecl, -⟩, hin⟩)
    · exact .inl ⟨idx, hattr, hin⟩
    · exact .inr ⟨hsame, idx, hdecl, hin⟩
  · rintro (⟨idx, hattr, hin⟩ | ⟨hsame, idx, hdecl, hin⟩)
    · exact .inl ⟨idx, hattr, hin⟩
    · by_cases hattr : attributed used = some idx
      · exact .inl ⟨idx, hattr, hin⟩
      · exact .inr ⟨hsame, idx, ⟨hdecl, hattr⟩, hin⟩

/-- **`referencesWithin` over the pass of `duplicatesOf` accepts exactly a loaded module that
`ReferencesWithin` admits**, for an `agree` test that decides `same`. -/
theorem referencesWithin_iff {find : Name → Option ConstantInfo}
    {attributed : Name → Option Nat} {modules : Array ModuleData} {names : Array Name}
    {agree : Name → Bool} {same : Name → Prop} (hagree : ∀ n, agree n = true ↔ same n)
    {owner? : Option Nat} {closure : Array RegulaPolicy.ModuleOrigin} :
    referencesWithin modules names attributed (duplicatesOf find attributed modules) agree owner?
        closure = true ↔
      ∃ owner, owner? = some owner ∧
        ReferencesWithin same modules names attributed owner closure := by
  unfold referencesWithin ReferencesWithin
  cases owner? with
  | none => simp
  | some owner =>
    cases hdata : modules[owner]? with
    | none => simp [hdata]
    | some data =>
      simp only [hdata, Array.all_eq_true', List.all_eq_true, refersWithin_iff hagree,
        Option.some.injEq, exists_eq_left']

/-! ### The offer of a replayed module with a shared copy -/

/-- Whether the copies of `n` agree (`agree`, which `validate` gives as `agrees`) and every module
that declares `n` is named in `owned`: the module the name is attributed to and each of its
`others`. A replayed module holding a shared copy of such a name is still offered for reuse
(`AdmitRequest.pinned`): every copy of the name is then `Identical` to the kept constant, or every
copy is the attributed module's copy or a theorem renamed into it (`renamedCopy`), and each is held
by an owned module that this environment replayed, or reused from an earlier one that offered it
on the same condition. `ownedAgrees_iff` states the decision. -/
def ownedAgrees (names : Array Name) (attributed : Name → Option Nat) (dups : Duplicates)
    (agree : Name → Bool) (owned : Std.HashSet Name) (n : Name) : Bool :=
  agree n && declaredOwned names attributed dups owned n

/-- The copies of `n` agree (`same`, which the offer reads as `AgreesIn`), the module `n` is
attributed to is named in `owned`, and so is every module that declares `n` (`DeclaredOwned`). -/
def OwnedAgrees (same : Name → Prop) (modules : Array ModuleData) (names : Array Name)
    (attributed : Name → Option Nat) (owned : Std.HashSet Name) (n : Name) : Prop :=
  same n ∧
    (∃ idx name, attributed n = some idx ∧ names[idx]? = some name ∧ name ∈ owned) ∧
    DeclaredOwned modules names owned n

/-- **`ownedAgrees` over the pass of `duplicatesOf` accepts exactly a name that `OwnedAgrees`
admits**, for an `agree` test that decides `same`. -/
theorem ownedAgrees_iff {find : Name → Option ConstantInfo} {attributed : Name → Option Nat}
    {modules : Array ModuleData} {names : Array Name} {agree : Name → Bool} {same : Name → Prop}
    (hagree : ∀ n, agree n = true ↔ same n) {owned : Std.HashSet Name} {n : Name} :
    ownedAgrees names attributed (duplicatesOf find attributed modules) agree owned n = true ↔
      OwnedAgrees same modules names attributed owned n := by
  unfold ownedAgrees OwnedAgrees
  rw [Bool.and_eq_true, hagree, declaredOwned_iff]

/-- The names that have a role in `env` (`Regula.Assumption.roles`). -/
def rolesIn (env : Environment) : Std.HashSet Name :=
  Std.HashSet.ofList ((Regula.Assumption.roles env).toList.map (·.1))

/-- The `differing` names of `env` whose copies agree up to renaming (`agreeing`), from the pass
`dups` over its loaded constants, among the names that only modules named in `owned` declare: a
constant a renamed copy renames must have a name with no role in `env` (`rolesIn`) that is outside
`differing` (`fixedIn`). -/
def agreeingIn (env : Environment) (dups : Duplicates) (owned : Std.HashSet Name) :
    Std.HashSet Name :=
  agreeing env.header.moduleData env.header.moduleNames (attributedIn env) dups owned
    (fixedIn (rolesIn env) dups)

/-- The copies of `n` agree in `env` (`Agrees`) with the owned modules named in `owned`, with each
constant a renamed copy renames free of a role and `Uniform` (`Fixed`). -/
def AgreesIn (env : Environment) (owned : Std.HashSet Name) (n : Name) : Prop :=
  Agrees env.find? env.header.moduleData env.header.moduleNames (attributedIn env) owned
    (Fixed (rolesIn env) env.find? env.header.moduleData) n

/-- **`agrees` over the pass `duplicatesIn` of `env` accepts exactly a name that `AgreesIn`
admits**, when the loaded modules outside `owned` meet `ImportScoped`. -/
theorem agreesIn_iff {env : Environment} {owned : Std.HashSet Name}
    (hscoped : ImportScoped env.header.moduleData env.header.moduleNames owned) (n : Name) :
    agrees (duplicatesIn env) (agreeingIn env (duplicatesIn env) owned) n = true ↔
      AgreesIn env owned n :=
  agrees_iff (fixedIn_iff (roles := rolesIn env)) hscoped

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
declarations refer only to constants of that closure (`referencesWithin`) and the copies of whose
constants' names agree (`copiesAgree`), with that closure. Both conditions read whether the
copies of a name agree as `agrees` over the pass over every loaded constant (`duplicatesIn`,
`agreeingIn`, with the modules of `owned`), which runs only when some owned module is offered. -/
def candidates (env : Environment) (origins : Array RegulaPolicy.ModuleOrigin)
    (owned : Array Name) (priors : Array PriorAdmission) :
    Array (Name × Array RegulaPolicy.ModuleOrigin) :=
  let here := originIndex origins
  let earlier := indexPriors priors
  let offered := owned.filterMap fun m => (offeredClosure earlier here m).map (m, ·)
  if offered.isEmpty then #[] else
    let dups := duplicatesIn env
    let agree := agrees dups (agreeingIn env dups (Std.HashSet.ofList owned.toList))
    offered.filter fun entry =>
      referencesWithin env.header.moduleData env.header.moduleNames (attributedIn env) dups agree
          (ownerIn env entry.1) entry.2 &&
        copiesAgree env.header.moduleData (attributedIn env) dups agree (ownerIn env entry.1)

/-- `m`, with the import closure `closure`, meets every condition of reuse but the last: it is
owned, it has `closure` here, a prior offers it over `closure`, and, at its index in `env`, every
name its constants refer to lands in `closure` (`ReferencesWithin`) and the copies of each of its
constants' names agree (`CopiesAgree`), both with agreement read as `AgreesIn` with the modules of
`owned`. -/
def Candidate (env : Environment) (origins : Array RegulaPolicy.ModuleOrigin) (owned : Array Name)
    (priors : Array PriorAdmission) (m : Name) (closure : Array RegulaPolicy.ModuleOrigin) :
    Prop :=
  m ∈ owned ∧ importClosure (originIndex origins) m = some closure ∧
    (∃ prior ∈ priors, m ∈ prior.modules ∧
      importClosure (originIndex prior.origins) m = some closure) ∧
    ∃ owner, ownerIn env m = some owner ∧
      ReferencesWithin (AgreesIn env (Std.HashSet.ofList owned.toList)) env.header.moduleData
        env.header.moduleNames (attributedIn env) owner closure ∧
      CopiesAgree (AgreesIn env (Std.HashSet.ofList owned.toList)) (attributedIn env)
        env.header.moduleData owner

/-- The owned modules an earlier environment offers, each with its closure here, are exactly the
owned modules with a closure here that a prior offers over the same closure. -/
private theorem mem_offered {origins : Array RegulaPolicy.ModuleOrigin} {owned : Array Name}
    {priors : Array PriorAdmission} {m : Name} {closure : Array RegulaPolicy.ModuleOrigin} :
    (m, closure) ∈ owned.filterMap (fun m =>
        (offeredClosure (indexPriors priors) (originIndex origins) m).map (m, ·)) ↔
      m ∈ owned ∧ importClosure (originIndex origins) m = some closure ∧
        ∃ prior ∈ priors, m ∈ prior.modules ∧
          importClosure (originIndex prior.origins) m = some closure := by
  simp only [Array.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, found, hfound, rfl, rfl⟩
    obtain ⟨hclosure, offering, hoffering, hm, hc⟩ := offeredClosure_eq_some.mp hfound
    obtain ⟨prior, hprior, rfl⟩ := Array.mem_map.mp hoffering
    exact ⟨ha, hclosure, prior, hprior, hm, hc⟩
  · rintro ⟨hm, hclosure, prior, hprior, hmod, hc⟩
    refine ⟨m, hm, closure, offeredClosure_eq_some.mpr ⟨hclosure, (prior, _),
      Array.mem_map.mpr ⟨prior, hprior, rfl⟩, hmod, hc⟩, rfl, rfl⟩

/-- A candidate is an owned module with a closure here that a prior offers over the same
closure, whatever the copies of its names. -/
theorem offered_of_mem_candidates {env : Environment} {origins : Array RegulaPolicy.ModuleOrigin}
    {owned : Array Name} {priors : Array PriorAdmission} {m : Name}
    {closure : Array RegulaPolicy.ModuleOrigin}
    (h : (m, closure) ∈ candidates env origins owned priors) :
    m ∈ owned ∧ importClosure (originIndex origins) m = some closure ∧
      ∃ prior ∈ priors, m ∈ prior.modules ∧
        importClosure (originIndex prior.origins) m = some closure := by
  unfold candidates at h
  simp only at h
  split at h
  · simp at h
  · exact mem_offered.mp (Array.mem_filter.mp h).1

/-- **The candidates are exactly the modules, with their closures, that `Candidate` admits**,
when the loaded modules outside `owned` meet `ImportScoped`. -/
theorem mem_candidates_iff {env : Environment} {origins : Array RegulaPolicy.ModuleOrigin}
    {owned : Array Name} {priors : Array PriorAdmission}
    (hscoped : ImportScoped env.header.moduleData env.header.moduleNames
      (Std.HashSet.ofList owned.toList))
    {entry : Name × Array RegulaPolicy.ModuleOrigin} :
    entry ∈ candidates env origins owned priors ↔
      Candidate env origins owned priors entry.1 entry.2 := by
  obtain ⟨m, closure⟩ := entry
  unfold candidates Candidate
  simp only
  split
  · rename_i hempty
    simp only [Array.not_mem_empty, false_iff]
    rintro ⟨hm, hclosure, hprior, -⟩
    have hmem := mem_offered.mpr ⟨hm, hclosure, hprior⟩
    rw [Array.isEmpty_iff.mp hempty] at hmem
    simp at hmem
  · have hagree : ∀ n, agrees (duplicatesOf env.find? (attributedIn env) env.header.moduleData)
        (agreeing env.header.moduleData env.header.moduleNames (attributedIn env)
          (duplicatesOf env.find? (attributedIn env) env.header.moduleData)
          (Std.HashSet.ofList owned.toList)
          (fixedIn (rolesIn env) (duplicatesOf env.find? (attributedIn env) env.header.moduleData)))
        n = true ↔ AgreesIn env (Std.HashSet.ofList owned.toList) n :=
      fun _ => agrees_iff (fixedIn_iff (roles := rolesIn env)) hscoped
    simp only [Array.mem_filter, mem_offered, Bool.and_eq_true, duplicatesIn, agreeingIn,
      referencesWithin_iff hagree, copiesAgree_iff hagree]
    constructor
    · rintro ⟨⟨hm, hclosure, hprior⟩, ⟨owner, howner, hrefs⟩, ⟨owner', howner', hcopies⟩⟩
      rw [howner] at howner'
      obtain rfl := Option.some.inj howner'
      exact ⟨hm, hclosure, hprior, owner, howner, hrefs, hcopies⟩
    · rintro ⟨hm, hclosure, hprior, owner, howner, hrefs, hcopies⟩
      exact ⟨⟨hm, hclosure, hprior⟩, ⟨owner, howner, hrefs⟩, ⟨owner, howner, hcopies⟩⟩

/-- The owned modules of `env` whose kernel admission this environment reuses instead of
replaying: an earlier environment of the same audit replayed and offers each one over the
identical import closure (`offeredClosure`), every declaration of every owned module in that
closure refers only to constants of its own closure (`referencesWithin`), the copies of the names
of the constants of every such module agree (`copiesAgree`, whose docstring argues why reuse is
then the replay this environment would repeat), and every owned module the closure contains is reused too. The last condition removes
each candidate (`candidates`) whose closure contains an owned module that is not a candidate; the
closure of every owned module of a kept candidate's closure lies within that closure
(`importClosure_trans`), so that module is kept as well and one pass settles the set. Every other
owned module is replayed. A module of this environment's own request is reused under the same
conditions, which happens only when an earlier environment loaded it before its own did (claimed
libraries that import one another). `mem_reusedModules_iff` states this decision both ways. -/
def reusedModules (env : Environment) (origins : Array RegulaPolicy.ModuleOrigin)
    (owned : Array Name) (priors : Array PriorAdmission) : Array Name :=
  let settled := candidates env origins owned priors
  let ownedSet := Std.HashSet.ofList owned.toList
  (settled.filter
    (closureWithin ownedSet (Std.HashSet.ofList (settled.map (·.1)).toList))).map (·.1)

/-- **A module is reused exactly when it is a candidate with some closure and every owned module
of that closure is a candidate too**, when the loaded modules outside `owned` meet
`ImportScoped`. -/
theorem mem_reusedModules_iff {env : Environment} {origins : Array RegulaPolicy.ModuleOrigin}
    {owned : Array Name} {priors : Array PriorAdmission} {m : Name}
    (hscoped : ImportScoped env.header.moduleData env.header.moduleNames
      (Std.HashSet.ofList owned.toList)) :
    m ∈ reusedModules env origins owned priors ↔
      ∃ closure, Candidate env origins owned priors m closure ∧
        ∀ origin ∈ closure, origin.name ∈ owned →
          ∃ inner, Candidate env origins owned priors origin.name inner := by
  have named : ∀ n, n ∈ Std.HashSet.ofList
      ((candidates env origins owned priors).map (·.1)).toList ↔
      ∃ inner, Candidate env origins owned priors n inner := by
    intro n
    rw [Std.HashSet.mem_ofList, List.contains_iff_mem, Array.mem_toList_iff]
    constructor
    · intro hn
      obtain ⟨entry, hentry, rfl⟩ := Array.mem_map.mp hn
      exact ⟨entry.2, (mem_candidates_iff hscoped).mp hentry⟩
    · rintro ⟨inner, hinner⟩
      exact Array.mem_map.mpr ⟨(n, inner), (mem_candidates_iff hscoped).mpr hinner, rfl⟩
  have ownedIff : ∀ n, n ∈ Std.HashSet.ofList owned.toList ↔ n ∈ owned := by
    intro n
    rw [Std.HashSet.mem_ofList, List.contains_iff_mem, Array.mem_toList_iff]
  unfold reusedModules
  simp only [Array.mem_map, Array.mem_filter, closureWithin_iff, named, ownedIff]
  constructor
  · rintro ⟨entry, ⟨hentry, hwithin⟩, rfl⟩
    exact ⟨entry.2, (mem_candidates_iff hscoped).mp hentry, hwithin⟩
  · rintro ⟨closure, hcandidate, hwithin⟩
    exact ⟨(m, closure), ⟨(mem_candidates_iff hscoped).mpr hcandidate, hwithin⟩, rfl⟩

/-- Every reused module is a candidate with a closure whose owned modules are all reused too, so
reuse never leaves an owned import to replay, when the loaded modules outside `owned` meet
`ImportScoped`. -/
theorem mem_reusedModules {env : Environment} {origins : Array RegulaPolicy.ModuleOrigin}
    {owned : Array Name} {priors : Array PriorAdmission} {m : Name}
    (hscoped : ImportScoped env.header.moduleData env.header.moduleNames
      (Std.HashSet.ofList owned.toList))
    (h : m ∈ reusedModules env origins owned priors) :
    ∃ closure, Candidate env origins owned priors m closure ∧
      ∀ origin ∈ closure, origin.name ∈ owned →
        origin.name ∈ reusedModules env origins owned priors := by
  obtain ⟨closure, hcandidate, hwithin⟩ := (mem_reusedModules_iff hscoped).mp h
  refine ⟨closure, hcandidate, fun origin horigin howned => ?_⟩
  obtain ⟨inner, hinner⟩ := hwithin origin horigin howned
  refine (mem_reusedModules_iff hscoped).mpr ⟨inner, hinner, fun other hother hotherOwned => ?_⟩
  obtain ⟨-, hclosure, -⟩ := hcandidate
  obtain ⟨-, hinnerClosure, -⟩ := hinner
  exact hwithin other
    (importClosure_trans (originIndex_keyed origins) hclosure horigin hinnerClosure other hother)
    hotherOwned

/-- Every reused module is an owned module with a closure here that a prior offers over the same
closure, whatever the copies of its names. -/
theorem offered_of_mem_reusedModules {env : Environment}
    {origins : Array RegulaPolicy.ModuleOrigin} {owned : Array Name}
    {priors : Array PriorAdmission} {m : Name} (h : m ∈ reusedModules env origins owned priors) :
    ∃ closure, m ∈ owned ∧ importClosure (originIndex origins) m = some closure ∧
      ∃ prior ∈ priors, m ∈ prior.modules ∧
        importClosure (originIndex prior.origins) m = some closure := by
  simp only [reusedModules] at h
  obtain ⟨⟨m', closure⟩, hentry, rfl⟩ := Array.mem_map.mp h
  exact ⟨closure, offered_of_mem_candidates (Array.mem_filter.mp hentry).1⟩

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
receipt's `modules` outside `reused`), other than its `shared` ones (those holding a shared copy
of a name that is not `offerable`, `AdmitRequest.pinned`, whose admission depends on which copy an
environment keeps), that it loaded with their import closure from the frozen paths
(`frozenClosure`), with the keys it admitted in them. An admission that offers nothing is not
handed on. -/
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
and value reports read, so on these names the replayed kernel holds the audited environment's
constants, except that for a constructor or a recursor it holds the record it regenerates from the
inductive type, which replay accepts only when it is `Identical` to the stored one
(`src/lean/Lean/Replay.lean:148-163` in Lean v4.35.0). -/
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
    obtain ⟨closure, _, hc, prior, hp, hm, hpc⟩ := offered_of_mem_reusedModules hr
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
    obtain ⟨_, _, _, prior, hp, hm, _⟩ := offered_of_mem_reusedModules hr
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
    obtain ⟨_, _, _, prior, hp, hm, _⟩ := offered_of_mem_reusedModules hr
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
  /-- The names a replayed module may hold a shared copy of and still be offered for reuse: the
  copies of the name agree (`agrees`) and every module declaring it is owned (`ownedAgrees`). -/
  offerable : Name → Bool

/-- The replayed modules no later environment may reuse: each holds a shared copy of a name that
is not `offerable`. -/
def AdmitRequest.pinned (admit : AdmitRequest) : Array Name :=
  RegulaPolicy.canonicalNames ((admit.request.copies.filter fun copy =>
    admit.shared copy && !admit.offerable copy.name).map (·.module))

/-- The receipt of an admission: the replayed modules, the required keys, admitted in the same
order, the reused modules and, as `shared`, the replayed modules no later environment may reuse
(`AdmitRequest.pinned`). -/
def AdmitRequest.receipt (admit : AdmitRequest) : ProducerReport.AdmissionReceipt :=
  { modules := RegulaPolicy.canonicalNames admit.request.replay
    required := admit.request.required
    admitted := admit.request.required
    reused := RegulaPolicy.canonicalNames admit.reused
    shared := admit.pinned }

/-- A replayed module the receipt does not list as `shared` holds a shared copy only of an
`offerable` name. -/
theorem offerable_of_unpinned {admit : AdmitRequest} {copy : Copy}
    (hc : copy ∈ admit.request.copies) (hm : copy.module ∉ admit.receipt.shared)
    (hs : admit.shared copy = true) : admit.offerable copy.name = true := by
  cases ho : admit.offerable copy.name
  · refine absurd ?_ hm
    simp only [AdmitRequest.receipt, AdmitRequest.pinned, RegulaPolicy.mem_canonicalNames,
      Array.mem_map, Array.mem_filter]
    exact ⟨copy, ⟨hc, by simp [hs, ho]⟩, rfl⟩
  · rfl

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
          checked, kept := fun _ => none, fuel := 0, shared := fun _ => false,
          offerable := fun _ => false }, rfl⟩ }⟩

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

/-- A declaration for which Lean's `collectAxioms` reports an axiom that its replayed development
does not reach: the declaration, the axioms `collectAxioms` reports and those it reaches in the
replayed kernel. -/
structure TableExcess where
  /-- The declaration. -/
  name : Name
  /-- The axioms Lean's `collectAxioms` reports for it (`KernelAxioms.recordedAxioms`). -/
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
modules contain a copy of a name that the base or another replayed module also declares, where
the loaded copies of the name do not agree (`agrees`) or a module outside `ownedModules` declares
it (`offerable`, `ownedAgrees`); their admission depends on which copy this environment keeps, so
they are not offered for reuse. A
reused module among `requested` is one whose declarations this environment reports: the receipt
requires the key of each of its constants that is neither `unsafe` nor `partial`, read from the
module's own data as for a replayed module (`mem_required`), and the coordinator accepts those
keys only when the earlier environment that replayed the module admitted them
(`reuseJustified`). With the receipt, `validate` returns the axioms that each name of the closure of
the `ownedModules`' declarations (`Probe.ownedConstants`) reaches in the replayed kernel
(`KernelAxioms.axiomTable` over the forward search `KernelAxioms.searchEdges` of `walkFind`,
`KernelAxioms.axiomTable_some`), after `checkTable` admitted those of the owned declarations against
the axioms Lean's `collectAxioms` reports, for each owned declaration, the axioms `collectAxioms`
omits, and for each owned declaration, the assumptions and checked operations that the walk of the
constants it uses reaches from it in the same kernel, read from the same forward search
(`RegulaPolicy.Assumptions.table_some`), with the roles `Regula.Assumption.roles` reads from the
environment. The original environment is retained
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
      -- The pass over every loaded constant (`duplicatesIn`) runs only when a copy is shared.
      let offerable : Name → Bool :=
        if request.copies.any shared then
          let dups := duplicatesIn env
          let owned := Std.HashSet.ofList ownedModules.toList
          ownedAgrees env.header.moduleNames (attributedIn env) dups
            (agrees dups (agreeingIn env dups owned)) owned
        else fun _ => true
      let replayed := replayMap find env.find? request.copies
      let checked ← Lean.Kernel.Environment.replay replayed base.toKernelEnv
      match checked_admitReplay.run
          { request, read, reused, checked, kept := env.find?, fuel, shared, offerable } with
      | .ok receipt =>
        let roots := (Regula.Probe.ownedConstants env ownedModules.toList).map (·.1)
        let walk := walkFind checked replayed
        let exhausted := IO.userError "the search of the axioms that the owned declarations reach \
          in the replayed kernel ran out of fuel"
        -- One forward search from the owned declarations, which the axiom table and the table of
        -- assumptions both read (`KernelAxioms.leafTable`).
        let some forward := searchEdges (successors walk) (fuel + roots.size) roots.toList
          | throw exhausted
        let some table := axiomTable walk (fuel + roots.size) forward
          | throw exhausted
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
          let lean := recordedAxioms env root
          entries := entries.push (root, lean, reached)
          let omitted := reached.filter fun a => !lean.contains a
          unless omitted.isEmpty do
            omissions := omissions.insert root omitted
        -- The assumptions and checked operations each owned declaration rests on, read from the
        -- types and values it reaches, proofs included, in the same kernel
        -- (`RegulaPolicy.Assumptions.table_some`). With no role in the environment, no declaration
        -- rests on one, so there is nothing to search back from.
        let roles : Std.HashMap Name RegulaPolicy.External.Role :=
          (Regula.Assumption.roles env).foldl (init := {}) fun roles (n, role) =>
            roles.insert n role
        let mut assumptions : Std.HashMap Name (Array Name) := {}
        let mut checkedOperations : Std.HashMap Name (Array Name) := {}
        unless roles.isEmpty do
          let some rests :=
              RegulaPolicy.Assumptions.table (roles[·]?) (fuel + roots.size) forward
            | throw <| IO.userError "the search of the assumptions that the owned declarations \
                rest on in the replayed kernel ran out of fuel"
          for root in roots do
            let some rested := rests[root]?
              | throw <| IO.userError s!"no assumptions were searched for {root} in the replayed \
                  kernel"
            let rested ← rested.mapM own
            let trusted := rested.filter fun d => roles[d]? matches some (.assumption ..)
            let checked := rested.filter fun d => roles[d]? matches some (.checked ..)
            unless trusted.isEmpty do assumptions := assumptions.insert root trusted
            unless checked.isEmpty do checkedOperations := checkedOperations.insert root checked
        match checked_checkTable.run entries with
        | .ok () => return .ok { receipt, replayed := { axioms, omissions, assumptions,
                                                        checkedOperations } }
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
