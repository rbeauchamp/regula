import Regula.Checker.ProducerReport
import Lean.Replay
import Regula.Probe
import Regula.Checker.SharedName
import Std.Data.HashMap.Lemmas

/-!
# Checked logical admission

Checked logical admission before report construction. The replay base contains
only imported modules outside the replayed inventory. Unsafe and partial entries
remain subject to generated-role policy; they cannot supply logical evidence.
An owned module that an earlier environment of the same audit admitted over the
identical import closure is reused instead of replayed again (`reusedModules`).
Replay reads each replayed module's own constants (`Copy`), so a name that several
modules contain, such as an equation lemma Lean realizes in each module that needs it,
has every owned copy checked (`replayMap_sound`, `checkCopies_sound`).
-/

namespace Regula.Checker.Admission

open Lean
open RegulaPolicy.Guards (forM_eq_ok)

/-- An earlier environment's completed admission in the same audit, as the coordinator offers it
to a later environment: the owned modules it replayed and offers for reuse, and the origin of
every module it loaded (`Probe.loadedModuleOrigins`). -/
structure PriorAdmission where
  /-- Owned modules the earlier environment replayed and admitted, offered for reuse. -/
  modules : Array Name
  /-- The name, canonical `.olean` path and direct imports of every module it loaded. -/
  origins : Array RegulaPolicy.ModuleOrigin
  deriving ToJson

instance : FromJson PriorAdmission := ⟨fun j => do
  Regula.Checker.PolicyCodec.exactFields j ["modules", "origins"]
  return { modules := ← j.getObjValAs? _ "modules", origins := ← j.getObjValAs? _ "origins" }⟩

/-- One environment's module origins, by module name. -/
def originIndex (origins : Array RegulaPolicy.ModuleOrigin) :
    Std.HashMap Name RegulaPolicy.ModuleOrigin :=
  origins.foldl (fun index origin => index.insert origin.name origin) {}

/-- The import closure of `m` in one environment: the origin of `m` and of every module it
transitively imports, ordered by name, or `none` when a reached module has no origin. Two
environments have equal closures of `m` exactly when they loaded `m` and every module below it
under the same names, from the same canonical `.olean` files, with the same import edges. -/
def importClosure (origins : Std.HashMap Name RegulaPolicy.ModuleOrigin) (m : Name) :
    Option (Array RegulaPolicy.ModuleOrigin) := Id.run do
  let mut pending := #[m]
  let mut seen : NameSet := ({} : NameSet).insert m
  let mut closure := #[]
  -- Each step settles one name and each name is pushed once, so a closure whose every module
  -- has an origin is settled within `origins.size` steps.
  for _ in [:origins.size] do
    let some name := pending.back? | break
    pending := pending.pop
    let some origin := origins[name]? | return none
    closure := closure.push origin
    for imported in origin.imports do
      unless seen.contains imported do
        seen := seen.insert imported
        pending := pending.push imported
  unless pending.isEmpty do return none
  return some (closure.qsort fun a b => Name.quickLt a.name b.name)

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

/-- The priors' offered modules, each with its admission's origins indexed by module name. -/
def indexPriors (priors : Array PriorAdmission) :
    Array (Array Name × Std.HashMap Name RegulaPolicy.ModuleOrigin) :=
  priors.map fun prior => (prior.modules, originIndex prior.origins)

/-- The import closure of `m` in the environment whose origins are `here`, when `m` is not
`requested` there and an `earlier` admission offers `m` over the identical closure. -/
def offeredClosure
    (earlier : Array (Array Name × Std.HashMap Name RegulaPolicy.ModuleOrigin))
    (here : Std.HashMap Name RegulaPolicy.ModuleOrigin) (requested : Array Name) (m : Name) :
    Option (Array RegulaPolicy.ModuleOrigin) :=
  if requested.contains m then none
  else match importClosure here m with
    | none => none
    | some closure =>
        if earlier.any (fun entry => entry.1.contains m && importClosure entry.2 m == some closure)
        then some closure else none

/-- `offeredClosure` returns a closure exactly for an unrequested module that an earlier
admission offers over that same closure. -/
theorem offeredClosure_eq_some {earlier : Array (Array Name × Std.HashMap Name
      RegulaPolicy.ModuleOrigin)} {here : Std.HashMap Name RegulaPolicy.ModuleOrigin}
    {requested : Array Name} {m : Name} {closure : Array RegulaPolicy.ModuleOrigin} :
    offeredClosure earlier here requested m = some closure ↔
      m ∉ requested ∧ importClosure here m = some closure ∧
      ∃ entry ∈ earlier, m ∈ entry.1 ∧ importClosure entry.2 m = some closure := by
  unfold offeredClosure
  by_cases hr : m ∈ requested
  · simp [Array.contains_eq_mem, hr]
  · simp only [Array.contains_eq_mem, hr, decide_false, Bool.false_eq_true, ↓reduceIte,
      not_false_eq_true, true_and]
    cases hc : importClosure here m with
    | none => simp
    | some found =>
      simp only [Option.some.injEq, Array.any_eq_true', Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq]
      by_cases hany : ∃ entry ∈ earlier, m ∈ entry.1 ∧ importClosure entry.2 m = some found
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

/-- The owned modules of `env` outside `requested` whose kernel admission this environment
reuses instead of replaying: an earlier environment of the same audit replayed and offers each
one over the identical import closure (`offeredClosure`), every declaration of every owned
module in that closure refers only to constants of its own closure (`referencesWithin`), every
constant of the module is attributed to it and is the copy this environment keeps
(`uniquelyKept`), and every owned module the closure contains is reused too. When the last condition fails for the
filtered set, nothing is reused. Every other owned module is replayed. `mem_reusedModules`
states this contract. -/
def reusedModules (env : Environment) (origins : Array RegulaPolicy.ModuleOrigin)
    (requested owned : Array Name) (priors : Array PriorAdmission) : Array Name :=
  let here := originIndex origins
  let earlier := indexPriors priors
  let settled := owned.filterMap fun m =>
    (offeredClosure earlier here requested m).bind fun closure =>
      if referencesWithin env m closure && uniquelyKept env m then some (m, closure) else none
  let ownedSet := Std.HashSet.ofList owned.toList
  let kept := settled.filter
    (closureWithin ownedSet (Std.HashSet.ofList (settled.map (·.1)).toList))
  if kept.all (closureWithin ownedSet (Std.HashSet.ofList (kept.map (·.1)).toList)) then
    kept.map (·.1)
  else #[]

/-- Every reused module is an owned, unrequested module that some prior offers over the
import closure it has here, whose declarations refer only to that closure, whose constants are
uniquely kept here, and whose closure's owned modules are all reused too, so reuse never leaves
an owned import to replay. -/
theorem mem_reusedModules {env : Environment} {origins : Array RegulaPolicy.ModuleOrigin}
    {requested owned : Array Name} {priors : Array PriorAdmission} {m : Name}
    (h : m ∈ reusedModules env origins requested owned priors) :
    m ∈ owned ∧ m ∉ requested ∧ ∃ closure,
      importClosure (originIndex origins) m = some closure ∧
      referencesWithin env m closure = true ∧ uniquelyKept env m = true ∧
      (∃ prior ∈ priors, m ∈ prior.modules ∧
        importClosure (originIndex prior.origins) m = some closure) ∧
      ∀ origin ∈ closure, origin.name ∈ owned →
        origin.name ∈ reusedModules env origins requested owned priors := by
  unfold reusedModules at h ⊢
  simp only at h ⊢
  split at h
  · rename_i hall
    simp only [hall, ↓reduceIte]
    obtain ⟨⟨m', closure⟩, hkept, rfl⟩ := Array.mem_map.mp h
    have hsettled := (Array.mem_filter.mp hkept).1
    obtain ⟨a, ha, hf⟩ := Array.mem_filterMap.mp hsettled
    cases ho : offeredClosure (indexPriors priors) (originIndex origins) requested a with
    | none => simp [ho] at hf
    | some found =>
      simp only [ho, Option.bind_some] at hf
      split at hf
      · rename_i hrefs
        obtain ⟨hrefs, hunique⟩ := Bool.and_eq_true_iff.mp hrefs
        simp only [Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        obtain ⟨hreq, hclosure, entry, hentry, hm, hc⟩ := offeredClosure_eq_some.mp ho
        obtain ⟨prior, hprior, rfl⟩ := Array.mem_map.mp hentry
        refine ⟨ha, hreq, found, hclosure, hrefs, hunique, ⟨prior, hprior, hm, hc⟩, ?_⟩
        intro origin horigin howned
        have hw := Array.all_eq_true'.mp hall _ hkept
        simp only [closureWithin, Array.all_eq_true', Bool.or_eq_true, Bool.not_eq_eq_eq_not,
          Bool.not_true, Std.HashSet.contains_ofList, List.contains_iff_mem,
          Array.mem_toList_iff] at hw
        exact (hw origin horigin).resolve_left (by simpa using howned)
      · simp at hf
  · simp at h

/-- Whether a report's admission reused only what `priors` offered (`offeredClosure`, over the
import closures the report's own module origins give). -/
def reuseJustified (priors : Array PriorAdmission) (report : ProducerReport.Environment) :
    Bool :=
  let here := originIndex report.moduleOrigins
  let earlier := indexPriors priors
  ((report.admission.map (·.reused)).getD #[]).all fun m =>
    (offeredClosure earlier here report.census.modules m).isSome

/-- An accepted report reused only unrequested modules that some prior offers over the import
closure the report's own module origins give them. -/
theorem reuseJustified_sound {priors : Array PriorAdmission} {report : ProducerReport.Environment}
    (h : reuseJustified priors report = true) {receipt : ProducerReport.AdmissionReceipt}
    (hr : report.admission = some receipt) {m : Name} (hm : m ∈ receipt.reused) :
    m ∉ report.census.modules ∧ ∃ closure,
      importClosure (originIndex report.moduleOrigins) m = some closure ∧
      ∃ prior ∈ priors, m ∈ prior.modules ∧
        importClosure (originIndex prior.origins) m = some closure := by
  simp only [reuseJustified, hr, Option.map_some, Option.getD_some, Array.all_eq_true',
    Option.isSome_iff_exists] at h
  obtain ⟨closure, ho⟩ := h m hm
  obtain ⟨hreq, hclosure, entry, hentry, hmem, hc⟩ := offeredClosure_eq_some.mp ho
  obtain ⟨prior, hprior, rfl⟩ := Array.mem_map.mp hentry
  exact ⟨hreq, closure, hclosure, prior, hprior, hmem, hc⟩

/-! ## Several copies of one name

Lean realizes some constants in the module that first needs them: equation, unfolding and
match-equation lemmas, functional induction and case principles, congruence and injectivity
lemmas. Two modules that do not import each other can each contain the same one, and Lean's
import (`Lean.finalizeImport`) keeps a single copy of the name when the two are theorems of the
same statement: `Environment.find?` returns the last one loaded, while the name stays attributed
to the first, whose own copy's precomputed axioms `collectAxioms` reports. The audited
environment therefore shows one copy, and `Kernel.Environment.replay` skips a theorem whose name
it already holds with that statement without checking its proof. Replay therefore reads each
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
fresh name, where its own name still denotes the held constant. The search below computes every
name its proof reaches, through the types and values of the constants it uses, so admission can
refuse a proof that reaches its own name (a circular proof) or axioms other than the held
constant's. `collectAxioms` reports, for an imported name, the axioms its attributed module
computed for its own copy when compiled, so copies with equal axioms make that report right
whichever copy a declaration used. -/

/-- The constants the type and value of `info` use (`ConstantInfo.getUsedConstantsAsSet`). -/
def successorsOf (info : ConstantInfo) : Array Name :=
  Std.TreeSet.toArray info.getUsedConstantsAsSet

/-- The constants the constant `find` holds under `n` uses, or none when it holds none. -/
def successors (find : Name → Option ConstantInfo) (n : Name) : Array Name :=
  match find n with
  | some info => successorsOf info
  | none => #[]

/-- `x` is reachable from `n` along `successors find`, in zero or more steps. -/
inductive Reach (find : Name → Option ConstantInfo) : Name → Name → Prop
  /-- Every name reaches itself. -/
  | refl (n : Name) : Reach find n n
  /-- A name reaches whatever a constant it uses reaches. -/
  | step {n m x : Name} : m ∈ successors find n → Reach find m x → Reach find n x

/-- Reachability extends by one more used constant. -/
theorem Reach.tail {find : Name → Option ConstantInfo} {n x y : Name} (h : Reach find n x)
    (hy : y ∈ successors find x) : Reach find n y := by
  induction h with
  | refl => exact .step hy (.refl y)
  | step hm _ ih => exact .step hm (ih hy)

/-- Push `m` onto the pending names unless it was seen before. -/
private def pushNew (acc : List Name × Std.HashSet Name) (m : Name) :
    List Name × Std.HashSet Name :=
  if acc.2.contains m then acc else (m :: acc.1, acc.2.insert m)

/-- `pushNew` leaves a seen name's state unchanged. -/
private theorem pushNew_seen {p : List Name} {s : Std.HashSet Name} {m : Name}
    (h : s.contains m = true) : pushNew (p, s) m = (p, s) := by
  simp [pushNew, h]

/-- `pushNew` pushes and records an unseen name. -/
private theorem pushNew_unseen {p : List Name} {s : Std.HashSet Name} {m : Name}
    (h : ¬ s.contains m = true) : pushNew (p, s) m = (m :: p, s.insert m) := by
  simp [pushNew, h]

/-- What folding `pushNew` over `names` does to the pending names `p` and the seen names `s`. -/
private theorem foldl_pushNew (names p : List Name) (s : Std.HashSet Name) :
    (∀ x, x ∈ (names.foldl pushNew (p, s)).2 ↔ x ∈ s ∨ x ∈ names) ∧
    (∀ x ∈ (names.foldl pushNew (p, s)).1, x ∈ p ∨ x ∈ names) ∧
    (∀ x ∈ p, x ∈ (names.foldl pushNew (p, s)).1) ∧
    (∀ x ∈ (names.foldl pushNew (p, s)).2, x ∈ s ∨ x ∈ (names.foldl pushNew (p, s)).1) := by
  induction names generalizing p s with
  | nil => exact ⟨by simp, by simp, by simp, fun x hx => .inl hx⟩
  | cons m names ih =>
    simp only [List.foldl_cons]
    by_cases hm : s.contains m
    · rw [pushNew_seen hm]
      obtain ⟨h1, h2, h3, h4⟩ := ih p s
      have hms : m ∈ s := Std.HashSet.mem_iff_contains.mpr hm
      refine ⟨fun x => ?_, fun x hx => ?_, h3, h4⟩
      · rw [h1 x, List.mem_cons]
        constructor
        · rintro (hx | hx)
          · exact .inl hx
          · exact .inr (.inr hx)
        · rintro (hx | rfl | hx)
          · exact .inl hx
          · exact .inl hms
          · exact .inr hx
      · rcases h2 x hx with hx | hx
        · exact .inl hx
        · exact .inr (List.mem_cons_of_mem _ hx)
    · rw [pushNew_unseen hm]
      obtain ⟨h1, h2, h3, h4⟩ := ih (m :: p) (s.insert m)
      refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => h3 x (List.mem_cons_of_mem _ hx),
        fun x hx => ?_⟩
      · rw [h1 x, Std.HashSet.mem_insert, List.mem_cons, beq_iff_eq]
        constructor
        · rintro ((rfl | hx) | hx)
          · exact .inr (.inl rfl)
          · exact .inl hx
          · exact .inr (.inr hx)
        · rintro (hx | rfl | hx)
          · exact .inl (.inr hx)
          · exact .inl (.inl rfl)
          · exact .inr hx
      · rcases h2 x hx with hx | hx
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact .inr List.mem_cons_self
          · exact .inl hx
        · exact .inr (List.mem_cons_of_mem _ hx)
      · rcases h4 x hx with hx | hx
        · rcases Std.HashSet.mem_insert.mp hx with hx | hx
          · rw [← beq_iff_eq.mp hx]
            exact .inr (h3 m List.mem_cons_self)
          · exact .inl hx
        · exact .inr hx

/-- Expand the `pending` names, recording in `seen` every name ever pushed. It returns the seen
names once nothing is pending, or `none` when `fuel` runs out first. -/
def reachLoop (find : Name → Option ConstantInfo) :
    Nat → List Name → Std.HashSet Name → Option (Std.HashSet Name)
  | _, [], seen => some seen
  | 0, _ :: _, _ => none
  | fuel + 1, n :: rest, seen =>
    let next := (successors find n).toList.foldl pushNew (rest, seen)
    reachLoop find fuel next.1 next.2

/-- Every name reachable from the constants `start` uses, within `fuel` expansions, or `none`
when the fuel runs out. -/
def reachSet (find : Name → Option ConstantInfo) (fuel : Nat) (start : ConstantInfo) :
    Option (Std.HashSet Name) :=
  let first := (successorsOf start).toList.foldl pushNew ([], {})
  reachLoop find fuel first.1 first.2

/-- The loop invariant: pending names were seen; every seen name is pending or has every
successor seen; and every seen name is reachable from a constant `start` uses. -/
private def LoopInv (find : Name → Option ConstantInfo) (start : ConstantInfo)
    (pending : List Name) (seen : Std.HashSet Name) : Prop :=
  (∀ x ∈ pending, x ∈ seen) ∧
    (∀ x ∈ seen, x ∈ pending ∨ ∀ m ∈ successors find x, m ∈ seen) ∧
    ∀ x ∈ seen, ∃ m ∈ successorsOf start, Reach find m x

/-- A loop that returns from an invariant state returns a set closed under `successors`,
containing every seen name, and holding only names reachable from `start`'s constants. -/
private theorem reachLoop_some {find : Name → Option ConstantInfo} {start : ConstantInfo} :
    ∀ (fuel : Nat) (pending : List Name) (seen result : Std.HashSet Name),
      LoopInv find start pending seen → reachLoop find fuel pending seen = some result →
      (∀ x ∈ result, ∀ m ∈ successors find x, m ∈ result) ∧ (∀ x ∈ seen, x ∈ result) ∧
        ∀ x ∈ result, ∃ m ∈ successorsOf start, Reach find m x := by
  intro fuel
  induction fuel with
  | zero =>
    intro pending seen result hinv h
    cases pending with
    | nil =>
      simp only [reachLoop, Option.some.injEq] at h
      subst h
      refine ⟨fun x hx => ?_, fun _ hx => hx, hinv.2.2⟩
      rcases hinv.2.1 x hx with hx | hx
      · simp at hx
      · exact hx
    | cons n rest => simp [reachLoop] at h
  | succ fuel ih =>
    intro pending seen result hinv h
    cases pending with
    | nil =>
      simp only [reachLoop, Option.some.injEq] at h
      subst h
      refine ⟨fun x hx => ?_, fun _ hx => hx, hinv.2.2⟩
      rcases hinv.2.1 x hx with hx | hx
      · simp at hx
      · exact hx
    | cons n rest =>
      simp only [reachLoop] at h
      obtain ⟨f1, f2, f3, f4⟩ := foldl_pushNew (successors find n).toList rest seen
      have hn : n ∈ seen := hinv.1 n List.mem_cons_self
      obtain ⟨m₀, hm₀, hreach⟩ := hinv.2.2 n hn
      have inv : LoopInv find start ((successors find n).toList.foldl pushNew (rest, seen)).1
          ((successors find n).toList.foldl pushNew (rest, seen)).2 := by
        refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
        · rcases f2 x hx with hx | hx
          · exact (f1 x).mpr (.inl (hinv.1 x (List.mem_cons_of_mem _ hx)))
          · exact (f1 x).mpr (.inr hx)
        · rcases f4 x hx with hx | hx
          · rcases hinv.2.1 x hx with hp | hsucc
            · rcases List.mem_cons.mp hp with rfl | hp
              · exact .inr fun m hm => (f1 m).mpr (.inr (Array.mem_toList_iff.mpr hm))
              · exact .inl (f3 x hp)
            · exact .inr fun m hm => (f1 m).mpr (.inl (hsucc m hm))
          · exact .inl hx
        · rcases (f1 x).mp hx with hx | hx
          · exact hinv.2.2 x hx
          · exact ⟨m₀, hm₀, hreach.tail (Array.mem_toList_iff.mp hx)⟩
      obtain ⟨r1, r2, r3⟩ := ih _ _ result inv h
      exact ⟨r1, fun x hx => r2 x ((f1 x).mpr (.inl hx)), r3⟩

/-- A completed `reachSet` holds exactly the names reachable from the constants `start` uses:
every such name is in it, and every name in it is such a name. -/
theorem reachSet_some {find : Name → Option ConstantInfo} {fuel : Nat} {start : ConstantInfo}
    {result : Std.HashSet Name} (h : reachSet find fuel start = some result) :
    (∀ m ∈ successorsOf start, ∀ x, Reach find m x → x ∈ result) ∧
      ∀ x ∈ result, ∃ m ∈ successorsOf start, Reach find m x := by
  obtain ⟨f1, f2, -, f4⟩ := foldl_pushNew (successorsOf start).toList [] {}
  have inv : LoopInv find start ((successorsOf start).toList.foldl pushNew ([], {})).1
      ((successorsOf start).toList.foldl pushNew ([], {})).2 := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · rcases f2 x hx with hx | hx
      · simp at hx
      · exact (f1 x).mpr (.inr hx)
    · rcases f4 x hx with hx | hx
      · simp at hx
      · exact .inl hx
    · rcases (f1 x).mp hx with hx | hx
      · simp at hx
      · exact ⟨x, Array.mem_toList_iff.mp hx, .refl x⟩
  obtain ⟨closed, contains, sound⟩ := reachLoop_some fuel _ _ result inv h
  refine ⟨fun m hm x hx => ?_, sound⟩
  have hm' : m ∈ result := contains m ((f1 m).mpr (.inr (Array.mem_toList_iff.mpr hm)))
  clear hm
  induction hx with
  | refl => exact hm'
  | step hs _ ih => exact ih (closed _ hm' _ hs)

/-- Whether `find` holds an axiom under `n`. -/
def isAxiomIn (find : Name → Option ConstantInfo) (n : Name) : Bool :=
  match find n with
  | some (.axiomInfo _) => true
  | _ => false

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
  RenamedOK checked info ∧ (∀ m ∈ successorsOf info, ¬ Reach find m name) ∧
    (∀ m ∈ successorsOf info, ∀ a, Reach find m a → isAxiomIn find a = true →
      ∃ m' ∈ successorsOf held, Reach checked.find? m' a) ∧
    ∀ m' ∈ successorsOf held, ∀ a, Reach checked.find? m' a → isAxiomIn checked.find? a = true →
      ∃ m ∈ successorsOf info, Reach find m a

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
          · exact soundHeld a (extraAxioms_nil hx.1 a (complete m hm a ha) hax)
          · exact sound a (extraAxioms_nil hx.2 a (completeHeld m hm a ha) hax)
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
    (shared copy = true → sameTheorem held copy.info = true) ∧
    (identical held copy.info = true ∨ ProofOK checked checked.find? copy.name held copy.info) ∧
    (identical held keptInfo = true ∨
      sameTheorem held keptInfo = true ∧ ProofOK checked kept copy.name held keptInfo)

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
        exact ⟨held, keptInfo, rfl, rfl, checkShared_ok h1, checkOwn_ok h2, checkKept_ok h3⟩
  · left
    refine ⟨hu, ?_⟩
    cases hs : shared copy
    · rfl
    · simp [hu, hs] at h

/-- Check every copy (`checkCopy`), stopping at the first refusal. -/
def checkCopies (checked : Kernel.Environment) (kept : Name → Option ConstantInfo) (fuel : Nat)
    (shared : Copy → Bool) (copies : Array Copy) : Except CopyFailure Unit :=
  forM copies (checkCopy checked kept fuel shared)

/-- A successful `checkCopies` admits every copy. -/
theorem checkCopies_sound {checked : Kernel.Environment} {kept : Name → Option ConstantInfo}
    {fuel : Nat} {shared : Copy → Bool} {copies : Array Copy}
    (h : checkCopies checked kept fuel shared copies = .ok ()) :
    ∀ copy ∈ copies, CopyAdmitted checked kept shared copy :=
  fun copy hc => checkCopy_ok (forM_eq_ok.mp h copy hc)

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

/-- Replay the completed owned logical declarations against trusted imports, except those of
the `reused` modules, which stay in the replay base with the trusted imports. The declarations
are the constants of each replayed module's own data (`Copy`). Every name of a copy that the base
lacks is replayed with the constant the audited environment `env` holds under it, the copy whose
statement and value reports read (`replayMap_sound`, `replayMap_complete`); every copy is then
checked against the replayed kernel and `env` (`checkCopies_sound`). The receipt's `shared`
modules contain a copy of a name that the base or another replayed module also declares; their
admission depends on which copy this environment keeps, so they are not offered for reuse. The
original environment is retained for compiler metadata only after replay succeeds. This is not a
fresh replay of the imported dependency graph. -/
unsafe def validate (env : Environment) (ownedModules : Array Name) (reused : Array Name := #[]) :
    IO (Except ProducerReport.AdmissionFailure ProducerReport.AdmissionReceipt) := do
  let mut replayModules := ownedModules.filter (!reused.contains ·)
  -- The force-loaded reporter now depends on the positive policy library.
  -- Replay these exact checker implementation modules too; importing them into
  -- the base would reintroduce unchecked owned policy declarations. They do not
  -- become claimed surfaces, and arbitrary reverse imports remain forbidden.
  let reporterModules := #[`Regula.Probe, `Regula.Report,
    `Regula.Checker.PolicyCodec, `Regula.StructuralName]
  for _ in [:reporterModules.size] do
    for (name, data) in env.header.moduleNames.zip env.header.moduleData do
      if reporterModules.contains name && !replayModules.contains name &&
          data.imports.any (fun imp => replayModules.contains imp.module) then
        replayModules := replayModules.push name
  let owned := replayModules.foldl (fun names name => names.insert name) ({} : NameSet)
  let mut copies : Array Copy := #[]
  let mut imports : Array Import := #[]
  for (name, data) in env.header.moduleNames.zip env.header.moduleData do
    if owned.contains name then
      -- Lean's import keys each constant of the module by the name listed beside it.
      unless data.constNames.size == data.constants.size do
        return .error ⟨s!"{failureTag} module {name} lists {data.constNames.size} constant \
          names for {data.constants.size} constants"⟩
      for constName in data.constNames, info in data.constants do
        unless info.name == constName do
          return .error ⟨s!"{failureTag} module {name} lists constant {info.name} under the \
            name {constName}"⟩
        copies := copies.push { «module» := name, info }
      continue
    -- Importing such a module would put unchecked owned declarations back in
    -- the trusted base. Ownership must be expanded or the claim rejected.
    if data.imports.any (fun imp => owned.contains imp.module) then
      return .error ⟨s!"{failureTag} unreplayed module {name} imports a replayed module"⟩
    imports := imports.push { module := name, importAll := true }
  let required := copies.filterMap fun copy =>
    if copy.info.isUnsafe || copy.info.isPartial then none else some (copy.module, copy.name)
  let counts := nameCounts copies
  -- Every search expands each name at most once; the audited environment declares no more names
  -- than its modules list constants.
  let fuel := env.header.moduleData.foldl (fun total data => total + data.constants.size) 0
  let base ← importModules imports {} 0 (loadExts := false) (level := .private)
  try
    let find := base.toKernelEnv.find?
    let shared (copy : Copy) : Bool := (find copy.name).isSome || 2 ≤ counts.getD copy.name 0
    let checked ← Lean.Kernel.Environment.replay (replayMap find env.find? copies)
      base.toKernelEnv
    if let .error failure := checkCopies checked env.find? fuel shared copies then
      throw <| IO.userError (← failure.describe)
    for key in required do
      if (checked.find? key.2).isNone then
        throw <| IO.userError s!"missing replayed declaration {key.2}"
    return .ok { modules := RegulaPolicy.canonicalNames replayModules, required,
                 admitted := required, reused := RegulaPolicy.canonicalNames reused,
                 shared := RegulaPolicy.canonicalNames ((copies.filter shared).map (·.module)) }
  catch error =>
    return .error ⟨s!"{failureTag} {error}"⟩
  finally
    -- No replay environment escapes this function. Release its separately
    -- imported regions, as Lean's bundled replay checker does.
    base.freeRegions

end Regula.Checker.Admission
