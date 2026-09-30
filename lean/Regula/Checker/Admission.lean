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
has every copy checked (`planReplay_sound`, `checkDuplicates_sound`).
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
module in that closure refers only to constants of its own closure (`referencesWithin`), and
every owned module the closure contains is reused too. When the last condition fails for the
filtered set, nothing is reused. Every other owned module is replayed. `mem_reusedModules`
states this contract. -/
def reusedModules (env : Environment) (origins : Array RegulaPolicy.ModuleOrigin)
    (requested owned : Array Name) (priors : Array PriorAdmission) : Array Name :=
  let here := originIndex origins
  let earlier := indexPriors priors
  let settled := owned.filterMap fun m =>
    (offeredClosure earlier here requested m).bind fun closure =>
      if referencesWithin env m closure then some (m, closure) else none
  let ownedSet := Std.HashSet.ofList owned.toList
  let kept := settled.filter
    (closureWithin ownedSet (Std.HashSet.ofList (settled.map (·.1)).toList))
  if kept.all (closureWithin ownedSet (Std.HashSet.ofList (kept.map (·.1)).toList)) then
    kept.map (·.1)
  else #[]

/-- Every reused module is an owned, unrequested module that some prior offers over the
import closure it has here, whose declarations refer only to that closure, and whose closure's
owned modules are all reused too, so reuse never leaves an owned import to replay. -/
theorem mem_reusedModules {env : Environment} {origins : Array RegulaPolicy.ModuleOrigin}
    {requested owned : Array Name} {priors : Array PriorAdmission} {m : Name}
    (h : m ∈ reusedModules env origins requested owned priors) :
    m ∈ owned ∧ m ∉ requested ∧ ∃ closure,
      importClosure (originIndex origins) m = some closure ∧
      referencesWithin env m closure = true ∧
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
        simp only [Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        obtain ⟨hreq, hclosure, entry, hentry, hm, hc⟩ := offeredClosure_eq_some.mp ho
        obtain ⟨prior, hprior, rfl⟩ := Array.mem_map.mp hentry
        refine ⟨ha, hreq, found, hclosure, hrefs, ⟨prior, hprior, hm, hc⟩, ?_⟩
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
same statement. The merged environment therefore does not show every copy, and
`Kernel.Environment.replay` skips a theorem whose name it already holds with that statement
without checking its proof. Replay reads each replayed module's own constants instead, and
admits a shared name only under `sameTheorem` (`Regula.Checker.SharedName`). -/

/-- A constant that a replayed module's own `.olean` data contains, with that module. -/
structure Copy where
  /-- The replayed module whose data contains the constant. -/
  «module» : Name
  /-- The constant as that module's data stores it. -/
  info : ConstantInfo

/-- The name the copy declares, which Lean's import and the kernel key it by. -/
abbrev Copy.name (copy : Copy) : Name := copy.info.name

/-- How `validate` checks each copy: the first copy of each name absent from the replay base is
replayed under that name; every other copy is a duplicate, paired with the constant of its name
that the replayed kernel holds. -/
structure ReplayPlan where
  /-- The copies to replay under their own names, by name. -/
  replay : Std.HashMap Name ConstantInfo := {}
  /-- Every other copy, with the constant of its name in the replay base or in `replay`. -/
  duplicates : Array (Copy × ConstantInfo) := #[]

/-- Place one copy against the constants `base` finds in the replay base (`planReplay`). -/
def ReplayPlan.add (base : Name → Option ConstantInfo) (plan : ReplayPlan) (copy : Copy) :
    ReplayPlan :=
  match base copy.name with
  | some held => { plan with duplicates := plan.duplicates.push (copy, held) }
  | none =>
    match plan.replay[copy.name]? with
    | some held => { plan with duplicates := plan.duplicates.push (copy, held) }
    | none => { plan with replay := plan.replay.insert copy.name copy.info }

/-- Place every copy, in order, against the constants `base` finds in the replay base. -/
def planReplay (base : Name → Option ConstantInfo) (copies : Array Copy) : ReplayPlan :=
  copies.foldl (ReplayPlan.add base) {}

/-- What `planReplay` maintains over the copies `seen` so far. -/
structure ReplayPlan.Placed (base : Name → Option ConstantInfo) (seen : List Copy)
    (plan : ReplayPlan) : Prop where
  /-- No replayed name is in the replay base. -/
  fresh : ∀ n ∈ plan.replay, base n = none
  /-- Every copy seen is a duplicate or the one replayed under its name. -/
  covered : ∀ c ∈ seen,
    (∃ held, (c, held) ∈ plan.duplicates) ∨ plan.replay[c.name]? = some c.info
  /-- Every duplicate was seen, paired with the base constant of its name or, when the base
  has none, with the copy replayed under it. -/
  paired : ∀ c held, (c, held) ∈ plan.duplicates → c ∈ seen ∧
    (base c.name = some held ∨ base c.name = none ∧ plan.replay[c.name]? = some held)
  /-- Every replayed constant is a copy seen, under its own name. -/
  replayed : ∀ n info, plan.replay[n]? = some info → ∃ c ∈ seen, c.name = n ∧ c.info = info

/-- Placing a copy that becomes a duplicate paired with `held` keeps `Placed`, provided `held` is
the base constant of its name or, when the base has none, the one replayed under it. -/
private theorem ReplayPlan.Placed.push {base : Name → Option ConstantInfo} {seen : List Copy}
    {plan : ReplayPlan} (h : plan.Placed base seen) {copy : Copy} {held : ConstantInfo}
    (hheld : base copy.name = some held ∨
      base copy.name = none ∧ plan.replay[copy.name]? = some held) :
    ReplayPlan.Placed base (seen ++ [copy])
      { plan with duplicates := plan.duplicates.push (copy, held) } := by
  refine ⟨h.fresh, fun c hc => ?_, fun c held' hd => ?_, fun n info hr => ?_⟩
  · rcases List.mem_append.mp hc with hc | hc
    · rcases h.covered c hc with ⟨held', hd⟩ | hr
      · exact .inl ⟨held', Array.mem_push_of_mem _ hd⟩
      · exact .inr hr
    · rw [List.mem_singleton.mp hc]
      exact .inl ⟨held, Array.mem_push_self⟩
  · rcases Array.mem_push.mp hd with hd | hd
    · obtain ⟨hs, hp⟩ := h.paired c held' hd
      exact ⟨List.mem_append_left _ hs, hp⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hd
      exact ⟨List.mem_append_right _ (List.mem_singleton_self _), hheld⟩
  · obtain ⟨c, hc, hn, hi⟩ := h.replayed n info hr
    exact ⟨c, List.mem_append_left _ hc, hn, hi⟩

/-- `ReplayPlan.add` keeps `Placed`. -/
private theorem ReplayPlan.Placed.add {base : Name → Option ConstantInfo} {seen : List Copy}
    {plan : ReplayPlan} (h : plan.Placed base seen) (copy : Copy) :
    (plan.add base copy).Placed base (seen ++ [copy]) := by
  unfold ReplayPlan.add
  split
  · rename_i held hb
    exact h.push (.inl hb)
  · rename_i hb
    split
    · rename_i held hr
      exact h.push (.inr ⟨hb, hr⟩)
    · rename_i hr
      -- A lookup of any other name is unchanged by the insertion.
      have other : ∀ n : Name, plan.replay[n]?.isSome → (plan.replay.insert copy.name copy.info)[n]? =
          plan.replay[n]? := by
        intro n hn
        rw [Std.HashMap.getElem?_insert]
        split
        · rename_i heq
          rw [← beq_iff_eq.mp heq, hr] at hn
          exact absurd hn (by simp)
        · rfl
      refine ⟨fun n hn => ?_, fun c hc => ?_, fun c held hd => ?_, fun n info hn => ?_⟩
      · rcases Std.HashMap.mem_insert.mp hn with hn | hn
        · rw [← beq_iff_eq.mp hn]
          exact hb
        · exact h.fresh n hn
      · rcases List.mem_append.mp hc with hc | hc
        · rcases h.covered c hc with hd | hr'
          · exact .inl hd
          · exact .inr ((other c.name (by simp [hr'])).trans hr')
        · rw [List.mem_singleton.mp hc]
          exact .inr Std.HashMap.getElem?_insert_self
      · obtain ⟨hs, hp⟩ := h.paired c held hd
        refine ⟨List.mem_append_left _ hs, ?_⟩
        rcases hp with hp | ⟨hbn, hrp⟩
        · exact .inl hp
        · exact .inr ⟨hbn, (other c.name (by simp [hrp])).trans hrp⟩
      · rw [Std.HashMap.getElem?_insert] at hn
        split at hn
        · rename_i heq
          obtain rfl := Option.some.inj hn
          exact ⟨copy, List.mem_append_right _ (List.mem_singleton_self _),
            beq_iff_eq.mp heq, rfl⟩
        · obtain ⟨c, hc, hcn, hci⟩ := h.replayed n info hn
          exact ⟨c, List.mem_append_left _ hc, hcn, hci⟩

/-- `planReplay` checks every copy and never replays over the base: no replayed name is in the
replay base; every copy is a duplicate or the one replayed under its name; every duplicate is
paired with the constant the replayed kernel holds under its name (the base's, or when the base
has none the replayed copy's); and every replayed constant is a copy, under its own name. -/
theorem planReplay_sound (base : Name → Option ConstantInfo) (copies : Array Copy) :
    (planReplay base copies).Placed base copies.toList := by
  unfold planReplay
  rw [← Array.foldl_toList]
  suffices step : ∀ (rest seen : List Copy) (plan : ReplayPlan), plan.Placed base seen →
      (rest.foldl (ReplayPlan.add base) plan).Placed base (seen ++ rest) by
    simpa using step copies.toList [] {} ⟨by simp, by simp, by simp, by simp⟩
  intro rest
  induction rest with
  | nil => intro seen plan h; simpa using h
  | cons copy rest ih =>
    intro seen plan h
    simpa using ih (seen ++ [copy]) (plan.add base copy) (h.add copy)

/-- Why a duplicate copy is not admitted. -/
inductive DuplicateFailure where
  /-- The copy and the constant the replayed kernel holds under its name are not theorems Lean's
  import accepts together. -/
  | differs (copy : Copy)
  /-- The kernel rejected the copy's own proof. -/
  | rejected (copy : Copy) (error : Kernel.Exception)

/-- The name under which `checkDuplicates` has the kernel check a duplicate theorem's own proof;
the kernel's theorem check requires it to be undeclared. -/
def proofCheckName (copy : Copy) : Name := .num (.str copy.name "regula_duplicate_proof") 0

/-- Check every duplicate against the replayed kernel `checked`: the copy and the constant of its
name that the kernel holds must be theorems Lean's import accepts together (`sameTheorem`), and
the kernel must accept the copy itself, which `Kernel.Environment.replay` would skip, renamed to
`proofCheckName`, with the same zero heartbeat and recursion limits as that replay. -/
def checkDuplicates (checked : Kernel.Environment) (duplicates : Array (Copy × ConstantInfo)) :
    Except DuplicateFailure Unit :=
  forM duplicates fun (copy, held) => do
    unless sameTheorem held copy.info do throw (.differs copy)
    let .thmInfo val := copy.info | throw (.differs copy)
    match checked.addDeclCore 0 0 (.thmDecl { val with name := proofCheckName copy }) none with
    | .ok _ => pure ()
    | .error error => throw (.rejected copy error)

/-- A successful `checkDuplicates` accepted every duplicate: it and the constant it is paired with
are theorems Lean's import accepts together, and the kernel added the copy, renamed to
`proofCheckName`, to `checked`. -/
theorem checkDuplicates_sound {checked : Kernel.Environment}
    {duplicates : Array (Copy × ConstantInfo)} (h : checkDuplicates checked duplicates = .ok ())
    {copy : Copy} {held : ConstantInfo} (hd : (copy, held) ∈ duplicates) :
    sameTheorem held copy.info = true ∧ ∃ val, copy.info = .thmInfo val ∧ ∃ env,
      checked.addDeclCore 0 0 (.thmDecl { val with name := proofCheckName copy }) none =
        .ok env := by
  have step := forM_eq_ok.mp h _ hd
  simp only at step
  cases hs : sameTheorem held copy.info
  · simp [hs] at step
  · simp only [true_and]
    simp only [hs] at step
    cases hi : copy.info with
    | thmInfo val =>
      simp only [hi] at step
      refine ⟨val, rfl, ?_⟩
      cases ha : checked.addDeclCore 0 0 (.thmDecl { val with name := proofCheckName copy }) none
      · simp [ha] at step
      · exact ⟨_, rfl⟩
    | _ => simp [hi] at step

/-- The detail of a duplicate failure. -/
def DuplicateFailure.describe : DuplicateFailure → IO String
  | .differs copy => pure s!"owned declaration {copy.name} of module {copy.module} shares its \
      name with a constant of the replay base or of another replayed module, and the two are not \
      theorems of the same statement, universe parameters and mutual block, the only shared name \
      admission admits"
  | .rejected copy error => do
    return s!"the kernel rejected the proof of owned declaration {copy.name} of module \
      {copy.module}, a copy of a theorem of that name that the replay base or another replayed \
      module also contains: {← (error.toMessageData {}).toString}"

/-- The tag of every kernel-admission failure detail. An admission failure leaves the affected
claim incomplete (RG2005), so the tag does not call it a violation. -/
def failureTag : String := "[INCOMPLETE[kernel-admission]]"

/-- Replay the completed owned logical declarations against trusted imports, except those of
the `reused` modules, which stay in the replay base with the trusted imports. The declarations
are the constants of each replayed module's own data (`Copy`), not the single copy of a name
that the merged environment keeps: the first copy of each name absent from the base is replayed
under that name (`planReplay_sound`), and every other copy is admitted only as a theorem Lean's
import accepts beside the constant the replayed kernel holds, whose own proof the kernel accepts
under a fresh name (`checkDuplicates_sound`). The original environment is retained for compiler
metadata only after replay succeeds. This is not a fresh replay of the imported dependency
graph. -/
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
  let base ← importModules imports {} 0 (loadExts := false) (level := .private)
  try
    let plan := planReplay base.toKernelEnv.find? copies
    let checked ← Lean.Kernel.Environment.replay plan.replay base.toKernelEnv
    if let .error failure := checkDuplicates checked plan.duplicates then
      throw <| IO.userError (← failure.describe)
    for key in required do
      if (checked.find? key.2).isNone then
        throw <| IO.userError s!"missing replayed declaration {key.2}"
    return .ok { modules := RegulaPolicy.canonicalNames replayModules, required,
                 admitted := required, reused := RegulaPolicy.canonicalNames reused }
  catch error =>
    return .error ⟨s!"{failureTag} {error}"⟩
  finally
    -- No replay environment escapes this function. Release its separately
    -- imported regions, as Lean's bundled replay checker does.
    base.freeRegions

end Regula.Checker.Admission
