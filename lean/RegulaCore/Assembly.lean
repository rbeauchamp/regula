import RegulaCore.Policy
import RegulaPolicy.Community
import RegulaPolicy.Acceptance
import RegulaPolicy.Traversal

/-! # Acceptance census assembly

Pure assembly of the acceptance census and job observations from the decoded manifest,
Lake inventory, producer history and frozen environment records. Contracts cover what
nothing downstream decides again: each surface's profile and execution claim and its
module order (`conformingProfile`, `surfaceAssignments`), exact history copies
(`histories`), the frozen environment an environment job reads (`checked_environmentJob`),
and, as soundness only, which record within that environment supplies
documentation-presence evidence (`checked_environmentEvidence`). The claimed
`accept` binds every other stage's observation to its job (`ResultBound`, `PolicyOK`,
`StageOK`). Manifest parsing, Lake loading and environment
extraction stay in the operational adapters; these definitions do not authenticate those
observations. -/

universe u

namespace Regula.Checker.Manifest

open Regula.Checker.Policy (Profile)

structure Surface where
  library : String
  executables : Array String
  claim : Profile
  execution : RegulaPolicy.ExecutionClaim
  rationale : String
  deriving Repr

structure ExcludedLibrary where
  library : String
  rationale : String
  deriving Repr

structure ExcludedExecutable where
  executable : String
  rationale : String
  deriving Repr

end Regula.Checker.Manifest

namespace Regula.Checker

structure Manifest where
  surfaces : Array Manifest.Surface
  excludedLibraries : Array Manifest.ExcludedLibrary
  excludedExecutables : Array Manifest.ExcludedExecutable
  deriving Repr

end Regula.Checker

namespace Regula.Checker.Lake

open Lean (Name)
open System (FilePath)

structure SourceEntry where
  «module» : Name
  source : FilePath
  deriving Repr, BEq

structure LibraryInventory where
  library : String
  modules : Array Name
  sources : Array SourceEntry
  /-- The Lean options and extra `lean` arguments Lake builds the library's modules with
  (RG2006). -/
  options : RegulaPolicy.Community.BuildOptions
  deriving Repr, BEq

structure ExecutableInventory where
  executable : String
  root : Name
  source : FilePath
  /-- The Lean options and extra `lean` arguments Lake builds the root module with (RG2006). -/
  options : RegulaPolicy.Community.BuildOptions
  deriving Repr, BEq

structure DependencyInventory where
  package : String
  root : FilePath
  configurationPaths : Array FilePath
  sources : Array SourceEntry
  deriving Repr, BEq

structure SurfaceInventory where
  root : FilePath
  leanLibDir : FilePath
  leanPath : Array FilePath
  leanSrcPath : Array FilePath
  libraries : Array LibraryInventory
  executables : Array ExecutableInventory
  dependencies : Array DependencyInventory
  deriving Repr, BEq

end Regula.Checker.Lake

namespace Regula.Checker.ProducerReport

/-- Completed history preserves the exact Lean-resolved source before/after the worker.
Unavailable history has no successful source receipt or usable edge payload. -/
inductive HistoryOutcome where
  | completed (path before after : String) (replacements : Array (Lean.Name × Lean.Name))
  | unavailable (detail : String)
  deriving Repr

end Regula.Checker.ProducerReport

namespace Regula.Checker.Acceptance

open Lean (Name)
open RegulaPolicy
open Regula.Checker.Policy (Profile request request_contract)

/-- Required meaning of a surface's manifest profile: exactly the conforming profile of
the same spelling, and a refusal exactly for compiler-trusting. -/
def ConformingProfileContract (select : Profile → Except String ConformingProfile) : Prop :=
  (∀ profile conforming, select profile = .ok conforming ↔
    profile.toString = conforming.spelling) ∧
  ∀ profile, (∃ e, select profile = .error e) ↔ profile = .compilerTrusting

private def conformingProfileImpl (profile : Profile) : Except String ConformingProfile :=
  match request (some profile) with
  | .conforming conforming => .ok conforming
  | _ => .error "compiler-trusting inspection is not a conforming claim"

private theorem conformingProfileImpl_ok (profile : Profile) (conforming : ConformingProfile) :
    conformingProfileImpl profile = .ok conforming ↔
      request (some profile) = .conforming conforming := by
  cases h : request (some profile) <;> simp [conformingProfileImpl, h]

/-- Registers `ConformingProfileContract`, reducing it to `RequestContract`. -/
theorem checked_conformingProfile :
    Regula.ExecutableContract conformingProfileImpl ConformingProfileContract := by
  have req := request_contract
  refine ⟨⟨fun profile conforming =>
    (conformingProfileImpl_ok profile conforming).trans ((req.2 profile).2 conforming),
    fun profile => ⟨?_, ?_⟩⟩⟩
  · rintro ⟨e, he⟩
    cases profile
    · rw [(conformingProfileImpl_ok _ .kernelOnly).mpr (((req.2 _).2 _).mpr rfl)] at he; cases he
    · rw [(conformingProfileImpl_ok _ .choiceFree).mpr (((req.2 _).2 _).mpr rfl)] at he; cases he
    · rw [(conformingProfileImpl_ok _ .standardLogical).mpr (((req.2 _).2 _).mpr rfl)] at he
      cases he
    · rfl
  · rintro rfl
    exact ⟨"compiler-trusting inspection is not a conforming claim",
      by simp [conformingProfileImpl, (req.2 Profile.compilerTrusting).1.mpr rfl]⟩

/-- Positive maxima remain distinct from no-profile and compiler-trusting classification.
Through `checked_conformingProfile`. -/
def conformingProfile (profile : Profile) : Except String ConformingProfile :=
  checked_conformingProfile.run profile

/-- Required claim surface for one manifest surface: its library name and execution claim,
the conforming profile its claim spells, and the modules of the first Lake library of that
name followed by the root of the first Lake executable of each claimed executable name. -/
def SurfaceAssigned (inventory : Lake.SurfaceInventory) (surface : Manifest.Surface)
    (assigned : SurfaceAssignment) : Prop :=
  assigned.target = surface.library ∧ assigned.execution = surface.execution ∧
  surface.claim.toString = assigned.profile.spelling ∧
  ∃ library, inventory.libraries.find? (·.library == surface.library) = some library ∧
    ∃ roots : List Name, roots.length = surface.executables.size ∧
      (∀ i (h : i < surface.executables.size) (h' : i < roots.length),
        (inventory.executables.find? (·.executable == surface.executables[i])).map (·.root) =
          some roots[i]) ∧
      assigned.modules.toList.map (·.name) = library.modules.toList ++ roots

/-- Required census assignment: success exactly with one `SurfaceAssigned` claim surface
per manifest surface, in manifest order. -/
def SurfaceAssignmentsContract
    (assign : Manifest → Lake.SurfaceInventory → Except String (Array SurfaceAssignment)) :
    Prop :=
  ∀ manifest inventory out, assign manifest inventory = .ok out ↔
    out.size = manifest.surfaces.size ∧
    ∀ i (h : i < manifest.surfaces.size) (h' : i < out.size),
      SurfaceAssigned inventory manifest.surfaces[i] out[i]

private def executableRoot (inventory : Lake.SurfaceInventory) (name : String) :
    Except String Name :=
  match inventory.executables.find? (·.executable == name) with
  | some exe => .ok exe.root
  | none => .error "manifest executable missing from Lake discovery"

private def assignSurface (inventory : Lake.SurfaceInventory) (surface : Manifest.Surface) :
    Except String SurfaceAssignment := do
  let some library := inventory.libraries.find? (·.library == surface.library)
    | throw "manifest surface missing from Lake discovery"
  let roots ← surface.executables.toList.mapM (executableRoot inventory)
  let modules ← (library.modules.toList ++ roots).mapM admitIdentity
  let profile ← conformingProfile surface.claim
  return ⟨surface.library, modules.toArray, profile, surface.execution⟩

private def surfaceAssignmentsImpl (manifest : Manifest)
    (inventory : Lake.SurfaceInventory) : Except String (Array SurfaceAssignment) :=
  List.toArray <$> manifest.surfaces.toList.mapM (assignSurface inventory)

private theorem executableRoot_ok (inventory : Lake.SurfaceInventory) (name : String)
    (root : Name) : executableRoot inventory name = .ok root ↔
      (inventory.executables.find? (·.executable == name)).map (·.root) = some root := by
  unfold executableRoot
  cases inventory.executables.find? (·.executable == name) <;> simp

private theorem admitIdentity_ok (n : Name) (identity : Identity) :
    admitIdentity n = .ok identity ↔ identity.name = n := by
  constructor
  · intro h
    unfold admitIdentity at h
    split at h
    · cases h; rfl
    · cases h
  · rintro rfl
    rw [admitIdentity_exact identity.name identity.nonanonymous]

private theorem admitIdentities_ok (names : List Name) (identities : List Identity) :
    names.mapM admitIdentity = .ok identities ↔ identities.map (·.name) = names := by
  rw [mapM_eq_ok]
  constructor
  · rintro ⟨hl, hi⟩
    apply List.ext_getElem (by simp [hl])
    intro i h h'
    simpa using (admitIdentity_ok _ _).mp (hi i h' (by simpa using h))
  · intro h
    subst h
    refine ⟨by simp, fun i h h' => (admitIdentity_ok _ _).mpr ?_⟩
    simp

private theorem assignSurface_ok (inventory : Lake.SurfaceInventory) (surface : Manifest.Surface)
    (assigned : SurfaceAssignment) :
    assignSurface inventory surface = .ok assigned ↔ SurfaceAssigned inventory surface assigned := by
  have rootsOk : ∀ roots : List Name,
      surface.executables.toList.mapM (executableRoot inventory) = .ok roots ↔
        roots.length = surface.executables.size ∧
        ∀ i (h : i < surface.executables.size) (h' : i < roots.length),
          (inventory.executables.find? (·.executable == surface.executables[i])).map (·.root) =
            some roots[i] := by
    intro roots
    rw [mapM_eq_ok]
    simp only [Array.length_toList, Array.getElem_toList, executableRoot_ok]
  unfold assignSurface SurfaceAssigned
  cases hl : inventory.libraries.find? (·.library == surface.library) with
  | none => simp
  | some library =>
    simp only [Option.some.injEq, exists_eq_left']
    cases hr : surface.executables.toList.mapM (executableRoot inventory) with
    | error e =>
      simp only [bind, Except.bind, reduceCtorEq, false_iff, not_and, not_exists]
      intro _ _ _ roots hlen hroots _
      rw [(rootsOk roots).mpr ⟨hlen, hroots⟩] at hr
      cases hr
    | ok roots =>
      have ⟨hlen, hroots⟩ := (rootsOk roots).mp hr
      cases hm : (library.modules.toList ++ roots).mapM admitIdentity with
      | error e =>
        simp only [hm, bind, Except.bind, reduceCtorEq, false_iff, not_and, not_exists]
        intro _ _ _ roots' hlen' hroots' hnames
        have same : roots' = roots := by
          apply List.ext_getElem (by rw [hlen, hlen'])
          intro i h h'
          have a := hroots' i (by omega) h
          have b := hroots i (by omega) h'
          rw [a] at b
          exact Option.some.inj b
        subst same
        rw [(admitIdentities_ok _ assigned.modules.toList).mpr hnames] at hm
        cases hm
      | ok modules =>
        have hnames := (admitIdentities_ok _ _).mp hm
        cases hp : conformingProfile surface.claim with
        | error e =>
          simp only [hm, bind, Except.bind, reduceCtorEq, false_iff, not_and, not_exists]
          intro _ _ hspell _ _ _ _
          have := (checked_conformingProfile.evidence.1 surface.claim assigned.profile).mpr hspell
          change conformingProfile surface.claim = _ at this
          rw [hp] at this
          cases this
        | ok profile =>
          have hspell := (checked_conformingProfile.evidence.1 surface.claim profile).mp hp
          simp only [hm, bind, Except.bind, pure, Except.pure, Except.ok.injEq]
          constructor
          · rintro rfl
            exact ⟨rfl, rfl, hspell, roots, hlen, hroots, by simpa using hnames⟩
          · rintro ⟨ht, he, hs, roots', hlen', hroots', hn⟩
            have same : roots' = roots := by
              apply List.ext_getElem (by rw [hlen, hlen'])
              intro i h h'
              have a := hroots' i (by omega) h
              have b := hroots i (by omega) h'
              rw [a] at b
              exact Option.some.inj b
            subst same
            have hmods : assigned.modules.toList = modules := by
              have := (admitIdentities_ok _ assigned.modules.toList).mpr hn
              rw [hm] at this
              exact (Except.ok.inj this).symm
            have hprof : assigned.profile = profile := by
              have h2 : assigned.profile.spelling = profile.spelling := hs.symm.trans hspell
              revert h2
              generalize assigned.profile = q
              cases q <;> cases profile <;> simp [ConformingProfile.spelling]
            cases assigned with
            | mk target mods prof exec =>
              simp only at ht he hmods hprof
              subst ht he hprof
              rw [← hmods]

/-- Registers `SurfaceAssignmentsContract` about the executed census assignment. -/
theorem checked_surfaceAssignments :
    Regula.ExecutableContract surfaceAssignmentsImpl SurfaceAssignmentsContract := by
  refine ⟨fun manifest inventory out => ?_⟩
  unfold surfaceAssignmentsImpl
  constructor
  · intro h
    cases hm : manifest.surfaces.toList.mapM (assignSurface inventory) with
    | error e => simp [hm, Functor.map, Except.map] at h
    | ok assigned =>
      simp only [hm, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      have ⟨hl, hi⟩ := (mapM_eq_ok _ _ _).mp hm
      refine ⟨by simpa using hl, fun i h h' => ?_⟩
      have step := hi i (by simpa using h) (by simpa using h')
      rw [Array.getElem_toList] at step
      exact (assignSurface_ok _ _ _).mp (by simpa using step)
  · rintro ⟨hl, hi⟩
    have hm : manifest.surfaces.toList.mapM (assignSurface inventory) = .ok out.toList :=
      (mapM_eq_ok _ _ _).mpr ⟨by simpa using hl, fun i h h' =>
        by simpa using (assignSurface_ok _ _ _).mpr (hi i (by simpa using h) (by simpa using h'))⟩
    simp [hm, Functor.map, Except.map]

/-- Construct requested surface assignments solely from the frozen manifest and Lake
inventory, before looking at returned declarations or policy results. Through
`checked_surfaceAssignments`. -/
def surfaceAssignments (manifest : Manifest) (inventory : Lake.SurfaceInventory) :
    Except String (Array SurfaceAssignment) :=
  checked_surfaceAssignments.run manifest inventory

/-- Manifest classification of every library and executable, as a total projection. The
claimed `TargetPartitionOK` checks it against discovery and the claim surfaces. -/
def configuredTargets (manifest : Manifest) : Array TargetAssignment :=
  manifest.surfaces.flatMap (fun surface =>
    #[⟨.library, surface.library, some surface.library⟩] ++
      surface.executables.map (fun name => ⟨.executable, name, some surface.library⟩)) ++
  manifest.excludedLibraries.map (fun excluded => ⟨.library, excluded.library, none⟩) ++
  manifest.excludedExecutables.map (fun excluded => ⟨.executable, excluded.executable, none⟩)

/-- Lake discovery as targets, as a total projection. -/
def discoveredTargets (inventory : Lake.SurfaceInventory) : Array DiscoveredTarget :=
  inventory.libraries.map (fun library => ⟨.library, library.library, library.modules⟩) ++
  inventory.executables.map (fun exe => ⟨.executable, exe.executable, #[exe.root]⟩)

/-- One completed producer history outcome, copied exactly: its module, path, source
snapshots before and after, and replacement edges. None is recorded as unsupported: the
operational history worker refuses a module with unsupported evaluators, so its outcome
is unavailable and refused. -/
def HistoryCopied (entry : Name × ProducerReport.HistoryOutcome) (observation : HistoryObservation) :
    Prop :=
  ∃ path before after replacements,
    entry.2 = .completed path before after replacements ∧
    observation = ⟨entry.1, ⟨path, before⟩, ⟨path, after⟩, replacements, #[]⟩

/-- Required history assembly: success exactly when every outcome completed, with one
exact copy per outcome, in order. An unavailable history is refused, never dropped. -/
def HistoriesContract
    (assemble : Array (Name × ProducerReport.HistoryOutcome) →
      Except String (Array HistoryObservation)) : Prop :=
  ∀ outcomes out, assemble outcomes = .ok out ↔
    out.size = outcomes.size ∧
    ∀ i (h : i < outcomes.size) (h' : i < out.size), HistoryCopied outcomes[i] out[i]

private def historyStep : Name × ProducerReport.HistoryOutcome → Except String HistoryObservation
  | (name, .unavailable detail) => .error s!"history unavailable for {name}: {detail}"
  | (name, .completed path before after replacements) =>
    .ok ⟨name, ⟨path, before⟩, ⟨path, after⟩, replacements, #[]⟩

private def historiesImpl (outcomes : Array (Name × ProducerReport.HistoryOutcome)) :
    Except String (Array HistoryObservation) :=
  List.toArray <$> outcomes.toList.mapM historyStep

private theorem historyStep_ok (entry : Name × ProducerReport.HistoryOutcome)
    (observation : HistoryObservation) :
    historyStep entry = .ok observation ↔ HistoryCopied entry observation := by
  obtain ⟨name, outcome⟩ := entry
  cases outcome with
  | unavailable detail => simp [historyStep, HistoryCopied]
  | completed path before after replacements =>
    simp only [historyStep, HistoryCopied, Except.ok.injEq]
    constructor
    · rintro rfl
      exact ⟨path, before, after, replacements, rfl, rfl⟩
    · rintro ⟨p, b, a, r, h, rfl⟩
      simp only [ProducerReport.HistoryOutcome.completed.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rfl

/-- Registers `HistoriesContract` about the executed history assembly. -/
theorem checked_histories : Regula.ExecutableContract historiesImpl HistoriesContract := by
  refine ⟨fun outcomes out => ?_⟩
  unfold historiesImpl
  constructor
  · intro h
    cases hm : outcomes.toList.mapM historyStep with
    | error e => simp [hm, Functor.map, Except.map] at h
    | ok copied =>
      simp only [hm, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      have ⟨hl, hi⟩ := (mapM_eq_ok _ _ _).mp hm
      refine ⟨by simpa using hl, fun i h h' => ?_⟩
      have step := hi i (by simpa using h) (by simpa using h')
      rw [Array.getElem_toList] at step
      exact (historyStep_ok _ _).mp (by simpa using step)
  · rintro ⟨hl, hi⟩
    have hm : outcomes.toList.mapM historyStep = .ok out.toList :=
      (mapM_eq_ok _ _ _).mpr ⟨by simpa using hl, fun i h h' =>
        by simpa using (historyStep_ok _ _).mpr (hi i (by simpa using h) (by simpa using h'))⟩
    simp [hm, Functor.map, Except.map]

/-- Preserve all completed histories, including their exact source binding. Unavailable
history cannot be turned into an empty successful observation. Through `checked_histories`. -/
def histories (outcomes : Array (Name × ProducerReport.HistoryOutcome)) :
    Except String (Array HistoryObservation) :=
  checked_histories.run outcomes

/-- Operational observations retained after the independent census has been frozen.
These data do not carry an accepted flag or determine the required stage list. -/
structure FrozenEnvironment where
  census : EnvironmentCensus
  roles : Roles census.policy
  admission : AdmissionObservation
  moduleDocumentation : Array (Name × Bool)
  declarationDocumentation : Array ((Name × Name) × Option String)
  histories : Array HistoryObservation

/-- Select the role receipt already computed during admission of this exact environment.
The dependent result prevents selecting a receipt for another inventory. -/
def frozenEnvironmentRoles (environments : Array FrozenEnvironment) :
    (slot : Fin (environments.map FrozenEnvironment.census).size) →
      Roles (environments.map FrozenEnvironment.census)[slot].policy :=
  fun slot => by
    simpa using (environments[slot.val]'(by simpa using slot.isLt)).roles

/-- Retaining admitted receipts is exactly the former recomputation at every slot. -/
theorem frozenEnvironmentRoles_eq (environments : Array FrozenEnvironment) :
    frozenEnvironmentRoles environments =
      (fun (slot : Fin (environments.map FrozenEnvironment.census).size) =>
        authorize (environments.map FrozenEnvironment.census)[slot].policy) := by
  funext slot
  exact Roles.eq_authorize _

/-- The complete project plan retains each environment's observations without merging
declaration namespaces, root registrations, replay or role authority. -/
structure Frozen (claim : Claim) where
  census : Census
  plan : Plan claim census
  roles : CensusRoles census
  environments : Array FrozenEnvironment

private def requireOne {α : Type u} (what : String) (values : Array α) : Except String α :=
  match values.toList with
  | [value] => .ok value
  | [] => .error s!"missing required {what} observation"
  | _ => .error s!"duplicate required {what} observation"

/-- Presence observations for modules have no docstring text payload. `some ""` encodes
observed presence only, exactly the existing `DocumentationPresenceOK` predicate. -/
def modulePresence (present : Bool) : Option String := if present then some "" else none

theorem modulePresence_iff (present : Bool) :
    DocumentationPresenceOK (modulePresence present) ↔ present = true := by
  cases present <;> simp [modulePresence, DocumentationPresenceOK]

/-- The documentation-presence rules RG5001–RG5003 are registered for exactly the evidence
modes whose required stages include documentation presence: their registry modes neither omit
a mode that checks presence nor advertise one that does not. -/
theorem documentationPresence_modes (id : Regula.RuleId)
    (h : id = .moduleDocumentation ∨ id = .materialDocumentation ∨ id = .materialIntent)
    (c : RegulaPolicy.Claim) :
    c.val.mode ∈ (Regula.descriptor id).evidenceModes ↔
      RegulaPolicy.Stage.documentationPresence ∈ RegulaPolicy.requiredStages c := by
  rcases h with rfl | rfl | rfl <;> cases hm : c.val.mode <;>
    simp [Regula.descriptor, Regula.projectModes, RegulaPolicy.requiredStages, hm]

/-- Each required slot receives its actual stage's observation. Failed lookup returns an
explicit error; unknown stages cannot become a completed empty payload. The caller supplies
the actual build process observation, not a synthesized success from diagnostic counts. -/
private def environmentEvidenceImpl (frozen : FrozenEnvironment) (stage : Stage)
    (subject : LocalJobSubject) : Except String JobEvidence := do
    match stage, subject with
      | .admission, .scope => pure <| .admission frozen.admission
      | .declarationPolicy, .declaration k => do
          let declaration ← requireOne "declaration" <| frozen.census.policy.declarations.filter
            (fun d => d.module == k.moduleKey.name.name && d.name == k.name.name)
          pure <| .declaration declaration
      | .execution, .root k => do
          let root ← requireOne "execution root" <| frozen.census.execution.roots.filter
            (fun r => r.module == k.moduleKey.name.name && r.name == k.name.name)
          pure <| .execution root
      | .transcript, .module k => do
          pure <| JobEvidence.transcript (← requireOne "transcript" <| frozen.census.policy.transcripts.filter
            (·.module == k.name.name))
      | .history, .module k => do
          pure <| JobEvidence.history (← requireOne "history" <| frozen.histories.filter (·.moduleName == k.name.name))
      | .origin, .module k => do
          let origins := frozen.census.execution.roots.flatMap fun r => r.boundaries.filterMap
            fun b => if b.module == k.name.name then b.account.nativeOrigin? else none
          let some origin := origins[0]? | throw "missing native-runtime origin observation"
          unless origins.all (fun other => decide (other = origin)) do throw "conflicting native-runtime origins"
          pure <| .origin origin
      | .documentationPresence, .module k => do
          let observation ← requireOne "module documentation" <|
            frozen.moduleDocumentation.filter (·.1 == k.name.name)
          pure <| .documentationPresence (modulePresence observation.2)
      | .documentationPresence, .declaration k => do
          let observation ← requireOne "declaration documentation" <|
            frozen.declarationDocumentation.filter (·.1 == (k.moduleKey.name.name, k.name.name))
          pure <| .documentationPresence observation.2
      | _, _ => throw "unsupported environment observation stage"

private theorem requireOne_ok {α : Type u} (what : String) (values : Array α) (value : α) :
    requireOne what values = .ok value ↔ values.toList = [value] := by
  unfold requireOne
  split <;> simp_all

private theorem filter_single {α : Type u} {p : α → Bool} {values : Array α} {value : α}
    (h : (values.filter p).toList = [value]) :
    value ∈ values ∧ p value = true ∧ ∀ other ∈ values, p other = true → other = value := by
  rw [Array.toList_filter] at h
  have hv : value ∈ values.toList.filter p := by rw [h]; simp
  rw [List.mem_filter] at hv
  refine ⟨Array.mem_def.mpr hv.1, hv.2, fun other ho hp => ?_⟩
  have : other ∈ values.toList.filter p := List.mem_filter.mpr ⟨Array.mem_def.mp ho, hp⟩
  rw [h] at this
  simpa using this

/-- Required documentation-presence evidence, as soundness: acceptance checks the supplied
docstring (presence for a module; for a registered declaration, a nonempty Intent section via
`MaterialDocumentationOK`), not which record supplied it, so this binding is not decided again
there. A success reports the presence of the only record with the job's module name, or
with its module and declaration names; a refusal fails closed. Every other stage's record is bound to its subject by
`LocalStageOK`. -/
def DocumentationEvidenceContract
    (evidence : FrozenEnvironment → Stage → LocalJobSubject → Except String JobEvidence) :
    Prop :=
  (∀ frozen k e, evidence frozen .documentationPresence (.module k) = .ok e →
    ∃ present, (k.name.name, present) ∈ frozen.moduleDocumentation ∧
      (∀ other ∈ frozen.moduleDocumentation, other.1 = k.name.name →
        other = (k.name.name, present)) ∧
      e = .documentationPresence (modulePresence present)) ∧
  (∀ frozen k e, evidence frozen .documentationPresence (.declaration k) = .ok e →
    ∃ doc, ((k.moduleKey.name.name, k.name.name), doc) ∈ frozen.declarationDocumentation ∧
      (∀ other ∈ frozen.declarationDocumentation,
        other.1 = (k.moduleKey.name.name, k.name.name) →
          other = ((k.moduleKey.name.name, k.name.name), doc)) ∧
      e = .documentationPresence doc)

/-- Registers `DocumentationEvidenceContract` about the executed evidence selection. -/
theorem checked_environmentEvidence :
    Regula.ExecutableContract environmentEvidenceImpl DocumentationEvidenceContract := by
  refine ⟨⟨fun frozen k e h => ?_, fun frozen k e h => ?_⟩⟩
  · simp only [environmentEvidenceImpl, bind, Except.bind] at h
    cases hr : requireOne "module documentation"
        (frozen.moduleDocumentation.filter (·.1 == k.name.name)) with
    | error _ => simp [hr] at h
    | ok observation =>
      simp only [hr, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨hmem, hp, huniq⟩ := filter_single ((requireOne_ok _ _ _).mp hr)
      have hname : observation = (k.name.name, observation.2) := by
        simp only [beq_iff_eq] at hp
        rw [← hp]
      refine ⟨observation.2, hname ▸ hmem, fun other ho h1 => ?_, h.symm⟩
      rw [huniq other ho (by simp [h1])]
      exact hname
  · simp only [environmentEvidenceImpl, bind, Except.bind] at h
    cases hr : requireOne "declaration documentation"
        (frozen.declarationDocumentation.filter (·.1 == (k.moduleKey.name.name, k.name.name))) with
    | error _ => simp [hr] at h
    | ok observation =>
      simp only [hr, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨hmem, hp, huniq⟩ := filter_single ((requireOne_ok _ _ _).mp hr)
      have hname : observation = ((k.moduleKey.name.name, k.name.name), observation.2) := by
        simp only [beq_iff_eq] at hp
        rw [← hp]
      refine ⟨observation.2, hname ▸ hmem, fun other ho h1 => ?_, h.symm⟩
      rw [huniq other ho (by simp [h1])]
      exact hname

/-- Required environment-job evidence: success exactly when exactly one frozen environment has
the job's environment key, with exactly that environment's `checked_environmentEvidence`
result for the job's stage and subject. -/
def EnvironmentJobContract
    (select : Array FrozenEnvironment → EnvironmentKey → Stage → LocalJobSubject →
      Except String JobEvidence) : Prop :=
  ∀ environments request stage subject evidence,
    select environments request stage subject = .ok evidence ↔
      ∃ environment,
        (environments.toList.filter fun value => decide (value.census.request.key = request)) =
          [environment] ∧
        checked_environmentEvidence.run environment stage subject = .ok evidence

private def environmentJobImpl (environments : Array FrozenEnvironment) (request : EnvironmentKey)
    (stage : Stage) (subject : LocalJobSubject) : Except String JobEvidence := do
  let environment ← requireOne "environment" <| environments.filter
    (fun value => decide (value.census.request.key = request))
  checked_environmentEvidence.run environment stage subject

/-- Registers `EnvironmentJobContract` about the executed environment lookup. -/
theorem checked_environmentJob :
    Regula.ExecutableContract environmentJobImpl EnvironmentJobContract := by
  refine ⟨fun environments request stage subject evidence => ?_⟩
  have exact := fun environment => (requireOne_ok "environment"
    (environments.filter fun value => decide (value.census.request.key = request)) environment)
  simp only [Array.toList_filter] at exact
  unfold environmentJobImpl
  cases hr : requireOne "environment"
      (environments.filter fun value => decide (value.census.request.key = request)) with
  | error e =>
    simp only [bind, Except.bind, reduceCtorEq, false_iff, not_exists, not_and]
    intro environment hf
    rw [(exact environment).mpr hf] at hr
    cases hr
  | ok environment =>
    simp only [bind, Except.bind]
    have selected := (exact environment).mp hr
    refine ⟨fun h => ⟨environment, selected, h⟩, ?_⟩
    rintro ⟨other, hf, h⟩
    rw [hf, List.cons.injEq] at selected
    rw [selected.1] at h
    exact h

/-- Global jobs are emitted once; local lookups select only the exact bound environment.
Duplicate metadata occurrences fail instead of being normalized into one response. -/
def observations {claim : Claim} (frozen : Frozen claim) (build : BuildObservation) :
    Except String (List (Nat × JobObservation)) := do
  let values : Array (Nat × JobObservation) ← frozen.plan.jobs.mapIdxM fun slot key => do
    let evidence ← match key.stage, key.subject with
      | .configuration, .scope =>
          pure (JobEvidence.configuration frozen.census.configuredTargets frozen.census.discoveredTargets)
      | .discovery, .scope => pure <| .discovery frozen.census
      | .build, .scope => pure <| .build build
      | stage, .environment request subject =>
          checked_environmentJob.run frozen.environments request stage subject
      | _, _ => throw "unsupported observation stage for project/file collector"
    return (slot, ({ key, snapshot := claim.val.snapshot, completion := .completed, evidence } : JobObservation))
  return values.toList

end Regula.Checker.Acceptance
