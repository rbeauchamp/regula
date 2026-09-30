import RegulaPolicy.Claim
import RegulaPolicy.Decision
import RegulaPolicy.Execution

/-! # Census and required-job plan

A frozen data census and a concrete required-job relation. The required jobs are
computed before result admission from the claim and census, never from returned successes.
The IO adapter is responsible for faithfully obtaining configuration, Lake and source data. -/
namespace RegulaPolicy
open Lean (Name)

/-- The kind of a Lake target of the root package. -/
inductive TargetKind where
  /-- A `lean_lib` target. -/
  | library
  /-- A `lean_exe` target. -/
  | executable
  deriving Repr, DecidableEq

/-- Actual Lake target observation, retaining its semantic module array. -/
structure DiscoveredTarget where
  /-- Whether the target is a library or an executable. -/
  kind : TargetKind
  /-- The target's Lake name. -/
  name : String
  /-- The target's modules as Lake resolves them; an executable's root module alone. -/
  modules : Array Name
  deriving Repr, DecidableEq

/-- Parsed target classification: none excludes, some names the owning positive surface. -/
structure TargetAssignment where
  /-- Whether the classified target is a library or an executable. -/
  kind : TargetKind
  /-- The classified target's Lake name. -/
  name : String
  /-- The claimed surface that owns the target, or `none` when the manifest excludes it. -/
  surface : Option String
  deriving Repr, DecidableEq

/-- These implementation imports remain forbidden through ordinary dependencies. -/
def reporterOnlyModuleNames : Array Name :=
  #[`Regula.Probe, `Regula.Report, `Regula.Checker.PolicyCodec]

/-- The published checker interfaces a claimed module may import by design (standard §7.10):
the executable-contract type and the material-claim registration attribute. The probe
force-loads both, so they are authenticated like the reporter and are never owned. -/
def publishedInterfaceModuleNames : Array Name :=
  #[`Regula.Contract, `Regula.MaterialClaim]

/-- Exact reporter identities used only to select authentication obligations. Membership
alone never grants an exemption. -/
def reporterModuleNames : Array Name :=
  reporterOnlyModuleNames ++ publishedInterfaceModuleNames

/-- A published interface is never a reporter-only module, so admitting it as a claimed
import leaves every reporter-only import restriction unchanged. -/
theorem publishedInterface_not_reporterOnly :
    ∀ n ∈ publishedInterfaceModuleNames, n ∉ reporterOnlyModuleNames := by decide +kernel

/-- Only the existing force-loaded reporter, public name codec and conditional collector
can enter the infrastructure partition. This is not a whole-library exemption. -/
def infrastructureModuleNames : Array Name :=
  reporterModuleNames ++ #[`Regula.StructuralName, `Regula.Collect]

/-- Canonical-artifact equality for one exact infrastructure module and snapshot. The
adapter obtains both paths independently from actual resolution and the checker library;
this type proves equality of those observations, not filesystem or compiler authenticity. -/
structure InfrastructureOrigin where
  /-- The infrastructure module this receipt is for. -/
  moduleKey : ModuleKey
  /-- The canonical path of the `.olean` the probed environment loaded the module from. -/
  actual : String
  /-- The canonical path of the module's `.olean` in the checker package's own library. -/
  expected : String
  /-- Proof that the module is one of `infrastructureModuleNames`. -/
  eligible : moduleKey.name.name ∈ infrastructureModuleNames
  /-- Proof that the observed path is nonempty. -/
  nonempty : actual ≠ ""
  /-- Proof that the observed and expected paths are equal. -/
  agrees : actual = expected
  deriving DecidableEq

/-- Refuse unsupported identities, absent origins and mismatched canonical artifacts. -/
def admitInfrastructureOrigin (key : ModuleKey) (actual expected : String) :
    Except String InfrastructureOrigin :=
  if hn : key.name.name ∈ infrastructureModuleNames then
    if hp : actual ≠ "" then
      if he : actual = expected then .ok ⟨key, actual, expected, hn, hp, he⟩
      else .error "infrastructure artifact origin mismatch"
    else .error "empty infrastructure artifact origin"
  else .error "unsupported infrastructure module"

/-- Every authenticated candidate is retained unchanged; no arbitrary fallback module
or artifact is substituted. Incoming-import checks remain a whole-census obligation. -/
theorem admitInfrastructureOrigin_exact (origin : InfrastructureOrigin) :
    admitInfrastructureOrigin origin.moduleKey origin.actual origin.expected = .ok origin := by
  unfold admitInfrastructureOrigin
  rw [dite_eq_left origin.eligible, dite_eq_left origin.nonempty, dite_eq_left origin.agrees]

/-- A standalone file is compiled in an isolated module. Retain both identities and
exact byte equality; this does not authenticate either filesystem read. -/
structure FileSourceBinding where
  /-- The snapshot of the file the audit was asked to check. -/
  requested : SourceSnapshot
  /-- The snapshot of the isolated copy that was compiled. -/
  compiled : SourceSnapshot
  /-- Proof that both snapshots hold the same source text. -/
  sameBytes : requested.source = compiled.source
  deriving DecidableEq

/-- Bind the requested file to its compiled copy when their source texts are equal, and
refuse otherwise. -/
def admitFileSourceBinding (requested compiled : SourceSnapshot) :
    Except String FileSourceBinding :=
  if h : requested.source = compiled.source then .ok ⟨requested, compiled, h⟩
  else .error "standalone source copy differs from requested file"

theorem fileSourceBinding_bytes (binding : FileSourceBinding) :
    binding.requested.source = binding.compiled.source := binding.sameBytes

/-- Frozen observations and independently collected keys. No field records policy success.
Material declarations are the explicit public evidence-registration census; its adequacy
remains semantic review. Imported modules are separate from claimed owned modules. -/
structure EnvironmentCensus where
  /-- The request this environment answers: its key and positive module assignment. -/
  request : EnvironmentRequest
  /-- The admitted declaration inventory of the environment's owned modules. -/
  policy : Inventory
  /-- The admitted execution roots and their closure accounts. -/
  execution : ExecutionInventory
  /-- The positive (owned) modules the request assigns to this environment. -/
  modules : Array ModuleKey
  /-- Loaded modules that are neither owned nor infrastructure: the import closure. -/
  importedModules : Array ModuleKey
  /-- Origin receipts of the loaded checker infrastructure modules. -/
  infrastructure : Array InfrastructureOrigin := #[]
  /-- The name, `.olean` path and direct imports of every loaded module. -/
  origins : Array ModuleOrigin := #[]
  /-- Captured source snapshots of infrastructure modules, where a source was captured. -/
  infrastructureSources : Array (ModuleKey × SourceSnapshot) := #[]
  /-- The captured source snapshot of each owned module, in `modules` order. -/
  moduleSources : Array (ModuleKey × SourceSnapshot)
  /-- For a single-file audit, the binding of the requested file to its compiled copy. -/
  fileSource : Option FileSourceBinding := none
  /-- Captured source snapshots of imported modules, where a source was captured. -/
  importedSources : Array (ModuleKey × SourceSnapshot)
  /-- Loaded modules built into the project's own output that no Lake target configures and
  that are neither owned nor infrastructure; `EnvironmentCensusOK` requires none. -/
  unclassifiedRootImports : Array ModuleKey
  /-- The modules whose declarations the kernel-admission replay covered. -/
  admissionModules : Array ModuleKey := #[]
  /-- The declarations the replay had to admit: every owned one that is neither `unsafe` nor
  `partial`. -/
  admissionDeclarations : Array DeclarationKey
  /-- The keys of the policy inventory's declarations, in inventory order. -/
  declarations : Array DeclarationKey
  /-- The keys of the admitted execution roots, in root order. -/
  roots : Array RootKey
  /-- The declarations registered as material evidence (`@[regula_material]`). -/
  materialDeclarations : Array DeclarationKey
  deriving DecidableEq

/-- The module keys of the environment's infrastructure receipts. -/
def EnvironmentCensus.infrastructureModules (i : EnvironmentCensus) : Array ModuleKey :=
    i.infrastructure.map (·.moduleKey)

/-- Every module of the environment: owned, then imported, then infrastructure. -/
def EnvironmentCensus.allModules (i : EnvironmentCensus) : Array ModuleKey :=
  i.modules ++ i.importedModules ++ i.infrastructureModules

/-- Every captured source of the environment: owned, then imported, then infrastructure. -/
def EnvironmentCensus.allModuleSources (i : EnvironmentCensus) : Array
    (ModuleKey × SourceSnapshot) :=
  i.moduleSources ++ i.importedSources ++ i.infrastructureSources

/-- One complete original request with separately admitted Lean environments. -/
structure Census where
  /-- The environment requests of the run, in coordinator order. -/
  requests : Array EnvironmentRequest
  /-- One environment census per request, in the same order. -/
  environments : Array EnvironmentCensus
  /-- Every positive (owned) module of the run, over all environments. -/
  modules : Array ModuleKey
  /-- The captured source of every positive module, over all environments. -/
  moduleSources : Array (ModuleKey × SourceSnapshot)
  /-- The manifest's classification of each Lake target. -/
  configuredTargets : Array TargetAssignment
  /-- The Lake targets of the root package as Lake resolves them. -/
  discoveredTargets : Array DiscoveredTarget
  /-- The documentation fences a documentation audit checks. -/
  fences : Array FenceKey := #[]
  /-- In the serialized-graph mode, the root modules the serialized-graph checker runs on. -/
  graphRoots : Array ModuleKey := #[]
  /-- In the serialized-graph mode, the positive modules each graph root's check covers. -/
  graphCoverage : Array (ModuleKey × Array ModuleKey) := #[]
  deriving DecidableEq

/-- Every module of every environment of the census. -/
def Census.allModules (i : Census) : Array ModuleKey := i.environments.flatMap (·.allModules)

/-- A generated-role receipt (`Roles`) for the policy inventory of every environment. -/
abbrev CensusRoles (i : Census) := (slot : Fin i.environments.size) →
    Roles i.environments[slot].policy

/-- The claim's source snapshots: its own sources, then every dependency's files. -/
def snapshotSources (c : Claim) : Array SourceSnapshot :=
  c.val.snapshot.sources ++ c.val.snapshot.dependencies.flatMap (·.files)

/-- The Lean module names of the keys, in order. -/
def moduleNames (ms : Array ModuleKey) : Array Name := ms.map (·.name.name)

/-- The (module, declaration) name pairs of the keys, in order. -/
def declarationNames (ds : Array DeclarationKey) : Array (Name × Name) :=
  ds.map (fun d => (d.moduleKey.name.name, d.name.name))

/-- The complete loaded import census binds every infrastructure receipt. Direct import
edges are inspected for every loaded module, including ordinary dependencies. Collect
is infrastructure only in its existing force-only case. Positive ownership is disjoint. -/
def InfrastructureOK (c : Claim) (i : EnvironmentCensus) : Prop :=
  (∀ m ∈ i.infrastructureModules, m ∉ i.modules ∧ m ∉ i.importedModules ∧
    m.snapshot.val = c.val.snapshot) ∧
  UniqueNames (i.origins.map (·.name)) ∧
  canonicalNames (i.origins.map (·.name)) = canonicalNames (moduleNames i.allModules) ∧
  (∀ receipt ∈ i.infrastructure, ∃ origin ∈ i.origins,
    origin.name = receipt.moduleKey.name.name ∧ origin.olean = receipt.actual) ∧
  (∀ origin ∈ i.origins, ∀ imported ∈ origin.imports,
    imported ∈ reporterOnlyModuleNames → origin.name ∈ reporterModuleNames ∧
      ∃ receipt ∈ i.infrastructure, receipt.moduleKey.name.name = origin.name) ∧
  (∀ receipt ∈ i.infrastructure, receipt.moduleKey.name.name = `Regula.Collect →
    ∀ origin ∈ i.origins, `Regula.Collect ∈ origin.imports → origin.name ∈ reporterModuleNames) ∧
  i.infrastructureSources.toList.Pairwise (fun a b => a.1 ≠ b.1) ∧
  (∀ entry ∈ i.infrastructureSources,
    entry.1 ∈ i.infrastructureModules ∧ entry.2 ∈ snapshotSources c)
set_option synthInstance.maxSize 1024 in
instance (c : Claim) (i : EnvironmentCensus) : Decidable (InfrastructureOK c i) := by
  unfold InfrastructureOK; infer_instance

/-- The admitted partition never supplies positive ownership or an ordinary import. -/
theorem infrastructure_disjoint (c : Claim) (i : EnvironmentCensus) (h : InfrastructureOK c i)
    (m : ModuleKey) (hm : m ∈ i.infrastructureModules) : m ∉ i.modules ∧ m ∉ i.importedModules :=
  ⟨(h.1 m hm).1, (h.1 m hm).2.1⟩

/-- An executable's root module lies in a library only when the manifest classifies the two
alike: the executable is claimed with that library's surface, or both are excluded. A claimed
root inside a claimed library therefore keeps that library's claim, and no root is claimed with
one surface while a library containing it is excluded or claimed with another, or excluded while
such a library is claimed. -/
def RootsClassifiedAlike (configured : Array TargetAssignment)
    (discovered : Array DiscoveredTarget) : Prop :=
  ∀ a ∈ configured, a.kind = .executable →
    ∀ t ∈ discovered, t.kind = .executable → t.name = a.name →
      ∀ n ∈ t.modules, ∀ lib ∈ discovered, lib.kind = .library → n ∈ lib.modules →
        ∀ l ∈ configured, l.kind = .library → l.name = lib.name → l.surface = a.surface
set_option synthInstance.maxSize 1024 in
instance (configured : Array TargetAssignment) (discovered : Array DiscoveredTarget) :
    Decidable (RootsClassifiedAlike configured discovered) := by
  unfold RootsClassifiedAlike; infer_instance

/-- Exact target partition, including excluded targets and executable roots classified alike
with every library containing them (`RootsClassifiedAlike`). Each positive surface owns its
library's modules and its claimed executables' root modules, a root inside the library once. -/
def TargetPartitionOK (c : Claim) (i : Census) : Prop :=
  i.configuredTargets.toList.Pairwise (fun a b => (a.kind, a.name) ≠ (b.kind, b.name)) ∧
  i.discoveredTargets.toList.Pairwise (fun a b => (a.kind, a.name) ≠ (b.kind, b.name)) ∧
  (∀ a ∈ i.configuredTargets, ∃ t ∈ i.discoveredTargets, a.kind = t.kind ∧ a.name = t.name) ∧
  (∀ t ∈ i.discoveredTargets, t.name ≠ "" ∧ t.modules ≠ #[] ∧
    (t.kind = .executable → t.modules.size = 1) ∧
    ∃ a ∈ i.configuredTargets, a.kind = t.kind ∧ a.name = t.name) ∧
  (∀ a ∈ i.configuredTargets, ∀ owner ∈ a.surface, ∃ s ∈ c.val.surfaces, s.target = owner) ∧
  (∀ s ∈ c.val.surfaces,
    (∃ a ∈ i.configuredTargets, a.kind = .library ∧ a.name = s.target ∧ a.surface = some s.target) ∧
    canonicalNames (s.modules.map (·.name)) = canonicalNames
      ((i.discoveredTargets.filter (fun t => i.configuredTargets.any (fun a =>
        a.kind == t.kind && a.name == t.name && a.surface == some s.target))).flatMap (·.modules)))
            ∧
  (∀ a ∈ i.configuredTargets, a.kind = .library → ∀ owner ∈ a.surface, a.name = owner) ∧
  RootsClassifiedAlike i.configuredTargets i.discoveredTargets
set_option synthInstance.maxSize 1024 in
instance (c : Claim) (i : Census) : Decidable (TargetPartitionOK c i) := by
  unfold TargetPartitionOK; infer_instance

/-- Optional graph selection and import coverage are frozen before checker processes.
The relation proves exact accounting of supplied coverage, not Lean import extraction. -/
def GraphPlanOK (c : Claim) (i : Census) : Prop :=
  if c.val.mode = .serializedGraph then
    i.graphRoots ≠ #[] ∧ i.graphRoots.toList.Pairwise (· ≠ ·) ∧
    i.graphCoverage.map (·.1) = i.graphRoots ∧
    (∀ root ∈ i.graphRoots, root ∈ i.modules) ∧
    (∀ entry ∈ i.graphCoverage, entry.1 ∈ entry.2 ∧ ∀ m ∈ entry.2, m ∈ i.modules) ∧
    ∀ m ∈ i.modules, ∃ entry ∈ i.graphCoverage, m ∈ entry.2
  else i.graphRoots = #[] ∧ i.graphCoverage = #[]
instance (c : Claim) (i : Census) : Decidable (GraphPlanOK c i) := by
  unfold GraphPlanOK; infer_instance

/-- Bucket keys by their names only. Hits and collisions are resolved by full structural
equality, including the admitted snapshot, so membership still compares every field. -/
instance : Hashable ModuleKey := ⟨fun k => hash k.name.name⟩
instance : LawfulHashable ModuleKey where
  hash_eq _ _ h := eq_of_beq h ▸ rfl
instance : Hashable DeclarationKey :=
    ⟨fun k => mixHash (hash k.moduleKey.name.name) (hash k.name.name)⟩
instance : LawfulHashable DeclarationKey where
  hash_eq _ _ h := eq_of_beq h ▸ rfl

/-- Exact admitted key/data reconciliation and claim bindings. These checks cannot establish
that the external environment traversal or source scan omitted nothing; that is the collector
boundary. They do prevent a returned policy table from defining its own required census. -/
def EnvironmentCensusOK (c : Claim) (global : Census) (i : EnvironmentCensus) : Prop :=
  i.request.modules = i.modules ∧ i.request.key.snapshot.val = c.val.snapshot ∧
  InfrastructureOK c i ∧
  UniqueNames (moduleNames i.allModules) ∧
  (∀ m ∈ i.allModules, m.snapshot.val = c.val.snapshot) ∧
  i.moduleSources.map (·.1) = i.modules ∧
  (∀ entry ∈ i.moduleSources, entry.2 ∈ c.val.snapshot.sources) ∧
  i.importedSources.toList.Pairwise (fun a b => a.1 ≠ b.1) ∧
  (∀ entry ∈ i.importedSources, entry.1 ∈ i.importedModules ∧ entry.2 ∈ snapshotSources c) ∧
  i.unclassifiedRootImports = #[] ∧
  (∀ m ∈ i.importedModules, ∀ target ∈ global.discoveredTargets, m.name.name ∈ target.modules →
    ∃ assignment ∈ global.configuredTargets, assignment.kind = target.kind ∧
      assignment.name = target.name ∧ assignment.surface.isSome = true) ∧
  UniqueNames (moduleNames i.admissionModules) ∧
  (∀ m ∈ i.admissionModules, m.snapshot.val = c.val.snapshot) ∧
  (∀ d ∈ i.admissionDeclarations, d.moduleKey ∈ i.allModules ∧ d.moduleKey ∈ i.admissionModules) ∧
  i.admissionDeclarations.toList.Pairwise (· ≠ ·) ∧
  (∀ d ∈ i.policy.declarations, d.isUnsafe = false → d.isPartial = false →
    (d.module, d.name) ∈ declarationNames i.admissionDeclarations) ∧
  declarationNames i.declarations = i.policy.declarations.map (fun d => (d.module, d.name)) ∧
  declarationNames i.roots = i.execution.roots.map (fun r => (r.module, r.name)) ∧
  (∀ d ∈ i.declarations, d.moduleKey ∈ i.modules) ∧
  (∀ r ∈ i.roots, r.moduleKey ∈ i.allModules) ∧
  (∀ d ∈ i.materialDeclarations, d ∈ i.declarations) ∧
  i.materialDeclarations.toList.Pairwise (· ≠ ·) ∧
  (∀ r ∈ i.execution.roots, ∀ b ∈ r.boundaries, b.module ∈ moduleNames i.allModules) ∧
  (match c.val.scope with
   | .project => True
   | .file source .. => i.modules.size = 1 ∧
       ∃ binding ∈ i.fileSource, binding.requested = source ∧ i.moduleSources.map (·.2) =
           #[binding.compiled]
   | .editor n source .. => moduleNames i.modules = #[n.name] ∧
       i.moduleSources.map (·.2) = #[source]
   | .documentation _ => False)
set_option synthInstance.maxSize 1024 in
instance (c : Claim) (global : Census) (i : EnvironmentCensus) : Decidable
    (EnvironmentCensusOK c global i) := by
  unfold EnvironmentCensusOK
  -- Index each repeatedly queried array once; membership and distinctness equivalences
  -- supply decisions for the unchanged predicate, without a second validity definition.
  let allModules := Std.ExtHashSet.ofList i.allModules.toList
  let admissionModules := Std.ExtHashSet.ofList i.admissionModules.toList
  let modules := Std.ExtHashSet.ofList i.modules.toList
  let declarations := Std.ExtHashSet.ofList i.declarations.toList
  let allNames := Std.ExtHashSet.ofList (moduleNames i.allModules).toList
  let admissionNames := Std.ExtHashSet.ofList (declarationNames i.admissionDeclarations).toList
  letI (m : ModuleKey) : Decidable (m ∈ i.allModules) :=
    decidable_of_iff (m ∈ allModules) (by simp [allModules, Std.ExtHashSet.mem_ofList])
  letI (m : ModuleKey) : Decidable (m ∈ i.admissionModules) :=
    decidable_of_iff (m ∈ admissionModules) (by simp [admissionModules, Std.ExtHashSet.mem_ofList])
  letI (m : ModuleKey) : Decidable (m ∈ i.modules) :=
    decidable_of_iff (m ∈ modules) (by simp [modules, Std.ExtHashSet.mem_ofList])
  letI (d : DeclarationKey) : Decidable (d ∈ i.declarations) :=
    decidable_of_iff (d ∈ declarations) (by simp [declarations, Std.ExtHashSet.mem_ofList])
  letI (n : Name) : Decidable (n ∈ moduleNames i.allModules) :=
    decidable_of_iff (n ∈ allNames) (by simp [allNames, Std.ExtHashSet.mem_ofList])
  letI (k : Name × Name) : Decidable (k ∈ declarationNames i.admissionDeclarations) :=
    decidable_of_iff (k ∈ admissionNames) (by simp [admissionNames, Std.ExtHashSet.mem_ofList])
  letI : Decidable (i.admissionDeclarations.toList.Pairwise (· ≠ ·)) := distinctDecidable _
  letI : Decidable (i.materialDeclarations.toList.Pairwise (· ≠ ·)) := distinctDecidable _
  cases c.val.scope <;> infer_instance

set_option synthInstance.maxSize 1024 in
/-- The indexed implementation decides the same proposition as the prior finite scan. -/
theorem environmentCensusOK_decide_eq_previous (c : Claim) (global : Census)
    (i : EnvironmentCensus) :
    decide (EnvironmentCensusOK c global i) = @decide (EnvironmentCensusOK c global i)
      (by unfold EnvironmentCensusOK; cases c.val.scope <;> infer_instance) := by
  congr

/-- Exact request occurrences and positive partition precede admission of any results.
Environment position is identity; no producer may select or deduplicate this domain. -/
def CensusOK (c : Claim) (i : Census) : Prop :=
  i.environments.map (·.request) = i.requests ∧
  (∀ n : Fin i.requests.size, i.requests[n].key.index = n.val) ∧
  (∀ e ∈ i.environments, EnvironmentCensusOK c i e) ∧
  i.modules = i.environments.flatMap (·.modules) ∧
  UniqueNames (moduleNames i.modules) ∧
  i.moduleSources = i.environments.flatMap (·.moduleSources) ∧
  GraphPlanOK c i ∧
  i.fences.toList.Pairwise (· ≠ ·) ∧
  (∀ f ∈ i.fences, f.document ∈ c.val.snapshot.sources) ∧
  (match c.val.scope with
   | .project => TargetPartitionOK c i ∧
       canonicalNames (moduleNames i.modules) = canonicalNames
         (c.val.surfaces.flatMap (fun s => s.modules.map (·.name))) ∧ i.fences = #[] ∧
       (if c.val.mode = .serializedGraph then i.requests.size = 1 else
         i.requests.map (fun r => moduleNames r.modules) =
           c.val.surfaces.flatMap (·.environmentNames))
   | .file .. | .editor .. => i.requests.size = 1 ∧ i.fences = #[]
   | .documentation docs => i.requests = #[] ∧ ∀ f ∈ i.fences, f.document ∈ docs)
set_option synthInstance.maxSize 1024 in
instance (c : Claim) (i : Census) : Decidable (CensusOK c i) := by
  unfold CensusOK
  cases c.val.scope <;> infer_instance

/-- Admission preserves the exact ordered request occurrences, without normalization. -/
theorem census_exact_requests (c : Claim) (i : Census) (h : CensusOK c i) :
    i.environments.map (·.request) = i.requests := h.1

/-- The complete original positive module domain is partitioned across environments. -/
theorem census_exact_modules (c : Claim) (i : Census) (h : CensusOK c i) :
    i.modules = i.environments.flatMap (·.modules) ∧ UniqueNames (moduleNames i.modules) :=
  ⟨h.2.2.2.1, h.2.2.2.2.1⟩

theorem census_request_index (c : Claim) (i : Census) (h : CensusOK c i)
    (slot : Fin i.requests.size) : i.requests[slot].key.index = slot.val := h.2.1 slot

theorem census_environment_index (c : Claim) (i : Census) (h : CensusOK c i)
    (slot : Fin i.environments.size) : i.environments[slot].request.key.index = slot.val := by
  have bound : slot.val < i.requests.size := by simp [← h.1]
  have position := h.2.1 ⟨slot.val, bound⟩
  simpa [← h.1] using position

/-- Two distinct response occurrences cannot be normalized into one request identity. -/
theorem census_environment_unique (c : Claim) (i : Census) (h : CensusOK c i)
    (left right : Fin i.environments.size)
    (same : i.environments[left].request.key = i.environments[right].request.key) : left =
        right := by
  apply Fin.ext
  rw [← census_environment_index c i h left, ← census_environment_index c i h right]
  exact congrArg (·.index) same

/-- Each requested occurrence has its unchanged environment data and local obligations. -/
theorem census_requested_environment (c : Claim) (i : Census) (h : CensusOK c i)
    (request : EnvironmentRequest) (hr : request ∈ i.requests) :
    ∃ e ∈ i.environments, e.request = request ∧ EnvironmentCensusOK c i e := by
  rw [← h.1] at hr
  obtain ⟨e, he, eq⟩ := Array.mem_map.mp hr
  exact ⟨e, he, eq, h.2.2.1 e he⟩

/-- Ordinary project requests are the claim's surface environments, in order: each surface's
library, then each of its executable roots alone (`SurfaceAssignment.environments`). -/
theorem census_project_partition (c : Claim) (i : Census) (h : CensusOK c i)
    (scope : c.val.scope = .project) (mode : c.val.mode ≠ .serializedGraph) :
    i.requests.map (fun r => moduleNames r.modules) =
      c.val.surfaces.flatMap (·.environmentNames) := by
  have hs := h.2.2.2.2.2.2.2.2.2
  rw [scope] at hs
  simpa [mode] using hs.2.2.2

/-- In an ordinary project census, every claimed executable's root module is requested in an
environment whose only positive module it is, so no other executable root or library module is
assigned beside it. -/
theorem census_executable_alone (c : Claim) (i : Census) (h : CensusOK c i)
    (scope : c.val.scope = .project) (mode : c.val.mode ≠ .serializedGraph)
    (s : SurfaceAssignment) (hs : s ∈ c.val.surfaces) (root : Identity)
    (hr : root ∈ s.executables) :
    ∃ r ∈ i.requests, moduleNames r.modules = #[root.name] := by
  have hin : #[root.name] ∈ c.val.surfaces.flatMap (·.environmentNames) := by
    refine Array.mem_flatMap.mpr ⟨s, hs, Array.mem_map.mpr ⟨#[root], ?_, by simp⟩⟩
    exact (s.mem_environments _).mpr (.inr ⟨root, hr, rfl⟩)
  rw [← census_project_partition c i h scope mode] at hin
  obtain ⟨r, hr', eq⟩ := Array.mem_map.mp hin
  exact ⟨r, hr', eq⟩

/-- No module of a claimed Lake target escapes a valid project census: every module of a
discovered library or executable that the manifest assigns to a surface is a positive module of
one of the census's environments, by `TargetPartitionOK`'s surface-module equality and
`CensusOK`'s module partition. This includes an executable root inside its surface's library. -/
theorem census_covers_claimed_targets (c : Claim) (i : Census) (h : CensusOK c i)
    (scope : c.val.scope = .project) (t : DiscoveredTarget) (ht : t ∈ i.discoveredTargets)
    (a : TargetAssignment) (ha : a ∈ i.configuredTargets) (kind : a.kind = t.kind)
    (name : a.name = t.name) (claimed : a.surface.isSome = true) :
    ∀ m ∈ t.modules, m ∈ moduleNames i.modules := by
  have hs := h.2.2.2.2.2.2.2.2.2
  rw [scope] at hs
  obtain ⟨tp, hmodules, -, -⟩ := hs
  obtain ⟨owner, hown⟩ := Option.isSome_iff_exists.mp claimed
  obtain ⟨s, hs, htarget⟩ := tp.2.2.2.2.1 a ha owner hown
  intro m hm
  have hsurface : m ∈ s.modules.map (·.name) := by
    rw [← mem_canonicalNames, (tp.2.2.2.2.2.1 s hs).2, mem_canonicalNames]
    refine Array.mem_flatMap.mpr ⟨t, Array.mem_filter.mpr ⟨ht, ?_⟩, hm⟩
    exact Array.any_eq_true'.mpr ⟨a, ha, by simp [kind, name, hown, htarget]⟩
  rw [← mem_canonicalNames, hmodules, mem_canonicalNames]
  exact Array.mem_flatMap.mpr ⟨s, hs, hsurface⟩

/-- A module's profile is derived from its positive assignment, never a result payload. -/
def profileForModule (c : Claim) (m : Name) : Option ConformingProfile :=
  match c.val.scope with
  | .project => (c.val.surfaces.find? (fun s => s.modules.any (fun n => n.name == m))).map
                 (·.profile)
  | .file _ p _ | .editor _ _ p _ => some p
  | .documentation _ => some .standardLogical

/-- A module's execution claim, derived from the claim: in a project, that of the surface
owning the module (none when no surface does); in a file or editor audit, the requested one;
none for documentation. -/
def executionForModule (c : Claim) (m : Name) : Option ExecutionClaim :=
  match c.val.scope with
  | .project => (c.val.surfaces.find? (fun s => s.modules.any (fun n => n.name == m))).map
                 (·.execution)
  | .file _ _ e | .editor _ _ _ e => some e
  | .documentation _ => none

/-- A shared root must meet each requesting surface's execution obligation. The requests
come from the owned ordinary declaration or each retained executable-contract registration. -/
def rootRequests (c : Claim) (i : EnvironmentCensus) (root : Name) : Array ExecutionClaim :=
  (i.policy.declarations.filter (fun d => d.name == root ||
    d.executableContract.any (fun contract => contract.root == root))).filterMap
      (fun d => executionForModule c d.module)

/-- Jobs use the existing stage/subject vocabulary; this pair is a projection of JobKey,
not a second identity scheme. Fixed array order supplies deterministic result slots. -/
def localStageSubjects (i : EnvironmentCensus) : Stage → Array LocalJobSubject
  | .admission => #[.scope]
  | .declarationPolicy => i.declarations.map .declaration
  | .execution => i.roots.map .root
  | .transcript => (i.modules.filter (fun m => i.policy.declarations.any (fun d =>
      d.module == m.name.name && declarationNeedsTranscript d.kind d.name))).map .module
  | .history => (i.allModules.filter (fun m => i.execution.roots.any (fun r => r.boundaries.any
      (fun b => b.module == m.name.name && b.boundary == .runtimeReplacement)))).map .module
  | .origin => (i.allModules.filter (fun m => i.execution.roots.any (fun r => r.boundaries.any
      (fun b => b.module == m.name.name && b.boundary == .nativeRuntime)))).map .module
  | .documentationPresence => i.modules.map .module ++ i.materialDeclarations.map .declaration
  | _ => #[]

/-- The subjects of a stage's jobs over the whole census: the scope for a whole-run stage, each
fence for `example`, and otherwise every environment's local subjects under its request key. -/
def stageSubjects (i : Census) : Stage → Array JobSubject
  | .configuration | .discovery | .build | .documentScan | .graph => #[.scope]
  | .example => i.fences.map .fence
  | stage => i.environments.flatMap fun e =>
      (localStageSubjects e stage).map (JobSubject.environment e.request.key)

/-- Required jobs are derived from mandatory mode stages and census subjects before results. -/
def requiredJobs (c : Claim) (i : Census) : Array (Stage × JobSubject) :=
  (requiredStages c).toArray.flatMap (fun stage => (stageSubjects i stage).map (stage, ·))

/-- Every local derived job of every requested environment remains in the whole plan. -/
theorem stageSubjects_environment (i : Census) (e : EnvironmentCensus) (he : e ∈ i.environments)
    (stage : Stage) (subject : LocalJobSubject) (hs : subject ∈ localStageSubjects e stage) :
    JobSubject.environment e.request.key subject ∈ stageSubjects i stage := by
  cases stage <;> first
    | solve | simp [localStageSubjects] at hs
    | (simp only [stageSubjects, Array.mem_flatMap, Array.mem_map]
       exact ⟨e, he, subject, hs, rfl⟩)

theorem requiredJobs_environment_coverage (c : Claim) (i : Census) (h : CensusOK c i)
    (request : EnvironmentRequest) (hr : request ∈ i.requests)
    (stage : Stage) (hs : stage ∈ requiredStages c) :
    ∃ e ∈ i.environments, e.request = request ∧
      ∀ subject ∈ localStageSubjects e stage,
        (stage, JobSubject.environment request.key subject) ∈ requiredJobs c i := by
  obtain ⟨e, he, eq, _⟩ := census_requested_environment c i h request hr
  refine ⟨e, he, eq, ?_⟩
  intro subject hsubject
  have hin := stageSubjects_environment i e he stage subject hsubject
  rw [eq] at hin
  simp only [requiredJobs, Array.mem_flatMap, List.mem_toArray, Array.mem_map]
  exact ⟨stage, hs, JobSubject.environment request.key subject, hin, rfl⟩

/-- Bucket selection only: collisions are resolved by full structural stage/subject
equality, including snapshots, source bytes and every constructor field. Omitting these
fields from the hash does not omit them from the original uniqueness relation. -/
private def localJobSubjectBucket : LocalJobSubject → UInt64
  | .scope => 0
  | .module k => hash k.name.name
  | .declaration k | .root k => hash (k.moduleKey.name.name, k.name.name)
  | .boundary k => hash (k.root.name.name, k.occurrence)

private def jobSubjectBucket : JobSubject → UInt64
  | .scope => 0
  | .environment key subject => mixHash (hash key.index) (localJobSubjectBucket subject)
  | .fence k => hash (k.document.uri, k.body.start)

local instance : BEq (Stage × JobSubject) := ⟨fun a b => decide (a = b)⟩
local instance : LawfulBEq (Stage × JobSubject) where
  eq_of_beq h := of_decide_eq_true h
  rfl {a} := by change decide (a = a) = true; exact decide_eq_true rfl
local instance : Hashable (Stage × JobSubject) := ⟨fun key => jobSubjectBucket key.2⟩
local instance : LawfulHashable (Stage × JobSubject) where
  hash_eq _ _ h := eq_of_beq h ▸ rfl

/-- The index decides the exact stage/subject relation required by PlanOK, not full
JobKey uniqueness (which would be weaker when claims differ). Ordered jobs are untouched. -/
theorem requiredJobs_distinct_iff (c : Claim) (i : Census) :
    (Std.ExtHashSet.ofList (requiredJobs c i).toList).size = (requiredJobs c i).toList.length ↔
      (requiredJobs c i).toList.Pairwise (· ≠ ·) :=
  distinct_iff _

/-- Concrete plan validity checks the census, derived keys, profile assignments and root
request coverage. Unknown module ownership cannot default to a permissive profile. -/
def PlanOK (c : Claim) (i : Census) : Prop :=
  c.val.snapshot.toolchain.leanVersion = "4.34.0" ∧
  c.val.snapshot.toolchain.compilerCommit = "293d5d0c0c3f3dded4688b3ccd6a33939ac5102b" ∧
  CensusOK c i ∧ (requiredJobs c i).toList.Pairwise (· ≠ ·) ∧
  (∀ job ∈ requiredJobs c i, stageSubjectCompatible job.1 job.2 = true) ∧
  (∀ e ∈ i.environments, ∀ d ∈ e.declarations,
      (profileForModule c d.moduleKey.name.name).isSome = true) ∧
  (∀ e ∈ i.environments, ∀ r ∈ e.roots, rootRequests c e r.name.name ≠ #[]) ∧
  (.execution ∈ requiredStages c → ∀ e ∈ i.environments, ∀ d ∈ e.policy.declarations,
    ∀ contract ∈ d.executableContract, contract.failure = none →
      ∃ root ∈ e.roots, root.name.name = contract.root)
set_option synthInstance.maxSize 1024 in
instance (c : Claim) (i : Census) : Decidable (PlanOK c i) := by
  letI : Decidable ((requiredJobs c i).toList.Pairwise (· ≠ ·)) :=
    decidable_of_iff _ (requiredJobs_distinct_iff c i)
  unfold PlanOK
  infer_instance

/-- The indexed implementation decides the same proposition as the prior finite scan. -/
theorem planOK_decide_eq_previous (c : Claim) (i : Census) :
    decide (PlanOK c i) = @decide (PlanOK c i) (by unfold PlanOK; infer_instance) := by
  congr

/-- The fixed JobKeys exactly realize the independently derived plan. Admission cannot
accept a caller-selected shorter list, duplicates, or another claim's keys. -/
structure Plan (c : Claim) (i : Census) where
  /-- The job keys, one per required job, in the order of `requiredJobs`. -/
  jobs : Array JobKey
  /-- Proof that the census and its derived plan satisfy `PlanOK`. -/
  valid : PlanOK c i
  /-- Proof that the jobs' stages and subjects are exactly `requiredJobs c i`, in order. -/
  exactJobs : jobs.map (fun k => (k.stage, k.subject)) = requiredJobs c i
  /-- Proof that every job key belongs to the claim `c`. -/
  exactClaim : ∀ k ∈ jobs, k.claim = c

/-- Validate the proposed keyed realization without dropping any record. -/
def admitPlan (c : Claim) (i : Census) (jobs : Array JobKey) : Except String (Plan c i) :=
  if hp : PlanOK c i then
    if hj : jobs.map (fun k => (k.stage, k.subject)) = requiredJobs c i then
      if hc : ∀ k ∈ jobs, k.claim = c then .ok ⟨jobs, hp, hj, hc⟩
      else .error "job belongs to a different claim"
    else .error "jobs do not exactly realize the required plan"
  else .error "invalid census or plan"

theorem admitPlan_invalid_census (c : Claim) (i : Census) (jobs : Array JobKey)
    (invalid : ¬ CensusOK c i) : admitPlan c i jobs = .error "invalid census or plan" := by
  have hp : ¬ PlanOK c i := fun h => invalid h.2.2.1
  simp [admitPlan, hp]

theorem admitPlan_request_mismatch (c : Claim) (i : Census) (jobs : Array JobKey)
    (mismatch : i.environments.map (·.request) ≠ i.requests) :
    admitPlan c i jobs = .error "invalid census or plan" :=
  admitPlan_invalid_census c i jobs (fun h => mismatch h.1)

/-- Any decision of the identical plan predicate preserves every admission outcome,
including ordered realization, exact claim equality and the original refusal precedence. -/
theorem admitPlan_decision_eq (c : Claim) (i : Census) (jobs : Array JobKey)
    (decision : Decidable (PlanOK c i)) :
    admitPlan c i jobs = @dite (Except String (Plan c i)) (PlanOK c i) decision
      (fun hp =>
        if hj : jobs.map (fun k => (k.stage, k.subject)) = requiredJobs c i then
          if hc : ∀ k ∈ jobs, k.claim = c then .ok ⟨jobs, hp, hj, hc⟩
          else .error "job belongs to a different claim"
        else .error "jobs do not exactly realize the required plan")
      (fun _ => .error "invalid census or plan") := by
  by_cases hp : PlanOK c i <;> simp [admitPlan, hp]

/-- Every valid keyed realization is admitted with its exact projections. -/
theorem admitPlan_exact (c : Claim) (i : Census) (p : Plan c i) :
    admitPlan c i p.jobs = .ok p := by
  unfold admitPlan
  rw [dite_eq_left p.valid, dite_eq_left p.exactJobs, dite_eq_left p.exactClaim]
/-- Realize all independently derived jobs; mapM refuses rather than discarding an
unsupported subject. The existing plan admission checks the complete resulting array. -/
def buildPlan (c : Claim) (i : Census) : Except String (Plan c i) := do
  let jobs ← (requiredJobs c i).mapM fun (stage, subject) => admitJobKey c stage subject
  admitPlan c i jobs

end RegulaPolicy
