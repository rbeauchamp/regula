import Std.Data.DHashMap.Lemmas
import RegulaPolicy.Domain
import RegulaPolicy.StackWalk
import Regula.Contract
import Regula.Decision

/-!
# The walk of an execution root

The execution collector of RG3001 and RG3002 (`Regula.Probe`) is an observing pass and a pure
decision. The pass reads the environment for each name that the walk reaches: the targets of the
edges from it, its boundaries, its unresolved paths and its retained compiler body (`NodeRecord`).
The names that the walk queues after a name are a definition of the targets
(`NodeRecord.successors`). The decision (`walk`) takes those records and the root and returns the
visits: each name that the recorded edges reach from the root, one time, in the order of a stack
of queued names. It is the stack walk `StackWalk.walk` over the successors of the records, the
walk that the reader of a result file runs over the successor lists that it decodes
(`Regula.SharedExecution.walk`). `assemble` builds the account of the root from a walk that
returned its visits (`Walked`), through the record of each visit (`Walked.record`). The type of a
record is indexed by its name, so the map of records holds a record only under its own name.

`walk_sound` and `walk_complete` state that the visits are exactly the names that the recorded
edges reach from the root (`Reach`), and `walk_nodup` that each name is visited one time.
`walk_ok` states that the bound of the steps is enough. Each follows from the theorem of the same
name about `StackWalk.walk`, through `reach_iff` and `bounds`. `checked_walk` registers the kind
`Regula.Decides`: a walk returns visits exactly when each name that the recorded edges reach
has a record.
-/

namespace RegulaPolicy.ExecutionWalk

open Lean

/-- The retained compiler body of a name, as the pass reads it. -/
inductive CodeStatus where
  /-- A compiled function body. -/
  | function
  /-- An `extern` body of a name that is `extern`. -/
  | externBody
  /-- An `extern` body of a name that is not `extern`: an opaque export placeholder. -/
  | placeholder
  /-- No body. -/
  | missing
  deriving Repr, DecidableEq, Inhabited

/-- The observed part of a name's record: the field whose value the environment fixes for the name
the record is made at, which is the module that the environment attributes to the name. -/
structure NodeRecord.ToolchainObserved where
  /-- The module that declares the name, when the environment attributes one. -/
  moduleName : Option Name := none
  deriving Inhabited

/-- The part of a name's record that marks an audited project writes decide. `@[extern]` and
`@[implemented_by]` decide whether the pass reads the value at all, so they decide the constants its
value uses and its compiled recursion helper. The simplification candidates are constants whose
type is an equality of two constants with the same list of distinct universe parameters, and they
include the equation lemmas of that shape that an attribute such as `@[simp]` makes Lean generate.
The retained calls include the initializers that `@[init]` names, and the status of the compiler
body reads `@[extern]`. The replacement, history and simplification targets are the data of
`@[implemented_by]`, of the replacement history and of `@[csimp]`, and the unresolved paths include
those of the replacement history. -/
structure NodeRecord.ProjectWritten where
  /-- The names that the retained compiler body of this name calls or names as initializers. -/
  compilerDependencies : Array Name := #[]
  /-- The retained compiler body of this name. -/
  code : CodeStatus := .missing
  /-- The targets of the simplification candidates of this name: constants whose type is an
  equality of this name and a constant, possibly itself, with the same list of distinct universe
  parameters, registered with `@[csimp]` or not. -/
  candidateTargets : Array Name := #[]
  /-- The names that the logical value of this name uses. -/
  logicalTargets : Array Name := #[]
  /-- The compiled recursion helper of this name. -/
  helperTargets : Array Name := #[]
  /-- The targets that the replacement history of this name records. -/
  historyTargets : Array Name := #[]
  /-- The current replacement target of this name. -/
  currentReplacementTargets : Array Name := #[]
  /-- The target of the active simplification of this name. -/
  activeSimplificationTargets : Array Name := #[]
  /-- The replacement targets of this name, for the search of replacement-only cycles. -/
  replacementTargets : Array Name := #[]
  /-- The paths at this name that the pass could not resolve. -/
  unresolved : Array String := #[]
  deriving Inhabited

/-- What the observing pass records of the name `name` that the walk reaches. The type is indexed by
the name, so the map of records (`Records`) holds the record of a name only under that name. The
record holds the targets of the edges from the name and not the edges, so each edge that
`assemble` builds from a record starts at the name of its visit. Each target set is declared in the
part that says where its value comes from. The boundaries hold fields of the two parts of
`ExecutionBoundary`, so they are a field of the record itself. -/
structure NodeRecord (name : Name) extends NodeRecord.ToolchainObserved, NodeRecord.ProjectWritten
    where
  /-- The boundaries at this name, each with the occurrence `0`. -/
  boundaries : Array RegulaPolicy.ExecutionBoundary := #[]
  deriving Inhabited

/-- The names that the walk queues after the name of `record`, in the order of the queue: the
names that its retained compiler body calls, then the targets of its simplification candidates,
of its replacement history, of its current replacement, of its logical value and of its compiled
recursion helper. Each group is in the order of `canonicalNames`, so the visit order and the
parent of each visit are a function of the edge sets of the closure: a reader of the result
file derives them with the same walk (`StackWalk.walk`, in `SharedExecution.walk`). Each queued
name is the target of an edge of the record, by this definition (`mem_successors`). -/
def NodeRecord.successors {name : Name} (record : NodeRecord name) : Array Name :=
  RegulaPolicy.canonicalNames record.compilerDependencies ++
    RegulaPolicy.canonicalNames record.candidateTargets ++
    RegulaPolicy.canonicalNames record.historyTargets ++
    RegulaPolicy.canonicalNames record.currentReplacementTargets ++
    RegulaPolicy.canonicalNames record.logicalTargets ++
    RegulaPolicy.canonicalNames record.helperTargets

/-- `next` is the target of an edge from the name of `record` that the walk follows: a name that
the retained compiler body calls, or a target of a simplification candidate, of the replacement
history, of the current replacement, of the logical value or of the compiled recursion helper. The
closure keeps each of these edges in its channel. -/
def Follows {name : Name} (record : NodeRecord name) (next : Name) : Prop :=
  next ∈ record.compilerDependencies ∨ next ∈ record.candidateTargets ∨
    next ∈ record.historyTargets ∨ next ∈ record.currentReplacementTargets ∨
    next ∈ record.logicalTargets ∨ next ∈ record.helperTargets

/-- The names that the walk queues after a record are the targets of the edges that it follows. -/
theorem mem_successors {name : Name} {record : NodeRecord name} {next : Name} :
    next ∈ record.successors ↔ Follows record next := by
  simp only [NodeRecord.successors, Follows, Array.mem_append, RegulaPolicy.mem_canonicalNames,
    or_assoc]

/-- The records of the pass: the record of each name, under that name. -/
abbrev Records := Std.DHashMap Name NodeRecord

/-! ## The decision -/

/-- A recorded edge: `name` has a record, and the record follows an edge to `next`. -/
def Edge (records : Records) (name next : Name) : Prop :=
  ∃ record, records.get? name = some record ∧ Follows record next

/-- The names that the recorded edges reach from `root`, `root` among them. -/
inductive Reach (records : Records) (root : Name) : Name → Prop
  /-- The root. -/
  | root : Reach records root root
  /-- A name that a recorded edge reaches from a reached name. -/
  | step {name next : Name} : Reach records root name → Edge records name next →
      Reach records root next

/-- What the walk reads of the records: the names that it queues after a name with a record
(`NodeRecord.successors`), and `none` for a name with no record. -/
def successorsOf (records : Records) (name : Name) : Option (Array Name) :=
  (records.get? name).map (·.successors)

/-- The bound of the steps of a walk: one more than the number of names that all records list.
A walk queues the root and the successors of each visited name, one time each. -/
def fuelOf (records : Records) : Nat :=
  records.fold (fun total _ record => total + record.successors.size) 1

/-- What `walk` reads: the records of the pass and the root. -/
structure WalkRequest where
  /-- The records of the pass, by name. -/
  records : Records
  /-- The root of the walk. -/
  root : Name

/-- The decision of the walk: the stack walk (`StackWalk.walk`) from the root over the successors
of the records, in at most `fuelOf` steps. It returns the visits, each name with the position of
the visit that queued it, or the failure: a reached name with no record, or a bound that runs
out, which `walk_ok` excludes. -/
@[regula_decision]
def walk (request : WalkRequest) : Except (StackWalk.Failure Name) (Array (Name × Option Nat)) :=
  StackWalk.walk (successorsOf request.records) (fuelOf request.records) request.root

/-! ## What a walk returns -/

/-- The names that the recorded edges reach are the names that the successors of the records
reach: the successors of a record are the targets of the edges that it follows
(`mem_successors`). -/
theorem reach_iff {records : Records} {root name : Name} :
    Reach records root name ↔ StackWalk.Reach (successorsOf records) root name := by
  constructor
  · intro reach
    induction reach with
    | root => exact .root
    | step _ edge known =>
      obtain ⟨record, found, follows⟩ := edge
      exact .step known (by simp [successorsOf, found]) (mem_successors.mpr follows)
  · intro reach
    induction reach with
    | root => exact .root
    | step _ found listed known =>
      obtain ⟨record, recordFound, rfl⟩ := Option.map_eq_some_iff.mp found
      exact .step known ⟨record, recordFound, mem_successors.mp listed⟩

/-- **Each visit of an accepted walk is a name that the recorded edges reach from the root**
(`StackWalk.walk_sound`). -/
theorem walk_sound {request : WalkRequest} {visits : Array (Name × Option Nat)}
    (accepted : walk request = .ok visits) :
    ∀ visit ∈ visits, Reach request.records request.root visit.1 :=
  fun visit member => reach_iff.mpr (StackWalk.walk_sound accepted visit member)

/-- **Each name that the recorded edges reach from the root is a visit of an accepted walk**
(`StackWalk.walk_complete`). -/
theorem walk_complete {request : WalkRequest} {visits : Array (Name × Option Nat)}
    (accepted : walk request = .ok visits) :
    ∀ name, Reach request.records request.root name → ∃ visit ∈ visits, visit.1 = name :=
  fun name reach => StackWalk.walk_complete accepted name (reach_iff.mp reach)

/-- **An accepted walk visits each name one time** (`StackWalk.walk_nodup`). -/
theorem walk_nodup {request : WalkRequest} {visits : Array (Name × Option Nat)}
    (accepted : walk request = .ok visits) : (visits.toList.map Prod.fst).Nodup :=
  StackWalk.walk_nodup accepted

/-- Each visit of an accepted walk has a record (`StackWalk.walk_recorded`). -/
theorem walk_recorded {request : WalkRequest} {visits : Array (Name × Option Nat)}
    (accepted : walk request = .ok visits) :
    ∀ visit ∈ visits, ∃ record, request.records.get? visit.1 = some record := by
  intro visit member
  obtain ⟨_, found⟩ := StackWalk.walk_recorded accepted visit member
  obtain ⟨record, recordFound, -⟩ := Option.map_eq_some_iff.mp found
  exact ⟨record, recordFound⟩

/-! ## The bound is enough -/

/-- The bound of a walk is more than the number of successors of all records: the names of the
records are distinct, each name with a successor has a record, and `fuelOf` is one more than the
number of names that the records list. -/
theorem bounds (records : Records) :
    StackWalk.Bounds (successorsOf records) (fuelOf records) := by
  refine ⟨records.keys, Std.DHashMap.nodup_keys, ?_, ?_⟩
  · intro name nonzero
    rw [Std.DHashMap.mem_keys, Std.DHashMap.mem_iff_isSome_get?]
    cases found : records.get? name with
    | none => simp [StackWalk.degree, successorsOf, found] at nonzero
    | some record => rfl
  · rw [← Std.DHashMap.map_fst_toList_eq_keys, List.map_map]
    have each : ∀ entry ∈ records.toList,
        (StackWalk.degree (successorsOf records) ∘ Sigma.fst) entry =
          entry.2.successors.size := by
      intro ⟨name, record⟩ member
      have found := Std.DHashMap.mem_toList_iff_get?_eq_some.mp member
      simp [StackWalk.degree, successorsOf, found]
    rw [List.map_congr_left each]
    unfold fuelOf
    rw [Std.DHashMap.fold_eq_foldl_toList]
    suffices sums : ∀ (start : Nat) (entries : List ((n : Name) × NodeRecord n)),
        entries.foldl (fun total entry => total + entry.2.successors.size) start =
          start + (entries.map fun entry => entry.2.successors.size).sum by
      rw [sums]
      omega
    intro start entries
    induction entries generalizing start with
    | nil => simp
    | cons entry rest step =>
      simp only [List.foldl_cons, step, List.map_cons, List.sum_cons]
      omega

/-- The walk has a record for each name that the recorded edges reach from the root. -/
def Recorded (request : WalkRequest) : Prop :=
  ∀ name, Reach request.records request.root name →
    ∃ record, request.records.get? name = some record

/-- **A walk returns visits when each name that the recorded edges reach has a record.** The
bound of the steps is enough (`bounds`, `StackWalk.walk_ok`). -/
theorem walk_ok {request : WalkRequest} (recorded : Recorded request) :
    ∃ visits, walk request = .ok visits :=
  StackWalk.walk_ok (bounds request.records) fun name reach => by
    obtain ⟨record, found⟩ := recorded name (reach_iff.mpr reach)
    exact ⟨record.successors, by simp [successorsOf, found]⟩

/-- `walk` decides `Recorded` exactly: it returns visits exactly when each name that the
recorded edges reach from the root has a record (`walk_ok`, `walk_complete`, `walk_recorded`).
It accepts a root whose record lists no successor, and it refuses a root with no record. The
pass gives the walk a record for each name that it reaches, so a refusal does not occur for its
records. -/
theorem checked_walk : Regula.ExecutableContract walk
    (Regula.Decides (fun result => result.isOk = true) Recorded) :=
  ⟨Regula.Decides.of_iff
    (fun request => by
      constructor
      · intro accepted
        cases h : walk request with
        | error e => simp [h, Except.isOk, Except.toBool] at accepted
        | ok visits =>
          intro name reach
          obtain ⟨visit, member, same⟩ := walk_complete h name reach
          subst same
          exact walk_recorded h visit member
      · intro recorded
        obtain ⟨visits, h⟩ := walk_ok recorded
        simp [h, Except.isOk, Except.toBool])
    (by
      let records : Records := (∅ : Records).insert `root {}
      refine ⟨{ records, root := `root }, ?_⟩
      have found : successorsOf records `root = some ({} : NodeRecord `root).successors := by
        simp [successorsOf, records]
      obtain ⟨more, fuel⟩ : ∃ more, fuelOf records = more + 1 := by
        obtain ⟨_, _, _, below⟩ := bounds records
        exact ⟨fuelOf records - 1, by omega⟩
      simp only [walk, StackWalk.walk, fuel, StackWalk.walkLoop, Std.HashSet.contains_empty,
        Bool.false_eq_true, ↓reduceIte, found]
      cases more <;> rfl)
    ⟨{ records := ∅, root := `root }, by
      have fuel : fuelOf (∅ : Records) = 0 + 1 := by
        unfold fuelOf
        rw [Std.DHashMap.fold_eq_foldl_toList, Std.DHashMap.toList_empty]
        rfl
      simp only [walk, StackWalk.walk, fuel, StackWalk.walkLoop, Std.HashSet.contains_empty,
        Bool.false_eq_true, ↓reduceIte, successorsOf, Std.DHashMap.get?_empty, Option.map_none]
      decide⟩⟩

/-! ## The account of a root -/

/-- The search of replacement-only cycles: the names that remain when names with no edge to a
remaining name are removed, as often as there are names. -/
def cyclicReplacementPaths (edges : Array (Name × Name)) : Array Name := Id.run do
  let mut remaining := edges.foldl (fun names (source, target) =>
    let names := if names.contains source then names else names.push source
    if names.contains target then names else names.push target) #[]
  for _ in [:remaining.size] do
    remaining := remaining.filter fun source =>
      edges.any fun (left, right) => left == source && remaining.contains right
  return remaining

/-- A walk that returned visits: the request, the visits, and the proof that `walk` returned
those visits for the request. `assemble` takes a value of this type, so the account of a root is
built only from the visits of a walk over the records that it reads. -/
structure Walked where
  /-- The records and the root that the walk read. -/
  request : WalkRequest
  /-- The visits that the walk returned. -/
  visits : Array (Name × Option Nat)
  /-- The walk returned these visits for the request. -/
  walked : walk request = .ok visits

/-- The record of a visit of a walk. A visit has a record (`walk_recorded`), so no default
record stands in for one. -/
def Walked.record (walked : Walked) (visit : Name × Option Nat)
    (member : visit ∈ walked.visits) : NodeRecord visit.1 :=
  walked.request.records.get visit.1 <| Std.DHashMap.mem_iff_isSome_get?.mpr <| by
    obtain ⟨record, found⟩ := walk_recorded walked.walked visit member
    rw [found]
    rfl

/-- The account of a root from a walk: the boundaries, the unresolved paths, the compiler edges
and the closure. `rootCompiled` says that the root itself requires retained code. Each part is
the parts of the records of the visits (`Walked.record`) in the order of the visits, then the
search of replacement-only cycles and the required code that is not available. The status of
the compiler body of a required name is read from its record. A required name with no record is
reported as unavailable code, which fails closed. -/
def assemble (rootCompiled : Bool) (walked : Walked) :
    Array RegulaPolicy.ExecutionBoundary × Array String × Array (Name × Name) ×
      RegulaPolicy.ExecutionClosure := Id.run do
  let root := walked.request.root
  let reached : Array ((visit : Name × Option Nat) × NodeRecord visit.1) :=
    walked.visits.attach.map fun ⟨visit, member⟩ => ⟨visit, walked.record visit member⟩
  -- The edges from each visit to the targets that its record lists, in the order of the visits.
  let edgesOf (targets : {name : Name} → NodeRecord name → Array Name) : Array (Name × Name) :=
    reached.flatMap fun entry => (targets entry.2).map (entry.1.1, ·)
  let compilerEdges := edgesOf (·.compilerDependencies)
  let mut compiledNames : Std.HashSet Name := {}
  if rootCompiled then compiledNames := compiledNames.insert root
  for entry in reached do
    for dependency in entry.2.compilerDependencies do
      compiledNames := compiledNames.insert dependency
  let mut unresolved := reached.flatMap (·.2.unresolved)
  let cycles := cyclicReplacementPaths (edgesOf (·.replacementTargets))
  if !cycles.isEmpty then
    unresolved := unresolved.push s!"replacement-only cycle reachable from {cycles}"
  let mut unavailableCode : Array Name := #[]
  for name in compiledNames do
    match ((walked.request.records.get? name).map (·.code) : Option CodeStatus) with
    | some .function | some .externBody => pure ()
    | some .placeholder =>
        unavailableCode := unavailableCode.push name
        unresolved := unresolved.push s!"{name}: compiler body is an opaque export placeholder"
    | some .missing | none =>
        unavailableCode := unavailableCode.push name
        unresolved := unresolved.push s!"{name}: compiled dependency body is unavailable"
  let boundaries := (reached.flatMap (·.2.boundaries)).mapIdx fun occurrence boundary =>
    { boundary with occurrence, compilerCallers := compilerEdges.filterMap fun (caller, callee) =>
        if callee == boundary.name then some caller else none }
  let closure : RegulaPolicy.ExecutionClosure := {
    nodes := RegulaPolicy.canonicalNames (walked.visits.map (·.1))
    visits := reached.map fun entry =>
      { name := entry.1.1, moduleName := entry.2.moduleName, parent := entry.1.2 }
    logicalEdges := RegulaPolicy.canonicalEdges (edgesOf (·.logicalTargets))
    candidateEdges := RegulaPolicy.canonicalEdges (edgesOf (·.candidateTargets))
    historyEdges := RegulaPolicy.canonicalEdges (edgesOf (·.historyTargets))
    currentReplacementEdges :=
      RegulaPolicy.canonicalEdges (edgesOf (·.currentReplacementTargets))
    activeSimplificationEdges :=
      RegulaPolicy.canonicalEdges (edgesOf (·.activeSimplificationTargets))
    helperEdges := RegulaPolicy.canonicalEdges (edgesOf (·.helperTargets))
    requiredCode := RegulaPolicy.canonicalNames compiledNames.toArray
    unavailableCode := RegulaPolicy.canonicalNames unavailableCode
  }
  return (boundaries, unresolved, RegulaPolicy.canonicalEdges compilerEdges, closure)

end RegulaPolicy.ExecutionWalk
