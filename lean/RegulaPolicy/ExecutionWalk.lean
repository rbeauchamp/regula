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

`AccountOf` states the account of a root as a relation over the records and the visits, with no
function of `assemble`: the nodes, the visits, the edge channels, the required and the unavailable
code, the unresolved paths and the boundaries. `assemble_account` states that `assemble` builds
that account for each walk that returned its visits. The relation leaves two orders unstated: the
order of the names in the message of a replacement-only cycle, and the order of the messages for
required code that is not available.
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

/-! ## What the account of a root is

The account is stated here as a relation over the records of the request and the visits of the
walk, with no function of `assemble`. Each name and edge set is in its canonical form, as admission
requires (`ExecutionClosure.Valid`), and holds exactly the names or the edges that the visits and
their records give. The visits and the boundaries are exactly those of the walk and of the visited
records, in their order. The unresolved paths are exactly the paths of the visited records in the
order of the visits, then the message of a replacement-only cycle when there is one, then one
message for each required name with no available code. The order of the names in the cycle message
and the order of the messages for code are not stated. -/

/-- `name` is the name of a visit. -/
def Visited (visits : Array (Name × Option Nat)) (name : Name) : Prop :=
  ∃ visit ∈ visits, visit.1 = name

/-- `edge` starts at a visited name, and the record of that name lists its end among `targets`. -/
def VisitedEdge (records : Records) (visits : Array (Name × Option Nat))
    (targets : {name : Name} → NodeRecord name → Array Name) (edge : Name × Name) : Prop :=
  Visited visits edge.1 ∧
    ∃ record : NodeRecord edge.1, records.get? edge.1 = some record ∧ edge.2 ∈ targets record

/-- An edge set of the account: in canonical form, and exactly the visited edges to `targets`. -/
def ChannelOf (records : Records) (visits : Array (Name × Option Nat))
    (targets : {name : Name} → NodeRecord name → Array Name) (edges : Array (Name × Name)) :
    Prop :=
  RegulaPolicy.canonicalEdges edges = edges ∧
    ∀ edge, edge ∈ edges ↔ VisitedEdge records visits targets edge

/-- A name that requires retained code: the root, when the root requires it, and each name that
the retained compiler body of a visited name calls. -/
def Required (request : WalkRequest) (visits : Array (Name × Option Nat)) (rootCompiled : Bool)
    (name : Name) : Prop :=
  (rootCompiled = true ∧ name = request.root) ∨
    ∃ caller, VisitedEdge request.records visits (·.compilerDependencies) (caller, name)

/-- A name with available code: its record has a compiled function body or an `extern` body. -/
def Available (records : Records) (name : Name) : Prop :=
  ∃ record : NodeRecord name, records.get? name = some record ∧
    (record.code = .function ∨ record.code = .externBody)

/-- The visited replacement edges have a cycle: some names, at least one, each with a visited
replacement edge to one of them. -/
def ReplacementCycle (records : Records) (visits : Array (Name × Option Nat)) : Prop :=
  ∃ names : List Name, names ≠ [] ∧
    ∀ name ∈ names, ∃ next ∈ names, VisitedEdge records visits (·.replacementTargets) (name, next)

/-- `name` is one of some names, each with a visited replacement edge to one of them. The set is
not empty, as `name` is in it, and each of its names is visited, as each edge starts at a visited
name. The names with such a set make the greatest such set: the names on a cycle of visited
replacement edges and the names from which such a cycle can be reached. -/
def OnReplacementCycle (records : Records) (visits : Array (Name × Option Nat)) (name : Name) :
    Prop :=
  ∃ names : List Name, name ∈ names ∧
    ∀ member ∈ names, ∃ next ∈ names,
      VisitedEdge records visits (·.replacementTargets) (member, next)

/-- The visited replacement edges have a cycle exactly when some name satisfies
`OnReplacementCycle`. -/
theorem replacementCycle_iff {records : Records} {visits : Array (Name × Option Nat)} :
    ReplacementCycle records visits ↔ ∃ name, OnReplacementCycle records visits name := by
  constructor
  · rintro ⟨names, nonempty, closed⟩
    obtain ⟨first, member⟩ := List.exists_mem_of_ne_nil names nonempty
    exact ⟨first, names, member, closed⟩
  · rintro ⟨name, names, member, closed⟩
    exact ⟨names, List.ne_nil_of_mem member, closed⟩

/-- The record of `name` has an opaque export placeholder as its compiler body. -/
def Placeholder (records : Records) (name : Name) : Prop :=
  ∃ record : NodeRecord name, records.get? name = some record ∧ record.code = .placeholder

/-- The message for a required name with no available code: that its compiler body is a
placeholder when its record has one, and otherwise that its body is unavailable. -/
def CodeMessage (records : Records) (name : Name) (message : String) : Prop :=
  (Placeholder records name ∧ message = s!"{name}: compiler body is an opaque export placeholder") ∨
    (¬ Placeholder records name ∧ message = s!"{name}: compiled dependency body is unavailable")

/-- The unresolved paths of the visited records, in the order of the visits. -/
def visitedPaths (records : Records) (visits : Array (Name × Option Nat)) : List String :=
  visits.toList.flatMap fun visit =>
    match records.get? visit.1 with
    | some record => record.unresolved.toList
    | none => []

/-- The boundaries of the visited records, in the order of the visits. -/
def visitedBoundaries (records : Records) (visits : Array (Name × Option Nat)) :
    List RegulaPolicy.ExecutionBoundary :=
  visits.toList.flatMap fun visit =>
    match records.get? visit.1 with
    | some record => record.boundaries.toList
    | none => []

/-- **The account of a root.** `account` is the boundaries, the unresolved paths, the compiler
edges and the closure that the visits of a walk and their records give:

- The nodes are canonical and are the visited names. The closure's visits are the walk's visits in
  their order, each with the module of its record and the position of its parent.
- Each edge channel and the compiler edges are canonical and are the edges from a visited name
  to a target of that channel in its record.
- The required code is canonical: the root when `rootCompiled`, and each name that a visited
  record's compiler body calls. The unavailable code is canonical: the required names with no
  record that has a function body or an `extern` body.
- The unresolved paths are the paths of the visited records in the order of the visits, then the
  message of a replacement-only cycle, then the messages for code. The cycle message is there
  exactly when the visited replacement edges have a cycle (`replacementCycle_iff`). It lists, each
  one time, the names that satisfy `OnReplacementCycle`: the names on a cycle of visited replacement
  edges and the names from which such a cycle can be reached. There is one message for each
  required name with no available code (`CodeMessage`). The order of the names in the cycle
  message and the order of the messages for code are not stated.
- The boundaries are the boundaries of the visited records in the order of the visits. Each has
  its index as its occurrence, and the callers of its name in the compiler edges as its callers. -/
def AccountOf (request : WalkRequest) (visits : Array (Name × Option Nat)) (rootCompiled : Bool)
    (account : Array RegulaPolicy.ExecutionBoundary × Array String × Array (Name × Name) ×
      RegulaPolicy.ExecutionClosure) : Prop :=
  let boundaries := account.1
  let unresolved := account.2.1
  let compilerEdges := account.2.2.1
  let closure := account.2.2.2
  let records := request.records
  -- The nodes and the visits.
  (RegulaPolicy.canonicalNames closure.nodes = closure.nodes ∧
    ∀ name, name ∈ closure.nodes ↔ Visited visits name) ∧
  (closure.visits.size = visits.size ∧ ∀ (index : Nat) (inVisits : index < visits.size)
      (inClosure : index < closure.visits.size),
    closure.visits[index].name = visits[index].1 ∧ closure.visits[index].parent = visits[index].2 ∧
      ∀ record : NodeRecord visits[index].1, records.get? visits[index].1 = some record →
        closure.visits[index].moduleName = record.moduleName) ∧
  -- The edges.
  ChannelOf records visits (·.compilerDependencies) compilerEdges ∧
  ChannelOf records visits (·.logicalTargets) closure.logicalEdges ∧
  ChannelOf records visits (·.candidateTargets) closure.candidateEdges ∧
  ChannelOf records visits (·.historyTargets) closure.historyEdges ∧
  ChannelOf records visits (·.currentReplacementTargets) closure.currentReplacementEdges ∧
  ChannelOf records visits (·.activeSimplificationTargets) closure.activeSimplificationEdges ∧
  ChannelOf records visits (·.helperTargets) closure.helperEdges ∧
  -- The code.
  (RegulaPolicy.canonicalNames closure.requiredCode = closure.requiredCode ∧
    ∀ name, name ∈ closure.requiredCode ↔ Required request visits rootCompiled name) ∧
  (RegulaPolicy.canonicalNames closure.unavailableCode = closure.unavailableCode ∧
    ∀ name, name ∈ closure.unavailableCode ↔
      Required request visits rootCompiled name ∧ ¬ Available records name) ∧
  -- The unresolved paths.
  (∃ (cycleNames : Array Name) (codeEntries : List (Name × String)),
    cycleNames.toList.Nodup ∧
    (∀ name, name ∈ cycleNames ↔ OnReplacementCycle records visits name) ∧
    (codeEntries.map (·.1)).Nodup ∧
    (∀ name, name ∈ codeEntries.map (·.1) ↔
      Required request visits rootCompiled name ∧ ¬ Available records name) ∧
    (∀ entry ∈ codeEntries, CodeMessage records entry.1 entry.2) ∧
    unresolved.toList = visitedPaths records visits ++
      (if cycleNames = #[] then [] else [s!"replacement-only cycle reachable from {cycleNames}"]) ++
      codeEntries.map (·.2)) ∧
  -- The boundaries.
  boundaries.size = (visitedBoundaries records visits).length ∧
  ∀ (index : Nat) (inBoundaries : index < boundaries.size)
    (inVisited : index < (visitedBoundaries records visits).length),
    boundaries[index].occurrence = index ∧
    { boundaries[index] with occurrence := 0, compilerCallers := #[] } =
      { (visitedBoundaries records visits)[index] with occurrence := 0, compilerCallers := #[] } ∧
    ∀ caller, caller ∈ boundaries[index].compilerCallers ↔
      VisitedEdge records visits (·.compilerDependencies) (caller, boundaries[index].name)

/-! ## `assemble` gives the account -/

/-- The visits of a walk, each with its record. -/
private def reachedOf (walked : Walked) :
    Array ((visit : Name × Option Nat) × NodeRecord visit.1) :=
  walked.visits.attach.map fun ⟨visit, member⟩ => ⟨visit, walked.record visit member⟩

/-- The edges from each visit to the targets that its record lists, in the order of the visits. -/
private def edgesFrom (walked : Walked) (targets : {name : Name} → NodeRecord name → Array Name) :
    Array (Name × Name) :=
  (reachedOf walked).flatMap fun entry => (targets entry.2).map (entry.1.1, ·)

private theorem assemble_nodes (rootCompiled : Bool) (walked : Walked) :
    (assemble rootCompiled walked).2.2.2.nodes =
      RegulaPolicy.canonicalNames (walked.visits.map (·.1)) := by
  unfold assemble
  simp only [Id.run]
  split <;> (try split) <;> rfl

private theorem assemble_visits (rootCompiled : Bool) (walked : Walked) :
    (assemble rootCompiled walked).2.2.2.visits = (reachedOf walked).map fun entry =>
      { name := entry.1.1, moduleName := entry.2.moduleName, parent := entry.1.2 } := by
  unfold assemble
  simp only [Id.run]
  split <;> (try split) <;> rfl

private theorem assemble_compilerEdges (rootCompiled : Bool) (walked : Walked) :
    (assemble rootCompiled walked).2.2.1 =
      RegulaPolicy.canonicalEdges (edgesFrom walked (·.compilerDependencies)) := by
  unfold assemble
  simp only [Id.run]
  split <;> (try split) <;> rfl

private theorem assemble_channels (rootCompiled : Bool) (walked : Walked) :
    let closure := (assemble rootCompiled walked).2.2.2
    closure.logicalEdges = RegulaPolicy.canonicalEdges (edgesFrom walked (·.logicalTargets)) ∧
    closure.candidateEdges = RegulaPolicy.canonicalEdges (edgesFrom walked (·.candidateTargets)) ∧
    closure.historyEdges = RegulaPolicy.canonicalEdges (edgesFrom walked (·.historyTargets)) ∧
    closure.currentReplacementEdges =
      RegulaPolicy.canonicalEdges (edgesFrom walked (·.currentReplacementTargets)) ∧
    closure.activeSimplificationEdges =
      RegulaPolicy.canonicalEdges (edgesFrom walked (·.activeSimplificationTargets)) ∧
    closure.helperEdges = RegulaPolicy.canonicalEdges (edgesFrom walked (·.helperTargets)) := by
  unfold assemble
  simp only [Id.run]
  split <;> (try split) <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem assemble_boundaries (rootCompiled : Bool) (walked : Walked) :
    (assemble rootCompiled walked).1 =
      ((reachedOf walked).flatMap (·.2.boundaries)).mapIdx fun occurrence boundary =>
        { boundary with occurrence, compilerCallers :=
            (edgesFrom walked (·.compilerDependencies)).filterMap fun (caller, callee) =>
              if callee == boundary.name then some caller else none } := by
  unfold assemble
  simp only [Id.run]
  split <;> (try split) <;> rfl

/-- The names that require retained code: the root, when it requires it, then the calls of the
compiler body of each visit, in the order of the visits. -/
private def requiredSet (rootCompiled : Bool) (walked : Walked) : Std.HashSet Name :=
  (reachedOf walked).foldl (fun names entry =>
      entry.2.compilerDependencies.foldl (fun names name => names.insert name) names)
    (if rootCompiled then (∅ : Std.HashSet Name).insert walked.request.root else ∅)

/-- One required name: no change when its record has a function body or an `extern` body, and
otherwise a message and the name. -/
private def codeStep (records : Records) (state : Array String × Array Name) (name : Name) :
    Array String × Array Name :=
  match ((records.get? name).map (·.code) : Option CodeStatus) with
  | some .function | some .externBody => state
  | some .placeholder =>
      (state.1.push s!"{name}: compiler body is an opaque export placeholder", state.2.push name)
  | some .missing | none =>
      (state.1.push s!"{name}: compiled dependency body is unavailable", state.2.push name)

/-- The unresolved paths before the required code: those of each visit, then the message of a
replacement-only cycle when the search finds one. -/
private def pathsOf (walked : Walked) : Array String :=
  let cycles := cyclicReplacementPaths (edgesFrom walked (·.replacementTargets))
  let paths := (reachedOf walked).flatMap (·.2.unresolved)
  if !cycles.isEmpty then paths.push s!"replacement-only cycle reachable from {cycles}" else paths

/-- A loop of `Id` whose body always continues with `g` is the fold of `g`. -/
private theorem forIn_yield_id {α β : Type} (l : List α) (init : β)
    (f : α → β → Id (ForInStep β)) (g : β → α → β) (h : ∀ a b, f a b = pure (.yield (g b a))) :
    forIn l init f = pure (l.foldl g init) := by
  have : f = fun a b => pure (.yield (g b a)) := funext fun a => funext fun b => h a b
  subst this
  simp

private theorem codeStep_loop (records : Records) (name : Name)
    (state : Array String × Array Name) :
    (match ((records.get? name).map (·.code) : Option CodeStatus) with
      | some .function => (pure (ForInStep.yield (state.1, state.2)) : Id _)
      | some .externBody => pure (ForInStep.yield (state.1, state.2))
      | some .placeholder => pure (ForInStep.yield
          (state.1.push
            (toString name ++ toString ": compiler body is an opaque export placeholder"),
            state.2.push name))
      | some .missing => pure (ForInStep.yield
          (state.1.push (toString name ++ toString ": compiled dependency body is unavailable"),
            state.2.push name))
      | none => pure (ForInStep.yield
          (state.1.push (toString name ++ toString ": compiled dependency body is unavailable"),
            state.2.push name))) =
      pure (.yield (codeStep records state name)) := by
  unfold codeStep
  split <;> rfl

private theorem assemble_code (rootCompiled : Bool) (walked : Walked) :
    let result := (requiredSet rootCompiled walked).toList.foldl
      (codeStep walked.request.records) (pathsOf walked, #[])
    (assemble rootCompiled walked).2.1 = result.1 ∧
    (assemble rootCompiled walked).2.2.2.requiredCode =
      RegulaPolicy.canonicalNames (requiredSet rootCompiled walked).toArray ∧
    (assemble rootCompiled walked).2.2.2.unavailableCode =
      RegulaPolicy.canonicalNames result.2 := by
  unfold assemble
  simp only [Id.run]
  split
  all_goals
    simp only [Array.forIn_pure_yield_eq_foldl, pure_bind]
    split
  all_goals
    rw [Std.HashSet.forIn_eq_forIn_toList, forIn_yield_id _ _ _ (codeStep walked.request.records)
      (fun name state => codeStep_loop walked.request.records name state)]
    simp only [pure_bind]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [requiredSet, pathsOf, reachedOf, edgesFrom, *, ↓reduceIte, Bool.false_eq_true] <;>
        rfl

/-- The record of a visit is the record that the map holds under its name. -/
private theorem get?_record (walked : Walked) (visit : Name × Option Nat)
    (member : visit ∈ walked.visits) :
    walked.request.records.get? visit.1 = some (walked.record visit member) := by
  unfold Walked.record
  exact Std.DHashMap.get?_eq_some_get _

private theorem mem_reachedOf {walked : Walked}
    {entry : (visit : Name × Option Nat) × NodeRecord visit.1} :
    entry ∈ reachedOf walked ↔
      ∃ (visit : Name × Option Nat) (member : visit ∈ walked.visits),
        entry = ⟨visit, walked.record visit member⟩ := by
  unfold reachedOf
  constructor
  · intro found
    obtain ⟨⟨visit, member⟩, -, rfl⟩ := Array.mem_map.mp found
    exact ⟨visit, member, rfl⟩
  · rintro ⟨visit, member, rfl⟩
    exact Array.mem_map.mpr ⟨⟨visit, member⟩, Array.mem_attach _ _, rfl⟩

/-- **The edges that `assemble` builds from the records of the visits are the visited edges.** -/
private theorem mem_edgesFrom {walked : Walked}
    {targets : {name : Name} → NodeRecord name → Array Name}
    {edge : Name × Name} :
    edge ∈ edgesFrom walked targets ↔
      VisitedEdge walked.request.records walked.visits targets edge := by
  unfold edgesFrom VisitedEdge Visited
  constructor
  · intro found
    obtain ⟨entry, inReached, inMap⟩ := Array.mem_flatMap.mp found
    obtain ⟨visit, member, rfl⟩ := mem_reachedOf.mp inReached
    obtain ⟨target, listed, rfl⟩ := Array.mem_map.mp inMap
    exact ⟨⟨visit, member, rfl⟩, walked.record visit member, get?_record walked visit member,
      listed⟩
  · obtain ⟨source, target⟩ := edge
    rintro ⟨⟨visit, member, named⟩, record, found, listed⟩
    obtain ⟨name, parent⟩ := visit
    simp only at named
    subst named
    rw [get?_record walked _ member] at found
    obtain rfl := Option.some.inj found
    exact Array.mem_flatMap.mpr ⟨⟨(name, parent), walked.record (name, parent) member⟩,
      mem_reachedOf.mpr ⟨_, member, rfl⟩, Array.mem_map.mpr ⟨target, listed, rfl⟩⟩

private theorem mem_foldl_insert (names : Array Name) (start : Std.HashSet Name) (name : Name) :
    name ∈ names.foldl (fun names name => names.insert name) start ↔
      name ∈ start ∨ name ∈ names := by
  rw [← Array.foldl_toList, ← Array.mem_toList_iff]
  induction names.toList generalizing start with
  | nil => simp
  | cons first rest ih =>
    simp only [List.foldl_cons, ih, Std.HashSet.mem_insert, beq_iff_eq, List.mem_cons]
    constructor
    · rintro ((rfl | inStart) | inRest)
      · exact .inr (.inl rfl)
      · exact .inl inStart
      · exact .inr (.inr inRest)
    · rintro (inStart | rfl | inRest)
      · exact .inl (.inr inStart)
      · exact .inl (.inl rfl)
      · exact .inr inRest

/-- **The required names are the root, when it requires retained code, and each name that the
compiler body of a visited record calls.** -/
private theorem mem_requiredSet (rootCompiled : Bool) (walked : Walked) (name : Name) :
    name ∈ requiredSet rootCompiled walked ↔
      Required walked.request walked.visits rootCompiled name := by
  have outer : ∀ (entries : List ((visit : Name × Option Nat) × NodeRecord visit.1))
      (start : Std.HashSet Name),
      name ∈ entries.foldl (fun names entry =>
          entry.2.compilerDependencies.foldl (fun names name => names.insert name) names) start ↔
        name ∈ start ∨ ∃ entry ∈ entries, name ∈ entry.2.compilerDependencies := by
    intro entries
    induction entries with
    | nil => intro start; simp
    | cons first rest ih =>
      intro start
      simp only [List.foldl_cons, ih, mem_foldl_insert, List.mem_cons]
      constructor
      · rintro ((inStart | inFirst) | ⟨entry, inRest, listed⟩)
        · exact .inl inStart
        · exact .inr ⟨first, .inl rfl, inFirst⟩
        · exact .inr ⟨entry, .inr inRest, listed⟩
      · rintro (inStart | ⟨entry, rfl | inRest, listed⟩)
        · exact .inl (.inl inStart)
        · exact .inl (.inr listed)
        · exact .inr ⟨entry, inRest, listed⟩
  unfold requiredSet Required
  rw [← Array.foldl_toList, outer]
  have called : (∃ entry ∈ (reachedOf walked).toList, name ∈ entry.2.compilerDependencies) ↔
      ∃ caller, VisitedEdge walked.request.records walked.visits (·.compilerDependencies)
        (caller, name) := by
    constructor
    · rintro ⟨entry, inReached, listed⟩
      refine ⟨entry.1.1, mem_edgesFrom.mp (Array.mem_flatMap.mpr ⟨entry, ?_, ?_⟩)⟩
      · exact Array.mem_toList_iff.mp inReached
      · exact Array.mem_map.mpr ⟨name, listed, rfl⟩
    · rintro ⟨caller, visited⟩
      obtain ⟨entry, inReached, inMap⟩ := Array.mem_flatMap.mp (mem_edgesFrom.mpr visited)
      obtain ⟨target, listed, same⟩ := Array.mem_map.mp inMap
      obtain ⟨-, rfl⟩ := Prod.mk.inj same
      exact ⟨entry, Array.mem_toList_iff.mpr inReached, listed⟩
  rw [called]
  cases rootCompiled
  · simp
  · simp only [↓reduceIte, Std.HashSet.mem_insert, beq_iff_eq, true_and]
    have empty : name ∉ (∅ : Std.HashSet Name) := Std.HashSet.not_mem_empty
    simp only [empty, or_false]
    exact or_congr_left ⟨Eq.symm, Eq.symm⟩

/-- One required name keeps the state when its code is available, and otherwise adds its message
and the name. -/
private theorem codeStep_cases (records : Records) (state : Array String × Array Name)
    (name : Name) :
    (Available records name ∧ codeStep records state name = state) ∨
      (¬ Available records name ∧ ∃ message, CodeMessage records name message ∧
        codeStep records state name = (state.1.push message, state.2.push name)) := by
  unfold codeStep Available CodeMessage Placeholder
  cases found : records.get? name with
  | none =>
    refine .inr ⟨?_, _, .inr ⟨?_, rfl⟩, rfl⟩
    · rintro ⟨record, inMap, -⟩
      cases inMap
    · rintro ⟨record, inMap, -⟩
      cases inMap
  | some record =>
    cases code : record.code with
    | function => exact .inl ⟨⟨record, rfl, .inl code⟩, by simp [code]⟩
    | externBody => exact .inl ⟨⟨record, rfl, .inr code⟩, by simp [code]⟩
    | placeholder =>
      refine .inr ⟨?_, _, .inl ⟨⟨record, rfl, code⟩, rfl⟩, by simp [code]⟩
      rintro ⟨other, found', function | extern⟩ <;> cases Option.some.inj found' <;>
        simp_all
    | missing =>
      refine .inr ⟨?_, _, .inr ⟨?_, rfl⟩, by simp [code]⟩
      · rintro ⟨other, found', function | extern⟩ <;> cases Option.some.inj found' <;>
          simp_all
      · rintro ⟨other, found', placeholder⟩
        cases Option.some.inj found'
        simp_all

/-- **The loop over the required names.** It adds one entry, a name and its message, for each
listed name with no available code, in the order of the list. -/
private theorem codeStep_fold (records : Records) :
    ∀ (names : List Name) (paths : Array String) (unavailable : Array Name),
      ∃ entries : List (Name × String),
        (entries.map (·.1)).Sublist names ∧
        (∀ name, name ∈ entries.map (·.1) ↔ name ∈ names ∧ ¬ Available records name) ∧
        (∀ entry ∈ entries, CodeMessage records entry.1 entry.2) ∧
        (names.foldl (codeStep records) (paths, unavailable)).1.toList =
          paths.toList ++ entries.map (·.2) ∧
        (names.foldl (codeStep records) (paths, unavailable)).2.toList =
          unavailable.toList ++ entries.map (·.1) := by
  intro names
  induction names with
  | nil => intro paths unavailable; exact ⟨[], by simp⟩
  | cons first rest ih =>
    intro paths unavailable
    rcases codeStep_cases records (paths, unavailable) first with ⟨available, same⟩ |
      ⟨missing, message, described, pushed⟩
    · simp only [List.foldl_cons, same]
      obtain ⟨entries, sublist, members, messages, pathsEq, namesEq⟩ := ih paths unavailable
      refine ⟨entries, sublist.cons _, fun name => ?_, messages, pathsEq, namesEq⟩
      rw [members, List.mem_cons]
      constructor
      · rintro ⟨inRest, notAvailable⟩
        exact ⟨.inr inRest, notAvailable⟩
      · rintro ⟨rfl | inRest, notAvailable⟩
        · exact absurd available notAvailable
        · exact ⟨inRest, notAvailable⟩
    · simp only [List.foldl_cons, pushed]
      obtain ⟨entries, sublist, members, messages, pathsEq, namesEq⟩ :=
        ih (paths.push message) (unavailable.push first)
      refine ⟨(first, message) :: entries, sublist.cons_cons _, fun name => ?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.mem_cons, members]
        constructor
        · rintro (rfl | ⟨inRest, notAvailable⟩)
          · exact ⟨.inl rfl, missing⟩
          · exact ⟨.inr inRest, notAvailable⟩
        · rintro ⟨rfl | inRest, notAvailable⟩
          · exact .inl rfl
          · exact .inr ⟨inRest, notAvailable⟩
      · intro entry inEntries
        rcases List.mem_cons.mp inEntries with rfl | inRest
        · exact described
        · exact messages entry inRest
      · rw [pathsEq, Array.toList_push]
        simp
      · rw [namesEq, Array.toList_push]
        simp

/-- A fold whose step keeps each name and adds the source of its edge holds each source. -/
private theorem mem_foldl_sources (edges : Array (Name × Name))
    (step : Array Name → Name × Name → Array Name)
    (keeps : ∀ names edge, ∀ name ∈ names, name ∈ step names edge)
    (adds : ∀ names edge, edge.1 ∈ step names edge) (start : Array Name) :
    ∀ edge ∈ edges, edge.1 ∈ edges.foldl step start := by
  have stays : ∀ (rest : List (Name × Name)) (names : Array Name) (name : Name), name ∈ names →
      name ∈ rest.foldl step names := by
    intro rest
    induction rest with
    | nil => intro names name inNames; exact inNames
    | cons first more ih => intro names name inNames; exact ih _ _ (keeps _ _ _ inNames)
  intro edge inEdges
  rw [← Array.foldl_toList]
  have listed := Array.mem_toList_iff.mpr inEdges
  generalize edges.toList = list at listed ⊢
  induction list generalizing start with
  | nil => cases listed
  | cons first more ih =>
    rcases List.mem_cons.mp listed with rfl | inMore
    · exact stays more _ _ (adds start _)
    · exact ih _ inMore

/-- A loop of `Id` over a range whose body keeps a property keeps it. -/
private theorem range_loop_keeps {β : Type} (P : β → Prop) (step : β → β)
    (keeps : ∀ value, P value → P (step value)) (range : Std.Legacy.Range) (start : β)
    (holds : P start) :
    P (Id.run (forIn range start fun _ value => pure (ForInStep.yield (step value)))) := by
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl]
  generalize List.range' _ _ _ = indices
  induction indices generalizing start with
  | nil => exact holds
  | cons first more ih => exact ih _ (keeps _ holds)

/-- **The search keeps each name of a cycle.** Names, each with an edge to one of them, remain
after each step of `cyclicReplacementPaths`, so the search returns them. -/
private theorem cycle_kept (edges : Array (Name × Name)) (names : List Name)
    (closed : ∀ name ∈ names, ∃ next ∈ names, (name, next) ∈ edges) :
    ∀ name ∈ names, name ∈ cyclicReplacementPaths edges := by
  unfold cyclicReplacementPaths
  apply range_loop_keeps (fun remaining => ∀ name ∈ names, name ∈ remaining)
  · intro remaining kept name member
    obtain ⟨next, inNames, edge⟩ := closed name member
    refine Array.mem_filter.mpr ⟨kept name member, Array.any_eq_true.mpr ?_⟩
    obtain ⟨index, inBounds, same⟩ := Array.mem_iff_getElem.mp edge
    exact ⟨index, inBounds, by simp [same, kept next inNames]⟩
  · intro name member
    obtain ⟨next, -, edge⟩ := closed name member
    refine mem_foldl_sources edges _ ?_ ?_ #[] (name, next) edge
    · intro seen edge name inSeen
      simp only
      split <;> split <;> simp_all
    · intro seen edge
      simp only
      split <;> split <;> simp_all

/-- A loop of `Id` over `[:count]` turns a property of the count of the steps left and the value
into the same property after the last step, when each step keeps it with one step fewer. -/
private theorem range_loop_counts {β : Type} (P : Nat → β → Prop) (step : β → β)
    (keeps : ∀ left value, P (left + 1) value → P left (step value)) (count : Nat) (start : β)
    (holds : P count start) :
    P 0 (Id.run (forIn [:count] start fun _ value => pure (ForInStep.yield (step value)))) := by
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl]
  have general : ∀ (indices : List Nat) (start : β), P indices.length start →
      P 0 (indices.foldl (fun value _ => step value) start) := by
    intro indices
    induction indices with
    | nil => intro start holds; exact holds
    | cons first more ih => intro start holds; exact ih _ (keeps _ _ holds)
  apply general
  simpa [Std.Legacy.Range.size] using holds

/-- A fold whose step keeps a property keeps it. -/
private theorem foldl_keeps {α β : Type} (P : β → Prop) (step : β → α → β)
    (keeps : ∀ value item, P value → P (step value item)) (items : Array α) (start : β)
    (holds : P start) : P (items.foldl step start) := by
  rw [← Array.foldl_toList]
  generalize items.toList = list
  induction list generalizing start with
  | nil => exact holds
  | cons first more ih => exact ih _ (keeps _ _ holds)

/-- One step of the search keeps the names with an edge to a remaining name. Before the step, the
names are at most one more than the steps left after it, or each has an edge to one of them.
After the step, the names are at most the steps left, or each has an edge to one of them: a step
that removes no name leaves the names as they were, and one that removes a name makes them fewer. -/
private theorem filter_step (edges : Array (Name × Name)) (remaining : Array Name)
    (keep : Name → Bool)
    (keeps : ∀ source, keep source = true ↔ ∃ next ∈ remaining, (source, next) ∈ edges)
    (left : Nat)
    (holds : remaining.size ≤ left + 1 ∨
      ∀ name ∈ remaining, ∃ next ∈ remaining, (name, next) ∈ edges) :
    (remaining.filter keep).size ≤ left ∨
      ∀ name ∈ remaining.filter keep, ∃ next ∈ remaining.filter keep, (name, next) ∈ edges := by
  by_cases every : ∀ source ∈ remaining, keep source = true
  · rw [Array.filter_eq_self.mpr every]
    exact .inr fun name member => (keeps name).mp (every name member)
  · have dropped : ∃ source ∈ remaining, ¬ keep source = true :=
      Classical.byContradiction fun none => every fun source member =>
        Classical.byContradiction fun notKept => none ⟨source, member, notKept⟩
    have fewer := Array.size_filter_lt_size_iff_exists.mpr dropped
    rcases holds with small | closed
    · exact .inl (by omega)
    · exact absurd (fun source member => (keeps source).mpr (closed source member)) every

/-- **The search returns names, each with an edge to one of them.** The loop runs one time for each
name of the edges, so after the last step (`filter_step`) no name remains, or each has an edge to
a remaining name. -/
private theorem cycles_closed (edges : Array (Name × Name)) :
    ∀ name ∈ cyclicReplacementPaths edges,
      ∃ next ∈ cyclicReplacementPaths edges, (name, next) ∈ edges := by
  have final : (cyclicReplacementPaths edges).size ≤ 0 ∨
      ∀ name ∈ cyclicReplacementPaths edges,
        ∃ next ∈ cyclicReplacementPaths edges, (name, next) ∈ edges := by
    unfold cyclicReplacementPaths
    apply range_loop_counts (fun left (remaining : Array Name) => remaining.size ≤ left ∨
      ∀ name ∈ remaining, ∃ next ∈ remaining, (name, next) ∈ edges)
    · intro left remaining holds
      refine filter_step edges remaining _ (fun source => ?_) left holds
      dsimp only
      rw [Array.any_eq_true']
      constructor
      · rintro ⟨⟨first, second⟩, inEdges, chosen⟩
        simp only [Bool.and_eq_true, beq_iff_eq, Array.contains_iff_mem] at chosen
        obtain ⟨rfl, inRemaining⟩ := chosen
        exact ⟨second, inRemaining, inEdges⟩
      · rintro ⟨next, inRemaining, inEdges⟩
        exact ⟨(source, next), inEdges, by simp [inRemaining]⟩
    · exact .inl (Nat.le_refl _)
  intro name member
  rcases final with empty | closed
  · exact absurd (Array.size_pos_of_mem member) (by omega)
  · exact closed name member

/-- Adding a name only when it is absent keeps the names distinct. -/
private theorem nodup_push_absent (names : Array Name) (name : Name) (nodup : names.toList.Nodup) :
    (if names.contains name then names else names.push name).toList.Nodup := by
  split
  · exact nodup
  · next missing =>
    rw [Array.toList_push, List.nodup_append]
    refine ⟨nodup, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro other inNames last inLast same
    rw [List.mem_singleton] at inLast
    subst inLast
    subst same
    exact missing (Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp inNames))

/-- The search returns each name one time: its first pass adds a name only when it is absent, and
each step keeps a part of the names. -/
private theorem cycles_nodup (edges : Array (Name × Name)) :
    (cyclicReplacementPaths edges).toList.Nodup := by
  unfold cyclicReplacementPaths
  apply range_loop_keeps (fun remaining : Array Name => remaining.toList.Nodup)
  · intro remaining nodup
    rw [Array.toList_filter]
    exact List.filter_sublist.nodup nodup
  · apply foldl_keeps (fun names : Array Name => names.toList.Nodup)
    · intro names ⟨source, target⟩ nodup
      dsimp only
      exact nodup_push_absent _ _ (nodup_push_absent _ _ nodup)
    · exact List.nodup_nil

/-- **The search returns exactly the names that satisfy `OnReplacementCycle`:** the names on a
cycle of visited replacement edges and the names from which such a cycle can be reached. A name
that it returns is one of the names that it returns, each with an edge to one of them
(`cycles_closed`), and the search keeps each name of such a set (`cycle_kept`). -/
private theorem mem_cycles (walked : Walked) (name : Name) :
    name ∈ cyclicReplacementPaths (edgesFrom walked (·.replacementTargets)) ↔
      OnReplacementCycle walked.request.records walked.visits name := by
  constructor
  · intro member
    refine ⟨(cyclicReplacementPaths (edgesFrom walked (·.replacementTargets))).toList,
      Array.mem_toList_iff.mpr member, fun other inNames => ?_⟩
    obtain ⟨next, inCycles, edge⟩ := cycles_closed _ other (Array.mem_toList_iff.mp inNames)
    exact ⟨next, Array.mem_toList_iff.mpr inCycles, mem_edgesFrom.mp edge⟩
  · rintro ⟨names, member, closed⟩
    exact cycle_kept _ names (fun other inNames => (closed other inNames).imp
      fun _ ⟨inNames, edge⟩ => ⟨inNames, mem_edgesFrom.mpr edge⟩) name member

/-- The parts that `assemble` gathers from the records of the visits are the parts of the visited
records, in the order of the visits. -/
private theorem parts_toList {α : Type} (walked : Walked)
    (part : {name : Name} → NodeRecord name → Array α) :
    ((reachedOf walked).flatMap (part ·.2)).toList =
      walked.visits.toList.flatMap fun visit =>
        match walked.request.records.get? visit.1 with
        | some record => (part record).toList
        | none => [] := by
  unfold reachedOf
  simp only [Array.toList_flatMap, Array.toList_map, Array.toList_attach, List.flatMap_map]
  have general : ∀ (visits : List (Name × Option Nat))
      (inside : ∀ visit ∈ visits, visit ∈ walked.visits),
      List.flatMap (fun visit : {visit // visit ∈ walked.visits} =>
          (part (walked.record visit.1 visit.2)).toList)
        (visits.attachWith (fun visit => visit ∈ walked.visits) inside) =
      List.flatMap (fun visit =>
          match walked.request.records.get? visit.1 with
          | some record => (part record).toList
          | none => []) visits := by
    intro visits
    induction visits with
    | nil => intro _; rfl
    | cons first rest ih =>
      intro inside
      simp only [List.attachWith_cons, List.flatMap_cons,
        get?_record walked first (inside first List.mem_cons_self)]
      rw [ih]
  exact general _ _

/-- The boundaries that `assemble` numbers are the boundaries of the visited records, in the order
of the visits. -/
private theorem boundaries_toList (walked : Walked) :
    ((reachedOf walked).flatMap (·.2.boundaries)).toList =
      visitedBoundaries walked.request.records walked.visits :=
  parts_toList walked (·.boundaries)

/-- The paths that `assemble` gathers are the paths of the visited records, in the order of the
visits. -/
private theorem paths_toList (walked : Walked) :
    ((reachedOf walked).flatMap (·.2.unresolved)).toList =
      visitedPaths walked.request.records walked.visits :=
  parts_toList walked (·.unresolved)

private theorem canonicalEdges_idempotent (edges : Array (Name × Name)) :
    RegulaPolicy.canonicalEdges (RegulaPolicy.canonicalEdges edges) =
      RegulaPolicy.canonicalEdges edges := by
  simp [RegulaPolicy.canonicalEdges]

private theorem channel_of (walked : Walked)
    (targets : {name : Name} → NodeRecord name → Array Name)
    {edges : Array (Name × Name)}
    (same : edges = RegulaPolicy.canonicalEdges (edgesFrom walked targets)) :
    ChannelOf walked.request.records walked.visits targets edges := by
  subst same
  exact ⟨canonicalEdges_idempotent _, fun edge => by
    rw [RegulaPolicy.mem_canonicalEdges, mem_edgesFrom]⟩

/-- **`assemble` gives the account of the root** (`AccountOf`): for each walk that returned its
visits, the account that `assemble` builds is the account that the visits and their records
give. -/
theorem assemble_account (rootCompiled : Bool) (walked : Walked) :
    AccountOf walked.request walked.visits rootCompiled (assemble rootCompiled walked) := by
  obtain ⟨unresolvedEq, requiredEq, unavailableEq⟩ := assemble_code rootCompiled walked
  obtain ⟨logical, candidate, history, current, active, helper⟩ :=
    assemble_channels rootCompiled walked
  obtain ⟨entries, sublist, members, messages, pathsEq, namesEq⟩ := codeStep_fold
    walked.request.records (requiredSet rootCompiled walked).toList (pathsOf walked) #[]
  generalize resultEq : (requiredSet rootCompiled walked).toList.foldl
    (codeStep walked.request.records) (pathsOf walked, #[]) = result at *
  have required : ∀ name, name ∈ entries.map (·.1) ↔
      Required walked.request walked.visits rootCompiled name ∧
        ¬ Available walked.request.records name := by
    intro name
    rw [members, Std.HashSet.mem_toList, mem_requiredSet]
  have distinct : (requiredSet rootCompiled walked).toList.Nodup :=
    List.Pairwise.imp (fun same => beq_eq_false_iff_ne.mp same) Std.HashSet.distinct_toList
  unfold AccountOf
  simp only
  refine ⟨⟨?_, ?_⟩, ?_, channel_of walked _ (assemble_compilerEdges rootCompiled walked),
    channel_of walked _ logical, channel_of walked _ candidate, channel_of walked _ history,
    channel_of walked _ current, channel_of walked _ active, channel_of walked _ helper,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  -- The nodes.
  · rw [assemble_nodes]
    exact RegulaPolicy.canonicalNames_idempotent _
  · intro name
    rw [assemble_nodes, RegulaPolicy.mem_canonicalNames]
    simp [Visited, Array.mem_map]
  -- The visits.
  · simp only [assemble_visits]
    refine ⟨by simp [reachedOf], fun index inVisits inClosure => ?_⟩
    refine ⟨by simp [reachedOf], by simp [reachedOf], fun record found => ?_⟩
    rw [get?_record walked _ (Array.getElem_mem inVisits)] at found
    cases Option.some.inj found
    simp [reachedOf]
  -- The code.
  · rw [requiredEq]
    exact RegulaPolicy.canonicalNames_idempotent _
  · intro name
    rw [requiredEq, RegulaPolicy.mem_canonicalNames, Std.HashSet.mem_toArray, mem_requiredSet]
  · rw [unavailableEq]
    exact RegulaPolicy.canonicalNames_idempotent _
  · intro name
    rw [unavailableEq, RegulaPolicy.mem_canonicalNames, ← Array.mem_toList_iff, namesEq,
      ← required]
    simp
  -- The unresolved paths.
  · refine ⟨cyclicReplacementPaths (edgesFrom walked (·.replacementTargets)), entries,
      cycles_nodup _, mem_cycles walked, sublist.nodup distinct, required, messages, ?_⟩
    rw [unresolvedEq, pathsEq]
    congr 1
    unfold pathsOf
    dsimp only
    by_cases empty : cyclicReplacementPaths (edgesFrom walked (·.replacementTargets)) = #[]
    · have notPushed :
          ¬ (!(cyclicReplacementPaths (edgesFrom walked (·.replacementTargets))).isEmpty) =
            true := by
        simp [empty]
      rw [ite_eq_right notPushed, ite_eq_left empty, List.append_nil, paths_toList]
    · have pushed :
          (!(cyclicReplacementPaths (edgesFrom walked (·.replacementTargets))).isEmpty) = true := by
        simpa [Array.isEmpty_iff] using empty
      rw [ite_eq_left pushed, ite_eq_right empty, Array.toList_push, paths_toList]
  -- The boundaries.
  · have sizeEq : ((reachedOf walked).flatMap (·.2.boundaries)).size =
        (visitedBoundaries walked.request.records walked.visits).length := by
      rw [← boundaries_toList, Array.length_toList]
    simp only [assemble_boundaries, Array.size_mapIdx]
    refine ⟨sizeEq, fun index inBoundaries inVisited => ?_⟩
    simp only [Array.getElem_mapIdx]
    have same : ((reachedOf walked).flatMap (·.2.boundaries))[index]'(by
          simpa using inBoundaries) =
        (visitedBoundaries walked.request.records walked.visits)[index] := by
      simp only [← boundaries_toList, Array.getElem_toList]
    refine ⟨trivial, by rw [same], fun caller => ?_⟩
    rw [Array.mem_filterMap]
    constructor
    · rintro ⟨⟨source, callee⟩, inEdges, chosen⟩
      simp only at chosen
      split at chosen
      · next named =>
        cases chosen
        rw [beq_iff_eq] at named
        exact mem_edgesFrom.mp (named ▸ inEdges)
      · cases chosen
    · intro visited
      exact ⟨(caller, _), mem_edgesFrom.mpr visited, by simp⟩

end RegulaPolicy.ExecutionWalk
