import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas
import RegulaPolicy.Domain
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
of queued names. `assemble` builds the account of the root from the records and the visits.

`walk_sound` and `walk_complete` state that the visits are exactly the names that the recorded
edges reach from the root (`Reach`), and `walk_nodup` that each name is visited one time.
`walk_ok` states that the bound of the steps is enough. `checked_walk` registers the kind
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

/-- What the observing pass records of one name that the walk reaches. The record holds the
targets of the edges from the name and not the edges, so each edge that `assemble` builds from a
record starts at the name of its visit. -/
structure NodeRecord where
  /-- The module that declares the name, when the environment attributes one. -/
  moduleName : Option Name := none
  /-- The names that the retained compiler body of this name calls. -/
  compilerDependencies : Array Name := #[]
  /-- The names that the logical value of this name uses. -/
  logicalTargets : Array Name := #[]
  /-- The targets of the simplification candidates of this name. -/
  candidateTargets : Array Name := #[]
  /-- The targets that the replacement history of this name records. -/
  historyTargets : Array Name := #[]
  /-- The current replacement target of this name. -/
  currentReplacementTargets : Array Name := #[]
  /-- The target of the active simplification of this name. -/
  activeSimplificationTargets : Array Name := #[]
  /-- The compiled recursion helper of this name. -/
  helperTargets : Array Name := #[]
  /-- The replacement targets of this name, for the search of replacement-only cycles. -/
  replacementTargets : Array Name := #[]
  /-- The boundaries at this name, each with the occurrence `0`. -/
  boundaries : Array RegulaPolicy.ExecutionBoundary := #[]
  /-- The paths at this name that the pass could not resolve. -/
  unresolved : Array String := #[]
  /-- The retained compiler body of this name. -/
  code : CodeStatus := .missing
  deriving Inhabited

/-- The names that the walk queues after the name of `record`, in the order of the queue: the
names that its retained compiler body calls, then the targets of its simplification candidates,
of its replacement history, of its current replacement, of its logical value and of its compiled
recursion helper. Each group is in the order of `canonicalNames`, so the visit order and the
parent of each visit are a function of the edge sets of the closure: a reader of the result
file derives them (`SharedExecution.walkLoop`). Each queued name is the target of an edge of the
record, by this definition (`mem_successors`). -/
def NodeRecord.successors (record : NodeRecord) : Array Name :=
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
def Follows (record : NodeRecord) (next : Name) : Prop :=
  next ∈ record.compilerDependencies ∨ next ∈ record.candidateTargets ∨
    next ∈ record.historyTargets ∨ next ∈ record.currentReplacementTargets ∨
    next ∈ record.logicalTargets ∨ next ∈ record.helperTargets

/-- The names that the walk queues after a record are the targets of the edges that it follows. -/
theorem mem_successors {record : NodeRecord} {next : Name} :
    next ∈ record.successors ↔ Follows record next := by
  simp only [NodeRecord.successors, Follows, Array.mem_append, RegulaPolicy.mem_canonicalNames,
    or_assoc]

/-- The records of the pass, by name. -/
abbrev Records := Std.HashMap Name NodeRecord

/-! ## The decision -/

/-- A recorded edge: `name` has a record, and the record follows an edge to `next`. -/
def Edge (records : Records) (name next : Name) : Prop :=
  ∃ record, records[name]? = some record ∧ Follows record next

/-- The names that the recorded edges reach from `root`, `root` among them. -/
inductive Reach (records : Records) (root : Name) : Name → Prop
  /-- The root. -/
  | root : Reach records root root
  /-- A name that a recorded edge reaches from a reached name. -/
  | step {name next : Name} : Reach records root name → Edge records name next →
      Reach records root next

/-- Why a walk returns no visits. -/
inductive WalkFailure where
  /-- The walk reached a name with no record. -/
  | unrecorded (name : Name)
  /-- The walk took more steps than its bound, which `walk_ok` excludes for records with each
  name that the walk reaches. -/
  | exhausted
  deriving Repr, DecidableEq

/-- The walk over the records: a stack of queued names, each with the position of the visit that
queued it. A step takes the name queued last. A name that was not visited is visited, and the
names that its record lists are queued in their order. `fuel` bounds the steps. -/
def walkLoop (records : Records) :
    Nat → List (Name × Option Nat) → Std.HashSet Name → Array (Name × Option Nat) →
      Except WalkFailure (Array (Name × Option Nat))
  | _, [], _, visits => .ok visits
  | 0, _ :: _, _, _ => .error .exhausted
  | fuel + 1, (name, parent) :: queued, visited, visits =>
    if visited.contains name then walkLoop records fuel queued visited visits
    else match records[name]? with
      | none => .error (.unrecorded name)
      | some record =>
        walkLoop records fuel
          (record.successors.foldl (fun queued next => (next, some visits.size) :: queued) queued)
          (visited.insert name) (visits.push (name, parent))

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

/-- The decision of the walk: the visits from the root over the records, each name with the
position of the visit that queued it, or the failure. -/
@[regula_decision]
def walk (request : WalkRequest) : Except WalkFailure (Array (Name × Option Nat)) :=
  walkLoop request.records (fuelOf request.records) [(request.root, none)] {} #[]

/-! ## What a walk returns -/

/-- The names that the walk queues after a visit: `queued` with each successor in front of it. -/
private theorem mem_foldl_queue {successors : Array Name} {position : Option Nat}
    {queued : List (Name × Option Nat)} {entry : Name × Option Nat} :
    entry ∈ successors.foldl (fun queued next => (next, position) :: queued) queued ↔
      (entry.1 ∈ successors ∧ entry.2 = position) ∨ entry ∈ queued := by
  rw [← Array.foldl_toList, ← Array.mem_toList_iff]
  generalize successors.toList = names
  induction names generalizing queued with
  | nil => simp
  | cons first rest step =>
    simp only [List.foldl_cons, step, List.mem_cons]
    constructor
    · rintro ((⟨member, same⟩) | (rfl | later))
      · exact .inl ⟨.inr member, same⟩
      · exact .inl ⟨.inl rfl, rfl⟩
      · exact .inr later
    · rintro (⟨(rfl | member), same⟩ | later)
      · exact .inr (.inl (by cases entry; simp_all))
      · exact .inl ⟨member, same⟩
      · exact .inr (.inr later)

/-- The walk queues one entry for each successor of a visit. -/
private theorem length_foldl_queue {successors : Array Name} {position : Option Nat}
    {queued : List (Name × Option Nat)} :
    (successors.foldl (fun queued next => (next, position) :: queued) queued).length =
      successors.size + queued.length := by
  rw [← Array.foldl_toList, ← Array.length_toList]
  generalize successors.toList = names
  induction names generalizing queued with
  | nil => simp
  | cons first rest step => simp only [List.foldl_cons, step, List.length_cons]; omega

/-- What the walk keeps from one step to the next. -/
private structure Inv (records : Records) (root : Name) (queue : List (Name × Option Nat))
    (visited : Std.HashSet Name) (visits : Array (Name × Option Nat)) : Prop where
  /-- The visited set holds the names of the visits. -/
  visited_iff : ∀ name, name ∈ visited ↔ ∃ visit ∈ visits, visit.1 = name
  /-- Each visit is reached. -/
  reached : ∀ visit ∈ visits, Reach records root visit.1
  /-- Each visit has a record. -/
  recorded : ∀ visit ∈ visits, ∃ record, records[visit.1]? = some record
  /-- Each queued name is reached. -/
  queued : ∀ entry ∈ queue, Reach records root entry.1
  /-- Each successor of a visit is visited or queued. -/
  closed : ∀ visit ∈ visits, ∀ next, Edge records visit.1 next →
    next ∈ visited ∨ ∃ entry ∈ queue, entry.1 = next
  /-- The root is visited or queued. -/
  rooted : root ∈ visited ∨ ∃ entry ∈ queue, entry.1 = root
  /-- No name is visited two times. -/
  nodup : (visits.toList.map Prod.fst).Nodup

/-- A step that takes a visited name keeps the invariant. -/
private theorem Inv.skip {records : Records} {root name : Name} {parent : Option Nat}
    {queued : List (Name × Option Nat)} {visited : Std.HashSet Name}
    {visits : Array (Name × Option Nat)}
    (inv : Inv records root ((name, parent) :: queued) visited visits)
    (seen : visited.contains name = true) : Inv records root queued visited visits := by
  have seenMem : name ∈ visited := Std.HashSet.mem_iff_contains.mpr seen
  refine ⟨inv.visited_iff, inv.reached, inv.recorded,
    fun e member => inv.queued e (List.mem_cons_of_mem _ member), ?_, ?_, inv.nodup⟩
  · intro visit member next edge
    rcases inv.closed visit member next edge with done | ⟨e, member', same⟩
    · exact .inl done
    · rcases List.mem_cons.mp member' with rfl | later
      · exact .inl (same ▸ seenMem)
      · exact .inr ⟨e, later, same⟩
  · rcases inv.rooted with done | ⟨e, member', same⟩
    · exact .inl done
    · rcases List.mem_cons.mp member' with rfl | later
      · exact .inl (same ▸ seenMem)
      · exact .inr ⟨e, later, same⟩

/-- A step that visits a name with a record keeps the invariant. -/
private theorem Inv.visit {records : Records} {root name : Name} {parent : Option Nat}
    {queued : List (Name × Option Nat)} {visited : Std.HashSet Name}
    {visits : Array (Name × Option Nat)} {record : NodeRecord}
    (inv : Inv records root ((name, parent) :: queued) visited visits)
    (unseen : visited.contains name = false) (found : records[name]? = some record) :
    Inv records root
      (record.successors.foldl (fun queued next => (next, some visits.size) :: queued) queued)
      (visited.insert name) (visits.push (name, parent)) := by
  have notVisited : name ∉ visited := fun mem =>
    by rw [Std.HashSet.mem_iff_contains.mp mem] at unseen; cases unseen
  have reachedName : Reach records root name := inv.queued (name, parent) (by simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [Std.HashSet.mem_insert, inv.visited_iff n]
    simp only [Array.mem_push, beq_iff_eq]
    constructor
    · rintro (rfl | ⟨v, member, same⟩)
      · exact ⟨(name, parent), .inr rfl, rfl⟩
      · exact ⟨v, .inl member, same⟩
    · rintro ⟨v, (member | rfl), same⟩
      · exact .inr ⟨v, member, same⟩
      · exact .inl same
  · intro v member
    rcases Array.mem_push.mp member with old | rfl
    · exact inv.reached v old
    · exact reachedName
  · intro v member
    rcases Array.mem_push.mp member with old | rfl
    · exact inv.recorded v old
    · exact ⟨record, found⟩
  · intro e member
    rcases mem_foldl_queue.mp member with ⟨listed, -⟩ | old
    · exact .step reachedName ⟨record, found, mem_successors.mp listed⟩
    · exact inv.queued e (List.mem_cons_of_mem _ old)
  · intro v member next edge
    rcases Array.mem_push.mp member with old | rfl
    · rcases inv.closed v old next edge with done | ⟨e, member', same⟩
      · exact .inl (Std.HashSet.mem_insert.mpr (.inr done))
      · rcases List.mem_cons.mp member' with rfl | later
        · exact .inl (Std.HashSet.mem_insert.mpr (.inl (by simpa using same)))
        · exact .inr ⟨e, mem_foldl_queue.mpr (.inr later), same⟩
    · obtain ⟨record', found', listed⟩ := edge
      rw [found] at found'
      cases found'
      exact .inr ⟨(next, some visits.size),
        mem_foldl_queue.mpr (.inl ⟨mem_successors.mpr listed, rfl⟩), rfl⟩
  · rcases inv.rooted with done | ⟨e, member', same⟩
    · exact .inl (Std.HashSet.mem_insert.mpr (.inr done))
    · rcases List.mem_cons.mp member' with rfl | later
      · exact .inl (Std.HashSet.mem_insert.mpr (.inl (by simpa using same)))
      · exact .inr ⟨e, mem_foldl_queue.mpr (.inr later), same⟩
  · rw [Array.toList_push, List.map_append, List.nodup_append]
    refine ⟨inv.nodup, by simp, ?_⟩
    intro a member b memberB
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at memberB
    subst memberB
    intro same
    subst same
    obtain ⟨v, vMember, vSame⟩ := List.mem_map.mp member
    exact notVisited ((inv.visited_iff _).mpr ⟨v, Array.mem_toList_iff.mp vMember, vSame⟩)

/-- The invariant of a walk, when it returns visits. -/
private theorem walkLoop_inv {records : Records} {root : Name} :
    ∀ (fuel : Nat) (queue : List (Name × Option Nat)) (visited : Std.HashSet Name)
      (visits result : Array (Name × Option Nat)),
      Inv records root queue visited visits →
      walkLoop records fuel queue visited visits = .ok result →
      ∃ visited', Inv records root [] visited' result := by
  intro fuel
  induction fuel with
  | zero =>
    intro queue visited visits result inv returned
    cases queue with
    | nil =>
      simp only [walkLoop, Except.ok.injEq] at returned
      exact ⟨visited, returned ▸ inv⟩
    | cons entry queued => simp [walkLoop] at returned
  | succ fuel step =>
    intro queue visited visits result inv returned
    cases queue with
    | nil =>
      simp only [walkLoop, Except.ok.injEq] at returned
      exact ⟨visited, returned ▸ inv⟩
    | cons entry queued =>
      obtain ⟨name, parent⟩ := entry
      by_cases seen : visited.contains name = true
      · simp only [walkLoop, seen, ↓reduceIte] at returned
        exact step queued visited visits result (Inv.skip inv seen) returned
      · have unseen : visited.contains name = false := by simpa using seen
        cases found : records[name]? with
        | none => simp [walkLoop, unseen, found] at returned
        | some record =>
          simp only [walkLoop, unseen, Bool.false_eq_true, ↓reduceIte, found] at returned
          exact step _ _ _ result (Inv.visit inv unseen found) returned

/-- The invariant at the start of a walk. -/
private theorem inv_start (records : Records) (root : Name) :
    Inv records root [(root, none)] {} #[] where
  visited_iff := by simp
  reached := by simp
  recorded := by simp
  queued := by simp [Reach.root]
  closed := by simp
  rooted := .inr ⟨(root, none), by simp, rfl⟩
  nodup := by simp

/-- **Each visit of an accepted walk is a name that the recorded edges reach from the root.** -/
theorem walk_sound {request : WalkRequest} {visits : Array (Name × Option Nat)}
    (accepted : walk request = .ok visits) :
    ∀ visit ∈ visits, Reach request.records request.root visit.1 := by
  obtain ⟨_, inv⟩ := walkLoop_inv _ _ _ _ _ (inv_start request.records request.root) accepted
  exact inv.reached

/-- **Each name that the recorded edges reach from the root is a visit of an accepted walk.** -/
theorem walk_complete {request : WalkRequest} {visits : Array (Name × Option Nat)}
    (accepted : walk request = .ok visits) :
    ∀ name, Reach request.records request.root name → ∃ visit ∈ visits, visit.1 = name := by
  obtain ⟨visited, inv⟩ :=
    walkLoop_inv _ _ _ _ _ (inv_start request.records request.root) accepted
  have closedVisited : ∀ name, Reach request.records request.root name → name ∈ visited := by
    intro name reach
    induction reach with
    | root => exact inv.rooted.resolve_right (by simp)
    | step _ edge known =>
      obtain ⟨visit, member, same⟩ := (inv.visited_iff _).mp known
      exact (inv.closed visit member _ (same ▸ edge)).resolve_right (by simp)
  exact fun name reach => (inv.visited_iff name).mp (closedVisited name reach)

/-- **An accepted walk visits each name one time.** -/
theorem walk_nodup {request : WalkRequest} {visits : Array (Name × Option Nat)}
    (accepted : walk request = .ok visits) : (visits.toList.map Prod.fst).Nodup := by
  obtain ⟨_, inv⟩ := walkLoop_inv _ _ _ _ _ (inv_start request.records request.root) accepted
  exact inv.nodup

/-- Each visit of an accepted walk has a record. -/
theorem walk_recorded {request : WalkRequest} {visits : Array (Name × Option Nat)}
    (accepted : walk request = .ok visits) :
    ∀ visit ∈ visits, ∃ record, request.records[visit.1]? = some record := by
  obtain ⟨_, inv⟩ := walkLoop_inv _ _ _ _ _ (inv_start request.records request.root) accepted
  exact inv.recorded

/-! ## The bound is enough -/

/-- The number of names that the records of `entries` list, for each entry whose name is not in
`visited`. -/
private def pendingIn (visited : Std.HashSet Name) : List (Name × NodeRecord) → Nat
  | [] => 0
  | entry :: rest =>
    (if visited.contains entry.1 then 0 else entry.2.successors.size) + pendingIn visited rest

/-- The visit of a name that no entry has leaves the count. -/
private theorem pendingIn_insert_absent {visited : Std.HashSet Name} {name : Name} :
    ∀ {entries : List (Name × NodeRecord)}, (∀ entry ∈ entries, entry.1 ≠ name) →
      pendingIn (visited.insert name) entries = pendingIn visited entries
  | [], _ => rfl
  | entry :: rest, absent => by
    have other : (name == entry.1) = false :=
      beq_false_of_ne fun same => absent entry List.mem_cons_self same.symm
    simp only [pendingIn, Std.HashSet.contains_insert, other, Bool.false_or,
      pendingIn_insert_absent (fun e member => absent e (List.mem_cons_of_mem _ member))]

/-- The visit of a name that is not visited takes the successors of its entry from the count. -/
private theorem pendingIn_insert_present {visited : Std.HashSet Name} {name : Name}
    {record : NodeRecord} (unseen : visited.contains name = false) :
    ∀ {entries : List (Name × NodeRecord)},
      entries.Pairwise (fun a b => (a.1 == b.1) = false) → (name, record) ∈ entries →
      pendingIn visited entries = pendingIn (visited.insert name) entries + record.successors.size
  | [], _, member => by simp at member
  | entry :: rest, distinct, member => by
    obtain ⟨apart, distinctRest⟩ := List.pairwise_cons.mp distinct
    rcases List.mem_cons.mp member with same | later
    · subst same
      have absent : ∀ e ∈ rest, e.1 ≠ name := fun e listed same => by
        have := apart e listed
        rw [same] at this
        simp at this
      simp only [pendingIn, unseen, Std.HashSet.contains_insert, beq_self_eq_true, Bool.true_or,
        Bool.false_eq_true, ↓reduceIte, pendingIn_insert_absent absent]
      omega
    · have other : (name == entry.1) = false :=
        beq_false_of_ne fun same => by
          have := apart _ later
          rw [same] at this
          simp at this
      simp only [pendingIn, Std.HashSet.contains_insert, other, Bool.false_or,
        pendingIn_insert_present unseen distinctRest later]
      omega

/-- The bound of a walk is one more than the count of all entries. -/
private theorem fuelOf_eq (records : Records) :
    fuelOf records = 1 + pendingIn {} records.toList := by
  unfold fuelOf
  rw [Std.HashMap.fold_eq_foldl_toList]
  suffices sums : ∀ (start : Nat) (entries : List (Name × NodeRecord)),
      entries.foldl (fun total entry => total + entry.2.successors.size) start =
        start + pendingIn {} entries from sums 1 _
  intro start entries
  induction entries generalizing start with
  | nil => simp [pendingIn]
  | cons entry rest step =>
    simp only [List.foldl_cons, step, pendingIn, Std.HashSet.contains_empty, Bool.false_eq_true,
      ↓reduceIte]
    omega

/-- A walk whose bound covers its queue and the count of the entries that are not visited
returns visits when each name that the recorded edges reach has a record. -/
private theorem walkLoop_ok {records : Records} {root : Name}
    (recorded : ∀ name, Reach records root name → ∃ record, records[name]? = some record) :
    ∀ (fuel : Nat) (queue : List (Name × Option Nat)) (visited : Std.HashSet Name)
      (visits : Array (Name × Option Nat)),
      Inv records root queue visited visits →
      queue.length + pendingIn visited records.toList ≤ fuel →
      ∃ result, walkLoop records fuel queue visited visits = .ok result := by
  intro fuel
  induction fuel with
  | zero =>
    intro queue visited visits _ bound
    cases queue with
    | nil => exact ⟨visits, by simp [walkLoop]⟩
    | cons entry queued => simp at bound
  | succ fuel step =>
    intro queue visited visits inv bound
    cases queue with
    | nil => exact ⟨visits, by simp [walkLoop]⟩
    | cons entry queued =>
      obtain ⟨name, parent⟩ := entry
      simp only [List.length_cons] at bound
      by_cases seen : visited.contains name = true
      · simp only [walkLoop, seen, ↓reduceIte]
        exact step queued visited visits (Inv.skip inv seen) (by omega)
      · have unseen : visited.contains name = false := by simpa using seen
        obtain ⟨record, found⟩ := recorded name (inv.queued (name, parent) (by simp))
        simp only [walkLoop, unseen, Bool.false_eq_true, ↓reduceIte, found]
        refine step _ _ _ (Inv.visit inv unseen found) ?_
        have present := pendingIn_insert_present unseen
          (Std.HashMap.distinct_keys_toList (m := records))
          (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr found)
        rw [length_foldl_queue]
        omega

/-- The walk has a record for each name that the recorded edges reach from the root. -/
def Recorded (request : WalkRequest) : Prop :=
  ∀ name, Reach request.records request.root name →
    ∃ record, request.records[name]? = some record

/-- **A walk returns visits when each name that the recorded edges reach has a record.** The
bound of the steps is enough. -/
theorem walk_ok {request : WalkRequest} (recorded : Recorded request) :
    ∃ visits, walk request = .ok visits :=
  walkLoop_ok recorded _ _ _ _ (inv_start request.records request.root) (by
    rw [fuelOf_eq, List.length_singleton]
    omega)

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
          obtain ⟨record, found⟩ := walk_recorded h visit member
          exact ⟨record, same ▸ found⟩
      · intro recorded
        obtain ⟨visits, h⟩ := walk_ok recorded
        simp [h, Except.isOk, Except.toBool])
    (by
      let records : Records := (∅ : Records).insert `root {}
      refine ⟨{ records, root := `root }, ?_⟩
      have found : records[`root]? = some {} := by simp [records]
      obtain ⟨more, fuel⟩ : ∃ more, fuelOf records = more + 1 :=
        ⟨pendingIn {} records.toList, by rw [fuelOf_eq]; omega⟩
      simp only [walk, fuel, walkLoop, Std.HashSet.contains_empty, Bool.false_eq_true,
        ↓reduceIte, found]
      cases more <;> rfl)
    ⟨{ records := ∅, root := `root }, by
      have fuel : fuelOf (∅ : Records) = 0 + 1 := by
        rw [fuelOf_eq, Std.HashMap.toList_empty]
        rfl
      simp only [walk, fuel, walkLoop, Std.HashSet.contains_empty, Bool.false_eq_true,
        ↓reduceIte, Std.HashMap.getElem?_empty]
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

/-- The account of a root from the records and the visits of the walk: the boundaries, the
unresolved paths, the compiler edges and the closure. `rootCompiled` says that the root itself
requires retained code. Each part is the parts of the visits' records in the order of the visits,
then the search of replacement-only cycles and the required code that is not available. -/
def assemble (root : Name) (rootCompiled : Bool) (records : Records)
    (visits : Array (Name × Option Nat)) :
    Array RegulaPolicy.ExecutionBoundary × Array String × Array (Name × Name) ×
      RegulaPolicy.ExecutionClosure := Id.run do
  let recordOf (name : Name) : NodeRecord := records.getD name {}
  let reached := visits.map fun (name, _) => recordOf name
  -- The edges from each visit to the targets that its record lists, in the order of the visits.
  let edgesOf (targets : NodeRecord → Array Name) : Array (Name × Name) :=
    (visits.zip reached).flatMap fun ((name, _), record) => (targets record).map (name, ·)
  let compilerEdges := edgesOf (·.compilerDependencies)
  let mut compiledNames : Std.HashSet Name := {}
  if rootCompiled then compiledNames := compiledNames.insert root
  for record in reached do
    for dependency in record.compilerDependencies do
      compiledNames := compiledNames.insert dependency
  let mut unresolved := reached.flatMap (·.unresolved)
  let cycles := cyclicReplacementPaths (edgesOf (·.replacementTargets))
  if !cycles.isEmpty then
    unresolved := unresolved.push s!"replacement-only cycle reachable from {cycles}"
  let mut unavailableCode : Array Name := #[]
  for name in compiledNames do
    match (recordOf name).code with
    | .function | .externBody => pure ()
    | .placeholder =>
        unavailableCode := unavailableCode.push name
        unresolved := unresolved.push s!"{name}: compiler body is an opaque export placeholder"
    | .missing =>
        unavailableCode := unavailableCode.push name
        unresolved := unresolved.push s!"{name}: compiled dependency body is unavailable"
  let boundaries := (reached.flatMap (·.boundaries)).mapIdx fun occurrence boundary =>
    { boundary with occurrence, compilerCallers := compilerEdges.filterMap fun (caller, callee) =>
        if callee == boundary.name then some caller else none }
  let closure : RegulaPolicy.ExecutionClosure := {
    nodes := RegulaPolicy.canonicalNames (visits.map (·.1))
    visits := (visits.zip reached).map fun ((name, parent), record) =>
      { name, moduleName := record.moduleName, parent }
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
