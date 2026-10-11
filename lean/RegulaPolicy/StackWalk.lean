module

public import Std.Data.HashSet.Lemmas

/-! # A stack walk over the successors of each node

The execution account of RG3001 and RG3002 is walked twice: by the producer, over the records of
its observing pass (`ExecutionWalk.walk`), and by the reader of a result file, over the successor
lists that it decodes from the shared edge sets (`Regula.SharedExecution.walk`). Both walks are
this definition (`walk`), at the node type and the successors of each: the names of the records,
and the indices of the decoded name table.

`walk` takes the successors of each node, or `none` for a node with no record, a bound of its
steps and a root. It returns the visits: each node that the successors reach from the root, one
time, in the order of a stack of queued nodes, each with the position of the visit that queued it.

`walk_sound` and `walk_complete` state that the visits are exactly the nodes that the successors
reach from the root (`Reach`), `walk_nodup` that each node is visited one time, and
`walk_recorded` that each visit has successors. `walk_ok` states that a walk returns visits when
each node that it reaches has successors and its bound is more than the number of successors of
all nodes (`Bounds`). `walk_agree` states that two walks over successors that a map of the nodes
carries one to the other return visits that the map carries one to the other, with the same
parents, whatever their bounds. The theorems hold for a node type with lawful equality and
hashing (`LawfulBEq`, `LawfulHashable`), a hypothesis of each one that reads the set of visited
nodes. -/

@[expose] public section

namespace RegulaPolicy.StackWalk

/-- Why a walk returns no visits. -/
inductive Failure (α : Type) where
  /-- The walk reached a node with no record. -/
  | unrecorded (node : α)
  /-- The walk took more steps than its bound, which `walk_ok` excludes for a bound that `Bounds`
  admits when each node that the walk reaches has a record. -/
  | exhausted
  deriving Repr, DecidableEq

/-- The walk over `successors`: a stack of queued nodes, each with the position of the visit that
queued it. A step takes the node queued last. A node that was not visited is visited, and its
successors are queued in their order. `fuel` bounds the steps. -/
def walkLoop {α : Type} [BEq α] [Hashable α] (successors : α → Option (Array α)) :
    Nat → List (α × Option Nat) → Std.HashSet α → Array (α × Option Nat) →
      Except (Failure α) (Array (α × Option Nat))
  | _, [], _, visits => .ok visits
  | 0, _ :: _, _, _ => .error .exhausted
  | fuel + 1, (node, parent) :: queued, visited, visits =>
    if visited.contains node then walkLoop successors fuel queued visited visits
    else match successors node with
      | none => .error (.unrecorded node)
      | some targets =>
        walkLoop successors fuel
          (targets.foldl (fun queued next => (next, some visits.size) :: queued) queued)
          (visited.insert node) (visits.push (node, parent))

/-- The walk from `root` over `successors`, in at most `fuel` steps: the visits, each node with the
position of the visit that queued it, or the failure. -/
def walk {α : Type} [BEq α] [Hashable α] (successors : α → Option (Array α)) (fuel : Nat)
    (root : α) : Except (Failure α) (Array (α × Option Nat)) :=
  walkLoop successors fuel [(root, none)] {} #[]

/-- The nodes that the successors reach from `root`, `root` among them. -/
inductive Reach {α : Type} (successors : α → Option (Array α)) (root : α) : α → Prop
  /-- The root. -/
  | root : Reach successors root root
  /-- A successor of a reached node. -/
  | step {node next : α} {targets : Array α} : Reach successors root node →
      successors node = some targets → next ∈ targets → Reach successors root next

/-- Each node that the successors reach from `root` has successors. -/
def Recorded {α : Type} (successors : α → Option (Array α)) (root : α) : Prop :=
  ∀ node, Reach successors root node → ∃ targets, successors node = some targets

/-- The number of successors of `node`, `0` for a node with no record. -/
def degree {α : Type} (successors : α → Option (Array α)) (node : α) : Nat :=
  ((successors node).map Array.size).getD 0

/-- `fuel` is more than the number of successors of all nodes: a list of distinct nodes holds
each node with a successor, and their successors number less than `fuel`. A walk queues the root
and the successors of each visit, so this bound is enough (`walk_ok`). -/
def Bounds {α : Type} (successors : α → Option (Array α)) (fuel : Nat) : Prop :=
  ∃ nodes : List α, nodes.Nodup ∧ (∀ node, degree successors node ≠ 0 → node ∈ nodes) ∧
    (nodes.map (degree successors)).sum < fuel

/-! ## What a walk returns -/

/-- The nodes that the walk queues after a visit: `queued` with each successor in front of it. -/
private theorem mem_foldl_queue {α : Type} {targets : Array α} {position : Option Nat}
    {queued : List (α × Option Nat)} {entry : α × Option Nat} :
    entry ∈ targets.foldl (fun queued next => (next, position) :: queued) queued ↔
      (entry.1 ∈ targets ∧ entry.2 = position) ∨ entry ∈ queued := by
  rw [← Array.foldl_toList, ← Array.mem_toList_iff]
  generalize targets.toList = nodes
  induction nodes generalizing queued with
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
private theorem length_foldl_queue {α : Type} {targets : Array α} {position : Option Nat}
    {queued : List (α × Option Nat)} :
    (targets.foldl (fun queued next => (next, position) :: queued) queued).length =
      targets.size + queued.length := by
  rw [← Array.foldl_toList, ← Array.length_toList]
  generalize targets.toList = nodes
  induction nodes generalizing queued with
  | nil => simp
  | cons first rest step => simp only [List.foldl_cons, step, List.length_cons]; omega

/-- What the walk keeps from one step to the next. -/
private structure Inv {α : Type} [BEq α] [Hashable α] (successors : α → Option (Array α))
    (root : α) (queue : List (α × Option Nat)) (visited : Std.HashSet α)
    (visits : Array (α × Option Nat)) : Prop where
  /-- The visited set holds the nodes of the visits. -/
  visited_iff : ∀ node, node ∈ visited ↔ ∃ visit ∈ visits, visit.1 = node
  /-- Each visit is reached. -/
  reached : ∀ visit ∈ visits, Reach successors root visit.1
  /-- Each visit has successors. -/
  recorded : ∀ visit ∈ visits, ∃ targets, successors visit.1 = some targets
  /-- Each queued node is reached. -/
  queued : ∀ entry ∈ queue, Reach successors root entry.1
  /-- Each successor of a visit is visited or queued. -/
  closed : ∀ visit ∈ visits, ∀ targets, successors visit.1 = some targets → ∀ next ∈ targets,
    next ∈ visited ∨ ∃ entry ∈ queue, entry.1 = next
  /-- The root is visited or queued. -/
  rooted : root ∈ visited ∨ ∃ entry ∈ queue, entry.1 = root
  /-- No node is visited two times. -/
  nodup : (visits.toList.map Prod.fst).Nodup

/-- A step that takes a visited node keeps the invariant. -/
private theorem Inv.skip {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {successors : α → Option (Array α)} {root node : α} {parent : Option Nat}
    {queued : List (α × Option Nat)} {visited : Std.HashSet α} {visits : Array (α × Option Nat)}
    (inv : Inv successors root ((node, parent) :: queued) visited visits)
    (seen : visited.contains node = true) : Inv successors root queued visited visits := by
  have seenMem : node ∈ visited := Std.HashSet.mem_iff_contains.mpr seen
  refine ⟨inv.visited_iff, inv.reached, inv.recorded,
    fun e member => inv.queued e (List.mem_cons_of_mem _ member), ?_, ?_, inv.nodup⟩
  · intro visit member targets found next listed
    rcases inv.closed visit member targets found next listed with done | ⟨e, member', same⟩
    · exact .inl done
    · rcases List.mem_cons.mp member' with rfl | later
      · exact .inl (same ▸ seenMem)
      · exact .inr ⟨e, later, same⟩
  · rcases inv.rooted with done | ⟨e, member', same⟩
    · exact .inl done
    · rcases List.mem_cons.mp member' with rfl | later
      · exact .inl (same ▸ seenMem)
      · exact .inr ⟨e, later, same⟩

/-- A step that visits a node with successors keeps the invariant. -/
private theorem Inv.visit {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {successors : α → Option (Array α)} {root node : α} {parent : Option Nat}
    {queued : List (α × Option Nat)} {visited : Std.HashSet α} {visits : Array (α × Option Nat)}
    {targets : Array α} (inv : Inv successors root ((node, parent) :: queued) visited visits)
    (unseen : visited.contains node = false) (found : successors node = some targets) :
    Inv successors root
      (targets.foldl (fun queued next => (next, some visits.size) :: queued) queued)
      (visited.insert node) (visits.push (node, parent)) := by
  have notVisited : node ∉ visited := fun mem =>
    by rw [Std.HashSet.mem_iff_contains.mp mem] at unseen; cases unseen
  have reachedNode : Reach successors root node := inv.queued (node, parent) (by simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [Std.HashSet.mem_insert, inv.visited_iff n]
    simp only [Array.mem_push, beq_iff_eq]
    constructor
    · rintro (rfl | ⟨v, member, same⟩)
      · exact ⟨(node, parent), .inr rfl, rfl⟩
      · exact ⟨v, .inl member, same⟩
    · rintro ⟨v, (member | rfl), same⟩
      · exact .inr ⟨v, member, same⟩
      · exact .inl same
  · intro v member
    rcases Array.mem_push.mp member with old | rfl
    · exact inv.reached v old
    · exact reachedNode
  · intro v member
    rcases Array.mem_push.mp member with old | rfl
    · exact inv.recorded v old
    · exact ⟨targets, found⟩
  · intro e member
    rcases mem_foldl_queue.mp member with ⟨listed, -⟩ | old
    · exact .step reachedNode found listed
    · exact inv.queued e (List.mem_cons_of_mem _ old)
  · intro v member targets' found' next listed
    rcases Array.mem_push.mp member with old | rfl
    · rcases inv.closed v old targets' found' next listed with done | ⟨e, member', same⟩
      · exact .inl (Std.HashSet.mem_insert.mpr (.inr done))
      · rcases List.mem_cons.mp member' with rfl | later
        · exact .inl (Std.HashSet.mem_insert.mpr (.inl (by simpa using same)))
        · exact .inr ⟨e, mem_foldl_queue.mpr (.inr later), same⟩
    · rw [found] at found'
      cases found'
      exact .inr ⟨(next, some visits.size), mem_foldl_queue.mpr (.inl ⟨listed, rfl⟩), rfl⟩
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
private theorem walkLoop_inv {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {successors : α → Option (Array α)} {root : α} :
    ∀ (fuel : Nat) (queue : List (α × Option Nat)) (visited : Std.HashSet α)
      (visits result : Array (α × Option Nat)),
      Inv successors root queue visited visits →
      walkLoop successors fuel queue visited visits = .ok result →
      ∃ visited', Inv successors root [] visited' result := by
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
      obtain ⟨node, parent⟩ := entry
      by_cases seen : visited.contains node = true
      · simp only [walkLoop, seen, ↓reduceIte] at returned
        exact step queued visited visits result (Inv.skip inv seen) returned
      · have unseen : visited.contains node = false := by simpa using seen
        cases found : successors node with
        | none => simp [walkLoop, unseen, found] at returned
        | some targets =>
          simp only [walkLoop, unseen, Bool.false_eq_true, ↓reduceIte, found] at returned
          exact step _ _ _ result (Inv.visit inv unseen found) returned

/-- The invariant at the start of a walk. -/
private theorem inv_start {α : Type} [BEq α] [Hashable α] (successors : α → Option (Array α))
    (root : α) : Inv successors root [(root, none)] {} #[] where
  visited_iff := by simp
  reached := by simp
  recorded := by simp
  queued := by simp [Reach.root]
  closed := by simp
  rooted := .inr ⟨(root, none), by simp, rfl⟩
  nodup := by simp

/-- **Each visit of an accepted walk is a node that the successors reach from the root.** -/
theorem walk_sound {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {successors : α → Option (Array α)} {fuel : Nat} {root : α}
    {visits : Array (α × Option Nat)} (accepted : walk successors fuel root = .ok visits) :
    ∀ visit ∈ visits, Reach successors root visit.1 := by
  obtain ⟨_, inv⟩ := walkLoop_inv _ _ _ _ _ (inv_start successors root) accepted
  exact inv.reached

/-- **Each node that the successors reach from the root is a visit of an accepted walk.** -/
theorem walk_complete {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {successors : α → Option (Array α)} {fuel : Nat} {root : α}
    {visits : Array (α × Option Nat)} (accepted : walk successors fuel root = .ok visits) :
    ∀ node, Reach successors root node → ∃ visit ∈ visits, visit.1 = node := by
  obtain ⟨visited, inv⟩ := walkLoop_inv _ _ _ _ _ (inv_start successors root) accepted
  have closedVisited : ∀ node, Reach successors root node → node ∈ visited := by
    intro node reach
    induction reach with
    | root => exact inv.rooted.resolve_right (by simp)
    | step _ found listed known =>
      obtain ⟨visit, member, same⟩ := (inv.visited_iff _).mp known
      exact (inv.closed visit member _ (same ▸ found) _ listed).resolve_right (by simp)
  exact fun node reach => (inv.visited_iff node).mp (closedVisited node reach)

/-- **An accepted walk visits each node one time.** -/
theorem walk_nodup {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {successors : α → Option (Array α)} {fuel : Nat} {root : α}
    {visits : Array (α × Option Nat)} (accepted : walk successors fuel root = .ok visits) :
    (visits.toList.map Prod.fst).Nodup := by
  obtain ⟨_, inv⟩ := walkLoop_inv _ _ _ _ _ (inv_start successors root) accepted
  exact inv.nodup

/-- Each visit of an accepted walk has successors. -/
theorem walk_recorded {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {successors : α → Option (Array α)} {fuel : Nat} {root : α}
    {visits : Array (α × Option Nat)} (accepted : walk successors fuel root = .ok visits) :
    ∀ visit ∈ visits, ∃ targets, successors visit.1 = some targets := by
  obtain ⟨_, inv⟩ := walkLoop_inv _ _ _ _ _ (inv_start successors root) accepted
  exact inv.recorded

/-! ## The bound is enough -/

/-- The number of successors of the nodes of `nodes` that are not in `visited`. -/
private def pendingIn {α : Type} [BEq α] [Hashable α] (successors : α → Option (Array α))
    (visited : Std.HashSet α) : List α → Nat
  | [] => 0
  | node :: rest =>
    (if visited.contains node then 0 else degree successors node) +
      pendingIn successors visited rest

/-- Before any visit, the count is the number of successors of all the nodes. -/
private theorem pendingIn_empty {α : Type} [BEq α] [Hashable α]
    (successors : α → Option (Array α)) :
    ∀ nodes : List α, pendingIn successors {} nodes = (nodes.map (degree successors)).sum
  | [] => rfl
  | node :: rest => by
    simp only [pendingIn, Std.HashSet.contains_empty, Bool.false_eq_true, ↓reduceIte,
      pendingIn_empty successors rest, List.map_cons, List.sum_cons]

/-- The visit of a node that `nodes` does not hold leaves the count. -/
private theorem pendingIn_insert_absent {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    [LawfulHashable α] {successors : α → Option (Array α)} {visited : Std.HashSet α}
    {node : α} : ∀ {nodes : List α}, node ∉ nodes →
      pendingIn successors (visited.insert node) nodes = pendingIn successors visited nodes
  | [], _ => rfl
  | first :: rest, absent => by
    have other : (node == first) = false :=
      beq_false_of_ne fun same => absent (same ▸ List.mem_cons_self)
    simp only [pendingIn, Std.HashSet.contains_insert, other, Bool.false_or,
      pendingIn_insert_absent (fun member => absent (List.mem_cons_of_mem _ member))]

/-- The visit of a node that is not visited takes its successors from the count. -/
private theorem pendingIn_insert {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    [LawfulHashable α] {successors : α → Option (Array α)} {visited : Std.HashSet α}
    {node : α} (unseen : visited.contains node = false) :
    ∀ {nodes : List α}, nodes.Nodup → (degree successors node ≠ 0 → node ∈ nodes) →
      pendingIn successors visited nodes =
        pendingIn successors (visited.insert node) nodes + degree successors node
  | [], _, covers => by
    have none : degree successors node = 0 := Classical.byContradiction fun nonzero =>
      List.not_mem_nil (covers nonzero)
    simp [pendingIn, none]
  | first :: rest, distinct, covers => by
    obtain ⟨apart, distinctRest⟩ := List.nodup_cons.mp distinct
    by_cases same : node = first
    · subst same
      simp only [pendingIn, unseen, Std.HashSet.contains_insert, beq_self_eq_true, Bool.true_or,
        Bool.false_eq_true, ↓reduceIte, pendingIn_insert_absent apart]
      omega
    · have other : (node == first) = false := beq_false_of_ne same
      have coversRest : degree successors node ≠ 0 → node ∈ rest := fun nonzero =>
        (List.mem_cons.mp (covers nonzero)).resolve_left same
      simp only [pendingIn, Std.HashSet.contains_insert, other, Bool.false_or,
        pendingIn_insert unseen distinctRest coversRest]
      omega

/-- A walk whose bound covers its queue and the count of the nodes that are not visited returns
visits when each node that the successors reach has successors. -/
private theorem walkLoop_ok {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {successors : α → Option (Array α)} {root : α} {nodes : List α} (distinct : nodes.Nodup)
    (covers : ∀ node, degree successors node ≠ 0 → node ∈ nodes)
    (recorded : Recorded successors root) :
    ∀ (fuel : Nat) (queue : List (α × Option Nat)) (visited : Std.HashSet α)
      (visits : Array (α × Option Nat)),
      Inv successors root queue visited visits →
      queue.length + pendingIn successors visited nodes ≤ fuel →
      ∃ result, walkLoop successors fuel queue visited visits = .ok result := by
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
      obtain ⟨node, parent⟩ := entry
      simp only [List.length_cons] at bound
      by_cases seen : visited.contains node = true
      · simp only [walkLoop, seen, ↓reduceIte]
        exact step queued visited visits (Inv.skip inv seen) (by omega)
      · have unseen : visited.contains node = false := by simpa using seen
        obtain ⟨targets, found⟩ := recorded node (inv.queued (node, parent) (by simp))
        simp only [walkLoop, unseen, Bool.false_eq_true, ↓reduceIte, found]
        refine step _ _ _ (Inv.visit inv unseen found) ?_
        have counted := pendingIn_insert unseen distinct (covers node)
        have size : degree successors node = targets.size := by simp [degree, found]
        rw [length_foldl_queue]
        omega

/-- **A walk returns visits when each node that it reaches has successors and its bound is more
than the number of successors of all nodes.** -/
theorem walk_ok {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {successors : α → Option (Array α)} {fuel : Nat} {root : α}
    (bounds : Bounds successors fuel) (recorded : Recorded successors root) :
    ∃ visits, walk successors fuel root = .ok visits := by
  obtain ⟨nodes, distinct, covers, below⟩ := bounds
  refine walkLoop_ok distinct covers recorded _ _ _ _ (inv_start successors root) ?_
  rw [pendingIn_empty, List.length_singleton]
  omega

/-! ## Two walks agree -/

/-- A walk that returns visits returns the same visits with a larger bound. -/
private theorem walkLoop_add {α : Type} [BEq α] [Hashable α]
    {successors : α → Option (Array α)} (more : Nat) :
    ∀ (fuel : Nat) (queue : List (α × Option Nat)) (visited : Std.HashSet α)
      (visits result : Array (α × Option Nat)),
      walkLoop successors fuel queue visited visits = .ok result →
      walkLoop successors (fuel + more) queue visited visits = .ok result := by
  intro fuel
  induction fuel with
  | zero =>
    intro queue visited visits result returned
    cases queue with
    | nil => simpa [walkLoop] using returned
    | cons entry queued => simp [walkLoop] at returned
  | succ fuel step =>
    intro queue visited visits result returned
    cases queue with
    | nil => simpa [walkLoop] using returned
    | cons entry queued =>
      obtain ⟨node, parent⟩ := entry
      rw [Nat.add_right_comm]
      by_cases seen : visited.contains node = true
      · simp only [walkLoop, seen, ↓reduceIte] at returned ⊢
        exact step _ _ _ _ returned
      · have unseen : visited.contains node = false := by simpa using seen
        cases found : successors node with
        | none => simp [walkLoop, unseen, found] at returned
        | some targets =>
          simp only [walkLoop, unseen, Bool.false_eq_true, ↓reduceIte, found] at returned ⊢
          exact step _ _ _ _ returned

/-- **Two accepted walks from one root over the same successors return the same visits**, whatever
their bounds. -/
theorem walk_fuel {α : Type} [BEq α] [Hashable α] {successors : α → Option (Array α)}
    {fuel fuel' : Nat} {root : α} {visits visits' : Array (α × Option Nat)}
    (accepted : walk successors fuel root = .ok visits)
    (accepted' : walk successors fuel' root = .ok visits') : visits = visits' := by
  rcases Nat.le_total fuel fuel' with below | above
  · have larger := walkLoop_add (fuel' - fuel) _ _ _ _ _ accepted
    rw [Nat.add_sub_cancel' below] at larger
    exact Except.ok.inj (larger.symm.trans accepted')
  · have larger := walkLoop_add (fuel - fuel') _ _ _ _ _ accepted'
    rw [Nat.add_sub_cancel' above] at larger
    exact Except.ok.inj (accepted.symm.trans larger)

/-- The queue of a visit, carried by a map of the nodes, is the queue of the image of the visit. -/
private theorem foldl_queue_map {α β : Type} (rename : α → β) {targets : Array α}
    {position : Option Nat} {queued : List (α × Option Nat)} :
    (targets.map rename).foldl (fun queued next => (next, position) :: queued)
        (queued.map (Prod.map rename id)) =
      (targets.foldl (fun queued next => (next, position) :: queued) queued).map
        (Prod.map rename id) := by
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_map]
  generalize targets.toList = nodes
  induction nodes generalizing queued with
  | nil => rfl
  | cons first rest step =>
    simp only [List.map_cons, List.foldl_cons]
    exact step (queued := (first, position) :: queued)

/-- A walk over successors that a map of the nodes carries to other successors is carried by the
map to the walk over the other successors, step for step. -/
private theorem walkLoop_map {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β] {successors : α → Option (Array α)}
    {successors' : β → Option (Array β)} {rename : α → β} {root : α}
    (injective : ∀ node node', Reach successors root node → Reach successors root node' →
      rename node = rename node' → node = node')
    (carried : ∀ node, Reach successors root node →
      successors' (rename node) = (successors node).map (·.map rename)) :
    ∀ (fuel : Nat) (queue : List (α × Option Nat)) (visited : Std.HashSet α)
      (visited' : Std.HashSet β) (visits result : Array (α × Option Nat)),
      (∀ entry ∈ queue, Reach successors root entry.1) →
      (∀ node, Reach successors root node → (rename node ∈ visited' ↔ node ∈ visited)) →
      walkLoop successors fuel queue visited visits = .ok result →
      walkLoop successors' fuel (queue.map (Prod.map rename id)) visited'
          (visits.map (Prod.map rename id)) = .ok (result.map (Prod.map rename id)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro queue visited visited' visits result _ _ returned
    cases queue with
    | nil =>
      simp only [walkLoop, Except.ok.injEq] at returned
      simp [walkLoop, returned]
    | cons entry queued => simp [walkLoop] at returned
  | succ fuel step =>
    intro queue visited visited' visits result queuedReached same returned
    cases queue with
    | nil =>
      simp only [walkLoop, Except.ok.injEq] at returned
      simp [walkLoop, returned]
    | cons entry queued =>
      obtain ⟨node, parent⟩ := entry
      have reached : Reach successors root node := queuedReached (node, parent) (by simp)
      have rest : ∀ entry ∈ queued, Reach successors root entry.1 :=
        fun entry member => queuedReached entry (List.mem_cons_of_mem _ member)
      simp only [List.map_cons, Prod.map_apply, id_eq]
      by_cases seen : visited.contains node = true
      · have seen' : visited'.contains (rename node) = true :=
          Std.HashSet.mem_iff_contains.mp ((same node reached).mpr
            (Std.HashSet.mem_iff_contains.mpr seen))
        simp only [walkLoop, seen, seen', ↓reduceIte] at returned ⊢
        exact step _ _ _ _ _ rest same returned
      · have unseen : visited.contains node = false := by simpa using seen
        have unseen' : visited'.contains (rename node) = false := by
          cases h : visited'.contains (rename node) with
          | false => rfl
          | true =>
            have := (same node reached).mp (Std.HashSet.mem_iff_contains.mpr h)
            rw [Std.HashSet.mem_iff_contains.mp this] at unseen
            cases unseen
        cases found : successors node with
        | none => simp [walkLoop, unseen, found] at returned
        | some targets =>
          have found' : successors' (rename node) = some (targets.map rename) := by
            rw [carried node reached, found, Option.map_some]
          simp only [walkLoop, unseen, unseen', Bool.false_eq_true, ↓reduceIte, found,
            found'] at returned ⊢
          rw [Array.size_map, foldl_queue_map,
            show (visits.map (Prod.map rename id)).push (rename node, parent) =
              (visits.push (node, parent)).map (Prod.map rename id) by simp]
          refine step _ _ _ _ _ ?_ ?_ returned
          · intro entry member
            rcases mem_foldl_queue.mp member with ⟨listed, -⟩ | old
            · exact .step reached found listed
            · exact rest entry old
          · intro other otherReached
            rw [Std.HashSet.mem_insert, Std.HashSet.mem_insert, beq_iff_eq, beq_iff_eq,
              same other otherReached]
            constructor
            · rintro (equal | member)
              · exact .inl (injective node other reached otherReached equal)
              · exact .inr member
            · rintro (rfl | member)
              · exact .inl rfl
              · exact .inr member

/-- **A walk over successors that a map of the nodes carries to other successors is carried to the
walk over those.** If the map is one-to-one on the nodes that the successors reach from the root,
and the successors of the image of each such node are the images of its successors, in their
order, then an accepted walk with the same bound from the image of the root returns the images of
the visits, with the same parents. -/
theorem walk_map {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β] {successors : α → Option (Array α)}
    {successors' : β → Option (Array β)} {rename : α → β} {fuel : Nat} {root : α}
    {visits : Array (α × Option Nat)}
    (injective : ∀ node node', Reach successors root node → Reach successors root node' →
      rename node = rename node' → node = node')
    (carried : ∀ node, Reach successors root node →
      successors' (rename node) = (successors node).map (·.map rename))
    (accepted : walk successors fuel root = .ok visits) :
    walk successors' fuel (rename root) = .ok (visits.map (Prod.map rename id)) := by
  simpa only [walk, List.map_cons, List.map_nil, Prod.map_apply, id_eq, Array.map_empty] using
    walkLoop_map injective carried fuel [(root, none)] {} {} #[] visits (by simp [Reach.root])
      (by simp) accepted

/-- **Two walks over successors that a map of the nodes carries one to the other agree.** If the
map is one-to-one on the nodes that the first successors reach from the root, and the successors
of the image of each such node are the images of its successors, in their order, then the visits
of the two walks, when both return visits, are the visits of the first carried by the map, with
the same parents, whatever the two bounds. -/
theorem walk_agree {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β] {successors : α → Option (Array α)}
    {successors' : β → Option (Array β)} {rename : α → β} {fuel fuel' : Nat} {root : α}
    {visits : Array (α × Option Nat)} {visits' : Array (β × Option Nat)}
    (injective : ∀ node node', Reach successors root node → Reach successors root node' →
      rename node = rename node' → node = node')
    (carried : ∀ node, Reach successors root node →
      successors' (rename node) = (successors node).map (·.map rename))
    (accepted : walk successors fuel root = .ok visits)
    (accepted' : walk successors' fuel' (rename root) = .ok visits') :
    visits' = visits.map (Prod.map rename id) :=
  walk_fuel accepted' (walk_map injective carried accepted)

end RegulaPolicy.StackWalk
