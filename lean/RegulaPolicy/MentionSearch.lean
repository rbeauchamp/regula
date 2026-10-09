module

public import Std.Data.DHashMap.Lemmas
public import Std.Data.HashSet.Lemmas
public import Regula.Contract
meta import Regula.Decision

/-! # The search of a mentioned constant

The pure decision of contract recognition and reach (RG1007): whether a constant that a term
mentions leads, through the constants that each constant mentions, to one of some target
constants, and by which route.

The collector (`Regula.Collect`) asks this question three times. Before it reduces a declared type
it asks whether `Regula.ExecutableContract` can be among the constants of the reduction
(`ContractScope.mayReach`). Before it reduces a registration's requirement it asks the same of
the three structures of a decision kind (`ContractScope.mayReachDecision`). For a decision
registration it asks whether the acceptance predicate or the specification mentions the
implementation, and by which constants (`mentionChain?`). Each question is an observing pass and
this decision. The pass reads, for each constant that the search may expand, the constants that
it mentions, as that question defines them (`References`). The decision (`search`) takes those
records, the constants of the term and the targets, and returns the route to the first target
that it takes from a stack of pushed constants, or `none`.

The type of a record is indexed by its constant, so the map of records holds a record only under
its own constant. A constant with no record is not expanded: the pass gives no record to a
constant that the question excludes or that the environment does not have.

`search_sound` states that a returned route starts at a constant of the term, ends at a target,
and follows one recorded mention between each two consecutive constants (`Route`).
`search_complete` states that the search returns a route when a constant of the term leads to a
target (`Leads`), so the bound of its steps is enough. `checked_search` registers the kind
`Regula.Decides` against `Found`.

**Not claimed.** That a record lists what its constant mentions, that a constant with no record
leads to no target in the environment, and that the reduction of a type introduces only constants
that its constants lead to, are the observing pass's and are stated in the guide. -/

@[expose] public section

namespace RegulaPolicy.MentionSearch
open Lean

/-- What the observing pass reads of the constant `name` that the search may expand: the
constants that it mentions, in the order the search pushes them. The type is indexed by the
constant, so the map of records (`Records`) holds the record of a constant only under that
constant. -/
structure References (name : Name) where
  /-- The constants that `name` mentions. -/
  mentioned : Array Name

/-- The records of the pass: the record of each constant that the search may expand, under that
constant. -/
abbrev Records := Std.DHashMap Name References

/-- What `search` reads: the records of the pass, the constants of the term in their order, and
the targets. -/
structure SearchRequest where
  /-- The records of the pass, by constant. -/
  records : Records
  /-- The constants that the term mentions. -/
  start : Array Name
  /-- The constants that the search looks for. -/
  targets : Array Name

/-! ## The relation -/

/-- A recorded mention: `name` has a record, and the record lists `next`. -/
def Mentions (records : Records) (name next : Name) : Prop :=
  ∃ record, records.get? name = some record ∧ next ∈ record.mentioned

/-- `name` leads to a target: it is a target, or it mentions a constant that leads to one. -/
inductive Leads (records : Records) (targets : Array Name) : Name → Prop
  /-- A target. -/
  | target {name : Name} : name ∈ targets → Leads records targets name
  /-- A constant with a recorded mention of a constant that leads to a target. -/
  | step {name next : Name} : Mentions records name next → Leads records targets next →
      Leads records targets name

/-- A constant that the term mentions leads to a target. -/
def Found (request : SearchRequest) : Prop :=
  ∃ name ∈ request.start, Leads request.records request.targets name

/-- `chain` is a route to `name`: its first constant is one that the term mentions, its last is
`name`, and each other constant has a recorded mention of the one after it. -/
inductive Route (records : Records) (start : Array Name) : Name → List Name → Prop
  /-- A constant that the term mentions. -/
  | start {name : Name} : name ∈ start → Route records start name [name]
  /-- A route with one more recorded mention. -/
  | step {name next : Name} {chain : List Name} : Route records start name chain →
      Mentions records name next → Route records start next (chain ++ [next])

/-! ## The decision -/

/-- Push `next` with its route in reverse order, `next` in front of `chain`, unless it is marked; a
pushed constant is marked. The route of `next` shares `chain`, the route of the constant that
pushes it, so the routes of the stack take one cell for each push. -/
def push (chain : List Name) (state : List (Name × List Name) × Std.HashSet Name)
    (next : Name) : List (Name × List Name) × Std.HashSet Name :=
  if state.2.contains next then state else ((next, next :: chain) :: state.1, state.2.insert next)

/-- The search over the records: a stack of pushed constants, each with its route in reverse
order. A step takes the constant pushed last. A target ends the search with its route, put in
order only then. Another constant with a record
pushes the constants that the record lists, in their order. `fuel` bounds the steps. -/
def searchLoop (records : Records) (targets : Array Name) :
    Nat → List (Name × List Name) → Std.HashSet Name → Option (Array Name)
  | _, [], _ => none
  | 0, _ :: _, _ => none
  | fuel + 1, (name, chain) :: stack, marked =>
    if targets.contains name then some chain.reverse.toArray
    else match records.get? name with
      | none => searchLoop records targets fuel stack marked
      | some record =>
        let pushed := record.mentioned.foldl (push chain) (stack, marked)
        searchLoop records targets fuel pushed.1 pushed.2

/-- The bound of the steps of a search: one more than the number of constants that the term and
all records list. A search pushes each constant one time. -/
def fuelOf (request : SearchRequest) : Nat :=
  request.records.fold (fun total _ record => total + record.mentioned.size)
    (request.start.size + 1)

/-- The decision of the search: the route to the first target that the search takes, or `none`
when no constant that the term mentions leads to a target. -/
@[regula_decision]
def search (request : SearchRequest) : Option (Array Name) :=
  let initial := request.start.foldl (push []) ([], {})
  searchLoop request.records request.targets (fuelOf request) initial.1 initial.2

/-! ## The pushes of one step -/

/-- What the pushes of `names` keep and add. -/
private theorem foldl_push {chain : List Name} :
    ∀ (names : List Name) (stack : List (Name × List Name)) (marked : Std.HashSet Name),
      (∀ entry ∈ stack, entry ∈ (names.foldl (push chain) (stack, marked)).1) ∧
      (∀ entry ∈ (names.foldl (push chain) (stack, marked)).1,
        entry ∈ stack ∨ (entry.1 ∈ names ∧ entry.2 = entry.1 :: chain)) ∧
      (∀ name, name ∈ (names.foldl (push chain) (stack, marked)).2 ↔ name ∈ marked ∨ name ∈ names) ∧
      (∀ name ∈ (names.foldl (push chain) (stack, marked)).2, name ∉ marked →
        ∃ entry ∈ (names.foldl (push chain) (stack, marked)).1, entry.1 = name)
  | [], stack, marked =>
    ⟨fun _ member => member, fun _ member => .inl member, fun _ => by simp,
      fun _ member unmarked => absurd member unmarked⟩
  | first :: rest, stack, marked => by
    simp only [List.foldl_cons]
    by_cases seen : marked.contains first = true
    · have kept : push chain (stack, marked) first = (stack, marked) := by simp [push, seen]
      rw [kept]
      obtain ⟨keeps, adds, marks, pushes⟩ := foldl_push rest stack marked
      refine ⟨keeps, fun entry member => ?_, fun name => ?_, pushes⟩
      · rcases adds entry member with old | ⟨listed, same⟩
        · exact .inl old
        · exact .inr ⟨List.mem_cons_of_mem _ listed, same⟩
      · rw [marks name, List.mem_cons]
        constructor
        · rintro (old | listed)
          · exact .inl old
          · exact .inr (.inr listed)
        · rintro (old | rfl | listed)
          · exact .inl old
          · exact .inl (Std.HashSet.mem_iff_contains.mpr seen)
          · exact .inr listed
    · have unseen : marked.contains first = false := by simpa using seen
      have added : push chain (stack, marked) first =
          ((first, first :: chain) :: stack, marked.insert first) := by simp [push, unseen]
      rw [added]
      obtain ⟨keeps, adds, marks, pushes⟩ :=
        foldl_push rest ((first, first :: chain) :: stack) (marked.insert first)
      refine ⟨fun entry member => keeps entry (List.mem_cons_of_mem _ member),
        fun entry member => ?_, fun name => ?_, fun name member unmarked => ?_⟩
      · rcases adds entry member with old | ⟨listed, same⟩
        · rcases List.mem_cons.mp old with rfl | old
          · exact .inr ⟨List.mem_cons_self, rfl⟩
          · exact .inl old
        · exact .inr ⟨List.mem_cons_of_mem _ listed, same⟩
      · rw [marks name, Std.HashSet.mem_insert, List.mem_cons]
        constructor
        · rintro ((same | old) | listed)
          · exact .inr (.inl (beq_iff_eq.mp same).symm)
          · exact .inl old
          · exact .inr (.inr listed)
        · rintro (old | rfl | listed)
          · exact .inl (.inr old)
          · exact .inl (.inl (by simp))
          · exact .inr listed
      · by_cases fresh : name ∈ marked.insert first
        · rcases Std.HashSet.mem_insert.mp fresh with same | old
          · have same : first = name := beq_iff_eq.mp same
            subst same
            exact ⟨(first, first :: chain), keeps _ List.mem_cons_self, rfl⟩
          · exact absurd old unmarked
        · exact pushes name member fresh

/-- The pushes of the constants that a record lists. -/
private theorem foldl_push_array {chain : List Name} (names : Array Name)
    (stack : List (Name × List Name)) (marked : Std.HashSet Name) :
    (∀ entry ∈ stack, entry ∈ (names.foldl (push chain) (stack, marked)).1) ∧
    (∀ entry ∈ (names.foldl (push chain) (stack, marked)).1,
      entry ∈ stack ∨ (entry.1 ∈ names ∧ entry.2 = entry.1 :: chain)) ∧
    (∀ name, name ∈ (names.foldl (push chain) (stack, marked)).2 ↔ name ∈ marked ∨ name ∈ names) ∧
    (∀ name ∈ (names.foldl (push chain) (stack, marked)).2, name ∉ marked →
      ∃ entry ∈ (names.foldl (push chain) (stack, marked)).1, entry.1 = name) := by
  rw [← Array.foldl_toList]
  obtain ⟨keeps, adds, marks, pushes⟩ := foldl_push (chain := chain) names.toList stack marked
  refine ⟨keeps, fun entry member => ?_, fun name => ?_, pushes⟩
  · simpa only [Array.mem_toList_iff] using adds entry member
  · simpa only [Array.mem_toList_iff] using marks name

/-! ## A returned route -/

/-- Each entry of the stack holds a route to its constant. -/
private def Routed (records : Records) (start : Array Name)
    (stack : List (Name × List Name)) : Prop :=
  ∀ entry ∈ stack, Route records start entry.1 entry.2.reverse

/-- A route found by the loop ends at a target. -/
private theorem searchLoop_route {records : Records} {targets start : Array Name} :
    ∀ (fuel : Nat) (stack : List (Name × List Name)) (marked : Std.HashSet Name)
      (chain : Array Name),
      Routed records start stack → searchLoop records targets fuel stack marked = some chain →
      ∃ name ∈ targets, Route records start name chain.toList := by
  intro fuel
  induction fuel with
  | zero =>
    intro stack marked chain _ returned
    cases stack <;> simp [searchLoop] at returned
  | succ fuel step =>
    intro stack marked chain routed returned
    cases stack with
    | nil => simp [searchLoop] at returned
    | cons entry stack =>
      obtain ⟨name, route⟩ := entry
      have here : Route records start name route.reverse := routed (name, route) List.mem_cons_self
      have rest : Routed records start stack :=
        fun entry member => routed entry (List.mem_cons_of_mem _ member)
      by_cases target : targets.contains name = true
      · simp only [searchLoop, target, ↓reduceIte, Option.some.injEq] at returned
        subst returned
        exact ⟨name, Array.contains_iff_mem.mp target, by simpa using here⟩
      · have other : targets.contains name = false := by simpa using target
        cases found : records.get? name with
        | none =>
          simp only [searchLoop, other, Bool.false_eq_true, ↓reduceIte, found] at returned
          exact step stack marked chain rest returned
        | some record =>
          simp only [searchLoop, other, Bool.false_eq_true, ↓reduceIte, found] at returned
          refine step _ _ chain (fun entry member => ?_) returned
          rcases (foldl_push_array record.mentioned stack marked).2.1 entry member with
            old | ⟨listed, same⟩
          · exact rest entry old
          · rw [same, List.reverse_cons]
            exact .step here ⟨record, found, listed⟩

/-- The routes of the first pushes start at a constant that the term mentions. -/
private theorem routed_initial (records : Records) (start : Array Name) :
    Routed records start (start.foldl (push []) ([], {})).1 := by
  intro entry member
  rcases (foldl_push_array (chain := []) start [] {}).2.1 entry member with old | ⟨listed, same⟩
  · simp at old
  · rw [same]
    exact .start listed

/-- A route to a constant that leads to a target starts at a constant that leads to one. -/
private theorem Route.found {records : Records} {start targets : Array Name} {name : Name}
    {chain : List Name} (route : Route records start name chain)
    (leads : Leads records targets name) : ∃ first ∈ start, Leads records targets first := by
  induction route with
  | start member => exact ⟨_, member, leads⟩
  | step _ mentions step => exact step (.step mentions leads)

/-- **A returned route starts at a constant that the term mentions, ends at a target, and follows
one recorded mention between each two consecutive constants.** -/
theorem search_sound {request : SearchRequest} {chain : Array Name}
    (returned : search request = some chain) :
    ∃ name ∈ request.targets, Route request.records request.start name chain.toList :=
  searchLoop_route _ _ _ chain (routed_initial request.records request.start) returned

/-- A search that returns a route has found a constant that leads to a target. -/
theorem found_of_search {request : SearchRequest} {chain : Array Name}
    (returned : search request = some chain) : Found request := by
  obtain ⟨name, target, route⟩ := search_sound returned
  exact route.found (.target target)

/-! ## No route -/

/-- What the search keeps from one step to the next, for a search that finds no target: each
constant of the term is marked, each pushed constant is marked, and a marked constant that is not
on the stack is not a target and has each constant that its record lists marked. -/
private structure Closed (request : SearchRequest) (stack : List (Name × List Name))
    (marked : Std.HashSet Name) : Prop where
  /-- Each constant that the term mentions is marked. -/
  start : ∀ name ∈ request.start, name ∈ marked
  /-- Each pushed constant is marked. -/
  pushed : ∀ entry ∈ stack, entry.1 ∈ marked
  /-- A marked constant off the stack is done. -/
  done : ∀ name ∈ marked, (∀ entry ∈ stack, entry.1 ≠ name) →
    name ∉ request.targets ∧ ∀ next, Mentions request.records name next → next ∈ marked

/-- The first pushes keep `Closed`. -/
private theorem closed_initial (request : SearchRequest) :
    Closed request (request.start.foldl (push []) ([], {})).1
      (request.start.foldl (push []) ([], {})).2 := by
  obtain ⟨-, adds, marks, pushes⟩ := foldl_push_array (chain := []) request.start [] {}
  refine ⟨fun name member => (marks name).mpr (.inr member), fun entry member => ?_,
    fun name member off => ?_⟩
  · rcases adds entry member with old | ⟨listed, -⟩
    · simp at old
    · exact (marks _).mpr (.inr listed)
  · obtain ⟨entry, pushed, same⟩ := pushes name member (by simp)
    exact absurd same (off entry pushed)

/-- The count of the constants that the records list, for each record of a constant that is not
marked. -/
private def pendingIn (marked : Std.HashSet Name) : List ((n : Name) × References n) → Nat
  | [] => 0
  | entry :: rest =>
    (if marked.contains entry.1 then 0 else entry.2.mentioned.size) + pendingIn marked rest

/-- The number of constants that the record of `name` lists, or `0` with no record. -/
private def weight (records : Records) (name : Name) : Nat :=
  ((records.get? name).map (·.mentioned.size)).getD 0

/-- The cost of a stack: one for each entry and the weight of its constant. -/
private def stackCost (records : Records) (stack : List (Name × List Name)) : Nat :=
  (stack.map fun entry => 1 + weight records entry.1).sum

/-- The marking of a constant that no entry has leaves the count. -/
private theorem pendingIn_insert_absent {marked : Std.HashSet Name} {name : Name} :
    ∀ {entries : List ((n : Name) × References n)}, (∀ entry ∈ entries, entry.1 ≠ name) →
      pendingIn (marked.insert name) entries = pendingIn marked entries
  | [], _ => rfl
  | entry :: rest, absent => by
    have other : (name == entry.1) = false :=
      beq_false_of_ne fun same => absent entry List.mem_cons_self same.symm
    simp only [pendingIn, Std.HashSet.contains_insert, other, Bool.false_or,
      pendingIn_insert_absent (fun e member => absent e (List.mem_cons_of_mem _ member))]

/-- The marking of a constant that is not marked takes the constants of its record from the
count. -/
private theorem pendingIn_insert_present {marked : Std.HashSet Name} {name : Name}
    {record : References name} (unmarked : marked.contains name = false) :
    ∀ {entries : List ((n : Name) × References n)},
      entries.Pairwise (fun a b => (a.1 == b.1) = false) → ⟨name, record⟩ ∈ entries →
      pendingIn marked entries = pendingIn (marked.insert name) entries + record.mentioned.size
  | [], _, member => by simp at member
  | entry :: rest, distinct, member => by
    obtain ⟨apart, distinctRest⟩ := List.pairwise_cons.mp distinct
    rcases List.mem_cons.mp member with same | later
    · subst same
      have absent : ∀ e ∈ rest, e.1 ≠ name := fun e listed same => by
        have := apart e listed
        rw [same] at this
        simp at this
      simp only [pendingIn, unmarked, Std.HashSet.contains_insert, beq_self_eq_true,
        Bool.true_or, Bool.false_eq_true, ↓reduceIte, pendingIn_insert_absent absent]
      omega
    · have other : (name == entry.1) = false :=
        beq_false_of_ne fun same => by
          have : (entry.1 == name) = false := apart _ later
          rw [same] at this
          simp at this
      simp only [pendingIn, Std.HashSet.contains_insert, other, Bool.false_or,
        pendingIn_insert_present unmarked distinctRest later]
      omega

/-- The marking of a constant that is not marked takes its weight from the count. -/
private theorem pendingIn_insert (records : Records) {marked : Std.HashSet Name} {name : Name}
    (unmarked : marked.contains name = false) :
    pendingIn marked records.toList =
      pendingIn (marked.insert name) records.toList + weight records name := by
  cases found : records.get? name with
  | none =>
    have absent : ∀ entry ∈ records.toList, entry.1 ≠ name := fun entry member same => by
      have listed := Std.DHashMap.mem_toList_iff_get?_eq_some.mp member
      have present : records.contains entry.1 = true := by
        rw [Std.DHashMap.contains_eq_isSome_get?, listed]
        rfl
      rw [same, Std.DHashMap.contains_eq_isSome_get?, found] at present
      cases present
    simp [weight, found, pendingIn_insert_absent absent]
  | some record =>
    have weighs : weight records name = record.mentioned.size := by simp [weight, found]
    rw [weighs]
    exact pendingIn_insert_present unmarked (Std.DHashMap.distinct_keys_toList (m := records))
      (Std.DHashMap.mem_toList_iff_get?_eq_some.mpr found)

/-- The pushes of `names` add at most one to the cost for each constant of `names`. -/
private theorem cost_foldl_push (records : Records) {chain : List Name} :
    ∀ (names : List Name) (stack : List (Name × List Name)) (marked : Std.HashSet Name),
      pendingIn (names.foldl (push chain) (stack, marked)).2 records.toList +
          stackCost records (names.foldl (push chain) (stack, marked)).1 ≤
        pendingIn marked records.toList + stackCost records stack + names.length
  | [], stack, marked => by simp
  | first :: rest, stack, marked => by
    simp only [List.foldl_cons, List.length_cons]
    by_cases seen : marked.contains first = true
    · have kept : push chain (stack, marked) first = (stack, marked) := by simp [push, seen]
      rw [kept]
      have := cost_foldl_push records (chain := chain) rest stack marked
      omega
    · have unseen : marked.contains first = false := by simpa using seen
      have added : push chain (stack, marked) first =
          ((first, first :: chain) :: stack, marked.insert first) := by simp [push, unseen]
      rw [added]
      have := cost_foldl_push records (chain := chain) rest ((first, first :: chain) :: stack)
        (marked.insert first)
      have taken := pendingIn_insert records unseen
      simp only [stackCost, List.map_cons, List.sum_cons] at this ⊢
      omega

/-- The bound of a search is one more than the count of the constants that the term and all
records list. -/
private theorem fuelOf_eq (request : SearchRequest) :
    fuelOf request = request.start.size + 1 + pendingIn {} request.records.toList := by
  unfold fuelOf
  rw [Std.DHashMap.fold_eq_foldl_toList]
  suffices sums : ∀ (initial : Nat) (entries : List ((n : Name) × References n)),
      entries.foldl (fun total entry => total + entry.2.mentioned.size) initial =
        initial + pendingIn {} entries from sums _ _
  intro initial entries
  induction entries generalizing initial with
  | nil => simp [pendingIn]
  | cons entry rest step =>
    simp only [List.foldl_cons, step, pendingIn, Std.HashSet.contains_empty, Bool.false_eq_true,
      ↓reduceIte]
    omega

/-- A constant that leads to a target is not marked when each marked constant is done. -/
private theorem not_leads {request : SearchRequest} {marked : Std.HashSet Name}
    (closed : Closed request [] marked) {name : Name}
    (leads : Leads request.records request.targets name) : name ∉ marked := by
  induction leads with
  | target member =>
    intro marks
    exact (closed.done _ marks (by simp)).1 member
  | step mentions _ step =>
    intro marks
    exact step ((closed.done _ marks (by simp)).2 _ mentions)

/-- A loop whose bound covers its count and that keeps `Closed` returns a route when a constant
that the term mentions leads to a target. -/
private theorem searchLoop_some {request : SearchRequest} (found : Found request) :
    ∀ (fuel : Nat) (stack : List (Name × List Name)) (marked : Std.HashSet Name),
      Closed request stack marked →
      pendingIn marked request.records.toList + stackCost request.records stack < fuel →
      (searchLoop request.records request.targets fuel stack marked).isSome := by
  obtain ⟨first, starts, leads⟩ := found
  intro fuel
  induction fuel with
  | zero => intro _ _ _ bound; omega
  | succ fuel step =>
    intro stack marked closed bound
    cases stack with
    | nil =>
      exact absurd (closed.start first starts) (not_leads closed leads)
    | cons entry stack =>
      obtain ⟨name, chain⟩ := entry
      by_cases target : request.targets.contains name = true
      · simp [searchLoop, Array.contains_iff_mem.mp target]
      · have other : request.targets.contains name = false := by simpa using target
        have outside : name ∉ request.targets := fun member =>
          by rw [Array.contains_iff_mem.mpr member] at other; cases other
        simp only [stackCost, List.map_cons, List.sum_cons] at bound
        cases found : request.records.get? name with
        | none =>
          simp only [searchLoop, other, Bool.false_eq_true, ↓reduceIte, found]
          refine step stack marked ⟨closed.start, fun entry member =>
            closed.pushed entry (List.mem_cons_of_mem _ member), fun n member off => ?_⟩ ?_
          · by_cases same : n = name
            · subst same
              exact ⟨outside, fun next ⟨record, has, _⟩ => by rw [found] at has; cases has⟩
            · exact closed.done n member (fun entry listed => by
                rcases List.mem_cons.mp listed with rfl | later
                · exact Ne.symm same
                · exact off entry later)
          · simp only [stackCost]
            omega
        | some record =>
          simp only [searchLoop, other, Bool.false_eq_true, ↓reduceIte, found]
          obtain ⟨keeps, adds, markIff, pushes⟩ :=
            foldl_push_array (chain := chain) record.mentioned stack marked
          have grows : ∀ n ∈ marked, n ∈ (record.mentioned.foldl (push chain) (stack, marked)).2 :=
            fun n member => (markIff n).mpr (.inl member)
          refine step _ _ ⟨fun n member => grows n (closed.start n member),
            fun entry member => ?_, fun n member off => ?_⟩ ?_
          · rcases adds entry member with old | ⟨listed, -⟩
            · exact grows _ (closed.pushed entry (List.mem_cons_of_mem _ old))
            · exact (markIff _).mpr (.inr listed)
          · have before : n ∈ marked := by
              by_cases fresh : n ∈ marked
              · exact fresh
              · obtain ⟨entry, pushed, same⟩ := pushes n member fresh
                exact absurd same (off entry pushed)
            by_cases same : n = name
            · subst same
              refine ⟨outside, fun next ⟨record', has, listed⟩ => by
                rw [found] at has
                cases has
                exact (markIff next).mpr (.inr listed)⟩
            · obtain ⟨notTarget, closes⟩ := closed.done n before (fun entry listed => by
                rcases List.mem_cons.mp listed with rfl | later
                · exact Ne.symm same
                · exact off entry (keeps entry later))
              exact ⟨notTarget, fun next mentions => grows next (closes next mentions)⟩
          · have cost := cost_foldl_push request.records (chain := chain)
              record.mentioned.toList stack marked
            rw [Array.foldl_toList, Array.length_toList] at cost
            simp only [stackCost] at cost ⊢
            have weighs : weight request.records name = record.mentioned.size := by
              simp [weight, found]
            omega

/-- **The search returns a route when a constant that the term mentions leads to a target.**
The bound of the steps is enough. -/
theorem search_complete {request : SearchRequest} (found : Found request) :
    (search request).isSome := by
  have bound := (cost_foldl_push request.records (chain := []) request.start.toList [] {})
  rw [Array.foldl_toList, Array.length_toList] at bound
  refine searchLoop_some found _ _ _ (closed_initial request) ?_
  rw [fuelOf_eq]
  simp only [stackCost, List.map_nil, List.sum_nil] at bound ⊢
  omega

/-- `search` decides `Found` exactly: it returns a route exactly when a constant that the term
mentions leads to a target (`found_of_search`, `search_complete`). It accepts a term that
mentions a target, and it refuses a term that mentions no constant. -/
theorem checked_search : Regula.ExecutableContract search
    (Regula.Decides (fun result => result.isSome = true) Found) :=
  ⟨Regula.Decides.of_iff
    (fun request => by
      constructor
      · intro accepted
        obtain ⟨chain, returned⟩ := Option.isSome_iff_exists.mp accepted
        exact found_of_search returned
      · exact search_complete)
    ⟨{ records := ∅, start := #[`target], targets := #[`target] },
      search_complete ⟨`target, by simp, .target (by simp)⟩⟩
    ⟨{ records := ∅, start := #[], targets := #[] }, fun accepted => by
      obtain ⟨chain, returned⟩ := Option.isSome_iff_exists.mp accepted
      obtain ⟨name, member, -⟩ := found_of_search returned
      simp at member⟩⟩

end RegulaPolicy.MentionSearch
