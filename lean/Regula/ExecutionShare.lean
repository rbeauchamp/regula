import Regula.Report
import Regula.SharedExecution
import RegulaPolicy.ExecutionWalk

/-! # Shared forms of execution accounts

The proposal a result writer offers `SharedExecution.internValue` for an `execution` member: the
shared form of an array of root accounts (`fitted`), with every reached name, edge and boundary
record of the environment once and one entry per root.

Nothing here is trusted or proved to be a correct encoding. `SharedExecution.internValue` keeps
the proposal only when the reader (`SharedExecution.restore?`) returns the logical value itself
from it, and otherwise writes the logical value as it is, so `SharedExecution.expand_intern` holds
whatever these functions return. What depends on them is only how small the written member is. A
root is written as an entry of constant size when the reader's derivation reproduces its account:
its visits are the walk over the environment's edges, its edges those leaving its reached names,
and its boundaries its visited names' records. The reader's walk is the collector's walk
(`RegulaPolicy.StackWalk.walk`), so for equal successor lists it gives the collector's visits and
parents (`walk_agree`). The collector (`Regula.Probe`) is written to produce accounts of that form,
which is unproved; a root whose account differs is written in full.

The typed accounts give the names and their indices. The members the reader copies into a
rebuilt account (a boundary's kind, correspondence, evidence and toolchain origin, a root's
module and unresolved paths) are taken from the logical value as they are, not encoded again, so
the reader returns them as the same values whether the logical value was built or parsed. -/
namespace Regula.ExecutionShare
open Lean RegulaPolicy
open Regula.SharedExecution (boundaryObject boundaryRecord closureObject field? rootObject
  visitObject)
open scoped Regula.Report

/-! ### The codecs build the reader's objects

Each object the logical document's codec writes is, by definition, the object the reader builds
from the same members: the same member names in the same order, so the same tree. -/

theorem visit_toJson (visit : ExecutionVisit) :
    toJson visit =
      visitObject (toJson visit.name) (toJson visit.moduleName) (toJson visit.parent) := rfl

theorem boundary_toJson (boundary : ExecutionBoundary) :
    toJson boundary =
      boundaryObject (toJson boundary.occurrence) (toJson boundary.name) (toJson boundary.module)
        (toJson boundary.boundary) (toJson boundary.correspondence) (toJson boundary.owned)
        (toJson boundary.replacement) (toJson boundary.evidence) (toJson boundary.terms?)
        (toJson boundary.compilerCallers) (toJson boundary.toolchainOrigin?) := rfl

theorem closure_toJson (closure : ExecutionClosure) :
    toJson closure =
      closureObject (toJson closure.nodes) (toJson closure.visits) (toJson closure.logicalEdges)
        (toJson closure.candidateEdges) (toJson closure.historyEdges)
        (toJson closure.currentReplacementEdges) (toJson closure.activeSimplificationEdges)
        (toJson closure.helperEdges) (toJson closure.requiredCode)
        (toJson closure.unavailableCode) := rfl

theorem root_toJson (root : ExecutionRoot) :
    toJson root =
      rootObject (toJson root.name) (toJson root.module) (toJson root.boundaries)
        (toJson root.unresolved) (toJson root.compilerEdges) (toJson root.closure) := rfl

/-! ### The proposal -/

/-- An index as a written account carries it. -/
private def number (index : Nat) : Json := SourceTexts.refJson index

/-- The member named `key` of a logical object as it is, `null` when it has none. -/
private def member (key : String) (value : Json) : Json := (field? key value).getD .null

/-- The edge channels of a written account: each member's name and the edges of a root it
shares. -/
def channels : List (String × (ExecutionRoot → Array (Name × Name))) := [
  ("compilerEdges", (·.compilerEdges)),
  ("logicalEdges", (·.closure.logicalEdges)),
  ("candidateEdges", (·.closure.candidateEdges)),
  ("historyEdges", (·.closure.historyEdges)),
  ("currentReplacementEdges", (·.closure.currentReplacementEdges)),
  ("activeSimplificationEdges", (·.closure.activeSimplificationEdges)),
  ("helperEdges", (·.closure.helperEdges))]

/-- The position of each element of `values`. -/
private def positions (values : Array Name) : Std.HashMap Name Nat :=
  (values.foldl (fun (found, place) value => (found.insert value place, place + 1))
    (({} : Std.HashMap Name Nat), 0)).1

/-- The shared part of a written account: the index of each name, and the members that hold the
names, modules, edges, boundary records and unavailable code of every root. -/
structure Tables where
  /-- The index of each name in the written `names`. -/
  index : Std.HashMap Name Nat
  /-- The members of the written account other than its roots. -/
  members : List (String × Json)

/-- The index of a name in the written `names`. -/
def Tables.node (tables : Tables) (name : Name) : Nat := tables.index.getD name 0

/-- The shared part for `roots`, whose accounts in the logical value are `accounts`, in the same
order. Names are listed in the order of `canonicalNames`, so an edge list ordered by index pairs
is in the order of `canonicalEdges`; each name's boundary records are those of the first root
that reaches it, in that root's order, with the members of that root's logical boundaries. -/
def tables (roots : Array ExecutionRoot) (accounts : Array Json) : Tables :=
  let seen := roots.foldl (init := ({} : Std.HashSet Name)) fun seen root =>
    let seen := seen.insert root.name
    let seen := root.closure.visits.foldl (fun seen visit => seen.insert visit.name) seen
    let seen := root.closure.nodes.foldl (fun seen name => seen.insert name) seen
    let seen := root.closure.requiredCode.foldl (fun seen name => seen.insert name) seen
    let seen := root.closure.unavailableCode.foldl (fun seen name => seen.insert name) seen
    let seen := root.boundaries.foldl (fun seen boundary => seen.insert boundary.name) seen
    channels.foldl (init := seen) fun seen (_, edges) =>
      (edges root).foldl (fun seen (source, target) => (seen.insert source).insert target) seen
  let names := canonicalNames seen.toArray
  let index := positions names
  let node (name : Name) : Nat := index.getD name 0
  let moduleOf := roots.foldl (init := ({} : Std.HashMap Name Name)) fun found root =>
    root.closure.visits.foldl (init := found) fun found visit =>
      match visit.moduleName with
      | some moduleName =>
          if found.contains visit.name then found else found.insert visit.name moduleName
      | none => found
  let moduleNames := canonicalNames
    (moduleOf.fold (fun (seen : Std.HashSet Name) _ moduleName => seen.insert moduleName)
      {}).toArray
  let moduleIndex := positions moduleNames
  let nameModules := names.map fun name =>
    match moduleOf.get? name with
    | some moduleName => number (moduleIndex.getD moduleName 0)
    | none => Json.null
  let channel (edges : ExecutionRoot → Array (Name × Name)) : Json :=
    let pairs := roots.foldl (init := ({} : Std.HashSet (Nat × Nat))) fun pairs root =>
      (edges root).foldl (fun pairs (source, target) => pairs.insert (node source, node target))
        pairs
    .arr <| (pairs.toArray.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)).map
      fun (source, target) => Json.arr #[number source, number target]
  let records := (roots.zip accounts).foldl (init := ({} : Std.HashMap Nat (Array Json)))
    fun found (root, account) =>
      let logical := (SharedExecution.array? (member "boundaries" account)).getD #[]
      let own := (root.boundaries.zip logical).foldl (init := ({} : Std.HashMap Nat (Array Json)))
        fun own (boundary, written) =>
          let slot := node boundary.name
          if found.contains slot then own
          else own.insert slot ((own.getD slot #[]).push (boundaryRecord (number slot)
            (member "name" written) (member "module" written) (member "boundary" written)
            (member "correspondence" written) (member "owned" written)
            (member "replacement" written) (member "evidence" written)
            (member "exact" written) (member "toolchainOrigin" written)))
      own.fold (fun found slot listed => found.insert slot listed) found
  let boundaries := (records.toArray.qsort fun a b => a.1 < b.1).flatMap (·.2)
  let unavailable := roots.foldl (init := ({} : Std.HashSet Nat)) fun found root =>
    root.closure.unavailableCode.foldl (fun found name => found.insert (node name)) found
  { index
    members := [("names", toJson names), ("modules", toJson moduleNames),
        ("nameModules", .arr nameModules)] ++
      channels.map (fun (key, edges) => (key, channel edges)) ++
      [("boundaries", .arr boundaries),
        ("unavailableCode",
          .arr ((unavailable.toArray.qsort fun a b => decide (a < b)).map number))] }

/-- The members every root entry has: its name's index, its module and unresolved paths as the
logical account `account` holds them, and whether the root itself requires code. -/
def entryMembers (tables : Tables) (root : ExecutionRoot) (account : Json) :
    List (String × Json) := [
  ("name", number (tables.node root.name)), ("module", member "module" account),
  ("unresolved", member "unresolved" account),
  ("requiresCode", toJson (root.closure.requiredCode.contains root.name))]

/-- A root entry from which the reader derives the whole account. -/
def derivedEntry (tables : Tables) (root : ExecutionRoot) (account : Json) : Json :=
  Json.mkObj (entryMembers tables root account)

/-- A root entry that holds the root's account as it is. -/
def explicitEntry (account : Json) : Json := Json.mkObj [("explicit", account)]

/-- The written account with the shared part `tables` and the root entries `entries`. -/
def sharedForm (tables : Tables) (entries : Array Json) : Json :=
  Json.mkObj (tables.members ++ [(SharedExecution.rootsKey, .arr entries)])

/-- The roots a logical `execution` value lists and their accounts in it, when it is an array of
root accounts; an environment without roots is the empty array. -/
private def roots? (value : Json) : Option (Array ExecutionRoot × Array Json) :=
  match (fromJson? value : Except String (Array ExecutionRoot)), SharedExecution.array? value with
  | .ok roots, some accounts => if roots.size == accounts.size then some (roots, accounts) else none
  | _, _ => none

/-- The shared form in which each root has the smallest entry from which the reader rebuilds its
account: derived, else explicit. `value` itself when it is not an array of root accounts. -/
def fitted (value : Json) : Json :=
  match roots? value with
  | some (roots, accounts) =>
      let tables := tables roots accounts
      match SharedExecution.graphOf? (sharedForm tables #[]) with
      | some graph =>
          let fits (entry account : Json) : Bool :=
            match SharedExecution.rebuildRoot graph entry with
            | some rebuilt => SharedExecution.same rebuilt account
            | none => false
          sharedForm tables <| (roots.zip accounts).map fun (root, account) =>
            let entry := derivedEntry tables root account
            if fits entry account then entry else explicitEntry account
      | none => value
  | none => value

/-- The proposals of a result writer: `fitted` alone. -/
def proposals : List (Json → Json) := [fitted]

/-! ### The forms a writer gives a value

`fitted` writes a root's derived entry when the reader rebuilds from it a value `same` as the
root's logical account, a test that compares object trees node for node. A document read back from
its file has its object trees in the shape the parser builds, which can differ from the shape of
the document the writer was given, so the derived entry of a root can rebuild the read account
where the writer wrote an explicit one. `sharedAs` is the shared form with the kind of each entry
given, and `formLike` is the form a writer gives a value with the entry kinds of a written value:
`formLike_internValue` and `formLike_sharedAs` state that it returns each writer's own form. -/

/-- The shared form of `value` with the root entry at each position explicit where `explicit`
holds of the position, and derived elsewhere; `value` itself where `fitted` writes it as it is. -/
def sharedAs (explicit : Nat → Bool) (value : Json) : Json :=
  match roots? value with
  | some (roots, accounts) =>
      let tables := tables roots accounts
      match SharedExecution.graphOf? (sharedForm tables #[]) with
      | some _ =>
          sharedForm tables <| (roots.zip accounts).mapIdx fun position (root, account) =>
            if explicit position then explicitEntry account else derivedEntry tables root account
      | none => value
  | none => value

/-- The root entries of a written execution value: its `roots` member, when that is an array. -/
def rootEntries? (written : Json) : Option (Array Json) :=
  match written.getObjVal? SharedExecution.rootsKey with
  | .ok (.arr entries) => some entries
  | _ => none

/-- Whether a root entry is explicit: it has an `explicit` member. -/
def isExplicit (entry : Json) : Bool := (entry.getObjVal? "explicit").toBool

/-- Whether the root entry at `position` of `entries` is explicit. -/
def explicitAt (entries : Array Json) (position : Nat) : Bool :=
  isExplicit (entries.getD position .null)

/-- The written value a result writer gives the logical execution value `value` with the entry
kinds of the written value `written`: the writer's form with `sharedAs` at the kinds of
`written`'s root entries in place of `fitted`, and the writer's own form (`proposals`) when
`written` has no root entries. -/
def formLike (written value : Json) : Json :=
  match rootEntries? written with
  | some entries => SharedExecution.internValue [sharedAs (explicitAt entries)] value
  | none => SharedExecution.internValue proposals value

/-- The last member of an object built from a list is found by its name. -/
theorem getObjVal?_mkObj_last (members : List (String × Json)) (key : String) (value : Json) :
    (Json.mkObj (members ++ [(key, value)])).getObjVal? key = .ok value := by
  have found :
      (Std.TreeMap.Raw.ofList (members ++ [(key, value)]) compare)[key]? = some value := by
    rw [Std.TreeMap.Raw.ofList_eq_insertMany_empty,
      Std.TreeMap.Raw.getElem?_insertMany_list Std.TreeMap.Raw.WF.emptyc]
    simp
  simp only [Json.mkObj, Json.getObjVal?]
  rw [Std.TreeMap.Raw.get?_eq_getElem?, found]
  rfl

/-- A name that no member of the list has is not found in the object built from it. -/
theorem getObjVal?_mkObj_absent (members : List (String × Json)) (key : String)
    (absent : (members.map Prod.fst).contains key = false) :
    ((Json.mkObj members).getObjVal? key).toBool = false := by
  have found : (Std.TreeMap.Raw.ofList members compare)[key]? = none :=
    Std.TreeMap.Raw.getElem?_ofList_of_contains_eq_false absent
  simp only [Json.mkObj, Json.getObjVal?]
  rw [Std.TreeMap.Raw.get?_eq_getElem?, found]
  rfl

theorem rootEntries?_sharedForm (tables : Tables) (entries : Array Json) :
    rootEntries? (sharedForm tables entries) = some entries := by
  simp only [rootEntries?, sharedForm, getObjVal?_mkObj_last]

theorem isExplicit_explicitEntry (account : Json) : isExplicit (explicitEntry account) = true := by
  simp only [isExplicit, explicitEntry]
  rw [show [("explicit", account)] = ([] : List (String × Json)) ++ [("explicit", account)]
    from rfl, getObjVal?_mkObj_last]
  rfl

theorem isExplicit_derivedEntry (tables : Tables) (root : ExecutionRoot) (account : Json) :
    isExplicit (derivedEntry tables root account) = false :=
  getObjVal?_mkObj_absent _ _ (by simp only [entryMembers, List.map]; decide)

/-- No written value with root entries is a `verbatim` one. -/
theorem rootEntries?_verbatim (value : Json) :
    rootEntries? (SharedExecution.verbatim value) = none := by
  unfold rootEntries?
  split
  · next entries found =>
    simp only [SharedExecution.verbatim, Json.getObjVal?] at found
    split at found
    · next member present =>
      have := JsonAgreement.mem_of_get? present
      simp [SharedExecution.rootsKey, SharedExecution.verbatimKey] at this
    · cases found
  · rfl

/-- A value that `roots?` reads root accounts from is an array. -/
private theorem roots?_arr {value : Json} {found : Array ExecutionRoot × Array Json}
    (listed : roots? value = some found) : ∃ elems, value = .arr elems := by
  unfold roots? at listed
  split at listed
  · cases value <;> simp_all [SharedExecution.array?]
  · cases listed

/-- The entries `sharedAs` writes at any kinds are written again from their own kinds. -/
private theorem mapIdx_explicitAt (tables : Tables) (pairs : Array (ExecutionRoot × Json))
    (explicit : Nat → ExecutionRoot × Json → Bool) :
    (pairs.mapIdx fun position (root, account) =>
      if explicitAt (pairs.mapIdx fun position pair =>
          if explicit position pair then explicitEntry pair.2
          else derivedEntry tables pair.1 pair.2)
          position then explicitEntry account
      else derivedEntry tables root account) =
    pairs.mapIdx fun position pair =>
      if explicit position pair then explicitEntry pair.2
      else derivedEntry tables pair.1 pair.2 := by
  apply Array.ext
  · simp
  · intro position inside _
    have inPairs : position < pairs.size := by simpa using inside
    have kind : explicitAt (pairs.mapIdx fun position pair =>
          if explicit position pair then explicitEntry pair.2
          else derivedEntry tables pair.1 pair.2)
          position = explicit position pairs[position] := by
      simp only [explicitAt, Array.getD_eq_getD_getElem?, Array.getElem?_mapIdx,
        Array.getElem?_eq_getElem inPairs, Option.map_some, Option.getD_some]
      split
      · next yes => rw [yes, isExplicit_explicitEntry]
      · next no => rw [Bool.not_eq_true] at no; rw [no, isExplicit_derivedEntry]
    simp only [Array.getElem_mapIdx, kind]

/-- `sharedAs` at the kinds of the entries it wrote writes the same value. -/
theorem sharedAs_explicitAt {explicit : Nat → Bool} {value : Json} {entries : Array Json}
    (found : rootEntries? (sharedAs explicit value) = some entries) :
    sharedAs (explicitAt entries) value = sharedAs explicit value := by
  rcases listed : roots? value with _ | ⟨roots, accounts⟩
  · simp [sharedAs, listed]
  · rcases decoded : SharedExecution.graphOf? (sharedForm (tables roots accounts) #[]) with
      _ | graph
    · simp [sharedAs, listed, decoded]
    · simp only [sharedAs, listed, decoded] at found ⊢
      rw [rootEntries?_sharedForm] at found
      cases found
      exact congrArg _ (mapIdx_explicitAt _ (roots.zip accounts) fun position _ =>
        explicit position)

/-- `sharedAs` at the kinds of the entries `fitted` wrote writes `fitted`'s value. -/
theorem sharedAs_fitted {value : Json} {entries : Array Json}
    (found : rootEntries? (fitted value) = some entries) :
    sharedAs (explicitAt entries) value = fitted value := by
  rcases listed : roots? value with _ | ⟨roots, accounts⟩
  · simp [sharedAs, fitted, listed]
  · rcases decoded : SharedExecution.graphOf? (sharedForm (tables roots accounts) #[]) with
      _ | graph
    · simp [sharedAs, fitted, listed, decoded]
    · simp only [sharedAs, fitted, listed, decoded] at found ⊢
      rw [rootEntries?_sharedForm] at found
      cases found
      let fits (pair : ExecutionRoot × Json) : Bool :=
        match SharedExecution.rebuildRoot graph (derivedEntry (tables roots accounts) pair.1 pair.2)
          with
        | some rebuilt => SharedExecution.same rebuilt pair.2
        | none => false
      have asIdx : ((roots.zip accounts).map fun (root, account) =>
          if (match SharedExecution.rebuildRoot graph (derivedEntry (tables roots accounts) root
              account) with
            | some rebuilt => SharedExecution.same rebuilt account
            | none => false) = true then derivedEntry (tables roots accounts) root account
          else explicitEntry account) =
          (roots.zip accounts).mapIdx fun _ pair =>
            if !fits pair then explicitEntry pair.2
            else derivedEntry (tables roots accounts) pair.1 pair.2 := by
        apply Array.ext
        · simp
        · intro position _ _
          simp only [Array.getElem_map, Array.getElem_mapIdx, fits]
          have flip : ∀ (kept : Bool) (derived explicit : Json),
              (if kept = true then derived else explicit) =
                if (!kept) = true then explicit else derived := by
            intro kept _ _; cases kept <;> rfl
          exact flip _ _ _
      rw [asIdx]
      exact congrArg _ (mapIdx_explicitAt _ (roots.zip accounts) fun _ pair => !fits pair)

/-- Where `sharedAs` writes the value as it is, so does `fitted`, and so does `sharedAs` at every
kind. -/
theorem sharedAs_self {explicit : Nat → Bool} {value : Json}
    (kept : sharedAs explicit value = value) :
    fitted value = value ∧ ∀ other, sharedAs other value = value := by
  rcases listed : roots? value with _ | ⟨roots, accounts⟩
  · exact ⟨by simp [fitted, listed], fun _ => by simp [sharedAs, listed]⟩
  · rcases decoded : SharedExecution.graphOf? (sharedForm (tables roots accounts) #[]) with
      _ | graph
    · exact ⟨by simp [fitted, listed, decoded], fun _ => by simp [sharedAs, listed, decoded]⟩
    · exfalso
      simp only [sharedAs, listed, decoded] at kept
      obtain ⟨elems, rfl⟩ := roots?_arr listed
      simp [sharedForm, Json.mkObj] at kept

/-- Where `fitted` writes the value as it is, so does `sharedAs`, at every kind. -/
theorem fitted_self {value : Json} (kept : fitted value = value) (explicit : Nat → Bool) :
    sharedAs explicit value = value := by
  rcases listed : roots? value with _ | ⟨roots, accounts⟩
  · simp [sharedAs, listed]
  · rcases decoded : SharedExecution.graphOf? (sharedForm (tables roots accounts) #[]) with
      _ | graph
    · simp [sharedAs, listed, decoded]
    · exfalso
      simp only [fitted, listed, decoded] at kept
      obtain ⟨elems, rfl⟩ := roots?_arr listed
      simp [sharedForm, Json.mkObj] at kept

/-- The writer's form of a value is decided by what its one proposal writes for that value. -/
theorem internValue_congr {propose other : Json → Json} {value : Json}
    (agree : propose value = other value) :
    SharedExecution.internValue [propose] value = SharedExecution.internValue [other] value := by
  simp [SharedExecution.internValue, SharedExecution.firstRecovered, agree]

/-- An array has no root entries. -/
theorem rootEntries?_arr (elems : Array Json) : rootEntries? (.arr elems) = none := rfl

/-- **`formLike` returns the result writers' form.** For every logical execution value, the form
`formLike` gives it with the entry kinds of the writers' written form is that written form. -/
theorem formLike_internValue (value : Json) :
    formLike (SharedExecution.internValue proposals value) value =
      SharedExecution.internValue proposals value := by
  unfold formLike
  split
  · next entries found =>
    show SharedExecution.internValue [sharedAs (explicitAt entries)] value =
      SharedExecution.internValue [fitted] value
    by_cases kept : fitted value = value
    · exact internValue_congr ((fitted_self kept _).trans kept.symm)
    · apply internValue_congr
      by_cases recovered : SharedExecution.recovers (fitted value) value = true
      · have written : SharedExecution.internValue proposals value = fitted value := by
          simp [proposals, SharedExecution.internValue, SharedExecution.firstRecovered, recovered]
        rw [written] at found
        exact sharedAs_fitted found
      · exfalso
        have written : SharedExecution.internValue proposals value =
            if SharedExecution.recovers value value then value
            else SharedExecution.verbatim value := by
          simp [proposals, SharedExecution.internValue, SharedExecution.firstRecovered, recovered]
        rw [written] at found
        split at found
        · rcases listed : roots? value with _ | ⟨roots, accounts⟩
          · exact kept (by simp [fitted, listed])
          · obtain ⟨elems, rfl⟩ := roots?_arr listed
            rw [rootEntries?_arr] at found
            cases found
        · rw [rootEntries?_verbatim] at found
          cases found
  · rfl

/-- **`formLike` returns the form at every entry kinds whose shared form the reader takes back.**
For every logical execution value and every choice of explicit positions under which `sharedAs`
writes the value as it is or the reader returns the value from it, the form `formLike` gives the
value with the entry kinds of the form written with that choice is that form. -/
theorem formLike_sharedAs {explicit : Nat → Bool} {value : Json}
    (restores : sharedAs explicit value = value ∨
      SharedExecution.recovers (sharedAs explicit value) value = true) :
    formLike (SharedExecution.internValue [sharedAs explicit] value) value =
      SharedExecution.internValue [sharedAs explicit] value := by
  by_cases kept : sharedAs explicit value = value
  · obtain ⟨fittedKept, others⟩ := sharedAs_self kept
    unfold formLike
    split
    · exact internValue_congr ((others _).trans kept.symm)
    · exact internValue_congr (fittedKept.trans kept.symm)
  · have recovered := restores.resolve_left kept
    have written : SharedExecution.internValue [sharedAs explicit] value =
        sharedAs explicit value := by
      simp [SharedExecution.internValue, SharedExecution.firstRecovered, recovered]
    rw [written]
    unfold formLike
    split
    · next entries found =>
      rw [internValue_congr (sharedAs_explicitAt found)]
      simp [SharedExecution.internValue, SharedExecution.firstRecovered, recovered]
    · next absent =>
      exfalso
      rcases listed : roots? value with _ | ⟨roots, accounts⟩
      · exact kept (by simp [sharedAs, listed])
      · rcases decoded : SharedExecution.graphOf? (sharedForm (tables roots accounts) #[]) with
          _ | graph
        · exact kept (by simp [sharedAs, listed, decoded])
        · simp only [sharedAs, listed, decoded, rootEntries?_sharedForm] at absent
          cases absent

/-! ### The reader's walk is the producer's walk -/

/-- **For equal successor lists, the reader's visits are the producer's.** Let `rename` take the
name indices that the decoded successors reach from `root` to names, one-to-one on them. Let the
record of the image of each such index list as its successors the images of the decoded successors
of the index, in their order. Then the producer's walk from the image of `root`, when it returns
visits, returns the reader's visits carried by `rename`, with the same parents
(`StackWalk.walk_agree`): the two walks are one definition. That the encoding and the decoding of
the shared edge sets give these hypotheses is not proved. -/
theorem walk_agree {graph : SharedExecution.Graph} {root : Nat}
    {request : ExecutionWalk.WalkRequest} {visits : Array (Name × Option Nat)}
    {rename : Nat → Name} (rooted : rename root = request.root)
    (injective : ∀ node node', StackWalk.Reach graph.next root node →
      StackWalk.Reach graph.next root node' → rename node = rename node' → node = node')
    (carried : ∀ node, StackWalk.Reach graph.next root node →
      ExecutionWalk.successorsOf request.records (rename node) =
        some ((graph.successors.getD node #[]).map rename))
    (accepted : ExecutionWalk.walk request = .ok visits) :
    visits = (SharedExecution.walk graph root).map (Prod.map rename id) :=
  StackWalk.walk_agree injective (fun node reach => carried node reach)
    (SharedExecution.walk_eq graph root) (by rw [rooted]; exact accepted)

end Regula.ExecutionShare
