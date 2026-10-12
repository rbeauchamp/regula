import Regula.Report
import Regula.SharedExecution
import RegulaPolicy.ExecutionWalk
import Regula.JsonCanon

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

/-- The proposals of a result writer: `fitted` in the form the JSON parser builds
(`JsonCanon.canon`), so that the parse of the written text is the written value itself
(`JsonRoundTrip.parse_compress_canonical`). -/
def proposals : List (Json → Json) := [fun value => JsonCanon.canon (fitted value)]

/-! ### The forms a writer gives a value

`fitted` writes a root's derived entry when the reader rebuilds from it a value `same` as the
root's logical account, a test that compares object trees node for node, so the kind of a root's
entry depends on the shapes of the trees of the document the writer was given. `sharedAs` is the
shared form with the kind of each entry given, and `formLike` is the form a writer gives a value
with the entry kinds of a written value, the shared form in the parser's form (`JsonCanon.canon`):
`formLike_internValue` and `formLike_sharedAs` state that it returns each writer's own form, so
admission (`ResultProtocol.admitDocument`) accepts a written value at every entry kinds under
which the reader takes its accounts back (`ResultProtocol.admitDocument_writeAs`). -/

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
  | some entries =>
      SharedExecution.internValue
        [fun value => JsonCanon.canon (sharedAs (explicitAt entries) value)] value
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

/-! ### Entry kinds in the parser's form

The written value of a result writer is the parser's form (`JsonCanon.canon`) of `fitted`'s value.
Each root entry is an object built with `Json.mkObj`, whose tree is a search tree, so the parser's
form of an entry has the same members (`JsonCanon.getObjVal?_canon`) and the same kind. -/

/-- An entry built from a list of members has the kind of its parser's form. -/
theorem isExplicit_canon_mkObj (members : List (String × Json)) :
    isExplicit (JsonCanon.canon (Json.mkObj members)) = isExplicit (Json.mkObj members) := by
  simp only [isExplicit]
  rw [JsonCanon.mkObj_eq, JsonCanon.getObjVal?_canon (JsonCanon.treeOf_ordered members)]
  cases Json.getObjVal? _ "explicit" <;> rfl

/-- Root entries built from lists of members have the kinds of their parser's forms. -/
theorem explicitAt_map_canon {entries : Array Json}
    (built : ∀ entry ∈ entries, ∃ members, entry = Json.mkObj members) :
    explicitAt (entries.map JsonCanon.canon) = explicitAt entries := by
  funext position
  simp only [explicitAt, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  rcases found : entries[position]? with _ | entry
  · rfl
  · obtain ⟨members, rfl⟩ := built _ (Array.mem_of_getElem? found)
    exact isExplicit_canon_mkObj members

/-- The root entries of the parser's form of a shared form are the parser's forms of its root
entries. -/
theorem rootEntries?_canon_sharedForm (tables : Tables) (entries : Array Json) :
    rootEntries? (JsonCanon.canon (sharedForm tables entries)) =
      some (entries.map JsonCanon.canon) := by
  have found := getObjVal?_mkObj_last tables.members SharedExecution.rootsKey (.arr entries)
  unfold rootEntries? sharedForm
  rw [JsonCanon.mkObj_eq, JsonCanon.getObjVal?_canon (JsonCanon.treeOf_ordered _),
    ← JsonCanon.mkObj_eq, found]
  simp [Except.map, JsonCanon.canon_arr]

/-- Each element of an array mapped by a function that builds every value from a list of members
is built from a list of members. -/
theorem built_map {α : Type} {pairs : Array α} {entry : Json} {build : α → Json}
    (each : ∀ pair, ∃ members, build pair = Json.mkObj members)
    (present : entry ∈ pairs.map build) :
    ∃ members, entry = Json.mkObj members := by
  obtain ⟨pair, _, rfl⟩ := Array.mem_map.mp present
  exact each pair

/-- As `built_map`, for a map with positions. -/
theorem built_mapIdx {α : Type} {pairs : Array α} {entry : Json} {build : Nat → α → Json}
    (each : ∀ position pair, ∃ members, build position pair = Json.mkObj members)
    (present : entry ∈ pairs.mapIdx build) : ∃ members, entry = Json.mkObj members := by
  obtain ⟨position, inside, rfl⟩ := Array.mem_mapIdx.mp present
  exact each position _

/-- What `fitted` writes, where it does not write the value as it is, is a shared form whose root
entries are each built from a list of members. -/
theorem fitted_shared {value : Json} (kept : ¬fitted value = value) :
    ∃ tables entries, fitted value = sharedForm tables entries ∧
      ∀ entry ∈ entries, ∃ members, entry = Json.mkObj members := by
  rcases listed : roots? value with _ | ⟨roots, accounts⟩
  · exact absurd (by simp [fitted, listed]) kept
  · rcases decoded : SharedExecution.graphOf? (sharedForm (tables roots accounts) #[]) with
      _ | graph
    · exact absurd (by simp [fitted, listed, decoded]) kept
    · simp only [fitted, listed, decoded]
      refine ⟨_, _, rfl, fun entry present => built_map (fun pair => ?_) present⟩
      split <;> exact ⟨_, rfl⟩

/-- What `sharedAs` writes, where it does not write the value as it is, is a shared form whose
root entries are each built from a list of members. -/
theorem sharedAs_shared {explicit : Nat → Bool} {value : Json}
    (kept : ¬sharedAs explicit value = value) :
    ∃ tables entries, sharedAs explicit value = sharedForm tables entries ∧
      ∀ entry ∈ entries, ∃ members, entry = Json.mkObj members := by
  rcases listed : roots? value with _ | ⟨roots, accounts⟩
  · exact absurd (by simp [sharedAs, listed]) kept
  · rcases decoded : SharedExecution.graphOf? (sharedForm (tables roots accounts) #[]) with
      _ | graph
    · exact absurd (by simp [sharedAs, listed, decoded]) kept
    · simp only [sharedAs, listed, decoded]
      refine ⟨_, _, rfl, fun entry present => built_mapIdx (fun position pair => ?_) present⟩
      split <;> exact ⟨_, rfl⟩

/-- The entry kinds of the parser's form of a shared form with entries built from lists of
members are the kinds of its own entries. -/
theorem kinds_canon {tables : Tables} {entries found : Array Json}
    (built : ∀ entry ∈ entries, ∃ members, entry = Json.mkObj members)
    (listed : rootEntries? (JsonCanon.canon (sharedForm tables entries)) = some found) :
    explicitAt found = explicitAt entries := by
  rw [rootEntries?_canon_sharedForm] at listed
  cases listed
  exact explicitAt_map_canon built

/-- **`formLike` returns the result writers' form.** For every logical execution value, the form
`formLike` gives it with the entry kinds of the writers' written form is that written form. -/
theorem formLike_internValue (value : Json) :
    formLike (SharedExecution.internValue proposals value) value =
      SharedExecution.internValue proposals value := by
  unfold formLike
  split
  · next entries found =>
    by_cases kept : fitted value = value
    · exact internValue_congr (congrArg JsonCanon.canon ((fitted_self kept _).trans kept.symm))
    · apply internValue_congr
      by_cases recovered :
          SharedExecution.recovers (JsonCanon.canon (fitted value)) value = true
      · have written : SharedExecution.internValue proposals value =
            JsonCanon.canon (fitted value) := by
          simp [proposals, SharedExecution.internValue, SharedExecution.firstRecovered, recovered]
        rw [written] at found
        obtain ⟨tables, shared, form, built⟩ := fitted_shared kept
        rw [form] at found
        have kinds := kinds_canon built found
        have own : rootEntries? (fitted value) = some shared := by
          rw [form, rootEntries?_sharedForm]
        rw [kinds, sharedAs_fitted own]
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
writes the value as it is or the reader returns the value from the parser's form of the shared
form, the form `formLike` gives the value with the entry kinds of the parser's form written with
that choice is that form. -/
theorem formLike_sharedAs {explicit : Nat → Bool} {value : Json}
    (restores : sharedAs explicit value = value ∨
      SharedExecution.recovers (JsonCanon.canon (sharedAs explicit value)) value = true) :
    formLike (SharedExecution.internValue [fun value => JsonCanon.canon (sharedAs explicit value)]
        value) value =
      SharedExecution.internValue [fun value => JsonCanon.canon (sharedAs explicit value)]
        value := by
  by_cases kept : sharedAs explicit value = value
  · obtain ⟨fittedKept, others⟩ := sharedAs_self kept
    unfold formLike
    split
    · exact internValue_congr (congrArg JsonCanon.canon ((others _).trans kept.symm))
    · exact internValue_congr (congrArg JsonCanon.canon (fittedKept.trans kept.symm))
  · have recovered := restores.resolve_left kept
    have written : SharedExecution.internValue
        [fun value => JsonCanon.canon (sharedAs explicit value)] value =
        JsonCanon.canon (sharedAs explicit value) := by
      simp [SharedExecution.internValue, SharedExecution.firstRecovered, recovered]
    rw [written]
    obtain ⟨tables, shared, form, built⟩ := sharedAs_shared kept
    unfold formLike
    split
    · next entries found =>
      rw [form] at found
      have kinds := kinds_canon built found
      have own : rootEntries? (sharedAs explicit value) = some shared := by
        rw [form, rootEntries?_sharedForm]
      have same : SharedExecution.internValue
          [fun value => JsonCanon.canon (sharedAs (explicitAt shared) value)] value =
          SharedExecution.internValue [fun value => JsonCanon.canon (sharedAs explicit value)]
            value :=
        internValue_congr (congrArg JsonCanon.canon (sharedAs_explicitAt own))
      rw [kinds, same]
      simp [SharedExecution.internValue, SharedExecution.firstRecovered, recovered]
    · next absent =>
      rw [form, rootEntries?_canon_sharedForm] at absent
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

/-! ### The written value is in the parser's form

`JsonCanon.Canonical` is the form of the values the JSON parser builds from the compact text of a
value whose object trees are search trees (`JsonRoundTrip.parse_compress_ws`,
`JsonCanon.canonical_canon`), and the parse of the compact text of a value in that form is the
value itself (`JsonRoundTrip.parse_compress_canonical_ws`). Each step of `SharedExecution.write` maps the values
of object trees and keeps their names and shapes, so it keeps that form where every value it
writes in place of another is in it. -/

section Canonical
open JsonCanon (Canonical)

/-- Applying `leaf` to every `sourceText` member keeps the parser's form where `leaf` does. -/
theorem canonical_mapTexts {leaf : Json → Json}
    (each : ∀ value, Canonical value → Canonical (leaf value)) {value : Json}
    (canonical : Canonical value) : Canonical (SourceTexts.mapTexts leaf value) := by
  induction canonical with
  | null => simpa [SourceTexts.mapTexts] using Canonical.null
  | bool b => simpa [SourceTexts.mapTexts] using Canonical.bool b
  | num n => simpa [SourceTexts.mapTexts] using Canonical.num n
  | str s => simpa [SourceTexts.mapTexts] using Canonical.str s
  | @arr elements _ step =>
    simp only [SourceTexts.mapTexts]
    exact .arr fun value present => by
      obtain ⟨original, inside, rfl⟩ := Array.mem_map.mp present
      exact step original inside
  | @obj written increasing members step =>
    have object := Canonical.obj increasing members
    rw [JsonCanon.mkObj_eq] at object ⊢
    simp only [SourceTexts.mapTexts, SourceTexts.mapFields_eq_map]
    refine object.map _ fun member present => ?_
    rw [JsonCanon.members_treeOf increasing] at present
    split
    · exact each _ (members member present)
    · exact step member present

/-- Applying `leaf` to every member named `key` keeps the parser's form where `leaf` does. -/
theorem canonical_mapMembers {key : String} {leaf : Json → Json}
    (each : ∀ value, Canonical value → Canonical (leaf value)) {value : Json}
    (canonical : Canonical value) : Canonical (SharedExecution.mapMembers key leaf value) := by
  induction canonical with
  | null => simpa [SharedExecution.mapMembers] using Canonical.null
  | bool b => simpa [SharedExecution.mapMembers] using Canonical.bool b
  | num n => simpa [SharedExecution.mapMembers] using Canonical.num n
  | str s => simpa [SharedExecution.mapMembers] using Canonical.str s
  | @arr elements _ step =>
    simp only [SharedExecution.mapMembers]
    exact .arr fun value present => by
      obtain ⟨original, inside, rfl⟩ := Array.mem_map.mp present
      exact step original inside
  | @obj written increasing members step =>
    have object := Canonical.obj increasing members
    rw [JsonCanon.mkObj_eq] at object ⊢
    simp only [SharedExecution.mapMembers, SharedExecution.mapMemberFields_eq_map]
    refine object.map _ fun member present => ?_
    rw [JsonCanon.members_treeOf increasing] at present
    split
    · exact each _ (members member present)
    · exact step member present

/-- Replacing the top-level `sourceTexts` members with a value in the parser's form keeps the
form. -/
theorem canonical_setTable {table value : Json} (listed : Canonical table)
    (canonical : Canonical value) : Canonical (SourceTexts.setTable table value) := by
  cases canonical with
  | @obj written increasing members =>
    have object := Canonical.obj increasing members
    rw [JsonCanon.mkObj_eq] at object ⊢
    simp only [SourceTexts.setTable, SourceTexts.setFields]
    refine object.map _ fun member present => ?_
    rw [JsonCanon.members_treeOf increasing] at present
    split
    · exact listed
    · exact members member present
  | null => exact .null
  | bool b => exact .bool b
  | num n => exact .num n
  | str s => exact .str s
  | arr each => exact .arr each

/-- The value a proposal list's writer chooses is one of the proposals' values. -/
theorem firstRecovered_mem {value written : Json} {proposals : List (Json → Json)}
    (found : SharedExecution.firstRecovered value proposals = some written) :
    ∃ propose ∈ proposals, written = propose value := by
  induction proposals with
  | nil => cases found
  | cons propose rest step =>
    simp only [SharedExecution.firstRecovered] at found
    split at found
    · cases found
      exact ⟨propose, List.mem_cons_self, rfl⟩
    · obtain ⟨other, inside, rfl⟩ := step found
      exact ⟨other, List.mem_cons_of_mem _ inside, rfl⟩

/-- The written form of an execution value in the parser's form is in it, when every proposal's
value is. -/
theorem canonical_internValue {proposals : List (Json → Json)}
    (each : ∀ propose ∈ proposals, ∀ value, Canonical (propose value)) {value : Json}
    (canonical : Canonical value) :
    Canonical (SharedExecution.internValue proposals value) := by
  unfold SharedExecution.internValue
  split
  · next written found =>
    obtain ⟨propose, inside, rfl⟩ := firstRecovered_mem found
    exact each propose inside value
  · split
    · exact canonical
    · exact JsonCanon.Canonical.single canonical

/-- Every value a result writer proposes is in the parser's form. -/
theorem canonical_proposals : ∀ propose ∈ proposals, ∀ value, Canonical (propose value) := by
  intro propose inside value
  rw [List.mem_singleton.mp inside]
  exact JsonCanon.canonical_canon _

/-- **The value a result writer writes is in the parser's form.** For every document in it, and
every list of proposals whose values are in it, what `SharedExecution.write` writes is in it. -/
theorem canonical_write {proposals : List (Json → Json)} {document written : Json}
    (each : ∀ propose ∈ proposals, ∀ value, Canonical (propose value))
    (canonical : Canonical document)
    (wrote : SharedExecution.write proposals document = .ok written) : Canonical written := by
  obtain ⟨_, _, _, _, rfl⟩ := SourceTexts.intern_eq_ok wrote
  refine canonical_setTable (.arr fun text present => ?_)
    (canonical_mapTexts (fun value inner => ?_)
      (canonical_mapMembers (fun _ inner => canonical_internValue each inner) canonical))
  · simp only [List.mem_toArray, List.mem_map] at present
    obtain ⟨_, _, rfl⟩ := present
    exact .str _
  · cases value with
    | str text => exact .num _
    | _ => exact inner

end Canonical

end Regula.ExecutionShare
