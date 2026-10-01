import Regula.Report
import Regula.SharedExecution

/-! # Shared forms of execution accounts

The proposals a result writer offers `SharedExecution.internValue` for an `execution` member: the
shared form of an array of root accounts, with every reached name, edge and boundary record of the
environment once and one entry per root.

Nothing here is trusted or proved to be a correct encoding. `SharedExecution.internValue` keeps a
proposal only when the reader (`SharedExecution.restore?`) returns the logical value's content
from it, and otherwise writes the logical value itself, so `SharedExecution.expand_intern` holds
whatever these functions return. What depends on them is only how small the written member is. A
root is written as an entry of constant size when the reader's derivation reproduces its account:
its visits are the walk over the environment's edges, its edges those leaving its reached names,
and its boundaries its visited names' records. The collector (`Regula.Probe`) is written to
produce accounts of that form, which is unproved; a root whose account differs is written with
its visits listed, or in full. -/
namespace Regula.ExecutionShare
open Lean RegulaPolicy
open Regula.SharedExecution (boundaryObject boundaryRecord closureObject rootObject visitObject)
open scoped Regula.Report

/-! ### The reader builds the objects the logical document holds

Each object the reader builds is, by definition, the object the logical document's codec writes
for the same members, so the reader's objects have exactly the codec's member names. -/

theorem visit_toJson (visit : ExecutionVisit) :
    toJson visit =
      visitObject (toJson visit.name) (toJson visit.moduleName) (toJson visit.parent) := rfl

theorem boundary_toJson (boundary : ExecutionBoundary) :
    toJson boundary =
      boundaryObject (toJson boundary.occurrence) (toJson boundary.name) (toJson boundary.module)
        (toJson boundary.boundary) (toJson boundary.correspondence) (toJson boundary.owned)
        (toJson boundary.replacement) (toJson boundary.evidence)
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

/-! ### Proposals -/

/-- An index as a written account carries it. -/
private def number (index : Nat) : Json := SourceTexts.refJson index

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

/-- The shared part for `roots`. Names are listed in the order of `canonicalNames`, so an edge
list ordered by index pairs is in the order of `canonicalEdges`; each name's boundary records are
those of the first root that reaches it, in that root's order. -/
def tables (roots : Array ExecutionRoot) : Tables :=
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
  let records := roots.foldl (init := ({} : Std.HashMap Nat (Array Json))) fun found root =>
    let own := root.boundaries.foldl (init := ({} : Std.HashMap Nat (Array Json)))
      fun own boundary =>
        let slot := node boundary.name
        if found.contains slot then own
        else own.insert slot ((own.getD slot #[]).push (boundaryRecord (number slot)
          (toJson boundary.name) (toJson boundary.module) (toJson boundary.boundary)
          (toJson boundary.correspondence) (toJson boundary.owned) (toJson boundary.replacement)
          (toJson boundary.evidence) (toJson boundary.toolchainOrigin?)))
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

/-- The members every root entry has: its name's index, its module, its unresolved paths and
whether the root itself requires code. -/
def entryMembers (tables : Tables) (root : ExecutionRoot) : List (String × Json) := [
  ("name", number (tables.node root.name)), ("module", toJson root.module),
  ("unresolved", toJson root.unresolved),
  ("requiresCode", toJson (root.closure.requiredCode.contains root.name))]

/-- A root entry from which the reader derives the whole account. -/
def derivedEntry (tables : Tables) (root : ExecutionRoot) : Json :=
  Json.mkObj (entryMembers tables root)

/-- A root entry that lists the root's visits, each as its name's index and the position of the
visit that queued it; the reader derives the rest. -/
def listedEntry (tables : Tables) (root : ExecutionRoot) : Json :=
  Json.mkObj (entryMembers tables root ++ [("visits", .arr (root.closure.visits.map fun visit =>
    Json.arr #[number (tables.node visit.name), toJson visit.parent]))])

/-- A root entry that holds the root's account as it is. -/
def explicitEntry (account : Json) : Json := Json.mkObj [("explicit", account)]

/-- The written account with the shared part `tables` and the root entries `entries`. -/
def sharedForm (tables : Tables) (entries : Array Json) : Json :=
  Json.mkObj (tables.members ++ [(SharedExecution.rootsKey, .arr entries)])

/-- The roots a logical `execution` value lists, when it is a nonempty array of root accounts. -/
private def roots? (value : Json) : Option (Array ExecutionRoot) :=
  match (fromJson? value : Except String (Array ExecutionRoot)) with
  | .ok roots => if roots.isEmpty then none else some roots
  | .error _ => none

/-- The shared form in which every root entry is derived; `value` itself when it is not a
nonempty array of root accounts. -/
def derived (value : Json) : Json :=
  match roots? value with
  | some roots =>
      let tables := tables roots
      sharedForm tables (roots.map (derivedEntry tables))
  | none => value

/-- The shared form in which each root has the smallest entry from which the reader rebuilds its
account: derived, else with its visits listed, else explicit. `value` itself when it is not a
nonempty array of root accounts. -/
def fitted (value : Json) : Json :=
  match roots? value, SharedExecution.array? value with
  | some roots, some accounts =>
      let tables := tables roots
      match SharedExecution.graphOf? (sharedForm tables #[]) with
      | some graph =>
          let fits (entry account : Json) : Bool :=
            match SharedExecution.rebuildRoot graph entry with
            | some rebuilt => SharedExecution.alike rebuilt account
            | none => false
          sharedForm tables <| (roots.zip accounts).map fun (root, account) =>
            let entry := derivedEntry tables root
            if fits entry account then entry
            else
              let entry := listedEntry tables root
              if fits entry account then entry else explicitEntry account
      | none => value
  | _, _ => value

/-- The proposals of a result writer, in the order it tries them. -/
def proposals : List (Json → Json) := [derived, fitted]

end Regula.ExecutionShare
