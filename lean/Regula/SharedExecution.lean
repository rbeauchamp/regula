import Regula.SourceTexts
import Std.Data.HashMap
import Std.Data.HashSet

/-! # Execution accounts of a result document, stored once per environment

An environment report names the execution account of its roots with one member, `execution`. In
the document a checker builds and a reader consumes (the *logical* document) that member is an
array with one complete account per root: the root's reached names, visits, edges and boundaries.
A root that reaches what another root reaches lists it again, so the logical member grows with the
roots times what each reaches. In the document a result file holds (the *written* document) the
member can be the *shared form*: every reached name, edge and boundary record of the environment
once, and one entry per root, of constant size when the root's account is derived from the
shared part. `restore?` is the reader: it rebuilds each root's account from the shared form.
`intern` writes a document and `expand` reads one.

The laws do not depend on how a shared form is produced. `internValue` keeps a proposed written
value only when `restore?` returns the logical value itself from it, decided by `same`, an
equality test proofs unfold (`same_eq`); otherwise it writes the logical value as it is. So
`restore?_internValue` and `expand_intern` hold for every `Json` value and every proposal, and
`read_write` composes them with the source-text laws: the reader returns exactly the document the
writer was given, object trees included, so whatever a function computes from the read document
it computes from the written one.

The laws concern `Json` values, not JSON text or the files that hold it: what `Json.parse`
returns for the text of a written value is outside them, as it is for `SourceTexts`. They do not
establish that a written value is small: a proposal that `restore?` does not take back is
replaced by the logical value. -/
namespace Regula.SharedExecution
open Lean
open Std.DTreeMap.Internal (Impl)
open Regula.SourceTexts (Fields Cases)

/-- The member whose value is an environment's execution account: an array of root accounts in
the logical document and the shared form in the written one. -/
def accountKey : String := "execution"

/-- The member of a written account that holds its root entries; a written account is an object
with this member. -/
def rootsKey : String := "roots"

/-- The only member of a written value that holds a logical value as it is (`verbatim`). -/
def verbatimKey : String := "verbatim"

/-! ### An equality test proofs unfold -/

mutual
/-- Whether two JSON values are the same value: the same constructor, the same array elements in
order and the same object trees, node for node. Lean's own `Json` equality is `partial`, so no
proof unfolds it; this one is a definition, and `same_eq` proves that a `true` answer is an
equality. Two objects with the same members whose trees are balanced differently are not the
same value, so the answer may be `false` for values Lean's equality identifies. -/
def same (a b : Json) : Bool :=
  match a, b with
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => a == b
  | .str a, .str b => a == b
  | .arr ⟨a⟩, .arr ⟨b⟩ => sameList a b
  | .obj ⟨⟨a⟩⟩, .obj ⟨⟨b⟩⟩ => sameFields a b
  | _, _ => false
termination_by sizeOf a
/-- `same` on the elements of two arrays, in order. -/
def sameList (a b : List Json) : Bool :=
  match a, b with
  | [], [] => true
  | head :: rest, other :: others => same head other && sameList rest others
  | _, _ => false
termination_by sizeOf a
/-- `same` on two object trees: the same shape, sizes and keys, and the same values. -/
def sameFields (a b : Fields) : Bool :=
  match a, b with
  | .leaf, .leaf => true
  | .inner size key value left right, .inner size' key' value' left' right' =>
      size == size' && key == key' && same value value' && sameFields left left' &&
        sameFields right right'
  | _, _ => false
termination_by sizeOf a
end

private theorem sameList_eq {a : List Json}
    (elements : ∀ value ∈ a, ∀ other, same value other = true → value = other) :
    ∀ b, sameList a b = true → a = b := by
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons other others => simp [sameList] at h
  | cons head rest step =>
    intro b h
    cases b with
    | nil => simp [sameList] at h
    | cons other others =>
      simp only [sameList, Bool.and_eq_true] at h
      rw [elements head List.mem_cons_self other h.1,
        step (fun value member => elements value (List.mem_cons_of_mem _ member)) others h.2]

/-- **`same` answers `true` only for equal values.** The converse is not claimed: nothing here
depends on it. -/
theorem same_eq (a b : Json) (h : same a b = true) : a = b := by
  revert b
  refine Cases.value (motive := fun a => ∀ b, same a b = true → a = b)
    (fieldsMotive := fun fields => ∀ other, sameFields fields other = true → fields = other) ?_ a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b h
    cases b <;> simp_all [same]
  · intro value b h
    cases b <;> simp_all [same]
  · intro value b h
    cases b <;> simp_all [same]
  · intro value b h
    cases b <;> simp_all [same]
  · intro elems elements b h
    obtain ⟨elems⟩ := elems
    cases b with
    | arr other =>
      obtain ⟨other⟩ := other
      simp only [same] at h
      have lists : elems = other :=
        sameList_eq (fun value member => elements value (Array.mem_def.mpr member)) other h
      rw [lists]
    | _ => simp [same] at h
  · intro fields step b h
    cases b with
    | obj other =>
      obtain ⟨⟨other⟩⟩ := other
      simp only [same] at h
      rw [step other h]
    | _ => simp [same] at h
  · intro other h
    cases other with
    | leaf => rfl
    | inner size key value left right => simp [sameFields] at h
  · intro size key value left right valueStep leftStep rightStep other h
    cases other with
    | leaf => simp [sameFields] at h
    | inner size' key' value' left' right' =>
      simp only [sameFields, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨rfl, rfl⟩, values⟩, lefts⟩, rights⟩ := h
      rw [valueStep value' values, leftStep left' lefts, rightStep right' rights]

/-! ### The members a document names with one key -/

mutual
/-- Apply `leaf` to the value of every member named `key` of `value`, at any depth outside such a
member; everything else, including each object tree's shape, is kept. -/
def mapMembers (key : String) (leaf : Json → Json) (value : Json) : Json :=
  match value with
  | .arr elems => .arr (elems.map (mapMembers key leaf))
  | .obj ⟨⟨fields⟩⟩ => .obj ⟨⟨mapMemberFields key leaf fields⟩⟩
  | .null => .null
  | .bool b => .bool b
  | .num n => .num n
  | .str s => .str s
termination_by sizeOf value
/-- `mapMembers` on the fields of one object. -/
def mapMemberFields (key : String) (leaf : Json → Json) (fields : Fields) : Fields :=
  match fields with
  | .leaf => .leaf
  | .inner size name value left right =>
      .inner size name (if name == key then leaf value else mapMembers key leaf value)
        (mapMemberFields key leaf left) (mapMemberFields key leaf right)
termination_by sizeOf fields
end

/-- The values of `values` when every one is present, and `none` otherwise. -/
def sequence (values : Array (Option Json)) : Option (Array Json) :=
  if values.all (·.isSome) then some (values.map (·.getD .null)) else none

/-- Restoring each element of an array, where each restores to itself, restores the array. -/
theorem sequence_self {values : Array Json} {leaf : Json → Option Json}
    (each : ∀ value ∈ values, leaf value = some value) :
    sequence (values.map leaf) = some values := by
  have mapped : values.map leaf = values.map some := Array.map_congr_left each
  have all : (values.map some).all (·.isSome) = true := by
    rw [Array.all_eq_true']
    intro option member
    obtain ⟨value, -, rfl⟩ := Array.mem_map.mp member
    rfl
  simp only [sequence, mapped, all, ↓reduceIte, Array.map_map]
  congr 1
  conv => rhs; rw [← Array.map_id values]
  apply Array.map_congr_left
  intro value _
  rfl

mutual
/-- Replace the value of every member named `key` of `value`, at any depth outside such a member,
by what `leaf` returns for it; `none` when `leaf` returns `none` for one of them. -/
def restoreMembers (key : String) (leaf : Json → Option Json) (value : Json) : Option Json :=
  match value with
  | .arr elems => (sequence (elems.map (restoreMembers key leaf))).map Json.arr
  | .obj ⟨⟨fields⟩⟩ =>
      (restoreMemberFields key leaf fields).map fun restored => .obj ⟨⟨restored⟩⟩
  | .null => some .null
  | .bool b => some (.bool b)
  | .num n => some (.num n)
  | .str s => some (.str s)
termination_by sizeOf value
/-- `restoreMembers` on the fields of one object. -/
def restoreMemberFields (key : String) (leaf : Json → Option Json) (fields : Fields) :
    Option Fields :=
  match fields with
  | .leaf => some .leaf
  | .inner size name value left right =>
      match (if name == key then leaf value else restoreMembers key leaf value),
          restoreMemberFields key leaf left, restoreMemberFields key leaf right with
      | some value, some left, some right => some (.inner size name value left right)
      | _, _, _ => none
termination_by sizeOf fields
end

/-- A reader that takes back what a writer made of each value takes back the whole document:
whenever `restore (write value) = some value` for every value, restoring the members named `key`
of a document whose members named `key` were written returns that document. -/
theorem restoreMembers_mapMembers (key : String) (write : Json → Json)
    (restore : Json → Option Json) (inverse : ∀ value, restore (write value) = some value)
    (value : Json) :
    restoreMembers key restore (mapMembers key write value) = some value := by
  refine Cases.value
    (motive := fun value =>
      restoreMembers key restore (mapMembers key write value) = some value)
    (fieldsMotive := fun fields =>
      restoreMemberFields key restore (mapMemberFields key write fields) = some fields) ?_ value
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [mapMembers, restoreMembers]
  · intro b
    simp [mapMembers, restoreMembers]
  · intro n
    simp [mapMembers, restoreMembers]
  · intro s
    simp [mapMembers, restoreMembers]
  · intro elems elements
    have found := sequence_self
      (leaf := fun element => restoreMembers key restore (mapMembers key write element)) elements
    have mapped : (elems.map (mapMembers key write)).map (restoreMembers key restore) =
        elems.map fun element => restoreMembers key restore (mapMembers key write element) := by
      rw [Array.map_map]
      rfl
    simp only [mapMembers, restoreMembers, mapped, found, Option.map_some]
  · intro fields step
    simp [mapMembers, restoreMembers, step]
  · simp [mapMemberFields, restoreMemberFields]
  · intro size name value left right valueStep leftStep rightStep
    by_cases h : (name == key) = true
    · simp [mapMemberFields, restoreMemberFields, h, inverse value, leftStep, rightStep]
    · simp [mapMemberFields, restoreMemberFields, h, valueStep, leftStep, rightStep]

/-! ### Reading a written account -/

/-- The first member named `key` among `fields`, in tree order: for the fields of an object, whose
keys are distinct, the member named `key`. -/
def member? (key : String) : Fields → Option Json
  | .leaf => none
  | .inner _ name value left right =>
      match member? key left with
      | some found => some found
      | none => if name == key then some value else member? key right

/-- The member named `key` of an object, and `none` for any other value. -/
def field? (key : String) : Json → Option Json
  | .obj ⟨⟨fields⟩⟩ => member? key fields
  | _ => none

/-- The elements of an array, and `none` for any other value. -/
def array? : Json → Option (Array Json)
  | .arr elems => some elems
  | _ => none

/-- The pair of natural numbers a two-element array of them is. -/
def pair? : Json → Option (Nat × Nat)
  | .arr elems =>
      match elems.toList with
      | [first, second] => do
          return (← SourceTexts.refOf? first, ← SourceTexts.refOf? second)
      | _ => none
  | _ => none

/-! The objects of a root's account, as the reader builds them. `Regula.Report`'s codecs for
`RegulaPolicy.ExecutionVisit`, `ExecutionBoundary`, `ExecutionClosure` and `ExecutionRoot` build
the same objects (`ExecutionShare.visit_toJson` and its companions, by `rfl`), so a codec and the
reader build the same value from the same members. Each lists its members in the order of their
keys, which is the order the JSON parser inserts the members of a compressed object in: an
account that was parsed is then the same tree as one that was built, which is what lets the
writer keep a shared form for a document that was read back. That is an observation about Lean's
tree insertion (`RegistryChecks` checks it on an account); no law depends on it. -/

/-- A visit of a root's account: its name, its module and the position of the visit that queued
it. -/
def visitObject (name moduleName parent : Json) : Json :=
  Json.mkObj [("moduleName", moduleName), ("name", name), ("parent", parent)]

/-- A boundary of a root's account. -/
def boundaryObject (occurrence name moduleName boundary correspondence owned replacement evidence
    compilerCallers toolchainOrigin : Json) : Json :=
  Json.mkObj [("boundary", boundary), ("compilerCallers", compilerCallers),
    ("correspondence", correspondence), ("evidence", evidence), ("module", moduleName),
    ("name", name), ("occurrence", occurrence), ("owned", owned), ("replacement", replacement),
    ("toolchainOrigin", toolchainOrigin)]

/-- A boundary record as a written account stores it once: the members of `boundaryObject` that
do not depend on the root, and `node`, the index of the boundary's name. -/
def boundaryRecord (node name moduleName boundary correspondence owned replacement evidence
    toolchainOrigin : Json) : Json :=
  Json.mkObj [("boundary", boundary), ("correspondence", correspondence), ("evidence", evidence),
    ("module", moduleName), ("name", name), ("node", node), ("owned", owned),
    ("replacement", replacement), ("toolchainOrigin", toolchainOrigin)]

/-- The closure of a root's account. -/
def closureObject (nodes visits logicalEdges candidateEdges historyEdges currentReplacementEdges
    activeSimplificationEdges helperEdges requiredCode unavailableCode : Json) : Json :=
  Json.mkObj [("activeSimplificationEdges", activeSimplificationEdges),
    ("candidateEdges", candidateEdges), ("currentReplacementEdges", currentReplacementEdges),
    ("helperEdges", helperEdges), ("historyEdges", historyEdges), ("logicalEdges", logicalEdges),
    ("nodes", nodes), ("requiredCode", requiredCode), ("unavailableCode", unavailableCode),
    ("visits", visits)]

/-- A root's account. -/
def rootObject (name moduleName boundaries unresolved compilerEdges closure : Json) : Json :=
  Json.mkObj [("boundaries", boundaries), ("closure", closure), ("compilerEdges", compilerEdges),
    ("module", moduleName), ("name", name), ("unresolved", unresolved)]

/-- The edges of a written channel as successor lists: entry `source` lists the targets of the
edges leaving `source`, in the order the channel lists them. `none` when an endpoint is not below
`size`. -/
def adjacency (size : Nat) (edges : Array (Nat × Nat)) : Option (Array (Array Nat)) :=
  edges.foldlM (init := Array.replicate size #[]) fun table (source, target) =>
    if source < size ∧ target < size then some (table.modify source (·.push target)) else none

/-- The shared part of a written account, decoded: the names and, by name index, each name's
module, its edges in each channel and its boundary records. -/
structure Graph where
  /-- Every name of the environment's accounts, once. -/
  names : Array Json
  /-- The module of each name, `null` where the environment attributes none. -/
  modules : Array Json
  /-- Retained compiler IR edges. -/
  compiler : Array (Array Nat)
  /-- Edges to the constants a followed value mentions. -/
  logical : Array (Array Nat)
  /-- Edges to simplification candidates. -/
  candidate : Array (Array Nat)
  /-- Edges to recorded historical replacement targets. -/
  history : Array (Array Nat)
  /-- Edges to current replacement targets. -/
  current : Array (Array Nat)
  /-- Edges to active simplification targets, which the walk does not follow. -/
  active : Array (Array Nat)
  /-- Edges to compiled recursion helpers. -/
  helper : Array (Array Nat)
  /-- The compiler edges reversed: entry `target` lists the sources that call it. -/
  callers : Array (Array Nat)
  /-- The names the walk queues after visiting a name, in the order it queues them. -/
  successors : Array (Array Nat)
  /-- The boundary records at each name, in the order the walk found them. -/
  boundaries : Array (Array Json)
  /-- Whether required code of the name is unavailable. -/
  unavailable : Array Bool
  /-- One more than the number of queued names of `successors`: a bound on the steps of any
  walk. -/
  fuel : Nat

/-- Decode the shared part of a written account from its object's fields; `none` when a member is
missing or malformed or an index is out of range. -/
def graph? (fields : Fields) : Option Graph := do
  let names ← array? (← member? "names" fields)
  let size := names.size
  let moduleTable ← array? (← member? "modules" fields)
  let nameModules ← array? (← member? "nameModules" fields)
  guard (nameModules.size == size)
  let modules ← sequence <| nameModules.map fun entry =>
    match entry with
    | .null => some .null
    | position => (SourceTexts.refOf? position).bind (moduleTable[·]?)
  let channel (key : String) : Option (Array (Nat × Nat)) := do
    (← array? (← member? key fields)).mapM pair?
  let compilerEdges ← channel "compilerEdges"
  let compiler ← adjacency size compilerEdges
  let logical ← adjacency size (← channel "logicalEdges")
  let candidate ← adjacency size (← channel "candidateEdges")
  let history ← adjacency size (← channel "historyEdges")
  let current ← adjacency size (← channel "currentReplacementEdges")
  let active ← adjacency size (← channel "activeSimplificationEdges")
  let helper ← adjacency size (← channel "helperEdges")
  let callers ← adjacency size (compilerEdges.map fun (source, target) => (target, source))
  let records ← array? (← member? "boundaries" fields)
  let boundaries ← records.foldlM (init := Array.replicate size #[]) fun table record => do
    let node ← SourceTexts.refOf? (← field? "node" record)
    if node < size then some (table.modify node (·.push record)) else none
  let unavailableNodes ← (← array? (← member? "unavailableCode" fields)).mapM SourceTexts.refOf?
  let unavailable ← unavailableNodes.foldlM (init := Array.replicate size false) fun table node =>
    if node < size then some (table.set! node true) else none
  -- The walk queues a name's successors channel by channel, each channel in its listed order.
  let successors := (Array.range size).map fun node =>
    [compiler, candidate, history, current, logical, helper].foldl
      (fun queued channel => queued ++ channel.getD node #[]) #[]
  return {
    names, modules, compiler, logical, candidate, history, current, active, helper, callers,
    successors, boundaries, unavailable,
    fuel := successors.foldl (fun count queued => count + queued.size) 1 }

/-- The shared part of a written account, decoded from the account. -/
def graphOf? : Json → Option Graph
  | .obj ⟨⟨fields⟩⟩ => graph? fields
  | _ => none

/-- The walk of the execution collector (`Regula.Probe`) over successor lists: a stack of queued
names, each with the visit that queued it. A step takes the name queued last; if it was not
visited, it is visited and its successors are queued in their listed order. The result lists each
visited name once, in visit order, with the position of the visit that queued it. `fuel` bounds
the steps; a walk takes one step for each queued name. -/
def walkLoop (successors : Array (Array Nat)) :
    Nat → List (Nat × Option Nat) → Std.HashSet Nat → Array (Nat × Option Nat) →
      Array (Nat × Option Nat)
  | 0, _, _, visits => visits
  | _, [], _, visits => visits
  | fuel + 1, (node, parent) :: queued, visited, visits =>
      if visited.contains node then walkLoop successors fuel queued visited visits
      else
        let position := visits.size
        let queued := (successors.getD node #[]).foldl
          (fun queued next => (next, some position) :: queued) queued
        walkLoop successors fuel queued (visited.insert node) (visits.push (node, parent))

/-- The visits of the walk from `root`. -/
def walk (graph : Graph) (root : Nat) : Array (Nat × Option Nat) :=
  walkLoop graph.successors graph.fuel [(root, none)] {} #[]

/-- A sorted array without its repeated elements. -/
def distinct (sorted : Array Nat) : Array Nat :=
  sorted.foldl (fun kept node => if kept.back? == some node then kept else kept.push node) #[]

/-- The account of one root, rebuilt from the shared part and the root's written entry.

An entry with an `explicit` member is that member. Any other entry gives the root's name index,
its `module` and `unresolved` paths, and whether the root itself requires code; its visits are
the walk from the root (`walk`). From the visits follow: the reached names, in name order; each
channel's edges, those leaving a reached name; the required code, the targets of the reached
compiler edges and the root if it requires code; the unavailable code among it; and the
boundaries, each visited name's records in visit order, numbered by position, with the reached
names that call the boundary's name in visit order. `none` when a member is missing or
malformed. -/
def rebuildRoot (graph : Graph) (entry : Json) : Option Json :=
  match field? "explicit" entry with
  | some root => some root
  | none => do
    let root ← SourceTexts.refOf? (← field? "name" entry)
    let rootName ← graph.names[root]?
    let moduleName ← field? "module" entry
    let unresolved ← field? "unresolved" entry
    let requiresCode ← match ← field? "requiresCode" entry with
      | .bool required => some required
      | _ => none
    let visits := walk graph root
    let order := visits.map (·.1)
    let reached := order.qsort fun a b => decide (a < b)
    let name (node : Nat) : Json := graph.names.getD node .null
    let edges (channel : Array (Array Nat)) : Json := .arr <| reached.flatMap fun source =>
      (channel.getD source #[]).map fun target => Json.arr #[name source, name target]
    let targets := (reached.flatMap fun source => graph.compiler.getD source #[]) ++
      (if requiresCode then #[root] else #[])
    let required := distinct (targets.qsort fun a b => decide (a < b))
    let position : Std.HashMap Nat Nat :=
      (order.foldl (fun (found, place) node => (found.insert node place, place + 1))
        (({} : Std.HashMap Nat Nat), 0)).1
    let callers (node : Nat) : Json :=
      let found := (graph.callers.getD node #[]).filterMap fun caller =>
        (position.get? caller).map fun place => (place, caller)
      .arr <| (found.qsort fun a b => decide (a.1 < b.1)).map fun (_, caller) => name caller
    let records := order.flatMap fun node =>
      (graph.boundaries.getD node #[]).map fun record => (node, record)
    let boundaries ← sequence <| records.mapIdx fun occurrence (node, record) => do
      return boundaryObject (SourceTexts.refJson occurrence) (← field? "name" record)
        (← field? "module" record) (← field? "boundary" record)
        (← field? "correspondence" record) (← field? "owned" record)
        (← field? "replacement" record) (← field? "evidence" record) (callers node)
        (← field? "toolchainOrigin" record)
    let visited := visits.map fun (node, parent) =>
      visitObject (name node) (graph.modules.getD node .null)
        (match parent with
          | some place => SourceTexts.refJson place
          | none => .null)
    return rootObject rootName moduleName (.arr boundaries) unresolved (edges graph.compiler)
      (closureObject (.arr (reached.map name)) (.arr visited) (edges graph.logical)
        (edges graph.candidate) (edges graph.history) (edges graph.current) (edges graph.active)
        (edges graph.helper) (.arr (required.map name))
        (.arr ((required.filter fun node => graph.unavailable.getD node false).map name)))

/-- **The reader.** The logical value a written value of an `execution` member stands for:
* an object with a `verbatim` member stands for that member's value;
* any other object with a `roots` member is a shared form, and stands for the array of its roots'
  accounts (`rebuildRoot`), `none` when it is malformed;
* every other value stands for itself. -/
def restore? : Json → Option Json
  | .obj ⟨⟨fields⟩⟩ =>
      match member? verbatimKey fields with
      | some value => some value
      | none =>
          match member? rootsKey fields with
          | some roots => do
              let graph ← graph? fields
              return .arr (← sequence ((← array? roots).map (rebuildRoot graph)))
          | none => some (.obj ⟨⟨fields⟩⟩)
  | value => some value

/-- A logical value written as it is: the one member of the written value. The writer uses it only
for a value that `restore?` would not return from itself. -/
def verbatim (value : Json) : Json := .obj ⟨⟨.inner 1 verbatimKey value .leaf .leaf⟩⟩

theorem restore?_verbatim (value : Json) : restore? (verbatim value) = some value := by
  simp [restore?, verbatim, member?]

/-- Whether the reader returns `value` itself from `written`, decided with `same`. -/
def recovers (written value : Json) : Bool :=
  match restore? written with
  | some restored => same restored value
  | none => false

theorem restore?_of_recovers {written value : Json} (h : recovers written value = true) :
    restore? written = some value := by
  unfold recovers at h
  split at h
  next restored found => rw [found, same_eq restored value h]
  next => cases h

/-- The first proposal for `value` that the reader takes back to `value`. -/
def firstRecovered (value : Json) : List (Json → Json) → Option Json
  | [] => none
  | propose :: rest =>
      let written := propose value
      if recovers written value then some written else firstRecovered value rest

theorem restore?_of_firstRecovered {value written : Json} (proposals : List (Json → Json))
    (h : firstRecovered value proposals = some written) : restore? written = some value := by
  induction proposals with
  | nil => simp [firstRecovered] at h
  | cons propose rest step =>
    simp only [firstRecovered] at h
    split at h
    next recovered =>
      cases h
      exact restore?_of_recovers recovered
    next => exact step h

/-- The written form of the value of an `execution` member: the first of `proposals` for it that
the reader takes back to it; without one, the value itself when the reader returns it from
itself, and otherwise the value as a `verbatim` member. -/
def internValue (proposals : List (Json → Json)) (value : Json) : Json :=
  match firstRecovered value proposals with
  | some written => written
  | none => if recovers value value then value else verbatim value

/-- **The reader recovers each value the writer was given.** For every value and every list of
proposals, `restore?` of the written form is that value. -/
theorem restore?_internValue (proposals : List (Json → Json)) (value : Json) :
    restore? (internValue proposals value) = some value := by
  unfold internValue
  split
  next written found => exact restore?_of_firstRecovered proposals found
  next =>
    split
    next recovered => exact restore?_of_recovers recovered
    next => exact restore?_verbatim value

/-- The written form of a logical document's execution accounts: each `execution` member is its
`internValue`. -/
def intern (proposals : List (Json → Json)) (document : Json) : Json :=
  mapMembers accountKey (internValue proposals) document

/-- The logical document a written one stands for: each `execution` member holds the value the
reader returns for it. Refused when the reader returns none for one of them. -/
def expand (written : Json) : Except String Json :=
  match restoreMembers accountKey restore? written with
  | some document => .ok document
  | none => .error "result document: an execution account does not restore"

/-- **The reader recovers the document the writer was given.** For every document and every list
of proposals, `expand` of what `intern` wrote is that document. -/
theorem expand_intern (proposals : List (Json → Json)) (document : Json) :
    expand (intern proposals document) = .ok document := by
  simp [expand, intern, restoreMembers_mapMembers accountKey (internValue proposals) restore?
    (restore?_internValue proposals) document]

/-- `mapMemberFields` is the tree's own value map, so it keeps every key and the tree's shape. -/
theorem mapMemberFields_eq_map (key : String) (leaf : Json → Json) (fields : Fields) :
    mapMemberFields key leaf fields =
      fields.map fun name value =>
        if name == key then leaf value else mapMembers key leaf value := by
  induction fields with
  | leaf => simp [mapMemberFields, Impl.map]
  | inner size name value left right hl hr => simp [mapMemberFields, Impl.map, hl, hr]

/-- Writing the execution accounts keeps the one `null` `sourceTexts` member `SourceTexts.intern`
requires, so by `SourceTexts.intern_isOk_iff` a document with that member is refused by `write`
only if a `sourceText` member of its written accounts or of the rest of it is not a string. -/
theorem slots_intern (proposals : List (Json → Json)) {document : Json}
    (h : SourceTexts.slots document = [.null]) :
    SourceTexts.slots (intern proposals document) = [.null] := by
  cases document with
  | obj raw =>
    obtain ⟨⟨fields⟩⟩ := raw
    have slot : SourceTexts.slotsFields fields = [.null] := by
      simpa [SourceTexts.slots] using h
    have distinct : (SourceTexts.tableKey == accountKey) = false := by decide
    simp only [intern, mapMembers, SourceTexts.slots]
    rw [mapMemberFields_eq_map, SourceTexts.slotsFields_map, slot]
    simp [distinct, mapMembers]
  | _ => simp [SourceTexts.slots] at h

/-- The value a result file holds for a logical result document: its execution accounts written
(`intern`), then its source texts stored once (`SourceTexts.intern`). Refused exactly when
`SourceTexts.intern` refuses the document with its accounts written. -/
def write (proposals : List (Json → Json)) (document : Json) : Except String Json :=
  SourceTexts.intern (intern proposals document)

/-- The logical result document a result file's value stands for: its source texts put back
(`SourceTexts.expand`), then its execution accounts restored (`expand`). -/
def read (written : Json) : Except String Json := do
  expand (← SourceTexts.expand written)

/-- **A reader of a result file's value recovers the document its writer was given.** Whenever
`write` produces a value, `read` of it is that document, for every document and every list of
proposals. So a function of the document a reader holds is the same function of the document the
writer was given: `f <$> read written = .ok (f document)`. -/
theorem read_write {proposals : List (Json → Json)} {document written : Json}
    (h : write proposals document = .ok written) : read written = .ok document := by
  have texts : SourceTexts.expand written = .ok (intern proposals document) :=
    SourceTexts.expand_intern h
  simp only [read, texts, bind, Except.bind]
  exact expand_intern proposals document

/-- Whether a written account is a shared form whose every root entry is derived from the shared
part alone: none is `explicit`. An observation for controls; no law depends on it. -/
def derivedOnly (written : Json) : Bool :=
  match field? rootsKey written with
  | some (.arr entries) =>
      (graphOf? written).isSome && !entries.isEmpty && entries.all fun entry =>
        (field? "explicit" entry).isNone
  | _ => false

end Regula.SharedExecution
