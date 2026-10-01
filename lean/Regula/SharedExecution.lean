import Regula.SourceTexts
import Std.Data.DTreeMap.Internal.WF.Lemmas
import Std.Data.HashMap
import Std.Data.HashSet

/-! # Execution accounts of a result document, stored once per environment

An environment report names the execution account of its roots with one member, `execution`. In
the document a checker builds and a reader consumes (the *logical* document) that member is an
array with one complete account per root: the root's reached names, visits, edges and boundaries.
A root that reaches what another root reaches lists it again, so the logical member grows with the
roots times what each reaches. In the document a result file holds (the *written* document) the
member is the *shared form*: every reached name, edge and boundary record of the environment
once, and one entry of constant size per root. `restore?` is the reader: it rebuilds each root's
account from the shared form. `intern` writes a document and `expand` reads one.

The laws do not depend on how a shared form is produced. `internValue` keeps a proposed written
value only when `restore?` returns the logical value's content from it, compared with `alike`,
an equality proofs unfold (`alike_content`); otherwise it writes the logical value itself. So
`restore?_internValue` and `expand_intern` hold for every `Json` value and every proposal, and
`read_write` composes them with the source-text laws.

What the reader recovers is the document's `content`: every value with each object as the list of
its members in order, which is what the document's JSON text shows. The recovered document may
balance an object's tree differently from the one written. `getObjVal?_content` proves that
reading a member by its key does not see that difference: two objects of the same content whose
trees are ordered hold values of the same content under every key. That every object of a given
document has an ordered tree is its hypothesis, not proved here. The laws concern `Json` values,
not JSON text or the files that hold it, and they do not establish that a written value is small:
a proposal that `restore?` does not take back is replaced by the logical value. -/
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

/-! ### Content, and an equality proofs unfold -/

/-- What a JSON value's text shows: the value with each object as the list of its members in the
order its tree lists them. Two `Json` values with the same content differ only in how their
object trees are balanced. -/
inductive Content where
  /-- `null`. -/
  | null
  /-- A boolean. -/
  | bool (value : Bool)
  /-- A number. -/
  | num (value : JsonNumber)
  /-- A string. -/
  | str (value : String)
  /-- An array's elements, in order. -/
  | arr (elements : List Content)
  /-- An object's members, in order. -/
  | obj (members : List (String × Content))

mutual
/-- The content of a JSON value. -/
def content (value : Json) : Content :=
  match value with
  | .null => .null
  | .bool b => .bool b
  | .num n => .num n
  | .str s => .str s
  | .arr elems => .arr (elems.map content).toList
  | .obj ⟨⟨fields⟩⟩ => .obj (contentFields fields)
termination_by sizeOf value
/-- The members of an object's fields with their contents, in tree order. -/
def contentFields (fields : Fields) : List (String × Content) :=
  match fields with
  | .leaf => []
  | .inner _ key value left right =>
      contentFields left ++ (key, content value) :: contentFields right
termination_by sizeOf fields
end

/-- The members of an object's fields, in tree order. -/
def entries : Fields → List (String × Json)
  | .leaf => []
  | .inner _ key value left right => entries left ++ (key, value) :: entries right

/-- Listed members with their contents. -/
def contentEntries (listed : List (String × Json)) : List (String × Content) :=
  listed.map fun (key, value) => (key, content value)

theorem contentFields_eq (fields : Fields) :
    contentFields fields = contentEntries (entries fields) := by
  induction fields with
  | leaf => simp [contentFields, entries, contentEntries]
  | inner size key value left right hl hr =>
    simp [contentFields, entries, contentEntries, hl, hr]

mutual
/-- Whether two JSON values have the same content: the same constructor, array elements in order,
and the same object members in order, whatever the shape of the two trees. Lean's own `Json`
equality is `partial`, so no proof unfolds it; this one is a definition, and `alike_content`
proves that a `true` answer is an equality of contents. -/
def alike (a b : Json) : Bool :=
  match a, b with
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => a == b
  | .str a, .str b => a == b
  | .arr ⟨a⟩, .arr ⟨b⟩ => alikeList a b
  | .obj ⟨⟨a⟩⟩, .obj ⟨⟨b⟩⟩ =>
      match alikeFields a (entries b) with
      | some [] => true
      | _ => false
  | _, _ => false
termination_by sizeOf a
/-- `alike` on the elements of two arrays, in order. -/
def alikeList (a b : List Json) : Bool :=
  match a, b with
  | [], [] => true
  | head :: rest, other :: others => alike head other && alikeList rest others
  | _, _ => false
termination_by sizeOf a
/-- Match the members of `a`, in tree order, against the listed members `listed`: the members of
`listed` that remain when each member of `a` has the key of the next listed member and a value
`alike` to it, and `none` otherwise. -/
def alikeFields (a : Fields) (listed : List (String × Json)) : Option (List (String × Json)) :=
  match a with
  | .leaf => some listed
  | .inner _ key value left right =>
      match alikeFields left listed with
      | some ((key', value') :: remaining) =>
          if key == key' && alike value value' then alikeFields right remaining else none
      | _ => none
termination_by sizeOf a
end

private theorem alikeList_content {a : List Json}
    (elements : ∀ value ∈ a, ∀ other, alike value other = true → content value = content other) :
    ∀ b, alikeList a b = true → a.map content = b.map content := by
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons other others => simp [alikeList] at h
  | cons head rest step =>
    intro b h
    cases b with
    | nil => simp [alikeList] at h
    | cons other others =>
      simp only [alikeList, Bool.and_eq_true] at h
      have first := elements head List.mem_cons_self other h.1
      have remaining :=
        step (fun value member => elements value (List.mem_cons_of_mem _ member)) others h.2
      simp [first, remaining]

/-- **`alike` answers `true` only for values with the same content.** The converse is not claimed:
nothing here depends on it. -/
theorem alike_content (a b : Json) (h : alike a b = true) : content a = content b := by
  revert b
  refine Cases.value (motive := fun a => ∀ b, alike a b = true → content a = content b)
    (fieldsMotive := fun fields => ∀ listed remaining,
      alikeFields fields listed = some remaining →
        ∃ matched, listed = matched ++ remaining ∧
          contentEntries matched = contentFields fields) ?_ a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b h
    cases b <;> simp_all [alike]
  · intro value b h
    cases b <;> simp_all [alike]
  · intro value b h
    cases b <;> simp_all [alike]
  · intro value b h
    cases b <;> simp_all [alike]
  · intro elems elements b h
    obtain ⟨elems⟩ := elems
    cases b with
    | arr other =>
      obtain ⟨other⟩ := other
      simp only [alike] at h
      have mapped := alikeList_content
        (fun value member => elements value (Array.mem_def.mpr member)) other h
      simp [content, mapped]
    | _ => simp [alike] at h
  · intro fields step b h
    cases b with
    | obj other =>
      obtain ⟨⟨other⟩⟩ := other
      simp only [alike] at h
      cases found : alikeFields fields (entries other) with
      | none => simp [found] at h
      | some remaining =>
        cases remaining with
        | cons head rest => simp [found] at h
        | nil =>
          obtain ⟨matched, listed, same⟩ := step _ _ found
          simp only [List.append_nil] at listed
          simp [content, ← same, contentFields_eq other, listed]
    | _ => simp [alike] at h
  · intro listed remaining h
    simp only [alikeFields, Option.some.injEq] at h
    exact ⟨[], by simp [h], by simp [contentEntries, contentFields]⟩
  · intro size key value left right valueStep leftStep rightStep listed remaining h
    simp only [alikeFields] at h
    cases found : alikeFields left listed with
    | none => simp [found] at h
    | some middle =>
      cases middle with
      | nil => simp [found] at h
      | cons head middle =>
        obtain ⟨key', value'⟩ := head
        simp only [found] at h
        split at h
        next same =>
          simp only [Bool.and_eq_true, beq_iff_eq] at same
          obtain ⟨rfl, values⟩ := same
          obtain ⟨before, listedEq, beforeContent⟩ := leftStep _ _ found
          obtain ⟨after, middleEq, afterContent⟩ := rightStep _ _ h
          refine ⟨before ++ (key, value') :: after, by simp [listedEq, middleEq], ?_⟩
          simp only [contentFields, ← beforeContent, ← afterContent, valueStep value' values]
          simp [contentEntries]
        next => cases h

/-! ### Reading a member by its key -/

/-- The content of the first member named `key` among listed members. -/
def lookup (key : String) : List (String × Content) → Option Content
  | [] => none
  | (name, value) :: rest => if name == key then some value else lookup key rest

theorem contentFields_toListModel (fields : Fields) :
    contentFields fields = fields.toListModel.map fun member => (member.1, content member.2) := by
  induction fields with
  | leaf => simp [contentFields]
  | inner size key value left right hl hr => simp [contentFields, hl, hr]

theorem lookup_getValue? (key : String) (listed : List ((_ : String) × Json)) :
    lookup key (listed.map fun member => (member.1, content member.2)) =
      (Std.Internal.List.getValue? key listed).map content := by
  induction listed with
  | nil => simp [lookup]
  | cons head rest step =>
    obtain ⟨name, value⟩ := head
    simp only [List.map_cons, lookup, Std.Internal.List.getValue?_cons, step]
    split <;> simp

/-- **Reading a member by its key depends only on an object's content, for ordered trees.** Two
objects with the same content whose trees are ordered by their keys hold, under every key, values
of the same content, or neither holds one: `Json.getObjVal?` does not see how a tree is balanced.
`Impl.Ordered` holds for every tree Lean's own operations build from the empty one (`Json.mkObj`,
the parser, `setObjVal!`), which is Std's `Impl.WF.ordered` and is not restated here; it is a
hypothesis because a `Json` value can hold any tree. The statement is about one object: a reader
that follows several members applies it at each object it reads. -/
theorem getObjVal?_content {a b : Fields} (orderedA : a.Ordered) (orderedB : b.Ordered)
    (same : content (.obj ⟨⟨a⟩⟩) = content (.obj ⟨⟨b⟩⟩)) (key : String) :
    ((Json.obj ⟨⟨a⟩⟩).getObjVal? key).toOption.map content =
      ((Json.obj ⟨⟨b⟩⟩).getObjVal? key).toOption.map content := by
  have fields : contentFields a = contentFields b := by simpa [content] using same
  have found : ∀ {t : Fields}, t.Ordered →
      ((Json.obj ⟨⟨t⟩⟩).getObjVal? key).toOption.map content = lookup key (contentFields t) := by
    intro t ordered
    have read : (Std.TreeMap.Raw.get? (⟨⟨t⟩⟩ : Std.TreeMap.Raw String Json compare) key) =
        Std.Internal.List.getValue? key t.toListModel :=
      Impl.Const.get?_eq_getValue? ordered
    rw [contentFields_toListModel, lookup_getValue?, ← read]
    simp only [Json.getObjVal?]
    split <;> simp_all [Except.toOption, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  rw [found orderedA, found orderedB, fields]

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

/-- Restoring each element of an array, where each restores to its own content, restores to an
array of the same contents. -/
theorem sequence_content {values : Array Json} {leaf : Json → Option Json}
    (each : ∀ value ∈ values, (leaf value).map content = some (content value)) :
    ∃ restored, sequence (values.map leaf) = some restored ∧
      restored.map content = values.map content := by
  have present : ∀ value ∈ values,
      ∃ found, leaf value = some found ∧ content found = content value :=
    fun value member => Option.map_eq_some_iff.mp (each value member)
  refine ⟨(values.map leaf).map (·.getD .null), ?_, ?_⟩
  · have all : (values.map leaf).all (·.isSome) = true := by
      rw [Array.all_eq_true']
      intro option member
      obtain ⟨value, inside, rfl⟩ := Array.mem_map.mp member
      obtain ⟨found, eq, -⟩ := present value inside
      simp [eq]
    simp only [sequence, all, ↓reduceIte]
  · rw [Array.map_map, Array.map_map]
    apply Array.map_congr_left
    intro value member
    obtain ⟨found, eq, same⟩ := present value member
    simp [eq, same]

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

/-- A reader that takes back the content of what a writer made of each value takes back the
content of the whole document: whenever `restore (write value)` is a value with the content of
`value`, for every value, restoring the members named `key` of a document whose members named
`key` were written returns a document with the content of that document. -/
theorem restoreMembers_mapMembers (key : String) (write : Json → Json)
    (restore : Json → Option Json)
    (inverse : ∀ value, (restore (write value)).map content = some (content value))
    (value : Json) :
    (restoreMembers key restore (mapMembers key write value)).map content =
      some (content value) := by
  refine Cases.value
    (motive := fun value =>
      (restoreMembers key restore (mapMembers key write value)).map content =
        some (content value))
    (fieldsMotive := fun fields =>
      (restoreMemberFields key restore (mapMemberFields key write fields)).map contentFields =
        some (contentFields fields)) ?_ value
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [mapMembers, restoreMembers]
  · intro b
    simp [mapMembers, restoreMembers]
  · intro n
    simp [mapMembers, restoreMembers]
  · intro s
    simp [mapMembers, restoreMembers]
  · intro elems elements
    obtain ⟨restored, found, same⟩ := sequence_content
      (leaf := fun element => restoreMembers key restore (mapMembers key write element)) elements
    have mapped : (elems.map (mapMembers key write)).map (restoreMembers key restore) =
        elems.map fun element => restoreMembers key restore (mapMembers key write element) := by
      rw [Array.map_map]
      rfl
    simp only [mapMembers, restoreMembers, mapped, found, Option.map_some, content, same]
  · intro fields step
    obtain ⟨restored, found, same⟩ := Option.map_eq_some_iff.mp step
    simp [mapMembers, restoreMembers, found, content, same]
  · simp [mapMemberFields, restoreMemberFields]
  · intro size name value left right valueStep leftStep rightStep
    obtain ⟨restoredLeft, foundLeft, leftContent⟩ := Option.map_eq_some_iff.mp leftStep
    obtain ⟨restoredRight, foundRight, rightContent⟩ := Option.map_eq_some_iff.mp rightStep
    by_cases h : (name == key) = true
    · obtain ⟨restoredValue, foundValue, valueContent⟩ :=
        Option.map_eq_some_iff.mp (inverse value)
      simp [mapMemberFields, restoreMemberFields, h, foundValue, foundLeft, foundRight,
        contentFields, valueContent, leftContent, rightContent]
    · obtain ⟨restoredValue, foundValue, valueContent⟩ := Option.map_eq_some_iff.mp valueStep
      simp [mapMemberFields, restoreMemberFields, h, foundValue, foundLeft, foundRight,
        contentFields, valueContent, leftContent, rightContent]

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

/-- A visit as a written root entry lists it: a name index below `size` and the position of the
visit that queued it, `null` for the root's own visit. -/
def visit? (size : Nat) : Json → Option (Nat × Option Nat)
  | .arr elems =>
      match elems.toList with
      | [node, parent] => do
          let node ← SourceTexts.refOf? node
          let parent ← match parent with
            | .null => some none
            | position => some <$> SourceTexts.refOf? position
          if node < size then some (node, parent) else none
      | _ => none
  | _ => none

/-- A visit of a root's account, with the members and their order of the logical document
(`Regula.Report`'s codec for `RegulaPolicy.ExecutionVisit`). -/
def visitObject (name moduleName parent : Json) : Json :=
  Json.mkObj [("name", name), ("moduleName", moduleName), ("parent", parent)]

/-- A boundary of a root's account, with the members and their order of the logical document
(`Regula.Report`'s codec for `RegulaPolicy.ExecutionBoundary`). -/
def boundaryObject (occurrence name moduleName boundary correspondence owned replacement evidence
    compilerCallers toolchainOrigin : Json) : Json :=
  Json.mkObj [("occurrence", occurrence), ("name", name), ("module", moduleName),
    ("boundary", boundary), ("correspondence", correspondence), ("owned", owned),
    ("replacement", replacement), ("evidence", evidence), ("compilerCallers", compilerCallers),
    ("toolchainOrigin", toolchainOrigin)]

/-- A boundary record as a written account stores it once: the members of `boundaryObject` that
do not depend on the root, and `node`, the index of the boundary's name. -/
def boundaryRecord (node name moduleName boundary correspondence owned replacement evidence
    toolchainOrigin : Json) : Json :=
  Json.mkObj [("node", node), ("name", name), ("module", moduleName), ("boundary", boundary),
    ("correspondence", correspondence), ("owned", owned), ("replacement", replacement),
    ("evidence", evidence), ("toolchainOrigin", toolchainOrigin)]

/-- The closure of a root's account, with the members and their order of the logical document
(`Regula.Report`'s codec for `RegulaPolicy.ExecutionClosure`). -/
def closureObject (nodes visits logicalEdges candidateEdges historyEdges currentReplacementEdges
    activeSimplificationEdges helperEdges requiredCode unavailableCode : Json) : Json :=
  Json.mkObj [("nodes", nodes), ("visits", visits), ("logicalEdges", logicalEdges),
    ("candidateEdges", candidateEdges), ("historyEdges", historyEdges),
    ("currentReplacementEdges", currentReplacementEdges),
    ("activeSimplificationEdges", activeSimplificationEdges), ("helperEdges", helperEdges),
    ("requiredCode", requiredCode), ("unavailableCode", unavailableCode)]

/-- A root's account, with the members and their order of the logical document
(`Regula.Report`'s codec for `RegulaPolicy.ExecutionRoot`). -/
def rootObject (name moduleName boundaries unresolved compilerEdges closure : Json) : Json :=
  Json.mkObj [("name", name), ("module", moduleName), ("boundaries", boundaries),
    ("unresolved", unresolved), ("compilerEdges", compilerEdges), ("closure", closure)]

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
its `module` and `unresolved` paths, whether the root itself requires code, and optionally its
`visits`; without them the visits are the walk from the root (`walk`). From the visits follow: the
reached names, in name order; each channel's edges, those leaving a reached name; the required
code, the targets of the reached compiler edges and the root if it requires code; the unavailable
code among it; and the boundaries, each visited name's records in visit order, numbered by
position, with the reached names that call the boundary's name in visit order. `none` when a
member is missing or malformed. -/
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
    let visits ← match field? "visits" entry with
      | some listed => (← array? listed).mapM (visit? graph.names.size)
      | none => some (walk graph root)
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
for a value that `restore?` would not return with its own content. -/
def verbatim (value : Json) : Json := .obj ⟨⟨.inner 1 verbatimKey value .leaf .leaf⟩⟩

theorem restore?_verbatim (value : Json) : restore? (verbatim value) = some value := by
  simp [restore?, verbatim, member?]

/-- Whether the reader returns a value with the content of `value` from `written`, decided with
`alike`. -/
def recovers (written value : Json) : Bool :=
  match restore? written with
  | some restored => alike restored value
  | none => false

theorem restore?_of_recovers {written value : Json} (h : recovers written value = true) :
    (restore? written).map content = some (content value) := by
  unfold recovers at h
  split at h
  next restored found => simp [found, alike_content restored value h]
  next => cases h

/-- The first proposal for `value` that the reader takes back to the content of `value`. -/
def firstRecovered (value : Json) : List (Json → Json) → Option Json
  | [] => none
  | propose :: rest =>
      let written := propose value
      if recovers written value then some written else firstRecovered value rest

theorem restore?_of_firstRecovered {value written : Json} (proposals : List (Json → Json))
    (h : firstRecovered value proposals = some written) :
    (restore? written).map content = some (content value) := by
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
the reader takes back to its content; without one, the value itself when the reader returns its
content from it, and otherwise the value as a `verbatim` member. -/
def internValue (proposals : List (Json → Json)) (value : Json) : Json :=
  match firstRecovered value proposals with
  | some written => written
  | none => if recovers value value then value else verbatim value

/-- **The reader recovers each value the writer was given.** For every value and every list of
proposals, `restore?` of the written form is a value with the content of the value. -/
theorem restore?_internValue (proposals : List (Json → Json)) (value : Json) :
    (restore? (internValue proposals value)).map content = some (content value) := by
  unfold internValue
  split
  next written found => exact restore?_of_firstRecovered proposals found
  next =>
    split
    next recovered => exact restore?_of_recovers recovered
    next => simp [restore?_verbatim]

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
of proposals, `expand` of what `intern` wrote is a document with the content of that document. -/
theorem expand_intern (proposals : List (Json → Json)) (document : Json) :
    (expand (intern proposals document)).map content = .ok (content document) := by
  obtain ⟨restored, found, same⟩ := Option.map_eq_some_iff.mp
    (restoreMembers_mapMembers accountKey (internValue proposals) restore?
      (restore?_internValue proposals) document)
  simp [expand, intern, found, Except.map, same]

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

/-- **A reader of a result file recovers the document its writer was given.** Whenever `write`
produces a value, `read` of it is a document with the content of the document, for every document
and every list of proposals. -/
theorem read_write {proposals : List (Json → Json)} {document written : Json}
    (h : write proposals document = .ok written) :
    (read written).map content = .ok (content document) := by
  have texts : SourceTexts.expand written = .ok (intern proposals document) :=
    SourceTexts.expand_intern h
  simp only [read, texts, bind, Except.bind]
  exact expand_intern proposals document

/-- Whether a written account is a shared form whose every root entry is derived from the shared
part alone: none lists its `visits` and none is `explicit`. An observation for controls; no law
depends on it. -/
def derivedOnly (written : Json) : Bool :=
  match field? rootsKey written with
  | some (.arr entries) =>
      (graphOf? written).isSome && !entries.isEmpty && entries.all fun entry =>
        (field? "explicit" entry).isNone && (field? "visits" entry).isNone
  | _ => false

end Regula.SharedExecution
