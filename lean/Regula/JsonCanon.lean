import RegulaCore.JsonAgreement

/-! # The form of a JSON value the parser builds

`PolicyCodec.parse` builds each object with `Json.mkObj` from its members in the order of the text,
and `PolicyCodec.compress` writes the members of an object in the order of its tree, which for a
search tree is the order of their names. So the parse of the printed text of a value is `canon` of
it: each object tree rebuilt with `Json.mkObj` from its members in name order, their values in the
same form (`JsonRoundTrip.parse_compress`). `Canonical` is the form `canon` gives
(`canonical_canon`), and `canon` keeps a value in it (`Canonical.canon_eq`); `canon` of a value
whose object trees are search trees agrees with it (`Regular.canon_agree`). The tree `Json.mkObj`
builds from members in increasing name order lists them in that order (`members_treeOf`), and a
value map of a tree keeps its shape (`treeOf_map`), so a writer that builds its objects that way
and maps their values keeps the form (`ExecutionShare.canonical_write`). -/

namespace Regula.JsonCanon
open Lean JsonAgreement
open Std.DTreeMap.Internal (Impl)
open Std.DTreeMap.Internal.Impl

/-- The object tree `Json.mkObj` builds from a list of members. -/
theorem mkObj_tree (written : List (String × Json)) :
    Json.mkObj written = .obj ⟨⟨written.foldl (fun tree member => tree.insert! member.1 member.2)
      (.leaf : Fields)⟩⟩ := by
  simp only [Json.mkObj, Std.TreeMap.Raw.ofList, Std.DTreeMap.Raw.Const.ofList, Impl.Const.ofList]
  rw [Impl.Const.insertMany_eq_foldl]
  rfl

/-- Inserting a name after every name of a search tree puts its member last. -/
theorem members_insert! {tree : Fields} (wf : tree.WF) {key : String} {value : Json}
    (after : ∀ member ∈ members tree, compare member.1 key = .lt) :
    members (tree.insert! key value) = members tree ++ [(key, value)] := by
  have perm := toListModel_insert! (k := key) (v := value) wf.balanced wf.ordered
  have absent : Std.Internal.List.containsKey key tree.toListModel = false := by
    rw [Std.Internal.List.containsKey_eq_false_iff]
    intro member present
    have less := after (member.1, member.2) (List.mem_map.mpr ⟨member, present, rfl⟩)
    rw [beq_eq_false_iff_ne]
    rintro rfl
    simp at less
  rw [Std.Internal.List.insertEntry_of_containsKey_eq_false absent] at perm
  have sorted : Impl.Ordered (tree.insert! key value) := WF.ordered (WF.insert! wf)
  unfold Impl.Ordered at sorted
  have listed : (tree.insert! key value).toListModel = tree.toListModel ++ [⟨key, value⟩] := by
    refine List.Perm.eq_of_pairwise (le := fun a b => compare a.1 b.1 = .lt) ?_ sorted ?_
      (perm.trans (List.perm_append_singleton _ _).symm)
    · intro a b _ _ ab ba
      rw [Std.OrientedCmp.gt_of_lt ab] at ba
      cases ba
    · refine List.pairwise_append.mpr ⟨wf.ordered, List.pairwise_singleton _ _, ?_⟩
      intro a present b inSingle
      rw [List.mem_singleton.mp inSingle]
      exact after (a.1, a.2) (List.mem_map.mpr ⟨a, present, rfl⟩)
  simp [members, listed]

/-- The tree `Json.mkObj` builds from `written`: each member inserted in turn (`mkObj_eq`). -/
def treeOf (written : List (String × Json)) : Fields :=
  written.foldl (fun tree member => tree.insert! member.1 member.2) .leaf

theorem mkObj_eq (written : List (String × Json)) : Json.mkObj written = .obj ⟨⟨treeOf written⟩⟩ :=
  mkObj_tree written

theorem foldl_wf {tree : Fields} (wf : tree.WF) (rest : List (String × Json)) :
    (rest.foldl (fun tree member => tree.insert! member.1 member.2) tree).WF := by
  induction rest generalizing tree with
  | nil => exact wf
  | cons member rest step => exact step wf.insert!

theorem treeOf_wf (written : List (String × Json)) : (treeOf written).WF :=
  foldl_wf WF.empty written

theorem members_foldl {tree : Fields} (wf : tree.WF) (rest : List (String × Json))
    (increasing : Increasing (members tree ++ rest)) :
    members (rest.foldl (fun tree member => tree.insert! member.1 member.2) tree) =
      members tree ++ rest := by
  induction rest generalizing tree with
  | nil => simp
  | cons member rest step =>
    simp only [List.foldl_cons]
    have after : ∀ earlier ∈ members tree, compare earlier.1 member.1 = .lt := by
      intro earlier present
      simp only [Increasing, List.map_append, List.map_cons, List.pairwise_append,
        List.pairwise_cons] at increasing
      exact increasing.2.2 earlier.1 (List.mem_map_of_mem present) member.1 List.mem_cons_self
    have inserted := members_insert! (value := member.2) wf after
    rw [step wf.insert! (by rw [inserted]; simpa using increasing), inserted]
    simp

theorem members_treeOf {written : List (String × Json)} (increasing : Increasing written) :
    members (treeOf written) = written := by
  have := members_foldl (tree := .leaf) (by exact WF.empty) written
    (by simpa [members] using increasing)
  unfold treeOf
  simpa [members] using this

theorem treeOf_ordered (written : List (String × Json)) : JsonAgreement.Ordered (treeOf written) :=
  (treeOf_wf written).ordered

theorem size_map (g : String → Json → Json) (tree : Fields) :
    (tree.map g).size = tree.size := by
  cases tree <;> rfl

theorem map_balanceL! (g : String → Json → Json) (k : String) (v : Json) (l r : Fields) :
    (balanceL! k v l r).map g = balanceL! k (g k v) (l.map g) (r.map g) := by
  rcases r with ⟨rs, rk, rv, rl, rr⟩ | _ <;>
    rcases l with ⟨ls, lk, lv, ⟨lls, llk, llv, lll, llr⟩ | _, ⟨lrs, lrk, lrv, lrl, lrr⟩ | _⟩ | _ <;>
    simp only [balanceL!, Impl.map, size_map] <;>
    (repeat' split) <;> (try simp [Impl.map]) <;> rfl

theorem map_balanceR! (g : String → Json → Json) (k : String) (v : Json) (l r : Fields) :
    (balanceR! k v l r).map g = balanceR! k (g k v) (l.map g) (r.map g) := by
  rcases l with ⟨ls, lk, lv, ll, lr⟩ | _ <;>
    rcases r with ⟨rs, rk, rv, ⟨rls, rlk, rlv, rll, rlr⟩ | _, ⟨rrs, rrk, rrv, rrl, rrr⟩ | _⟩ | _ <;>
    simp only [balanceR!, Impl.map, size_map] <;>
    (repeat' split) <;> (try simp [Impl.map]) <;> rfl

theorem map_insert! (g : String → Json → Json) (k : String) (v : Json) (tree : Fields) :
    (tree.insert! k v).map g = (tree.map g).insert! k (g k v) := by
  induction tree with
  | leaf => rfl
  | inner sz k' v' l r hl hr =>
    simp only [insert!, Impl.map]
    split <;> simp [map_balanceL!, map_balanceR!, hl, hr, Impl.map]

theorem map_foldl (g : String → Json → Json) (tree : Fields) (rest : List (String × Json)) :
    (rest.foldl (fun tree member => tree.insert! member.1 member.2) tree).map g =
      (rest.map fun member => (member.1, g member.1 member.2)).foldl
        (fun tree member => tree.insert! member.1 member.2) (tree.map g) := by
  induction rest generalizing tree with
  | nil => rfl
  | cons member rest step => simp [step, map_insert!]

theorem treeOf_map (g : String → Json → Json) (written : List (String × Json)) :
    (treeOf written).map g = treeOf (written.map fun member => (member.1, g member.1 member.2)) :=
  map_foldl g .leaf written

/-! ### Members in the order of their names -/

/-- Put `member` into members whose names go up, at the place of its name: it replaces a member
of the same name. -/
def insertMember (member : String × Json) : List (String × Json) → List (String × Json)
  | [] => [member]
  | next :: rest =>
    match compare member.1 next.1 with
    | .lt => member :: next :: rest
    | .eq => member :: rest
    | .gt => next :: insertMember member rest

/-- `insertMember` with the members before the place kept in reverse order in `before`. It calls
itself last, so its stack depth does not grow with the number of members. -/
def insertMemberTR (member : String × Json) (before : List (String × Json)) :
    List (String × Json) → List (String × Json)
  | [] => before.reverseAux [member]
  | next :: rest =>
    match compare member.1 next.1 with
    | .lt => before.reverseAux (member :: next :: rest)
    | .eq => before.reverseAux (member :: rest)
    | .gt => insertMemberTR member (next :: before) rest

theorem insertMemberTR_eq (member : String × Json) (before sorted : List (String × Json)) :
    insertMemberTR member before sorted = before.reverseAux (insertMember member sorted) := by
  induction sorted generalizing before with
  | nil => rfl
  | cons next rest step =>
    simp only [insertMemberTR, insertMember]
    split
    · rfl
    · rfl
    · rw [step]
      rfl

/-- `insertMember` as the compiled code runs it (`insertMember_eq_insertMemberImpl`). -/
def insertMemberImpl (member : String × Json) (sorted : List (String × Json)) :
    List (String × Json) :=
  insertMemberTR member [] sorted

/-- The compiled code runs `insertMemberImpl` for `insertMember`, whose stack depth does not grow
with the number of members. -/
@[csimp] theorem insertMember_eq_insertMemberImpl : @insertMember = @insertMemberImpl := by
  funext member sorted
  rw [insertMemberImpl, insertMemberTR_eq]
  rfl

/-- The members with their names going up: the list itself when its names already go up, and
otherwise each member put in place in turn, the last member of each name kept. -/
def sortMembers (written : List (String × Json)) : List (String × Json) :=
  if ascending (written.map (·.1)) then written
  else written.foldl (fun sorted member => insertMember member sorted) []

theorem increasing_iff (written : List (String × Json)) :
    Increasing written ↔ written.Pairwise fun a b => compare a.1 b.1 = .lt := by
  simp [Increasing, List.pairwise_map]

theorem mem_insertMember {member other : String × Json} {sorted : List (String × Json)}
    (present : other ∈ insertMember member sorted) : other = member ∨ other ∈ sorted := by
  induction sorted with
  | nil => simpa [insertMember] using present
  | cons next rest step =>
    simp only [insertMember] at present
    split at present
    · simpa using present
    · simp only [List.mem_cons] at present
      rcases present with rfl | inRest
      · exact .inl rfl
      · exact .inr (List.mem_cons_of_mem _ inRest)
    · simp only [List.mem_cons] at present
      rcases present with rfl | inRest
      · exact .inr List.mem_cons_self
      · rcases step inRest with rfl | inRest
        · exact .inl rfl
        · exact .inr (List.mem_cons_of_mem _ inRest)

theorem insertMember_increasing (member : String × Json) {sorted : List (String × Json)}
    (increasing : sorted.Pairwise fun a b => compare a.1 b.1 = .lt) :
    (insertMember member sorted).Pairwise fun a b => compare a.1 b.1 = .lt := by
  induction sorted with
  | nil => simp [insertMember]
  | cons next rest step =>
    rw [List.pairwise_cons] at increasing
    simp only [insertMember]
    split
    · rename_i less
      refine List.pairwise_cons.mpr ⟨fun other present => ?_, List.pairwise_cons.mpr increasing⟩
      rcases List.mem_cons.mp present with rfl | inRest
      · exact less
      · exact Std.TransCmp.lt_trans less (increasing.1 other inRest)
    · rename_i same
      obtain same : member.1 = next.1 := Std.LawfulEqCmp.eq_of_compare same
      refine List.pairwise_cons.mpr ⟨fun other present => ?_, increasing.2⟩
      rw [same]
      exact increasing.1 other present
    · rename_i greater
      refine List.pairwise_cons.mpr ⟨fun other present => ?_, step increasing.2⟩
      rcases mem_insertMember present with rfl | inRest
      · exact Std.OrientedCmp.lt_of_gt greater
      · exact increasing.1 other inRest

theorem sortMembers_increasing (written : List (String × Json)) :
    Increasing (sortMembers written) := by
  rw [increasing_iff]
  unfold sortMembers
  split
  · rename_i up
    rw [ascending_iff, List.pairwise_map] at up
    exact up
  · suffices ∀ (rest sorted : List (String × Json)),
        sorted.Pairwise (fun a b => compare a.1 b.1 = .lt) →
        (rest.foldl (fun sorted member => insertMember member sorted) sorted).Pairwise
          (fun a b => compare a.1 b.1 = .lt) from this written [] List.Pairwise.nil
    intro rest
    induction rest with
    | nil => exact fun _ h => h
    | cons member rest step => exact fun sorted h => step _ (insertMember_increasing member h)

theorem mem_sortMembers {written : List (String × Json)} {member : String × Json}
    (present : member ∈ sortMembers written) : member ∈ written := by
  unfold sortMembers at present
  split at present
  · exact present
  · suffices ∀ (rest sorted : List (String × Json)),
        member ∈ rest.foldl (fun sorted member => insertMember member sorted) sorted →
        member ∈ sorted ∨ member ∈ rest from (this written [] present).resolve_left (by simp)
    intro rest
    induction rest with
    | nil => exact fun _ h => .inl h
    | cons next rest step =>
      intro sorted h
      rcases step _ h with inserted | inRest
      · rcases mem_insertMember inserted with rfl | inSorted
        · exact .inr List.mem_cons_self
        · exact .inl inSorted
      · exact .inr (List.mem_cons_of_mem _ inRest)

theorem sortMembers_of_increasing {written : List (String × Json)}
    (increasing : Increasing written) : sortMembers written = written := by
  have up : ascending (written.map (·.1)) = true := (ascending_iff _).mpr increasing
  simp [sortMembers, up]

/-! ### The form the parser builds -/

mutual
/-- The value `j` with each object tree rebuilt as the strict parser builds it: its members in the
order of their names (`sortMembers`), inserted in turn (`Json.mkObj`). Its stack depth grows with
the nesting of `j` and the height of its object trees, not with the length of an array or the size
of an object: `canonAll` and `insertMemberTR` (which runs for `insertMember`) call themselves last,
which the pinned compiler emits as a jump. -/
def canon (j : Json) : Json :=
  match j with
  | .arr ⟨elems⟩ => .arr ⟨canonAll elems []⟩
  | .obj ⟨⟨fields⟩⟩ => Json.mkObj (sortMembers (canonFields fields))
  | .null => .null
  | .bool b => .bool b
  | .num n => .num n
  | .str s => .str s
termination_by structural j
/-- `canon` of each element of `elems`, after the values `done` holds in reverse order. It calls
itself last, so its stack depth does not grow with the length of an array. -/
def canonAll (elems : List Json) (done : List Json) : List Json :=
  match elems with
  | [] => done.reverse
  | j :: rest => canonAll rest (canon j :: done)
termination_by structural elems
/-- The members of a tree in its order, each value `canon` of the member's. -/
def canonFields (fields : Fields) : List (String × Json) :=
  match fields with
  | .leaf => []
  | .inner _ k v l r => canonFields l ++ (k, canon v) :: canonFields r
termination_by structural fields
end

theorem canonAll_eq (elems done : List Json) :
    canonAll elems done = done.reverse ++ elems.map canon := by
  induction elems generalizing done with
  | nil => simp [canonAll]
  | cons j rest step => simp [canonAll, step]

theorem canonFields_eq (fields : Fields) :
    canonFields fields = (members fields).map fun member => (member.1, canon member.2) := by
  induction fields with
  | leaf => simp [canonFields]
  | inner size key value left right hl hr => simp [canonFields, hl, hr]

theorem canon_arr (elems : Array Json) : canon (.arr elems) = .arr (elems.map canon) := by
  obtain ⟨elems⟩ := elems
  simp [canon, canonAll_eq]

theorem canon_obj (fields : Fields) :
    canon (.obj ⟨⟨fields⟩⟩) =
      Json.mkObj (sortMembers ((members fields).map fun member => (member.1, canon member.2))) := by
  simp [canon, canonFields_eq]

/-- Each object tree in the value is the tree the strict parser builds for its members: their
names go up, and they are inserted in turn (`Json.mkObj`). -/
inductive Canonical : Json → Prop
  /-- `null` has no object. -/
  | null : Canonical .null
  /-- A Boolean has no object. -/
  | bool (value : Bool) : Canonical (.bool value)
  /-- A number has no object. -/
  | num (value : JsonNumber) : Canonical (.num value)
  /-- A string has no object. -/
  | str (value : String) : Canonical (.str value)
  /-- An array of values with this property. -/
  | arr {elements : Array Json} : (∀ value ∈ elements, Canonical value) →
      Canonical (.arr elements)
  /-- The object built from members whose names go up and whose values have this property. -/
  | obj {written : List (String × Json)} : Increasing written →
      (∀ member ∈ written, Canonical member.2) → Canonical (Json.mkObj written)

theorem canonical_canon (j : Json) : Canonical (canon j) := by
  refine Cases.value (motive := fun j => Canonical (canon j))
    (fieldsMotive := fun fields => ∀ member ∈ members fields, Canonical (canon member.2))
    ⟨.null, .bool, .num, .str, ?_, ?_, ?_, ?_⟩ j
  · intro elems each
    rw [canon_arr]
    refine .arr fun value present => ?_
    obtain ⟨original, inside, rfl⟩ := Array.mem_map.mp present
    exact each original inside
  · intro fields each
    rw [canon_obj]
    refine .obj (sortMembers_increasing _) fun member present => ?_
    obtain ⟨original, inside, rfl⟩ := List.mem_map.mp (mem_sortMembers present)
    exact each original inside
  · intro member present
    exact nomatch present
  · intro size key value left right here lefts rights member present
    simp only [members_inner, List.mem_append, List.mem_cons] at present
    rcases present with inLeft | rfl | inRight
    · exact lefts member inLeft
    · exact here
    · exact rights member inRight

theorem Canonical.canon_eq {j : Json} (canonical : Canonical j) : canon j = j := by
  induction canonical with
  | null => rfl
  | bool value => rfl
  | num value => rfl
  | str value => rfl
  | @arr elements _ step =>
    rw [canon_arr]
    congr 1
    conv => rhs; rw [← Array.map_id elements]
    exact Array.map_congr_left fun value present => step value present
  | @obj written increasing _ step =>
    rw [mkObj_eq, canon_obj, members_treeOf increasing]
    have same : (written.map fun member => (member.1, canon member.2)) = written := by
      conv => rhs; rw [← List.map_id written]
      exact List.map_congr_left fun member present => by rw [step member present]; rfl
    rw [same, sortMembers_of_increasing increasing, mkObj_eq]

theorem Canonical.regular {j : Json} (canonical : Canonical j) : Regular j := by
  induction canonical with
  | null => exact .null
  | bool value => exact .bool value
  | num value => exact .num value
  | str value => exact .str value
  | arr _ step => exact .arr step
  | @obj written increasing _ step =>
    rw [mkObj_eq]
    exact .obj (treeOf_ordered written) fun member present =>
      step member (members_treeOf increasing ▸ present)

theorem increasing_members {fields : Fields} (ordered : JsonAgreement.Ordered fields)
    (g : String → Json → Json) :
    Increasing ((members fields).map fun member => (member.1, g member.1 member.2)) := by
  rw [ordered_iff] at ordered
  simpa [Increasing, List.pairwise_map] using ordered

theorem canon_obj_of_ordered {fields : Fields} (ordered : JsonAgreement.Ordered fields) :
    canon (.obj ⟨⟨fields⟩⟩) =
      .obj ⟨⟨treeOf ((members fields).map fun member => (member.1, canon member.2))⟩⟩ := by
  rw [canon_obj, sortMembers_of_increasing (increasing_members ordered fun _ value => canon value),
    mkObj_eq]

theorem agreeAll_map {elems : List Json} (each : ∀ value ∈ elems, Agree (canon value) value) :
    AgreeAll (elems.map canon) elems := by
  induction elems with
  | nil => exact .nil
  | cons head rest step =>
    exact .cons (each head List.mem_cons_self)
      (step fun value inside => each value (List.mem_cons_of_mem _ inside))

/-- **The parser's form of a value whose object trees are search trees agrees with it.** -/
theorem Regular.canon_agree {j : Json} (regular : Regular j) : Agree (canon j) j := by
  induction regular with
  | null => exact .null
  | bool value => exact .bool value
  | num value => exact .num value
  | str value => exact .str value
  | @arr elements _ step =>
    obtain ⟨elements⟩ := elements
    show Agree (.arr ⟨canonAll elements []⟩) (.arr ⟨elements⟩)
    rw [canonAll_eq, List.reverse_nil, List.nil_append]
    exact .arr (agreeAll_map fun value inside => step value (Array.mem_def.mpr inside))
  | @obj fields ordered _ step =>
    rw [canon_obj_of_ordered ordered]
    have listed := members_treeOf (increasing_members ordered fun _ value => canon value)
    refine .obj ?_ ((agreeFields_iff _ _).mpr fun member present => ?_)
    · simp [count_eq_length, listed]
    · rw [listed] at present
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp present
      exact ⟨original.2, get?_of_mem ordered inside, step original inside⟩

theorem Canonical.obj_inv {j : Json} (canonical : Canonical j) {fields : Fields}
    (shape : j = .obj ⟨⟨fields⟩⟩) :
    ∃ written, fields = treeOf written ∧ Increasing written ∧
      ∀ member ∈ written, Canonical member.2 := by
  cases canonical with
  | obj increasing each =>
    rw [mkObj_eq] at shape
    cases shape
    exact ⟨_, rfl, increasing, each⟩
  | _ => cases shape

/-- A value map of a canonical object tree, whose new values are canonical, is canonical: the
tree's shape depends only on its names (`treeOf_map`). -/
theorem Canonical.map {fields : Fields} (canonical : Canonical (.obj ⟨⟨fields⟩⟩))
    (g : String → Json → Json) (each : ∀ member ∈ members fields, Canonical (g member.1 member.2)) :
    Canonical (.obj ⟨⟨fields.map g⟩⟩) := by
  obtain ⟨written, rfl, increasing, _⟩ := canonical.obj_inv rfl
  rw [treeOf_map, ← mkObj_eq]
  refine .obj (by simpa [Increasing, List.pairwise_map] using increasing) fun member present => ?_
  obtain ⟨original, inside, rfl⟩ := List.mem_map.mp present
  exact each original (by rw [members_treeOf increasing]; exact inside)

theorem Canonical.members {fields : Fields} (canonical : Canonical (.obj ⟨⟨fields⟩⟩)) :
    ∀ member ∈ JsonAgreement.members fields, Canonical member.2 := by
  obtain ⟨written, rfl, increasing, each⟩ := canonical.obj_inv rfl
  rw [members_treeOf increasing]
  exact each

theorem Canonical.elements {elements : Array Json} (canonical : Canonical (.arr elements)) :
    ∀ value ∈ elements, Canonical value := by
  cases canonical with
  | arr each => exact each

/-- The member a name finds in the parser's form of an object whose tree is a search tree is the
parser's form of the member it finds in the object. -/
theorem getObjVal?_canon {fields : Fields} (ordered : JsonAgreement.Ordered fields) (key : String) :
    (canon (.obj ⟨⟨fields⟩⟩)).getObjVal? key =
      (Json.getObjVal? (.obj ⟨⟨fields⟩⟩) key).map canon := by
  rw [canon_obj_of_ordered ordered]
  have listed := members_treeOf (increasing_members ordered fun _ value => canon value)
  have built := treeOf_ordered ((members fields).map fun member => (member.1, canon member.2))
  simp only [Json.getObjVal?]
  rcases found : (⟨⟨fields⟩⟩ : Std.TreeMap.Raw String Json compare).get? key with _ | value
  · rcases image : (⟨⟨treeOf ((members fields).map fun member => (member.1, canon member.2))⟩⟩ :
        Std.TreeMap.Raw String Json compare).get? key with _ | other
    · rw [image]
      rfl
    · exfalso
      have present := mem_of_get? image
      rw [listed] at present
      obtain ⟨original, inside, named⟩ := List.mem_map.mp present
      have := get?_of_mem ordered inside
      rw [show original.1 = key from congrArg Prod.fst named, found] at this
      cases this
  · have present := mem_of_get? found
    have image := get?_of_mem built (member := (key, canon value)) (by
      rw [listed]
      exact List.mem_map.mpr ⟨_, present, rfl⟩)
    simp only at image
    rw [image]
    rfl

/-- An object with one member whose value is canonical is canonical. -/
theorem Canonical.single {key : String} {value : Json} (canonical : Canonical value) :
    Canonical (.obj ⟨⟨.inner 1 key value .leaf .leaf⟩⟩) := by
  have built : Json.mkObj [(key, value)] = .obj ⟨⟨.inner 1 key value .leaf .leaf⟩⟩ := by
    rw [mkObj_eq]
    rfl
  rw [← built]
  exact .obj (by simp [Increasing]) fun member present => by
    rw [List.mem_singleton.mp present]
    exact canonical

end Regula.JsonCanon
