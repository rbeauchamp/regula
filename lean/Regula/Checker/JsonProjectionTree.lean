import Lean
import Std.Data.TreeMap.Raw.AdditionalOperations

/-! # JSON tree value-map laws

Structural value-map laws for raw JSON objects. These do not assume the raw
tree is ordered or balanced; keys and tree shape are preserved, including malformed
trees. They support the corpus adapter's qualification-only payload view. -/
namespace Regula.Checker.JsonProjectionTree
open Lean Std.DTreeMap.Internal
open Std.DTreeMap.Internal.Impl

private theorem map_balanceL (f : String → Json → Json) (k : String) (v : Json)
    (l r : Impl String (fun _ => Json)) :
    (balanceL! k v l r).map f = balanceL! k (f k v) (l.map f) (r.map f) := by
  unfold balanceL!
  repeat' first
    | rfl
    | simp_all only [gt_iff_lt, Std.DHashMap.Internal.AssocList.panicWithPosWithDecl_eq,
        Impl.map, size_map]
    | split

private theorem map_balanceR (f : String → Json → Json) (k : String) (v : Json)
    (l r : Impl String (fun _ => Json)) :
    (balanceR! k v l r).map f = balanceR! k (f k v) (l.map f) (r.map f) := by
  unfold balanceR!
  repeat' first
    | rfl
    | simp_all only [gt_iff_lt, Std.DHashMap.Internal.AssocList.panicWithPosWithDecl_eq,
        Impl.map, size_map]
    | split

private theorem map_insertImpl (f : String → Json → Json) (k : String) (v : Json)
    (t : Impl String (fun _ => Json)) :
    (t.insert! k v).map f = (t.map f).insert! k (f k v) := by
  induction t with
  | leaf => rfl
  | inner sz key value left right hl hr =>
    simp only [Impl.insert!, Impl.map]
    split <;> simp_all [map_balanceL, map_balanceR, Impl.map]

private theorem get_mapImpl (f : String → Json → Json) (k : String)
    (t : Impl String (fun _ => Json)) :
    Impl.Const.get? (t.map f) k = (Impl.Const.get? t k).map (f k) := by
  induction t with
  | leaf => rfl
  | inner sz key value left right hl hr =>
    simp only [Impl.map, Impl.Const.get?]
    split <;> simp_all

/-- Value mapping commutes with insertion even for a malformed raw tree. -/
theorem map_insert (f : String → Json → Json) (t : Std.TreeMap.Raw String Json compare)
    (k : String) (v : Json) :
    (t.insert k v).map f = (t.map f).insert k (f k v) := by
  cases t with | mk inner =>
    cases inner with | mk inner =>
      exact congrArg (fun t => Std.TreeMap.Raw.mk (Std.DTreeMap.Raw.mk t))
        (map_insertImpl f k v inner)

/-- Lookup follows identical branches before and after value mapping, without WF. -/
theorem get_map (f : String → Json → Json) (t : Std.TreeMap.Raw String Json compare)
    (k : String) :
    (t.map f).get? k = (t.get? k).map (f k) := by
  exact get_mapImpl f k t.inner.inner

end Regula.Checker.JsonProjectionTree
