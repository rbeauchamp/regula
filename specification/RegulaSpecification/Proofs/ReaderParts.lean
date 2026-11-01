/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Effects
import RegulaSpecification.Proofs.Language

/-!
# What the parts of the reader give

For every response, about the definitions in `Regula.Reader`: the key paths of a TOML table, the modules a file's
parser sees, the commands of a file, and the modules of the default targets.
-/

namespace RegulaSpecification.Effects

open Lean (Name Syntax Import MessageLog)
open Lean.Parser (InputContext ModuleParserState isTerminalCommand)
open System (FilePath)
open Regula.Effect
open Regula.Language
open Regula.Reader
open RegulaSpecification.Language

variable {L E : Type}

/-! ## Key paths -/

/-- `tablesIn` holds exactly the tables of the array. -/
theorem mem_tablesIn {xs : Array Lake.Toml.Value} {sub : Lake.Toml.Table} :
    sub ∈ tablesIn xs ↔ ∃ r, Lake.Toml.Value.table r sub ∈ xs := by
  simp only [tablesIn, List.mem_filterMap, Array.mem_toList_iff]
  constructor
  · rintro ⟨x, hx, h⟩
    cases x <;> simp at h
    subst h
    exact ⟨_, hx⟩
  · rintro ⟨r, h⟩
    exact ⟨_, h, rfl⟩

/-- Each key the reader lists is a key path, unless the table is deeper than it follows. -/
theorem keysOf_sound (fuel : Nat) (pre : Name) (t : Lake.Toml.Table) (k : Name)
    (h : k ∈ keysOf fuel pre t) : KeyPath pre t k ∨ Deeper fuel t := by
  induction fuel generalizing pre t k with
  | zero => exact .inr .zero
  | succ fuel ih =>
    simp only [keysOf, List.mem_flatMap, Array.mem_toList_iff] at h
    obtain ⟨⟨tk, v⟩, hm, hk⟩ := h
    have under_sound : ∀ (sub : Lake.Toml.Table),
        k ∈ (if sub.items.isEmpty then [pre ++ tk] else keysOf fuel (pre ++ tk) sub) →
        (sub.items.isEmpty = true ∧ k = pre ++ tk) ∨ KeyPath (pre ++ tk) sub k ∨
          (sub.items.isEmpty = false ∧ Deeper fuel sub) := by
      intro sub hs
      cases he : sub.items.isEmpty with
      | true =>
        simp only [he, ite_true, List.mem_singleton] at hs
        exact .inl ⟨rfl, hs⟩
      | false =>
        simp only [he, Bool.false_eq_true, ite_false] at hs
        rcases ih _ _ _ hs with h' | h'
        · exact .inr (.inl h')
        · exact .inr (.inr ⟨rfl, h'⟩)
    cases v with
    | table' r sub =>
      rcases under_sound sub hk with ⟨he, rfl⟩ | h' | ⟨he, h'⟩
      · exact .inl (.empty hm he)
      · exact .inl (.under hm h')
      · exact .inr (.table hm he h')
    | array r xs =>
      simp only at hk
      split at hk
      · rename_i hempty
        have hk' : k = pre ++ tk := by simpa using hk
        subst hk'
        refine .inl (.leaf hm (by simp) ?_)
        rintro r' xs' he r'' sub hin
        cases he
        have hmem : sub ∈ tablesIn xs := mem_tablesIn.mpr ⟨_, hin⟩
        rw [List.isEmpty_iff.mp hempty] at hmem
        cases hmem
      · simp only [List.mem_flatMap] at hk
        obtain ⟨sub, hsub, hu⟩ := hk
        obtain ⟨r2, hx⟩ := mem_tablesIn.mp hsub
        rcases under_sound _ hu with ⟨he, rfl⟩ | h' | ⟨he, h'⟩
        · exact .inl (.emptyIn hm hx he)
        · exact .inl (.underIn hm hx h')
        · exact .inr (.array hm hx he h')
    | string r s | integer r i | float r f | boolean r b | dateTime r d =>
      have hk' : k = pre ++ tk := by simpa using hk
      subst hk'
      exact .inl (.leaf hm (by simp) (by simp))

/-- What the reader adds for a table deeper than it follows: a key whose last component is `too deep`. -/
def IsDeepKey (k : Name) : Prop :=
  ∃ pre, k = .str pre "too deep"

/-- A table deeper than the reader follows gives the key that says so. -/
theorem keysOf_deep {fuel : Nat} {pre : Name} {t : Lake.Toml.Table} (h : Deeper fuel t) :
    ∃ k ∈ keysOf fuel pre t, IsDeepKey k := by
  induction h generalizing pre with
  | zero => exact ⟨.str pre "too deep", by simp [keysOf], pre, rfl⟩
  | @table n k r sub t hm he _ ih =>
    obtain ⟨d, hd, hdeep⟩ := ih (pre := pre ++ k)
    refine ⟨d, ?_, hdeep⟩
    simp only [keysOf, List.mem_flatMap, Array.mem_toList_iff]
    exact ⟨(k, .table r sub), hm, by simpa [he] using hd⟩
  | @array n k r xs r' sub t hm hx he _ ih =>
    obtain ⟨d, hd, hdeep⟩ := ih (pre := pre ++ k)
    refine ⟨d, ?_, hdeep⟩
    simp only [keysOf, List.mem_flatMap, Array.mem_toList_iff]
    refine ⟨(k, .array r xs), hm, ?_⟩
    have hsub : sub ∈ tablesIn xs := mem_tablesIn.mpr ⟨_, hx⟩
    have hne : (tablesIn xs).isEmpty = false := by
      cases hl : tablesIn xs with
      | nil => rw [hl] at hsub; cases hsub
      | cons _ _ => rfl
    simp only [hne, Bool.false_eq_true, ite_false, List.mem_flatMap]
    exact ⟨sub, hsub, by simpa [he] using hd⟩

/-- Each key path is listed, or the reader's list holds the key that says the table is too deep. -/
theorem keysOf_complete {pre : Name} {t : Lake.Toml.Table} {n : Name} (h : KeyPath pre t n) :
    ∀ fuel, n ∈ keysOf fuel pre t ∨ ∃ k ∈ keysOf fuel pre t, IsDeepKey k := by
  induction h with
  | @leaf pre k v t hm hv ha =>
    intro fuel
    cases fuel with
    | zero => exact .inr ⟨.str pre "too deep", by simp [keysOf], pre, rfl⟩
    | succ fuel =>
      left
      simp only [keysOf, List.mem_flatMap, Array.mem_toList_iff]
      refine ⟨(k, v), hm, ?_⟩
      cases v with
      | table' r sub => exact absurd rfl (hv r sub)
      | array r xs =>
        have hnone : tablesIn xs = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro sub hsub
          obtain ⟨r2, hx⟩ := mem_tablesIn.mp hsub
          exact ha r xs rfl _ _ hx
        simp [hnone]
      | string | integer | float | boolean | dateTime => simp
  | @empty pre k r sub t hm he =>
    intro fuel
    cases fuel with
    | zero => exact .inr ⟨.str pre "too deep", by simp [keysOf], pre, rfl⟩
    | succ fuel =>
      left
      simp only [keysOf, List.mem_flatMap, Array.mem_toList_iff]
      exact ⟨(k, .table r sub), hm, by simp [he]⟩
  | @under pre k r sub t n hm hn ih =>
    intro fuel
    cases fuel with
    | zero => exact .inr ⟨.str pre "too deep", by simp [keysOf], pre, rfl⟩
    | succ fuel =>
      have hne : sub.items.isEmpty = false := by
        cases he : sub.items.isEmpty with
        | false => rfl
        | true =>
          exfalso
          have hnil : sub.items = #[] := Array.isEmpty_iff.mp he
          clear ih
          cases hn <;> simp_all
      have hin {x : Name} (hx : x ∈ keysOf fuel (pre ++ k) sub) : x ∈ keysOf (fuel + 1) pre t := by
        simp only [keysOf, List.mem_flatMap, Array.mem_toList_iff]
        exact ⟨(k, .table r sub), hm, by simpa [hne] using hx⟩
      rcases ih fuel with h' | ⟨d, hd, hdeep⟩
      · exact .inl (hin h')
      · exact .inr ⟨d, hin hd, hdeep⟩
  | @emptyIn pre k r xs r' sub t hm hx he =>
    intro fuel
    cases fuel with
    | zero => exact .inr ⟨.str pre "too deep", by simp [keysOf], pre, rfl⟩
    | succ fuel =>
      left
      simp only [keysOf, List.mem_flatMap, Array.mem_toList_iff]
      refine ⟨(k, .array r xs), hm, ?_⟩
      have hsub : sub ∈ tablesIn xs := mem_tablesIn.mpr ⟨_, hx⟩
      simp only
      split
      · simp
      · simp only [List.mem_flatMap]
        exact ⟨sub, hsub, by simp [he]⟩
  | @underIn pre k r xs r' sub t n hm hx hn ih =>
    intro fuel
    cases fuel with
    | zero => exact .inr ⟨.str pre "too deep", by simp [keysOf], pre, rfl⟩
    | succ fuel =>
      have hne : sub.items.isEmpty = false := by
        cases he : sub.items.isEmpty with
        | false => rfl
        | true =>
          exfalso
          have hnil : sub.items = #[] := Array.isEmpty_iff.mp he
          clear ih
          cases hn <;> simp_all
      have hsub : sub ∈ tablesIn xs := mem_tablesIn.mpr ⟨_, hx⟩
      have hin {x : Name} (hx' : x ∈ keysOf fuel (pre ++ k) sub) : x ∈ keysOf (fuel + 1) pre t := by
        simp only [keysOf, List.mem_flatMap, Array.mem_toList_iff]
        refine ⟨(k, .array r xs), hm, ?_⟩
        simp only
        split
        · rename_i hempty
          rw [List.isEmpty_iff.mp hempty] at hsub
          cases hsub
        · simp only [List.mem_flatMap]
          exact ⟨sub, hsub, by simpa [hne] using hx'⟩
      rcases ih fuel with h' | ⟨d, hd, hdeep⟩
      · exact .inl (hin h')
      · exact .inr ⟨d, hin hd, hdeep⟩

/-- The key that says a table is too deep is in no closed set. -/
theorem deepKey_not_admitted {k : Name} (h : IsDeepKey k) : ¬ ConfigKeyAdmitted k := by
  obtain ⟨pre, rfl⟩ := h
  have hlast : ∀ q : Name, (Name.str q "too deep").getString! = "too deep" := fun _ => rfl
  rintro (h | ⟨o, ho, he⟩)
  · have : ∀ k ∈ configKeys, k.getString! ≠ "too deep" := by decide +kernel
    exact this _ h (hlast pre)
  · have : ∀ o ∈ options, (`leanOptions ++ o).getString! ≠ "too deep" := by decide +kernel
    exact this o ho (he ▸ hlast pre)

/-! ## What a file's parser sees -/

/-- What the imports of the modules outside `seen` can still add to the search. -/
def remaining : List (Name × Array Import) → List Name → Nat
  | [], _ => 0
  | (k, v) :: hs, seen => (if seen.contains k then 0 else v.size) + remaining hs seen

theorem remaining_nil (hs : List (Name × Array Import)) :
    remaining hs [] = (hs.map (·.2.size)).sum := by
  induction hs with
  | nil => rfl
  | cons x hs ih =>
    obtain ⟨k, v⟩ := x
    simp [remaining, ih]

theorem remaining_mono (hs : List (Name × Array Import)) (seen : List Name) (m : Name) :
    remaining hs (m :: seen) ≤ remaining hs seen := by
  induction hs with
  | nil => exact Nat.le_refl _
  | cons x hs ih =>
    obtain ⟨k, v⟩ := x
    simp only [remaining]
    by_cases h1 : seen.contains k = true
    · have h2 : (m :: seen).contains k = true := by
        simp only [List.contains_cons, Bool.or_eq_true]
        exact .inr h1
      simp only [h1, h2, ite_true]
      omega
    · simp only [h1, Bool.false_eq_true, ite_false]
      split <;> omega

/-- Following a module once takes what it adds out of what remains. -/
theorem remaining_step (hs : List (Name × Array Import)) (seen : List Name) (m : Name)
    (hm : seen.contains m = false) :
    ((hs.lookup m).getD #[]).size + remaining hs (m :: seen) ≤ remaining hs seen := by
  induction hs with
  | nil => simp [remaining]
  | cons x hs ih =>
    obtain ⟨k, v⟩ := x
    simp only [remaining]
    by_cases hk : m = k
    · subst hk
      have h2 : (m :: seen).contains m = true := by simp
      simp only [List.lookup_cons_self, Option.getD_some, hm, h2, ite_true, Bool.false_eq_true, ite_false]
      have := remaining_mono hs seen m
      omega
    · have hne : (m == k) = false := by simpa using hk
      simp only [List.lookup_cons, hne]
      by_cases h1 : seen.contains k = true
      · have h2 : (m :: seen).contains k = true := by
          simp only [List.contains_cons, Bool.or_eq_true]
          exact .inr h1
        simp only [h1, h2, ite_true]
        omega
      · have h2 : (m :: seen).contains k = false := by
          simp only [List.contains_cons, Bool.or_eq_false_iff]
          have hk2 : ¬k = m := fun h => hk h.symm
          exact ⟨by simp [hk2], by simpa using h1⟩
        simp only [h1, h2, Bool.false_eq_true, ite_false]
        omega

/-- What the search gives, when `fuel` suffices: only the toolchain's modules, and a set `S` of the project's
modules it followed, so that each name of `todo` is in one or the other and what each followed module passes on
is too. -/
theorem visible_closed (hs : List (Name × Array Import)) (held : List Name) (fuel : Nat)
    (todo seen : List Name) (hf : todo.length + remaining hs seen ≤ fuel) :
    (∀ x ∈ visibleToolchain (fun n => hs.lookup n) held.contains todo seen fuel, x ∈ held) ∧
    ∃ S : List Name, (∀ m ∈ seen, m ∈ S) ∧
      (∀ m ∈ todo, m ∈ visibleToolchain (fun n => hs.lookup n) held.contains todo seen fuel ∨ m ∈ S) ∧
      ∀ s ∈ S, s ∉ seen → s ∉ held ∧ ∀ i ∈ (hs.lookup s).getD #[], i.isExported = true →
        i.module ∈ visibleToolchain (fun n => hs.lookup n) held.contains todo seen fuel ∨
          i.module ∈ S := by
  induction fuel generalizing todo seen with
  | zero =>
    have : todo = [] := by
      cases todo with
      | nil => rfl
      | cons _ _ => simp at hf
    subst this
    exact ⟨by simp [visibleToolchain], seen, fun _ h => h, by simp, fun _ h h' => absurd h h'⟩
  | succ fuel ih =>
    cases todo with
    | nil =>
      exact ⟨by simp [visibleToolchain], seen, fun _ h => h, by simp, fun _ h h' => absurd h h'⟩
    | cons m rest =>
      simp only [List.length_cons] at hf
      simp only [visibleToolchain]
      by_cases hm : held.contains m = true
      · simp only [hm, ite_true]
        obtain ⟨h1, S, h2, h3, h4⟩ := ih rest seen (by omega)
        refine ⟨?_, S, h2, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · simpa using hm
          · exact h1 x hx
        · intro n hn
          rcases List.mem_cons.mp hn with rfl | hn
          · exact .inl (List.mem_cons_self ..)
          · rcases h3 n hn with h | h
            · exact .inl (List.mem_cons_of_mem _ h)
            · exact .inr h
        · intro s hs' hns
          obtain ⟨h5, h6⟩ := h4 s hs' hns
          refine ⟨h5, fun i hi he => ?_⟩
          rcases h6 i hi he with h | h
          · exact .inl (List.mem_cons_of_mem _ h)
          · exact .inr h
      · simp only [hm, Bool.false_eq_true, ite_false]
        by_cases hsn : seen.contains m = true
        · simp only [hsn, ite_true]
          obtain ⟨h1, S, h2, h3, h4⟩ := ih rest seen (by omega)
          refine ⟨h1, S, h2, ?_, h4⟩
          intro n hn
          rcases List.mem_cons.mp hn with rfl | hn
          · exact .inr (h2 _ (by simpa using hsn))
          · exact h3 n hn
        · simp only [hsn, Bool.false_eq_true, ite_false]
          have hsn' : seen.contains m = false := by simpa using hsn
          have hstep := remaining_step hs seen m hsn'
          have hlen : (((hs.lookup m).getD #[]).toList.filter (·.isExported) |>.map (·.module)).length ≤
              ((hs.lookup m).getD #[]).size := by
            simp only [List.length_map]
            exact Nat.le_trans (List.length_filter_le _ _) (by simp)
          obtain ⟨h1, S, h2, h3, h4⟩ := ih
            ((((hs.lookup m).getD #[]).toList.filter (·.isExported) |>.map (·.module)) ++ rest) (m :: seen)
            (by simp only [List.length_append]; omega)
          refine ⟨h1, S, fun n hn => h2 n (List.mem_cons_of_mem _ hn), ?_, ?_⟩
          · intro n hn
            rcases List.mem_cons.mp hn with rfl | hn
            · exact .inr (h2 _ (List.mem_cons_self ..))
            · exact h3 n (List.mem_append_right _ hn)
          · intro s hs' hns
            by_cases hsm : s = m
            · subst hsm
              refine ⟨by simpa using hm, fun i hi he => ?_⟩
              refine h3 _ (List.mem_append_left _ ?_)
              simp only [List.mem_map, List.mem_filter]
              exact ⟨i, ⟨Array.mem_toList_iff.mpr hi, he⟩, rfl⟩
            · exact h4 s hs' (by simpa [hsm] using hns)

/-- What the search gives comes from a name of `todo` by `Sees`. -/
theorem visible_sound (hs : List (Name × Array Import)) (held : List Name) (fuel : Nat)
    (todo seen : List Name) (x : Name)
    (h : x ∈ visibleToolchain (fun n => hs.lookup n) held.contains todo seen fuel) :
    ∃ m ∈ todo, Sees hs held m x := by
  induction fuel generalizing todo seen with
  | zero => simp [visibleToolchain] at h
  | succ fuel ih =>
    cases todo with
    | nil => simp [visibleToolchain] at h
    | cons m rest =>
      simp only [visibleToolchain] at h
      by_cases hm : held.contains m = true
      · simp only [hm, ite_true] at h
        rcases List.mem_cons.mp h with rfl | h
        · exact ⟨x, List.mem_cons_self .., .self (by simpa using hm)⟩
        · obtain ⟨n, hn, hs'⟩ := ih rest seen h
          exact ⟨n, List.mem_cons_of_mem _ hn, hs'⟩
      · simp only [hm, Bool.false_eq_true, ite_false] at h
        by_cases hsn : seen.contains m = true
        · simp only [hsn, ite_true] at h
          obtain ⟨n, hn, hs'⟩ := ih rest seen h
          exact ⟨n, List.mem_cons_of_mem _ hn, hs'⟩
        · simp only [hsn, Bool.false_eq_true, ite_false] at h
          obtain ⟨n, hn, hs'⟩ := ih _ _ h
          rcases List.mem_append.mp hn with hn | hn
          · simp only [List.mem_map, List.mem_filter] at hn
            obtain ⟨i, ⟨hi, he⟩, rfl⟩ := hn
            cases hl : hs.lookup m with
            | none => simp [hl] at hi
            | some imports =>
              simp only [hl, Option.getD_some] at hi
              exact ⟨m, List.mem_cons_self .., .through (by simpa using hm) hl
                (Array.mem_toList_iff.mp hi) he hs'⟩
          · exact ⟨n, List.mem_cons_of_mem _ hn, hs'⟩

/-- The search gives exactly what `Sees` states from its first names, with the bound the reader gives it. So the
import asked for the parser names exactly the modules that `Sees` states, and that `Sees` is Lean's rule is H1. -/
theorem mem_visible_iff (hs : List (Name × Array Import)) (held direct : List Name) (fuel : Nat)
    (hf : direct.length + (hs.map (·.2.size)).sum ≤ fuel) (x : Name) :
    x ∈ visibleToolchain (fun n => hs.lookup n) held.contains direct [] fuel ↔
      ∃ m ∈ direct, Sees hs held m x := by
  refine ⟨visible_sound hs held fuel direct [] x, ?_⟩
  rintro ⟨m, hm, hsees⟩
  have hr : remaining hs [] = (hs.map (·.2.size)).sum := remaining_nil hs
  obtain ⟨h1, S, -, h3, h4⟩ := visible_closed hs held fuel direct [] (by rw [hr]; exact hf)
  have key : ∀ a b, Sees hs held a b →
      (a ∈ visibleToolchain (fun n => hs.lookup n) held.contains direct [] fuel ∨ a ∈ S) →
      b ∈ visibleToolchain (fun n => hs.lookup n) held.contains direct [] fuel := by
    intro a b hab
    induction hab with
    | self hn =>
      rintro (h | h)
      · exact h
      · exact absurd hn (h4 _ h (by simp)).1
    | @through a imports i b hna hl hi he _ ih =>
      rintro (h | h)
      · exact absurd (h1 _ h) hna
      · refine ih ?_
        have := (h4 _ h (by simp)).2 i (by simp [hl, hi]) he
        exact this
  exact key _ _ hsees (h3 m hm)

/-! ## The commands of a file -/

/-- `parseAll` gives what `Parsed` states of its events. -/
theorem parseAll_parsed (input : InputContext) (env : E) (state : ModuleParserState) (messages : MessageLog)
    (fuel : Nat) {t : List (Event L E)} {commands : List Syntax} {final : MessageLog}
    (h : Runs (parseAll input env state messages fuel) t (commands, final)) :
    Parsed input env fuel state messages commands final t := by
  induction fuel generalizing state messages t commands final with
  | zero =>
    obtain ⟨rfl, he⟩ := runs_pure_iff.mp h
    cases he
    exact .stop
  | succ fuel ih =>
    obtain ⟨t₁, t₂, ⟨stx, state', messages'⟩, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
    obtain rfl := runs_call_iff.mp h₁
    dsimp only at h₂
    split at h₂
    · rename_i hterm
      obtain ⟨rfl, he⟩ := runs_pure_iff.mp h₂
      cases he
      exact .last hterm
    · rename_i hterm
      obtain ⟨t₃, t₄, ⟨rest, final'⟩, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
      obtain ⟨rfl, he⟩ := runs_pure_iff.mp h₄
      cases he
      exact .next (by simpa using hterm) (by simpa using ih _ _ h₃)

/-! ## The modules of the default targets -/

/-- `defaultModules` gives what `DefaultModules` states of its events, or an answer of Lake failed. -/
theorem defaultModules_spec (root : Root L) (targets : List Name) {t T : List (Event L E)}
    {b : Except String (List (Name × FilePath))} (hT : ∀ e ∈ t, e ∈ T)
    (h : Runs (defaultModules root targets : Attempt L E _).run t b) :
    (∀ ms, b = .ok ms → DefaultModules T root targets ms) ∧
      ((∃ e, b = .error e) → ∃ target lib x, target ∈ targets ∧ root.findLib target = some lib ∧
        (⟨.libModules lib, .error x⟩ : Event L E) ∈ t) := by
  induction targets generalizing t b with
  | nil =>
    rw [defaultModules] at h
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h
    exact ⟨fun ms he => by cases he; exact .nil, fun ⟨e, he⟩ => by cases he⟩
  | cons target targets ih =>
    rw [defaultModules] at h
    obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
    have hT₁ : ∀ e ∈ t₁, e ∈ T := fun e he => hT e (List.mem_append_left _ he)
    have hT₂ : ∀ e ∈ t₂, e ∈ T := fun e he => hT e (List.mem_append_right _ he)
    have here : (∀ a, r = .ok a → ∀ ms, DefaultModules T root targets ms →
        DefaultModules T root (target :: targets) (a ++ ms)) ∧
        ((∃ e, r = .error e) → ∃ lib x, root.findLib target = some lib ∧
          (⟨.libModules lib, .error x⟩ : Event L E) ∈ t₁) := by
      rw [modulesOfTarget] at h₁
      cases hl : root.findLib target with
      | some lib =>
        simp only [hl] at h₁
        obtain ⟨t₃, t₄, r', rfl, h₃, h₄⟩ := runs_attempt_bind_iff.mp h₁
        obtain ⟨r'', h₅, rfl⟩ := runs_attempt_iff.mp h₃
        obtain rfl := runs_call_iff.mp h₅
        cases r'' with
        | ok listed =>
          obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₄
          refine ⟨fun a he ms hms => ?_, fun ⟨e, he⟩ => by cases he⟩
          cases he
          exact .lib hl (hT₁ _ (by simp)) hms
        | error e =>
          obtain ⟨rfl, rfl⟩ := h₄
          exact ⟨fun a he => (by cases he), fun _ => ⟨lib, e, rfl, by simp⟩⟩
      | none =>
        simp only [hl] at h₁
        cases he : root.findExe target with
        | some m =>
          simp only [he] at h₁
          obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₁
          refine ⟨fun a ha ms hms => ?_, fun ⟨e, h'⟩ => by cases h'⟩
          cases ha
          exact .exe hl he hms
        | none =>
          simp only [he] at h₁
          obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₁
          refine ⟨fun a ha ms hms => ?_, fun ⟨e, h'⟩ => by cases h'⟩
          cases ha
          exact .other hl he hms
    cases r with
    | error e =>
      obtain ⟨rfl, rfl⟩ := h₂
      refine ⟨fun ms he => (by cases he), fun _ => ?_⟩
      obtain ⟨lib, x, hl, hx⟩ := here.2 ⟨e, rfl⟩
      exact ⟨target, lib, x, List.mem_cons_self .., hl, by simpa using hx⟩
    | ok a =>
      obtain ⟨t₃, t₄, r', rfl, h₃, h₄⟩ := runs_attempt_bind_iff.mp h₂
      obtain ⟨i1, i2⟩ := ih (fun e he => hT₂ e (List.mem_append_left _ he)) h₃
      cases r' with
      | error e =>
        obtain ⟨rfl, rfl⟩ := h₄
        refine ⟨fun ms he => (by cases he), fun _ => ?_⟩
        obtain ⟨tg, lib, x, hg, hl, hx⟩ := i2 ⟨e, rfl⟩
        exact ⟨tg, lib, x, List.mem_cons_of_mem _ hg, hl, by simp [hx]⟩
      | ok rest =>
        obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₄
        refine ⟨fun ms he => ?_, fun ⟨e, he⟩ => by cases he⟩
        cases he
        exact here.1 a rfl rest (i1 rest rfl)

/-- `defaultModules` acts on nothing. -/
theorem defaultModules_no_act {root : Root L} {targets : List Name} {t : List (Event L E)}
    {b : Except String (List (Name × FilePath))}
    (h : Runs (defaultModules root targets : Attempt L E _).run t b) : ∀ e ∈ t, e.acted? = none := by
  induction targets generalizing t b with
  | nil =>
    rw [defaultModules] at h
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h
    intro e he
    cases he
  | cons target targets ih =>
    rw [defaultModules] at h
    obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
    have hhere : ∀ e ∈ t₁, e.acted? = none := by
      rw [modulesOfTarget] at h₁
      split at h₁
      · obtain ⟨t₃, t₄, r', rfl, h₃, h₄⟩ := runs_attempt_bind_iff.mp h₁
        obtain ⟨r'', h₅, rfl⟩ := runs_attempt_iff.mp h₃
        obtain rfl := runs_call_iff.mp h₅
        cases r'' with
        | ok a =>
          obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₄
          intro e he
          simp only [List.append_nil, List.mem_singleton] at he
          subst he
          rfl
        | error x =>
          obtain ⟨rfl, rfl⟩ := h₄
          intro e he
          simp only [List.append_nil, List.mem_singleton] at he
          subst he
          rfl
      · split at h₁ <;>
          · obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₁
            intro e he
            cases he
    cases r with
    | error x =>
      obtain ⟨rfl, rfl⟩ := h₂
      simpa using hhere
    | ok a =>
      obtain ⟨t₃, t₄, r', rfl, h₃, h₄⟩ := runs_attempt_bind_iff.mp h₂
      have hrest := ih h₃
      cases r' with
      | error x =>
        obtain ⟨rfl, rfl⟩ := h₄
        intro e he
        simp only [List.append_nil, List.mem_append] at he
        rcases he with he | he
        · exact hhere e he
        · exact hrest e he
      | ok rest =>
        obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₄
        intro e he
        simp only [List.append_nil, List.mem_append] at he
        rcases he with he | he
        · exact hhere e he
        · exact hrest e he

end RegulaSpecification.Effects
