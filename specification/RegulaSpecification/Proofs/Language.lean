module

public import Regula.Language
public import RegulaSpecification.Language
import all Init.Data.Array.BinSearch
import all Init.Data.Ord.String
import all Init.Prelude
import all Lean.Data.Name
import all Regula.Language
import all Regula.LanguageSet

/-!
# The language decision against its record

Each theorem is about the definition that the checker runs. What fills a {name (full := Regula.Language.Reading)}`Reading` from a real project
(`Regula.Reader`) is in {lit}`Proofs/Reader.lean`, and the specification's trusted base lists what stays assumed.
-/

@[expose] public section

namespace RegulaSpecification.Language

open Lean (Name Syntax)
open Regula.Language
open LeanIntent

theorem contains_iff {α : Type} [BEq α] [LawfulBEq α] {l : List α} {x : α} :
    l.contains x = true ↔ x ∈ l := List.contains_iff_mem

/-- Whether adjacent elements strictly increase under {name}`lt`. -/
def isSorted {α : Type} (lt : α → α → Bool) : List α → Bool
  | [] | [_] => true
  | a :: b :: rest => lt a b && isSorted lt (b :: rest)

theorem pairwise_of_isSorted {α : Type} {lt : α → α → Bool}
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true) :
    ∀ {l : List α}, isSorted lt l = true → l.Pairwise (fun a b => lt a b = true)
  | [], _ => .nil
  | [_], _ => .cons (by simp) .nil
  | a :: b :: rest, h => by
    simp only [isSorted, Bool.and_eq_true] at h
    have hrest := pairwise_of_isSorted htrans h.2
    refine .cons ?_ hrest
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact htrans a b c h.1 ((List.pairwise_cons.mp hrest).1 c hc)

theorem getElem_lt_of_isSorted {α : Type} {lt : α → α → Bool}
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    {as : Array α} (h : isSorted lt as.toList = true) :
    ∀ (i j : Nat) (hi : i < as.size) (hj : j < as.size), i < j → lt as[i] as[j] = true := by
  have hp := List.pairwise_iff_getElem.mp (pairwise_of_isSorted htrans h)
  intro i j hi hj hij
  have h1 := hp i j (by simpa using hi) (by simpa using hj) hij
  simpa [Array.getElem_toList] using h1

theorem binSearchAux_iff {α : Type} {as : Array α} {lt : α → α → Bool}
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hirrefl : ∀ a, lt a a = false)
    (htotal : ∀ a b, lt a b = false → lt b a = false → a = b)
    (hsorted : ∀ (i j : Nat) (hi : i < as.size) (hj : j < as.size), i < j → lt as[i] as[j] = true)
    (k : α) :
    ∀ (d : Nat) (lo : Fin (as.size + 1)) (hi : Fin as.size) (hle : lo.1 ≤ hi.1),
      hi.1 - lo.1 ≤ d →
      (Array.binSearchAux lt Option.isSome as k lo hi hle = true ↔
        ∃ (i : Nat) (h : i < as.size), lo.1 ≤ i ∧ i ≤ hi.1 ∧ as[i] = k)
  | d, lo, hi, hle, hd => by
    unfold Array.binSearchAux
    have hm_lt : (lo.1 + hi.1) / 2 < as.size := by omega
    dsimp only
    let m := (lo.1 + hi.1) / 2
    let a := as[m]'hm_lt
    have hlt_left : ∀ (i : Nat) (hi' : i < as.size), i ≤ m → lt a k = true → as[i] ≠ k := by
      intro i hi' him hlak heq
      subst heq
      rcases Nat.lt_or_eq_of_le him with hlt | rfl
      · have h1 := hsorted i m hi' hm_lt hlt
        have h2 := htrans _ _ _ h1 hlak
        rw [hirrefl] at h2
        cases h2
      · rw [hirrefl] at hlak
        cases hlak
    have hlt_right : ∀ (i : Nat) (hi' : i < as.size), m ≤ i → lt k a = true → as[i] ≠ k := by
      intro i hi' hmi hlka heq
      subst heq
      rcases Nat.lt_or_eq_of_le hmi with hlt | rfl
      · have h1 := hsorted m i hm_lt hi' hlt
        have h2 := htrans _ _ _ hlka h1
        rw [hirrefl] at h2
        cases h2
      · rw [hirrefl] at hlka
        cases hlka
    cases h1 : lt a k with
    | true =>
      simp only [↓reduceIte]
      split
      · rename_i h'
        cases d with
        | zero => omega
        | succ d' =>
          rw [binSearchAux_iff htrans hirrefl htotal hsorted k d' ⟨m + 1, by omega⟩ hi h' (by simp; omega)]
          constructor
          · rintro ⟨i, hi', hlo, hhi, heq⟩
            exact ⟨i, hi', by dsimp only at hlo; omega, hhi, heq⟩
          · rintro ⟨i, hi', hlo, hhi, heq⟩
            have hgt : m < i := by
              refine Nat.lt_of_not_le fun him => hlt_left i hi' him h1 heq
            exact ⟨i, hi', by dsimp only; omega, hhi, heq⟩
      · rename_i h'
        simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
        rintro ⟨i, hi', hlo, hhi, heq⟩
        exact hlt_left i hi' (by omega) h1 heq
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases h2 : lt k a with
      | true =>
        simp only [↓reduceIte]
        split
        · rename_i h'
          simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
          rintro ⟨i, hi', hlo, hhi, heq⟩
          exact hlt_right i hi' (by omega) h2 heq
        · rename_i h'
          cases d with
          | zero => omega
          | succ d' =>
            rw [binSearchAux_iff htrans hirrefl htotal hsorted k d' lo ⟨m - 1, by omega⟩ (by simp; omega) (by simp; omega)]
            constructor
            · rintro ⟨i, hi', hlo, hhi, heq⟩
              exact ⟨i, hi', hlo, by dsimp only at hhi; omega, heq⟩
            · rintro ⟨i, hi', hlo, hhi, heq⟩
              have hlt : i < m := by
                refine Nat.lt_of_not_le fun hmi => hlt_right i hi' hmi h2 heq
              exact ⟨i, hi', hlo, by dsimp only; omega, heq⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.isSome_some, true_iff]
        exact ⟨m, hm_lt, by omega, by omega, htotal a k h1 h2⟩

theorem binSearchContains_iff {α : Type} {as : Array α} {lt : α → α → Bool}
    (htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (hirrefl : ∀ a, lt a a = false)
    (htotal : ∀ a b, lt a b = false → lt b a = false → a = b)
    (hsorted : isSorted lt as.toList = true) (k : α) :
    as.binSearchContains k lt = true ↔ k ∈ as.toList := by
  unfold Array.binSearchContains
  by_cases h0 : 0 < as.size
  · have hhi : as.size - 1 < as.size := by omega
    simp only [h0, ↓reduceDIte, hhi, ↓reduceIte, Nat.zero_le]
    rw [binSearchAux_iff htrans hirrefl htotal (getElem_lt_of_isSorted htrans hsorted) k as.size _ _ _ (by simp)]
    constructor
    · rintro ⟨i, hi, -, -, rfl⟩
      exact Array.mem_toList_iff.mpr (Array.getElem_mem hi)
    · intro hm
      obtain ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hm)
      exact ⟨i, hi, Nat.zero_le _, by simp; omega, heq⟩
  · have hsz : as.size = 0 := by omega
    have hempty : as.toList = [] := List.eq_nil_of_length_eq_zero (by simpa using hsz)
    simp [h0, hempty]

theorem nameCmp_self (a : Name) : Name.cmp a a = .eq := by
  induction a with
  | anonymous => rfl
  | num p n ih =>
    simp [Name.cmp, ih]
  | str p s ih =>
    simp [Name.cmp, ih, Std.ReflCmp.compare_self]

theorem nameCmp_eq_iff (a b : Name) : Name.cmp a b = .eq ↔ a = b := by
  induction a generalizing b with
  | anonymous =>
    cases b <;> simp [Name.cmp]
  | num p₁ i₁ ih =>
    cases b with
    | anonymous => simp [Name.cmp]
    | str _ _ => simp [Name.cmp]
    | num p₂ i₂ =>
      simp only [Name.cmp, Name.num.injEq]
      cases h : Name.cmp p₁ p₂ with
      | eq => simp [(ih p₂).mp h, Std.LawfulEqCmp.compare_eq_iff_eq]
      | lt =>
        have hne : p₁ ≠ p₂ := fun he => by subst he; rw [nameCmp_self] at h; cases h
        simp [hne]
      | gt =>
        have hne : p₁ ≠ p₂ := fun he => by subst he; rw [nameCmp_self] at h; cases h
        simp [hne]
  | str p₁ s₁ ih =>
    cases b with
    | anonymous => simp [Name.cmp]
    | num _ _ => simp [Name.cmp]
    | str p₂ s₂ =>
      simp only [Name.cmp, Name.str.injEq]
      cases h : Name.cmp p₁ p₂ with
      | eq => simp [(ih p₂).mp h, Std.LawfulEqCmp.compare_eq_iff_eq]
      | lt =>
        have hne : p₁ ≠ p₂ := fun he => by subst he; rw [nameCmp_self] at h; cases h
        simp [hne]
      | gt =>
        have hne : p₁ ≠ p₂ := fun he => by subst he; rw [nameCmp_self] at h; cases h
        simp [hne]

theorem nameCmp_swap (a b : Name) : (Name.cmp a b).swap = Name.cmp b a := by
  induction a generalizing b with
  | anonymous =>
    cases b <;> rfl
  | num p₁ i₁ ih =>
    cases b with
    | anonymous => rfl
    | str _ _ => rfl
    | num p₂ i₂ =>
      simp only [Name.cmp, ← ih p₂]
      cases Name.cmp p₁ p₂ with
      | eq => exact (Std.OrientedCmp.eq_swap (cmp := (compare : Nat → Nat → Ordering))).symm
      | lt => rfl
      | gt => rfl
  | str p₁ s₁ ih =>
    cases b with
    | anonymous => rfl
    | num _ _ => rfl
    | str p₂ s₂ =>
      simp only [Name.cmp, ← ih p₂]
      cases Name.cmp p₁ p₂ with
      | eq => exact (Std.OrientedCmp.eq_swap (cmp := (compare : String → String → Ordering))).symm
      | lt => rfl
      | gt => rfl

theorem nameCmp_lt_trans {a b c : Name} (h1 : Name.cmp a b = .lt) (h2 : Name.cmp b c = .lt) :
    Name.cmp a c = .lt := by
  induction a generalizing b c with
  | anonymous =>
    cases b <;> cases c <;> simp [Name.cmp] at h1 h2 ⊢
  | num p₁ i₁ ih =>
    cases b with
    | anonymous => simp [Name.cmp] at h1
    | str _ _ =>
      cases c with
      | anonymous | num _ _ => simp [Name.cmp] at h2
      | str _ _ => rfl
    | num p₂ i₂ =>
      cases c with
      | anonymous => simp [Name.cmp] at h2
      | str _ _ => rfl
      | num p₃ i₃ =>
        simp only [Name.cmp] at h1 h2 ⊢
        cases hp1 : Name.cmp p₁ p₂ with
        | gt => rw [hp1] at h1; cases h1
        | eq =>
          have heq := (nameCmp_eq_iff p₁ p₂).mp hp1
          subst heq
          rw [hp1] at h1
          cases hp2 : Name.cmp p₁ p₃ with
          | gt => rw [hp2] at h2; cases h2
          | lt => rfl
          | eq =>
            rw [hp2] at h2
            dsimp only at h1 h2
            exact Std.TransCmp.lt_trans h1 h2
        | lt =>
          cases hp2 : Name.cmp p₂ p₃ with
          | gt => rw [hp2] at h2; cases h2
          | eq =>
            have heq := (nameCmp_eq_iff p₂ p₃).mp hp2
            subst heq
            simp [hp1]
          | lt => simp [ih hp1 hp2]
  | str p₁ s₁ ih =>
    cases b with
    | anonymous | num _ _ => simp [Name.cmp] at h1
    | str p₂ s₂ =>
      cases c with
      | anonymous | num _ _ => simp [Name.cmp] at h2
      | str p₃ s₃ =>
        simp only [Name.cmp] at h1 h2 ⊢
        cases hp1 : Name.cmp p₁ p₂ with
        | gt => rw [hp1] at h1; cases h1
        | eq =>
          have heq := (nameCmp_eq_iff p₁ p₂).mp hp1
          subst heq
          rw [hp1] at h1
          cases hp2 : Name.cmp p₁ p₃ with
          | gt => rw [hp2] at h2; cases h2
          | lt => rfl
          | eq =>
            rw [hp2] at h2
            dsimp only at h1 h2
            exact Std.TransCmp.lt_trans h1 h2
        | lt =>
          cases hp2 : Name.cmp p₂ p₃ with
          | gt => rw [hp2] at h2; cases h2
          | eq =>
            have heq := (nameCmp_eq_iff p₂ p₃).mp hp2
            subst heq
            simp [hp1]
          | lt => simp [ih hp1 hp2]

theorem nameLt_trans (a b c : Name) (h1 : Name.lt a b = true) (h2 : Name.lt b c = true) :
    Name.lt a c = true := by
  simp only [Name.lt, beq_iff_eq] at h1 h2 ⊢
  exact nameCmp_lt_trans h1 h2

theorem nameLt_irrefl (a : Name) : Name.lt a a = false := by
  simp [Name.lt, nameCmp_self]

theorem nameLt_total (a b : Name) (h1 : Name.lt a b = false) (h2 : Name.lt b a = false) : a = b := by
  simp only [Name.lt, beq_eq_false_iff_ne, ne_eq] at h1 h2
  have hswap := nameCmp_swap a b
  cases hc : Name.cmp a b with
  | eq => exact (nameCmp_eq_iff a b).mp hc
  | lt => exact absurd hc h1
  | gt =>
    rw [hc] at hswap
    exact absurd hswap.symm h2

theorem strLt_trans (a b c : String) (h1 : strLt a b = true) (h2 : strLt b c = true) :
    strLt a c = true := by
  simp only [strLt, decide_eq_true_eq] at h1 h2 ⊢
  exact String.lt_trans h1 h2

theorem strLt_irrefl (a : String) : strLt a a = false := by
  simp [strLt, String.lt_irrefl]

theorem strLt_total (a b : String) (h1 : strLt a b = false) (h2 : strLt b a = false) : a = b := by
  simp only [strLt, decide_eq_false_iff_not] at h1 h2
  exact String.le_antisymm (String.not_lt.mp h2) (String.not_lt.mp h1)

theorem kinds_sorted : isSorted Name.lt kinds = true := by decide +kernel
theorem leafKinds_sorted : isSorted Name.lt leafKinds = true := by decide +kernel
theorem atoms_sorted : isSorted strLt atoms = true := by decide +kernel

theorem isKind_iff (k : Name) : isKind k = true ↔ k ∈ kinds := by
  unfold isKind
  exact binSearchContains_iff nameLt_trans nameLt_irrefl nameLt_total (as := kindsArray) kinds_sorted k

theorem isLeafKind_iff (k : Name) : isLeafKind k = true ↔ k ∈ leafKinds := by
  unfold isLeafKind
  exact binSearchContains_iff nameLt_trans nameLt_irrefl nameLt_total (as := leafKindsArray) leafKinds_sorted k

theorem isAtom_iff (v : String) : isAtom v = true ↔ v ∈ atoms := by
  unfold isAtom
  exact binSearchContains_iff strLt_trans strLt_irrefl strLt_total (as := atomsArray) atoms_sorted v

theorem occurs_node {s : Syntax} {i k} {as : Array Syntax} :
    Occurs s (.node i k as) ↔ s = .node i k as ∨ (k ∉ leafKinds ∧ ∃ c ∈ as, Occurs s c) := by
  constructor
  · intro h
    cases h with
    | self => exact .inl rfl
    | child hk hc hs => exact .inr ⟨hk, _, hc, hs⟩
  · rintro (rfl | ⟨hk, c, hc, hs⟩)
    · exact .self _
    · exact .child hk hc hs

theorem occurs_leaf {s t : Syntax} (h : Occurs s t) (ht : ∀ i k as, t ≠ .node i k as) : s = t := by
  cases h with
  | self => rfl
  | child _ _ _ => exact absurd rfl (ht _ _ _)

theorem mem_positionsGo_iff (t : Syntax) (s : Syntax) :
    ∀ acc, s ∈ positionsGo acc t ↔ Occurs s t ∨ s ∈ acc := by
  induction t using Syntax.rec
    (motive_2 := fun as => ∀ acc, s ∈ positionsOfArrayGo acc as ↔ (∃ c ∈ as, Occurs s c) ∨ s ∈ acc)
    (motive_3 := fun l => ∀ acc, s ∈ positionsOfListGo acc l ↔ (∃ c ∈ l, Occurs s c) ∨ s ∈ acc) with
  | missing =>
    intro acc
    simp only [positionsGo, List.mem_cons]
    exact or_congr ⟨fun h => h ▸ .self _, fun h => occurs_leaf h (by intros; exact Syntax.noConfusion)⟩ Iff.rfl
  | node i k as ih =>
    intro acc
    rw [occurs_node]
    simp only [positionsGo]
    by_cases hk : k ∈ leafKinds
    · have hlk : isLeafKind k = true := (isLeafKind_iff k).mpr hk
      simp only [hlk, ↓reduceIte, List.mem_cons, hk, not_true_eq_false, false_and, or_false]
    · have hlk : isLeafKind k = false := by
        cases h : isLeafKind k with
        | false => rfl
        | true => exact absurd ((isLeafKind_iff k).mp h) hk
      simp only [hlk, Bool.false_eq_true, ↓reduceIte, ih, List.mem_cons, hk, not_false_eq_true, true_and]
      constructor
      · rintro (h | rfl | h)
        · exact .inl (.inr h)
        · exact .inl (.inl rfl)
        · exact .inr h
      · rintro ((rfl | h) | h)
        · exact .inr (.inl rfl)
        · exact .inl h
        · exact .inr (.inr h)
  | atom i v =>
    intro acc
    simp only [positionsGo, List.mem_cons]
    exact or_congr ⟨fun h => h ▸ .self _, fun h => occurs_leaf h (by intros; exact Syntax.noConfusion)⟩ Iff.rfl
  | ident i r n p =>
    intro acc
    simp only [positionsGo, List.mem_cons]
    exact or_congr ⟨fun h => h ▸ .self _, fun h => occurs_leaf h (by intros; exact Syntax.noConfusion)⟩ Iff.rfl
  | mk l ih =>
    simp only [positionsOfArrayGo, ih, List.mem_toArray]
  | nil =>
    simp [positionsOfListGo]
  | cons x xs hx hxs =>
    simp only [positionsOfListGo, hxs, hx, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h)
      · exact .inr h
    · rintro ((h | h) | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)

theorem mem_positions_iff (t : Syntax) (s : Syntax) : s ∈ positions t ↔ Occurs s t := by
  simp [positions, mem_positionsGo_iff]

theorem anonymous_not_reserved : ¬ ReservedName .anonymous := fun h => by cases h

theorem root_not_reserved : ¬ ReservedName (.str .anonymous "_root_") := by
  intro h
  generalize he : Name.str .anonymous "_root_" = x at h
  cases h with
  | underscore _ hne =>
    obtain ⟨hp, hs⟩ := Name.str.inj he
    subst hp
    exact hne (by rw [hs])
  | autoParam =>
    have := (Name.str.inj he).2
    exact absurd this (by decide)
  | str h =>
    have := (Name.str.inj he).1
    subst this
    exact anonymous_not_reserved h
  | num _ => cases he

theorem reservedName_iff (n : Name) : reservedName n = true ↔ ReservedName n := by
  induction n with
  | anonymous =>
    simp only [reservedName, Bool.false_eq_true, false_iff]
    intro h
    cases h
  | num p m ih =>
    simp only [reservedName, ih]
    exact ⟨.num, fun h => by cases h with | num h => exact h⟩
  | str p s ih =>
    by_cases hr : (p, s) = (Name.anonymous, "_root_")
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
      simp only [reservedName, Bool.false_eq_true, false_iff]
      exact root_not_reserved
    · have heq : reservedName (.str p s) =
          (s.front == '_' || s == "autoParam" || reservedName p) := by
        cases p with
        | anonymous =>
          have : s ≠ "_root_" := fun h => hr (by rw [h])
          simp [reservedName, this]
        | str _ _ => rfl
        | num _ _ => rfl
      rw [heq]
      simp only [Bool.or_eq_true, beq_iff_eq, ih]
      constructor
      · rintro ((h | rfl) | h)
        · exact .underscore h hr
        · exact .autoParam
        · exact .str h
      · intro h
        cases h with
        | underscore h _ => exact .inl (.inl h)
        | autoParam => exact .inl (.inr rfl)
        | str h => exact .inr h

theorem mem_targets_iff (as : Array Syntax) (n : Name) : n ∈ targets as ↔ TargetOf as n := by
  simp only [targets, List.mem_flatMap, TargetOf]
  constructor
  · rintro ⟨x, hx, hn⟩
    have hx' : x ∈ as := by simpa using hx
    match x, hx', hn with
    | .ident i r m p, hx', hn =>
      have : n = m := by simpa using hn
      subst this
      exact ⟨i, r, p, .inl hx'⟩
    | .node i' k xs, hx', hn =>
      by_cases hk : k = `null
      · subst hk
        simp only [List.mem_filterMap] at hn
        obtain ⟨y, hy, hm⟩ := hn
        match y, hy, hm with
        | .ident i r m p, hy, hm =>
          have : m = n := by simpa using hm
          subst this
          exact ⟨i, r, p, .inr ⟨i', xs, hx', by simpa using hy⟩⟩
        | .missing, _, hm => simp at hm
        | .atom .., _, hm => simp at hm
        | .node .., _, hm => simp at hm
      · simp [hk] at hn
    | .missing, _, hn => simp at hn
    | .atom .., _, hn => simp at hn
  · rintro ⟨i, r, p, h | ⟨i', xs, hx, hy⟩⟩
    · exact ⟨_, by simpa using h, by simp⟩
    · refine ⟨_, by simpa using hx, ?_⟩
      simp only [List.mem_filterMap]
      exact ⟨_, by simpa using hy, by simp⟩

theorem canActivate_iff (N n : Name) : canActivate N n = true ↔ CanActivate N n := by
  simp only [canActivate, List.any_eq_true, List.mem_range, CanActivate, targetComponents]
  have hdrop : (fun x => x == `_root_) = (fun x : Name => decide (x = `_root_)) := by
    funext x
    by_cases h : x = `_root_ <;> simp [h]
  rw [hdrop]
  constructor
  · rintro ⟨i, hi, hs⟩
    refine ⟨i + 1, by omega, by omega, ?_⟩
    simpa [List.isSuffixOf_iff_suffix] using hs
  · rintro ⟨i, h0, hi, hs⟩
    refine ⟨i - 1, by omega, ?_⟩
    have : i - 1 + 1 = i := by omega
    rw [this]
    simpa [List.isSuffixOf_iff_suffix] using hs

theorem identIn_iff (allowed : List Name) (as : Array Syntax) (n : Nat) :
    identIn allowed as n = true ↔ ∃ i r c p, as[n]? = some (.ident i r c p) ∧ c ∈ allowed := by
  unfold identIn
  match h : as[n]? with
  | none => simp
  | some .missing => simp
  | some (.atom ..) => simp
  | some (.node ..) => simp
  | some (.ident i r c p) =>
    simp only [contains_iff, Option.some.injEq, Syntax.ident.injEq]
    exact ⟨fun hc => ⟨_, _, _, _, ⟨rfl, rfl, rfl, rfl⟩, hc⟩,
      fun ⟨_, _, _, _, ⟨_, _, hc, _⟩, hm⟩ => hc ▸ hm⟩

theorem noArgument_iff (o : Option Syntax) :
    noArgument o = true ↔ ∃ i', o = some (.node i' `null #[]) := by
  match o with
  | none => simp [noArgument]
  | some .missing => simp [noArgument]
  | some (.atom ..) => simp [noArgument]
  | some (.ident ..) => simp [noArgument]
  | some (.node i k xs) =>
    by_cases hk : k = `null
    · subst hk
      constructor
      · intro h
        have : xs = #[] := by simpa [noArgument] using h
        subst this
        exact ⟨i, rfl⟩
      · rintro ⟨i', h⟩
        cases Option.some.inj h
        simp [noArgument]
    · simp [noArgument, hk]

theorem argumentsAdmitted_iff (sp : List Name) (k : Name) (as : Array Syntax) :
    argumentsAdmitted sp k as = true ↔
      (k = `Lean.Parser.Attr.simple →
        (∃ i r a p, as[0]? = some (.ident i r a p) ∧ a ∈ simpleAttributes) ∧
          ∃ i', as[1]? = some (.node i' `null #[])) ∧
      (k = `Lean.Parser.Command.set_option →
        ∃ i r o p, as[1]? = some (.ident i r o p) ∧ o ∈ options) ∧
      (k = `Lean.Parser.Tactic.posConfigItem →
        ∃ i r c p, as[1]? = some (.ident i r c p) ∧ c ∈ configItems) ∧
      (k = `Lean.Parser.Command.derivingClass →
        ∃ i r c p, as[1]? = some (.ident i r c p) ∧ c ∈ derivingClasses) ∧
      ((k = `Lean.Parser.Command.namespace ∨ k = `Lean.Parser.Command.openSimple) →
        ∀ n, TargetOf as n → ∀ N ∈ sp, ¬ CanActivate N n) := by
  have htargets : (targets as).all (fun n => sp.all fun N => !canActivate N n) = true ↔
      ∀ n, TargetOf as n → ∀ N ∈ sp, ¬ CanActivate N n := by
    simp only [List.all_eq_true, mem_targets_iff, Bool.not_eq_true', ← canActivate_iff,
      Bool.not_eq_true]
  unfold argumentsAdmitted
  by_cases h1 : k = `Lean.Parser.Attr.simple
  · subst h1
    simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, identIn_iff, noArgument_iff]
    exact ⟨fun h => ⟨fun _ => h, fun e => absurd e (by decide), fun e => absurd e (by decide),
        fun e => absurd e (by decide),
        fun e => e.elim (fun e => absurd e (by decide)) (fun e => absurd e (by decide))⟩,
      fun h => h.1 trivial⟩
  have b1 : (k == `Lean.Parser.Attr.simple) = false := by simpa using h1
  by_cases h2 : k = `Lean.Parser.Command.set_option
  · subst h2
    simp only [b1, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
    rw [identIn_iff]
    exact ⟨fun h => ⟨fun e => absurd e (by decide), fun _ => h, fun e => absurd e (by decide),
        fun e => absurd e (by decide),
        fun e => e.elim (fun e => absurd e (by decide)) (fun e => absurd e (by decide))⟩,
      fun h => h.2.1 trivial⟩
  have b2 : (k == `Lean.Parser.Command.set_option) = false := by simpa using h2
  by_cases h3 : k = `Lean.Parser.Tactic.posConfigItem
  · subst h3
    simp only [b1, b2, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
    rw [identIn_iff]
    exact ⟨fun h => ⟨fun e => absurd e (by decide), fun e => absurd e (by decide), fun _ => h,
        fun e => absurd e (by decide),
        fun e => e.elim (fun e => absurd e (by decide)) (fun e => absurd e (by decide))⟩,
      fun h => h.2.2.1 trivial⟩
  have b3 : (k == `Lean.Parser.Tactic.posConfigItem) = false := by simpa using h3
  by_cases h4 : k = `Lean.Parser.Command.derivingClass
  · subst h4
    simp only [b1, b2, b3, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
    rw [identIn_iff]
    exact ⟨fun h => ⟨fun e => absurd e (by decide), fun e => absurd e (by decide),
        fun e => absurd e (by decide), fun _ => h,
        fun e => e.elim (fun e => absurd e (by decide)) (fun e => absurd e (by decide))⟩,
      fun h => h.2.2.2.1 trivial⟩
  have b4 : (k == `Lean.Parser.Command.derivingClass) = false := by simpa using h4
  simp only [b1, b2, b3, b4, Bool.false_eq_true, ↓reduceIte]
  by_cases h5 : k = `Lean.Parser.Command.namespace ∨ k = `Lean.Parser.Command.openSimple
  · have b5 : (k == `Lean.Parser.Command.namespace || k == `Lean.Parser.Command.openSimple) = true := by
      simpa using h5
    simp only [b5, ↓reduceIte, htargets]
    exact ⟨fun h => ⟨fun e => absurd e h1, fun e => absurd e h2, fun e => absurd e h3,
        fun e => absurd e h4, fun _ => h⟩, fun h => h.2.2.2.2 h5⟩
  · have b5 : (k == `Lean.Parser.Command.namespace || k == `Lean.Parser.Command.openSimple) = false := by
      simpa [Bool.or_eq_false_iff, not_or] using h5
    simp only [b5, Bool.false_eq_true, ↓reduceIte, true_iff]
    exact ⟨fun e => absurd e h1, fun e => absurd e h2, fun e => absurd e h3, fun e => absurd e h4,
      fun e => absurd e h5⟩

theorem positionAdmitted_iff (sp : List Name) (s : Syntax) :
    positionAdmitted sp s = true ↔ PositionAdmitted sp s := by
  cases s with
  | missing => simp [positionAdmitted, PositionAdmitted]
  | atom i v => simp [positionAdmitted, PositionAdmitted, isAtom_iff]
  | ident i r n p =>
    simp only [positionAdmitted, PositionAdmitted, Bool.not_eq_true', ← reservedName_iff,
      Bool.not_eq_true]
  | node i k as =>
    simp only [positionAdmitted, PositionAdmitted, NodeAdmitted, Bool.and_eq_true, Bool.or_eq_true,
      isKind_iff, isLeafKind_iff, argumentsAdmitted_iff]

theorem offenders_eq_nil_iff (sp : List Name) (t : Syntax) :
    offenders sp t = [] ↔ TreeAdmitted sp t := by
  simp only [offenders, List.filter_eq_nil_iff, mem_positions_iff, TreeAdmitted, Bool.not_eq_true',
    ← positionAdmitted_iff]
  simp

theorem mem_offenders_iff (sp : List Name) (t s : Syntax) :
    s ∈ offenders sp t ↔ Occurs s t ∧ ¬ PositionAdmitted sp s := by
  simp [offenders, mem_positions_iff, ← positionAdmitted_iff]

theorem moduleFile_iff (h : Syntax) : moduleFile h = true ↔ ModuleFile h := by
  simp only [moduleFile, List.any_eq_true, mem_positions_iff, ModuleFile]
  constructor
  · rintro ⟨x, hx, hk⟩
    match x, hx, hk with
    | .node i k as, hx, hk =>
      have : k = `Lean.Parser.Module.moduleTk := by simpa [isNodeOf] using hk
      subst this
      exact ⟨i, as, hx⟩
    | .missing, _, hk => simp [isNodeOf] at hk
    | .atom .., _, hk => simp [isNodeOf] at hk
    | .ident .., _, hk => simp [isNodeOf] at hk
  · rintro ⟨i, as, hx⟩
    exact ⟨_, hx, by simp [isNodeOf]⟩

theorem readToEnd_iff (cs : List Syntax) : readToEnd cs = true ↔ ReadToEnd cs := by
  simp only [readToEnd, ReadToEnd]
  match h : cs.getLast? with
  | none => simp
  | some .missing => simp [isNodeOf]
  | some (.atom ..) => simp [isNodeOf]
  | some (.ident ..) => simp [isNodeOf]
  | some (.node i k as) =>
    simp only [isNodeOf, beq_iff_eq, Option.some.injEq, Syntax.node.injEq]
    exact ⟨fun hk => ⟨i, as, ⟨rfl, hk, rfl⟩⟩, fun ⟨_, _, _, hk, _⟩ => hk⟩

theorem fileAdmitted_iff (f : FileRead) : f.admitted = true ↔ FileAdmitted f := by
  simp only [FileRead.admitted, FileRead.offenders, Bool.and_eq_true, moduleFile_iff, readToEnd_iff,
    List.isEmpty_iff, List.flatMap_eq_nil_iff, List.mem_cons, forall_eq_or_imp, offenders_eq_nil_iff,
    FileAdmitted, and_assoc]

theorem closedNameChar_iff (c : Char) : closedNameChar c = true ↔ ClosedChar c := by
  simp [closedNameChar, ClosedChar, or_assoc]

theorem closedComponent_iff (s : String) : closedComponent s = true ↔ ClosedComponent s := by
  simp [closedComponent, ClosedComponent, closedNameChar_iff]

theorem closedModuleName_iff (n : Name) : closedModuleName n = true ↔ ClosedModuleName n := by
  induction n with
  | anonymous =>
    simp only [closedModuleName, Bool.false_eq_true, false_iff]
    intro h
    cases h
  | num p m _ =>
    simp only [closedModuleName, Bool.false_eq_true, false_iff]
    intro h
    cases h
  | str p s ih =>
    cases p with
    | anonymous =>
      simp only [closedModuleName, closedComponent_iff]
      exact ⟨.one, fun h => by
        cases h with
        | one hc => exact hc
        | more hp _ => cases hp⟩
    | str q t =>
      simp only [closedModuleName, closedComponent_iff, Bool.and_eq_true] at ih ⊢
      exact ⟨fun ⟨hp, hc⟩ => .more (ih.mp hp) hc, fun h => by
        cases h with
        | more hp hc => exact ⟨ih.mpr hp, hc⟩⟩
    | num q k =>
      simp only [closedModuleName, Bool.false_eq_true, false_iff]
      intro h
      cases h with
      | more hp _ => cases hp

theorem configKeyAdmitted_iff (k : Name) : configKeyAdmitted k = true ↔ ConfigKeyAdmitted k := by
  simp [configKeyAdmitted, ConfigKeyAdmitted, List.any_eq_true]

theorem configClosed_iff (r : Reading) : r.configClosed = true ↔ ConfigClosed r := by
  have h : (∀ k ∈ r.configKeys, k.getRoot = `require ∨ ConfigKeyAdmitted k) ↔
      ∀ k ∈ r.configKeys, ¬ k.getRoot = `require → ConfigKeyAdmitted k :=
    forall_congr' fun k => forall_congr' fun _ => by
      by_cases hk : k.getRoot = `require <;> simp [hk]
  simp [Reading.configClosed, ConfigClosed, configKeyAdmitted_iff, and_assoc, h]

theorem readInFull_iff (r : Reading) : r.readInFull = true ↔ ReadInFull r := by
  simp [Reading.readInFull, ReadInFull]

theorem requiresDependency_iff (r : Reading) :
    r.requiresDependency = true ↔ RequiresDependency r := by
  simp [Reading.requiresDependency, RequiresDependency]

theorem mathlibReached_iff (r : Reading) : r.mathlibReached = true ↔ MathlibReached r := by
  simp [Reading.mathlibReached, MathlibReached]

theorem covered_iff (r : Reading) : r.covered = true ↔ Covered r := by
  simp [Reading.covered, Covered, closedModuleName_iff, and_assoc]

theorem filesAdmitted_iff (r : Reading) : r.filesAdmitted = true ↔ FilesAdmitted r := by
  simp [Reading.filesAdmitted, FilesAdmitted, fileAdmitted_iff]

theorem decision_meets : languageRecord.Meets decision := by
  rw [language_meets_iff]
  have hn {b : Bool} {P : Prop} (h : b = true ↔ P) (hp : ¬ P) : b = false := by
    cases b
    · rfl
    · exact absurd (h.mp rfl) hp
  have base {r : Reading} (c : ConfigClosed r) (f : ReadInFull r) (k : ¬ RequiresDependency r) :
      r.configClosed = true ∧ r.readInFull = true ∧ r.requiresDependency = false :=
    ⟨(configClosed_iff r).mpr c, (readInFull_iff r).mpr f, hn (requiresDependency_iff r) k⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r c
    simp [decision, hn (configClosed_iff r) c]
  · intro r c f
    simp [decision, (configClosed_iff r).mpr c, hn (readInFull_iff r) f]
  · intro r c f k
    simp [decision, (configClosed_iff r).mpr c, (readInFull_iff r).mpr f,
      (requiresDependency_iff r).mpr k]
  · intro r c f k m
    obtain ⟨b1, b2, b3⟩ := base c f k
    simp [decision, b1, b2, b3, (mathlibReached_iff r).mpr m]
  · intro r c f k m v
    obtain ⟨b1, b2, b3⟩ := base c f k
    simp [decision, b1, b2, b3, hn (mathlibReached_iff r) m, hn (covered_iff r) v]
  · intro r c f k m v o
    obtain ⟨b1, b2, b3⟩ := base c f k
    simp [decision, b1, b2, b3, hn (mathlibReached_iff r) m, (covered_iff r).mpr v,
      hn (filesAdmitted_iff r) o]
  · intro r c f k m v o
    obtain ⟨b1, b2, b3⟩ := base c f k
    simp [decision, b1, b2, b3, hn (mathlibReached_iff r) m, (covered_iff r).mpr v,
      (filesAdmitted_iff r).mpr o]

theorem decision_admitted_iff (r : Reading) : decision r = .admitted ↔ Inside r :=
  admitted_iff decision_meets r

theorem no_files_not_admitted (r : Reading) (h : r.files = []) : decision r ≠ .admitted := by
  intro ha
  obtain ⟨-, -, -, -, ⟨hroots, hr, -, hc⟩, -⟩ := (decision_admitted_iff r).mp ha
  cases hl : r.roots with
  | nil => exact hroots hl
  | cons m rest =>
    have hm : m ∈ r.reached := hr m (by simp [hl])
    obtain ⟨f, hf, -⟩ := hc m hm
    simp [h] at hf

theorem mathlib_not_admitted (r : Reading) (h : MathlibReached r) : decision r ≠ .admitted :=
  fun ha => ((decision_admitted_iff r).mp ha).2.2.2.1 h

theorem dependency_not_admitted (r : Reading) (h : RequiresDependency r) : decision r ≠ .admitted :=
  fun ha => ((decision_admitted_iff r).mp ha).2.2.1 h

theorem open_path_not_admitted (r : Reading) (h : r.openPaths ≠ []) : decision r ≠ .admitted :=
  fun ha => h ((decision_admitted_iff r).mp ha).1.2.2.1

theorem unclosed_module_not_admitted (r : Reading) (m : Name) (hm : m ∈ r.reached)
    (hn : closedModuleName m = false) : decision r ≠ .admitted := fun ha => by
  have := ((decision_admitted_iff r).mp ha).2.2.2.2.1.2.2.1 m hm
  simp [(closedModuleName_iff m).mpr this] at hn

theorem offender_not_admitted (r : Reading) (f : FileRead) (hf : f ∈ r.files) (s t : Syntax)
    (ht : t = f.header ∨ t ∈ f.commands) (ho : s ∈ offenders f.scopedParsers t) :
    decision r ≠ .admitted := by
  intro ha
  obtain ⟨-, -, -, -, -, hfiles⟩ := (decision_admitted_iff r).mp ha
  have hadm : FileAdmitted f := hfiles f hf
  obtain ⟨hocc, hbad⟩ := (mem_offenders_iff _ _ _).mp ho
  rcases ht with rfl | ht
  · exact hbad (hadm.2.2.2.1 s hocc)
  · exact hbad (hadm.2.2.2.2 t ht s hocc)

theorem treeRelative_iff (base path rel : List String) :
    treeRelative base path = some rel ↔ TreeRelative base path rel := by
  simp only [treeRelative, TreeRelative]
  by_cases hp : base <+: path
  · obtain ⟨tail, rfl⟩ := hp
    have hpre : base.isPrefixOf (base ++ tail) = true := by simp [List.isPrefixOf_iff_prefix]
    simp only [hpre, ↓reduceIte, List.drop_left, List.append_cancel_left_eq]
    constructor
    · intro h
      split at h
      · rename_i hall
        have := Option.some.inj h
        subst this
        simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hall
        refine ⟨rfl, fun c hc => ?_⟩
        have := hall c hc
        simp_all
      · simp at h
    · rintro ⟨rfl, hc⟩
      have : (tail.all fun c => !c.isEmpty && c.front != '.') = true := by
        simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq]
        intro c h
        exact ⟨by simpa using (hc c h).1, (hc c h).2⟩
      exact ite_eq_left_iff.mpr (fun h => absurd this h)
  · have hnone : base.isPrefixOf path = false := by
      rw [← Bool.not_eq_true, List.isPrefixOf_iff_prefix]
      exact hp
    simp only [hnone, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff]
    rintro ⟨rfl, -⟩
    exact hp (List.prefix_append _ _)

/-- `..`, {lit}`.` and {lit}`.lake` are no components of what {name}`treeRelative` gives. A component may still hold a separator or be
absolute, for an argument that no real path is. -/
theorem treeRelative_no_parent {base path rel : List String} (h : treeRelative base path = some rel) :
    ".." ∉ rel ∧ "." ∉ rel ∧ ".lake" ∉ rel := by
  obtain ⟨-, hc⟩ := (treeRelative_iff base path rel).mp h
  refine ⟨fun m => (hc _ m).2 ?_, fun m => (hc _ m).2 ?_, fun m => (hc _ m).2 ?_⟩ <;> decide

/-- The gate over a monad that records its steps, as the specification reads it. -/
def traced : GateRun := fun o b v =>
  let tell (s : Step) : StateM (List Step) Unit := modify (s :: ·)
  let run := gate (m := StateM (List Step)) (tell .read *> pure o) (tell .build *> pure b)
    (tell .rules *> pure v)
  let (report, steps) := run.run []
  (report, steps.reverse)

theorem gate_meets : fullGateRecord.Meets traced := by
  rw [fullGate_meets_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

theorem fullGate_o2Run : O2Run fullGateRecord := o2Run_of_meets gate_meets

theorem gate_exit_zero_iff (r : Reading) (b : Bool) (v : Regula.Closed.Verdict) :
    (traced (decision r) b v).1.exitCode = 0 ↔
      Inside r ∧ b = true ∧ v = .pass := by
  rw [Report.exitCode_eq_zero_iff, ← decision_admitted_iff]
  obtain ⟨u1, u2, u3, u4, u5⟩ := (fullGate_meets_iff traced).mp gate_meets
  cases decision r <;> cases b <;> simp_all

end RegulaSpecification.Language
