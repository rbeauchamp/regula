import Std.Data.HashSet

/-!
# Reachability over names

The one search of the rules over the closed input (`Regula.Rules`): the constants that a constant
mentions, the constants that compiled code runs, and the departures. `reach` is total, and its fuel
is an argument, not a guess: each step of the search takes one name off its work list, and adds to
it only what `next` gives for a name that it has not seen, so the sum of the work list and of what
`next` gives for the unseen names falls by at least one at each step (`unseenWeight_insert`).
`mem_reach` states that the result is exactly the names that the seeds reach (`Reach`), for each
function `next` that gives names only for the names of `us`.
-/

namespace Regula.Closed
open Lean (Name)

/-- `e` is `s`, or a name that `next` gives from a name that `s` reaches. -/
inductive Reach (next : Name → List Name) (s : Name) : Name → Prop
  /-- `s` reaches itself. -/
  | refl : Reach next s s
  /-- `s` reaches what `next` gives for a name that it reaches. -/
  | step {b c : Name} : Reach next s b → c ∈ next b → Reach next s c

/-- The search: `seen` holds the names it has visited, and `work` those it has still to visit. -/
def reachGo (next : Name → List Name) : Nat → Std.HashSet Name → List Name → Std.HashSet Name
  | 0, seen, _ => seen
  | _ + 1, seen, [] => seen
  | k + 1, seen, n :: rest =>
    if seen.contains n then reachGo next k seen rest
    else reachGo next k (seen.insert n) (next n ++ rest)

/-- What `next` gives for the names of `us` that are not in `seen`. -/
def unseenWeight (next : Name → List Name) (us : List Name) (seen : Std.HashSet Name) : Nat :=
  ((us.filter fun n => !seen.contains n).map fun n => (next n).length).sum

/-- Marking `n` seen takes at least what `next` gives for `n` off the weight. -/
theorem unseenWeight_insert (next : Name → List Name) (us : List Name) (seen : Std.HashSet Name)
    (n : Name) (hn : next n ≠ [] → n ∈ us) (hs : seen.contains n = false) :
    unseenWeight next us (seen.insert n) + (next n).length ≤ unseenWeight next us seen := by
  unfold unseenWeight
  induction us with
  | nil =>
    have : next n = [] := Classical.byContradiction fun h => by simpa using hn h
    simp [this]
  | cons u us ih =>
    by_cases hun : u = n
    · subst hun
      have hmono :
          ((us.filter fun m => !(seen.insert u).contains m).map fun m => (next m).length).sum
          ≤ ((us.filter fun m => !seen.contains m).map fun m => (next m).length).sum := by
        clear ih hn
        induction us with
        | nil => simp
        | cons v vs ih =>
          simp only [List.filter_cons, Std.HashSet.contains_insert]
          by_cases h1 : seen.contains v = true
          · by_cases h2 : (u == v) = true <;> simp_all
          · by_cases h2 : (u == v) = true
            · simp_all; omega
            · simp_all
      rw [List.filter_cons_of_neg (by simp [Std.HashSet.contains_insert]),
        List.filter_cons_of_pos (by simp [hs])]
      simp only [List.map_cons, List.sum_cons]
      omega
    · have hn' : next n ≠ [] → n ∈ us := fun h => by
        rcases List.mem_cons.mp (hn h) with h' | h'
        · exact absurd h'.symm hun
        · exact h'
      have := ih hn'
      have hb : (n == u) = false := by simpa using fun h => hun h.symm
      simp only [List.filter_cons, Std.HashSet.contains_insert, hb, Bool.false_or]
      split <;> simp_all <;> omega

variable {next : Name → List Name}

/-- The search keeps each name it has seen. -/
theorem reachGo_mono (k : Nat) (seen : Std.HashSet Name) (work : List Name) (x : Name)
    (h : seen.contains x = true) : (reachGo next k seen work).contains x = true := by
  induction k generalizing seen work with
  | zero => simpa [reachGo]
  | succ k ih =>
    cases work with
    | nil => simpa [reachGo]
    | cons n rest =>
      simp only [reachGo]
      split
      · exact ih _ _ h
      · exact ih _ _ (by simp [Std.HashSet.contains_insert, h])

/-- Soundness: each name of the result is in `seen` or reached from `work`. -/
theorem reachGo_sound (P : Name → Prop) (hclosed : ∀ b, P b → ∀ c ∈ next b, P c)
    (k : Nat) (seen : Std.HashSet Name) (work : List Name)
    (hs : ∀ x, seen.contains x = true → P x) (hw : ∀ x ∈ work, P x) (x : Name)
    (h : (reachGo next k seen work).contains x = true) : P x := by
  induction k generalizing seen work with
  | zero => exact hs x (by simpa [reachGo] using h)
  | succ k ih =>
    cases work with
    | nil => exact hs x (by simpa [reachGo] using h)
    | cons n rest =>
      simp only [reachGo] at h
      split at h
      · exact ih _ _ hs (fun y hy => hw y (List.mem_cons_of_mem _ hy)) h
      · refine ih _ _ ?_ ?_ h
        · intro y hy
          rw [Std.HashSet.contains_insert] at hy
          rcases Bool.or_eq_true _ _ ▸ hy with h1 | h1
          · have : n = y := by simpa using h1
            exact this ▸ hw n (List.mem_cons_self ..)
          · exact hs y h1
        · intro y hy
          rcases List.mem_append.mp hy with h1 | h1
          · exact hclosed n (hw n (List.mem_cons_self ..)) y h1
          · exact hw y (List.mem_cons_of_mem _ h1)

/-- With enough fuel the search ends with a set that is closed under `next`. -/
theorem reachGo_closed (us : List Name) (hus : ∀ n, next n ≠ [] → n ∈ us)
    (k : Nat) (seen : Std.HashSet Name) (work : List Name)
    (hk : work.length + unseenWeight next us seen < k + 1)
    (hc : ∀ x, seen.contains x = true → ∀ y ∈ next x, seen.contains y = true ∨ y ∈ work) :
    (∀ x ∈ work, (reachGo next k seen work).contains x = true) ∧
    ∀ x, (reachGo next k seen work).contains x = true → ∀ y ∈ next x,
      (reachGo next k seen work).contains y = true := by
  induction k generalizing seen work with
  | zero =>
    have hw : work = [] := by
      cases work with
      | nil => rfl
      | cons _ _ => simp only [List.length_cons] at hk; omega
    subst hw
    simp only [reachGo]
    refine ⟨by simp, fun x hx y hy => ?_⟩
    simpa using hc x hx y hy
  | succ k ih =>
    cases work with
    | nil =>
      simp only [reachGo]
      refine ⟨by simp, fun x hx y hy => ?_⟩
      simpa using hc x hx y hy
    | cons n rest =>
      simp only [reachGo]
      split
      · rename_i hin
        obtain ⟨h1, h2⟩ := ih seen rest (by simp only [List.length_cons] at hk; omega)
          (fun x hx y hy => by
          rcases hc x hx y hy with h | h
          · exact .inl h
          · rcases List.mem_cons.mp h with rfl | h
            · exact .inl hin
            · exact .inr h)
        refine ⟨fun x hx => ?_, h2⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact reachGo_mono _ _ _ _ hin
        · exact h1 x hx
      · rename_i hin
        have hin' : seen.contains n = false := by simpa using hin
        have hw := unseenWeight_insert next us seen n (hus n) hin'
        obtain ⟨h1, h2⟩ := ih (seen.insert n) (next n ++ rest)
          (by simp only [List.length_cons, List.length_append] at hk ⊢; omega) (fun x hx y hy => by
            rw [Std.HashSet.contains_insert] at hx
            rcases Bool.or_eq_true _ _ ▸ hx with hx | hx
            · have : n = x := by simpa using hx
              subst this
              exact .inr (List.mem_append_left _ hy)
            · rcases hc x hx y hy with h | h
              · exact .inl (by simp [Std.HashSet.contains_insert, h])
              · rcases List.mem_cons.mp h with rfl | h
                · exact .inl (by simp [Std.HashSet.contains_insert])
                · exact .inr (List.mem_append_right _ h))
        refine ⟨fun x hx => ?_, h2⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact reachGo_mono _ _ _ _ (by simp [Std.HashSet.contains_insert])
        · exact h1 x (List.mem_append_right _ hx)

/-- The weight of the unseen names is at most the weight of all names. -/
theorem unseenWeight_le (next : Name → List Name) (us : List Name) (seen : Std.HashSet Name) :
    unseenWeight next us seen ≤ (us.map fun n => (next n).length).sum := by
  unfold unseenWeight
  induction us with
  | nil => simp
  | cons u us ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    split <;> (try simp only [List.map_cons, List.sum_cons]) <;> omega

/-- Every name that `seeds` reach through `next`, by a search with `weight` for what `next` gives
over all names (`mem_reach`). -/
def reach (next : Name → List Name) (weight : Nat) (seeds : List Name) : Std.HashSet Name :=
  reachGo next (seeds.length + weight) {} seeds

/-- The search finds exactly the names that the seeds reach, when `next` gives names only for the
names of `us` and `weight` bounds what it gives for them. -/
theorem mem_reach {weight : Nat} (us seeds : List Name) (hus : ∀ n, next n ≠ [] → n ∈ us)
    (hw : (us.map fun n => (next n).length).sum ≤ weight) (x : Name) :
    (reach next weight seeds).contains x = true ↔ ∃ s ∈ seeds, Reach next s x := by
  constructor
  · intro h
    refine reachGo_sound (fun y => ∃ s ∈ seeds, Reach next s y) ?_ _ _ _ (by simp)
      (fun y hy => ⟨y, hy, .refl⟩) x h
    rintro b ⟨s, hs, hr⟩ c hc
    exact ⟨s, hs, .step hr hc⟩
  · rintro ⟨s, hs, hr⟩
    obtain ⟨h1, h2⟩ := reachGo_closed (next := next) us hus (seeds.length + weight) {} seeds
      (by have := unseenWeight_le next us ({} : Std.HashSet Name); omega)
      (by simp)
    induction hr with
    | refl => exact h1 s hs
    | step _ hc ih => exact h2 _ ih _ hc

end Regula.Closed
