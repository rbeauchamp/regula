module

public import RegulaPolicy.Domain

/-! Reusable facts for proving what a successful `Except` validator establishes.
They let theorems be stated about the executed guard sequences directly, instead of
sampling refusals of mutated inputs. They concern pure `Except` values only. -/

@[expose] public section

namespace RegulaPolicy.Guards

universe u v w

section Except

variable {ε : Type u} {ε' : Type w} {α β : Type v}

/-- A sequenced computation succeeds exactly when each step succeeds in turn. -/
@[simp] theorem bind_eq_ok {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

/-- An `unless` guard succeeds exactly when its condition holds. Not a simp lemma: `simp` already
proves it from `ite_throw_eq_ok` and `pure_eq_ok`. -/
theorem unless_eq_ok {c : Bool} {e : ε} {u : PUnit} :
    (unless c do throw e : Except ε PUnit) = .ok u ↔ c = true := by
  cases c <;> simp [throw, throwThe, MonadExceptOf.throw, pure, Except.pure]

/-- A thrown error is never success. -/
@[simp] theorem throw_ne_ok {e : ε} {a : α} : (throw e : Except ε α) ≠ .ok a := by
  simp [throw, throwThe, MonadExceptOf.throw]

/-- `pure` succeeds with exactly its value. -/
@[simp] theorem pure_eq_ok {a b : α} : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

/-- A thrown error short-circuits the rest of a sequence. -/
@[simp] theorem throw_bind {e : ε} {f : α → Except ε β} :
    (throw e >>= f : Except ε β) = throw e := rfl

/-- A guarded branch whose alternative throws succeeds exactly when the guard holds
and the guarded branch succeeds. -/
@[simp] theorem ite_throw_eq_ok {p : Prop} [Decidable p] {a : Except ε α} {e : ε} {b : α} :
    (if p then a else throw e) = .ok b ↔ p ∧ a = .ok b := by
  by_cases hp : p <;> simp [hp]

/-- A unit-valued success has only one possible value. -/
@[simp] theorem exists_punit_eq_ok {e : Except ε PUnit} :
    (∃ x, e = .ok x) ↔ e = .ok ⟨⟩ :=
  ⟨fun ⟨⟨⟩, h⟩ => h, fun h => ⟨_, h⟩⟩

/-- A mapped error changes no success. -/
@[simp] theorem mapError_eq_ok {x : Except ε α} {f : ε → ε'} {a : α} :
    x.mapError f = .ok a ↔ x = .ok a := by
  cases x <;> simp [Except.mapError]

/-- List traversal form of `forM_eq_ok`. -/
private theorem list_forM_eq_ok {xs : List α} {g : α → Except ε PUnit} :
    forM xs g = .ok ⟨⟩ ↔ ∀ x ∈ xs, g x = .ok ⟨⟩ := by
  induction xs with
  | nil => simp [pure, Except.pure]
  | cons x xs ih =>
    simp only [List.forM_cons, bind_eq_ok, ih, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨⟩, hx, hs⟩; exact ⟨hx, hs⟩
    · rintro ⟨hx, hs⟩; exact ⟨_, hx, hs⟩

/-- A list traversal succeeds exactly when the step succeeds on every element. -/
theorem listForM_eq_ok {xs : List α} {g : α → Except ε PUnit} {u : PUnit} :
    xs.forM g = .ok u ↔ ∀ x ∈ xs, g x = .ok ⟨⟩ := by
  induction xs with
  | nil => simp [List.forM, pure, Except.pure]
  | cons x xs ih =>
    change (g x >>= fun _ => xs.forM g) = _ ↔ _
    rw [bind_eq_ok]
    simp only [ih, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨⟩, hx, hs⟩; exact ⟨hx, hs⟩
    · rintro ⟨hx, hs⟩; exact ⟨_, hx, hs⟩

/-- An array traversal succeeds exactly when the step succeeds on every element;
the first refusal stops it, so success covers every element. -/
theorem forM_eq_ok {xs : Array α} {g : α → Except ε PUnit} :
    forM xs g = .ok ⟨⟩ ↔ ∀ x ∈ xs, g x = .ok ⟨⟩ := by
  rw [← Array.forM_eq_forM]
  unfold Array.forM
  rw [← Array.foldlM_toList]
  have fold : ∀ l : List α, l.foldlM (fun _ => g) ⟨⟩ = forM l g := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih => simp [List.foldlM, ← ih]
  rw [fold, list_forM_eq_ok]
  simp

/-- List form of `foldlM_append_eq_ok`. -/
private theorem list_foldlM_append_eq_ok {xs : List α} {f : α → Except ε (Array β)}
    {init expected : Array β}
    (h : xs.foldlM (fun acc x => return acc ++ (← f x)) init = .ok expected) :
    (∀ x ∈ xs, ∃ ys, f x = .ok ys) ∧
      ∀ y, y ∈ expected ↔ y ∈ init ∨ ∃ x ∈ xs, ∃ ys, f x = .ok ys ∧ y ∈ ys := by
  induction xs generalizing init with
  | nil =>
    simp only [List.foldlM_nil, pure_eq_ok] at h
    subst h
    simp
  | cons x xs ih =>
    simp only [List.foldlM_cons, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨acc, ⟨ys, hx, rfl⟩, hrest⟩ := h
    obtain ⟨hall, hmem⟩ := ih hrest
    refine ⟨fun x' hx' => ?_, fun y => ?_⟩
    · rcases List.mem_cons.mp hx' with rfl | hx'
      · exact ⟨ys, hx⟩
      · exact hall x' hx'
    · rw [hmem, Array.mem_append]
      constructor
      · rintro ((h | h) | ⟨x', hx', ys', hf, hy⟩)
        · exact .inl h
        · exact .inr ⟨x, List.mem_cons_self, ys, hx, h⟩
        · exact .inr ⟨x', List.mem_cons_of_mem _ hx', ys', hf, hy⟩
      · rintro (h | ⟨x', hx', ys', hf, hy⟩)
        · exact .inl (.inl h)
        · rcases List.mem_cons.mp hx' with rfl | hx'
          · rw [hx] at hf
            cases hf
            exact .inl (.inr hy)
          · exact .inr ⟨x', hx', ys', hf, hy⟩

/-- An accumulating array traversal that succeeds ran every step successfully, and its
result holds exactly the initial members and the members every step returned. -/
theorem foldlM_append_eq_ok {xs : Array α} {f : α → Except ε (Array β)}
    {init expected : Array β}
    (h : xs.foldlM (fun acc x => return acc ++ (← f x)) init = .ok expected) :
    (∀ x ∈ xs, ∃ ys, f x = .ok ys) ∧
      ∀ y, y ∈ expected ↔ y ∈ init ∨ ∃ x ∈ xs, ∃ ys, f x = .ok ys ∧ y ∈ ys := by
  rw [← Array.foldlM_toList] at h
  simpa using list_foldlM_append_eq_ok h

end Except

variable {α : Type} [BEq α] [LawfulBEq α]

/-- A duplicate-free list whose members all occur in `l₂` is no longer than `l₂`. -/
private theorem length_le_of_nodup_subset : ∀ {l₁ l₂ : List α}, l₁.Nodup →
    (∀ x ∈ l₁, x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l₂, hn, hs => by
    rw [List.nodup_cons] at hn
    have ha : a ∈ l₂ := hs a (by simp)
    have ht : ∀ x ∈ t, x ∈ l₂.erase a := fun x hx =>
      (List.mem_erase_of_ne (fun h => hn.1 (by subst h; exact hx))).mpr (hs x (by simp [hx]))
    have := length_le_of_nodup_subset hn.2 ht
    rw [List.length_erase_of_mem ha] at this
    have : 0 < l₂.length := List.length_pos_of_mem ha
    simp
    omega

/-- A duplicate-free list with exactly the members of `l₂` and the same length
witnesses that `l₂` is duplicate-free. -/
private theorem nodup_of_same_members : ∀ {l₁ l₂ : List α}, l₁.Nodup →
    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁.length = l₂.length → l₂.Nodup
  | _, [], _, _, _ => List.nodup_nil
  | l₁, a :: t, hn, hm, hl => by
    by_cases hat : a ∈ t
    · exfalso
      have := length_le_of_nodup_subset (l₂ := t) hn (fun x hx => by
        have := (hm x).mp hx
        simp only [List.mem_cons] at this
        rcases this with rfl | h
        · exact hat
        · exact h)
      simp at hl
      omega
    · have ha : a ∈ l₁ := (hm a).mpr (by simp)
      refine List.nodup_cons.mpr ⟨hat, nodup_of_same_members (hn.erase a) (fun x => ?_) ?_⟩
      · rw [hn.mem_erase_iff, hm]
        simp only [List.mem_cons]
        constructor
        · rintro ⟨hne, rfl | h⟩
          · exact absurd rfl hne
          · exact h
        · intro h
          exact ⟨fun e => hat (by subst e; exact h), Or.inr h⟩
      · rw [List.length_erase_of_mem ha, hl]
        simp

/-- The executed size comparison against the canonical edge set decides that the
observed edge sequence has no duplicate. -/
theorem nodup_of_canonicalEdges_size (xs : Array (Lean.Name × Lean.Name))
    (h : (canonicalEdges xs).size = xs.size) : xs.toList.Nodup := by
  let : Ord (Lean.Name × Lean.Name) := lexOrd
  apply nodup_of_same_members (l₁ := (canonicalEdges xs).toList)
  · have := CanonicalSet.unique (CanonicalSet.normalize (α := Lean.Name × Lean.Name) xs.toList)
    simp only [canonicalEdges, List.toList_toArray]
    exact this.imp fun hne heq => hne (by subst heq; exact Std.ReflCmp.compare_self)
  · intro x
    simp
  · simpa using h

/-- The executed size comparison against the canonical name set decides that the
observed name sequence has no duplicate. -/
theorem nodup_of_canonicalNames_size (xs : Array Lean.Name)
    (h : (canonicalNames xs).size = xs.size) : xs.toList.Nodup := by
  apply nodup_of_same_members (l₁ := (canonicalNames xs).toList)
  · have := CanonicalSet.unique (CanonicalSet.normalize (α := Lean.Name) xs.toList)
    simp only [canonicalNames, List.toList_toArray]
    exact this.imp fun hne heq => hne (by subst heq; exact Std.ReflCmp.compare_self)
  · intro x
    simp
  · simpa using h

end RegulaPolicy.Guards
