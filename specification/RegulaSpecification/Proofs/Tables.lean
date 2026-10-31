import RegulaSpecification.Proofs.Link

/-!
# What the rules' tables hold

`Regula.Closed.Input.tables` indexes the input once, so that a rule reads a hash table in place of a
list. These theorems state what each table holds in terms of the specification's input: the
constants by name and the constants of claimed modules.
-/

namespace RegulaSpecification

open Lean (Name)

namespace Link

variable {i : Regula.Closed.Input}

theorem mem_insertFold (l : List Name) (init : Std.HashSet Name) (x : Name) :
    (l.foldl (·.insert ·) init).contains x = true ↔ x ∈ l ∨ init.contains x = true := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq,
      List.mem_cons]
    constructor
    · rintro (h | rfl | h)
      · exact .inl (.inr h)
      · exact .inl (.inl rfl)
      · exact .inr h
    · rintro ((rfl | h) | h)
      · exact .inr (.inl rfl)
      · exact .inl h
      · exact .inr (.inr h)

/-- `setOf` holds exactly the names of its list. -/
theorem mem_setOf (l : List Name) (x : Name) :
    (Regula.Closed.setOf l).contains x = true ↔ x ∈ l := by
  unfold Regula.Closed.setOf
  rw [mem_insertFold]
  simp

theorem names_toSpec (i : Regula.Closed.Input) :
    (toSpec i).decls.map (·.name) = i.decls.map (·.name) := by
  simp [toSpec, decl, Function.comp_def]

theorem unique_of_wf (h : (toSpec i).WellFormed) : (i.decls.map (·.name)).Nodup := by
  have := h.unique
  rwa [names_toSpec] at this

/-- What folding the constants of `l` into a table holds. -/
theorem index_fold (l : List Regula.Closed.Decl) (hu : (l.map (·.name)).Nodup)
    (init : Std.HashMap Name Regula.Closed.Decl) (n : Name) (d : Regula.Closed.Decl) :
    (l.foldl (fun m d => m.insert d.name d) init)[n]? = some d ↔
      (d ∈ l ∧ d.name = n) ∨ (n ∉ l.map (·.name) ∧ init[n]? = some d) := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons] at hu
    simp only [List.foldl_cons, ih hu.2, Std.HashMap.getElem?_insert, List.mem_cons, List.map_cons,
      not_or]
    by_cases han : a.name = n
    · subst han
      have hnot : a.name ∈ l.map (·.name) → False := hu.1
      constructor
      · rintro (⟨hd, hn⟩ | ⟨-, h⟩)
        · exact .inl ⟨.inr hd, hn⟩
        · simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h
          subst h
          exact .inl ⟨.inl rfl, rfl⟩
      · rintro (⟨rfl | hd, hn⟩ | ⟨h, -⟩)
        · exact .inr ⟨hnot, by simp⟩
        · exact .inl ⟨hd, hn⟩
        · exact absurd rfl h.1
    · have hb : (a.name == n) = false := by simpa using han
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro (⟨hd, hn⟩ | ⟨h1, h2⟩)
        · exact .inl ⟨.inr hd, hn⟩
        · exact .inr ⟨⟨fun h => han h.symm, h1⟩, h2⟩
      · rintro (⟨rfl | hd, hn⟩ | ⟨h1, h2⟩)
        · exact absurd hn han
        · exact .inl ⟨hd, hn⟩
        · exact .inr ⟨h1.2, h2⟩

theorem index_eq_some (hu : (i.decls.map (·.name)).Nodup) {n : Name} {d : Regula.Closed.Decl} :
    i.index[n]? = some d ↔ d ∈ i.decls ∧ d.name = n := by
  unfold Regula.Closed.Input.index
  rw [index_fold _ hu]
  simp

theorem get_of_mem (hu : (i.decls.map (·.name)).Nodup) {d : Regula.Closed.Decl}
    (hd : d ∈ i.decls) : i.tables.index[d.name]? = some d :=
  (index_eq_some hu).mpr ⟨hd, rfl⟩

/-- What a function of the constant that a name has decides, in terms of the input's constants. -/
theorem any_index_iff (hu : (i.decls.map (·.name)).Nodup) (P : Regula.Closed.Decl → Bool) (n : Name) :
    i.tables.index[n]?.any P = true ↔ ∃ d ∈ i.decls, d.name = n ∧ P d = true := by
  cases h : i.tables.index[n]? with
  | none =>
    simp only [Option.any_none, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro d hd hn
    rw [← hn, get_of_mem hu hd] at h
    simp at h
  | some d =>
    obtain ⟨hd, hn⟩ := (index_eq_some hu).mp h
    simp only [Option.any_some]
    constructor
    · exact fun hp => ⟨d, hd, hn, hp⟩
    · rintro ⟨d', hd', hn', hp⟩
      have := get_of_mem hu hd'
      rw [hn', h] at this
      simp only [Option.some.injEq] at this
      exact this ▸ hp

theorem resolves_iff {n : Name} : (toSpec i).Resolves n ↔ ∃ d ∈ i.decls, d.name = n := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    exact ⟨d, hd, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl⟩

/-- The set of claimed modules holds exactly the modules that the specification's input claims. -/
theorem claimed_contains (i : Regula.Closed.Input) (m : Name) :
    (Regula.Closed.setOf i.modules).contains m = true ↔ (toSpec i).ClaimedModule m :=
  mem_setOf _ _

theorem mem_claimed (i : Regula.Closed.Input) {d : Regula.Closed.Decl} :
    d ∈ i.tables.claimed ↔ d ∈ i.decls ∧ (toSpec i).ClaimedModule d.module := by
  have : i.tables.claimed =
      i.decls.filter fun d => (Regula.Closed.setOf i.modules).contains d.module := rfl
  rw [this, List.mem_filter, claimed_contains]

theorem claimedName_of_mem {c : Name} (h : (toSpec i).ClaimedName c) :
    ∃ d ∈ i.decls, d.name = c ∧ (toSpec i).ClaimedModule d.module := by
  obtain ⟨x, hx, hn, hc⟩ := h
  obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
  exact ⟨d, hd, hn, hc⟩

end Link

end RegulaSpecification
