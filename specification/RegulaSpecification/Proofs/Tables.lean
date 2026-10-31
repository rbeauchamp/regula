import RegulaSpecification.Proofs.Link

/-!
# What the rules' tables hold

`Regula.Closed.Input.tables` indexes the input once, so that a rule reads a hash table in place of a
list. These theorems state what each table holds in terms of the specification's input: the
constants by name, the constants of claimed modules and the axiom set of each constant.
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
theorem any_index_iff (hu : (i.decls.map (·.name)).Nodup) (P : Regula.Closed.Decl → Bool)
    (n : Name) :
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

/-! ## The axiom sets -/

/-- What folding the mentions of one constant into the table holds. -/
theorem mem_mentionFold (name : Name) (uses : List Name) (init : Std.HashMap Name (List Name))
    (u c : Name) :
    c ∈ (uses.foldl (fun m v => m.insert v (name :: m.getD v [])) init).getD u [] ↔
      (u ∈ uses ∧ c = name) ∨ c ∈ init.getD u [] := by
  induction uses generalizing init with
  | nil => simp
  | cons v vs ih =>
    simp only [List.foldl_cons, ih, Std.HashMap.getD_insert, List.mem_cons]
    by_cases hv : v = u
    · subst hv
      simp only [beq_self_eq_true, ↓reduceIte, List.mem_cons, true_or, true_and]
      by_cases hc : c = name <;> simp [hc]
    · have hb : (v == u) = false := by simpa using hv
      have hne : u ≠ v := fun h => hv h.symm
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      simp [hne]

/-- What folding the mentions of the constants of `l` into the table holds. -/
theorem mem_mentionedFold (l : List Regula.Closed.Decl) (init : Std.HashMap Name (List Name))
    (u c : Name) :
    c ∈ (l.foldl (fun m d => d.uses.foldl (fun m v => m.insert v (d.name :: m.getD v [])) m)
        init).getD u [] ↔ (∃ d ∈ l, d.name = c ∧ u ∈ d.uses) ∨ c ∈ init.getD u [] := by
  induction l generalizing init with
  | nil => simp
  | cons d ds ih =>
    simp only [List.foldl_cons, ih, mem_mentionFold, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (h | ⟨hu, rfl⟩ | h)
      · exact .inl (.inr h)
      · exact .inl (.inl ⟨rfl, hu⟩)
      · exact .inr h
    · rintro ((⟨rfl, hu⟩ | h) | h)
      · exact .inr (.inl ⟨hu, rfl⟩)
      · exact .inl h
      · exact .inr (.inr h)

/-- The constants that mention `u`, as the table holds them. -/
theorem mem_mentionedBy (i : Regula.Closed.Input) (u c : Name) :
    c ∈ i.mentionedBy.getD u [] ↔ ∃ d ∈ i.decls, d.name = c ∧ u ∈ d.uses := by
  unfold Regula.Closed.Input.mentionedBy
  rw [mem_mentionedFold]
  simp

/-- The search backwards from `a` reaches `c` exactly when `c` reaches `a`. -/
theorem reach_mentionedBy_iff {a c : Name} :
    Regula.Closed.Reach (fun n => i.mentionedBy.getD n []) a c ↔ (toSpec i).Reaches c a := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl _
    | step _ hc ih =>
      obtain ⟨d, hd, rfl, hu⟩ := (mem_mentionedBy i _ _).mp hc
      exact .step (decl d) (mem_decls.mpr ⟨d, hd, rfl⟩) rfl hu ih
  · intro h
    induction h with
    | refl => exact .refl
    | step x hx hn hu _ ih =>
      obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
      exact .step ih ((mem_mentionedBy i _ _).mpr ⟨d, hd, hn, hu⟩)

/-- The search that `Input.axiomReach` makes from `a` finds exactly the constants that reach `a`. -/
theorem contains_axiomReach (a c : Name) :
    (Regula.Closed.reach (fun n => i.mentionedBy.getD n [])
        ((i.mentionedBy.keys.map fun n => (i.mentionedBy.getD n []).length).sum) [a]).contains c =
          true ↔
      (toSpec i).Reaches c a := by
  rw [Regula.Closed.mem_reach i.mentionedBy.keys [a] ?_ (Nat.le_refl _)]
  · simp [reach_mentionedBy_iff]
  · intro n hn
    rw [Std.HashMap.mem_keys]
    refine Classical.byContradiction fun hm => hn ?_
    rw [Std.HashMap.getD_eq_fallback hm]

/-- The set that the rules read is exactly the axiom set that the specification states. No field of
the input holds it, so no hypothesis about a reader stands behind this. -/
theorem axiomSet_iff (c a : Name) :
    a ∈ i.tables.axiomSet c ↔ (toSpec i).AxiomOf c a := by
  have hax : ∀ d : Regula.Closed.Decl, (d.kind == .axiom) = true ↔ (decl d).kind = .axiom := by
    intro d
    cases hd : d.kind <;> simp [decl, constKind, hd]
  simp only [Regula.Closed.Tables.axiomSet, Regula.Closed.Input.tables,
    Regula.Closed.Input.axiomReach,
    List.mem_filterMap, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨b, s⟩, ⟨d, ⟨hd, hk⟩, hpair⟩, hif⟩
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    split at hif
    · rename_i hc
      simp only [Option.some.injEq] at hif
      subst hif
      exact ⟨(contains_axiomReach _ _).mp hc,
        ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, (hax d).mp hk⟩⟩
    · simp at hif
  · rintro ⟨hr, x, hx, rfl, hk⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    exact ⟨(d.name, _), ⟨d, ⟨hd, (hax d).mpr hk⟩, rfl⟩, by
      have hc := (contains_axiomReach (i := i) d.name c).mpr hr
      simp only [decl, hc, ↓reduceIte]⟩

end Link

end RegulaSpecification
