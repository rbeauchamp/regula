import RegulaSpecification.Proofs.Link

/-!
# What the rules' tables hold

`Regula.Closed.Input.tables` indexes the input once, so that a rule reads a hash table in place of a
list. These theorems state what each table holds in terms of the specification's input, for the
tables that the checker builds: the constants by name, the claims of each module, the constants of
claimed modules, the constants that a set of constants reaches (`Input.Reaches`), the execution
closure (`Input.Executes`) and the departures (`Input.DepartsTo`).
-/

namespace RegulaSpecification

open Lean (Name)

namespace Link

variable {i : Regula.Closed.Input}

/-! ## The constants by name -/

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

theorem tables_index (i : Regula.Closed.Input) : i.tables.index = i.index := rfl

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

/-! ## The claims of each module -/

theorem mem_claimsOf (m : Name) (p : Regula.Closed.Profile) (e : Regula.Closed.Execution) :
    (p, e) ∈ i.claimsOf m ↔ (toSpec i).Claimed m (profile p) (execution e) := by
  simp only [Regula.Closed.Input.claimsOf, List.mem_flatMap, Input.Claimed, Input.InTarget]
  constructor
  · rintro ⟨t, ht, hx⟩
    by_cases hm : t.modules.contains m = true
    · rw [ite_eq_left hm, List.mem_filterMap] at hx
      obtain ⟨⟨name, c⟩, he, hc⟩ := hx
      by_cases hn : name = t.name
      · subst hn
        cases c with
        | claimed q y =>
          simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          exact ⟨target t, mem_targets.mpr ⟨t, ht, rfl⟩, by simpa [target] using hm,
            mem_manifest.mpr ⟨_, he, rfl⟩⟩
        | excluded => simp at hc
      · simp [hn] at hc
    · rw [ite_eq_right hm] at hx
      simp at hx
  · rintro ⟨x, hx, hm, hme⟩
    obtain ⟨t, ht, rfl⟩ := mem_targets.mp hx
    obtain ⟨⟨name, c⟩, he, hc⟩ := mem_manifest.mp hme
    simp only [entry, target, Entry.mk.injEq] at hc hm
    obtain ⟨rfl, hcl⟩ := hc
    cases c with
    | claimed q y =>
      simp only [classification, Classification.claimed.injEq] at hcl
      obtain ⟨hq, hy⟩ := hcl
      obtain rfl := profile_inj hq
      obtain rfl := execution_inj hy
      refine ⟨t, ht, ?_⟩
      rw [ite_eq_left (by simpa using hm), List.mem_filterMap]
      exact ⟨_, he, by simp⟩
    | excluded => simp [classification] at hcl

theorem profile_surj (p : Profile) : profile (profile' p) = p := by cases p <;> rfl

theorem execution_surj (e : Execution) : execution (execution' e) = e := by cases e <;> rfl

theorem claimedModule_iff (i : Regula.Closed.Input) (m : Name) :
    i.claimedModule m = true ↔ (toSpec i).ClaimedModule m := by
  simp only [Regula.Closed.Input.claimedModule, Bool.not_eq_true',
    List.isEmpty_eq_false_iff_exists_mem]
  constructor
  · rintro ⟨⟨p, e⟩, h⟩
    exact ⟨_, _, (mem_claimsOf m p e).mp h⟩
  · rintro ⟨p, e, h⟩
    refine ⟨(profile' p, execution' e), (mem_claimsOf m _ _).mpr ?_⟩
    rwa [profile_surj, execution_surj]

/-- What folding the modules of `l` into a table holds. -/
theorem claimTable_fold {β : Type} [Inhabited β] (g : Name → β) (l : List Name)
    (init : Std.HashMap Name β) (m : Name) :
    (l.foldl (fun t n => t.insert n (g n)) init)[m]? =
      if m ∈ l then some (g m) else init[m]? := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, Std.HashMap.getElem?_insert, List.mem_cons]
    by_cases hl : m ∈ l
    · simp [hl]
    · by_cases ha : m = a
      · subst ha
        simp
      · have hb : (a == m) = false := by simpa using fun h => ha h.symm
        simp [hl, ha, hb]

theorem claimTable_getD (i : Regula.Closed.Input) (m : Name) :
    i.claimTable.getD m [] = i.claimsOf m := by
  rw [Std.HashMap.getD_eq_getD_getElem?]
  unfold Regula.Closed.Input.claimTable
  rw [claimTable_fold]
  by_cases hm : m ∈ i.targets.flatMap (·.modules)
  · simp [hm]
  · simp only [hm, ↓reduceIte, Std.HashMap.getElem?_empty, Option.getD_none]
    symm
    simp only [Regula.Closed.Input.claimsOf, List.flatMap_eq_nil_iff]
    intro t ht
    rw [ite_eq_right]
    intro hc
    exact hm (List.mem_flatMap.mpr ⟨t, ht, by simpa using hc⟩)

theorem claimsFor_eq (i : Regula.Closed.Input) (m : Name) :
    i.tables.claimsFor m = i.claimsOf m := claimTable_getD i m

theorem mem_claimed (i : Regula.Closed.Input) {d : Regula.Closed.Decl} :
    d ∈ i.tables.claimed ↔ d ∈ i.decls ∧ (toSpec i).ClaimedModule d.module := by
  have : i.tables.claimed = i.decls.filter fun d => !(i.claimTable.getD d.module []).isEmpty := rfl
  rw [this, List.mem_filter, claimTable_getD]
  exact and_congr_right fun _ => claimedModule_iff i _

/-- Whether a name is a constant of a claimed module. -/
theorem claimedName_iff (hu : (i.decls.map (·.name)).Nodup) (c : Name) :
    i.tables.claimedName c = true ↔ (toSpec i).ClaimedName c := by
  unfold Regula.Closed.Tables.claimedName
  rw [any_index_iff hu]
  constructor
  · rintro ⟨d, hd, hn, hc⟩
    rw [claimsFor_eq] at hc
    exact ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, hn, (claimedModule_iff i _).mp hc⟩
  · rintro ⟨x, hx, hn, hc⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    refine ⟨d, hd, hn, ?_⟩
    rw [claimsFor_eq]
    exact (claimedModule_iff i _).mpr hc

theorem claimedName_of_mem {c : Name} (h : (toSpec i).ClaimedName c) :
    ∃ d ∈ i.decls, d.name = c ∧ (toSpec i).ClaimedModule d.module := by
  obtain ⟨x, hx, hn, hc⟩ := h
  obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
  exact ⟨d, hd, hn, hc⟩

/-! ## The searches -/

/-- A name reaches what a name that it gives reaches. -/
theorem Reach_head {next : Name → List Name} {a b c : Name}
    (h : Regula.Closed.Reach next b c) (hb : b ∈ next a) : Regula.Closed.Reach next a c := by
  induction h with
  | refl => exact .step .refl hb
  | step _ hc ih => exact .step ih hc

/-- `Reaches` extends by one more mention. -/
theorem reaches_snoc {s : Input} {a b c : Name} (h : s.Reaches a b) (d : Decl) (hd : d ∈ s.decls)
    (hn : d.name = b) (hc : c ∈ d.uses) : s.Reaches a c := by
  induction h with
  | refl => exact .step d hd hn hc (.refl _)
  | step d' hd' hn' hu _ ih => exact .step d' hd' hn' hu (ih hn)

theorem mem_usesOf (hu : (i.decls.map (·.name)).Nodup) {n c : Name} :
    c ∈ i.tables.usesOf n ↔ ∃ d ∈ i.decls, d.name = n ∧ c ∈ d.uses := by
  unfold Regula.Closed.Tables.usesOf
  cases h : i.tables.index[n]? with
  | none =>
    simp only [Option.elim, List.not_mem_nil, false_iff, not_exists, not_and]
    intro d hd hn
    rw [← hn, get_of_mem hu hd] at h
    simp at h
  | some d =>
    obtain ⟨hd, hn⟩ := (index_eq_some hu).mp h
    simp only [Option.elim]
    constructor
    · exact fun hc => ⟨d, hd, hn, hc⟩
    · rintro ⟨d', hd', hn', hc⟩
      have := get_of_mem hu hd'
      rw [hn', h] at this
      simp only [Option.some.injEq] at this
      exact this ▸ hc

theorem reach_iff_reaches (hu : (i.decls.map (·.name)).Nodup) {a b : Name} :
    Regula.Closed.Reach i.tables.usesOf a b ↔ (toSpec i).Reaches a b := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl _
    | step _ hc ih =>
      obtain ⟨d, hd, hn, hu'⟩ := (mem_usesOf hu).mp hc
      exact reaches_snoc ih (decl d) (mem_decls.mpr ⟨d, hd, rfl⟩) hn hu'
  · intro h
    induction h with
    | refl => exact .refl
    | step x hx hn hc _ ih =>
      obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
      exact Reach_head ih ((mem_usesOf hu).mpr ⟨d, hd, hn, hc⟩)

/-- The constants that `seeds` reach through the constants each mentions. -/
theorem contains_mentions (hu : (i.decls.map (·.name)).Nodup) (seeds : List Name) (x : Name) :
    (i.tables.mentions seeds).contains x = true ↔ ∃ s ∈ seeds, (toSpec i).Reaches s x := by
  unfold Regula.Closed.Tables.mentions
  rw [Regula.Closed.mem_reach (i.decls.map (·.name)) seeds ?_ (Nat.le_of_eq ?_)]
  · simp only [reach_iff_reaches hu]
  · intro n hn
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hn
    obtain ⟨d, hd, rfl, -⟩ := (mem_usesOf hu).mp hc
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  · rfl

end Link

end RegulaSpecification
