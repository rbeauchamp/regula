import RegulaSpecification.Proofs.Foundation

/-!
# RG3001 and RG3002, against their statements

`Regula.Closed.Input.rg3001` and `rg3002` are the functions that the checker runs. `rg3001_exact` and
`rg3002_exact` prove that each reports a subject exactly when its violation predicate holds of it at
`toSpec i`. They read one environment, so a cycle of departures is the cycle of that environment: no
departure of another executable's environment joins it.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Link

variable {i : Regula.Closed.Input}

theorem claimedTarget_iff (i : Regula.Closed.Input) (t : Name) :
    i.claimedTarget t = true ↔ (toSpec i).ClaimedTarget t := by
  simp only [Regula.Closed.Input.claimedTarget, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    Input.ClaimedTarget, toSpec, List.mem_map]
  constructor
  · rintro ⟨⟨target, c⟩, he, rfl, hc⟩
    cases c with
    | claimed p e => exact ⟨profile p, execution e, _, he, rfl⟩
    | excluded => simp at hc
  · rintro ⟨p, e, ⟨target, c⟩, he, hx⟩
    simp only [entry, Entry.mk.injEq] at hx
    obtain ⟨rfl, hc⟩ := hx
    cases c with
    | claimed q x => exact ⟨_, he, rfl, rfl⟩
    | excluded => simp [classification] at hc

theorem kind_executable (x : Regula.Closed.Target) :
    (x.kind == .executable) = true ↔ (target x).kind = .executable := by
  cases h : x.kind <;> simp [target, kind, h]

theorem loadsTarget_iff (i : Regula.Closed.Input) (x : Regula.Closed.Target) :
    i.loadsTarget x = true ↔ (toSpec i).LoadsRoot (target x) := by
  simp [Regula.Closed.Input.loadsTarget, Input.LoadsRoot, target, toSpec]

theorem contains_index (hu : (i.decls.map (·.name)).Nodup) (n : Name) :
    i.tables.index.contains n = true ↔ (toSpec i).Resolves n := by
  rw [resolves_iff, Std.HashMap.contains_eq_isSome_getElem?]
  cases h : i.tables.index[n]? with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro d hd hn
    rw [← hn, get_of_mem hu hd] at h
    simp at h
  | some d =>
    obtain ⟨hd, hn⟩ := (index_eq_some hu).mp h
    simpa using ⟨d, hd, hn⟩

/-- The claims of the executables whose root this environment loads. -/
theorem mem_rootClaims (p : Regula.Closed.Profile) (e : Regula.Closed.Execution) :
    (p, e) ∈ i.rootClaims ↔ ∃ x ∈ (toSpec i).targets, x.kind = .executable ∧
      (⟨x.name, .claimed (profile p) (execution e)⟩ : Entry) ∈ (toSpec i).manifest ∧
        (toSpec i).LoadsRoot x := by
  simp only [Regula.Closed.Input.rootClaims, List.mem_flatMap]
  constructor
  · rintro ⟨x, hx, hm⟩
    by_cases hc : (x.kind == .executable && i.loadsTarget x) = true
    · rw [ite_eq_left hc, List.mem_filterMap] at hm
      obtain ⟨⟨name, c⟩, he, hg⟩ := hm
      simp only [Bool.and_eq_true] at hc
      by_cases hn : name = x.name
      · subst hn
        cases c with
        | claimed q y =>
          simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hg
          obtain ⟨rfl, rfl⟩ := hg
          exact ⟨target x, mem_targets.mpr ⟨x, hx, rfl⟩, (kind_executable x).mp hc.1,
            mem_manifest.mpr ⟨_, he, rfl⟩, (loadsTarget_iff i x).mp hc.2⟩
        | excluded => simp at hg
      · simp [hn] at hg
    · rw [ite_eq_right hc] at hm
      simp at hm
  · rintro ⟨x', hx', hk, hm, hl⟩
    obtain ⟨x, hx, rfl⟩ := mem_targets.mp hx'
    obtain ⟨⟨name, c⟩, he, hc⟩ := mem_manifest.mp hm
    simp only [entry, target, Entry.mk.injEq] at hc
    obtain ⟨rfl, hcl⟩ := hc
    refine ⟨x, hx, ?_⟩
    rw [ite_eq_left (by
      simp only [Bool.and_eq_true]
      exact ⟨(kind_executable x).mpr hk, (loadsTarget_iff i x).mpr hl⟩), List.mem_filterMap]
    cases c with
    | claimed q y =>
      simp only [classification, Classification.claimed.injEq] at hcl
      obtain rfl := profile_inj hcl.1
      obtain rfl := execution_inj hcl.2
      exact ⟨_, he, by simp⟩
    | excluded => simp [classification] at hcl

theorem root_iff {r : Name} {p : Regula.Closed.Profile} {e : Regula.Closed.Execution} :
    (toSpec i).ExecutableRoot r (profile p) (execution e) ↔
      r = `main ∧ (toSpec i).Resolves `main ∧ (p, e) ∈ i.rootClaims := by
  rw [mem_rootClaims]
  constructor
  · rintro ⟨x, hx, hk, hm, d, hd, hn, rfl, hl⟩
    exact ⟨rfl, ⟨d, hd, hn⟩, x, hx, hk, hm, hl⟩
  · rintro ⟨rfl, ⟨d, hd, hn⟩, x, hx, hk, hm, hl⟩
    exact ⟨x, hx, hk, hm, d, hd, hn, rfl, hl⟩

theorem mem_compiledOf (hu : (i.decls.map (·.name)).Nodup) {n c : Name} :
    c ∈ i.tables.compiledOf n ↔ ∃ d ∈ i.decls, d.name = n ∧ c ∈ d.compiled := by
  unfold Regula.Closed.Tables.compiledOf
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

theorem reach_iff_executes (hu : (i.decls.map (·.name)).Nodup) {a b : Name} :
    Regula.Closed.Reach i.tables.compiledOf a b ↔ (toSpec i).Executes a b := by
  constructor
  · intro h
    induction h with
    | refl => exact .root _
    | step _ hc ih =>
      obtain ⟨d, hd, hn, hu'⟩ := (mem_compiledOf hu).mp hc
      exact .step (decl d) ih (mem_decls.mpr ⟨d, hd, rfl⟩) hn hu'
  · intro h
    induction h with
    | root => exact .refl
    | step x _ hx hn hc ih =>
      obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
      exact .step ih ((mem_compiledOf hu).mpr ⟨d, hd, hn, hc⟩)

/-- The execution closure of the checker is the closure of `main`, when the environment has a claimed
root. -/
theorem contains_closure (hu : (i.decls.map (·.name)).Nodup) (c : Name) :
    (i.closure i.tables).contains c = true ↔
      i.rootClaims ≠ [] ∧ (toSpec i).Resolves `main ∧ (toSpec i).Executes `main c := by
  unfold Regula.Closed.Input.closure
  by_cases hroot : (!i.rootClaims.isEmpty && i.tables.index.contains `main) = true
  · rw [ite_eq_left hroot]
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hroot
    rw [Regula.Closed.mem_reach (i.decls.map (·.name)) [`main] ?_ (Nat.le_of_eq ?_)]
    · simp only [List.mem_singleton, exists_eq_left, reach_iff_executes hu]
      exact ⟨fun h => ⟨hroot.1, (contains_index hu _).mp hroot.2, h⟩, fun h => h.2.2⟩
    · intro n hn
      obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hn
      obtain ⟨d, hd, rfl, -⟩ := (mem_compiledOf hu).mp hc
      exact List.mem_map.mpr ⟨d, hd, rfl⟩
    · rfl
  · rw [ite_eq_right hroot]
    simp only [Std.HashSet.contains_empty, Bool.false_eq_true, false_iff, not_and]
    intro hr hm
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hroot
    exact absurd ⟨hr, (contains_index hu _).mpr hm⟩ hroot

/-! ## Departures -/

/-- One step of the table of departures. -/
def departStep (m : Std.HashMap Name (List Name)) (x : Regula.Closed.Departure) :
    Std.HashMap Name (List Name) :=
  if x.reference == x.runs then m
  else m.insert x.reference (x.runs :: m.getD x.reference [])

theorem mem_departFold (l : List Regula.Closed.Departure) (init : Std.HashMap Name (List Name))
    (c n : Name) :
    n ∈ (l.foldl departStep init).getD c [] ↔
      (∃ x ∈ l, x.reference = c ∧ x.runs = n ∧ c ≠ n) ∨ n ∈ init.getD c [] := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, List.mem_cons, exists_eq_or_imp]
    have hstep : n ∈ (departStep init a).getD c [] ↔
        (a.reference = c ∧ a.runs = n ∧ c ≠ n) ∨ n ∈ init.getD c [] := by
      unfold departStep
      by_cases he : a.reference = a.runs
      · simp only [he, beq_self_eq_true, ↓reduceIte]
        constructor
        · exact .inr
        · rintro (⟨rfl, rfl, h⟩ | h)
          · exact absurd rfl h
          · exact h
      · have hb : (a.reference == a.runs) = false := by simpa using he
        simp only [hb, Bool.false_eq_true, ↓reduceIte, Std.HashMap.getD_insert]
        by_cases hr : a.reference = c
        · subst hr
          simp only [beq_self_eq_true, ↓reduceIte, List.mem_cons]
          constructor
          · rintro (rfl | h)
            · exact .inl ⟨trivial, rfl, he⟩
            · exact .inr h
          · rintro (⟨-, rfl, -⟩ | h)
            · exact .inl rfl
            · exact .inr h
        · have hb' : (a.reference == c) = false := by simpa using hr
          simp [hb', hr]
    rw [hstep]
    constructor
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h)
      · exact .inr h
    · rintro ((h | h) | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)

theorem departsTable_eq (i : Regula.Closed.Input) :
    i.departsTable = (i.decls.flatMap (·.departures)).foldl departStep {} := rfl

theorem mem_departsOf {c n : Name} :
    n ∈ i.tables.departsOf c ↔ (toSpec i).Departs c n := by
  have : i.tables.departsOf c = i.departsTable.getD c [] := rfl
  rw [this, departsTable_eq, mem_departFold]
  simp only [Std.HashMap.getD_empty, List.not_mem_nil, or_false, List.mem_flatMap]
  constructor
  · rintro ⟨x, ⟨d, hd, hx⟩, rfl, rfl, hne⟩
    exact ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, departure x, List.mem_map.mpr ⟨x, hx, rfl⟩, rfl, rfl,
      hne⟩
  · rintro ⟨y, hy, z, hz, rfl, rfl, hne⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    exact ⟨x, ⟨d, hd, hx⟩, rfl, rfl, hne⟩

theorem departsTo_snoc {s : Input} {a b c : Name} (h : s.DepartsTo a b) (hc : s.Departs b c) :
    s.DepartsTo a c := by
  induction h with
  | one h => exact .more h (.one hc)
  | more h _ ih => exact .more h (ih hc)

theorem departsTo_iff {a b : Name} :
    (toSpec i).DepartsTo a b ↔
      ∃ s ∈ i.tables.departsOf a, Regula.Closed.Reach i.tables.departsOf s b := by
  constructor
  · intro h
    induction h with
    | one h => exact ⟨_, mem_departsOf.mpr h, .refl⟩
    | more h _ ih =>
      obtain ⟨s, hs, hr⟩ := ih
      exact ⟨_, mem_departsOf.mpr h, Reach_head hr hs⟩
  · rintro ⟨s, hs, hr⟩
    induction hr with
    | refl => exact .one (mem_departsOf.mp hs)
    | step _ hc ih => exact departsTo_snoc ih (mem_departsOf.mp hc)

/-- The search for a cycle of departures decides `DepartsTo c c`. -/
theorem contains_cycle (c : Name) :
    (Regula.Closed.reach i.tables.departsOf i.tables.departsWeight (i.tables.departsOf c)).contains c
      = true ↔ (toSpec i).DepartsTo c c := by
  rw [departsTo_iff]
  refine Regula.Closed.mem_reach ((i.decls.flatMap (·.departures)).map (·.reference)) _ ?_
    (Nat.le_of_eq ?_) c
  · intro n hn
    obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ hn
    obtain ⟨y, hy, z, hz, rfl, -⟩ := mem_departsOf.mp hm
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    exact List.mem_map.mpr ⟨x, List.mem_flatMap.mpr ⟨d, hd, hx⟩, rfl⟩
  · simp only [List.map_map, Function.comp_def]
    rfl

/-! ## RG3001 -/

/-- The function that the checker runs reports a name exactly when it violates RG3001. -/
theorem rg3001_exact (hu : (i.decls.map (·.name)).Nodup) (s : Name) :
    s ∈ (i.rg3001 i.tables).map (·.subject) ↔ Violates3001 (toSpec i) s := by
  unfold Regula.Closed.Input.rg3001 Regula.Closed.Input.missingRoots
  simp only [List.mem_map, List.mem_append, List.mem_filterMap]
  constructor
  · rintro ⟨f, hf | ⟨c, hc, hg⟩, rfl⟩
    · split at hf
      · simp at hf
      · rename_i hm
        obtain ⟨x, hx, hg⟩ := List.mem_filterMap.mp hf
        split at hg
        · rename_i hk
          simp only [Bool.and_eq_true] at hk
          simp only [Option.some.injEq] at hg
          subst hg
          refine .inr ⟨target x, mem_targets.mpr ⟨x, hx, rfl⟩, rfl, (kind_executable x).mp hk.1.1,
            (claimedTarget_iff i _).mp hk.1.2, (loadsTarget_iff i x).mp hk.2, fun hr => ?_⟩
          exact hm ((contains_index hu _).mpr hr)
        · simp at hg
    · obtain ⟨hroots, hmain, hex⟩ := (contains_closure hu c).mp (by simpa using hc)
      obtain ⟨⟨p, e⟩, hpe⟩ := List.exists_mem_of_ne_nil _ hroots
      have hroot := (root_iff (i := i)).mpr ⟨rfl, hmain, hpe⟩
      split at hg
      · rename_i hnone
        simp only [Option.some.injEq] at hg
        subst hg
        refine .inl ⟨_, _, _, hroot, hex, .inl fun hr => ?_⟩
        obtain ⟨d, hd, hn⟩ := resolves_iff.mp hr
        have hn' : d.name = c := hn
        rw [← hn', get_of_mem hu hd] at hnone
        simp at hnone
      · rename_i d hd
        obtain ⟨hd', hn⟩ := (index_eq_some hu).mp hd
        split at hg
        · rename_i hcyc
          simp only [Option.some.injEq] at hg
          subst hg
          simp only [Regula.Closed.finding]
          rw [hn]
          exact .inl ⟨_, _, _, hroot, hex, .inr ((contains_cycle c).mp hcyc)⟩
        · simp at hg
  · rintro (⟨r, P, E, hroot, hex, hcond⟩ | ⟨x', hx', rfl, hk, ⟨p, e, hm⟩, hl, hr⟩)
    · have hroot' : (toSpec i).ExecutableRoot r (profile (profile' P)) (execution (execution' E)) := by
        rwa [profile_surj, execution_surj]
      obtain ⟨rfl, hmain, hpe⟩ := root_iff.mp hroot'
      have hc : (i.closure i.tables).contains s = true :=
        (contains_closure hu s).mpr ⟨List.ne_nil_of_mem hpe, hmain, hex⟩
      cases hidx : i.tables.index[s]? with
      | none =>
        exact ⟨_, .inr ⟨s, by simpa using hc, by simp [hidx]; rfl⟩, rfl⟩
      | some d =>
        obtain ⟨hd, hn⟩ := (index_eq_some hu).mp hidx
        rcases hcond with hnr | hcyc
        · exact absurd ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, hn⟩ hnr
        · refine ⟨Regula.Closed.finding .executionUnresolved d "is on a cycle of departures",
            .inr ⟨s, by simpa using hc, ?_⟩, hn⟩
          simp only [hidx]
          rw [ite_eq_left ((contains_cycle s).mpr hcyc)]
    · obtain ⟨x, hx, rfl⟩ := mem_targets.mp hx'
      have hnc : i.tables.index.contains `main = false := by
        cases hb : i.tables.index.contains `main with
        | false => rfl
        | true => exact absurd ((contains_index hu _).mp hb) hr
      refine ⟨{ rule := .executionUnresolved, subject := x.name, module := none
                detail := "is a claimed executable whose environment has no `main`" },
        .inl ?_, rfl⟩
      rw [ite_eq_right (by simp [hnc])]
      refine List.mem_filterMap.mpr ⟨x, hx, ?_⟩
      rw [ite_eq_left]
      simp only [Bool.and_eq_true]
      exact ⟨⟨(kind_executable x).mpr hk, (claimedTarget_iff i _).mpr ⟨p, e, hm⟩⟩,
        (loadsTarget_iff i x).mpr hl⟩

/-! ## RG3002 -/

theorem unbindable_iff (hu : (i.decls.map (·.name)).Nodup) (d : Regula.Closed.Decl) :
    i.tables.unbindable d = true ↔ (toSpec i).Unbindable (decl d) := by
  unfold Regula.Closed.Tables.unbindable
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', Input.Unbindable, decl]
  constructor
  · rintro ((h | ⟨h1, h2⟩) | h)
    · exact .inl h
    · refine .inr (.inl ⟨h1, fun hh => ?_⟩)
      simp [(recursionHelper_iff hu d).mpr hh] at h2
    · exact .inr (.inr h)
  · rintro (h | ⟨h1, h2⟩ | h)
    · exact .inl (.inl h)
    · refine .inl (.inr ⟨h1, ?_⟩)
      cases hb : i.tables.recursionHelper d with
      | false => rfl
      | true => exact absurd ((recursionHelper_iff hu d).mp hb) h2
    · exact .inr h

/-- A correspondence, as the function decides it. -/
theorem corresponds_iff (h : Admitted i) (p : Regula.Closed.Profile) (x : Regula.Closed.Departure) :
    i.corresponds i.tables p x = true ↔ (toSpec i).Corresponds (profile p) (departure x) := by
  have hu := unique_of_wf h.wf
  unfold Regula.Closed.Input.corresponds
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨q, hq, ⟨hr, hn⟩, ha⟩
    obtain ⟨d, hd, hdn, hp⟩ := (any_index_iff hu _ _).mp ha
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    refine ⟨proof q, List.mem_map.mpr ⟨q, hq, rfl⟩, by simp [proof, departure, hr, hn], ?_, ?_⟩
    · exact ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, hdn, h1, h2⟩
    · intro a hax
      have hset := (axiomSet_iff h.axioms hd (.inr ⟨q, hq, hdn.symm⟩) a).mpr (by
        rw [hdn]; exact hax)
      exact (admits_iff hu p a).mp (h3 a hset)
  · rintro ⟨y, hy, hs, ⟨z, hz, hzn, h1, h2⟩, hadm⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hz
    simp only [proof, departure, Goal.corresponds.injEq] at hs
    refine ⟨q, hq, ⟨hs.1, hs.2⟩, (any_index_iff hu _ _).mpr ⟨d, hd, hzn, ?_⟩⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
    refine ⟨⟨h1, h2⟩, fun a ha => (admits_iff hu p a).mpr (hadm a ?_)⟩
    have := (axiomSet_iff h.axioms hd (.inr ⟨q, hq, hzn.symm⟩) a).mp ha
    have hzn' : d.name = (proof q).theorem_ := hzn
    rwa [hzn'] at this

theorem execution_checked (e : Regula.Closed.Execution) :
    (e == .checked) = true ↔ execution e = .checked := by
  cases e <;> simp [execution]

/-- The function that the checker runs reports a constant exactly when it violates RG3002. -/
theorem rg3002_exact (h : Admitted i) (s : Name) :
    s ∈ (i.rg3002 i.tables).map (·.subject) ↔ Violates3002 (toSpec i) s := by
  have hu := unique_of_wf h.wf
  unfold Regula.Closed.Input.rg3002
  simp only [List.mem_map, List.mem_flatMap, List.mem_filter, List.mem_filterMap]
  constructor
  · rintro ⟨f, ⟨⟨p, e⟩, ⟨hpe, he⟩, c, hc, hg⟩, rfl⟩
    obtain ⟨-, hmain, hex⟩ := (contains_closure hu c).mp (by simpa using hc)
    obtain ⟨d, hidx, hg⟩ := Option.bind_eq_some_iff.mp hg
    obtain ⟨hd, hn⟩ := (index_eq_some hu).mp hidx
    have hroot : (toSpec i).ExecutableRoot `main (profile p) .checked := by
      have := (root_iff (i := i) (r := `main) (p := p) (e := e)).mpr ⟨rfl, hmain, hpe⟩
      rwa [(execution_checked e).mp he] at this
    split at hg
    · rename_i hb
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb
      simp only [Option.some.injEq] at hg
      subst hg
      simp only [Regula.Closed.finding]
      rw [hn]
      exact ⟨_, _, hroot, hex, .inl ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, hn, hb.1,
        (unbindable_iff hu d).mp hb.2⟩⟩
    · split at hg
      · simp at hg
      · rename_i x rest hl
        simp only [Option.some.injEq] at hg
        subst hg
        simp only [Regula.Closed.finding]
        rw [hn]
        have hx : x ∈ d.departures.filter
            fun x => !x.inToolchain && !i.corresponds i.tables p x := by
          rw [hl]; exact List.mem_cons_self ..
        obtain ⟨hx, hf⟩ := List.mem_filter.mp hx
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
        refine ⟨_, _, hroot, hex, .inr ⟨departure x,
          ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, hn, List.mem_map.mpr ⟨x, hx, rfl⟩, hf.1⟩, fun hk => ?_⟩⟩
        simp [(corresponds_iff h p x).mpr hk] at hf
  · rintro ⟨r, P, hroot, hex, hcond⟩
    have hroot' : (toSpec i).ExecutableRoot r (profile (profile' P)) (execution .checked) := by
      rwa [profile_surj]
    obtain ⟨rfl, hmain, hpe⟩ := root_iff.mp hroot'
    have hc : (i.closure i.tables).contains s = true :=
      (contains_closure hu s).mpr ⟨List.ne_nil_of_mem hpe, hmain, hex⟩
    have hP : profile (profile' P) = P := profile_surj P
    obtain ⟨d, hd, hn, hfound⟩ : ∃ d ∈ i.decls, d.name = s ∧
        ((d.inToolchain = false ∧ i.tables.unbindable d = true) ∨
          ∃ x ∈ d.departures, x.inToolchain = false ∧
            i.corresponds i.tables (profile' P) x = false) := by
      rcases hcond with ⟨y, hy, hn, ht, hb⟩ | ⟨x', ⟨y, hy, hn, hx', ht⟩, hnc⟩
      · obtain ⟨d, hd, rfl⟩ := mem_decls.mp hy
        exact ⟨d, hd, hn, .inl ⟨ht, (unbindable_iff hu d).mpr hb⟩⟩
      · obtain ⟨d, hd, rfl⟩ := mem_decls.mp hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hx'
        refine ⟨d, hd, hn, .inr ⟨x, hx, ht, ?_⟩⟩
        cases hb : i.corresponds i.tables (profile' P) x with
        | false => rfl
        | true =>
          have := (corresponds_iff h _ x).mp hb
          rw [hP] at this
          exact absurd this hnc
    have hidx : i.tables.index[s]? = some d := (index_eq_some hu).mpr ⟨hd, hn⟩
    by_cases hb : (!d.inToolchain && i.tables.unbindable d) = true
    · refine ⟨Regula.Closed.finding .executionBoundary d "is code that no theorem can bind",
        ⟨(profile' P, .checked), ⟨hpe, by simp⟩, s, by simpa using hc, ?_⟩, hn⟩
      simp only [hidx, Option.bind_some]
      rw [ite_eq_left hb]
    · obtain ⟨x, hx, ht, hnc⟩ : ∃ x ∈ d.departures, x.inToolchain = false ∧
          i.corresponds i.tables (profile' P) x = false := by
        rcases hfound with ⟨h1, h2⟩ | hx
        · simp [h1, h2] at hb
        · exact hx
      have hne : d.departures.filter
          (fun x => !x.inToolchain && !i.corresponds i.tables (profile' P) x) ≠ [] :=
        List.ne_nil_of_mem (List.mem_filter.mpr ⟨hx, by simp [ht, hnc]⟩)
      cases hl : d.departures.filter
          (fun x => !x.inToolchain && !i.corresponds i.tables (profile' P) x) with
      | nil => exact absurd hl hne
      | cons y rest =>
        refine ⟨Regula.Closed.finding .executionBoundary d
            s!"runs {y.runs} in place of {y.reference} with no admitted correspondence",
          ⟨(profile' P, .checked), ⟨hpe, by simp⟩, s, by simpa using hc, ?_⟩, hn⟩
        simp only [hidx, Option.bind_some]
        rw [ite_eq_right hb, hl]

end Link

end RegulaSpecification
