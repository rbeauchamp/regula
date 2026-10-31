import RegulaSpecification.Proofs.Foundation

/-!
# RG1007 to RG1009, against their statements

`Regula.Closed.Tables.rg1007` to `rg1009` are the functions that the checker runs, on the contracts
and the registrations of the input. For each, `rg100N_exact` proves that it reports a subject exactly
when `Violates100N` holds of it at `toSpec i`. They read no axiom set, and they need only that each
name is the name of one constant.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Link

variable {i : Regula.Closed.Input}

theorem isDecision_iff (k : Regula.Closed.Contract) :
    Regula.Closed.Tables.isDecision k = true ↔ (contract k).IsDecision := by
  rcases k with ⟨_, _, _, k, _, _⟩
  cases k <;> simp [Regula.Closed.Tables.isDecision, Contract.IsDecision, contract, contractKind]

theorem safeComputable_iff (hu : (i.decls.map (·.name)).Nodup) (f : Name) :
    i.tables.safeComputable f = true ↔ (toSpec i).SafeComputable f := by
  unfold Regula.Closed.Tables.safeComputable
  rw [any_index_iff hu]
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨d, hd, hn, ⟨h1, h2⟩, h3⟩
    exact ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, hn, h1, h2, h3⟩
  · rintro ⟨x, hx, hn, h1, h2, h3⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    exact ⟨d, hd, hn, ⟨h1, h2⟩, h3⟩

theorem specReachesImpl_iff (hu : (i.decls.map (·.name)).Nodup) (k : Regula.Closed.Contract) :
    (i.tables.mentions k.spec).contains k.impl = true ↔ (toSpec i).SpecReachesImpl (contract k) :=
  contains_mentions hu k.spec k.impl

theorem projectTest_iff (hu : (i.decls.map (·.name)).Nodup) (c : Name) :
    i.tables.projectTest c = true ↔ (toSpec i).ProjectTest c := by
  unfold Regula.Closed.Tables.projectTest
  rw [any_index_iff hu]
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨d, hd, hn, h1, h2⟩
    exact ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, hn, h1, h2⟩
  · rintro ⟨x, hx, hn, h1, h2⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    exact ⟨d, hd, hn, h1, h2⟩

/-- The condition of RG1007 that the chain of tests in the function decides. -/
theorem rg1007_chain (t : Regula.Closed.Tables) (k : Regula.Closed.Contract)
    (g : String → Regula.Closed.Finding) (f : Regula.Closed.Finding)
    (h : (if !t.claimedName k.theorem_ then none
      else if k.fixedArgs != 0 then some (g s!"fixes {k.fixedArgs} arguments of {k.impl}")
      else if !t.safeComputable k.impl then
        some (g s!"names {k.impl}, which is not a safe, total, computable constant")
      else if Regula.Closed.Tables.isDecision k && (t.mentions k.spec).contains k.impl then
        some (g s!"states its specification through its implementation {k.impl}")
      else none) = some f) :
    t.claimedName k.theorem_ = true ∧ (∃ s, f = g s) ∧
      (k.fixedArgs ≠ 0 ∨ t.safeComputable k.impl = false ∨
        (Regula.Closed.Tables.isDecision k = true ∧
          (t.mentions k.spec).contains k.impl = true)) := by
  split at h
  · simp at h
  · rename_i hc
    have hc' : t.claimedName k.theorem_ = true := by simpa using hc
    split at h
    · rename_i hx
      simp only [Option.some.injEq] at h
      exact ⟨hc', ⟨_, h.symm⟩, .inl (by simpa using hx)⟩
    · split at h
      · rename_i hx
        simp only [Option.some.injEq] at h
        exact ⟨hc', ⟨_, h.symm⟩, .inr (.inl (by simpa using hx))⟩
      · split at h
        · rename_i hx
          simp only [Option.some.injEq] at h
          exact ⟨hc', ⟨_, h.symm⟩, .inr (.inr (by simpa using hx))⟩
        · simp at h

/-- The function that the checker runs reports a theorem exactly when it violates RG1007. -/
theorem rg1007_exact (hu : (i.decls.map (·.name)).Nodup) (s : Name) :
    s ∈ (i.tables.rg1007 i.contracts).map (·.subject) ↔ Violates1007 (toSpec i) s := by
  unfold Regula.Closed.Tables.rg1007
  simp only [List.mem_map, List.mem_filterMap]
  constructor
  · rintro ⟨f, ⟨k, hk, hg⟩, rfl⟩
    obtain ⟨hc, ⟨m, rfl⟩, hcond⟩ := rg1007_chain _ _ _ _ hg
    refine ⟨contract k, mem_contracts.mpr ⟨k, hk, rfl⟩, rfl, (claimedName_iff hu _).mp hc, ?_⟩
    rcases hcond with h | h | ⟨h1, h2⟩
    · exact .inl h
    · refine .inr (.inl fun hs => ?_)
      have hs' : i.tables.safeComputable k.impl = true := (safeComputable_iff hu _).mpr hs
      rw [hs'] at h
      simp at h
    · exact .inr (.inr ⟨(isDecision_iff k).mp h1, (specReachesImpl_iff hu k).mp h2⟩)
  · rintro ⟨x, hx, rfl, hc, hv⟩
    obtain ⟨k, hk, rfl⟩ := mem_contracts.mp hx
    have hc' : i.tables.claimedName k.theorem_ = true := (claimedName_iff hu _).mpr hc
    obtain ⟨f, hf, hs⟩ : ∃ f, (if !i.tables.claimedName k.theorem_ then none
        else if k.fixedArgs != 0 then
          some (Regula.Closed.theoremFinding i.tables .executableContract k.theorem_
            s!"fixes {k.fixedArgs} arguments of {k.impl}")
        else if !i.tables.safeComputable k.impl then
          some (Regula.Closed.theoremFinding i.tables .executableContract k.theorem_
            s!"names {k.impl}, which is not a safe, total, computable constant")
        else if Regula.Closed.Tables.isDecision k && (i.tables.mentions k.spec).contains k.impl then
          some (Regula.Closed.theoremFinding i.tables .executableContract k.theorem_
            s!"states its specification through its implementation {k.impl}")
        else none) = some f ∧ f.subject = k.theorem_ := by
      split
      · rename_i h
        simp [hc'] at h
      · split
        · exact ⟨_, rfl, rfl⟩
        · rename_i h1
          split
          · exact ⟨_, rfl, rfl⟩
          · rename_i h2
            split
            · exact ⟨_, rfl, rfl⟩
            · rename_i h3
              exfalso
              simp only [bne_iff_ne, ne_eq, Classical.not_not] at h1
              have h2' : i.tables.safeComputable k.impl = true := by simpa using h2
              rcases hv with h | h | ⟨h4, h5⟩
              · exact h h1
              · exact h ((safeComputable_iff hu _).mp h2')
              · exact h3 (by
                  simp only [Bool.and_eq_true]
                  exact ⟨(isDecision_iff k).mpr h4, (specReachesImpl_iff hu k).mpr h5⟩)
    exact ⟨f, ⟨k, hk, hf⟩, hs⟩

/-- The function that the checker runs reports a function exactly when it violates RG1008. -/
theorem rg1008_exact (hu : (i.decls.map (·.name)).Nodup) (s : Name) :
    s ∈ (i.tables.rg1008 i.contracts i.decisions i.decidableResults).map (·.subject) ↔
      Violates1008 (toSpec i) s := by
  unfold Regula.Closed.Tables.rg1008
  rw [mem_report (sub := id) (fun _ => rfl)]
  have hany : i.contracts.any
      (fun k => k.impl == s && Regula.Closed.Tables.isDecision k && i.tables.claimedName k.theorem_)
        = true ↔
      ∃ k ∈ (toSpec i).contracts, k.impl = s ∧ k.IsDecision ∧ (toSpec i).ClaimedName k.theorem_ := by
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨k, hk, ⟨hi, hd⟩, hc⟩
      exact ⟨contract k, mem_contracts.mpr ⟨k, hk, rfl⟩, hi, (isDecision_iff k).mp hd,
        (claimedName_iff hu _).mp hc⟩
    · rintro ⟨x, hx, hi, hd, hc⟩
      obtain ⟨k, hk, rfl⟩ := mem_contracts.mp hx
      exact ⟨k, hk, ⟨hi, (isDecision_iff k).mpr hd⟩, (claimedName_iff hu _).mpr hc⟩
  constructor
  · rintro ⟨f, hf, hc, rfl⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not, List.any_eq_false] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    refine ⟨hf, (claimedName_iff hu _).mp h1, h2, fun hk => ?_⟩
    have := hany.mpr hk
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at this
    obtain ⟨k, hk, hb⟩ := this
    have hne := h3 k hk
    simp [hb] at hne
  · rintro ⟨hf, h1, h2, h3⟩
    refine ⟨s, hf, ?_, rfl⟩
    have hnot : i.contracts.any (fun k => k.impl == s && Regula.Closed.Tables.isDecision k &&
        i.tables.claimedName k.theorem_) = false := by
      cases hb : i.contracts.any (fun k => k.impl == s && Regula.Closed.Tables.isDecision k &&
          i.tables.claimedName k.theorem_) with
      | false => rfl
      | true => exact absurd (hany.mp hb) h3
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
      hnot, and_true]
    exact ⟨(claimedName_iff hu _).mpr h1, h2⟩

/-- The function that the checker runs reports a theorem exactly when it violates RG1009. -/
theorem rg1009_exact (hu : (i.decls.map (·.name)).Nodup) (s : Name) :
    s ∈ (i.tables.rg1009 i.contracts).map (·.subject) ↔ Violates1009 (toSpec i) s := by
  unfold Regula.Closed.Tables.rg1009
  simp only [List.mem_map, List.mem_filterMap]
  constructor
  · rintro ⟨f, ⟨k, hk, hg⟩, rfl⟩
    split at hg
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      split at hg
      · rename_i hne
        simp only [Option.some.injEq] at hg
        subst hg
        obtain ⟨c, hm, hf⟩ := filter_nonempty.mp hne
        simp only [Bool.and_eq_true] at hf
        have hspec := (contains_mentions hu k.spec c).mp (by simpa using hm)
        have himpl := (contains_mentions hu (k.impl :: k.accept) c).mp hf.2
        obtain ⟨a, ha, hr⟩ := himpl
        refine ⟨contract k, mem_contracts.mpr ⟨k, hk, rfl⟩, rfl, (claimedName_iff hu _).mp hc.1,
          (isDecision_iff k).mp hc.2, c, (projectTest_iff hu c).mp hf.1, hspec, ?_⟩
        rcases List.mem_cons.mp ha with rfl | ha
        · exact .inl hr
        · exact .inr ⟨a, ha, hr⟩
      · simp at hg
    · simp at hg
  · rintro ⟨x, hx, rfl, hc, hd, c, hp, hs, hr⟩
    obtain ⟨k, hk, rfl⟩ := mem_contracts.mp hx
    have hne : (!((i.tables.mentions k.spec).toList.filter fun c => i.tables.projectTest c &&
        (i.tables.mentions (k.impl :: k.accept)).contains c).isEmpty) = true := by
      refine filter_nonempty.mpr ⟨c, ?_, ?_⟩
      · simpa using (contains_mentions hu k.spec c).mpr hs
      · simp only [Bool.and_eq_true]
        refine ⟨(projectTest_iff hu c).mpr hp, (contains_mentions hu _ c).mpr ?_⟩
        rcases hr with hr | ⟨a, ha, hr⟩
        · exact ⟨k.impl, List.mem_cons_self .., hr⟩
        · exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩
    refine ⟨Regula.Closed.theoremFinding i.tables .sharedTest k.theorem_
        s!"its specification and its implementation or acceptance share the tests \
          {(i.tables.mentions k.spec).toList.filter fun c => i.tables.projectTest c &&
            (i.tables.mentions (k.impl :: k.accept)).contains c}", ⟨k, hk, ?_⟩, rfl⟩
    have hgate : (i.tables.claimedName k.theorem_ && Regula.Closed.Tables.isDecision k) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨(claimedName_iff hu _).mpr hc, (isDecision_iff k).mpr hd⟩
    rw [ite_eq_left hgate, ite_eq_left hne]

end Link

end RegulaSpecification
