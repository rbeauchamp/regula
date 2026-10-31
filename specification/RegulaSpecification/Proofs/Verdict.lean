import RegulaSpecification.Proofs.Records

/-!
# The verdict, against its statement

`Regula.Closed.Bundle.refusal?` is the admission that the checker runs, and `Regula.Closed.run` its
verdict. `refusal_none_iff` proves that the admission refuses exactly a bundle that the specification's
`Bundle.WellFormed` refuses, or one that lacks an axiom set that a rule reads. `run_refused` and
`run_complete` then state the verdict: a refused bundle is `incomplete`, and an admitted one is `pass`
or `fail`, and `pass` exactly when every rule that reads one environment holds of each environment.

**What this leaves out.** `gateRecord` also requires RG6001, which reads the owner's record. Leaf #485
implements it, so the verdict does not read it yet, and `run_complete` states `AllHold` of each
environment, not `Bundle.AllHold`. That the shell (`Regula.Load`) fills the bundle through Lean's and
Lake's interfaces is trusted, as `AxiomsRead` and the module documentation of `Link` state.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Link

/-- The bundle of the checker as the specification's. -/
def toBundle (b : Regula.Closed.Bundle) : Bundle := ⟨b.envs.map toSpec⟩

/-- The allowlists of the checker as the specification's. -/
def allowlists (a : Regula.Closed.Allowlists) : Allowlists :=
  ⟨fun n => a.options n = true, fun n => a.extensions n = true⟩

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

theorem mem_mapFold {α : Type} (f : α → Name) (l : List α) (x : Name) :
    (l.foldl (fun s a => s.insert (f a)) ({} : Std.HashSet Name)).contains x = true ↔ x ∈ l.map f := by
  have : l.foldl (fun s a => s.insert (f a)) ({} : Std.HashSet Name) =
      (l.map f).foldl (·.insert ·) {} := by
    simp [List.foldl_map]
  rw [this, mem_insertFold]
  simp

theorem duplicate_none (seen : Std.HashSet Name) (l : List Name) :
    Regula.Closed.Input.duplicate? seen l = none ↔
      l.Nodup ∧ ∀ x ∈ l, seen.contains x = false := by
  induction l generalizing seen with
  | nil => simp [Regula.Closed.Input.duplicate?]
  | cons a l ih =>
    rw [Regula.Closed.Input.duplicate?]
    by_cases ha : seen.contains a = true
    · rw [ite_eq_left ha]
      constructor
      · intro h
        cases h
      · rintro ⟨-, h⟩
        have := h a (List.mem_cons_self ..)
        rw [ha] at this
        cases this
    · rw [ite_eq_right ha, ih, List.nodup_cons]
      have ha' : seen.contains a = false := by simpa using ha
      constructor
      · rintro ⟨hnd, hl⟩
        refine ⟨⟨fun hm => ?_, hnd⟩, fun x hx => ?_⟩
        · have := hl a hm
          simp [Std.HashSet.contains_insert] at this
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact ha'
          · have := hl x hx
            simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff] at this
            exact this.2
      · rintro ⟨⟨hm, hnd⟩, hl⟩
        refine ⟨hnd, fun x hx => ?_⟩
        have hb : (a == x) = false := by simpa using fun (h : a = x) => hm (h ▸ hx)
        simp [Std.HashSet.contains_insert, hb, hl x (List.mem_cons_of_mem _ hx)]

/-- The first constant without an axiom set is none exactly when each constant that a rule reads the
set of has one. -/
theorem axiomsMissing_none (i : Regula.Closed.Input) :
    i.axiomsMissing? = none ↔
      ∀ d ∈ i.decls, ((toSpec i).ClaimedModule d.module ∨ ∃ q ∈ i.proved, q.theorem_ = d.name) →
        d.axioms.isSome = true := by
  unfold Regula.Closed.Input.axiomsMissing?
  simp only [Option.map_eq_none_iff, List.find?_eq_none, Bool.and_eq_true, Bool.or_eq_true,
    Option.isNone_iff_eq_none, not_and]
  have hc : ∀ d : Regula.Closed.Decl, (!(i.claimTable.getD d.module []).isEmpty) = true ↔
      (toSpec i).ClaimedModule d.module := by
    intro d
    rw [claimTable_getD]
    exact claimedModule_iff i _
  have ht : ∀ d : Regula.Closed.Decl, i.theoremSet.contains d.name = true ↔
      ∃ q ∈ i.proved, q.theorem_ = d.name := by
    intro d
    unfold Regula.Closed.Input.theoremSet
    rw [mem_mapFold (fun q : Regula.Closed.Correspondence => q.theorem_)]
    simp
  constructor
  · intro h d hd hr
    cases hx : d.axioms with
    | some _ => rfl
    | none =>
      refine absurd ?_ (h d hd hx)
      rcases hr with hr | hr
      · exact .inl ((hc d).mpr hr)
      · exact .inr ((ht d).mpr hr)
  · intro h d hd hn hr
    have := h d hd (by
      rcases hr with hr | hr
      · exact .inl ((hc d).mp hr)
      · exact .inr ((ht d).mp hr))
    simp [hn] at this

theorem nameSet_iff (i : Regula.Closed.Input) (n : Name) :
    i.nameSet.contains n = true ↔ (toSpec i).Resolves n := by
  unfold Regula.Closed.Input.nameSet
  rw [mem_mapFold (fun d : Regula.Closed.Decl => d.name), resolves_iff]
  simp

theorem recordSet_iff (i : Regula.Closed.Input) (n : Name) :
    i.recordSet.contains n = true ↔ ∃ r ∈ (toSpec i).modules, r.name = n := by
  unfold Regula.Closed.Input.recordSet
  rw [mem_mapFold (fun r : Regula.Closed.ModuleRecord => r.name)]
  simp only [List.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨record r, mem_modules.mpr ⟨r, hr, rfl⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨r, hr, rfl⟩ := mem_modules.mp hx
    exact ⟨r, hr, rfl⟩

theorem openMention_none (i : Regula.Closed.Input) :
    i.openMention? = none ↔ ∀ d ∈ (toSpec i).decls, ∀ u ∈ d.uses, (toSpec i).Resolves u := by
  unfold Regula.Closed.Input.openMention?
  simp only [List.findSome?_eq_none_iff, Option.map_eq_none_iff, List.find?_eq_none]
  constructor
  · intro h x hx u hu
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    exact (nameSet_iff i u).mp (by simpa using h d hd u hu)
  · intro h d hd u hu
    have := (nameSet_iff i u).mpr (h (decl d) (mem_decls.mpr ⟨d, hd, rfl⟩) u hu)
    simp [this]

theorem unrecorded_none (i : Regula.Closed.Input) :
    i.unrecorded? = none ↔
      ∀ t ∈ (toSpec i).targets, ∀ m ∈ t.modules, ∃ r ∈ (toSpec i).modules, r.name = m := by
  unfold Regula.Closed.Input.unrecorded?
  simp only [List.findSome?_eq_none_iff, Option.map_eq_none_iff, List.find?_eq_none]
  constructor
  · intro h x hx m hm
    obtain ⟨t, ht, rfl⟩ := mem_targets.mp hx
    exact (recordSet_iff i m).mp (by simpa using h t ht m hm)
  · intro h t ht m hm
    have := (recordSet_iff i m).mpr (h (target t) (mem_targets.mpr ⟨t, ht, rfl⟩) m hm)
    simp [this]

/-- What the admission of one input decides. -/
theorem input_refusal_none (i : Regula.Closed.Input) :
    i.refusal? = none ↔ (toSpec i).WellFormed ∧ i.axiomsMissing? = none := by
  have hunique : Regula.Closed.Input.duplicate? {} (i.decls.map (·.name)) = none ↔
      ((toSpec i).decls.map (·.name)).Nodup := by
    rw [duplicate_none, names_toSpec]
    simp
  have hwf : (toSpec i).WellFormed ↔
      Regula.Closed.Input.duplicate? {} (i.decls.map (·.name)) = none ∧ i.openMention? = none ∧
        i.unrecorded? = none := by
    rw [hunique, openMention_none, unrecorded_none]
    exact ⟨fun h => ⟨h.unique, h.closed, h.loaded⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩
  rw [hwf]
  unfold Regula.Closed.Input.refusal?
  split
  · rename_i h
    simp [h]
  · rename_i h1
    split
    · rename_i h2
      simp [h2]
    · rename_i h2
      split
      · rename_i h3
        simp [h3]
      · rename_i h3
        split
        · rename_i h4
          simp [h4]
        · rename_i h4
          simp [h1, h2, h3, h4]

theorem loadedSet_iff (b : Regula.Closed.Bundle) (n : Name) :
    b.loadedSet.contains n = true ↔ ∃ i ∈ b.envs, n ∈ i.loads := by
  suffices h : ∀ (l : List Regula.Closed.Input) (init : Std.HashSet Name),
      (l.foldl (fun s i => i.loads.foldl (·.insert ·) s) init).contains n = true ↔
        (∃ i ∈ l, n ∈ i.loads) ∨ init.contains n = true by
    unfold Regula.Closed.Bundle.loadedSet
    rw [h]
    simp
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro init
    simp only [List.foldl_cons, ih, mem_insertFold, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h)
      · exact .inr h
    · rintro ((h | h) | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)

theorem unloaded_none (b : Regula.Closed.Bundle) (first : Regula.Closed.Input) :
    b.unloaded? first = none ↔ ∀ t ∈ first.targets, ∀ m ∈ t.modules, ∃ i ∈ b.envs, m ∈ i.loads := by
  unfold Regula.Closed.Bundle.unloaded?
  simp only [List.findSome?_eq_none_iff, Option.map_eq_none_iff, List.find?_eq_none]
  constructor
  · intro h t ht m hm
    exact (loadedSet_iff b m).mp (by simpa using h t ht m hm)
  · intro h t ht m hm
    have := (loadedSet_iff b m).mpr (h t ht m hm)
    simp [this]

/-- What the admission of a bundle decides. -/
theorem refusal_none_iff (b : Regula.Closed.Bundle) :
    b.refusal? = none ↔ (toBundle b).WellFormed ∧ ∀ i ∈ b.envs, i.axiomsMissing? = none := by
  have hmap : ∀ i, i ∈ (toBundle b).envs ↔ ∃ j ∈ b.envs, toSpec j = i := by
    intro i
    simp [toBundle]
  unfold Regula.Closed.Bundle.refusal?
  split
  · rename_i he
    simp only [reduceCtorEq, false_iff, not_and]
    intro hwf
    exact absurd (by simp [toBundle, he]) hwf.nonempty
  · rename_i first rest he
    have hfirst : first ∈ b.envs := by simp [he]
    have hrefusals : (b.envs.findSome? (·.refusal?)) = none ↔
        ∀ i ∈ b.envs, (toSpec i).WellFormed ∧ i.axiomsMissing? = none := by
      simp only [List.findSome?_eq_none_iff, input_refusal_none]
    have hproject : b.oneProject first = true ↔
        ∀ i ∈ b.envs, i.targets = first.targets ∧ i.manifest = first.manifest ∧
          i.modules = first.modules := by
      simp only [Regula.Closed.Bundle.oneProject, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
        and_assoc]
    have hclaims : b.claimsSome = true ↔
        ∃ i ∈ b.envs, ∃ t, (toSpec i).ClaimedTarget t := by
      simp only [Regula.Closed.Bundle.claimsSome, List.any_eq_true, claimedTarget_iff]
      constructor
      · rintro ⟨i, hi, e, -, hc⟩
        exact ⟨i, hi, _, hc⟩
      · rintro ⟨i, hi, t, p, x, hm⟩
        obtain ⟨e, he', hee⟩ := mem_manifest.mp hm
        have ht : e.target = t := congrArg Entry.target hee
        exact ⟨i, hi, e, he', by rw [ht]; exact ⟨p, x, hm⟩⟩
    constructor
    · intro h
      split at h
      · simp at h
      · rename_i hr
        have hall := hrefusals.mp hr
        split at h
        · simp at h
        · rename_i hp
          have hpr := hproject.mp (by
            cases hb : b.oneProject first with
            | false => simp [hb] at hp
            | true => rfl)
          split at h
          · simp at h
          · rename_i hcov
            have hcovv := (unloaded_none b first).mp hcov
            split at h
            · rename_i hcl
              refine ⟨⟨by simp [toBundle, he], ?_, ?_, ?_, ?_⟩, fun i hi => (hall i hi).2⟩
              · intro i hi
                obtain ⟨j, hj, rfl⟩ := (hmap i).mp hi
                exact (hall j hj).1
              · intro i hi j hj
                obtain ⟨x, hx, rfl⟩ := (hmap i).mp hi
                obtain ⟨y, hy, rfl⟩ := (hmap j).mp hj
                obtain ⟨t1, m1, r1⟩ := hpr x hx
                obtain ⟨t2, m2, r2⟩ := hpr y hy
                simp [toSpec, t1, m1, r1, t2, m2, r2]
              · intro i hi t ht m hm
                obtain ⟨x, hx, rfl⟩ := (hmap i).mp hi
                obtain ⟨t0, ht0, rfl⟩ := mem_targets.mp ht
                rw [(hpr x hx).1] at ht0
                obtain ⟨j, hj, hl⟩ := hcovv t0 ht0 m hm
                exact ⟨toSpec j, (hmap _).mpr ⟨j, hj, rfl⟩, hl⟩
              · obtain ⟨i, hi, t, hc⟩ := hclaims.mp hcl
                exact ⟨toSpec i, (hmap _).mpr ⟨i, hi, rfl⟩, t, hc⟩
            · simp at h
    · rintro ⟨hwf, hax⟩
      have hr : b.envs.findSome? (·.refusal?) = none := hrefusals.mpr fun i hi =>
        ⟨hwf.each _ ((hmap _).mpr ⟨i, hi, rfl⟩), hax i hi⟩
      have hp : b.oneProject first = true := by
        refine hproject.mpr fun i hi => ?_
        obtain ⟨h1, h2, h3, -, -⟩ := hwf.oneProject _ ((hmap _).mpr ⟨i, hi, rfl⟩) _
          ((hmap _).mpr ⟨first, hfirst, rfl⟩)
        simp only [toSpec] at h1 h2 h3
        exact ⟨(List.map_inj_right (fun _ _ h => target_inj h)).mp h1,
          (List.map_inj_right (fun _ _ h => entry_inj h)).mp h2,
          (List.map_inj_right (fun _ _ h => record_inj h)).mp h3⟩
      have hcov : b.unloaded? first = none := (unloaded_none b first).mpr fun t ht m hm => by
        obtain ⟨j, hj, hl⟩ := hwf.covered _ ((hmap _).mpr ⟨first, hfirst, rfl⟩) (target t)
          (mem_targets.mpr ⟨t, ht, rfl⟩) m hm
        obtain ⟨y, hy, rfl⟩ := (hmap j).mp hj
        exact ⟨y, hy, hl⟩
      have hcl := hclaims.mpr (by
        obtain ⟨i, hi, t, hc⟩ := hwf.claims
        obtain ⟨y, hy, rfl⟩ := (hmap i).mp hi
        exact ⟨y, hy, t, hc⟩)
      rw [hr]
      simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hcov, hcl]

/-- A list that `dedupe` leaves empty was empty. -/
theorem dedupe_eq_nil {fs : List Regula.Closed.Finding} (h : Regula.Closed.dedupe fs = []) :
    fs = [] := by
  cases fs with
  | nil => rfl
  | cons f fs =>
    exfalso
    have step : ∀ (l : List Regula.Closed.Finding) (s : Std.HashSet String)
        (acc : List Regula.Closed.Finding), acc ≠ [] →
        (l.foldl (init := (s, acc)) fun (seen, acc) f =>
          let key := s!"{f.rule.spelling}|{f.subject}|{f.module}|{f.detail}"
          if seen.contains key then (seen, acc) else (seen.insert key, f :: acc)).2 ≠ [] := by
      intro l
      induction l with
      | nil => intro _ _ h; exact h
      | cons g gs ih =>
        intro s acc hne
        simp only [List.foldl_cons]
        split
        · exact ih _ _ hne
        · exact ih _ _ (List.cons_ne_nil _ _)
    simp only [Regula.Closed.dedupe, List.foldl_cons, List.reverse_eq_nil_iff] at h
    revert h
    split
    · simp_all
    · exact step _ _ _ (List.cons_ne_nil _ _)

theorem nil_iff_no_subject (fs : List Regula.Closed.Finding) :
    fs = [] ↔ ∀ s, s ∉ fs.map (·.subject) := by
  cases fs with
  | nil => simp
  | cons f fs =>
    constructor
    · intro h
      cases h
    · intro h
      exact absurd (List.mem_cons_self ..) (h f.subject)

/-- An admitted input has no finding exactly when every rule that reads one environment holds of
it. -/
theorem findings_nil_iff {i : Regula.Closed.Input} (h : Admitted i) (a : Regula.Closed.Allowlists) :
    i.findings a = [] ↔ AllHold (allowlists a) (toSpec i) := by
  have hu := unique_of_wf h.wf
  have hc : ∀ r, i.check a i.tables r = [] ↔ (∀ s, s ∉ (i.check a i.tables r).map (·.subject)) :=
    fun r => nil_iff_no_subject _
  have hall : i.findings a = [] ↔ ∀ r, i.check a i.tables r = [] := by
    simp only [Regula.Closed.Input.findings, List.flatMap_eq_nil_iff]
    exact ⟨fun h r => h r (Regula.RuleId.mem_all r), fun h r _ => h r⟩
  rw [hall]
  constructor
  · intro hn
    have at' : ∀ r s, s ∉ (i.check a i.tables r).map (·.subject) := fun r => (hc r).mp (hn r)
    refine ⟨fun c hv => at' .projectAxiom c ((rg1001_exact i c).mpr hv),
      fun c hv => at' .proofHole c ((rg1002_exact h c).mpr hv),
      fun c hv => at' .unknownAxiom c ((rg1003_exact h c).mpr hv),
      fun c hv => at' .compilerTrusting c ((rg1004_exact h c).mpr hv),
      fun c hv => at' .profileExceeded c ((rg1005_exact h c).mpr hv),
      fun c hv => at' .escapeHatch c ((rg1006_exact hu c).mpr hv),
      fun c hv => at' .executableContract c ((rg1007_exact hu c).mpr hv),
      fun c hv => at' .decisionContract c ((rg1008_exact hu c).mpr hv),
      fun c hv => at' .sharedTest c ((rg1009_exact hu c).mpr hv),
      fun c hv => at' .configuration c ((rg2002_exact i c).mpr hv),
      fun c hv => at' .coverage c ((rg2004_exact i c).mpr hv),
      fun c hv => at' .communityConfiguration c ((rg2006_exact a.options i c).mpr hv),
      fun c hv => at' .closedSubset c ((rg2007_exact a.extensions i c).mpr hv),
      fun c hv => at' .executionUnresolved c ((rg3001_exact hu c).mpr hv),
      fun c hv => at' .executionBoundary c ((rg3002_exact h c).mpr hv)⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ r
    rw [hc r]
    intro s hs
    cases r
    · exact h1 s ((rg1001_exact i s).mp hs)
    · exact h2 s ((rg1002_exact h s).mp hs)
    · exact h3 s ((rg1003_exact h s).mp hs)
    · exact h4 s ((rg1004_exact h s).mp hs)
    · exact h5 s ((rg1005_exact h s).mp hs)
    · exact h6 s ((rg1006_exact hu s).mp hs)
    · exact h7 s ((rg1007_exact hu s).mp hs)
    · exact h8 s ((rg1008_exact hu s).mp hs)
    · exact h9 s ((rg1009_exact hu s).mp hs)
    · simp [Regula.Closed.Input.check] at hs
    · exact h10 s ((rg2002_exact i s).mp hs)
    · simp [Regula.Closed.Input.check] at hs
    · exact h11 s ((rg2004_exact i s).mp hs)
    · simp [Regula.Closed.Input.check] at hs
    · exact h12 s ((rg2006_exact a.options i s).mp hs)
    · exact h13 s ((rg2007_exact a.extensions i s).mp hs)
    · exact h14 s ((rg3001_exact hu s).mp hs)
    · exact h15 s ((rg3002_exact h s).mp hs)
    all_goals simp [Regula.Closed.Input.check] at hs

end Link

open Link

/-- A bundle that the admission refuses is `incomplete`: a part of the input that cannot be read is
never a pass and never an empty report. -/
theorem run_refused {a : Regula.Closed.Allowlists} {b : Regula.Closed.Bundle}
    (h : b.refusal? ≠ none) : (Regula.Closed.run a b).1 = .incomplete := by
  unfold Regula.Closed.run
  split
  · rfl
  · contradiction

/-- A bundle that has the closed form, with the axiom sets that `AxiomsRead` states, is not
`incomplete`, and it is `pass` exactly when every rule that reads one environment holds of each of
its environments. RG6001 is leaf #485's, so this is `gateRecord`'s third property without it. -/
theorem run_complete {a : Regula.Closed.Allowlists} {b : Regula.Closed.Bundle}
    (h : (toBundle b).WellFormed) (hax : ∀ i ∈ b.envs, AxiomsRead i) :
    (Regula.Closed.run a b).1 ≠ .incomplete ∧
      ((Regula.Closed.run a b).1 = .pass ↔
        ∀ i ∈ (toBundle b).envs, AllHold (allowlists a) i) := by
  have hmem : ∀ i ∈ b.envs, toSpec i ∈ (toBundle b).envs := fun i hi => by
    simp only [toBundle, List.mem_map]
    exact ⟨i, hi, rfl⟩
  have hadm : ∀ i ∈ b.envs, Admitted i := fun i hi => ⟨h.each _ (hmem i hi), hax i hi⟩
  have hnone : b.refusal? = none := (refusal_none_iff b).mpr ⟨h, fun i hi =>
    (axiomsMissing_none i).mpr (hax i hi).present⟩
  unfold Regula.Closed.run
  rw [hnone]
  simp only
  constructor
  · split <;> simp
  · have hempty : Regula.Closed.dedupe (b.envs.flatMap (·.findings a)) = [] ↔
        ∀ i ∈ b.envs, i.findings a = [] := by
      rw [← List.flatMap_eq_nil_iff]
      refine ⟨dedupe_eq_nil, fun hf => ?_⟩
      rw [hf]
      rfl
    have : (if (Regula.Closed.dedupe (b.envs.flatMap (·.findings a))).isEmpty then
        Regula.Closed.Verdict.pass else .fail) = .pass ↔
        Regula.Closed.dedupe (b.envs.flatMap (·.findings a)) = [] := by
      cases Regula.Closed.dedupe (b.envs.flatMap (·.findings a)) <;> simp
    rw [this, hempty]
    constructor
    · intro hf i hi
      obtain ⟨y, hy, rfl⟩ : ∃ y ∈ b.envs, toSpec y = i := by
        simpa [toBundle] using hi
      exact (findings_nil_iff (hadm y hy) a).mp (hf y hy)
    · intro hf i hi
      exact (findings_nil_iff (hadm i hi) a).mpr (hf _ (hmem i hi))

/-- A pass of the checker is an admitted bundle: an input that the admission refuses is never a pass. -/
theorem run_pass_admitted {a : Regula.Closed.Allowlists} {b : Regula.Closed.Bundle}
    (hp : (Regula.Closed.run a b).1 = .pass) : b.refusal? = none := by
  cases hr : b.refusal? with
  | none => rfl
  | some why =>
    have := run_refused (a := a) (b := b) (by simp [hr])
    rw [this] at hp
    cases hp

/-- A pass of the checker holds each rule of each environment, when the axiom sets of the input are
the ones that `AxiomOf` states: the direction of `run_complete` that a user of the verdict reads. The
admission gives the rest of `run_complete`'s hypotheses. -/
theorem run_pass_holds {a : Regula.Closed.Allowlists} {b : Regula.Closed.Bundle}
    (hax : ∀ i ∈ b.envs, AxiomsRead i) (hp : (Regula.Closed.run a b).1 = .pass) :
    ∀ i ∈ (toBundle b).envs, AllHold (allowlists a) i :=
  (run_complete ((refusal_none_iff b).mp (run_pass_admitted hp)).1 hax).2.mp hp

/-- A pass of the checker holds RG2006 and RG2007 of each environment, at the allowlists it ran with.
These two rules read no axiom set, so this has no hypothesis. -/
theorem run_pass_holds_closed_subset {a : Regula.Closed.Allowlists} {b : Regula.Closed.Bundle}
    (hp : (Regula.Closed.run a b).1 = .pass) :
    ∀ i ∈ b.envs, (∀ t, ¬ Violates2006 (fun n => a.options n = true) (toSpec i) t) ∧
      ∀ m, ¬ Violates2007 (fun n => a.extensions n = true) (toSpec i) m := by
  intro i hi
  have hnil : Regula.Closed.dedupe (b.envs.flatMap (·.findings a)) = [] := by
    unfold Regula.Closed.run at hp
    rw [run_pass_admitted hp] at hp
    simp only at hp
    cases he : Regula.Closed.dedupe (b.envs.flatMap (·.findings a)) with
    | nil => rfl
    | cons _ _ => simp [he] at hp
  have hfind : i.findings a = [] := List.flatMap_eq_nil_iff.mp (dedupe_eq_nil hnil) i hi
  have hall : ∀ r, i.check a i.tables r = [] := fun r =>
    List.flatMap_eq_nil_iff.mp hfind r (Regula.RuleId.mem_all r)
  refine ⟨fun t hv => ?_, fun m hv => ?_⟩
  · have := (rg2006_exact a.options i t).mpr hv
    have hn : i.optionFindings a.options = [] := hall .communityConfiguration
    simp [hn] at this
  · have := (rg2007_exact a.extensions i m).mpr hv
    have hn : i.extensionFindings a.extensions = [] := hall .closedSubset
    simp [hn] at this

end RegulaSpecification
