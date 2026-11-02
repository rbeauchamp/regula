/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Link

/-!
# What the rules' tables hold

Each theorem here holds of every value of `Regula.Closed.Tables i`, so no theorem about a rule has a hypothesis
about the tables it reads.
-/

namespace RegulaSpecification

open Lean (Name)

namespace Link

variable {i : Regula.Closed.Input}

theorem get_of_mem (t : Regula.Closed.Tables i) {d : Regula.Closed.Decl} (hd : d ∈ i.decls) :
    t.index[d.name]? = some d :=
  (t.mem_index _ _).mpr ⟨hd, rfl⟩

theorem any_index_iff (t : Regula.Closed.Tables i) (P : Regula.Closed.Decl → Bool) (n : Name) :
    t.index[n]?.any P = true ↔ ∃ d ∈ i.decls, d.name = n ∧ P d = true := by
  cases h : t.index[n]? with
  | none =>
    simp only [Option.any_none, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro d hd hn
    rw [← hn, get_of_mem t hd] at h
    cases h
  | some d =>
    obtain ⟨hd, hn⟩ := (t.mem_index _ _).mp h
    simp only [Option.any_some]
    constructor
    · exact fun hp => ⟨d, hd, hn, hp⟩
    · rintro ⟨d', hd', hn', hp⟩
      have := get_of_mem t hd'
      rw [hn', h] at this
      simp only [Option.some.injEq] at this
      exact this ▸ hp

theorem mem_claimed (t : Regula.Closed.Tables i) {d : Regula.Closed.Decl} :
    d ∈ t.claimed ↔ d ∈ i.decls ∧ (toSpec i).ClaimedModule d.module :=
  t.mem_claimed d

theorem claimedName_of_mem {c : Name} (h : (toSpec i).ClaimedName c) :
    ∃ d ∈ i.decls, d.name = c ∧ (toSpec i).ClaimedModule d.module := by
  obtain ⟨x, hx, hn, hc⟩ := h
  obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
  exact ⟨d, hd, hn, hc⟩

theorem reaches_iff {c e : Name} : i.Reaches c e ↔ (toSpec i).Reaches c e := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl _
    | step d hd hn hu _ ih => exact .step (decl d) (mem_decls.mpr ⟨d, hd, rfl⟩) hn hu ih
  · intro h
    induction h with
    | refl => exact .refl _
    | step x hx hn hu _ ih =>
      obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
      exact .step d hd hn hu ih

theorem kind_axiom_iff (d : Regula.Closed.Decl) :
    d.kind = .axiom ↔ (decl d).kind = .axiom := by
  cases hd : d.kind <;> simp [decl, constKind, hd]

/-- No field of the input holds the axiom set, so no hypothesis about a reader stands behind this. -/
theorem axiomSet_iff (t : Regula.Closed.Tables i) (c a : Name) :
    a ∈ t.axiomSet c ↔ (toSpec i).AxiomOf c a := by
  rw [t.mem_axiomSet]
  constructor
  · rintro ⟨hr, d, hd, rfl, hk⟩
    exact ⟨reaches_iff.mp hr, decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, (kind_axiom_iff d).mp hk⟩
  · rintro ⟨hr, x, hx, rfl, hk⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    exact ⟨reaches_iff.mpr hr, d, hd, rfl, (kind_axiom_iff d).mpr hk⟩

end Link

end RegulaSpecification
