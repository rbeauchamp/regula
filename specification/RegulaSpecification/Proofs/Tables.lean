/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Link

/-!
# What the rules' tables hold

A value of `Regula.Closed.Tables i` carries what each of its tables holds of the input `i`. These
theorems state that in terms of the specification's input: the constants by name, the constants of
claimed modules and the axiom set of each constant. Each holds of every value of `Tables i`, so no
theorem about a rule has a hypothesis about the tables it reads.
-/

namespace RegulaSpecification

open Lean (Name)

namespace Link

variable {i : Regula.Closed.Input}

/-- A constant of the input is in each index, under its name. -/
theorem get_of_mem (t : Regula.Closed.Tables i) {d : Regula.Closed.Decl} (hd : d ∈ i.decls) :
    t.index[d.name]? = some d :=
  (t.mem_index _ _).mpr ⟨hd, rfl⟩

/-- What a function of the constant that a name has decides, in terms of the input's constants. -/
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

/-- The table of claimed constants, against the specification's claimed modules. -/
theorem mem_claimed (t : Regula.Closed.Tables i) {d : Regula.Closed.Decl} :
    d ∈ t.claimed ↔ d ∈ i.decls ∧ (toSpec i).ClaimedModule d.module :=
  t.mem_claimed d

/-- A claimed name of the specification's input is that of a claimed constant of the checker's. -/
theorem claimedName_of_mem {c : Name} (h : (toSpec i).ClaimedName c) :
    ∃ d ∈ i.decls, d.name = c ∧ (toSpec i).ClaimedModule d.module := by
  obtain ⟨x, hx, hn, hc⟩ := h
  obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
  exact ⟨d, hd, hn, hc⟩

/-! ## The axiom sets -/

/-- The walk of the checker's input is the walk of the specification's. -/
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

/-- The kind that the checker reads is `axiom` exactly when the specification's is. -/
theorem kind_axiom_iff (d : Regula.Closed.Decl) :
    d.kind = .axiom ↔ (decl d).kind = .axiom := by
  cases hd : d.kind <;> simp [decl, constKind, hd]

/-- The set that the rules read is exactly the axiom set that the specification states. No field of
the input holds it, so no hypothesis about a reader stands behind this. -/
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
