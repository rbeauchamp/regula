/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import Regula.Rules
import RegulaSpecification.CasesGate

/-!
# The link from the implementation's input to the specification's

The checker runs over `Regula.Closed.Input`, and the specification states each rule over
`RegulaSpecification.Input`: two types with the same data, so that the specification is written
independently of the code. A value of the checker's type also holds the proof of the closed form,
and `wf_toSpec` carries that proof to the specification's statement of that form. `toSpec` carries
an input of the checker to the specification's, and each `rg100N_exact` is stated about
the function that the checker runs on an input `i` and the predicate of the specification at
`toSpec i`.

`ofSpec` goes the other way, so that the admission of the checker is a function of the
specification's input, and `ofAdmitted` carries a well-formed input, so that a function of the
checker is a checker of the specification's input (`Checker`) and can meet a rule's intent record.
-/

namespace RegulaSpecification

open Lean (Name)

namespace Link

/-- The implementation's profile in the specification. -/
def profile : Regula.Closed.Profile → Profile
  | .kernelOnly => .kernelOnly
  | .choiceFree => .choiceFree
  | .standardLogical => .standardLogical

/-- The specification's profile in the implementation. -/
def profile' : Profile → Regula.Closed.Profile
  | .kernelOnly => .kernelOnly
  | .choiceFree => .choiceFree
  | .standardLogical => .standardLogical

/-- The implementation's kind of constant in the specification. -/
def constKind : Regula.Closed.Kind → Kind
  | .axiom => .axiom
  | .definition => .definition
  | .theorem => .theorem
  | .opaque => .opaque
  | .quotient => .quotient
  | .inductive => .inductive
  | .constructor => .constructor
  | .recursor => .recursor

/-- The specification's kind of constant in the implementation. -/
def constKind' : Kind → Regula.Closed.Kind
  | .axiom => .axiom
  | .definition => .definition
  | .theorem => .theorem
  | .opaque => .opaque
  | .quotient => .quotient
  | .inductive => .inductive
  | .constructor => .constructor
  | .recursor => .recursor

/-- The implementation's safety in the specification. -/
def safety : Regula.Closed.Safety → Safety
  | .safe => .safe
  | .unsafe => .unsafe
  | .partial => .partial

/-- The specification's safety in the implementation. -/
def safety' : Safety → Regula.Closed.Safety
  | .safe => .safe
  | .unsafe => .unsafe
  | .partial => .partial

/-- The implementation's constant in the specification. -/
def decl (d : Regula.Closed.Decl) : Decl where
  name := d.name
  module := d.module
  kind := constKind d.kind
  safety := safety d.safety
  uses := d.uses
  valueUses := d.valueUses
  implementedBy := d.implementedBy
  isExtern := d.isExtern
  inToolchain := d.inToolchain

/-- The specification's constant in the implementation. -/
def decl' (d : Decl) : Regula.Closed.Decl where
  name := d.name
  module := d.module
  kind := constKind' d.kind
  safety := safety' d.safety
  uses := d.uses
  valueUses := d.valueUses
  implementedBy := d.implementedBy
  isExtern := d.isExtern
  inToolchain := d.inToolchain

/-- A reading of the checker as the specification's input. -/
def toSpecDraft (d : Regula.Closed.Draft) : Input where
  profile := profile d.profile
  modules := d.modules
  decls := d.decls.map decl
  unique := by
    have h := d.unique
    simpa [decl, Function.comp_def] using h

/-- The input of the checker as the specification's input. -/
def toSpec (i : Regula.Closed.Input) : Input := toSpecDraft i.toDraft

/-- The specification's input as a reading of the checker. -/
def ofSpec (s : Input) : Regula.Closed.Draft where
  profile := profile' s.profile
  modules := s.modules
  decls := s.decls.map decl'
  unique := by
    have h := s.unique
    simpa [decl', Function.comp_def] using h

/-- The specification's well-formed input as the input of the checker. -/
def ofAdmitted (s : Admitted Input) : Regula.Closed.Input where
  toDraft := ofSpec s.1
  closed := by
    intro d hd u hu
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
    obtain ⟨e, he, hn⟩ := s.2.closed x hx u hu
    exact ⟨decl' e, List.mem_map.mpr ⟨e, he, rfl⟩, hn⟩
  claims := s.2.claims

/-- `profile'` loses nothing. -/
theorem profile_surj (p : Profile) : profile (profile' p) = p := by cases p <;> rfl

/-- `decl'` loses nothing. -/
theorem decl_decl' (d : Decl) : decl (decl' d) = d := by
  rcases d with ⟨_, _, k, s, _, _, _, _, _⟩
  cases k <;> cases s <;> rfl

/-- `ofSpec` loses nothing that the specification's input holds. -/
theorem toSpecDraft_ofSpec (s : Input) : toSpecDraft (ofSpec s) = s := by
  rcases s with ⟨p, m, ds, u⟩
  simp only [toSpecDraft, ofSpec, profile_surj, List.map_map, Function.comp_def, decl_decl',
    List.map_id']

/-- `ofAdmitted` loses nothing that the specification's input holds. -/
theorem toSpec_ofAdmitted (s : Admitted Input) : toSpec (ofAdmitted s) = s.1 :=
  toSpecDraft_ofSpec s.1

/-- The constants of the specification's input are those of the checker's reading. -/
theorem mem_declsDraft {d : Regula.Closed.Draft} {x : Decl} :
    x ∈ (toSpecDraft d).decls ↔ ∃ e ∈ d.decls, decl e = x := by simp [toSpecDraft]

/-- The constants of the specification's input are those of the checker's input. -/
theorem mem_decls {i : Regula.Closed.Input} {x : Decl} :
    x ∈ (toSpec i).decls ↔ ∃ d ∈ i.decls, decl d = x := mem_declsDraft

/-- A reading of the checker has the closed form of the specification exactly when each mentioned
constant is held and a module is claimed. -/
theorem wf_toSpecDraft_iff (d : Regula.Closed.Draft) :
    (toSpecDraft d).WellFormed ↔
      (∀ x ∈ d.decls, ∀ u ∈ x.uses, ∃ e ∈ d.decls, e.name = u) ∧ d.modules ≠ [] := by
  constructor
  · intro h
    refine ⟨fun x hx u hu => ?_, h.claims⟩
    obtain ⟨y, hy, hn⟩ := h.closed (decl x) (mem_declsDraft.mpr ⟨x, hx, rfl⟩) u hu
    obtain ⟨e, he, rfl⟩ := mem_declsDraft.mp hy
    exact ⟨e, he, hn⟩
  · rintro ⟨hc, hm⟩
    refine ⟨fun x hx u hu => ?_, hm⟩
    obtain ⟨y, hy, rfl⟩ := mem_declsDraft.mp hx
    obtain ⟨e, he, hn⟩ := hc y hy u hu
    exact ⟨decl e, mem_declsDraft.mpr ⟨e, he, rfl⟩, hn⟩

/-- Each input of the checker has the closed form of the specification: the type carries it. -/
theorem wf_toSpec (i : Regula.Closed.Input) : (toSpec i).WellFormed :=
  (wf_toSpecDraft_iff i.toDraft).mpr ⟨i.closed, i.claims⟩

end Link

end RegulaSpecification
