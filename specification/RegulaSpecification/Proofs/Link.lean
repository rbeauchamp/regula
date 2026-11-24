module

public import Regula.Input
public import RegulaSpecification.RuleRecord

@[expose] public section

namespace RegulaSpecification

open Lean (Name)

namespace Link

def profile : Regula.Closed.Profile → Profile
  | .kernelOnly => .kernelOnly
  | .choiceFree => .choiceFree
  | .standardLogical => .standardLogical

def profile' : Profile → Regula.Closed.Profile
  | .kernelOnly => .kernelOnly
  | .choiceFree => .choiceFree
  | .standardLogical => .standardLogical

def constKind : Regula.Closed.Kind → Kind
  | .axiom => .axiom
  | .definition => .definition
  | .theorem => .theorem
  | .opaque => .opaque
  | .quotient => .quotient
  | .inductive => .inductive
  | .constructor => .constructor
  | .recursor => .recursor

def constKind' : Kind → Regula.Closed.Kind
  | .axiom => .axiom
  | .definition => .definition
  | .theorem => .theorem
  | .opaque => .opaque
  | .quotient => .quotient
  | .inductive => .inductive
  | .constructor => .constructor
  | .recursor => .recursor

def safety : Regula.Closed.Safety → Safety
  | .safe => .safe
  | .unsafe => .unsafe
  | .partial => .partial

def safety' : Safety → Regula.Closed.Safety
  | .safe => .safe
  | .unsafe => .unsafe
  | .partial => .partial

def ctorIdxForm : Regula.Closed.CtorIdxForm → CtorIdxForm
  | .none => .none
  | .defn ind => .defn ind
  | .impl ind => .impl ind

def ctorIdxForm' : CtorIdxForm → Regula.Closed.CtorIdxForm
  | .none => .none
  | .defn ind => .defn ind
  | .impl ind => .impl ind

def decl (d : Regula.Closed.Decl) : Decl where
  name := d.name
  module := d.module
  kind := constKind d.kind
  safety := safety d.safety
  uses := d.uses
  valueUses := d.valueUses
  implementedBy := d.implementedBy
  isExtern := d.isExtern
  initFn := d.initFn
  inToolchain := d.inToolchain
  ctorIdxForm := ctorIdxForm d.ctorIdxForm

def decl' (d : Decl) : Regula.Closed.Decl where
  name := d.name
  module := d.module
  kind := constKind' d.kind
  safety := safety' d.safety
  uses := d.uses
  valueUses := d.valueUses
  implementedBy := d.implementedBy
  isExtern := d.isExtern
  initFn := d.initFn
  inToolchain := d.inToolchain
  ctorIdxForm := ctorIdxForm' d.ctorIdxForm

def csimp (e : Regula.Closed.CSimpEntry) : CSimpEntry where
  module := e.module
  thm := e.thm

def csimp' (e : CSimpEntry) : Regula.Closed.CSimpEntry where
  module := e.module
  thm := e.thm

def toSpecDraft (d : Regula.Closed.Draft) : Input where
  profile := profile d.profile
  modules := d.modules
  moduleFiles := d.moduleFiles
  claimedConstants := d.claimedConstants
  csimps := d.csimps.map csimp
  decls := d.decls.map decl
  unique := by
    have h := d.unique
    simpa [decl, Function.comp_def] using h

def toSpec (i : Regula.Closed.Input) : Input := toSpecDraft i.toDraft

def ofSpec (s : Input) : Regula.Closed.Draft where
  profile := profile' s.profile
  modules := s.modules
  moduleFiles := s.moduleFiles
  claimedConstants := s.claimedConstants
  csimps := s.csimps.map csimp'
  decls := s.decls.map decl'
  unique := by
    have h := s.unique
    simpa [decl', Function.comp_def] using h

def ofAdmitted (s : Admitted Input) : Regula.Closed.Input where
  toDraft := ofSpec s.1
  closed := by
    intro d hd u hu
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
    obtain ⟨e, he, hn⟩ := s.2.closed x hx u hu
    exact ⟨decl' e, List.mem_map.mpr ⟨e, he, rfl⟩, hn⟩
  claims := s.2.claims

theorem profile_surj (p : Profile) : profile (profile' p) = p := by cases p <;> rfl

theorem decl_decl' (d : Decl) : decl (decl' d) = d := by
  rcases d with ⟨_, _, k, s, _, _, _, _, _, _, cf⟩
  cases k <;> cases s <;> cases cf <;> rfl

theorem csimp_csimp' (e : CSimpEntry) : csimp (csimp' e) = e := by
  cases e
  rfl

theorem toSpecDraft_ofSpec (s : Input) : toSpecDraft (ofSpec s) = s := by
  rcases s with ⟨p, m, mf, cc, cs, ds, u⟩
  simp only [toSpecDraft, ofSpec, profile_surj, List.map_map, Function.comp_def, decl_decl',
    csimp_csimp', List.map_id']

theorem toSpec_ofAdmitted (s : Admitted Input) : toSpec (ofAdmitted s) = s.1 :=
  toSpecDraft_ofSpec s.1

theorem mem_declsDraft {d : Regula.Closed.Draft} {x : Decl} :
    x ∈ (toSpecDraft d).decls ↔ ∃ e ∈ d.decls, decl e = x := by simp [toSpecDraft]

theorem mem_decls {i : Regula.Closed.Input} {x : Decl} :
    x ∈ (toSpec i).decls ↔ ∃ d ∈ i.decls, decl d = x := mem_declsDraft

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

theorem wf_toSpec (i : Regula.Closed.Input) : (toSpec i).WellFormed :=
  (wf_toSpecDraft_iff i.toDraft).mpr ⟨i.closed, i.claims⟩

end Link

end RegulaSpecification
