module

public import RegulaSpecification.Proofs.Load

@[expose] public section

namespace RegulaSpecification

open Lean (Name ConstantInfo)
open Link

namespace Loader

variable {f : Regula.Load.Facts} {roots : List Name} {p : Regula.Closed.Profile}

inductive OccursIn (c : Name) : Lean.Expr → Prop
  | const (ls : List Lean.Level) : OccursIn c (.const c ls)
  | projType (i : Nat) (b : Lean.Expr) : OccursIn c (.proj c i b)
  | proj (t : Name) (i : Nat) {b : Lean.Expr} : OccursIn c b → OccursIn c (.proj t i b)
  | appFn {f : Lean.Expr} (a : Lean.Expr) : OccursIn c f → OccursIn c (.app f a)
  | appArg (f : Lean.Expr) {a : Lean.Expr} : OccursIn c a → OccursIn c (.app f a)
  | lamType (n : Name) {d : Lean.Expr} (b : Lean.Expr) (bi : Lean.BinderInfo) :
      OccursIn c d → OccursIn c (.lam n d b bi)
  | lamBody (n : Name) (d : Lean.Expr) {b : Lean.Expr} (bi : Lean.BinderInfo) :
      OccursIn c b → OccursIn c (.lam n d b bi)
  | forallType (n : Name) {d : Lean.Expr} (b : Lean.Expr) (bi : Lean.BinderInfo) :
      OccursIn c d → OccursIn c (.forallE n d b bi)
  | forallBody (n : Name) (d : Lean.Expr) {b : Lean.Expr} (bi : Lean.BinderInfo) :
      OccursIn c b → OccursIn c (.forallE n d b bi)
  | letType (n : Name) {t : Lean.Expr} (v b : Lean.Expr) (nd : Bool) :
      OccursIn c t → OccursIn c (.letE n t v b nd)
  | letValue (n : Name) (t : Lean.Expr) {v : Lean.Expr} (b : Lean.Expr) (nd : Bool) :
      OccursIn c v → OccursIn c (.letE n t v b nd)
  | letBody (n : Name) (t v : Lean.Expr) {b : Lean.Expr} (nd : Bool) :
      OccursIn c b → OccursIn c (.letE n t v b nd)
  | mdata (m : Lean.MData) {b : Lean.Expr} : OccursIn c b → OccursIn c (.mdata m b)

def UsedConstantsComplete : Prop := ∀ c e, OccursIn c e → c ∈ e.getUsedConstants

def InfoOccurs : ConstantInfo → Name → Prop
  | .axiomInfo v, u => OccursIn u v.type
  | .defnInfo v, u => OccursIn u v.type ∨ OccursIn u v.value
  | .thmInfo v, u => OccursIn u v.type ∨ OccursIn u v.value
  | .opaqueInfo v, u => OccursIn u v.type ∨ OccursIn u v.value
  | .quotInfo v, u => OccursIn u v.type ∨ u = `Eq
  | .ctorInfo v, u => OccursIn u v.type ∨ u = v.induct
  | .recInfo v, u => OccursIn u v.type ∨ u ∈ v.all
  | .inductInfo v, u => OccursIn u v.type ∨ u ∈ v.ctors ∨ u ∈ v.all

def ValueOccurs : ConstantInfo → Name → Prop
  | .defnInfo v, u => OccursIn u v.value
  | .thmInfo v, u => OccursIn u v.value
  | .opaqueInfo v, u => OccursIn u v.value
  | .axiomInfo _, _ | .quotInfo _, _ | .inductInfo _, _ | .ctorInfo _, _ | .recInfo _, _ => False

inductive OccursReaches (f : Regula.Load.Facts) : Name → Name → Prop
  | refl (c : Name) : OccursReaches f c c
  | step {c u e : Name} (k : ConstantInfo) : f.env.constants.map₁[c]? = some k →
      (InfoOccurs k u ∨ ∃ v ∈ f.stated.getD c [], InfoOccurs v u) → OccursReaches f u e →
      OccursReaches f c e

theorem mentions_of_occurs (hused : UsedConstantsComplete) {k : ConstantInfo} {u : Name}
    (h : InfoOccurs k u) : Mentions k u := by
  cases k with
  | axiomInfo v => exact hused _ _ h
  | defnInfo v => exact h.imp (hused _ _) (hused _ _)
  | thmInfo v => exact h.imp (hused _ _) (hused _ _)
  | opaqueInfo v => exact h.imp (hused _ _) (hused _ _)
  | quotInfo v => exact h.imp_left (hused _ _)
  | ctorInfo v => exact h.imp_left (hused _ _)
  | recInfo v => exact h.imp_left (hused _ _)
  | inductInfo v => exact h.imp_left (hused _ _)

theorem valueMentions_of_occurs (hused : UsedConstantsComplete) {k : ConstantInfo} {u : Name}
    (h : ValueOccurs k u) : ValueMentions k u := by
  cases k with
  | defnInfo v | thmInfo v | opaqueInfo v => exact hused _ _ h
  | axiomInfo v | quotInfo v | ctorInfo v | recInfo v | inductInfo v => exact h

theorem envReaches_of_occurs (hused : UsedConstantsComplete) {c e : Name}
    (h : OccursReaches f c e) : EnvReaches f c e := by
  induction h with
  | refl => exact .refl _
  | step k hk ho _ ih =>
    exact .step ⟨k, hk, ho.imp (mentions_of_occurs hused)
      fun ⟨v, hv, hu⟩ => ⟨v, hv, mentions_of_occurs hused hu⟩⟩ ih

theorem pass_occurs (hused : UsedConstantsComplete)
    (h : (Regula.Closed.decision (f.input roots p)).verdict = .pass) {n m : Name}
    {info : ConstantInfo} (hn : f.env.constants.map₁[n]? = some info)
    (hm : f.moduleOf? n = some m) (hc : m ∈ f.claimed) :
    (∀ l ∈ loopConstructs, ¬ ValueOccurs info l) ∧
      ((∃ v, info = .defnInfo v) ∨ (∃ v, info = .opaqueInfo v) → ¬ ValueOccurs info ``Lean.Order.fix) ∧
      ∀ a, OccursReaches f n a → EnvAxiom f a → EnvAdmits f p a := by
  obtain ⟨-, h6, h7, hfix, h8, -⟩ := (pass_floor h).2.2.2.2.2.2 n info m hn hm hc
  exact ⟨fun l hl ho => h7 l hl (valueMentions_of_occurs hused ho),
    fun hrun ho => hfix hrun (valueMentions_of_occurs hused ho),
    fun a hr hax => h8 a (envReaches_of_occurs hused hr) hax⟩

theorem claimedConstants_complete (hsize : f.env.header.moduleData.size = f.modules.size) {k : Nat}
    {lm : Regula.Load.LoadedModule} (hk : f.modules[k]? = some lm) (hc : lm.claimed = true) :
    ∃ data, f.env.header.moduleData[k]? = some data ∧
      ∀ n info, (n, info) ∈ data.constNames.zip data.constants →
        (lm.name, n, info) ∈ f.claimedConstants := by
  have hlt : k < f.modules.size := (Array.getElem?_eq_some_iff.mp hk).1
  refine ⟨f.env.header.moduleData[k]'(hsize ▸ hlt), Array.getElem?_eq_getElem _,
    fun n info hx => ?_⟩
  exact mem_claimedConstants.mpr ⟨k, lm, _, hk, hc, rfl, Array.getElem?_eq_getElem _, hx⟩

end Loader

end RegulaSpecification
