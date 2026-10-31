/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Load

/-!
# Two facts about Lean, as hypotheses

Each theorem here states what a pass gives with a fact about Lean as its hypothesis, so its
statement names what it rests on (`pass_occurs`, `claimedConstants_complete`).

`Expr.getUsedConstants` runs an `opaque` function that `@[implemented_by]` replaces
(`Lean/Util/FoldConsts.lean`), so no proof can read its body. `pass_iff` is therefore stated over
what that function gives. The theorems below state the same floor over the constants that occur in
an expression, a statement that reads no Lean function, with the fact about Lean as their one
hypothesis. `UsedConstantsComplete` is that fact, so a reader sees it in the theorem's statement.
-/

namespace RegulaSpecification

open Lean (Name ConstantInfo)
open Link

namespace Loader

variable {f : Regula.Load.Facts} {roots : List Name} {p : Regula.Closed.Profile}

/-- The constant `c` occurs in `e`: as a constant, or as the structure of a projection, the
positions at which `Expr.foldConsts` visits one (`Lean/Util/FoldConsts.lean:36-42`). -/
inductive OccursIn (c : Name) : Lean.Expr → Prop
  /-- `c` itself. -/
  | const (ls : List Lean.Level) : OccursIn c (.const c ls)
  /-- The structure of a projection. -/
  | projType (i : Nat) (b : Lean.Expr) : OccursIn c (.proj c i b)
  /-- Below a projection. -/
  | proj (t : Name) (i : Nat) {b : Lean.Expr} : OccursIn c b → OccursIn c (.proj t i b)
  /-- In the function of an application. -/
  | appFn {f : Lean.Expr} (a : Lean.Expr) : OccursIn c f → OccursIn c (.app f a)
  /-- In the argument of an application. -/
  | appArg (f : Lean.Expr) {a : Lean.Expr} : OccursIn c a → OccursIn c (.app f a)
  /-- In the type of a binder. -/
  | lamType (n : Name) {d : Lean.Expr} (b : Lean.Expr) (bi : Lean.BinderInfo) :
      OccursIn c d → OccursIn c (.lam n d b bi)
  /-- In the body of a binder. -/
  | lamBody (n : Name) (d : Lean.Expr) {b : Lean.Expr} (bi : Lean.BinderInfo) :
      OccursIn c b → OccursIn c (.lam n d b bi)
  /-- In the type of a binder. -/
  | forallType (n : Name) {d : Lean.Expr} (b : Lean.Expr) (bi : Lean.BinderInfo) :
      OccursIn c d → OccursIn c (.forallE n d b bi)
  /-- In the body of a binder. -/
  | forallBody (n : Name) (d : Lean.Expr) {b : Lean.Expr} (bi : Lean.BinderInfo) :
      OccursIn c b → OccursIn c (.forallE n d b bi)
  /-- In the type of a `let`. -/
  | letType (n : Name) {t : Lean.Expr} (v b : Lean.Expr) (nd : Bool) :
      OccursIn c t → OccursIn c (.letE n t v b nd)
  /-- In the value of a `let`. -/
  | letValue (n : Name) (t : Lean.Expr) {v : Lean.Expr} (b : Lean.Expr) (nd : Bool) :
      OccursIn c v → OccursIn c (.letE n t v b nd)
  /-- In the body of a `let`. -/
  | letBody (n : Name) (t v : Lean.Expr) {b : Lean.Expr} (nd : Bool) :
      OccursIn c b → OccursIn c (.letE n t v b nd)
  /-- Below metadata. -/
  | mdata (m : Lean.MData) {b : Lean.Expr} : OccursIn c b → OccursIn c (.mdata m b)

/-- The fact about Lean that a floor over occurrences rests on: `Expr.getUsedConstants` lists each
constant that occurs in an expression. -/
def UsedConstantsComplete : Prop := ∀ c e, OccursIn c e → c ∈ e.getUsedConstants

/-- A constant occurs in the fields of a `ConstantInfo` that `Mentions` reads. -/
def InfoOccurs : ConstantInfo → Name → Prop
  | .axiomInfo v, u => OccursIn u v.type
  | .defnInfo v, u => OccursIn u v.type ∨ OccursIn u v.value
  | .thmInfo v, u => OccursIn u v.type ∨ OccursIn u v.value
  | .opaqueInfo v, u => OccursIn u v.type ∨ OccursIn u v.value
  | .quotInfo _, _ => False
  | .ctorInfo v, u => OccursIn u v.type
  | .recInfo v, u => OccursIn u v.type
  | .inductInfo v, u => OccursIn u v.type ∨ u ∈ v.ctors

/-- A constant occurs in the value of a `ConstantInfo`. -/
def ValueOccurs : ConstantInfo → Name → Prop
  | .defnInfo v, u => OccursIn u v.value
  | .thmInfo v, u => OccursIn u v.value
  | .opaqueInfo v, u => OccursIn u v.value
  | .axiomInfo _, _ | .quotInfo _, _ | .inductInfo _, _ | .ctorInfo _, _ | .recInfo _, _ => False

/-- `c` reaches `e` through the constants that occur in what the names of the environment state. -/
inductive OccursReaches (f : Regula.Load.Facts) : Name → Name → Prop
  /-- A constant reaches itself. -/
  | refl (c : Name) : OccursReaches f c c
  /-- A constant reaches what a constant that occurs in it reaches. -/
  | step {c u e : Name} (k : ConstantInfo) : f.env.constants.map₁[c]? = some k →
      (InfoOccurs k u ∨ ∃ v ∈ f.stated.getD c [], InfoOccurs v u) → OccursReaches f u e →
      OccursReaches f c e

/-- Under the fact about Lean, an occurrence is a mention. -/
theorem mentions_of_occurs (hused : UsedConstantsComplete) {k : ConstantInfo} {u : Name}
    (h : InfoOccurs k u) : Mentions k u := by
  cases k with
  | axiomInfo v => exact hused _ _ h
  | defnInfo v => exact h.imp (hused _ _) (hused _ _)
  | thmInfo v => exact h.imp (hused _ _) (hused _ _)
  | opaqueInfo v => exact h.imp (hused _ _) (hused _ _)
  | quotInfo v => exact h
  | ctorInfo v => exact hused _ _ h
  | recInfo v => exact hused _ _ h
  | inductInfo v => exact h.imp_left (hused _ _)

/-- Under the fact about Lean, an occurrence in a value is a mention in it. -/
theorem valueMentions_of_occurs (hused : UsedConstantsComplete) {k : ConstantInfo} {u : Name}
    (h : ValueOccurs k u) : ValueMentions k u := by
  cases k with
  | defnInfo v | thmInfo v | opaqueInfo v => exact hused _ _ h
  | axiomInfo v | quotInfo v | ctorInfo v | recInfo v | inductInfo v => exact h

/-- Under the fact about Lean, a walk over occurrences is a walk over mentions. -/
theorem envReaches_of_occurs (hused : UsedConstantsComplete) {c e : Name}
    (h : OccursReaches f c e) : EnvReaches f c e := by
  induction h with
  | refl => exact .refl _
  | step k hk ho _ ih =>
    exact .step ⟨k, hk, ho.imp (mentions_of_occurs hused)
      fun ⟨v, hv, hu⟩ => ⟨v, hv, mentions_of_occurs hused hu⟩⟩ ih

/-- The floor of RG1005 and of RG1006's loop constructs, over what occurs in the constants of a
claimed module, with the fact about Lean as the hypothesis: on a pass, its value holds no loop
construct, and each axiom that it reaches by occurrences is one that the profile admits. -/
theorem pass_occurs (hused : UsedConstantsComplete)
    (h : (Regula.Closed.decision (f.input roots p)).verdict = .pass) {n m : Name}
    {info : ConstantInfo} (hn : f.env.constants.map₁[n]? = some info)
    (hm : f.moduleOf? n = some m) (hc : m ∈ f.claimed) :
    (∀ l ∈ loopConstructs, ¬ ValueOccurs info l) ∧
      ∀ a, OccursReaches f n a → EnvAxiom f a → EnvAdmits f p a := by
  obtain ⟨-, h6, h7, h8⟩ := (pass_floor h).2.2.2.2 n info m hn hm hc
  exact ⟨fun l hl ho => h7 l hl (valueMentions_of_occurs hused ho),
    fun a hr hax => h8 a (envReaches_of_occurs hused hr) hax⟩

/-- Each constant of each claimed module is one that `Facts.claimedConstants` lists, and so one that
`pass_held` reaches, when the header holds data for each of its modules. Lean builds `moduleData`
and `modules` from one array (`Lean/Environment.lean:2313-2317` and `2367-2370`), so this is the
fact about Lean, as the hypothesis `hsize`. -/
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
