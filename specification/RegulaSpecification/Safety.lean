import RegulaSpecification.Foundation

/-!
# RG1006: `unsafe`, `partial` and loop declarations

RG1006 refuses three things in a claimed module: a constant that is unsafe or partial, a constant that has
the name of a recursion helper, and a constant whose value mentions a loop construct of Lean. A `while`
needs no `partial` of the module that uses it: it compiles through a private `partial` of Lean's library
({lit}`Init/While.lean`), so the flags alone do not show it. A constant with a helper's name needs no flag
either: the compiler reads `f._unsafe_rec` in place of {lit}`f` by its name alone ({lit}`getDeclInfo?`,
{lit}`Lean/Compiler/LCNF/ToDecl.lean:25-27`).

The two constants of these the rule admits have an exempted form:
- `f._unsafe_rec`, partial and not unsafe, with neither {attr}`@[implemented_by]` nor
  {attr}`@[extern]`, beside a safe, total definition {lit}`f` of its module ({lit}`HelperForm`). It
  is the form of what Lean's elaborator adds for a safe recursive definition, and it is a form and
  nothing else: the input holds nothing of who produced it, so one added during the build is
  admitted too, and no rule reads what it computes.
- `T.ctorIdx._impl`, unsafe, with neither {attr}`@[implemented_by]` nor {attr}`@[extern]` and
  structural form {lit}`CtorIdxForm.impl T`, beside the safe definition `T.ctorIdx` (structural form
  {lit}`CtorIdxForm.defn T`, {attr}`@[implemented_by]` {lit}`T.ctorIdx._impl`, not {attr}`@[extern]`) and
  the safe inductive type {lit}`T` in the same module, with {lit}`getObjTagNat` in the toolchain
  ({lit}`CtorIdxImpl`). It is the exact structural form that Lean v4.36.0's {lit}`mkCtorIdx`
  generates ({lit}`Lean/Meta/Constructions/CtorIdx.lean:40-141`).

{lit}`helperForm_unreached` and {lit}`ctorIdxImpl_unreached` state why neither exempted form can
change what the proof verdict claims, under H6.
-/

namespace RegulaSpecification

open Lean (Name)

/-- The constants through which Lean's `while`, {lit}`repeat` and `repeat ... until` run: the one value
of the type {name}`Lean.Loop` that they iterate over, and the loop itself ({lit}`Init/While.lean` at v4.36.0).
-/
def loopConstructs : List Name := [``Lean.Loop.mk, ``repeatM]

namespace Input

variable (i : Input)

/-- {name}`d` has the exempted recursion-helper form, which names no origin: a partial, safe-flagged
definition named `f._unsafe_rec` beside a safe, total definition {lit}`f`, neither with an
{attr}`@[implemented_by]` or {attr}`@[extern]`. The base of a `partial def` is an opaque constant, so its helper
has not this form. -/
def HelperForm (d : Decl) : Prop :=
  d.safety = .partial ∧ d.implementedBy = none ∧ d.isExtern = false ∧
    ∃ base ∈ i.decls, d.name = Name.str base.name "_unsafe_rec" ∧ base.kind = .definition ∧
      base.module = d.module ∧ base.safety = .safe ∧ base.implementedBy = none ∧
      base.isExtern = false

/-- {name}`d` has the exempted form of the unsafe half `T.ctorIdx._impl` of a compiler-generated
{lit}`ctorIdx` pair ({lit}`Lean/Meta/Constructions/CtorIdx.lean:40-141` at v4.36.0): an unsafe
definition of form {lit}`CtorIdxForm.impl ind` with neither {attr}`@[implemented_by]` nor
{attr}`@[extern]`, beside the safe definition `ind.ctorIdx` (of form {lit}`CtorIdxForm.defn ind`
with {attr}`@[implemented_by]` {lit}`ind.ctorIdx._impl` and without {attr}`@[extern]`) and the safe
inductive type {lit}`ind` in the same module, with {lit}`getObjTagNat` in the toolchain. -/
def CtorIdxImpl (d : Decl) : Prop :=
  ∃ ind,
    (∃ tag ∈ i.decls, tag.name = `getObjTagNat ∧ tag.inToolchain = true) ∧
    (∃ indDecl ∈ i.decls, indDecl.name = ind ∧ indDecl.kind = .inductive ∧
      indDecl.safety = .safe ∧ indDecl.module = d.module) ∧
    d.name = Name.str (Name.str ind "ctorIdx") "_impl" ∧
    d.kind = .definition ∧ d.safety = .unsafe ∧ d.ctorIdxForm = .impl ind ∧
    d.implementedBy = none ∧ d.isExtern = false ∧
    ∃ defDecl ∈ i.decls,
      defDecl.name = Name.str ind "ctorIdx" ∧ defDecl.module = d.module ∧
      defDecl.kind = .definition ∧ defDecl.safety = .safe ∧
      defDecl.ctorIdxForm = .defn ind ∧
      defDecl.implementedBy = some (Name.str (Name.str ind "ctorIdx") "_impl") ∧
      defDecl.isExtern = false

end Input

/-- The name of {name}`d` is one that the compiler reads as a recursion helper: `b._unsafe_rec`, for some
name {lit}`b`. Nothing here depends on the constant's kind or flags. -/
def HelperNamed (d : Decl) : Prop := ∃ b : Name, d.name = Name.str b "_unsafe_rec"

/-- The value of {name}`d` directly mentions a loop construct. -/
def MentionsLoop (d : Decl) : Prop := ∃ l ∈ loopConstructs, l ∈ d.valueUses

/-- RG1006: a claimed module holds a constant that is unsafe, partial or named as a recursion
helper, without an exempted form, or a constant whose value directly mentions a loop construct. -/
def Violates1006 (i : Input) (c : Name) : Prop :=
  ∃ d ∈ i.decls, d.name = c ∧ i.ClaimedModule d.module ∧
    (((d.safety ≠ .safe ∨ HelperNamed d) ∧ ¬ i.HelperForm d ∧ ¬ i.CtorIdxImpl d) ∨ MentionsLoop d)

/-- H6, a hypothesis about Lean's kernel at v4.36.0, never an axiom: a safe constant mentions only safe constants. The kernel checks each
theorem, opaque constant, axiom and safe definition at the safety {lit}`safe` ({lit}`src/kernel/environment.cpp:155`, `:180`, `:195`, `:214`, with
{lit}`src/kernel/type_checker.h:124-125`), and refuses there a mention of an unsafe or a partial constant ({lit}`src/kernel/type_checker.cpp:110-117`).
The checker replays the cone of the claim in that kernel, so it holds of each constant of the cone, which holds each constant that a
claimed constant reaches. -/
def SafeMentionsSafe (i : Input) : Prop :=
  ∀ d ∈ i.decls, d.safety = .safe → ∀ u ∈ d.uses, ∀ q ∈ i.decls, q.name = u → q.safety = .safe

theorem Input.eq_of_name_eq {l : List Decl} (h : (l.map (·.name)).Nodup) {a b : Decl} (ha : a ∈ l) (hb : b ∈ l)
    (he : a.name = b.name) : a = b := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := List.nodup_cons.mp h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd (List.mem_map.mpr ⟨b, hb', he.symm⟩) h1
    · exact absurd (List.mem_map.mpr ⟨a, ha', he⟩) h1
    · exact ih h2 ha' hb'

theorem safe_reach_safe {i : Input} (h : SafeMentionsSafe i) {c e : Name} (hr : i.Reaches c e) :
    ∀ d ∈ i.decls, d.name = c → d.safety = .safe → ∀ p ∈ i.decls, p.name = e → p.safety = .safe := by
  induction hr with
  | refl c =>
    intro d hd hc hs p hp he
    have hsame : p = d := Input.eq_of_name_eq i.unique hp hd (he.trans hc.symm)
    rw [hsame]
    exact hs
  | @step c u e d₀ hd₀ hc₀ hu hrest ih =>
    intro d hd hc hs p hp he
    have hsame : d₀ = d := Input.eq_of_name_eq i.unique hd₀ hd (hc₀.trans hc.symm)
    subst hsame
    by_cases hq : ∃ q ∈ i.decls, q.name = u
    · obtain ⟨q, hqm, hqn⟩ := hq
      exact ih q hqm hqn (h d₀ hd₀ hs u hu q hqm hqn) p hp he
    · cases hrest with
      | refl => exact absurd ⟨p, hp, he⟩ hq
      | step x hx hxn _ _ => exact absurd ⟨x, hx, hxn⟩ hq

/-- Why a constant of the exempted recursion-helper form cannot change what the proof verdict claims, under H6: no safe constant reaches it. So no theorem
depends on it, and no proof's axioms come through it. It can change what a compiled program runs, which that verdict does not claim. -/
theorem helperForm_unreached {i : Input} (h : SafeMentionsSafe i) {d p : Decl} (hd : d ∈ i.decls) (hs : d.safety = .safe)
    (hp : p ∈ i.decls) (hf : i.HelperForm p) : ¬ i.Reaches d.name p.name := fun hr => by
  have := safe_reach_safe h hr d hd rfl hs p hp rfl
  rw [hf.1] at this
  cases this

/-- Why the unsafe half `T.ctorIdx._impl` of a compiler-generated {lit}`ctorIdx` pair cannot change
what the proof verdict claims, under H6: no safe constant reaches it. -/
theorem ctorIdxImpl_unreached {i : Input} (h : SafeMentionsSafe i) {d p : Decl} (hd : d ∈ i.decls)
    (hs : d.safety = .safe) (hp : p ∈ i.decls) (hc : i.CtorIdxImpl p) : ¬ i.Reaches d.name p.name := fun hr => by
  have := safe_reach_safe h hr d hd rfl hs p hp rfl
  obtain ⟨_, _, _, _, _, hu, -⟩ := hc
  rw [hu] at this
  cases this

/-- The intent record of RG1006. -/
def rg1006 := ruleRecord "RG1006" Violates1006

end RegulaSpecification
