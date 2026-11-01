/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Foundation

/-!
# RG1006: `unsafe`, `partial` and loop declarations

RG1006 refuses three things in a claimed module: a constant that is unsafe or partial, a constant
that has the name of a recursion helper, and a constant whose value mentions a loop construct of
Lean. A `while` needs no `partial` of the module that uses it: it compiles through a private
`partial` of Lean's library (`Init/While.lean`), so the flags alone do not show it. A constant with
a helper's name needs no flag either: the compiler reads `f._unsafe_rec` in place of `f` by its name
alone (`getDeclInfo?`, `Lean/Compiler/LCNF/ToDecl.lean:25-27`).

The one constant of these the rule admits has **the exempted form**: `f._unsafe_rec`, partial and not
unsafe, with neither `@[implemented_by]` nor `@[extern]`, beside a safe, total definition `f` of its module.
It is the form of what Lean's elaborator adds for a safe recursive definition, which is why it is
exempted, and it is a form and nothing else. The input holds nothing of who produced a constant, so one
of this form that a module's own code adds during the build is admitted too, and no rule reads what it
computes. `helperForm_unreached` states why it cannot change what the proof verdict claims, under H6.
-/

namespace RegulaSpecification

open Lean (Name)

/-- The constants through which Lean's `while`, `repeat` and `repeat ... until` run: the one value
of the type `Lean.Loop` that they iterate over, and the loop itself (`Init/While.lean` at v4.35.0).
-/
def loopConstructs : List Name := [``Lean.Loop.mk, ``repeatM]

namespace Input

variable (i : Input)

/-- `d` has the exempted form, which names no origin: a partial, safe-flagged definition named `f._unsafe_rec` beside a safe, total definition `f`, neither with an
`@[implemented_by]` or `@[extern]`. The base of a `partial def` is an opaque constant, so its helper
has not this form. -/
def HelperForm (d : Decl) : Prop :=
  d.safety = .partial ∧ d.implementedBy = none ∧ d.isExtern = false ∧
    ∃ base ∈ i.decls, d.name = Name.str base.name "_unsafe_rec" ∧ base.kind = .definition ∧
      base.module = d.module ∧ base.safety = .safe ∧ base.implementedBy = none ∧
      base.isExtern = false

end Input

/-- The name of `d` is one that the compiler reads as a recursion helper: `b._unsafe_rec`, for some
name `b`. Nothing here depends on the constant's kind or flags. -/
def HelperNamed (d : Decl) : Prop := ∃ b : Name, d.name = Name.str b "_unsafe_rec"

/-- The value of `d` directly mentions a loop construct. -/
def MentionsLoop (d : Decl) : Prop := ∃ l ∈ loopConstructs, l ∈ d.valueUses

/-- RG1006: a claimed module holds a constant that is unsafe, partial or named as a recursion
helper, without the exempted form, or a constant whose value directly mentions a loop
construct. -/
def Violates1006 (i : Input) (c : Name) : Prop :=
  ∃ d ∈ i.decls, d.name = c ∧ i.ClaimedModule d.module ∧
    (((d.safety ≠ .safe ∨ HelperNamed d) ∧ ¬ i.HelperForm d) ∨ MentionsLoop d)

/-- H6, a hypothesis about Lean's kernel at v4.35.0, never an axiom: a safe constant mentions only safe constants. The kernel checks each
theorem, opaque constant, axiom and safe definition at the safety `safe` (`src/kernel/environment.cpp:156`, `:181`, `:196`, `:215`, with
`src/kernel/type_checker.h:127-128`), and refuses there a mention of an unsafe or a partial constant (`src/kernel/type_checker.cpp:110-117`).
`lake check` replays the build in that kernel, so it holds of the build that a proof verdict reads. -/
def SafeMentionsSafe (i : Input) : Prop :=
  ∀ d ∈ i.decls, d.safety = .safe → ∀ u ∈ d.uses, ∀ q ∈ i.decls, q.name = u → q.safety = .safe

/-- A name is that of one constant of the input. -/
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

/-- Under H6, each constant that a safe constant reaches through what it mentions is safe. -/
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

/-- Why a constant of the exempted form cannot change what the proof verdict claims, under H6: no safe constant reaches it. So no theorem
depends on it, and no proof's axioms come through it. It can change what a compiled program runs, which that verdict does not claim. -/
theorem helperForm_unreached {i : Input} (h : SafeMentionsSafe i) {d p : Decl} (hd : d ∈ i.decls) (hs : d.safety = .safe)
    (hp : p ∈ i.decls) (hf : i.HelperForm p) : ¬ i.Reaches d.name p.name := fun hr => by
  have := safe_reach_safe h hr d hd rfl hs p hp rfl
  rw [hf.1] at this
  cases this

/-- The intent record of RG1006. -/
def rg1006 := ruleRecord "RG1006" Violates1006

end RegulaSpecification
