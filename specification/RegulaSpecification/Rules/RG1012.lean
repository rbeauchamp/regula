import RegulaSpecification.Rule
import Regula.Rules.RG1012

/-!
# RG1012: hidden panics

A definition or opaque constant of a claimed module whose value mentions a panic form. Lean's total functions
can still panic, and a panic gives the type's default value, in Lean's logic ({name}`panicCore` is
{name}`default`, {lit}`Init/Prelude.lean:3849` at v4.35.0) and in the compiled program, which prints the
message and goes on with that value unless the variable {lit}`LEAN_ABORT_ON_PANIC` is set or the program asked
to exit on a panic ({lit}`lean_panic_impl`, {lit}`src/runtime/object.cpp:176-207` at v4.35.0). So a proved
function can go on with a value that its proofs never considered.

A panic form is one of Lean's four panic functions, or a constant that is no theorem and whose name's last
string component, with its macro scopes erased, contains {lit}`!`: Lean names so an operation that panics when it
fails, and each listed form elaborates to a mention of one ({lit}`xs[i]!` to {name}`GetElem?.getElem!`,
{lit}`panic!`, {lit}`unreachable!` and {lit}`assert!` to {name}`panicWithPosWithDecl`). The rule reads only
what a value mentions directly: a build fails under the closure of the mentions within the claim exactly
when it fails under the direct mentions, because the last claimed constant on any path to a panic form
mentions that form itself. A theorem is no subject, and a theorem's name is no panic form, because a proof
is never run. {name (full := Regula.Rules.RG1012.check)}`Regula.Rules.RG1012.check` is the function that the
checker runs.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

/-- Lean's four panic functions. -/
def panicFunctions : List Name := [``panicCore, ``panic, ``panicWithPos, ``panicWithPosWithDecl]

/-- The name {name}`u`, with its macro scopes erased, is a string component {lit}`s` that contains {lit}`!`,
followed by nothing but numeric components. -/
def BangNamed (u : Name) : Prop :=
  ∃ p s, ∃ ks : List Nat, u.eraseMacroScopes = ks.foldl Name.num (Name.str p s) ∧ '!' ∈ s.toList

namespace Input

variable (i : Input)

/-- {name}`u` is a panic form of the input: one of Lean's four panic functions, or a name that
{name}`BangNamed` admits and that the input does not hold as a theorem. -/
def PanicForm (u : Name) : Prop :=
  u ∈ panicFunctions ∨ (BangNamed u ∧ ¬ ∃ e ∈ i.decls, e.name = u ∧ e.kind = .theorem)

end Input

/-- RG1012: a definition or opaque constant of a claimed module whose value mentions a panic form. -/
def Violates1012 (i : Input) (c : Name) : Prop :=
  ∃ d ∈ i.decls, d.name = c ∧ i.ClaimedModule d.module ∧ (d.kind = .definition ∨ d.kind = .opaque) ∧
    ∃ u ∈ d.valueUses, i.PanicForm u

/-- The intent record of RG1012. -/
def rg1012 := ruleRecord "RG1012" Violates1012

namespace Witnesses

theorem bangNamed_get : BangNamed ``Option.get! := ⟨`Option, "get!", [], rfl, by decide⟩

/-- A name with macro scopes, as hygiene makes one of {name}`Option.get!`. -/
def hygienicGet : Name := .num (.str (.str (.str ``Option.get! "_@") "M") "_hyg") 3

theorem bangNamed_hygienic : BangNamed hygienicGet := ⟨`Option, "get!", [], rfl, by decide⟩

theorem foldl_num_eq_str {ks : List Nat} {x p : Name} {s : String}
    (h : ks.foldl Name.num x = .str p s) : ks = [] ∧ x = .str p s := by
  induction ks generalizing x with
  | nil => exact ⟨rfl, h⟩
  | cons k ks ih =>
    rw [List.foldl_cons] at h
    exact absurd (ih h).2 (by simp)

/-- {name}`GetElem?.getElem?`, to which {lit}`xs[i]?` elaborates, is named with no {lit}`!`. -/
theorem not_bangNamed_query : ¬ BangNamed ``GetElem?.getElem? := by
  rintro ⟨p, s, ks, he, hc⟩
  have hq : (``GetElem?.getElem?).eraseMacroScopes = Name.str `GetElem? "getElem?" := rfl
  rw [hq] at he
  obtain ⟨-, hx⟩ := foldl_num_eq_str he.symm
  simp only [Name.str.injEq] at hx
  rw [hx.2] at hc
  exact absurd hc (by decide)

/-- {name}`Option.get!`, a definition of the toolchain. -/
def getBang : Decl := toolchain ``Option.get! .definition

/-- A definition of a claimed module whose value mentions {name}`Option.get!`. -/
def bangUser : Decl := { plain `Good.g `Good .definition [``Option.get!] with valueUses := [``Option.get!] }

/-- The cases of RG1012. -/
def w1012 : Witnessed Violates1012 where
  support i := i.decls.map (·.name)
  support_complete _ _ h := by
    obtain ⟨d, hd, hn, -⟩ := h
    exact name_mem (P := fun _ => True) ⟨d, hd, hn, trivial⟩
  refused := withDecls [getBang, bangUser]
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, getBang, bangUser])
  refused_wf := wf_withDecls _ _
    (uses_resolve (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, getBang, bangUser]))
  bad := `Good.g
  bad_violates := by
    refine ⟨bangUser, by simp [withDecls], rfl, claimed_withDecls, .inl rfl, ``Option.get!,
      by simp [bangUser], .inr ⟨bangNamed_get, ?_⟩⟩
    rintro ⟨e, he, hn, hk⟩
    rw [eq_of_name (d' := getBang) he (by simp [withDecls]) (by simp [hn, getBang, toolchain, plain])] at hk
    simp [getBang, toolchain, plain] at hk
  admitted := base
  admitted_wf := wf_base
  fine := `Good.t
  fine_admitted := by
    rintro ⟨d, hd, hn, -, hk, -⟩
    rw [t_of_name hd hn] at hk
    simp [tDecl, plain] at hk

theorem rg1012_adequate : O2 rg1012 ∧ O2Run rg1012 ∧ O3 rg1012 ∧ O4 rg1012 ∧
    O5 rg1012 (.rel SameReports) := adequate w1012

theorem rg1012_noisy : ¬ rg1012.Meets w1012.candidates := noisy_fails w1012 t_mem_support

/-- A definition of a claimed module whose value mentions {name}`panicWithPosWithDecl`, as {lit}`panic!` gives. -/
def panicUser : Decl :=
  { plain `Good.p `Good .definition [``panicWithPosWithDecl] with valueUses := [``panicWithPosWithDecl] }

/-- {name}`base`, with {name}`panicUser` and the panic function that it mentions. -/
def withPanic : Input := withDecls [toolchain ``panicWithPosWithDecl .definition, panicUser]
  (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, panicUser])

theorem wf_withPanic : withPanic.WellFormed :=
  wf_withDecls _ _
    (uses_resolve (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, panicUser]))

theorem rg1012_refuses_panic : Violates1012 withPanic `Good.p :=
  ⟨panicUser, by simp [withPanic, withDecls], rfl, claimed_withDecls, .inl rfl, ``panicWithPosWithDecl,
    by simp [panicUser], .inl (by simp [panicFunctions])⟩

/-- A theorem of the toolchain whose name contains {lit}`!`. -/
def bangLemma : Decl := toolchain `Std.get!_lemma .theorem

/-- A definition of a claimed module whose value mentions {name}`bangLemma`, as a proof inside a value can. -/
def lemmaUser : Decl :=
  { plain `Good.u `Good .definition [`Std.get!_lemma] with valueUses := [`Std.get!_lemma] }

/-- A theorem of a claimed module whose proof mentions {name}`Option.get!`. -/
def bangProof : Decl :=
  { plain `Good.q `Good .theorem [``Option.get!] with valueUses := [``Option.get!] }

/-- {name}`base`, with {name}`lemmaUser`, {name}`bangProof` and what they mention. -/
def withLemma : Input := withDecls [bangLemma, lemmaUser, getBang, bangProof]
  (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, bangLemma, lemmaUser, getBang, bangProof])

/-- A theorem whose name contains {lit}`!` is no panic form, and a theorem is no subject, even when its proof
mentions one. So a rule that refuses every mention of a name with {lit}`!`, or every claimed constant whose value
mentions a panic form, does not meet this. -/
theorem rg1012_admits_theorems : ¬ Violates1012 withLemma `Good.u ∧ ¬ Violates1012 withLemma `Good.q := by
  have hmem : ∀ d ∈ [bangLemma, lemmaUser, getBang, bangProof], d ∈ withLemma.decls := by
    intro d hd
    exact List.mem_append_right _ hd
  refine ⟨?_, ?_⟩
  · rintro ⟨d, hd, hn, -, -, u, hu, hp⟩
    rw [eq_of_name hd (hmem lemmaUser (by simp)) (by simp [hn, lemmaUser, plain])] at hu
    simp only [lemmaUser, plain, List.mem_singleton] at hu
    subst hu
    rcases hp with hp | ⟨-, hno⟩
    · simp [panicFunctions] at hp
    · exact hno ⟨bangLemma, hmem bangLemma (by simp), rfl, rfl⟩
  · rintro ⟨d, hd, hn, -, hk, -⟩
    rw [eq_of_name hd (hmem bangProof (by simp)) (by simp [hn, bangProof, plain])] at hk
    simp [bangProof, plain] at hk

end Witnesses

namespace Link

variable {i : Regula.Closed.Input} (t : Regula.Closed.Tables i)

theorem lastString?_foldl (ks : List Nat) (x : Name) :
    Regula.Rules.RG1012.lastString? (ks.foldl Name.num x) = Regula.Rules.RG1012.lastString? x := by
  induction ks generalizing x with
  | nil => rfl
  | cons k ks ih =>
    rw [List.foldl_cons, ih]
    rfl

theorem lastString?_eq_some (n : Name) (s : String) :
    Regula.Rules.RG1012.lastString? n = some s ↔ ∃ p, ∃ ks : List Nat, n = ks.foldl Name.num (Name.str p s) := by
  constructor
  · intro h
    induction n with
    | anonymous => cases h
    | str p t =>
      simp only [Regula.Rules.RG1012.lastString?, Option.some.injEq] at h
      subst h
      exact ⟨p, [], rfl⟩
    | num q k ih =>
      obtain ⟨p, ks, rfl⟩ := ih (by simpa [Regula.Rules.RG1012.lastString?] using h)
      exact ⟨p, ks ++ [k], by simp [List.foldl_append]⟩
  · rintro ⟨p, ks, rfl⟩
    rw [lastString?_foldl]
    rfl

theorem bangNamed_iff (u : Name) : Regula.Rules.RG1012.bangNamed u = true ↔ BangNamed u := by
  unfold Regula.Rules.RG1012.bangNamed BangNamed
  rw [Option.any_eq_true]
  constructor
  · rintro ⟨s, hs, hc⟩
    obtain ⟨p, ks, he⟩ := (lastString?_eq_some _ _).mp hs
    exact ⟨p, s, ks, he, by simpa [String.contains_char_eq] using hc⟩
  · rintro ⟨p, s, ks, he, hc⟩
    exact ⟨s, (lastString?_eq_some _ _).mpr ⟨p, ks, he⟩, by simpa [String.contains_char_eq] using hc⟩

theorem kindTheorem_iff (b : Regula.Closed.Decl) :
    (b.kind == .theorem) = true ↔ (decl b).kind = .theorem := by
  cases hd : b.kind <;> simp [decl, constKind, hd]

theorem panicForm_iff (u : Name) :
    Regula.Rules.RG1012.panicForm t u = true ↔ (toSpec i).PanicForm u := by
  have hl : Regula.Rules.RG1012.panicFunctions.contains u = true ↔ u ∈ panicFunctions := by
    simp [Regula.Rules.RG1012.panicFunctions, panicFunctions]
  have hthm : (t.index[u]?.any (·.kind == .theorem)) = true ↔
      ∃ e ∈ (toSpec i).decls, e.name = u ∧ e.kind = .theorem := by
    rw [any_index_iff t]
    constructor
    · rintro ⟨d, hd, rfl, hk⟩
      exact ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, (kindTheorem_iff d).mp hk⟩
    · rintro ⟨x, hx, rfl, hk⟩
      obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
      exact ⟨d, hd, rfl, (kindTheorem_iff d).mpr hk⟩
  unfold Regula.Rules.RG1012.panicForm Input.PanicForm
  rw [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', hl, bangNamed_iff, ← hthm]
  simp

theorem hasRunValue_iff (d : Regula.Closed.Decl) :
    Regula.Rules.RG1012.hasRunValue d = true ↔
      (decl d).kind = .definition ∨ (decl d).kind = .opaque := by
  cases hd : d.kind <;> simp [Regula.Rules.RG1012.hasRunValue, decl, constKind, hd]

theorem rg1012_exact (s : Name) :
    s ∈ (Regula.Rules.RG1012.check t).map (·.subject) ↔ Violates1012 (toSpec i) s := by
  have hc : ∀ d : Regula.Closed.Decl,
      (Regula.Rules.RG1012.hasRunValue d && d.valueUses.any (Regula.Rules.RG1012.panicForm t)) = true ↔
        ((decl d).kind = .definition ∨ (decl d).kind = .opaque) ∧
          ∃ u ∈ (decl d).valueUses, (toSpec i).PanicForm u := by
    intro d
    rw [Bool.and_eq_true, hasRunValue_iff, List.any_eq_true]
    exact and_congr_right fun _ => exists_congr fun u => and_congr_right fun _ => panicForm_iff t u
  unfold Regula.Rules.RG1012.check
  rw [mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro ⟨d, hd, hcd, rfl⟩
    obtain ⟨hd, hm⟩ := (mem_claimed t).mp hd
    obtain ⟨hk, hu⟩ := (hc d).mp hcd
    exact ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm, hk, hu⟩
  · rintro ⟨x, hx, rfl, hm, hk, hu⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    exact ⟨d, (mem_claimed t).mpr ⟨hd, hm⟩, (hc d).mpr ⟨hk, hu⟩, rfl⟩

end Link

/-- RG1012 with its statement, its proof and its cases, for the registry. -/
def rg1012Proved : Proved := ⟨Regula.Rules.RG1012.rule, Violates1012, Link.rg1012_exact, Witnesses.w1012⟩

/-- The function of RG1012 over the specification's input. -/
def rg1012Checker : Checker Input Name := rg1012Proved.checker

theorem rg1012_meets : rg1012.Meets rg1012Checker := rg1012Proved.meets "RG1012"

theorem rg1012_cases :
    Witnesses.w1012.bad ∈ rg1012Checker ⟨Witnesses.w1012.refused, Witnesses.w1012.refused_wf⟩ ∧
      Witnesses.w1012.fine ∉
        rg1012Checker ⟨Witnesses.w1012.admitted, Witnesses.w1012.admitted_wf⟩ :=
  rg1012Proved.cases_hold

theorem rg1012_checker_refuses_panic :
    `Good.p ∈ rg1012Checker ⟨Witnesses.withPanic, Witnesses.wf_withPanic⟩ :=
  ((meets_iff _).mp rg1012_meets _ _).mpr Witnesses.rg1012_refuses_panic

end RegulaSpecification
