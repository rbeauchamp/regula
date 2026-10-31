module

/-! # Lemmas about `Except` validators and list traversal

Facts for proving what a successful `Except` validator establishes, about the executed guard
sequences themselves. `Regula.Checker.Manifest` and the qualification evaluator
(`RegulaQualification.Checks`) use them. They concern pure `Except` values only. The last lemma,
`perm_of_length_of_mem`, is about lists of names; `Regula.Checker.PolicyCodec.exactFields_iff` and
`Regula.JsonAgreement` use it. -/

public section

namespace RegulaPolicy.Guards

universe u v w

section Except

variable {ε : Type u} {α β : Type v}

/-- A sequenced computation succeeds exactly when each step succeeds in turn. -/
@[simp] theorem bind_eq_ok {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

/-- A thrown error is never success. -/
@[simp] theorem throw_ne_ok {e : ε} {a : α} : (throw e : Except ε α) ≠ .ok a := by
  simp [throw, throwThe, MonadExceptOf.throw]

/-- `pure` succeeds with exactly its value. -/
@[simp] theorem pure_eq_ok {a b : α} : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

/-- A list traversal succeeds exactly when the step succeeds on every element. -/
theorem listForM_eq_ok {xs : List α} {g : α → Except ε PUnit} {u : PUnit} :
    xs.forM g = .ok u ↔ ∀ x ∈ xs, g x = .ok ⟨⟩ := by
  induction xs with
  | nil => simp [List.forM, pure, Except.pure]
  | cons x xs ih =>
    change (g x >>= fun _ => xs.forM g) = _ ↔ _
    rw [bind_eq_ok]
    simp only [ih, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨⟩, hx, hs⟩; exact ⟨hx, hs⟩
    · rintro ⟨hx, hs⟩; exact ⟨_, hx, hs⟩

end Except

/-- Pure `Except` traversal refuses with `e` exactly when some element refuses with `e`
after a prefix whose elements all succeed; the suffix is not evaluated. -/
theorem forM_eq_error {α ε : Type} (f : α → Except ε Unit) (l : List α) (e : ε) :
    l.forM f = .error e ↔ ∃ before x after, l = before ++ x :: after ∧
      (∀ b ∈ before, f b = .ok ()) ∧ f x = .error e := by
  induction l with
  | nil =>
    refine ⟨fun h => (by cases h), ?_⟩
    rintro ⟨before, x, after, h, -⟩
    cases before <;> cases h
  | cons y l ih =>
    rw [show (y :: l).forM f = (f y >>= fun _ => l.forM f) from rfl]
    simp only [List.cons_eq_append_iff]
    cases hy : f y with
    | error e' =>
      simp only [bind, Except.bind, Except.error.injEq]
      constructor
      · rintro rfl; exact ⟨[], y, l, Or.inl ⟨rfl, rfl⟩, nofun, hy⟩
      · rintro ⟨before, x, after, ⟨rfl, h⟩ | ⟨tail, rfl, _⟩, hb, hx⟩
        · simp only [List.cons.injEq] at h
          rw [h.1, hy] at hx
          exact Except.error.inj hx
        · have := hb y List.mem_cons_self
          rw [hy] at this; cases this
    | ok u =>
      cases u
      simp only [bind, Except.bind, ih]
      constructor
      · rintro ⟨before, x, after, rfl, hb, hx⟩
        refine ⟨y :: before, x, after, Or.inr ⟨before, rfl, rfl⟩, fun b hb' => ?_, hx⟩
        rcases List.mem_cons.mp hb' with rfl | hb'
        · exact hy
        · exact hb b hb'
      · rintro ⟨before, x, after, ⟨rfl, h⟩ | ⟨tail, rfl, rfl⟩, hb, hx⟩
        · simp only [List.cons.injEq] at h
          rw [h.1, hy] at hx; cases hx
        · exact ⟨tail, x, after, rfl, fun b hb' => hb b (List.mem_cons_of_mem y hb'), hx⟩

/-- A list with the length of a list of distinct names, and with each of those names, is those
names in some order. `Regula.Checker.PolicyCodec.exactFields_iff` and `Regula.JsonAgreement`
use it. -/
theorem perm_of_length_of_mem {expected : List String} (distinct : expected.Nodup) :
    ∀ {actual : List String}, actual.length = expected.length →
      (∀ name ∈ expected, name ∈ actual) → actual.Perm expected := by
  induction expected with
  | nil =>
    intro actual length _
    rw [List.length_nil, List.length_eq_zero_iff] at length
    rw [length]
  | cons name rest step =>
    intro actual length members
    obtain ⟨absent, distinct⟩ := List.nodup_cons.mp distinct
    have present : name ∈ actual := members name List.mem_cons_self
    have shorter : (actual.erase name).length = rest.length := by
      rw [List.length_erase_of_mem present, length, List.length_cons, Nat.add_sub_cancel]
    have others : ∀ other ∈ rest, other ∈ actual.erase name := fun other member =>
      (List.mem_erase_of_ne fun (same : other = name) => absent (same ▸ member)).mpr
        (members other (List.mem_cons_of_mem _ member))
    exact (List.perm_cons_erase present).trans ((step distinct shorter others).cons name)

end RegulaPolicy.Guards
