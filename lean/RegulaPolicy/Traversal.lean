module

/-! Exact first-refusal and pointwise-map laws for pure `Except` list traversal; the success
law is `Guards.listForM_eq_ok`. They are shared by scope admission, census assembly,
worker-result admission and the qualification evaluator, and concern pure `Except` only,
not effects of any other monad. -/

public section

namespace RegulaPolicy

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

/-- Pure `Except` traversal succeeds exactly with pointwise successful results. -/
theorem mapM_eq_ok {α β ε : Type} (g : α → Except ε β) :
    ∀ (l : List α) (out : List β), l.mapM g = .ok out ↔
      out.length = l.length ∧ ∀ i (h : i < l.length) (h' : i < out.length), g l[i] = .ok out[i]
  | [], out => by cases out <;> simp [pure, Except.pure]
  | a :: l, out => by
    have ih := mapM_eq_ok g l
    rw [List.mapM_cons]
    cases ha : g a with
    | error e =>
      simp only [bind, Except.bind, reduceCtorEq, false_iff, not_and]
      intro hl hi
      have := hi 0 (by simp) (by simp [hl])
      simp [ha] at this
    | ok b =>
      cases hr : l.mapM g with
      | error e =>
        simp only [bind, Except.bind, reduceCtorEq, false_iff, not_and]
        intro hl hi
        cases out with
        | nil => simp at hl
        | cons c cs =>
          have := (ih cs).mpr ⟨by simpa using hl, fun i h h' => hi (i+1) (Nat.succ_lt_succ h) (Nat.succ_lt_succ h')⟩
          rw [hr] at this; cases this
      | ok bs =>
        have hbs := (ih bs).mp hr
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
        constructor
        · rintro rfl
          refine ⟨by simp [hbs.1], fun i h h' => ?_⟩
          cases i with
          | zero => simpa using ha
          | succ i => simpa using hbs.2 i (by simpa using h) (by simpa using h')
        · rintro ⟨hl, hi⟩
          cases out with
          | nil => simp at hl
          | cons c cs =>
            have h0 := hi 0 (by simp) (by simp)
            simp [ha] at h0
            have := (ih cs).mpr ⟨by simpa using hl, fun i h h' => hi (i+1) (Nat.succ_lt_succ h) (Nat.succ_lt_succ h')⟩
            rw [hr] at this
            cases this
            simp [h0]

end RegulaPolicy
