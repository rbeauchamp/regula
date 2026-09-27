import RegulaQualification.Checks
import Init.Data.List.Monadic

/-! # JSON template instantiation

Whole-field template instantiation. Structural correctness is proved for the raw
transformation, then required by its dependent-result adapter. The recursion returns
ordinary data; its proof is separate, avoiding unsupported dependent-result helper
attribution on the pinned compiler. Depth exhaustion explicitly refuses. -/
namespace RegulaQualification.Template
open Lean

/-- `Forall₂ R xs ys`: the lists have equal length and `R` relates their elements pairwise, in
order. This is the relation of Batteries' `List.Forall₂`, which Mathlib reuses; it is stated here
because the `regula` package imports only Lean's core libraries, so that requiring it adds no
dependency. -/
inductive Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  /-- Two empty lists are related. -/
  | nil : Forall₂ R [] []
  /-- Related heads extend related tails. -/
  | cons {a : α} {b : β} {xs : List α} {ys : List β} :
      R a b → Forall₂ R xs ys → Forall₂ R (a :: xs) (b :: ys)

/-- Ordered structure is preserved; only entire string leaves are transformed. -/
inductive Maps (f : String → String) : Json → Json → Prop where
  /-- `null` maps to itself. -/
  | null : Maps f .null .null
  /-- A Boolean maps to itself. -/
  | bool (b : Bool) : Maps f (.bool b) (.bool b)
  /-- A number maps to itself. -/
  | num (n : JsonNumber) : Maps f (.num n) (.num n)
  /-- A string leaf maps to `f` applied to the whole string. -/
  | str (s : String) : Maps f (.str s) (.str (f s))
  /-- An array maps to the array of related elements, in order and of the same length. -/
  | arr {xs : Array Json} {ys : List Json} (h : Forall₂ (Maps f) xs.toList ys) :
      Maps f (.arr xs) (.arr ys.toArray)
  /-- An object maps to the object with the same keys in order, each value related. -/
  | obj {xs : Std.TreeMap.Raw String Json} {ys : List (String × Json)}
      (keys : xs.toList.map Prod.fst = ys.map Prod.fst)
      (values : Forall₂ (Maps f) (xs.toList.map Prod.snd) (ys.map Prod.snd)) :
      Maps f (.obj xs) (Json.mkObj ys)

/-- Exact list relation for successful traversal through the standard monadic map. -/
theorem mapM_related {α β : Type} (R : α → β → Prop) (step : α → Except String β)
    (hs : ∀ a b, step a = .ok b → R a b) (xs : List α) (ys : List β)
    (h : xs.mapM step = .ok ys) : Forall₂ R xs ys := by
  induction xs generalizing ys with
  | nil =>
      change Except.ok [] = Except.ok ys at h
      have := Except.ok.inj h
      subst ys
      exact .nil
  | cons x xs ih =>
      rw [List.mapM_cons] at h
      change Except.bind (step x) (fun y => Except.map (List.cons y) (xs.mapM step)) = .ok ys at h
      cases hx : step x with
      | error e => simp [hx, Except.bind] at h
      | ok y =>
          cases ht : xs.mapM step with
          | error e => simp [hx, ht, Except.bind, Except.map] at h
          | ok tail =>
              have : ys = y :: tail := by simpa [hx, ht, Except.bind, Except.map] using h.symm
              subst ys
              exact .cons (hs x y hx) (ih tail ht)

/-- Separate ordered key preservation from the corresponding value relation. -/
theorem fields {R : Json → Json → Prop} {xs ys : List (String × Json)}
    (h : Forall₂ (fun a b => a.1 = b.1 ∧ R a.2 b.2) xs ys) :
    xs.map Prod.fst = ys.map Prod.fst ∧ Forall₂ R (xs.map Prod.snd) (ys.map Prod.snd) := by
  induction h with
  | nil => exact ⟨rfl, .nil⟩
  | cons h _ ih =>
      refine ⟨?_, .cons h.2 ih.2⟩
      simp only [List.map_cons, h.1, ih.1]

/-- Actual bounded transformation, using the standard map for ordered containers. -/
def transform (f : String → String) : Nat → Json → Except String Json
  | 0, _ => .error "template nesting exceeds supported depth"
  | n + 1, input => match input with
    | .null => .ok .null
    | .bool b => .ok (.bool b)
    | .num x => .ok (.num x)
    | .str s => .ok (.str (f s))
    | .arr xs => (xs.toList.mapM (transform f n)).map (fun ys => .arr ys.toArray)
    | .obj xs => (xs.toList.mapM (fun (entry : String × Json) =>
        (transform f n entry.2).map (fun value => (entry.1, value)))).map Json.mkObj

/-- Structural fidelity for every input and successful bounded transformation. -/
theorem transform_sound (f : String → String) (fuel : Nat) (input output : Json)
    (h : transform f fuel input = .ok output) : Maps f input output := by
  induction fuel generalizing input output with
  | zero => simp [transform] at h
  | succ n ih =>
      cases input with
      | null => simp only [transform, Except.ok.injEq] at h; subst output; exact .null
      | bool b => simp only [transform, Except.ok.injEq] at h; subst output; exact .bool b
      | num x => simp only [transform, Except.ok.injEq] at h; subst output; exact .num x
      | str s => simp only [transform, Except.ok.injEq] at h; subst output; exact .str s
      | arr xs =>
          simp only [transform] at h
          cases hm : xs.toList.mapM (transform f n) with
          | error e => simp [hm, Except.map] at h
          | ok ys =>
              have : output = .arr ys.toArray := by simpa [hm, Except.map] using h.symm
              subst output
              exact .arr (mapM_related (Maps f) (transform f n) ih _ _ hm)
      | obj xs =>
          simp only [transform] at h
          cases hm : xs.toList.mapM (fun (entry : String × Json) =>
            (transform f n entry.2).map (fun value => (entry.1, value))) with
          | error e => rw [hm] at h; contradiction
          | ok ys =>
              rw [hm] at h
              have : output = Json.mkObj ys := (Except.ok.inj h).symm
              subst output
              have related : Forall₂ (fun (a b : String × Json) => a.1 = b.1 ∧ Maps f a.2 b.2)
                  xs.toList ys := by
                apply mapM_related _ _ _ _ _ hm
                intro a b hb
                cases hv : transform f n a.2 with
                | error e => simp [hv, Except.map] at hb
                | ok value =>
                    have : b = (a.1, value) := by simpa [hv, Except.map] using hb.symm
                    subst b
                    exact ⟨rfl, ih _ _ hv⟩
              exact .obj (fields related).1 (fields related).2

/-- The IO adapter cannot consume a transformed value without the structural proof. -/
def instantiate (f : String → String) (fuel : Nat) (input : Json) :
    Except String {output // Maps f input output} :=
  match h : transform f fuel input with
  | .error e => .error e
  | .ok output => .ok ⟨output, transform_sound f fuel input output h⟩

/-- Exact success/refusal preservation by the evidence-requiring adapter, including
success whenever the actual transformer succeeds. -/
theorem instantiate_exact (f : String → String) (fuel : Nat) (input : Json) :
    (instantiate f fuel input).map Subtype.val = transform f fuel input := by
  unfold instantiate
  split <;> simp_all [Except.map]

/-- Lookup replaces only an entire matching value. -/
def replace (bindings : List (String × String)) (s : String) : String :=
  ((bindings.find? (fun p => p.1 == s)).map Prod.snd).getD s

/-- Unmatched text is unchanged, including a sentinel occurring as a substring. -/
theorem replace_unmatched (bindings : List (String × String)) (s : String)
    (h : bindings.find? (fun p => p.1 == s) = none) : replace bindings s = s := by
  simp [replace, h]
end RegulaQualification.Template
