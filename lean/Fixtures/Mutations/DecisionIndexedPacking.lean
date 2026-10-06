/-
Mutation of `Fixtures.Positive.DependentDecisionKinds`, at the toolchain boundary, for the second
review's second finding: the kind is stated about the implementation applied to the only field
of a type with one constructor and an index. The index restricts the type: `Limited true` holds
only the numbers up to three, so the kind says nothing of `check 4`, which accepts a number the
specification excludes. Lean's `structure` command makes no projection for such a type, but
Lean's kernel admits a primitive projection on it, which a metaprogram adds here. Lean accepts
the proof; the checker must refuse the registration under RG1007 and name the function the kind
decides.
-/
import Lean
import Regula.Contract

open Lean Elab Command

/-- A number with an index that says whether it is at most three. -/
inductive Limited : Bool → Type where
  | mk (n : Nat) : Limited (decide (n ≤ 3))

def check (n : Nat) : Bool := decide (n ≠ 3)

-- `Limited.field : (b : Bool) → Limited b → Nat := fun b self => self.1`, a constant whose
-- kernel value is the primitive projection of the constructor's field.
run_cmd do
  let limited := mkApp (mkConst ``Limited) (.bvar 0)
  let value := Expr.lam `b (mkConst ``Bool)
    (Expr.lam `self limited (Expr.proj ``Limited 0 (.bvar 0)) .default) .default
  let type := Expr.forallE `b (mkConst ``Bool)
    (Expr.forallE `self limited (mkConst ``Nat) .default) .default
  liftCoreM <| addDecl <| Declaration.defnDecl
    { name := `Limited.field, levelParams := [], type, value, hints := .abbrev, safety := .safe }

theorem Limited.field_mk (n : Nat) : Limited.field _ (Limited.mk n) = n := rfl

theorem Limited.field_le : ∀ {b : Bool} (x : Limited b), b = true → Limited.field b x ≤ 3 := by
  intro b x
  cases x with
  | mk n => intro h; rw [Limited.field_mk]; exact of_decide_eq_true h

theorem check_decides :
    Regula.ExecutableContract check (fun g =>
      Regula.Decides (· = true) (fun input : Limited true => Limited.field true input < 3)
        (fun input => g (Limited.field true input))) :=
  ⟨.of_iff (fun input => by
      have bound := Limited.field_le input rfl
      simp only [check, decide_eq_true_eq]
      omega)
    ⟨(Limited.mk 0 : Limited true), by decide⟩ ⟨(Limited.mk 3 : Limited true), by decide⟩⟩

/-- Outside the restricted domain the function accepts a number the specification excludes. -/
theorem check_four : check 4 = true ∧ ¬ 4 < 3 := by decide
