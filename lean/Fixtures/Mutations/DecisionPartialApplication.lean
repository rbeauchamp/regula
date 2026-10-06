/-
Mutation of `Fixtures.Positive.DependentDecisionKinds`, at the toolchain boundary, for the finding
of the review of the corrected design: the kind is stated about the implementation with an
argument left. The result of the decided function is then a function, the acceptance predicate
reads it at `false`, and the kind is the kind of that one slice (`Regula.Decides.iff_slice`):
each function below refuses an input that satisfies the specification, at `true`. Lean accepts
each proof. The checker must refuse each registration under RG1007 and give the number of
arguments that are left. The three registrations are the three forms that reach the class: a
field application (the reviewer's registration), the constant itself, and `Function.uncurry`.
-/
import Regula.Contract

/-- The reviewer's function: the last argument is not supplied below. -/
def lowUnless (n : Nat) (i : Fin (n + 1)) (b : Bool) : Bool := !b && decide (i.val < 3)

theorem lowUnless_decides :
    Regula.ExecutableContract lowUnless (fun g =>
      Regula.Decides (fun h : Bool → Bool => h false = true)
        (fun p : (n : Nat) ×' Fin (n + 1) => p.2.val < 3)
        (fun p => g p.1 p.2)) :=
  ⟨.of_iff (fun p => by simp [lowUnless]) ⟨⟨0, 0⟩, by decide⟩ ⟨⟨3, 3⟩, by decide⟩⟩

/-- The function refuses an input that satisfies the specification. -/
theorem lowUnless_refuses : lowUnless 0 0 true = false ∧ (0 : Fin 1).val < 3 := by decide

/-- A function of two arguments, decided below as a function of the first. -/
def smallUnless (n : Nat) (b : Bool) : Bool := !b && decide (n < 3)

theorem smallUnless_decides :
    Regula.ExecutableContract smallUnless
      (Regula.Decides (fun h : Bool → Bool => h false = true) (fun n => n < 3)) :=
  ⟨.of_iff (fun n => by simp [smallUnless]) ⟨0, by decide⟩ ⟨3, by decide⟩⟩

/-- A function of three arguments, of which `Function.uncurry` supplies two below. -/
def sumUnless (n m : Nat) (b : Bool) : Bool := !b && decide (n + m < 3)

theorem sumUnless_decides :
    Regula.ExecutableContract sumUnless (fun g =>
      Regula.Decides (fun h : Bool → Bool => h false = true)
        (fun p : Nat × Nat => p.1 + p.2 < 3) (Function.uncurry g)) :=
  ⟨.of_iff (fun p => by simp [sumUnless, Function.uncurry]) ⟨(0, 0), by decide⟩
    ⟨(3, 0), by decide⟩⟩
