/-
Mutation of `Fixtures.Positive.DependentDecisionKinds`, at the toolchain boundary: the kind is
stated about the implementation at universe level zero, not at its own universe parameter, so it
says nothing of the lists of a type in a higher universe. Lean accepts the proof; the checker
must refuse the registration under RG1007 and name the levels.
-/
import Regula.Contract

universe u

def inhabited {α : Type u} (items : List α) : Bool := !items.isEmpty

theorem inhabited_decides :
    Regula.ExecutableContract @inhabited.{0} (fun check =>
      Regula.Decides (· = true) (fun input => input.2 ≠ [])
        (fun input : (α : Type) × List α => @check input.1 input.2)) :=
  ⟨.of_iff (fun input => by cases input.2 <;> simp [inhabited])
    ⟨⟨Unit, [()]⟩, rfl⟩ ⟨⟨Unit, []⟩, by simp [inhabited]⟩⟩
