/-
Mutation of `Fixtures.Positive.DependentDecisionKinds`, at the toolchain boundary, for the second
review's first finding: the reviewer's registration, word for word. It gives a function that
refuses every input a two-way kind, through an acceptance predicate that is stated for every
payload type and so reads the payload proposition. No kind has such a predicate: the kinds of
`Regula.Contract` take `accepts : ρ → Prop` for the one result type of the decided function, and
no structure `Regula.Dependent.Decides` exists. Lean must reject the file.
-/
import Regula.Contract

def never (_ : Bool) : Bool := false

theorem never_decides :
    Regula.ExecutableContract never
      (Regula.Dependent.Decides (payload := fun b : Bool => b = true)
        (Result := fun _ : Prop => Bool) (fun {p} _ => p) (fun b => b = true)) :=
  ⟨{ sound := fun _ holds => holds
     accepted := ⟨true, rfl⟩
     complete := fun _ holds => holds
     refused := ⟨false, by decide⟩ }⟩
