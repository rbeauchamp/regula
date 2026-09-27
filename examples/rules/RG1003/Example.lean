import Dependency
/-! # Inherited reflexivity

Reflexivity inherited from the dependency. -/
theorem reflexive (n : Nat) : n = n := Dependency.reflexive n
