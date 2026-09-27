/-!
Checked correspondence at general universes with implicit types, a dependent
value, and a proof parameter in the actual executable domain. The theorem
reorders parameters and states a reversed equality at a proper domain prefix.
The remaining domain is discharged by congruence, not a binder-count rule.
-/
universe u v

def fixtures_dependent_impl {α : Type u} {β : α → Type v}
    (a : α) (b : β a) (n : Nat) (_h : 0 < n) : β a × Nat := (b, 2 * n)

@[implemented_by fixtures_dependent_impl]
def fixtures_dependent_reference {α : Type u} {β : α → Type v}
    (a : α) (b : β a) (n : Nat) (_h : 0 < n) : β a × Nat := (b, n + n)

theorem fixtures_dependent_correspondence {α : Type u} {β : α → Type v} (a : α) :
    @fixtures_dependent_impl α β a = @fixtures_dependent_reference α β a := by
  funext b n h
  simp only [fixtures_dependent_impl, fixtures_dependent_reference, Nat.two_mul]
