module

public import Regula.Contract
public import Fixtures.Positive.HiddenTest

/-
Controls for the shared-test rule in a `module` file whose shared test is imported with no
exported value (`Fixtures.Positive.HiddenTest`). The environment of this file has the test and
the function around it as axioms. The project check has their values, so it must refuse each
registration below and name the test:

* `fixtures_imported_check_decides`: the specification and the function both call the imported
  test.
* `fixtures_imported_none_decides`: the specification calls the imported test, and the function
  reaches it only below the imported function `fixtures_hidden_count`.

The native linter controls `SharedTestHidden` and `SharedTestBelowHidden` of
`Regula.Qualification.NativeLinter` give the same two registrations to the editor: it refuses
the first from the type of the test, and it reports the reading of the second as incomplete.
-/

/-- Whether `n` is below four: it calls the imported test. -/
public def fixtures_imported_check (n : Nat) : Bool := fixtures_hidden_small n

public theorem fixtures_imported_check_decides :
    Regula.ExecutableContract fixtures_imported_check
      (Regula.Decides (· = true) fun n => fixtures_hidden_small n = true) :=
  ⟨.of_iff (fun _ => Iff.rfl) ⟨0, fixtures_hidden_small_zero⟩ ⟨4, fixtures_hidden_small_four⟩⟩

/-- Whether the test refuses each element: it calls the imported function around the test. -/
public def fixtures_imported_none (numbers : List Nat) : Bool :=
  fixtures_hidden_count numbers == 0

public theorem fixtures_imported_none_decides :
    Regula.ExecutableContract fixtures_imported_none
      (Regula.Decides (· = true) fun numbers => ∀ n ∈ numbers, fixtures_hidden_small n = false) :=
  ⟨.of_iff (fun numbers => by
      simp only [fixtures_imported_none, beq_iff_eq, fixtures_hidden_count_eq_zero_iff])
    ⟨[], by simp [fixtures_imported_none, fixtures_hidden_count_eq_zero_iff]⟩
    ⟨[0], by simp [fixtures_imported_none, fixtures_hidden_count_eq_zero_iff,
      fixtures_hidden_small_zero]⟩⟩
