import RegulaCompiler
import Regula.Contract
import Regula.Decision

/-! # Decision contracts of the compiler installer

The decision kind of each pure decision `RegulaCompiler` runs, with its `@[regula_decision]`
registration. The installer imports only the toolchain, because CI runs it with `lean --run`
before the package is built. This second module of its library imports it together with the two
checker interfaces, and nothing the installer runs imports this module. Each kind restates a
theorem of the installer about the same definition and adds the witnesses a kind requires. -/
namespace RegulaCompiler

/-- `source?` accepts only a specification that passes `valid` (`source?_sound`), and it accepts
the one given here. That it accepts every specification that passes `valid` is not claimed, and
neither is which source it returns; that is `source?_sound`. -/
theorem checked_source : Regula.ExecutableContract source?
    (Regula.DecidesSoundly (·.isSome = true) (fun spec => valid spec = true)) :=
  ⟨{ sound := fun spec accepted => by
       cases admitted : source? spec with
       | some source => exact (source?_sound spec source admitted).2
       | none => rw [admitted] at accepted; exact absurd accepted Bool.false_ne_true
     accepted := ⟨{ owner := "leanprover", repository := "lean4", selector := "regula"
                    revision := "0123456789abcdef0123456789abcdef01234567" }, by
       simp (config := { decide := true }) [source?, valid, component, objectName]⟩ }⟩

/-- `admitsIdentity` accepts exactly a full object name that both reports equal
(`admitsIdentity_iff`): it accepts such a name reported twice and refuses three empty texts. -/
theorem checked_admitsIdentity : Regula.ExecutableContract admitsIdentity (fun admits =>
    Regula.Decides (· = true)
      (fun input : (String × String) × String =>
        objectName input.1.1 = true ∧ input.1.2 = input.1.1 ∧ input.2 = input.1.1)
      (Function.uncurry (Function.uncurry admits))) :=
  ⟨.of_iff (fun input => admitsIdentity_iff input.1.1 input.1.2 input.2)
    ⟨(("0123456789abcdef0123456789abcdef01234567", "0123456789abcdef0123456789abcdef01234567"),
        "0123456789abcdef0123456789abcdef01234567"),
      (admitsIdentity_iff _ _ _).mpr ⟨by simp [objectName]; decide, rfl, rfl⟩⟩
    ⟨(("", ""), ""), fun accepted =>
      absurd ((admitsIdentity_iff "" "" "").mp accepted).1 (by decide)⟩⟩

/-- `installsSystemPackages` accepts exactly a GitHub Actions job on Linux
(`installsSystemPackages_iff`): it accepts those two values and refuses two absent ones. -/
theorem checked_installsSystemPackages :
    Regula.ExecutableContract installsSystemPackages (fun installs =>
      Regula.Decides (· = true)
        (fun input : Option String × Option String =>
          input.1 = some "true" ∧ input.2 = some "Linux")
        (Function.uncurry installs)) :=
  ⟨.of_iff (fun input => installsSystemPackages_iff input.1 input.2)
    ⟨(some "true", some "Linux"), (installsSystemPackages_iff _ _).mpr ⟨rfl, rfl⟩⟩
    ⟨(none, none), fun accepted =>
      nomatch ((installsSystemPackages_iff none none).mp accepted).1⟩⟩

attribute [regula_decision] source? admitsIdentity installsSystemPackages

end RegulaCompiler
