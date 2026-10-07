import RegulaVerification
import Regula.Contract
import Regula.Decision

/-! # Decision contracts of the verification driver

The decision kind of each pure decision `RegulaVerification` runs, with its
`@[regula_decision]` registration. The driver imports only the toolchain, because
`scripts/verify.sh` runs it with `lean --run` before the package is built. This second module of
its library imports it together with the two checker interfaces, and nothing the driver runs
imports this module. Each kind restates theorems of the driver about the same definition and adds
the witnesses a kind requires. -/
namespace RegulaVerification

/-- `parseMode` accepts exactly the argument lists of the supported invocations
(`parseMode_sound`, `parseMode_roundtrip`): it accepts the empty list, which selects the first
acceptance step, and refuses an unsupported argument. -/
theorem checked_parseMode : Regula.ExecutableContract parseMode
    (Regula.Decides (·.isSome = true) (fun args => ∃ mode, args = arguments mode)) :=
  ⟨.of_roundtrip parseMode_roundtrip
    (fun args mode parsed => (parseMode_sound args mode parsed).symm) .ordinary
    (unwritten := ["unsupported"]) (by decide)⟩

/-- `dependencyFree` accepts only a lock manifest whose `packages` array is present and empty
(`dependencyFree_packages`), and it accepts the manifest with that one field. That it accepts
every such manifest is not claimed. -/
theorem checked_dependencyFree : Regula.ExecutableContract dependencyFree
    (Regula.DecidesSoundly (· = true)
      (fun manifest => manifest.getObjValAs? (Array Lean.Json) "packages" = .ok #[])) :=
  ⟨{ sound := dependencyFree_packages
     accepted := ⟨Lean.Json.mkObj [("packages", Lean.Json.arr #[])], by decide +kernel⟩ }⟩

/-- `select` accepts exactly the argument lists of the supported invocations, as `parseMode`
does (`select_exact`): it accepts the empty list and refuses an unsupported argument. Its result
type depends on the arguments, since the selected mode carries the proof that the arguments are
that mode's, so the decision is of whether a mode is selected (`Regula.Dependent.isSome`). -/
theorem checked_select : Regula.ExecutableContract select (fun selected =>
    Regula.Decides (· = true) (fun args => ∃ mode, args = arguments mode)
      (Regula.Dependent.isSome selected)) :=
  have isSome (args : List String) :
      Regula.Dependent.isSome select args = (parseMode args).isSome := by
    rw [Regula.Dependent.isSome, ← select_exact, Option.isSome_map]
  ⟨.of_iff (fun args => by rw [isSome]; exact checked_parseMode.evidence.iff args)
    ⟨[], by rw [isSome]; decide⟩ ⟨["unsupported"], by rw [isSome]; decide⟩⟩

/-- `passed` accepts exactly the ends in which every command ran to its end with exit status 0
(`passed_iff`). It accepts a step whose one command so ended, and refuses one whose command
ended with another status. The specification is stated with membership and equality alone; it
uses nothing `passed` is defined with. -/
theorem checked_passed : Regula.ExecutableContract passed
    (Regula.Decides (· = true)
      (fun ends : List (Option UInt32) => ∀ ended ∈ ends, ended = some 0)) :=
  ⟨.of_iff passed_iff ⟨[some 0], by decide⟩ ⟨[some 1], by decide⟩⟩

/-- `walked` accepts exactly the paths below the project root that the copy of the first
acceptance step holds (`walked_iff`): the path does not start with `tmp`, and none of its
components is a name that an isolated copy of a project leaves out. It accepts `lean` and
refuses `tmp`. That this is the rule of the checker's isolated copy is not claimed. -/
theorem checked_walked : Regula.ExecutableContract walked
    (Regula.Decides (· = true) (fun relative => relative.head? ≠ some "tmp" ∧
      ∀ component ∈ relative, component ≠ ".git" ∧ component ≠ ".lake" ∧ component ≠ ".cache" ∧
        component ≠ ".regula-scratch")) :=
  ⟨.of_iff walked_iff ⟨["lean"], by decide⟩ ⟨["tmp"], by decide⟩⟩

/-- `removal` decides to remove exactly when a directory is at the path and its real path is that
path (`removal_remove_iff`). It removes for a directory at its own place and does not remove when
nothing is there. With a symbolic link at the path the place is not a directory, so it does not
remove. -/
theorem checked_removal : Regula.ExecutableContract removal
    (Regula.Decides (· = .remove) (fun observed =>
      observed.place = .directory ∧ observed.sameLocation = true)) :=
  ⟨.of_iff removal_remove_iff ⟨⟨.directory, true⟩, rfl⟩ ⟨⟨.absent, false⟩, by decide⟩⟩

attribute [regula_decision] parseMode dependencyFree select passed walked removal

end RegulaVerification
