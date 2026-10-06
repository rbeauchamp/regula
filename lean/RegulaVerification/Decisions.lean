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
that mode's, so the kind is one of `Regula.Dependent`. -/
theorem checked_select : Regula.ExecutableContract select
    (Regula.Dependent.Decides (·.isSome = true) (fun args => ∃ mode, args = arguments mode)) :=
  have isSome (args : List String) : (select args).isSome = (parseMode args).isSome := by
    rw [← select_exact, Option.isSome_map]
  ⟨.of_iff (fun args => by rw [isSome]; exact checked_parseMode.evidence.iff args)
    ⟨[], by rw [isSome]; decide⟩ ⟨["unsupported"], by rw [isSome]; decide⟩⟩

attribute [regula_decision] parseMode dependencyFree select

end RegulaVerification
