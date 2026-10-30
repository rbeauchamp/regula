import RegulaVerification.Driver
import Regula.Contract
import Regula.Decision

/-! # Decision contracts of the verification driver

The decision kind of each pure decision `RegulaVerification` registers with `Regula.RegisteredDecision`.
The driver imports only the toolchain, because `scripts/verify.sh` runs it with `lean --run` before
the package is built. This second module of its library imports it together with the two checker
interfaces, and nothing the driver runs imports this module. Each kind restates theorems of the
driver about the same definition and adds the witnesses a kind requires. It imports no module of the
excluded `Regula` library. -/

namespace RegulaVerification

/-- `parseMode` accepts exactly the argument lists of the supported invocations
(`parseMode_sound`, `parseMode_roundtrip`): it accepts the empty list, which selects the first
acceptance step, and refuses an unsupported argument. -/
theorem checked_parseMode : Regula.ExecutableContract parseMode
    (Regula.Decides (·.isSome = true) (fun args => ∃ mode, args = arguments mode)) :=
  ⟨.of_roundtrip parseMode_roundtrip
    (fun args mode parsed => (parseMode_sound args mode parsed).symm) .ordinary
    (unwritten := ["unsupported"]) (by decide)⟩

/-- `dependencyFree` accepts exactly a manifest that is there and records no package, with a package
overrides file that records none (`dependencyFree_iff`): it accepts such a manifest and refuses an
absent one. -/
theorem checked_dependencyFree : Regula.ExecutableContract dependencyFree
    (Regula.Decides (· = true)
      (fun read => ∃ manifest, read = some (manifest, #[]) ∧ manifest.packages = #[])) :=
  ⟨.of_iff dependencyFree_iff
    ⟨some ({ name := `regula, lakeDir := ".lake", fixedToolchain := false }, #[]), rfl⟩
    ⟨none, nofun⟩⟩

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

/-- `removal` decides to remove exactly when a directory is at the path and its real path is that
path (`removal_remove_iff`). It removes for a directory at its own place and does not remove when
nothing is there. With a symbolic link at the path the place is not a directory, so it does not
remove. -/
theorem checked_removal : Regula.ExecutableContract removal
    (Regula.Decides (· = .remove) (fun observed =>
      observed.place = .directory ∧ observed.sameLocation = true)) :=
  ⟨.of_iff removal_remove_iff ⟨⟨.directory, true⟩, rfl⟩ ⟨⟨.absent, false⟩, by decide⟩⟩

/-- `buildCovers` accepts exactly a surface manifest of the shape `claimedTargets` reads all of
whose claimed targets are targets of the first acceptance step's build (`buildCovers_iff`). It
accepts a manifest with no surface and refuses one with no `surfaces` field. That
`claimedTargets` reads the claimed targets as the checker's manifest reader does is not claimed. -/
theorem checked_buildCovers : Regula.ExecutableContract buildCovers
    (Regula.Decides (· = true) (fun manifest => ∃ targets,
      claimedTargets manifest = some targets ∧ ∀ target ∈ targets, target ∈ surfaceTargets)) :=
  ⟨.of_iff buildCovers_iff
    ⟨Lean.Json.mkObj [("surfaces", Lean.Json.arr #[])], by decide +kernel⟩
    ⟨Lean.Json.null, by decide +kernel⟩⟩

theorem parseMode_registered : Regula.RegisteredDecision @parseMode := ⟨⟩

theorem dependencyFree_registered : Regula.RegisteredDecision @dependencyFree := ⟨⟩

theorem select_registered : Regula.RegisteredDecision @select := ⟨⟩

theorem passed_registered : Regula.RegisteredDecision @passed := ⟨⟩

theorem removal_registered : Regula.RegisteredDecision @removal := ⟨⟩

theorem buildCovers_registered : Regula.RegisteredDecision @buildCovers := ⟨⟩

end RegulaVerification
