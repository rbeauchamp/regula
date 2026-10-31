import Regula.Contract
import Regula.Decision

/-! # Foundation claim profiles

The profile that a surface of `foundation_manifest.json` claims, with its spelling, which the
manifest's parse reads back (`Profile.parse?_eq_some_iff`). -/

namespace Regula.Checker.Policy

/-- A foundation claim profile, as a surface of `foundation_manifest.json` names it. -/
inductive Profile where
  /-- `kernel-only`: no axioms. -/
  | kernelOnly
  /-- `choice-free`: at most `propext` and `Quot.sound`. -/
  | choiceFree
  /-- `standard-logical`: additionally `Classical.choice`. -/
  | standardLogical
  /-- `compiler-trusting`: not a conforming profile, which the checker refuses. -/
  | compilerTrusting
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Profile

/-- The profile a manifest or command-line spelling names; any other text is refused. -/
def parse? : String → Option Profile
  | "kernel-only" => some .kernelOnly
  | "choice-free" => some .choiceFree
  | "standard-logical" => some .standardLogical
  | "compiler-trusting" => some .compilerTrusting
  | _ => none

theorem parse?_registered : Regula.RegisteredDecision @parse? := ⟨⟩

/-- The spelling of a profile, which `parse?` reads back (`Profile.parse?_eq_some_iff`). -/
def toString : Profile → String
  | .kernelOnly => "kernel-only"
  | .choiceFree => "choice-free"
  | .standardLogical => "standard-logical"
  | .compilerTrusting => "compiler-trusting"

instance : ToString Profile := ⟨toString⟩

end Profile

/-- Command-line and manifest spellings select exactly the profile rendered by `toString`. -/
theorem Profile.parse?_eq_some_iff (text : String) (profile : Profile) :
    Profile.parse? text = some profile ↔ profile.toString = text := by
  constructor
  · intro h
    unfold Profile.parse? at h
    split at h <;> cases h <;> rfl
  · rintro rfl
    cases profile <;> rfl

/-- `Profile.parse?` accepts exactly the profile spellings (`Profile.parse?_eq_some_iff`). -/
theorem Profile.checked_parse : Regula.ExecutableContract Profile.parse?
    (Regula.Decides (·.isSome = true) fun text => ∃ profile : Profile, text = profile.toString) :=
  ⟨.of_roundtrip (fun profile => (Profile.parse?_eq_some_iff _ profile).mpr rfl)
    (fun text profile read => (Profile.parse?_eq_some_iff text profile).mp read)
    .kernelOnly (unwritten := "") rfl⟩

end Regula.Checker.Policy
