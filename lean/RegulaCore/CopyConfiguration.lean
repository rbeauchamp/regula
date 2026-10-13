import Lean
import Regula.Contract
import Regula.Decision

/-! # Captured configuration inputs for project-copy relocation

The request freezes these loaded package selections before construction. The same typed input
feeds the copier and the effective-configuration account; Lake loading remains an IO observation.
-/

namespace Regula.CopyConfiguration

open Lean

/-- The fields of one loaded dependency that determine its path override. -/
structure Dependency where
  /-- The loaded package name. -/
  package : String
  /-- Its loaded scope. -/
  scope : String
  /-- Its original canonical directory. -/
  root : String
  /-- Whether it is copied with the root package. -/
  owned : Bool
  /-- The loaded configuration file, relative to its directory. -/
  configFile : String
  /-- The loaded manifest file, relative to its directory. -/
  manifestFile : String
  deriving DecidableEq, BEq, ToJson, FromJson

/-- Project-relative filenames, or an exact absolute path for an external selected policy
manifest, and exact captured or generated text; absence is explicit. -/
abbrev Files := Array (String × Option String)

/-- Compare the complete derived expectation with the observed configuration. No field or
override entry is skipped; equality includes order, filenames, presence and exact text. -/
@[regula_decision] def check (pair : Files × Files) : Except String Unit :=
  if pair.2 = pair.1 then .ok () else .error "effective configuration differs from request"

/-- Configuration admission succeeds exactly when all expected and observed fields agree. -/
theorem check_iff (expected observed : Files) : check (expected, observed) = .ok () ↔ observed = expected := by
  simp [check]

/-- The actual configuration comparison decides complete equality, with both outcomes. -/
theorem checked_check : Regula.ExecutableContract check
    (Regula.Decides (· = .ok ()) (fun pair => pair.2 = pair.1)) :=
  ⟨.of_iff (fun pair => check_iff pair.1 pair.2) ⟨(#[], #[]), rfl⟩
    ⟨(#[], #[("unexpected", none)]), by
      intro h
      have impossible := congrArg Array.size ((check_iff _ _).mp h)
      simp at impossible⟩⟩

/-- Loaded source selections captured as part of a request, without any destination state. -/
structure Inputs where
  /-- The original root package's canonical directory. -/
  project : String
  /-- The manifest file Lake loaded, relative to the package. -/
  manifestFile : String
  /-- Lake's loaded packages fallback. -/
  packagesDir : String
  /-- The overrides file Lake reads, relative to the package. -/
  overridesFile : String
  /-- Every resolved dependency, in Lake's loaded order. -/
  dependencies : Array Dependency
  deriving DecidableEq, BEq, ToJson, FromJson

end Regula.CopyConfiguration
