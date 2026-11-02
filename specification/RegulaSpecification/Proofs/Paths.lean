/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.EffectsRecord
import RegulaSpecification.Proofs.Load

/-!
# The checker's decisions over paths, against what they state

Each decision of the checker over a path, with a theorem that relates it, in both directions, to a statement that names none of
the checker's functions: `exactBelow` to `ExactlyBelow`, `below` to `StrictlyBelow` and `startsSearchPath` to `SearchPathStarts`. `RegulaSpecification.Language` relates `treeRelative` to `TreeRelative`, and
`RegulaSpecification.Proofs.ReaderWalk` relates `inTree` to it, and `apart_iff` relates `apart` to `Apart`.
-/

namespace RegulaSpecification.Effects

open System (FilePath)
open Regula.Effect
open RegulaSpecification.Loader

variable {L E : Type}

/-- `exactBelow` decides `ExactlyBelow`. -/
theorem exactBelow_eq_true_iff (dir path real : FilePath) :
    Regula.Load.exactBelow dir path real = true ↔ ExactlyBelow dir path real :=
  exactBelow_iff dir path real

/-- The same, of a refusal. -/
theorem exactBelow_eq_false_iff (dir path real : FilePath) :
    Regula.Load.exactBelow dir path real = false ↔ ¬ ExactlyBelow dir path real := by
  rw [← exactBelow_eq_true_iff, Bool.not_eq_true]

/-- `below` decides `StrictlyBelow`. -/
theorem below_eq_true_iff (dir path : FilePath) : Regula.Load.below dir path = true ↔ StrictlyBelow dir path :=
  below_iff dir path

/-- The same, of a refusal. -/
theorem below_eq_false_iff (dir path : FilePath) : Regula.Load.below dir path = false ↔ ¬ StrictlyBelow dir path := by
  rw [← below_eq_true_iff, Bool.not_eq_true]

/-- **`startsSearchPath` decides what the search path states**, in both directions, for every search path. -/
theorem startsSearchPath_eq_true_iff (received : String) (root : Root L) :
    Regula.Load.startsSearchPath (root.leanPath.map toString) ((System.SearchPath.parse received).map toString) = true ↔
      SearchPathStarts received root := by
  rw [Regula.Load.startsSearchPath, List.isPrefixOf_iff_prefix]
  exact ⟨fun ⟨r, hr⟩ => ⟨r, hr.symm⟩, fun ⟨r, hr⟩ => ⟨r, hr.symm⟩⟩

/-- The same, of a refusal. -/
theorem startsSearchPath_eq_false_iff (received : String) (root : Root L) :
    Regula.Load.startsSearchPath (root.leanPath.map toString) ((System.SearchPath.parse received).map toString) = false ↔
      ¬ SearchPathStarts received root := by
  rw [← startsSearchPath_eq_true_iff, Bool.not_eq_true]

end RegulaSpecification.Effects
