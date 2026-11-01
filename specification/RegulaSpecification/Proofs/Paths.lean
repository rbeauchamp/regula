/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.EffectsRecord
import RegulaSpecification.Proofs.Load

/-!
# The checker's decisions over paths, against what they state

Each decision of the checker over a path or an identity, with a theorem that relates it, in both directions, to a statement that names none of
the checker's functions: `exactBelow` to `ExactlyBelow`, `below` to `StrictlyBelow` and `dispatchedFrom` to `LakeDispatched`. `RegulaSpecification.Language` relates `treeRelative` to `TreeRelative`, and
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

/-- **`dispatchedFrom` decides what the search path states**, in both directions, for every search path. -/
theorem dispatchedFrom_eq_true_iff (received : String) (root : Root L) :
    Regula.Load.dispatchedFrom (root.leanPath.map toString) ((System.SearchPath.parse received).map toString) = true ↔
      LakeDispatched received root := by
  rw [Regula.Load.dispatchedFrom, List.isPrefixOf_iff_prefix]
  exact ⟨fun ⟨r, hr⟩ => ⟨r, hr.symm⟩, fun ⟨r, hr⟩ => ⟨r, hr.symm⟩⟩

/-- The same, of a refusal. -/
theorem dispatchedFrom_eq_false_iff (received : String) (root : Root L) :
    Regula.Load.dispatchedFrom (root.leanPath.map toString) ((System.SearchPath.parse received).map toString) = false ↔
      ¬ LakeDispatched received root := by
  rw [← dispatchedFrom_eq_true_iff, Bool.not_eq_true]

end RegulaSpecification.Effects
