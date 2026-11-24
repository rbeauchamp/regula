module

public import RegulaSpecification.EffectsRecord
public import RegulaSpecification.Proofs.Load
import all Regula.Load

@[expose] public section

namespace RegulaSpecification.Effects

open System (FilePath)
open Regula.Effect
open RegulaSpecification.Loader

variable {L E : Type}

theorem exactBelow_eq_true_iff (dir path real : FilePath) :
    Regula.Load.exactBelow dir path real = true ↔ ExactlyBelow dir path real :=
  exactBelow_iff dir path real

theorem exactBelow_eq_false_iff (dir path real : FilePath) :
    Regula.Load.exactBelow dir path real = false ↔ ¬ ExactlyBelow dir path real := by
  rw [← exactBelow_eq_true_iff, Bool.not_eq_true]

theorem below_eq_true_iff (dir path : FilePath) : Regula.Load.below dir path = true ↔ StrictlyBelow dir path :=
  below_iff dir path

theorem below_eq_false_iff (dir path : FilePath) : Regula.Load.below dir path = false ↔ ¬ StrictlyBelow dir path := by
  rw [← below_eq_true_iff, Bool.not_eq_true]

theorem startsSearchPath_eq_true_iff (received : String) (root : Root L) :
    Regula.Load.startsSearchPath (root.leanPath.map toString) ((System.SearchPath.parse received).map toString) = true ↔
      SearchPathStarts received root := by
  rw [Regula.Load.startsSearchPath, List.isPrefixOf_iff_prefix]
  exact ⟨fun ⟨r, hr⟩ => ⟨r, hr.symm⟩, fun ⟨r, hr⟩ => ⟨r, hr.symm⟩⟩

theorem startsSearchPath_eq_false_iff (received : String) (root : Root L) :
    Regula.Load.startsSearchPath (root.leanPath.map toString) ((System.SearchPath.parse received).map toString) = false ↔
      ¬ SearchPathStarts received root := by
  rw [← startsSearchPath_eq_true_iff, Bool.not_eq_true]

end RegulaSpecification.Effects
