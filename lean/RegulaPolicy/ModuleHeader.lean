module

public import Regula.Contract

/-! # Module header decision

The decision behind RG5001 for one claimed module (standard §5.3 and §6.4): the module has a
module docstring, that docstring is the first command after the imports, and no import is
repeated with the same modifiers. These are the checks Mathlib's header linter makes on a
module's docstring placement and imports; a library that follows standard §6.7 turns that linter
off because it also enforces Mathlib's copyright header.

## Main declarations

- `Observation`: what the adapter reads of a module: whether it has module documentation, whether
  the first command after its header is a module docstring, and its header imports in order.
- `failures`: the executed decision, every failure of one observation in a fixed order.
- `failures_eq_nil_iff`: no failure exactly when `OK` holds.
- `checked_failures`: that equivalence registered as a two-way decision (`Regula.Decides`), with
  an accepted and a refused header.
- `mem_repeated_iff`: a repeated-import failure names exactly the imports that occur twice or more.

## Boundaries

The observation is supplied by the operational adapter, which parses the module's header and
first command with Lean's own parser and reads the module documentation Lean recorded. These
theorems concern the decision over that observation, not the adapter's parsing. -/

@[expose] public section

namespace RegulaPolicy.ModuleHeader

open Lean (Name)

/-- One `import` of a module header: the imported module and its modifiers, the fields of
Lean's `Import`. Two imports repeat each other when all four fields agree, so `public import A`
and `import all A` are different imports. -/
structure ImportSpec where
  /-- The imported module. -/
  module : Name
  /-- `import all`. -/
  importAll : Bool
  /-- `public import`. -/
  isExported : Bool
  /-- `meta import`. -/
  isMeta : Bool
  deriving DecidableEq, Repr

/-- What the RG5001 decision reads of one claimed module. -/
structure Observation where
  /-- The module has a module docstring, in either of Lean's documentation formats. -/
  documented : Bool
  /-- The first command after the module header is a module docstring (`/-! … -/`). -/
  documentationFirst : Bool
  /-- The header's imports, in source order. -/
  imports : List ImportSpec
  deriving DecidableEq, Repr

/-- One way a module header fails RG5001. -/
inductive Failure where
  /-- The module has no module docstring. -/
  | missingDocumentation
  /-- The module has a module docstring, but another command comes first after the imports. -/
  | misplacedDocumentation
  /-- The header imports `spec` more than once. -/
  | repeatedImport (spec : ImportSpec)
  deriving DecidableEq, Repr

/-- The imports that occur more than once, each listed once, in order of first occurrence. -/
def repeated (imports : List ImportSpec) : List ImportSpec :=
  (imports.filter fun spec => 1 < imports.count spec).eraseDups

/-- Every failure of a module header: first the documentation failure, if any (a missing
docstring is reported as missing, not also as misplaced), then each repeated import. -/
def failures (o : Observation) : List Failure :=
  (if !o.documented then [.missingDocumentation]
    else if !o.documentationFirst then [.misplacedDocumentation] else []) ++
  (repeated o.imports).map .repeatedImport

/-- The RG5001 obligation of one module: it is documented, its docstring comes first after the
imports, and its imports are pairwise different. -/
def OK (o : Observation) : Prop :=
  o.documented = true ∧ o.documentationFirst = true ∧ o.imports.Nodup

/-- A repeated-import failure names exactly the imports that occur at least twice. -/
theorem mem_repeated_iff (imports : List ImportSpec) (spec : ImportSpec) :
    spec ∈ repeated imports ↔ 1 < imports.count spec := by
  simp only [repeated, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq,
    and_iff_right_iff_imp]
  exact fun h => List.count_pos_iff.mp (by omega)

/-- No import is repeated exactly when the imports are pairwise different. -/
theorem repeated_eq_nil_iff (imports : List ImportSpec) :
    repeated imports = [] ↔ imports.Nodup := by
  rw [List.nodup_iff_count_of_mem, List.eq_nil_iff_forall_not_mem]
  refine ⟨fun h a ha => ?_, fun h a ha => ?_⟩
  · have hpos := List.count_pos_iff.mpr ha
    have := h a
    rw [mem_repeated_iff] at this
    omega
  · rw [mem_repeated_iff] at ha
    have hmem : a ∈ imports := List.count_pos_iff.mp (by omega)
    have := h a hmem
    omega

/-- The decision reports no failure exactly when the module meets its RG5001 obligation. -/
theorem failures_eq_nil_iff (o : Observation) : failures o = [] ↔ OK o := by
  rw [OK, ← repeated_eq_nil_iff]
  cases hd : o.documented <;> cases hf : o.documentationFirst <;>
    simp [failures, hd, hf]

/-- The documentation failure, when there is one, is determined by the two documentation
observations alone and comes first. -/
theorem failures_documentation (o : Observation) :
    (failures o).head? =
      if !o.documented then some .missingDocumentation
      else if !o.documentationFirst then some .misplacedDocumentation
      else ((repeated o.imports).map Failure.repeatedImport).head? := by
  cases hd : o.documented <;> cases hf : o.documentationFirst <;> simp [failures, hd, hf]

/-- `failures` reports nothing exactly for a header that meets `OK` (`failures_eq_nil_iff`):
nothing for a documented header with no import, and a failure for an undocumented one. -/
theorem checked_failures :
    Regula.ExecutableContract failures (Regula.Decides (· = []) OK) :=
  ⟨.of_iff failures_eq_nil_iff ⟨⟨true, true, []⟩, by decide⟩ ⟨⟨false, false, []⟩, by decide⟩⟩

end RegulaPolicy.ModuleHeader
