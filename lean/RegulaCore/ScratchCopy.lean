import Regula.Contract
import Regula.Decision

/-! # The place of a copy that the verification driver made

The two decisions about paths by which a project audit admits a copy of the project that the
verification driver made (`AxiomGate.driverCopy`): that the copy is the directory `project` of a
directory of the project's scratch area, and that the audit's own executable is below the copy's
build directory. Each is about lists of path components and has a decision contract.

The paths are observations of the audit (`IO.FS.realPath`, Lake's build directory of the copy,
`IO.appPath`). These decisions do not show that the driver made the copy new in the run that
audits it. No path shows that, and it is the statement that rests on the driver. -/

namespace Regula.Checker.ScratchCopy

/-- `List.isPrefixOf?` gives the rest of a list exactly when the list is the prefix and then that
rest. -/
theorem isPrefixOf?_eq_some_iff (start path rest : List String) :
    start.isPrefixOf? path = some rest ↔ path = start ++ rest := by
  induction start generalizing path with
  | nil => simp [List.isPrefixOf?, eq_comm]
  | cons first others ih =>
    cases path with
    | nil => simp [List.isPrefixOf?]
    | cons head tail =>
      by_cases same : first = head
      · simp [List.isPrefixOf?, same, ih]
      · simp [List.isPrefixOf?, same, Ne.symm same]

/-- The name of the scratch directory when `path` is the directory `project` directly inside a
directory of the scratch area `area`, each given by its path components. -/
@[regula_decision]
def name? (area path : List String) : Option String :=
  match area.isPrefixOf? path with
  | some [name, "project"] => some name
  | _ => none

/-- `name?` gives a name exactly for the path that is the area, that name and `project`. -/
theorem name?_eq_some_iff (area path : List String) (name : String) :
    name? area path = some name ↔ path = area ++ [name, "project"] := by
  unfold name?
  constructor
  · intro found
    split at found
    · next directory rest =>
      cases found
      exact (isPrefixOf?_eq_some_iff _ _ _).mp rest
    · cases found
  · rintro rfl
    have rest : area.isPrefixOf? (area ++ [name, "project"]) = some [name, "project"] :=
      (isPrefixOf?_eq_some_iff _ _ _).mpr rfl
    simp [rest]

/-- `name?` finds a name exactly for a path that is the area, one name and `project`: it finds
one for `x/project` below the empty area and none for the empty path. -/
theorem checked_name? : Regula.ExecutableContract name? (fun decide =>
    Regula.Decides (·.isSome = true)
      (fun input : List String × List String => ∃ name, input.2 = input.1 ++ [name, "project"])
      (Function.uncurry decide)) :=
  ⟨.of_iff
    (fun input => by
      constructor
      · intro found
        cases named : name? input.1 input.2 with
        | none => simp [Function.uncurry, named] at found
        | some name => exact ⟨name, (name?_eq_some_iff _ _ _).mp named⟩
      · rintro ⟨name, shaped⟩
        simp [Function.uncurry, (name?_eq_some_iff _ _ _).mpr shaped])
    ⟨([], ["x", "project"]), by decide⟩ ⟨([], []), by decide⟩⟩

/-- Whether `path` is below `directory` and is not `directory` itself, each given by its path
components. -/
@[regula_decision]
def inside (directory path : List String) : Bool :=
  match directory.isPrefixOf? path with
  | some (_ :: _) => true
  | _ => false

/-- `inside` accepts exactly a path that is the directory with one component or more after
it. -/
theorem inside_iff (directory path : List String) :
    inside directory path = true ↔ ∃ first rest, path = directory ++ first :: rest := by
  unfold inside
  constructor
  · intro found
    split at found
    · next first rest below =>
      exact ⟨first, rest, (isPrefixOf?_eq_some_iff _ _ _).mp below⟩
    · cases found
  · rintro ⟨first, rest, rfl⟩
    have below : directory.isPrefixOf? (directory ++ first :: rest) = some (first :: rest) :=
      (isPrefixOf?_eq_some_iff _ _ _).mpr rfl
    simp [below]

/-- `inside` accepts exactly the paths below a directory: it accepts `a/b` below `a` and
refuses `a` itself. -/
theorem checked_inside : Regula.ExecutableContract inside (fun decide =>
    Regula.Decides (· = true)
      (fun input : List String × List String =>
        ∃ first rest, input.2 = input.1 ++ first :: rest)
      (Function.uncurry decide)) :=
  ⟨.of_iff (fun input => inside_iff input.1 input.2)
    ⟨(["a"], ["a", "b"]), by decide⟩ ⟨(["a"], ["a"]), by decide⟩⟩

end Regula.Checker.ScratchCopy
