import Lean

/-!
# Module names that reach the audit

A module name names a file below a directory: `Lean.modToFilePath` joins its components with
`FilePath.join`, which discards its base for an absolute component. `safeModuleComponents?` admits a
name only when no component is absolute and no segment of a component between path separators is
empty, `.` or `..`. Every module name the audit handles has passed it at the entry where it reaches
the audit (`requireSafeModuleNames`), and `modulePath?` builds a path below its base from an admitted
name (`modulePath?_below`). This module imports only `Lean`, so each entry can use it.
-/

namespace Regula.Checker

open Lean System

/-- Whether `c` is a path separator of the current platform (`FilePath.pathSeparators`). -/
def isPathSeparator (c : Char) : Bool :=
  FilePath.pathSeparators.contains c

/-- The platform's own separator (`FilePath.pathSeparator`) is one of its separators. -/
theorem isPathSeparator_pathSeparator : isPathSeparator FilePath.pathSeparator = true := by
  unfold isPathSeparator FilePath.pathSeparators FilePath.pathSeparator
  cases System.Platform.isWindows <;> decide

/-- The characters of a path split at each path separator (`isPathSeparator`): the lexical
segments of the path, with an empty segment before a leading separator, between two adjacent
ones and after a trailing one. -/
def splitAtSeparators : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if isPathSeparator c then [] :: splitAtSeparators cs
    else match splitAtSeparators cs with
      | w :: ws => (c :: w) :: ws
      | [] => [[c]]

/-- A split has at least one segment. -/
theorem splitAtSeparators_ne_nil : ∀ cs : List Char, splitAtSeparators cs ≠ []
  | [] => by simp [splitAtSeparators]
  | c :: cs => by
    unfold splitAtSeparators
    split
    · simp
    · split <;> simp

/-- Splitting at a separator between two texts splits each text on its own. -/
theorem splitAtSeparators_append_separator {c : Char} (hc : isPathSeparator c = true) :
    ∀ a b : List Char, splitAtSeparators (a ++ c :: b) = splitAtSeparators a ++ splitAtSeparators b
  | [], b => by simp [splitAtSeparators, hc]
  | x :: a, b => by
    have ih := splitAtSeparators_append_separator hc a b
    simp only [List.cons_append, splitAtSeparators]
    split
    · simp [ih]
    · rw [ih]
      obtain ⟨w, ws, hw⟩ : ∃ w ws, splitAtSeparators a = w :: ws := by
        cases h : splitAtSeparators a with
        | nil => exact absurd h (splitAtSeparators_ne_nil a)
        | cons w ws => exact ⟨w, ws, rfl⟩
      simp [hw]

/-- A text with no separator is one segment. -/
theorem splitAtSeparators_of_no_separator :
    ∀ cs : List Char, (∀ x ∈ cs, isPathSeparator x = false) → splitAtSeparators cs = [cs]
  | [], _ => by simp [splitAtSeparators]
  | c :: cs, h => by
    have hc : isPathSeparator c = false := h c (by simp)
    have ih := splitAtSeparators_of_no_separator cs fun x hx => h x (by simp [hx])
    simp [splitAtSeparators, hc, ih]

/-- Whether `segment`, a part of a path between separators, names one entry directly below a
directory: it is not empty, not `.` or `..`, and holds no path separator. -/
def safeSegment (segment : String) : Bool :=
  !segment.isEmpty && segment != "." && segment != ".." && !segment.toList.any isPathSeparator

/-- The segments of `part` between path separators (`splitAtSeparators`). -/
def pathSegments (part : String) : List String :=
  (splitAtSeparators part.toList).map String.ofList

/-- Whether `part`, one component of a module name, names entries below a directory: it is not an
absolute path (`FilePath.isAbsolute`, so on Windows also a drive such as `C:`), and each of its
segments between path separators is a `safeSegment`, so it is not empty and has no `.` or `..`
segment. A relative component with separators, such as `foo/bar` of a library named `foo/bar`,
names `foo/bar` below the directory. `FilePath.join` discards its base for an absolute right
operand, so `Lean.modToFilePath` puts a module with an absolute component outside its directory,
and a `..` segment leaves it. -/
def safeModuleComponent (part : String) : Bool :=
  !(FilePath.mk part).isAbsolute && (pathSegments part).all safeSegment

/-- The string components of module name `name`, root first, when there is at least one and each
is a `safeModuleComponent`; `none` for the anonymous name, a numeric component or an unsafe one.
Every module name the audit handles passes it at the entry where the name reaches the audit
(`requireSafeModuleNames`, `Lake.checkModuleNames`, `Environment.attributeLoaded`). -/
def safeModuleComponents? : Name → Option (List String)
  | .anonymous => none
  | .num .. => none
  | .str p s =>
    if safeModuleComponent s then
      match p with
      | .anonymous => some [s]
      | p => (safeModuleComponents? p).map (· ++ [s])
    else none

/-- The first of `names` that `safeModuleComponents?` does not admit. -/
def unsafeModuleName? (names : Array Name) : Option Name :=
  names.find? fun name => (safeModuleComponents? name).isNone

/-- Refuse, before any path is built from them, module names that reach the audit at the entry
`entry` when one of them is not admitted by `safeModuleComponents?`: a component that is an
absolute path or has an empty, `.` or `..` segment between path separators, or a numeric component. -/
def requireSafeModuleNames (entry : String) (names : Array Name) : IO Unit := do
  if let some name := unsafeModuleName? names then
    throw <| IO.userError s!"module-name-unsafe: {entry} names module {name}, whose name has a \
      component that is an absolute path, has an empty, `.` or `..` segment between path \
      separators, or is a number"

/-- The path segments of the file of module `name` with extension `ext`, below the directory it
belongs to: the segments of each component of `name` (`safeModuleComponents?`, `pathSegments`), the
last one with `.` and `ext` appended; `none` unless `name` is admitted and every resulting segment
is a `safeSegment`. -/
def moduleSegments? (name : Name) (ext : String) : Option (List String) :=
  match safeModuleComponents? name with
  | none => none
  | some parts =>
    let segments := parts.flatMap pathSegments
    let withExtension := segments.dropLast ++ segments.getLast?.toList.map (· ++ "." ++ ext)
    if !withExtension.isEmpty && withExtension.all safeSegment then some withExtension else none

/-- The path of `segments` below the directory `dir`: the text of `dir`, then for each segment the
platform's path separator and the segment. -/
def pathBelow (dir : FilePath) : List String → FilePath
  | [] => dir
  | segment :: rest =>
    pathBelow ⟨dir.toString ++ String.singleton FilePath.pathSeparator ++ segment⟩ rest

/-- The lexical segments of a path below `dir` are those of `dir`, then the given segments. -/
theorem splitAtSeparators_pathBelow :
    ∀ (dir : FilePath) (segments : List String), (∀ s ∈ segments, safeSegment s = true) →
      splitAtSeparators (pathBelow dir segments).toString.toList =
        splitAtSeparators dir.toString.toList ++ segments.map String.toList
  | dir, [], _ => by simp [pathBelow]
  | dir, s :: rest, h => by
    have hs : safeSegment s = true := h s (by simp)
    have hno : ∀ x ∈ s.toList, isPathSeparator x = false := by
      intro x hx
      simp only [safeSegment, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at hs
      simpa using hs.2 x hx
    rw [pathBelow, splitAtSeparators_pathBelow _ rest fun t ht => h t (by simp [ht])]
    have hsplit : splitAtSeparators (dir.toString.toList ++ FilePath.pathSeparator :: s.toList) =
        splitAtSeparators dir.toString.toList ++ [s.toList] := by
      rw [splitAtSeparators_append_separator isPathSeparator_pathSeparator,
        splitAtSeparators_of_no_separator _ hno]
    simp [String.toList_append, hsplit]

/-- The file of module `name` with extension `ext` below the directory `dir`, the path of its
segments (`moduleSegments?`, `pathBelow`); `none` for an empty `dir`, whose path would start at the
root, and for a name that `safeModuleComponents?` does not admit. The ownership audit builds the
paths of checker sources, package sources and owned artifacts with it (`Lake.checkerSource`,
`Lake.packageModules`, `Environment.attributeLoaded`); the other paths built from module names rest
on the names having passed the check at their entry (`requireSafeModuleNames`).
`modulePath?_below` states that the path lies below `dir`. -/
def modulePath? (dir : FilePath) (name : Name) (ext : String) : Option FilePath :=
  if dir.toString.isEmpty then none else (moduleSegments? name ext).map (pathBelow dir)

/-- For every admitted module name and nonempty base, the path `modulePath?` builds lies below the
base directory: the base is not empty, and the lexical segments of the path (`splitAtSeparators`)
are those of the base followed by at least one more segment, none of which is empty, `.` or `..` or
holds a path separator. So the base's segments are a strict prefix of the path's, and no further
segment climbs out of the base. -/
theorem modulePath?_below {dir : FilePath} {name : Name} {ext : String} {path : FilePath}
    (h : modulePath? dir name ext = some path) :
    dir.toString ≠ "" ∧ ∃ more : List String, more ≠ [] ∧ (∀ s ∈ more, safeSegment s = true) ∧
      splitAtSeparators path.toString.toList =
        splitAtSeparators dir.toString.toList ++ more.map String.toList := by
  unfold modulePath? at h
  split at h
  · cases h
  · rename_i hdir
    refine ⟨fun hempty => hdir (by simp [hempty]), ?_⟩
    obtain ⟨segments, hsegments, rfl⟩ := Option.map_eq_some_iff.mp h
    unfold moduleSegments? at hsegments
    split at hsegments
    · cases hsegments
    · dsimp only at hsegments
      split at hsegments
      · rename_i hsafe
        cases hsegments
        simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
          List.all_eq_true] at hsafe
        exact ⟨_, hsafe.1, hsafe.2, splitAtSeparators_pathBelow dir _ hsafe.2⟩
      · cases hsegments

/-- The segments of the base directory are a strict prefix of those of each path `modulePath?`
builds. -/
theorem modulePath?_strict_prefix {dir : FilePath} {name : Name} {ext : String} {path : FilePath}
    (h : modulePath? dir name ext = some path) :
    splitAtSeparators dir.toString.toList <+: splitAtSeparators path.toString.toList ∧
      (splitAtSeparators dir.toString.toList).length <
        (splitAtSeparators path.toString.toList).length := by
  obtain ⟨-, more, hmore, -, hsplit⟩ := modulePath?_below h
  rw [hsplit]
  refine ⟨List.prefix_append _ _, ?_⟩
  simp only [List.length_append, List.length_map]
  have : 0 < more.length := List.length_pos_iff.mpr hmore
  omega

end Regula.Checker
