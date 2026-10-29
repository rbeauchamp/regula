import Lean.Util.FoldConsts

/-! # The reference check of Lean's directory readers

Lean v4.35.0's `System.FilePath.readDir` calls `readdir` until it returns null and returns what it
collected, so it cannot tell the end of a directory from a failed read (issue 408), and
`System.FilePath.walkDir` lists through it. Each program of Regula lists a directory through
`Regula.Filesystem.Construction.listNames`, `listDirectory` or `walkDirectory`, which refuse a
failed read. `readerReferences` reports each declaration that refers to one of the two readers, in
its type or its value. `lake exe qualify readers` runs it over every module of each package of the
repository (`Regula.Qualification.Readers`).

It reads the constants of a compiled module, not its source text, and it does not follow a call
into Lean's or Lake's library: `IO.FS.removeDirAll` and Lake's module globs still read directories
with `readDir`. -/

namespace Regula.ReaderCheck

open Lean

/-- The directory readers of Lean's library that cannot tell the end of a directory from a failed
read, which no declaration of a package of Regula refers to. -/
def directoryReaders : List Name := [``System.FilePath.readDir, ``System.FilePath.walkDir]

/-- Each declaration of `constants` that refers to a directory reader, in its type or its value,
with those readers, as `ConstantInfo.getUsedConstantsAsSet` collects the constants of a
declaration.

Assumes: Lean v4.35.0 runs `Expr.foldConsts` through its `implemented_by` replacement
`FoldConstsImpl.foldUnsafe` (`src/lean/Lean/Util/FoldConsts.lean:24-47`), which applies its
function to the name of each `.const` subterm and to the structure of each `.proj` subterm, each
shared subterm visited once. Its logical body returns the initial value (`:51-53`), so no theorem
about it reaches that traversal. `ConstantInfo.getUsedConstantsAsSet` (`:66-74`) collects them
over the type and the value, the value of a theorem and of an opaque constant included. -/
def readerReferences (constants : List ConstantInfo) : List (Name × List Name) :=
  constants.filterMap fun constant =>
    let readers := directoryReaders.filter (constant.getUsedConstantsAsSet.contains ·)
    if readers.isEmpty then none else some (constant.name, readers)

/-- No declaration is reported exactly when the collector's set of no declaration of `constants`
contains a directory reader. It proves the filter over the collector's output, not that the
collector's native traversal finds each constant of an expression (the `Assumes:` entry of
`readerReferences`). -/
theorem readerReferences_eq_nil_iff (constants : List ConstantInfo) :
    readerReferences constants = [] ↔
      ∀ constant ∈ constants, ∀ reader ∈ directoryReaders,
        constant.getUsedConstantsAsSet.contains reader = false := by
  simp [readerReferences, List.filterMap_eq_nil_iff, List.filter_eq_nil_iff]

/-- A declaration named `name` whose value calls `reader`, or calls nothing when `reader` is `none`:
the planted declaration of the reader check's positive control, and the plain one of its negative
control. -/
def readerProbe (name : Name) (reader : Option Name) : ConstantInfo :=
  let value := match reader with
    | some reader => .app (.const reader []) (.const ``Unit.unit [])
    | none => .const ``Unit.unit []
  .defnInfo
    { name, levelParams := [], type := .const ``Unit [], value, hints := .opaque, safety := .safe }

/-- Why the reader check's controls fail, if they do: `readerReferences` must report a planted
reference to each directory reader, and no declaration without one. The compiled check runs the
native traversal, so this control exercises it on these expressions. -/
def controlFailure : Option String :=
  match directoryReaders.find? fun reader =>
      readerReferences [readerProbe `planted (some reader)] != [(`planted, [reader])] with
  | some reader => some s!"the reader check misses a planted reference to {reader}"
  | none =>
    if (readerReferences [readerProbe `plain none]).isEmpty then none
    else some "the reader check reports a declaration with no reference"

/-- The refusal of the declarations of `references`. -/
def refusal (references : List (Name × List Name)) : String :=
  s!"these declarations refer to Lean's readDir or walkDir, which cannot tell the end of a \
    directory from a failed read: {references}. List a directory through \
    Regula.Filesystem.Construction.listNames, listDirectory or walkDirectory"

end Regula.ReaderCheck
