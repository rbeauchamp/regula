import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.Path

/-! # The check that no declaration of a package refers to Lean's directory readers

Lean v4.34.1's `System.FilePath.readDir` calls `readdir` until it returns null and returns what it
collected, so it cannot tell the end of a directory from a failed read (issue 408), and
`System.FilePath.walkDir` lists through it. Each program of Regula lists a directory through
`Regula.Filesystem.Construction.listNames`, `listDirectory` or `walkDirectory`, which refuse a
failed read. `readerReferences` reports each declaration that refers to one of the two readers, in
its type or its value.

`lake exe qualify observers` runs it over every module of the root package's libraries and over
the root modules of its executables (`Regula.Qualification.Observers`). The root module of each
executable of the `markdown` and `website` packages runs `checkPackage` at its end, which fails the
build of that module on a reference: it reads that module and every module of its own package that
the module imports.

## What it does not cover

The check reads the constants of each module, not its source text. It does not follow a call into
Lean's or Lake's library, so `IO.FS.removeDirAll` and Lake's module globs still read directories
with `readDir`. A module of the `markdown` or `website` package that no executable imports is not
read, nor is the `audit` package, which holds the standard's example library and no program. No
inventory records the executables of the `markdown` and `website` packages that run
`checkPackage`. -/

namespace Regula.Checker

open Lean System

/-- The facts of a compiled module that its census reads: its exported part, whose header gives
its imports and `isModule`, and its constants in every part `importModules` reads at its default
`OLeanLevel.private`, each name once in the form of the last part that has it. A file without a
`module` header is one part. A `module` file's exported part holds only its exported constants,
some of its theorems weakened to axioms, so its server and private parts are read too.

Assumes:
- Lean v4.34.1 writes a `module` file as an exported, a server and a private part, and any other
  file as one part (`writeModule`, `src/lean/Lean/Environment.lean:1901-1909`), named by
  `OLeanLevel.adjustFileName` (`:1820-1823`). The parts must be read together
  (`readModuleDataParts`, `:1765-1790`), and the private part holds every constant of the module
  (`mkModuleData`, `:1868-1872`), a theorem among them as a theorem (`:2249-2251`). -/
def readModuleCensus (olean : FilePath) : IO (ModuleData × Array ConstantInfo) := do
  let (main, _) ← readModuleData olean
  if !main.isModule then return (main, main.constants)
  let parts ← readModuleDataParts #[olean, OLeanLevel.server.adjustFileName olean,
    OLeanLevel.private.adjustFileName olean]
  let mut seen : NameSet := {}
  let mut constants := #[]
  for (data, _) in parts.reverse do
    for constant in data.constants do
      unless seen.contains constant.name do
        seen := seen.insert constant.name
        constants := constants.push constant
  return (main, constants)

end Regula.Checker

namespace Regula.ReaderCheck

open Lean System

/-- The directory readers of Lean's library that cannot tell the end of a directory from a failed
read, which no declaration of a package of Regula refers to. -/
def directoryReaders : List Name := [``System.FilePath.readDir, ``System.FilePath.walkDir]

/-- Each declaration of `constants` that refers to a directory reader, in its type or its value,
with those readers (`ConstantInfo.getUsedConstantsAsSet`, which also reads the value of a theorem
and of an opaque constant). -/
def readerReferences (constants : List ConstantInfo) : List (Name × List Name) :=
  constants.filterMap fun constant =>
    let readers := directoryReaders.filter (constant.getUsedConstantsAsSet.contains ·)
    if readers.isEmpty then none else some (constant.name, readers)

/-- No declaration is reported exactly when no declaration of `constants` refers to a directory
reader. -/
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
reference to each directory reader, and no declaration without one. -/
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

/-- The directory of the package of `file`, an absolute path: its nearest ancestor that holds a
Lake configuration file, `lakefile.toml` or `lakefile.lean`. -/
def packageDirectory (file : FilePath) : IO FilePath := do
  let mut directory := file
  for _ in file.components do
    let some parent := directory.parent | break
    directory := parent
    for configuration in ["lakefile.toml", "lakefile.lean"] do
      if ← (directory / configuration).pathExists then return directory
  throw <| IO.userError s!"no Lake configuration file is above {file}"

/-- The compiled file of each module that `env` imports whose real path is in the directory
`package` and not in its `.lake/packages`: the modules of that package, found as Lean finds each
imported module (`findOLean`). -/
def packageModules (env : Environment) (package : FilePath) : IO (Array FilePath) := do
  let inside (directory olean : FilePath) := directory.components.isPrefixOf olean.components
  env.header.moduleNames.filterMapM fun module => do
    let olean ← IO.FS.realPath (← findOLean module)
    return if inside package olean && !inside (package / ".lake" / "packages") olean then
      some olean else none

/-- Refuse, after the reader check's controls (`controlFailure`), each declaration of this module
and of each module of its own package that it imports which refers to a directory reader. The
root module of each executable of the `markdown` and `website` packages runs it at its end. -/
def checkPackage : Elab.Command.CommandElabM Unit := do
  if let some failure := controlFailure then throwError failure
  let env ← getEnv
  let package ← packageDirectory (← IO.FS.realPath (← getFileName))
  let current := env.constants.foldStage2 (fun constants _ constant => constant :: constants) []
  let mut references := readerReferences current
  for olean in ← packageModules env package do
    let constants := (← Regula.Checker.readModuleCensus olean).2
    references := references ++ readerReferences constants.toList
  unless references.isEmpty do throwError (refusal references)

end Regula.ReaderCheck
