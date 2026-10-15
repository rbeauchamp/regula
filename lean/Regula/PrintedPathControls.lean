import Regula.CompilerObservation
import Regula.CompilerProbe
import Regula.Qualification.Launcher
import Lean.Elab.Command
import Lake
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr

/-! # Controls of the reads of a path that a program prints

A read that removed the whitespace at the ends of the path that a program printed could name a path
that the program did not print (https://github.com/rbeauchamp/regula/issues/465). These controls run
each read of a path that a program other than Git prints on that program's own output, in a new
temporary directory. The first acceptance step builds this module, and its build fails when a
control does not give the expected result, naming each such control. All but the last observe a
program once, and they prove nothing: `Regula.Filesystem.Construction.checked_printedLine?` and
`checked_printedPath?` state which text each decoder reads, and as what.

- `Regula.Qualification.Launcher.resolvedLean` (`/usr/bin/which lean`): with ` bin` alone in
  `PATH`, a relative entry whose name starts with a space, and a `lean` in ` bin` and in `bin`, it
  must give ` bin/lean` in the directory, with the space kept. With an entry whose name holds a
  newline, it must fail.
- `Regula.Qualification.Launcher.printedLeanPath` (`lake env printenv LEAN_PATH`): in a directory
  with no Lake configuration, with an inherited `LEAN_PATH` of one entry whose name ends in a space,
  the last entry that it gives must be that entry, with the space kept.
- `Regula.Toolchain.selectedLean` (`elan which lean`): for the toolchain that the package's
  `lean-toolchain` names, it must give the compiler that elaborates this module. Elan prints an
  absolute path that ends in `/bin/lean`, which no removal of whitespace at its ends changes, so
  this control observes only that the decoder accepts what Elan prints.
- `Regula.CompilerObservation.printedSysroot` (`lean --print-prefix`), which `findSysroot` runs
  when `LEAN_SYSROOT` is not set: for a copy of the toolchain's `lean` in `tool /bin`, below a
  directory whose name ends in a space, it must give that directory, with the space kept.
  `Lean.findSysroot` gives `tool` there. For the program `false`, which fails, it must fail with
  the error that `IO.Process.run` gives, as `Lean.findSysroot` does.

The root package's `lakefile.lean` holds a copy of `printedLine?`, `printedPrefix?`,
`printedSysroot` and `findSysroot`, since Lake elaborates it before Regula is built. The last
control is a check of the kernel, not an observation: the commands of the lakefile up to
`end Regula.CompilerObservation` are elaborated again below `LakefileCopy`, and the kernel must
admit that each copy equals its original by `rfl`, with no `implemented_by` or `extern` attribute
on either (`lakefileCopies`). -/

namespace Regula.PrintedPathControls

open System

/-- The controls of `Launcher.resolvedLean`, each with whether it gave the expected result. -/
def which (base : FilePath) : IO (List (String × Bool)) := do
  let place (dir : FilePath) : IO Unit := do
    IO.FS.createDirAll dir
    IO.FS.writeFile (dir / "lean") ""
    IO.Prim.setAccessRights (dir / "lean") 448
  place (base / " bin")
  place (base / "bin")
  let broken := base / "line\nbreak"
  place broken
  let spaced ← (Regula.Qualification.Launcher.resolvedLean base #[("PATH", " bin")]).toBaseIO
  let newline ← (Regula.Qualification.Launcher.resolvedLean base
    #[("PATH", broken.toString)]).toBaseIO
  return [
    ("Regula.Qualification.Launcher.resolvedLean with the entry ` bin` in PATH",
      match spaced with | .ok path => path == (base / " bin/lean").toString | .error _ => false),
    ("Regula.Qualification.Launcher.resolvedLean with an entry whose name holds a newline",
      newline matches .error _)]

/-- The control of `Launcher.printedLeanPath` in `base`, with the toolchain `selector`, and whether
it gave the expected result. -/
def leanPath (base : FilePath) (selector : String) : IO (String × Bool) := do
  let dir := base / "unconfigured"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "lean-toolchain") s!"{selector}\n"
  let entry := (base / "entry ").toString
  let read ← (Regula.Qualification.Launcher.printedLeanPath dir
    #[("LEAN_PATH", some entry)]).toBaseIO
  return ("Regula.Qualification.Launcher.printedLeanPath with an inherited entry that ends in a \
      space",
    match read with
    | .ok path => (SearchPath.parse path).getLast?.map (·.toString) == some entry
    | .error _ => false)

/-- The control of `Toolchain.selectedLean` for the toolchain `selector` from `root`, and whether
it gave the compiler that elaborates this module. -/
def selected (root : FilePath) (selector : String) : IO (String × Bool) := do
  let running ← IO.FS.realPath ((← Lean.getBuildDir) / "bin" / "lean")
  let read ← (Regula.Toolchain.selectedLean root selector).toBaseIO
  return ("Regula.Toolchain.selectedLean for the toolchain of the package",
    match read with | .ok lean => lean == running | .error _ => false)

/-- The control of `CompilerObservation.printedSysroot`, the reader that `findSysroot` runs when
`LEAN_SYSROOT` is not set, and whether it gave the expected result. The `lean` of the toolchain
that elaborates this module is copied to `tool /bin`, below a directory whose name ends in a space,
beside a link `tool /lib` to the toolchain's library. That `lean` prints the real path of
`tool ` for `--print-prefix`, and the read must keep the space. -/
def sysroot (base : FilePath) : IO (String × Bool) := do
  let installation := base / "tool "
  IO.FS.createDirAll (installation / "bin")
  let toolchain ← Lean.getBuildDir
  Regula.Filesystem.copyFile (toolchain / "bin" / "lean") (installation / "bin" / "lean") 493
  let linked ← IO.Process.output
    { cmd := "ln", args := #["-s", (toolchain / "lib").toString, (installation / "lib").toString] }
  unless linked.exitCode == 0 do
    throw <| IO.userError s!"the control could not link {installation / "lib"}: {linked.stderr}"
  let expected ← IO.FS.realPath installation
  let read ← (Regula.CompilerObservation.printedSysroot
    (installation / "bin" / "lean").toString).toBaseIO
  return ("Regula.CompilerObservation.printedSysroot of a lean below a directory whose name ends \
      in a space",
    match read with | .ok root => root == expected | .error _ => false)

/-- The control of `CompilerObservation.printedSysroot` for a program that fails, `false`, and
whether it fails with the error that `IO.Process.run` gives for that run, as `Lean.findSysroot`
does (`Lean/Util/Path.lean:180-187` of Lean v4.34.1). -/
def failedSysroot : IO (String × Bool) := do
  let read ← (Regula.CompilerObservation.printedSysroot "false").toBaseIO
  let run ← (IO.Process.run { cmd := "false", args := #["--print-prefix"] }).toBaseIO
  return ("Regula.CompilerObservation.printedSysroot of a program that fails",
    match read, run with
    | .error read, .error run => toString read == toString run
    | _, _ => false)

/-- The names that the root package's `lakefile.lean` copies from `Regula.CompilerObservation`. -/
def lakefileCopied : List Lean.Name :=
  [``Regula.CompilerObservation.printedLine?, ``Regula.CompilerObservation.printedPrefix?,
    ``Regula.CompilerObservation.printedSysroot, ``Regula.CompilerObservation.findSysroot]

/-- The namespace below which `lakefileCopies` elaborates the lakefile's copies again. -/
def copySpace : Lean.Name := `LakefileCopy

/-- The commands of the configuration file `file` from its first command, which must be
`namespace Regula.CompilerObservation`, to its command `end Regula.CompilerObservation`, read by
Lean's parser in the environment `env`, and the modules that the file's header imports. A file
without those commands, or with a syntax error before the second, is thrown. -/
def lakefileSection (env : Lean.Environment) (file : FilePath) :
    IO (Array Lean.Syntax × Array Lean.Import) := do
  let input ← IO.FS.readFile file
  let inputCtx := Lean.Parser.mkInputContext input file.toString
  let (header, parserState, messages) ← Lean.Parser.parseHeader inputCtx
  let context : Lean.Parser.ParserModuleContext := { env, options := {} }
  let mut state := parserState
  let mut messages := messages
  let mut commands := #[]
  -- Each command reads at least one character, or is the end of the input, so the loop ends
  -- before the bound.
  for _ in [0:input.utf8ByteSize + 1] do
    let (command, next, logged) := Lean.Parser.parseCommand inputCtx context state messages
    state := next
    messages := logged
    if messages.hasErrors then
      throw <| IO.userError s!"{file} has a syntax error before end Regula.CompilerObservation"
    if Lean.Parser.isTerminalCommand command then break
    if commands.isEmpty && !(command.isOfKind ``Lean.Parser.Command.namespace &&
        command[1].getId == `Regula.CompilerObservation) then
      throw <| IO.userError
        s!"the first command of {file} is not namespace Regula.CompilerObservation"
    commands := commands.push command
    if command.isOfKind ``Lean.Parser.Command.end &&
        command[1][0].getId == `Regula.CompilerObservation then
      return (commands, Lean.Elab.headerToImports header)
  throw <| IO.userError s!"{file} has no command end Regula.CompilerObservation"

/-- Why a constant below `space` that `names` use in their types and values, transitively, or one
of `names` itself, has an `implemented_by` or `extern` attribute in `env`, so that its compiled code
need not compute its value, or `none` when none has. -/
def replacedImplementation (env : Lean.Environment) (space : Lean.Name) (names : List Lean.Name) :
    Option String :=
  Id.run do
    let mut pending := names
    let mut queued : Lean.NameSet := names.foldl (·.insert ·) {}
    -- A name is queued once, and each name taken that is not the last is one of a few definitions
    -- below `space`, so the bound fails closed only on far larger definitions.
    for _ in [0:1000] do
      let name :: rest := pending | return none
      pending := rest
      let some constant := env.find? name | return some s!"{name} is not declared"
      if (Lean.Compiler.getImplementedBy? env name).isSome || Lean.isExtern env name then
        return some s!"{name} has an implemented_by or extern attribute"
      let used := constant.type.getUsedConstants ++
        ((constant.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
      for next in used do
        if space.isPrefixOf next && !queued.contains next then
          queued := queued.insert next
          pending := next :: pending
    return some s!"the definitions below {space} use more constants than the bound"

open Lean Elab Command in
/-- Why a copy below `copySpace` of one of `names` in the current environment is not the same
function as the original that the module `Regula.CompilerObservation` declares, or `none` when each
is. The kernel must admit that each copy equals its original by `rfl`, so they are equal as
functions. Neither the copies nor the originals, nor a definition below their namespaces that they
use, may have an `implemented_by` or `extern` attribute (`replacedImplementation`), so the compiled
code of each computes the value that the kernel compared. -/
def copyDifference (names : List Lean.Name) : CommandElabM (Option String) := do
  let env ← getEnv
  let space := `Regula.CompilerObservation
  for name in names do
    let declaring := (env.getModuleIdxFor? name).bind fun i => env.allImportedModuleNames[i.toNat]?
    unless declaring == some space do
      return some s!"{name} is not declared by {space}"
  let copies := names.map (copySpace ++ ·)
  if let some reason := replacedImplementation env copySpace copies then return some reason
  if let some reason := replacedImplementation env space names then return some reason
  for name in names do
    let copied := copySpace ++ name
    let some constant := env.find? copied | return some s!"lakefile.lean declares no {name}"
    unless constant.levelParams.isEmpty do return some s!"{name} has universe parameters"
    let (type, value) ← liftTermElabM do
      return (← Meta.mkEq (mkConst copied) (mkConst name), ← Meta.mkEqRefl (mkConst name))
    let declaration :=
      .thmDecl { name := copySpace ++ `same ++ name, levelParams := [], type, value }
    let depth := (maxRecDepth.get (← getOptions)).toUSize
    if let .error error := env.addDeclCore 0 depth declaration none then
      return some s!"the kernel does not admit that the copy of {name} is the same: \
        {← (error.toMessageData (← getOptions)).toString}"
  return none

open Lean Elab Command in
/-- The control of the copies of `lakefileCopied` in the root package's `lakefile.lean` at `root`,
and whether each is the same constant as its original (`copyDifference`), with the reason when one
is not. The commands of the lakefile up to `end Regula.CompilerObservation` (`lakefileSection`) are
elaborated again below `copySpace` in this module's environment, which must import each module that
the lakefile imports, and the environment is then restored. Lake elaborates them in the environment
of those imports alone: the modules that this module imports beyond them are taken to change no
elaboration of these commands. -/
def lakefileCopies (root : FilePath) : CommandElabM (String × Bool) := do
  let name := "the copies of Regula.CompilerObservation in lakefile.lean"
  let env ← getEnv
  let scopes := (← get).scopes
  let difference ← try
      let (commands, imports) ← lakefileSection env (root / "lakefile.lean")
      if let some missing := imports.find? fun i => (env.getModuleIdx? i.module).isNone then
        pure (some s!"this module does not import {missing.module}, which lakefile.lean imports")
      else
        withoutModifyingEnv do
          elabCommand (← `(namespace $(mkIdent copySpace)))
          for command in commands do elabCommand command
          elabCommand (← `(end $(mkIdent copySpace)))
          copyDifference lakefileCopied
    catch error => pure (some (← error.toMessageData.toString))
    finally modify fun state => { state with scopes }
  return (if let some reason := difference then s!"{name}: {reason}" else name, difference.isNone)

/-- Run the controls in a new temporary directory, with the result of `lakefileCopies`, `copies`,
and fail, naming each control that does not give the expected result. -/
def check (copies : String × Bool) : IO Unit := do
  let root ← IO.currentDir
  let selector := (← IO.FS.readFile (root / "lean-toolchain")).trimAscii.toString
  Regula.Filesystem.withOwnTempDir fun base => do
    let results := (← which base) ++
      [← leanPath base selector, ← selected root selector, ← sysroot base, ← failedSysroot,
        copies]
    let failed := results.filterMap fun (name, held) => if held then none else some name
    unless failed.isEmpty do
      throw <| IO.userError s!"controls of the reads of a printed path failed: {failed}"

end Regula.PrintedPathControls

-- At the root, so that the lakefile's commands are elaborated again in no namespace and with no
-- open declarations of this module, as Lake elaborates them.
run_cmd do
  let copies ← Regula.PrintedPathControls.lakefileCopies (← IO.currentDir)
  Regula.PrintedPathControls.check copies
