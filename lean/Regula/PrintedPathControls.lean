import Regula.CompilerObservation
import Regula.CompilerProbe
import Regula.Qualification.Launcher
import Lean.Elab.Command

/-! # Controls of the reads of a path that a program prints

A read that removed the whitespace at the ends of the path that a program printed could name a path
that the program did not print (https://github.com/rbeauchamp/regula/issues/465). These controls run
each read of a path that a program other than Git prints on that program's own output, in a new
temporary directory. The first acceptance step builds this module, and its build fails when a
control does not give the expected result, naming each such control. They observe each program
once, and they prove nothing: `Regula.Filesystem.Construction.checked_printedLine?` and
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
  `Lean.findSysroot` gives `tool` there. -/

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

/-- Run the controls in a new temporary directory, and fail, naming each control that does not
give the expected result. -/
def check : IO Unit := do
  let root ← IO.currentDir
  let selector := (← IO.FS.readFile (root / "lean-toolchain")).trimAscii.toString
  Regula.Filesystem.withOwnTempDir fun base => do
    let results := (← which base) ++
      [← leanPath base selector, ← selected root selector, ← sysroot base]
    let failed := results.filterMap fun (name, held) => if held then none else some name
    unless failed.isEmpty do
      throw <| IO.userError s!"controls of the reads of a printed path failed: {failed}"

run_cmd do check

end Regula.PrintedPathControls
