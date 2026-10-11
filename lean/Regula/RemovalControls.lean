import Regula.Removal
import Lean.Elab.Command

/-! # Controls of the removal decision and its reach check

Planted cases that the operations of `Regula.Removal` must refuse, each a control of one way a
removal could escape the decision. The first acceptance step builds this module, and its build
fails when a control does not give the expected result. No executable imports this module, so no
planted declaration below is linked into a program, and its planted initializer never runs.

- A symbolic link at a component above the last one: `removeOwn` refuses `linked/out`, where
  `linked` is a link to a directory that has `out`, and removes nothing there. It removes the same
  directory at its own place. This control is about the file system, a trusted boundary: it
  observes the operation on the toolchain's file system calls, and it proves nothing.
- A name that extends the name of `removeDecided`: a declaration with that name that calls a
  removal primitive is a raw removal (`rawRemovalsFrom`), so only `removeDecided` and the variants
  that the compiler made of it are admitted (`decidedVariants`).
- A removal in an initializer: `rawRemovals` starts at each initializer that an executable runs
  (`initializers`), so it finds a removal that no call from `main` reaches.
- A declaration of another name bound to a C function of the runtime that removes: it is a raw
  removal (`removalSymbols`).
- An absent output below a linked ancestor: `ownPath` refuses it before anything is made. -/

namespace Regula.RemovalControls

open Lean System

/-- The planted removal of the control of initializers. It removes a directory only when the
variable `REGULA_REMOVAL_CONTROL_PLANTED` is set, and no program runs it. -/
initialize plantedInitializer : Unit ← do
  if (← IO.getEnv "REGULA_REMOVAL_CONTROL_PLANTED").isSome then
    IO.FS.removeDirAll "/regula-removal-control-planted"

-- A symbolic link above the last component: refused, and nothing is removed through the link.
run_cmd do
  let base ← IO.FS.realPath (← IO.FS.createTempDir)
  try
    IO.FS.createDirAll (base / "target" / "out")
    IO.FS.writeFile (base / "target" / "out" / "keep") "keep"
    let linked ← IO.Process.output
      { cmd := "ln", args := #["-s", (base / "target").toString, (base / "linked").toString] }
    unless linked.exitCode == 0 do throwError "ln -s failed: {linked.stderr}"
    let refused ← (Regula.Removal.removeOwn .directory (base / "linked" / "out")).toBaseIO
    unless refused matches .error _ do throwError "removeOwn removed through a linked component"
    unless (← (Regula.Removal.ownPath (base / "linked" / "new")).toBaseIO) matches .error _ do
      throwError "ownPath accepted an absent path below a linked component"
    unless (← Regula.Removal.ownPath (base / "target" / "new")) == base / "target" / "new" do
      throwError "ownPath changed a path below its own place"
    unless ← (base / "target" / "out" / "keep").pathExists do
      throwError "removeOwn removed an entry below a linked component"
    Regula.Removal.removeOwn .directory (base / "target" / "out")
    if ← (base / "target" / "out").pathExists then
      throwError "removeOwn kept a directory at its own place"
  finally
    IO.FS.removeDirAll base

-- A declaration whose name extends the name of `removeDecided` is not admitted.
run_cmd do
  let planted := Regula.Removal.decidedName ++ `unchecked
  Elab.Command.liftTermElabM do
    let type := mkForall `path .default (mkConst ``FilePath) (mkApp (mkConst ``IO) (mkConst ``Unit))
    let value := mkLambda `path .default (mkConst ``FilePath)
      (mkApp (mkConst ``IO.FS.removeDirAll) (mkBVar 0))
    addAndCompile (.defnDecl { name := planted, levelParams := [], type, value
                               hints := .opaque, safety := .safe })
  let (raw, unknown) := Regula.Removal.rawRemovalsFrom (← getEnv) #[planted]
  unless raw == #[(planted, ``IO.FS.removeDirAll)] && unknown.isEmpty do
    throwError "the planted declaration {planted} is not a raw removal: {raw}, unknown {unknown}"
  unless Regula.Removal.decidedVariants (← getEnv) Regula.Removal.decidedName do
    throwError "removeDecided itself is not admitted"

/-- The planted binding of the control of `extern` declarations: a declaration of another name
bound to the C function of `IO.FS.removeFile`. No program calls it. -/
@[extern "lean_io_remove_file"]
opaque plantedRemoval (path : @& FilePath) : IO Unit

/-- A caller of `plantedRemoval`, the root of its control. -/
def callsPlantedRemoval (path : FilePath) : IO Unit := plantedRemoval path

-- A declaration bound to a removal symbol of the runtime is a raw removal, whatever its name.
run_cmd do
  let (raw, unknown) := Regula.Removal.rawRemovalsFrom (← getEnv) #[``callsPlantedRemoval]
  unless raw == #[(``plantedRemoval, `lean_io_remove_file)] && unknown.isEmpty do
    throwError "the planted binding is not a raw removal: {raw}, unknown {unknown}"

-- The planted initializer is found, and no other initializer of this module's imports removes.
run_cmd do
  let env ← getEnv
  let (raw, unknown) := Regula.Removal.rawRemovalsFrom env (Regula.Removal.initializers env)
  unless unknown.isEmpty do throwError "initializers with unknown compiled code: {unknown}"
  unless raw.size == 1 && raw.all fun (caller, primitive) =>
      primitive == ``IO.FS.removeDirAll && (env.getModuleIdxFor? caller).isNone do
    throwError "the planted initializer is not the only raw removal: {raw}"

end Regula.RemovalControls
