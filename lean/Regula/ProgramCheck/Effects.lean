/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Regula.Workspace
import all Regula.Workspace
meta import Lean.Elab.Command
meta import Lean.Util.Path
public import Regula.Table
public import Regula.LintMain
public import Regula.Contract
public import Regula.Decision

/-! # Where the effects of the repository's code lie

The closed form of "so thin that it only calls Lean" is stated in the specification's section "The trusted base". This
module shows it where the specification's package cannot, because a constant that calls Lake's load depends on axioms
that no profile admits, and `lake check` of that package would refuse them:

- Each row of `Regula.Load.lakeCalls` is a straight line of calls of Lake, with no test (the theorems below, each by `rfl`,
  so the statement is the body).
- `Regula.ProgramCheck.Effects` walks each constant of the repository's Lean libraries through Lean's own environment,
  at the level where bodies are held, those that the executable and the library that gives no verdict reach: a constant whose type or value mentions an effect, directly or through another
  constant of the repository, lies in a closed set of modules, and the build fails on any other. So a decision that gains
  an effect in `Regula.Reader`, `Regula.Shell` or `Regula.Load` fails the gate. The check fails too when it finds no
  effect, so an empty scan is no pass.
-/

public section

namespace Regula.ProgramCheck.Effects

open Lean

theorem parseToml_row : Regula.Load.lakeCalls.parseToml = fun input => (Lake.Toml.loadToml input).toBaseIO := by
  rfl

theorem lakeInstall_row : Regula.Load.lakeCalls.lakeInstall = fun sysroot => do
    let lake := Lake.LakeInstall.ofLean (← Lake.LeanInstall.get sysroot (collocated := true))
    return (lake.lake, lake.libDir) := by
  rfl

theorem loadWorkspace_row : Regula.Load.lakeCalls.loadWorkspace = fun sysroot wsDir => EIO.toBaseIO do
    let lakeEnv ← Regula.Load.lakeEnvironment sysroot
    let (ws?, log) ← (Lake.loadWorkspace { lakeEnv, wsDir }).captureLog
    return (ws?.map Regula.Load.rootOf, Regula.Load.messagesOf log) := by
  rfl

theorem loadRoot_row : Regula.Load.lakeCalls.loadRoot = fun sysroot wsDir => EIO.toBaseIO do
    let lakeEnv ← Regula.Load.lakeEnvironment sysroot
    let (ws?, log) ← Lake.ELogT.run? (m := BaseIO)
      (Lake.loadWorkspaceRoot { lakeEnv, wsDir, relConfigFile := "lakefile.toml" })
    return (ws?.map Regula.Load.rootOf, Regula.Load.messagesOf log) := by
  rfl

theorem libModules_row : Regula.Load.lakeCalls.libModules = fun lib => EIO.toBaseIO do
    return (← lib.getModuleArray).map fun m => (m.name, m.leanFile) := by
  rfl

theorem lakeEnvironment_eq (sysroot : String) : Regula.Load.lakeEnvironment sysroot = (do
    let lean ← Lake.LeanInstall.get sysroot (collocated := true)
    let env ← Lake.Env.compute (Lake.LakeInstall.ofLean lean) lean (← Lake.findElanInstall?)
    return { env with initLeanPath := [], initLeanSrcPath := [] }) := by
  rfl

/-- What marks an effect: Lean's types of effects, and what escapes them. -/
meta def effectRoots : List Name :=
  [``IO, ``EIO, ``BaseIO, ``ST, ``EST, ``IO.RealWorld, ``Void, `unsafeBaseIO, `unsafeIO, `unsafeEIO]

/-- The modules that may hold an effect: the one table, the calls of Lake and the executable's root. In `Regula.Effect`,
only the interpreter may. The repository's two programs, `Regula.DiagnosticsGate` and `Regula.TestListing`, each declare
their own `main`, so they are no imports of this module, and each holds its own theorem. -/
meta def effectModules : List Name :=
  [`Regula.Table, `Regula.Workspace, `Regula.LintMain]

/-- The constants of a `ConstantInfo`: its type and any value. -/
meta def mentionsOf (info : ConstantInfo) : Array Name :=
  info.type.getUsedConstants ++ (info.value?.map (·.getUsedConstants)).getD #[]

/-- Whether a constant's type mentions a root of effect. -/
meta def typeEffectful (info : ConstantInfo) : Bool :=
  info.type.getUsedConstants.any effectRoots.contains

/-- The walk: every constant of the repository's modules, and those of them that mention an effect, by a fixed point over
what they mention. -/
meta def scan (env : Environment) : List (Name × Name) := Id.run do
  let mut own : NameMap Name := {}
  for modName in env.header.moduleNames, data in env.header.moduleData do
    if modName.getRoot == `Regula then
      for n in data.constNames do
        own := own.insert n modName
  let mut effectful : NameSet := {}
  let mut changed := true
  while changed do
    changed := false
    for (n, _) in own do
      unless effectful.contains n do
        if let some info := env.find? n then
          let hit := mentionsOf info |>.any fun u =>
            effectRoots.contains u || effectful.contains u ||
              (!own.contains u && (env.find? u |>.map typeEffectful |>.getD false))
          if hit then
            effectful := effectful.insert n
            changed := true
  return effectful.toList.filterMap fun n => (own.find? n).map (n, ·)

-- The check.
run_cmd do
  initSearchPath (← findSysroot)
  let mods := #[`Regula.LintMain, `Regula.Contract, `Regula.Decision]
  let env ← importModules (mods.map ({ module := · })) {} (loadExts := false) (level := .private)
  let found := scan env
  unless found.any (·.1 == ``Regula.Effect.Prog.interpret) do
    throwError "the scan of effects found no interpreter, so it read nothing"
  let outside := found.filter fun (n, m) =>
    !effectModules.contains m && !(m == `Regula.Effect && (`Regula.Effect.Prog.interpret).isPrefixOf n)
  unless outside.isEmpty do
    throwError m!"constants outside the closed set of modules mention an effect: {outside}"

end Regula.ProgramCheck.Effects
