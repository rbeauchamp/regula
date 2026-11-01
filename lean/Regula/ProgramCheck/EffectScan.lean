/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Lean.Environment
public import Regula.Reach

/-! # Where a constant of the repository can reach an effect

The decision of the check in `Regula.ProgramCheck.Effects`, as pure functions, so that
`specification/RegulaSpecification/Proofs/EffectScan.lean` proves what it decides: `scan` gives exactly the constants of the
repository's modules that mention an effect, directly or through another constant of the repository
(`mem_scan_iff`), and `judge` passes exactly when the interpreter is among them and each of them lies in the closed set of
modules (`judge_ok_iff`). `graphOf` reads the environment through Lean's own `header` and `find?`; that those report what the
`.olean` files hold is Lean's, as the specification's trusted base lists. `Expr.getUsedConstants` is trusted to list what an
expression mentions.
-/

public section

namespace Regula.ProgramCheck.EffectScan

open Lean

/-- What marks an effect: Lean's types of effects, and what escapes them. -/
def effectRoots : List Name :=
  [``IO, ``EIO, ``BaseIO, ``ST, ``EST, ``IO.RealWorld, ``Void, `unsafeBaseIO, `unsafeIO, `unsafeEIO]

/-- The modules that may hold an effect: the one table, the calls of Lake and the executable's root. In `Regula.Effect`,
only the interpreter may. The repository's two programs, `Regula.DiagnosticsGate` and `Regula.TestListing`, each declare
their own `main`, so they are no imports of the check, and each holds its own theorem. -/
def effectModules : List Name :=
  [`Regula.Table, `Regula.Workspace, `Regula.LintMain]

/-- What the scan reads of the repository: each of its constants with its module, what a constant mentions, and whether a
constant outside the repository has a type that mentions an effect. -/
structure Graph where
  /-- Each constant of the repository's modules, with its module. -/
  own : List (Name × Name)
  /-- What a constant mentions. -/
  mentions : Name → List Name
  /-- Whether a constant outside the repository has a type that mentions an effect. -/
  foreign : Name → Bool

/-- The names of the constants of the repository. -/
def Graph.ownNames (g : Graph) : Std.HashSet Name :=
  Std.HashSet.ofList (g.own.map (·.1))

/-- A name that marks an effect by itself: one of `effectRoots`, or a constant outside the repository whose type mentions one. -/
def Graph.hit (g : Graph) (u : Name) : Bool :=
  effectRoots.contains u || (!g.ownNames.contains u && g.foreign u)

/-- Which constants of the repository mention each name. -/
def Graph.callers (g : Graph) : Std.HashMap Name (List Name) :=
  g.own.foldl (init := {}) fun m x =>
    (g.mentions x.1).foldl (init := m) fun m u => m.insert u (x.1 :: m.getD u [])

/-- The constants of the repository that mention a name that marks an effect. -/
def Graph.seeds (g : Graph) : List Name :=
  (g.own.map (·.1)).filter fun n => (g.mentions n).any g.hit

/-- The constants of the repository that mention an effect, directly or through another constant of the repository: a search
back from `seeds` through `callers`. -/
def scan (g : Graph) : List (Name × Name) :=
  let callers := g.callers
  let weight := (callers.keys.map fun n => (callers.getD n []).length).sum
  let found := Regula.Closed.reach (callers.getD · []) weight g.seeds
  g.own.filter fun x => found.contains x.1

/-- Whether a constant may mention an effect, by the closed set of modules. -/
def allowed (x : Name × Name) : Bool :=
  effectModules.contains x.2 || (x.2 == `Regula.Effect && (`Regula.Effect.Prog.interpret).isPrefixOf x.1)

/-- What the check says of what the scan found: it fails when it finds no interpreter, so an empty scan is no pass, and on any
constant outside the closed set of modules. -/
def judge (found : List (Name × Name)) : Except String Unit :=
  if !found.any (·.1 == `Regula.Effect.Prog.interpret) then
    .error "the scan of effects found no interpreter, so it read nothing"
  else
    match found.filter (!allowed ·) with
    | [] => .ok ()
    | outside => .error s!"constants outside the closed set of modules mention an effect: {outside}"

/-- What a constant mentions: what its type and any value mention. -/
def mentionsOf (info : ConstantInfo) : List Name :=
  (info.type.getUsedConstants ++ (info.value?.map (·.getUsedConstants)).getD #[]).toList

/-- What the scan reads of an environment: each constant that a module of the repository states, by the module's own data in
the header, and what `find?` gives for a name. -/
def graphOf (env : Environment) : Graph where
  own := ((env.header.moduleNames.zip env.header.moduleData).toList.filter (·.1.getRoot == `Regula)).flatMap fun x =>
    x.2.constNames.toList.map (·, x.1)
  mentions := fun n => ((env.find? n).map mentionsOf).getD []
  foreign := fun u => ((env.find? u).map fun info => info.type.getUsedConstants.any effectRoots.contains).getD false

end Regula.ProgramCheck.EffectScan
