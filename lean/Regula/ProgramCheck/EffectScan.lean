module

public import Lean.Environment
public import Regula.Reach

public section

namespace Regula.ProgramCheck.EffectScan

open Lean

def effectRoots : List Name :=
  [``IO, ``EIO, ``BaseIO, ``ST, ``EST, ``IO.RealWorld, ``Void, `unsafeBaseIO, `unsafeIO, `unsafeEIO]

def effectModules : List Name :=
  [`Regula.Table, `Regula.Workspace, `Regula.LintMain]

structure Graph where
  own : List (Name × Name)
  mentions : Name → List Name
  foreign : Name → Bool

def Graph.ownNames (g : Graph) : Std.HashSet Name :=
  Std.HashSet.ofList (g.own.map (·.1))

def Graph.hit (g : Graph) (u : Name) : Bool :=
  effectRoots.contains u || (!g.ownNames.contains u && g.foreign u)

def Graph.callers (g : Graph) : Std.HashMap Name (List Name) :=
  g.own.foldl (init := {}) fun m x =>
    (g.mentions x.1).foldl (init := m) fun m u => m.insert u (x.1 :: m.getD u [])

def Graph.seeds (g : Graph) : List Name :=
  (g.own.map (·.1)).filter fun n => (g.mentions n).any g.hit

def scan (g : Graph) : List (Name × Name) :=
  let callers := g.callers
  let weight := (callers.keys.map fun n => (callers.getD n []).length).sum
  let found := Regula.Closed.reach (callers.getD · []) weight g.seeds
  g.own.filter fun x => found.contains x.1

def allowed (x : Name × Name) : Bool :=
  effectModules.contains x.2 || (x.2 == `Regula.Effect && (`Regula.Effect.Prog.interpret).isPrefixOf x.1)

def judge (found : List (Name × Name)) : Except String Unit :=
  if !found.any (·.1 == `Regula.Effect.Prog.interpret) then
    .error "the scan of effects found no interpreter, so it read nothing"
  else
    match found.filter (!allowed ·) with
    | [] => .ok ()
    | outside => .error s!"constants outside the closed set of modules mention an effect: {outside}"

def mentionsOf (info : ConstantInfo) : List Name :=
  (info.type.getUsedConstants ++ (info.value?.map (·.getUsedConstants)).getD #[]).toList

def graphOf (env : Environment) : Graph where
  own := ((env.header.moduleNames.zip env.header.moduleData).toList.filter (·.1.getRoot == `Regula)).flatMap fun x =>
    x.2.constNames.toList.map (·, x.1)
  mentions := fun n => ((env.find? n).map mentionsOf).getD []
  foreign := fun u => ((env.find? u).map fun info => info.type.getUsedConstants.any effectRoots.contains).getD false

end Regula.ProgramCheck.EffectScan
