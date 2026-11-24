module

public import Lean.Data.Name
public import Regula.LanguageSet

public section

namespace Regula.Language

open Lean (Name Syntax)

def strLt (a b : String) : Bool :=
  decide (a < b)

def kindsArray : Array Name := kinds.toArray

def leafKindsArray : Array Name := leafKinds.toArray

def atomsArray : Array String := atoms.toArray

def isLeafKind (k : Name) : Bool :=
  leafKindsArray.binSearchContains k Name.lt

def isKind (k : Name) : Bool :=
  kindsArray.binSearchContains k Name.lt

def isAtom (v : String) : Bool :=
  atomsArray.binSearchContains v strLt

mutual
  def positionsGo (acc : List Syntax) : Syntax → List Syntax
    | .node i k as =>
      let acc := .node i k as :: acc
      if isLeafKind k then acc else positionsOfArrayGo acc as
    | s => s :: acc
  def positionsOfArrayGo (acc : List Syntax) : Array Syntax → List Syntax
    | ⟨l⟩ => positionsOfListGo acc l
  def positionsOfListGo (acc : List Syntax) : List Syntax → List Syntax
    | [] => acc
    | x :: xs => positionsOfListGo (positionsGo acc x) xs
end

def positions (t : Syntax) : List Syntax :=
  (positionsGo [] t).reverse

def reservedName : Name → Bool
  | .anonymous => false
  | .str .anonymous "_root_" => false
  | .str p s => s.front == '_' || s == "autoParam" || reservedName p
  | .num p _ => reservedName p

def targets (as : Array Syntax) : List Name :=
  as.toList.flatMap fun
    | .ident _ _ n _ => [n]
    | .node _ `null xs => xs.toList.filterMap fun
      | .ident _ _ n _ => some n
      | _ => none
    | _ => []

def canActivate (N n : Name) : Bool :=
  let target := n.components.dropWhile (· == `_root_)
  (List.range target.length).any fun i => (target.take (i + 1)).isSuffixOf N.components

def identIn (allowed : List Name) (as : Array Syntax) (i : Nat) : Bool :=
  match as[i]? with
  | some (.ident _ _ n _) => allowed.contains n
  | _ => false

def noArgument : Option Syntax → Bool
  | some (.node _ `null xs) => xs.isEmpty
  | _ => false

def argumentsAdmitted (scopedParsers : List Name) (k : Name) (as : Array Syntax) : Bool :=
  if k == `Lean.Parser.Attr.simple then identIn simpleAttributes as 0 && noArgument as[1]?
  else if k == `Lean.Parser.Command.set_option then identIn options as 1
  else if k == `Lean.Parser.Tactic.posConfigItem then identIn configItems as 1
  else if k == `Lean.Parser.Command.derivingClass then identIn derivingClasses as 1
  else if k == `Lean.Parser.Command.namespace || k == `Lean.Parser.Command.openSimple then
    (targets as).all fun n => scopedParsers.all fun N => !canActivate N n
  else true

def positionAdmitted (scopedParsers : List Name) : Syntax → Bool
  | .missing => false
  | .atom _ v => isAtom v
  | .ident _ _ n _ => !reservedName n
  | .node _ k as =>
    (isKind k || isLeafKind k) && argumentsAdmitted scopedParsers k as

def offenders (scopedParsers : List Name) (t : Syntax) : List Syntax :=
  (positions t).filter (!positionAdmitted scopedParsers ·)

def isNodeOf (k : Name) : Syntax → Bool
  | .node _ k' _ => k' == k
  | _ => false

def moduleFile (header : Syntax) : Bool :=
  (positions header).any (isNodeOf `Lean.Parser.Module.moduleTk)

def readToEnd (commands : List Syntax) : Bool :=
  match commands.getLast? with
  | some s => isNodeOf `Lean.Parser.Command.eoi s
  | none => false

def FileRead.offenders (f : FileRead) : List Syntax :=
  (f.header :: f.commands).flatMap (Regula.Language.offenders f.scopedParsers)

def FileRead.admitted (f : FileRead) : Bool :=
  f.parsed && moduleFile f.header && readToEnd f.commands && f.offenders.isEmpty

def configKeyAdmitted (k : Name) : Bool :=
  configKeys.contains k || options.any (k == `leanOptions ++ ·)

def closedNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

def closedComponent (s : String) : Bool :=
  !s.isEmpty && s.toList.all closedNameChar

def closedModuleName : Name → Bool
  | .anonymous => false
  | .num _ _ => false
  | .str .anonymous s => closedComponent s
  | .str (.str q t) s => closedModuleName (.str q t) && closedComponent s
  | .str (.num _ _) _ => false

def treeRelative (base path : List String) : Option (List String) :=
  if base.isPrefixOf path then
    let rel := path.drop base.length
    if rel.all (fun c => !c.isEmpty && c.front != '.') then some rel else none
  else none

def configKeysClosed (keys : List Name) : Bool :=
  keys.all fun k => k.getRoot == `require || configKeyAdmitted k

def configIsClosed (toolchainFile : Option String) (leanConfig : Bool) (openPaths : List String)
    (configKeys : List Name) : Bool :=
  toolchainFile == some leanToolchain && !leanConfig && openPaths.isEmpty &&
    configKeysClosed configKeys

def covers (roots reached : List Name) (files : List FileRead) : Bool :=
  !roots.isEmpty && roots.all reached.contains && reached.all closedModuleName &&
    reached.all fun m => files.any (·.module == m)

namespace Reading

variable (r : Reading)

def configClosed : Bool :=
  configIsClosed r.toolchainFile r.leanConfig r.openPaths r.configKeys

def readInFull : Bool :=
  r.unread.isEmpty

def requiresDependency : Bool :=
  r.configKeys.any (·.getRoot == `require)

def mathlibReached : Bool :=
  r.reached.any (·.getRoot == `Mathlib)

def covered : Bool :=
  covers r.roots r.reached r.files

def filesAdmitted : Bool :=
  r.files.all (·.admitted)

end Reading

def decision (r : Reading) : Outcome :=
  if !r.configClosed then .refused
  else if !r.readInFull then .incomplete
  else if r.requiresDependency then .proofOnly
  else if r.mathlibReached then .proofOnly
  else if !r.covered then .incomplete
  else if !r.filesAdmitted then .refused
  else .admitted

structure ClosedConfig where
  keys : List Name
  admitted : keys.all configKeyAdmitted = true
  noRequire : keys.any (·.getRoot == `require) = false

namespace ClosedConfig

def empty : ClosedConfig := ⟨[], rfl, rfl⟩

theorem keys_closed (cfg : ClosedConfig) : configKeysClosed cfg.keys = true := by
  simp only [configKeysClosed, List.all_eq_true, Bool.or_eq_true]
  intro k hk
  exact .inr (List.all_eq_true.mp cfg.admitted k hk)

end ClosedConfig

inductive Stage where
  | configRefused (toolchainFile : Option String) (leanConfig : Bool) (configKeys : List Name)
      (openPaths : List String) (unread : List (Name × String))
      (h : configIsClosed toolchainFile leanConfig openPaths configKeys = false)
  | unread (cfg : ClosedConfig) (roots reached : List Name) (unread : List (Name × String))
      (hne : unread.isEmpty = false)
  | dependency (configKeys : List Name)
      (hclosed : configKeysClosed configKeys = true)
      (hreq : configKeys.any (·.getRoot == `require) = true)
  | mathlib (cfg : ClosedConfig) (roots reached : List Name)
      (hmathlib : reached.any (·.getRoot == `Mathlib) = true)
  | uncovered (cfg : ClosedConfig) (roots reached : List Name) (files : List FileRead)
      (hnomath : reached.any (·.getRoot == `Mathlib) = false)
      (huncov : covers roots reached files = false)
  | filesRefused (cfg : ClosedConfig) (roots reached : List Name) (files : List FileRead)
      (hnomath : reached.any (·.getRoot == `Mathlib) = false)
      (hcov : covers roots reached files = true)
      (hbad : files.all (·.admitted) = false)
  | admitted (cfg : ClosedConfig) (roots reached : List Name) (files : List FileRead)
      (hnomath : reached.any (·.getRoot == `Mathlib) = false)
      (hcov : covers roots reached files = true)
      (hadm : files.all (·.admitted) = true)

namespace Stage

def toReading : Stage → Reading
  | .configRefused toolchainFile leanConfig configKeys openPaths errs _ =>
    { toolchainFile, leanConfig, configKeys, openPaths, roots := [], reached := [], files := [], unread := errs }
  | .unread cfg roots reached errs _ =>
    { toolchainFile := some leanToolchain, leanConfig := false, configKeys := cfg.keys,
      openPaths := [], roots, reached, files := [], unread := errs }
  | .dependency configKeys _ _ =>
    { toolchainFile := some leanToolchain, leanConfig := false, configKeys,
      openPaths := [], roots := [], reached := [], files := [], unread := [] }
  | .mathlib cfg roots reached _ =>
    { toolchainFile := some leanToolchain, leanConfig := false, configKeys := cfg.keys,
      openPaths := [], roots, reached, files := [], unread := [] }
  | .uncovered cfg roots reached files _ _
  | .filesRefused cfg roots reached files _ _ _
  | .admitted cfg roots reached files _ _ _ =>
    { toolchainFile := some leanToolchain, leanConfig := false, configKeys := cfg.keys,
      openPaths := [], roots, reached, files, unread := [] }

def outcome : Stage → Outcome
  | .configRefused .. | .filesRefused .. => .refused
  | .unread .. | .uncovered .. => .incomplete
  | .dependency .. | .mathlib .. => .proofOnly
  | .admitted .. => .admitted

theorem decision_toReading (s : Stage) : decision s.toReading = s.outcome := by
  cases s with
  | configRefused _ _ _ _ _ h =>
    simp [toReading, outcome, decision, Reading.configClosed, h]
  | unread cfg _ _ _ hne =>
    simp [toReading, outcome, decision, Reading.configClosed, configIsClosed, Reading.readInFull, cfg.keys_closed, hne]
  | dependency _ hc hr =>
    simp [toReading, outcome, decision, Reading.configClosed, configIsClosed, Reading.readInFull,
      Reading.requiresDependency, hc, hr]
  | mathlib cfg _ _ hm =>
    simp [toReading, outcome, decision, Reading.configClosed, configIsClosed, Reading.readInFull,
      Reading.requiresDependency, Reading.mathlibReached, cfg.keys_closed, cfg.noRequire, hm]
  | uncovered cfg _ _ _ hm hc =>
    simp [toReading, outcome, decision, Reading.configClosed, configIsClosed, Reading.readInFull,
      Reading.requiresDependency, Reading.mathlibReached, Reading.covered,
      cfg.keys_closed, cfg.noRequire, hm, hc]
  | filesRefused cfg _ _ _ hm hc hf =>
    simp [toReading, outcome, decision, Reading.configClosed, configIsClosed, Reading.readInFull,
      Reading.requiresDependency, Reading.mathlibReached, Reading.covered, Reading.filesAdmitted,
      cfg.keys_closed, cfg.noRequire, hm, hc, hf]
  | admitted cfg _ _ _ hm hc hf =>
    simp [toReading, outcome, decision, Reading.configClosed, configIsClosed, Reading.readInFull,
      Reading.requiresDependency, Reading.mathlibReached, Reading.covered, Reading.filesAdmitted,
      cfg.keys_closed, cfg.noRequire, hm, hc, hf]

def earlyUnread (toolchainFile : Option String) (why : String) : Stage :=
  match ht : toolchainFile == some leanToolchain with
  | true => .unread ClosedConfig.empty [] [] [(`config, why)] rfl
  | false => .configRefused toolchainFile false [] [] [(`config, why)] (by simp [configIsClosed, ht])

def mkLeanConfig (toolchainFile : Option String) : Stage :=
  .configRefused toolchainFile true [] [] [] (by simp [configIsClosed])

def mkOpenPaths (cfg : ClosedConfig) (paths : List String) (hne : paths.isEmpty = false) : Stage :=
  .configRefused (some leanToolchain) false cfg.keys paths [] (by simp [configIsClosed, hne])

def ofConfig (toolchainFile : Option String) (keys : List Name) : Except Stage ClosedConfig :=
  match hc : configIsClosed toolchainFile false [] keys with
  | false => .error (.configRefused toolchainFile false keys [] [] hc)
  | true =>
    match hr : keys.any (·.getRoot == `require) with
    | true => .error (.dependency keys (by simp only [configIsClosed, Bool.and_eq_true] at hc; exact hc.2) hr)
    | false => .ok ⟨keys, by
        simp only [configIsClosed, configKeysClosed, Bool.and_eq_true, List.all_eq_true, List.any_eq_false] at hc hr ⊢
        intro k hk
        cases hreq : k.getRoot == `require with
        | true => exact absurd hreq (hr k hk)
        | false => simpa [hreq] using hc.2 k hk, hr⟩

def ofFiles (cfg : ClosedConfig) (roots reached : List Name) (files : List FileRead)
    (hnomath : reached.any (·.getRoot == `Mathlib) = false) : Stage :=
  match hc : covers roots reached files with
  | false => .uncovered cfg roots reached files hnomath hc
  | true =>
    match hf : files.all (·.admitted) with
    | false => .filesRefused cfg roots reached files hnomath hc hf
    | true => .admitted cfg roots reached files hnomath hc hf

end Stage

def gate {m : Type → Type} [Monad m] (read : m Outcome) (build : m Bool)
    (rules : m Regula.Closed.Verdict) : m Report := do
  match ← read with
  | .refused => return .refused
  | .incomplete => return .incomplete
  | .proofOnly => return .proofOnly
  | .admitted =>
    if ← build then
      return .full (← rules)
    else
      return .full .fail

namespace Report

def exitCode : Report → UInt32
  | .full .pass => 0
  | .proofOnly => 3
  | .full .fail | .refused => 1
  | .full .incomplete | .incomplete => 2

theorem exitCode_eq_zero_iff (r : Report) : r.exitCode = 0 ↔ r = .full .pass := by
  rcases r with (_ | _ | _) | _ | _ | _ <;>
    first
      | exact ⟨fun _ => rfl, fun _ => rfl⟩
      | exact ⟨fun h => absurd h (by decide), fun h => by cases h⟩

def label : Report → String
  | .full .pass => "regula: full verdict: pass, under the hypotheses H1 to H5 and the trusted base of its specification, at Lean 4.36.0"
  | .full v => s!"regula: full verdict: {v.label}"
  | .proofOnly =>
    "regula: only a proof verdict is possible for this project, and nothing was built, so no full \
      verdict: `lake build --wfail` and `lake lint` in the project give it, and they run \
      the project's code and its dependencies'"
  | .refused => "regula: refused before compiling (RG1010), so no build ran and no verdict is given"
  | .incomplete => "regula: incomplete (RG2001): the check could not read the project, so no build ran"

def labelOn (subject : String) : Report → String
  | .full .pass => (Report.full .pass).label ++ ", on " ++ Regula.Closed.detailText subject
  | r => r.label

end Report

end Regula.Language
