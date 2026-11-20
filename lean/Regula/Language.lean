module

public import Lean.Data.Name
public import Regula.LanguageSet

/-!
# The language decision

The decision of the check that reads a project before anything of it is compiled: a pure function over what
Lean's parser gave for each file and what Lake's TOML parser gave for the configuration.
`specification/RegulaSpecification/Language.lean` states what it must decide, and
`specification/RegulaSpecification/Proofs/Language.lean` proves `decision` against that record in both
directions.

`positions` lists every position of a tree that the check reads, and everything else filters that list, so
there is one walk over `Lean.Syntax`. It is structural, with no `partial` and no fuel.

`gate` is the order of the full gate over any monad, so the order is a theorem about the code that runs.

What an admitted reading means is what the specification's `LeanBehaviour` says, under its hypotheses H1 and
H2 about Lean: that each tree is the one Lean elaborates, and that what the closed set admits runs no code
that the project wrote. No proof reaches either. A pass of the full verdict rests on them, on H3, H4 and H5
and on the rest of the specification's trusted base.
-/

public section

namespace Regula.Language

open Lean (Name Syntax)

/-- Strict order on `String` for binary search on sorted tables. -/
def strLt (a b : String) : Bool :=
  decide (a < b)

/-- Prebuilt sorted array of `kinds` for binary search. -/
def kindsArray : Array Name := kinds.toArray

/-- Prebuilt sorted array of `leafKinds` for binary search. -/
def leafKindsArray : Array Name := leafKinds.toArray

/-- Prebuilt sorted array of `atoms` for binary search. -/
def atomsArray : Array String := atoms.toArray

/-- Whether `k` is a leaf kind whose children are open text. -/
def isLeafKind (k : Name) : Bool :=
  leafKindsArray.binSearchContains k Name.lt

/-- Whether `k` is an admitted non-leaf syntax kind. -/
def isKind (k : Name) : Bool :=
  kindsArray.binSearchContains k Name.lt

/-- Whether `v` is an admitted token outside `leafKinds`. -/
def isAtom (v : String) : Bool :=
  atomsArray.binSearchContains v strLt

mutual
  /-- Every position of a tree that the check reads, pushed in reverse onto `acc`. -/
  def positionsGo (acc : List Syntax) : Syntax → List Syntax
    | .node i k as =>
      let acc := .node i k as :: acc
      if isLeafKind k then acc else positionsOfArrayGo acc as
    | s => s :: acc
  /-- `positionsGo` of each element. -/
  def positionsOfArrayGo (acc : List Syntax) : Array Syntax → List Syntax
    | ⟨l⟩ => positionsOfListGo acc l
  /-- `positionsGo` of each element. -/
  def positionsOfListGo (acc : List Syntax) : List Syntax → List Syntax
    | [] => acc
    | x :: xs => positionsOfListGo (positionsGo acc x) xs
end

/-- Every position of a tree that the check reads: the tree, and the positions of each child of a node
whose kind is not a leaf kind. -/
def positions (t : Syntax) : List Syntax :=
  (positionsGo [] t).reverse

/-- Whether a project may not write this name, because Lean or its compiler reads its form. -/
def reservedName : Name → Bool
  | .anonymous => false
  | .str .anonymous "_root_" => false
  | .str p s => s.front == '_' || s == "autoParam" || reservedName p
  | .num p _ => reservedName p

/-- The names a `namespace` or `open` command takes as its targets. -/
def targets (as : Array Syntax) : List Name :=
  as.toList.flatMap fun
    | .ident _ _ n _ => [n]
    | .node _ `null xs => xs.toList.filterMap fun
      | .ident _ _ n _ => some n
      | _ => none
    | _ => []

/-- Whether, from some namespace, a target `n` can activate the namespace `N`. -/
def canActivate (N n : Name) : Bool :=
  let target := n.components.dropWhile (· == `_root_)
  (List.range target.length).any fun i => (target.take (i + 1)).isSuffixOf N.components

/-- The identifier that is the argument of `as` at `i`, in the table `allowed`. -/
def identIn (allowed : List Name) (as : Array Syntax) (i : Nat) : Bool :=
  match as[i]? with
  | some (.ident _ _ n _) => allowed.contains n
  | _ => false

/-- Whether an optional argument of the parser is absent. -/
def noArgument : Option Syntax → Bool
  | some (.node _ `null xs) => xs.isEmpty
  | _ => false

/-- What the kind `k` asks of its arguments, beyond being in the closed set. -/
def argumentsAdmitted (scopedParsers : List Name) (k : Name) (as : Array Syntax) : Bool :=
  if k == `Lean.Parser.Attr.simple then identIn simpleAttributes as 0 && noArgument as[1]?
  else if k == `Lean.Parser.Command.set_option then identIn options as 1
  else if k == `Lean.Parser.Tactic.posConfigItem then identIn configItems as 1
  else if k == `Lean.Parser.Command.derivingClass then identIn derivingClasses as 1
  else if k == `Lean.Parser.Command.namespace || k == `Lean.Parser.Command.openSimple then
    (targets as).all fun n => scopedParsers.all fun N => !canActivate N n
  else true

/-- Whether one position is admitted. -/
def positionAdmitted (scopedParsers : List Name) : Syntax → Bool
  | .missing => false
  | .atom _ v => isAtom v
  | .ident _ _ n _ => !reservedName n
  | .node _ k as =>
    (isKind k || isLeafKind k) && argumentsAdmitted scopedParsers k as

/-- The positions of `t` that are not admitted. -/
def offenders (scopedParsers : List Name) (t : Syntax) : List Syntax :=
  (positions t).filter (!positionAdmitted scopedParsers ·)

/-- Whether a position is a node of the kind `k`. -/
def isNodeOf (k : Name) : Syntax → Bool
  | .node _ k' _ => k' == k
  | _ => false

/-- Whether the header holds the keyword `module`. -/
def moduleFile (header : Syntax) : Bool :=
  (positions header).any (isNodeOf `Lean.Parser.Module.moduleTk)

/-- Whether the last tree is the parser's end of input. -/
def readToEnd (commands : List Syntax) : Bool :=
  match commands.getLast? with
  | some s => isNodeOf `Lean.Parser.Command.eoi s
  | none => false

/-- Each position of a file that is not admitted. -/
def FileRead.offenders (f : FileRead) : List Syntax :=
  (f.header :: f.commands).flatMap (Regula.Language.offenders f.scopedParsers)

/-- Whether one file is in the closed language. -/
def FileRead.admitted (f : FileRead) : Bool :=
  f.parsed && moduleFile f.header && readToEnd f.commands && f.offenders.isEmpty

/-- Whether a key of `lakefile.toml` is in the closed set. -/
def configKeyAdmitted (k : Name) : Bool :=
  configKeys.contains k || options.any (k == `leanOptions ++ ·)

/-- Whether a character may be in a component of a module name: an ASCII letter or digit, `_` or `'`. -/
def closedNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

/-- Whether a string is a component of a closed module name. -/
def closedComponent (s : String) : Bool :=
  !s.isEmpty && s.toList.all closedNameChar

/-- Whether a module name is in the closed domain, so that the path Lean's `modToFilePath` joins from it
stays below the directory it starts from: `FilePath.join` discards its base for an absolute component, and
a component can be `..`. -/
def closedModuleName : Name → Bool
  | .anonymous => false
  | .num _ _ => false
  | .str .anonymous s => closedComponent s
  | .str (.str q t) s => closedModuleName (.str q t) && closedComponent s
  | .str (.num _ _) _ => false

/-- The components of `path` below `base`, when `path` lies at or below `base` and no component below it
starts with `.`: so none is `.` or `..`, and none is `.lake`. It is what maps a file that Lake names in the
checker's tree to the same relative file of the project, and back. -/
def treeRelative (base path : List String) : Option (List String) :=
  if base.isPrefixOf path then
    let rel := path.drop base.length
    if rel.all (fun c => !c.isEmpty && c.front != '.') then some rel else none
  else none

/-- Whether what was read covers a claim: there is a claim, each root is reached, each module reached has a
name in the closed domain, and each has its file read. -/
def covers (roots reached : List Name) (files : List FileRead) : Bool :=
  !roots.isEmpty && roots.all reached.contains && reached.all closedModuleName &&
    reached.all fun m => files.any (·.module == m)

namespace Reading

variable (r : Reading)

/-- The pinned toolchain, no `lakefile.lean`, no path outside the closed domain, and each key whose root is
not `require` in the closed set. -/
def configClosed : Bool :=
  r.toolchainFile == some leanToolchain && !r.leanConfig && r.openPaths.isEmpty &&
    r.configKeys.all fun k => k.getRoot == `require || configKeyAdmitted k

/-- Nothing failed to read. -/
def readInFull : Bool :=
  r.unread.isEmpty

/-- Whether the project's configuration has a dependency: a key with the root `require`. -/
def requiresDependency : Bool :=
  r.configKeys.any (·.getRoot == `require)

/-- Whether Mathlib is in the build's imports. -/
def mathlibReached : Bool :=
  r.reached.any (·.getRoot == `Mathlib)

/-- The roots, the modules reached and the files read cover a claim. -/
def covered : Bool :=
  covers r.roots r.reached r.files

/-- Each file read is in the closed language. -/
def filesAdmitted : Bool :=
  r.files.all (·.admitted)

end Reading

/-- The decision. -/
def decision (r : Reading) : Outcome :=
  if !r.configClosed then .refused
  else if !r.readInFull then .incomplete
  else if r.requiresDependency then .proofOnly
  else if r.mathlibReached then .proofOnly
  else if !r.covered then .incomplete
  else if !r.filesAdmitted then .refused
  else .admitted

/-- The key paths of a `lakefile.toml`, each in the closed set and none with the root `require`. -/
structure ClosedConfig where
  /-- The key paths of `lakefile.toml`. -/
  keys : List Name
  /-- Each key path is in the closed set. -/
  admitted : keys.all configKeyAdmitted = true
  /-- No key path has root `require`. -/
  noRequire : keys.any (·.getRoot == `require) = false

namespace ClosedConfig

/-- The empty closed configuration, with no key paths. -/
def empty : ClosedConfig := ⟨[], rfl, rfl⟩

theorem keys_closed (cfg : ClosedConfig) :
    cfg.keys.all (fun k => k.getRoot == `require || configKeyAdmitted k) = true := by
  simp only [List.all_eq_true, Bool.or_eq_true]
  intro k hk
  exact .inr (List.all_eq_true.mp cfg.admitted k hk)

end ClosedConfig

/-- The phased result of reading a project before compiling it. Each constructor fixes its outcome by its own
invariant, so early exits cannot construct half-populated `Reading` records whose phase `decision` must later
reconstruct (`Stage.decision_toReading`). -/
inductive Stage where
  /-- The configuration is outside the closed set (wrong toolchain, `lakefile.lean`, open path or bad key). -/
  | configRefused (toolchainFile : Option String) (leanConfig : Bool) (configKeys : List Name)
      (openPaths : List String) (unread : List (Name × String))
      (h : (toolchainFile == some leanToolchain && !leanConfig && openPaths.isEmpty &&
        configKeys.all fun k => k.getRoot == `require || configKeyAdmitted k) = false)
  /-- The configuration is closed, and something failed to read. -/
  | unread (cfg : ClosedConfig) (roots reached : List Name) (unread : List (Name × String))
      (hne : unread.isEmpty = false)
  /-- The configuration is closed, nothing failed to read, and `lakefile.toml` has a `require` key. -/
  | dependency (configKeys : List Name)
      (hclosed : configKeys.all (fun k => k.getRoot == `require || configKeyAdmitted k) = true)
      (hreq : configKeys.any (·.getRoot == `require) = true)
  /-- The configuration is closed with no dependency, the walk read in full, and Mathlib was reached. -/
  | mathlib (cfg : ClosedConfig) (roots reached : List Name)
      (hmathlib : reached.any (·.getRoot == `Mathlib) = true)
  /-- The walk read in full without Mathlib and files were parsed, but coverage failed. -/
  | uncovered (cfg : ClosedConfig) (roots reached : List Name) (files : List FileRead)
      (hnomath : reached.any (·.getRoot == `Mathlib) = false)
      (huncov : covers roots reached files = false)
  /-- Coverage holds without Mathlib, and some parsed file is outside the closed language. -/
  | filesRefused (cfg : ClosedConfig) (roots reached : List Name) (files : List FileRead)
      (hnomath : reached.any (·.getRoot == `Mathlib) = false)
      (hcov : covers roots reached files = true)
      (hbad : files.all (·.admitted) = false)
  /-- Every phase passed and every file is in the closed language. -/
  | admitted (cfg : ClosedConfig) (roots reached : List Name) (files : List FileRead)
      (hnomath : reached.any (·.getRoot == `Mathlib) = false)
      (hcov : covers roots reached files = true)
      (hadm : files.all (·.admitted) = true)

namespace Stage

/-- The `Reading` that a phased stage represents. -/
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

/-- The outcome fixed by the stage constructor alone. -/
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
    simp [toReading, outcome, decision, Reading.configClosed, Reading.readInFull, cfg.keys_closed, hne]
  | dependency _ hc hr =>
    simp [toReading, outcome, decision, Reading.configClosed, Reading.readInFull,
      Reading.requiresDependency, hc, hr]
  | mathlib cfg _ _ hm =>
    simp [toReading, outcome, decision, Reading.configClosed, Reading.readInFull,
      Reading.requiresDependency, Reading.mathlibReached, cfg.keys_closed, cfg.noRequire, hm]
  | uncovered cfg _ _ _ hm hc =>
    simp [toReading, outcome, decision, Reading.configClosed, Reading.readInFull,
      Reading.requiresDependency, Reading.mathlibReached, Reading.covered,
      cfg.keys_closed, cfg.noRequire, hm, hc]
  | filesRefused cfg _ _ _ hm hc hf =>
    simp [toReading, outcome, decision, Reading.configClosed, Reading.readInFull,
      Reading.requiresDependency, Reading.mathlibReached, Reading.covered, Reading.filesAdmitted,
      cfg.keys_closed, cfg.noRequire, hm, hc, hf]
  | admitted cfg _ _ _ hm hc hf =>
    simp [toReading, outcome, decision, Reading.configClosed, Reading.readInFull,
      Reading.requiresDependency, Reading.mathlibReached, Reading.covered, Reading.filesAdmitted,
      cfg.keys_closed, cfg.noRequire, hm, hc, hf]

/-- Early unread stop before TOML keys are parsed: `incomplete` when `lean-toolchain` is pinned,
and `refused` otherwise. -/
def earlyUnread (toolchainFile : Option String) (why : String) : Stage :=
  match ht : toolchainFile == some leanToolchain with
  | true => .unread ClosedConfig.empty [] [] [(`config, why)] rfl
  | false => .configRefused toolchainFile false [] [] [(`config, why)] (by simp [ht])

/-- Stop because `lakefile.lean` exists. -/
def mkLeanConfig (toolchainFile : Option String) : Stage :=
  .configRefused toolchainFile true [] [] [] (by simp)

/-- Stop because the loaded configuration names an open path, non-single glob or non-library target. -/
def mkOpenPaths (cfg : ClosedConfig) (paths : List String) (hne : paths.isEmpty = false) : Stage :=
  .configRefused (some leanToolchain) false cfg.keys paths [] (by simp [hne])

/-- Classify the toolchain and TOML key paths into either a stopping stage (`refused` or `proofOnly`)
or a closed configuration with no dependency. -/
def ofConfig (toolchainFile : Option String) (keys : List Name) : Except Stage ClosedConfig :=
  match hc : toolchainFile == some leanToolchain &&
      keys.all (fun k => k.getRoot == `require || configKeyAdmitted k) with
  | false => .error (.configRefused toolchainFile false keys [] [] (by
      simp only [Bool.and_eq_false_iff, Bool.not_false, List.isEmpty_nil, Bool.and_true] at hc ⊢
      exact hc))
  | true =>
    match hr : keys.any (·.getRoot == `require) with
    | true => .error (.dependency keys (by simp only [Bool.and_eq_true] at hc; exact hc.2) hr)
    | false => .ok ⟨keys, by
        simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_false] at hc hr ⊢
        intro k hk
        cases hreq : k.getRoot == `require with
        | true => exact absurd hreq (hr k hk)
        | false => simpa [hreq] using hc.2 k hk, hr⟩

/-- Classify parsed files after a full Mathlib-free walk into `uncovered`, `filesRefused` or `admitted`. -/
def ofFiles (cfg : ClosedConfig) (roots reached : List Name) (files : List FileRead)
    (hnomath : reached.any (·.getRoot == `Mathlib) = false) : Stage :=
  match hc : covers roots reached files with
  | false => .uncovered cfg roots reached files hnomath hc
  | true =>
    match hf : files.all (·.admitted) with
    | false => .filesRefused cfg roots reached files hnomath hc hf
    | true => .admitted cfg roots reached files hnomath hc hf

end Stage

/-- The order of the full gate, over any monad: `read` first, and `build` and `rules` only for an
admitted project. -/
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

/-- The exit code of a report under the full gate. Only the full verdict's pass exits with 0, so a
script cannot read a proof verdict as a full one. -/
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

/-- The words that state the report of a run of the full gate. Each verdict names itself, and a pass of the full
verdict names the hypotheses it rests on. -/
def label : Report → String
  | .full .pass => "regula: full verdict: pass, under the hypotheses H1 to H5 and the trusted base of its specification, at Lean 4.35.0"
  | .full v => s!"regula: full verdict: {v.label}"
  | .proofOnly =>
    "regula: only a proof verdict is possible for this project, and nothing was built, so no full \
      verdict: `lake build --wfail` and `lake lint` in the project give it, and they run \
      the project's code and its dependencies'"
  | .refused => "regula: refused before compiling (RG1010), so no build ran and no verdict is given"
  | .incomplete => "regula: incomplete (RG2001): the check could not read the project, so no build ran"

/-- The last line of a run of the full gate on the project at `subject`: a pass says what it audited, on one physical line and
at the end of the line, so that no path can change the words that state the verdict. -/
def labelOn (subject : String) : Report → String
  | .full .pass => (Report.full .pass).label ++ ", on " ++ Regula.Closed.detailText subject
  | r => r.label

end Report

end Regula.Language
