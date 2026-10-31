/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Regula.LanguageSet

/-!
# The language decision

The decision of the check that reads a project before anything of it is compiled: a pure function over
what Lean's parser gave for each file and what Lake's TOML parser gave for the configuration.
`specification/RegulaSpecification/Language.lean` states what it must decide, and
`specification/RegulaSpecification/Proofs/Language.lean` proves `decision` against that record in both
directions.

`positions` lists every position of a tree that the check reads, and everything else filters that list,
so there is one walk over `Lean.Syntax`. It is structural, with no `partial` and no fuel.

`gate` is the order of the full gate over any monad, so the order is a theorem about the code that runs
and not an observation alone.

A pass here means what the specification's `LeanBehaviour` says, under its hypotheses H1 and H2 about
Lean: that each tree is the one Lean elaborates, and that what the closed set admits runs no code that
the project wrote. No proof reaches either.
-/

public section

namespace Regula.Language

open Lean (Name Syntax)

mutual
  /-- Every position of a tree that the check reads: the tree, and the positions of each child of a node
  whose kind is not a leaf kind. -/
  def positions : Syntax → List Syntax
    | .node i k as =>
      .node i k as :: (if leafKinds.contains k then [] else positionsOfArray as)
    | s => [s]
  /-- `positions` of each element. -/
  def positionsOfArray : Array Syntax → List Syntax
    | ⟨l⟩ => positionsOfList l
  /-- `positions` of each element. -/
  def positionsOfList : List Syntax → List Syntax
    | [] => []
    | x :: xs => positions x ++ positionsOfList xs
end

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
  let target := (components n).dropWhile (· == `_root_)
  (List.range target.length).any fun i => (target.take (i + 1)).isSuffixOf (components N)

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
  | .atom _ v => atoms.contains v
  | .ident _ _ n _ => !reservedName n
  | .node _ k as =>
    (kinds.contains k || leafKinds.contains k) && argumentsAdmitted scopedParsers k as

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

namespace Reading

variable (r : Reading)

/-- The pinned toolchain, no `lakefile.lean`, no other key, and no package from a local path. -/
def configClosed : Bool :=
  r.toolchainFile == some leanToolchain && !r.leanConfig && r.configKeys.all configKeyAdmitted &&
    r.packages.all (·.fromGit)

/-- The checker started outside the project's Lake, nothing failed to read, and no output exists. -/
def readInFull : Bool :=
  r.outside && r.unread.isEmpty && r.outputs.isEmpty

/-- Whether a dependency's Lake configuration is code, which a Lake load would run. -/
def dependencyConfigIsCode : Bool :=
  r.packages.any (!·.tomlConfig)

/-- Whether Mathlib is in the build's imports. -/
def mathlibReached : Bool :=
  r.reached.any (·.getRoot == `Mathlib)

/-- There is a claim, each root is reached, and each module reached has its file read. -/
def covered : Bool :=
  !r.roots.isEmpty && r.roots.all r.reached.contains &&
    r.reached.all fun m => r.files.any (·.module == m)

/-- Each file of the root package is in the closed language. -/
def rootAdmitted : Bool :=
  r.files.all fun f => !f.inRoot || f.admitted

/-- Each file of a dependency is in the closed language. -/
def dependenciesAdmitted : Bool :=
  r.files.all fun f => f.inRoot || f.admitted

end Reading

/-- The decision. -/
def decision (r : Reading) : Outcome :=
  if !r.configClosed then .refused
  else if !r.readInFull then .incomplete
  else if r.dependencyConfigIsCode then .proofOnly
  else if r.mathlibReached then .proofOnly
  else if !r.covered then .incomplete
  else if !r.rootAdmitted then .refused
  else if !r.dependenciesAdmitted then .proofOnly
  else .admitted

/-- The order of the full gate, over any monad: `read` first, and `build` and `rules` only when it let
them. -/
def gate {m : Type → Type} [Monad m] (read : m Outcome) (build : m Bool)
    (rules : m Regula.Closed.Verdict) : m Report := do
  let finish (label : Regula.Closed.Verdict → Report) : m Report := do
    if ← build then
      return label (← rules)
    else
      return label .fail
  match ← read with
  | .refused => return .refused
  | .incomplete => return .incomplete
  | .admitted => finish .full
  | .proofOnly => finish .proof

namespace Report

/-- The exit code of a report under the full gate. Only the full verdict's pass exits with 0, so a
script cannot read a proof verdict as a full one. -/
def exitCode : Report → UInt32
  | .full .pass => 0
  | .proof .pass => 3
  | .full .fail | .proof .fail | .refused => 1
  | .full .incomplete | .proof .incomplete | .incomplete => 2

/-- Only the full verdict's pass exits with 0. -/
theorem exitCode_eq_zero_iff (r : Report) : r.exitCode = 0 ↔ r = .full .pass := by
  rcases r with (_ | _ | _) | (_ | _ | _) | _ | _ <;>
    first
      | exact ⟨fun _ => rfl, fun _ => rfl⟩
      | exact ⟨fun h => absurd h (by decide), fun h => by cases h⟩

/-- The last line of a run of the full gate. Each verdict names itself, and a pass of the full verdict
names the hypotheses it rests on. -/
def label : Report → String
  | .full .pass => "regula: full verdict: pass, under the hypotheses H1 and H2 about Lean 4.35.0"
  | .full v => s!"regula: full verdict: {v.label}"
  | .proof v =>
    s!"regula: proof verdict: {v.label}, which says nothing about what ran during the build; no full \
      verdict"
  | .refused => "regula: refused before compiling (RG1010), so no build ran and no verdict is given"
  | .incomplete => "regula: incomplete (RG2001): the check could not read the project, so no build ran"

end Report

end Regula.Language
