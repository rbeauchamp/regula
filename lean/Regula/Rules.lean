/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Regula.RuleId
public import Regula.Tables
public import Regula.Verdict
import Lean.Compiler.Old

/-!
# The rules over the closed input

Each rule as a pure, total function from the closed input (`Regula.Closed.Input`) to the constants
that violate it, in the order of `specification/RegulaSpecification/Foundation.lean` (RG1001 to
RG1005) and `Safety.lean` (RG1006). Each reads only fields of the input, through its tables.
`specification/RegulaSpecification/Proofs/` proves of each that it reports a subject exactly when
the violation predicate of the specification holds of it.

A rule reads the input through a value of `Tables i` (`Regula.Tables`), which carries what each of
its tables holds of the input `i`.

`Input.report` gives the outcome of an input, which passes exactly when no rule reports a subject.
`decision` gives the outcome of what the load gave, so a reading that the admission refuses
(`Draft.admit`) is `incomplete`.
-/

public section

namespace Regula.Closed

open Lean (Name)

/-- The three axioms of Lean's logic that a profile can admit. -/
def logicalAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- The axioms of the toolchain by which Lean's kernel trusts the compiler: none at v4.35.0. -/
def compilerAxioms : List Name := []

/-- Whether `a` has the name form of the axiom a native proof adds:
`<declaration>._native.<tactic>.<suffix>`. -/
def nativeProofAxiom : Name → Bool
  | .str (.str (.str _ "_native") _) _ => true
  | _ => false

/-- The constants through which Lean's `while`, `repeat` and `repeat ... until` run: the one value
of the type `Lean.Loop` that they iterate over, and the loop itself (`Init/While.lean` at v4.35.0).
-/
def loopConstructs : List Name := [``Lean.Loop.mk, ``repeatM]

/-- Whether the value of `d` mentions a loop construct. -/
def mentionsLoop (d : Decl) : Bool := loopConstructs.any d.valueUses.contains

/-- Whether the compiler reads the name of `d` as a recursion helper's. This is its own test,
whatever the kind or flags of the constant. -/
def namedAsHelper (d : Decl) : Bool := (Lean.Compiler.isUnsafeRecName? d.name).isSome

/-- One finding: a rule, the constant that violates it, the module of the constant, and a detail. -/
structure Finding where
  /-- The rule that the constant violates. -/
  rule : RuleId
  /-- The constant. -/
  subject : Name
  /-- The module of the constant. -/
  module : Name
  /-- What the rule found. -/
  detail : String

/-- A finding whose subject is the constant `d`. -/
def finding (rule : RuleId) (d : Decl) (detail : String) : Finding :=
  { rule, subject := d.name, module := d.module, detail }

namespace Tables

variable {i : Input} (t : Tables i)

/-- `a` is one of the three logical axioms and is the toolchain's own constant of that name. -/
def known (a : Name) : Bool :=
  logicalAxioms.contains a && (t.index[a]?).any (·.inToolchain)

/-- Profile `p` admits axiom `a`. -/
def admits : Profile → Name → Bool
  | .kernelOnly, _ => false
  | .choiceFree, a => t.known a && (a == ``propext || a == ``Quot.sound)
  | .standardLogical, a => t.known a

/-- `d` has the name of a recursion helper, and its base is a safe, total definition in its module.
The name is read with the compiler's own test, `Lean.Compiler.isUnsafeRecName?`. The base is a
definition: the base of a `partial def` is an opaque constant, so its helper is no exception. -/
def helperBaseFits (d : Decl) : Bool :=
  match Lean.Compiler.isUnsafeRecName? d.name with
  | some base => t.index[base]?.any fun b =>
      b.kind == .definition && b.module == d.module && b.safety == .safe &&
        b.implementedBy.isNone && !b.isExtern
  | none => false

/-- `d` has the form of the recursion helper of a safe recursive definition in the same module. -/
def recursionHelper (d : Decl) : Bool :=
  d.safety == .partial && d.implementedBy.isNone && !d.isExtern && t.helperBaseFits d

/-- RG1001: a constant of a claimed module is an axiom. -/
def rg1001 : List Finding :=
  t.claimed.filterMap fun d =>
    if d.kind == .axiom then some (finding .projectAxiom d "declares an axiom") else none

/-- RG1002: a constant of a claimed module depends on `sorryAx`. -/
def rg1002 : List Finding :=
  t.claimed.filterMap fun d =>
    if (t.axiomSet d.name).contains ``sorryAx then
      some (finding .proofHole d "depends on sorryAx")
    else none

/-- RG1003: a constant of a claimed module depends on an axiom that is not known, and that RG1002
and RG1004 do not name. -/
def rg1003 : List Finding :=
  t.claimed.filterMap fun d =>
    let unknown := (t.axiomSet d.name).filter fun a =>
      !t.known a && a != ``sorryAx && !nativeProofAxiom a && !compilerAxioms.contains a
    if !unknown.isEmpty then
      some (finding .unknownAxiom d s!"depends on the unknown axioms {unknown}")
    else none

/-- RG1004: a constant of a claimed module depends on a native proof's axiom or on an axiom by which
the kernel trusts the compiler. -/
def rg1004 : List Finding :=
  t.claimed.filterMap fun d =>
    let compiler := (t.axiomSet d.name).filter fun a =>
      nativeProofAxiom a || compilerAxioms.contains a
    if !compiler.isEmpty then
      some (finding .nativeProof d s!"depends on the native-proof axioms {compiler}")
    else none

/-- RG1005: a constant of a claimed module depends on an axiom that the project's profile does not
admit. -/
def rg1005 : List Finding :=
  t.claimed.filterMap fun d =>
    let excess := (t.axiomSet d.name).filter (!t.admits i.profile ·)
    if !excess.isEmpty then
      some (finding .profileExceeded d s!"depends on {excess}, outside the profile")
    else none

/-- What RG1006 prints of a constant that it reports. -/
def escapeDetail (d : Decl) : String :=
  if mentionsLoop d then "mentions a loop construct of Lean"
  else
    match d.safety with
    | .unsafe => "is unsafe"
    | .partial => "is partial"
    | .safe => "has the name of a recursion helper, and is not partial"

/-- RG1006: a constant of a claimed module is unsafe, partial or named as a recursion helper,
without the form of a recursion helper, or its value mentions a loop construct of Lean. -/
def rg1006 : List Finding :=
  t.claimed.filterMap fun d =>
    if ((d.safety != .safe || namedAsHelper d) && !t.recursionHelper d) || mentionsLoop d then
      some (finding .escapeHatch d (escapeDetail d))
    else none

/-- The findings of one rule, matched exhaustively over the closed type of the rules. RG1010 and
RG2001 read no constant. RG1010 is the language check, which runs before the build
(`Regula.Language`), and RG2001 is the admission (`Draft.admit`) and the shell's refusal of a build
it cannot load. -/
def check : RuleId → List Finding
  | .projectAxiom => t.rg1001
  | .proofHole => t.rg1002
  | .unknownAxiom => t.rg1003
  | .nativeProof => t.rg1004
  | .profileExceeded => t.rg1005
  | .escapeHatch => t.rg1006
  | .language => []
  | .environment => []

end Tables

/-- Every finding of the input. -/
def Input.findings (i : Input) : List Finding :=
  RuleId.all.flatMap i.tables.check

/-- The outcome of a run: each verdict with what it carries. A pass has no finding, a failure has at
least one, and an incomplete run has its reason. -/
inductive Report where
  /-- The input has the closed form, and no rule reports a subject. -/
  | pass
  /-- A rule reports a subject: the first finding and the rest. -/
  | fail (first : Finding) (rest : List Finding)
  /-- The build could not be loaded or the input does not have the closed form, and why. -/
  | incomplete (why : String)

namespace Report

/-- The verdict of a report. -/
def verdict : Report → Verdict
  | .pass => .pass
  | .fail _ _ => .fail
  | .incomplete _ => .incomplete

/-- The findings of a report. -/
def findings : Report → List Finding
  | .pass => []
  | .fail first rest => first :: rest
  | .incomplete _ => []

end Report

/-- The report of the closed input: it passes exactly when no rule reports a subject. -/
def Input.report (i : Input) : Report :=
  match i.findings with
  | [] => .pass
  | first :: rest => .fail first rest

/-- The report of a run, from what the load gave: a build it cannot read is `incomplete`, and
otherwise the report is `Input.report`. -/
def decision : Except String Input → Report
  | .error why => .incomplete why
  | .ok input => input.report


end Regula.Closed
