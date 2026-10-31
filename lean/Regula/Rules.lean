module

public import Regula.Input
public import Regula.RuleId
public import Regula.Verdict
import Lean.Compiler.Old

/-!
# The rules over the closed input

Each rule as a pure, total function from the closed input (`Regula.Closed.Input`) to the constants
that violate it, in the order of `specification/RegulaSpecification/Foundation.lean` (RG1001 to
RG1005) and `Safety.lean` (RG1006). Each reads only fields of the input.
`specification/RegulaSpecification/Proofs/` proves of each that it reports a subject exactly when
the violation predicate of the specification holds of it.

The rules read the axiom set of a constant from `Decl.axioms`, which the loader computes with
`Lean.collectAxioms`. An input without the set of a claimed constant is refused before any rule runs
(`Input.refusal?`), so a missing set is never read as an empty one.

`run` gives the verdict: an input that the admission refuses is `incomplete`, and a well-formed one
passes exactly when no rule reports a subject.
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
  deriving Inhabited

/-- What the rules read of one input, computed once. -/
structure Tables where
  /-- The profile that the project states. -/
  profile : Profile
  /-- The constants by name. -/
  index : Std.HashMap Name Decl
  /-- The constants of claimed modules. -/
  claimed : List Decl

/-- The tables of the input. -/
def Input.tables (i : Input) : Tables :=
  let claimed := setOf i.modules
  { profile := i.profile, index := i.index, claimed := i.decls.filter (claimed.contains ·.module) }

/-- A finding whose subject is the constant `d`. -/
def finding (rule : RuleId) (d : Decl) (detail : String) : Finding :=
  { rule, subject := d.name, module := d.module, detail }

/-- The axiom set of constant `d` (`Input.AxiomOf`), as the loader computed it. The admission
refuses an input without the set of a claimed constant (`Input.axiomsMissing?`). -/
def Decl.axiomSet (d : Decl) : List Name := d.axioms.getD []

namespace Tables

variable (t : Tables)

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
      b.kind == .definition && b.module == d.module && !b.isUnsafe && !b.isPartial &&
        b.implementedBy.isNone && !b.isExtern
  | none => false

/-- `d` has the form of the recursion helper of a safe recursive definition in the same module. -/
def recursionHelper (d : Decl) : Bool :=
  d.isPartial && !d.isUnsafe && d.implementedBy.isNone && !d.isExtern && t.helperBaseFits d

/-- RG1001: a constant of a claimed module is an axiom. -/
def rg1001 : List Finding :=
  t.claimed.filterMap fun d =>
    if d.kind == .axiom then some (finding .projectAxiom d "declares an axiom") else none

/-- RG1002: a constant of a claimed module depends on `sorryAx`. -/
def rg1002 : List Finding :=
  t.claimed.filterMap fun d =>
    if d.axiomSet.contains ``sorryAx then some (finding .proofHole d "depends on sorryAx") else none

/-- RG1003: a constant of a claimed module depends on an axiom that is not known, and that RG1002
and RG1004 do not name. -/
def rg1003 : List Finding :=
  t.claimed.filterMap fun d =>
    let unknown := d.axiomSet.filter fun a => !t.known a && a != ``sorryAx && !nativeProofAxiom a &&
      !compilerAxioms.contains a
    if !unknown.isEmpty then
      some (finding .unknownAxiom d s!"depends on the unknown axioms {unknown}")
    else none

/-- RG1004: a constant of a claimed module depends on a native proof's axiom or on an axiom by which
the kernel trusts the compiler. -/
def rg1004 : List Finding :=
  t.claimed.filterMap fun d =>
    let compiler := d.axiomSet.filter fun a => nativeProofAxiom a || compilerAxioms.contains a
    if !compiler.isEmpty then
      some (finding .nativeProof d s!"depends on the native-proof axioms {compiler}")
    else none

/-- RG1005: a constant of a claimed module depends on an axiom that the project's profile does not
admit. -/
def rg1005 : List Finding :=
  t.claimed.filterMap fun d =>
    let excess := d.axiomSet.filter (!t.admits t.profile ·)
    if !excess.isEmpty then
      some (finding .profileExceeded d s!"depends on {excess}, outside the profile")
    else none

/-- RG1006: a constant of a claimed module is unsafe, partial or named as a recursion helper,
without the form of a recursion helper, or its value mentions a loop construct of Lean. -/
def rg1006 : List Finding :=
  t.claimed.filterMap fun d =>
    if ((d.isUnsafe || d.isPartial || namedAsHelper d) && !t.recursionHelper d) || mentionsLoop d
    then
      some (finding .escapeHatch d (if mentionsLoop d then "mentions a loop construct of Lean"
        else if d.isUnsafe then "is unsafe"
        else if d.isPartial then "is partial"
        else "has the name of a recursion helper, and is not partial"))
    else none

/-- The findings of one rule, matched exhaustively over the closed type of the rules. RG2001 reads
no constant: it is the admission (`Input.refusal?`) and the shell's refusal of a build it cannot
load. -/
def check : RuleId → List Finding
  | .projectAxiom => t.rg1001
  | .proofHole => t.rg1002
  | .unknownAxiom => t.rg1003
  | .nativeProof => t.rg1004
  | .profileExceeded => t.rg1005
  | .escapeHatch => t.rg1006
  | .environment => []

end Tables

/-- Every finding of the input. -/
def Input.findings (i : Input) : List Finding :=
  RuleId.all.flatMap i.tables.check

/-- The verdict of a run and its findings, or the reason the run is incomplete. An input that the
admission refuses is incomplete; a well-formed input passes exactly when no rule reports a
subject. -/
def run (i : Input) : Verdict × List Finding × Option String :=
  match i.refusal? with
  | some why => (.incomplete, [], some why)
  | none =>
    let fs := i.findings
    (if fs.isEmpty then .pass else .fail, fs, none)

end Regula.Closed
