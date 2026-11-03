module

public import Regula.Tables
public import Regula.Verdict

/-!
# What every rule shares

The core of the rules over the closed input (`Regula.Closed.Input`): what a rule is, what it reports,
the report of a run, and the tables that more than one reader uses. Each rule is a module of its own
below `Regula/Rules/`, which imports this module and no other rule, and `Regula.Rules` lists them.

A rule reads the input through a value of `Tables i` (`Regula.Tables`), which carries what each of its
tables holds of the input `i`. A table that one rule alone reads is defined in that rule's module.
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
RG1006 reads it, and so does the loader's check of a constant that Lean's import replaced
(`Regula.Load.fitsUnshown`). -/
def loopConstructs : List Name := [``Lean.Loop.mk, ``repeatM]

/-- What a rule reports of one constant: the constant, its module, and what the rule found. -/
structure Violation where
  /-- The constant. -/
  subject : Name
  /-- The module of the constant. -/
  module : Name
  /-- What the rule found. -/
  detail : String

/-- A violation by the constant `d`. -/
def violation (d : Decl) (detail : String) : Violation :=
  { subject := d.name, module := d.module, detail }

/-- A rule: the name that its findings print, and the constants that it reports on an input, read
through the tables of that input. -/
structure Rule where
  /-- The stable name of the rule, which each of its findings prints. -/
  spelling : String
  /-- The constants of the input that violate the rule. -/
  check : ∀ {i : Input}, Tables i → List Violation

/-- One finding: the spelling of the rule that reports it, the constant, its module, and a detail. -/
structure Finding where
  /-- The spelling of the rule. -/
  rule : String
  /-- The constant. -/
  subject : Name
  /-- The module of the constant. -/
  module : Name
  /-- What the rule found. -/
  detail : String

/-- The finding of the rule `r` that its violation `v` gives. -/
def Finding.of (r : Rule) (v : Violation) : Finding :=
  { rule := r.spelling, subject := v.subject, module := v.module, detail := v.detail }

namespace Tables

variable {i : Input} (t : Tables i)

/-- `a` is one of the three logical axioms and is the toolchain's own constant of that name. -/
def known (a : Name) : Bool :=
  logicalAxioms.contains a && (t.index[a]?).any (·.inToolchain)

/-- Profile `p` admits axiom `a`. RG1005 reads it, and so does the loader's check of a constant that
Lean's import replaced (`Regula.Load.fitsUnshown`). -/
def admits : Profile → Name → Bool
  | .kernelOnly, _ => false
  | .choiceFree, a => t.known a && (a == ``propext || a == ``Quot.sound)
  | .standardLogical, a => t.known a

end Tables

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

/-- The verdict of a report. Its body is exposed, as is that of `findings`, so that the registry proves what a report
holds (`Regula.Closed.report_pass_iff`). -/
@[expose] def verdict : Report → Verdict
  | .pass => .pass
  | .fail _ _ => .fail
  | .incomplete _ => .incomplete

/-- The findings of a report. -/
@[expose] def findings : Report → List Finding
  | .pass => []
  | .fail first rest => first :: rest
  | .incomplete _ => []

end Report

end Regula.Closed
