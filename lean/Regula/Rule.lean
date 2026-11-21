module

public import Regula.Tables
public import Regula.Verdict

/-!
# What every rule shares

The core of the rules over the closed input (`Regula.Closed.Input`): what a rule is, what it reports,
the report of a run, and the tables that more than one reader uses. Each rule is a module of its own
below `Regula/Rules/`, which imports this module and no other rule, and `Regula.Rules` lists them.

A rule that reads constants reads them through a value of `Tables i` (`Regula.Tables`), which carries what
each of its tables holds of the input `i`. RG1013 reads the input's two lists of modules and no table. A table
that one rule alone reads is defined in that rule's module.
-/

public section

namespace Regula.Closed

open Lean (Name)

/-- The three axioms of Lean's logic that a profile can admit. -/
def logicalAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- The axioms of the toolchain by which Lean's kernel trusts the compiler: none at v4.36.0. -/
def compilerAxioms : List Name := []

/-- Whether `a` has the name form of the axiom a native proof adds:
`<declaration>._native.<tactic>.<suffix>`. -/
def nativeProofAxiom : Name → Bool
  | .str (.str (.str _ "_native") _) _ => true
  | _ => false

/-- The constants through which Lean's `while`, `repeat` and `repeat ... until` run: the one value
of the type `Lean.Loop` that they iterate over, and the loop itself (`Init/While.lean` at v4.36.0).
RG1006 reads it, and so does the loader's check of a constant that Lean's import replaced
(`Regula.Load.fitsUnshown`). -/
def loopConstructs : List Name := [``Lean.Loop.mk, ``repeatM]

/-- What a rule reports on: a constant in a module, or a module itself (for RG1013). -/
inductive Subject where
  /-- The constant `name` associated with `module` (its declaring module, or for RG1011's `@[csimp]`
  clause, the claimed module that registered it). -/
  | constant (name module : Name)
  /-- The module `name`. -/
  | module (name : Name)

/-- The name of a subject: the constant's name, or the module's name. -/
def Subject.name : Subject → Name
  | .constant name _ => name
  | .module name => name

/-- Non-blank fix guidance for a finding: non-empty text whose first character is not whitespace,
so no rule can emit empty, blank, or leading-whitespace guidance. -/
structure Guidance where
  /-- The remediation text printed beneath the finding line. -/
  text : String
  /-- The guidance begins with a non-whitespace character. -/
  nonblank : text.toList.head?.any (!·.isWhitespace) = true

namespace Guidance

theorem text_ne_empty (g : Guidance) : g.text ≠ "" := by
  intro h
  have hn := g.nonblank
  rw [h] at hn
  simp at hn

theorem exists_nonwhitespace (g : Guidance) : ∃ c ∈ g.text.toList, c.isWhitespace = false := by
  have hn := g.nonblank
  cases hl : g.text.toList with
  | nil => simp [hl] at hn
  | cons c cs =>
    rw [hl] at hn
    simp only [List.head?_cons, Option.any_some, Bool.not_eq_true'] at hn
    exact ⟨c, by simp, hn⟩

end Guidance

/-- What a rule reports of one subject: the subject, what the rule found, and non-blank fix guidance. -/
structure Violation where
  /-- The constant or module that violated the rule. -/
  subject : Subject
  /-- What the rule found. -/
  detail : String
  /-- Actionable fix guidance for the finding. -/
  guidance : Guidance

/-- A violation by the constant `d`. -/
def violation (d : Decl) (detail : String) (guidance : Guidance) : Violation :=
  { subject := .constant d.name d.module, detail, guidance }

/-- A rule: the name that its findings print, and the subjects that it reports on an input, read
through the tables of that input. -/
structure Rule where
  /-- The stable name of the rule, which each of its findings prints. -/
  spelling : String
  /-- The subjects of the input that violate the rule. -/
  check : ∀ {i : Input}, Tables i → List Violation

/-- One finding: the spelling of the rule that reports it, the subject, a detail, and fix guidance. -/
structure Finding where
  /-- The spelling of the rule. -/
  rule : String
  /-- The constant or module that violated the rule. -/
  subject : Subject
  /-- What the rule found. -/
  detail : String
  /-- Actionable fix guidance for the finding. -/
  guidance : Guidance

/-- The finding of the rule `r` that its violation `v` gives. -/
def Finding.of (r : Rule) (v : Violation) : Finding :=
  { rule := r.spelling, subject := v.subject, detail := v.detail, guidance := v.guidance }

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

/-- `defDecl` and `implDecl` form the compiler-generated `T.ctorIdx` / `T.ctorIdx._impl` pair for
the safe inductive type `ind` (`Lean/Meta/Constructions/CtorIdx.lean:40-141` at v4.36.0): `ind` is a
safe inductive in the same module, `getObjTagNat` is the toolchain's constant
(`Init/Prelude.lean:1381-1382`), `defDecl` is the safe definition `ind.ctorIdx` whose sole
replacement is `@[implemented_by ind.ctorIdx._impl]` with no initialization function, and `implDecl`
is the unsafe definition `ind.ctorIdx._impl` with no replacement attribute or initialization
function. -/
def ctorIdxPair (ind : Name) (defDecl implDecl : Decl) : Bool :=
  let defName := Name.str ind "ctorIdx"
  let implName := Name.str defName "_impl"
  (t.index[`getObjTagNat]?).any (·.inToolchain) &&
  (t.index[ind]?).any (fun indDecl =>
    indDecl.kind == .inductive &&
    indDecl.safety == .safe &&
    indDecl.module == defDecl.module) &&
  defDecl.name == defName &&
  defDecl.kind == .definition &&
  defDecl.safety == .safe &&
  defDecl.ctorIdxForm == .defn ind &&
  defDecl.implementedBy == some implName &&
  !defDecl.isExtern &&
  defDecl.initFn.isNone &&
  implDecl.name == implName &&
  implDecl.module == defDecl.module &&
  implDecl.kind == .definition &&
  implDecl.safety == .unsafe &&
  implDecl.ctorIdxForm == .impl ind &&
  implDecl.implementedBy.isNone &&
  !implDecl.isExtern &&
  implDecl.initFn.isNone

/-- `d` is the safe half `T.ctorIdx` of a valid compiler-generated `ctorIdx` pair. RG1011 exempts
its `@[implemented_by T.ctorIdx._impl]` attribute. -/
def ctorIdxDef (d : Decl) : Bool :=
  match d.ctorIdxForm with
  | .defn ind => (t.index[Name.str d.name "_impl"]?).any (t.ctorIdxPair ind d ·)
  | _ => false

/-- `d` is the unsafe half `T.ctorIdx._impl` of a valid compiler-generated `ctorIdx` pair. RG1006
exempts its `unsafe` safety. -/
def ctorIdxImpl (d : Decl) : Bool :=
  match d.ctorIdxForm with
  | .impl ind => (t.index[Name.str ind "ctorIdx"]?).any (t.ctorIdxPair ind · d)
  | _ => false

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
