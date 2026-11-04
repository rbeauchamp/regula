module

public import Regula.Rules.RG1001
public import Regula.Rules.RG1002
public import Regula.Rules.RG1003
public import Regula.Rules.RG1004
public import Regula.Rules.RG1005
public import Regula.Rules.RG1006
public import Regula.Rules.RG1011
public import Regula.Rules.RG1012

/-!
# The registry of the rules

The one list of the rules that a run applies, and the report of a run: the findings of each registered
rule, in the order of the list, and a pass exactly when no registered rule reports a subject
(`report_pass_iff`). Adding a rule is a module of its own below `Regula/Rules/` and one line of
`registry`, with its statement in `specification/RegulaSpecification/Rules/` and one line of the
specification's registry, which `specification/RegulaSpecification/Rules.lean` proves equal to this one.

RG1010, the language check (`Regula.Language`), and RG2001, the refusal of a build that the checker cannot
read, are no rules of this list: neither reads a constant.
-/

public section

namespace Regula.Closed

/-- The rules that a run applies, in the order of their findings. -/
def registry : List Rule :=
  [Regula.Rules.RG1001.rule, Regula.Rules.RG1002.rule, Regula.Rules.RG1003.rule, Regula.Rules.RG1004.rule,
    Regula.Rules.RG1005.rule, Regula.Rules.RG1006.rule, Regula.Rules.RG1011.rule,
    Regula.Rules.RG1012.rule]

/-- The codes that no rule of the registry may take: the language check's and the environment's. -/
def reservedSpellings : List String := ["RG1010", "RG2001"]

/-- Each spelling names one check, so a finding's code names the rule that reports it. -/
theorem spellings_nodup : (registry.map (·.spelling) ++ reservedSpellings).Nodup := by decide

/-- Every finding of the input: the findings of each registered rule, in the order of the registry. -/
def Input.findings (i : Input) : List Finding :=
  let t := i.tables
  registry.flatMap fun r => (r.check t).map (Finding.of r)

theorem mem_findings {i : Input} {f : Finding} :
    f ∈ i.findings ↔ ∃ r ∈ registry, ∃ v ∈ r.check i.tables, Finding.of r v = f := by
  simp [Input.findings]

theorem findings_eq_nil_iff (i : Input) : i.findings = [] ↔ ∀ r ∈ registry, r.check i.tables = [] := by
  simp [Input.findings]

/-- The report of the closed input: it passes exactly when no rule reports a subject. -/
def Input.report (i : Input) : Report :=
  match i.findings with
  | [] => .pass
  | first :: rest => .fail first rest

theorem report_findings (i : Input) : i.report.findings = i.findings := by
  simp only [Input.report]
  cases i.findings <;> rfl

/-- A run passes exactly when no registered rule reports a subject, and otherwise fails: an input of
the closed form is never incomplete. -/
theorem report_pass_iff (i : Input) :
    i.report.verdict = .pass ↔ ∀ r ∈ registry, r.check i.tables = [] := by
  rw [← findings_eq_nil_iff]
  simp only [Input.report]
  cases i.findings <;> simp [Report.verdict]

theorem report_not_incomplete (i : Input) : i.report.verdict ≠ .incomplete := by
  simp only [Input.report]
  cases i.findings <;> simp [Report.verdict]

/-- The report of a run, from what the load gave: a build it cannot read is `incomplete`, and
otherwise the report is `Input.report`. -/
def decision : Except String Input → Report
  | .error why => .incomplete why
  | .ok input => input.report

end Regula.Closed
