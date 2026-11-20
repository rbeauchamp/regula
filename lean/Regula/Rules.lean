module

public import Regula.Rules.RG1001
public import Regula.Rules.RG1002
public import Regula.Rules.RG1003
public import Regula.Rules.RG1004
public import Regula.Rules.RG1005
public import Regula.Rules.RG1006
public import Regula.Rules.RG1011
public import Regula.Rules.RG1012
public import Regula.Rules.RG1013

/-!
# The registry of the rules

The one list of the rules that a run applies, and the report of a run: the findings of each registered
rule, in the order of the list, and a pass exactly when no registered rule reports a subject
(`report_pass_iff`). Adding a rule is a module of its own below `Regula/Rules/` and one line of
`registry`, with its statement in `specification/RegulaSpecification/Rules/` and one line of the
specification's registry, which `specification/RegulaSpecification/Rules.lean` proves equal to this one.

RG1010, the language check (`Regula.Language`), and RG2001, the refusal of a build that the checker cannot
read, are no rules of this list: neither is a function from a closed input to its subjects. RG1010 reads
source files before a build, and RG2001 is the run in which the rules are given no input.
-/

public section

namespace Regula.Closed

/-- The rules that a run applies, in the order of their findings. -/
def registry : List Rule :=
  [Regula.Rules.RG1001.rule, Regula.Rules.RG1002.rule, Regula.Rules.RG1003.rule, Regula.Rules.RG1004.rule,
    Regula.Rules.RG1005.rule, Regula.Rules.RG1006.rule, Regula.Rules.RG1011.rule,
    Regula.Rules.RG1012.rule, Regula.Rules.RG1013.rule]

/-- The codes that no rule of the registry may take: the language check's and the environment's. -/
def reservedSpellings : List String := ["RG1010", "RG2001"]

/-- Each spelling names one check, so a finding's code names the rule that reports it. -/
theorem spellings_nodup : (registry.map (·.spelling) ++ reservedSpellings).Nodup := by decide

/-- Every finding of the input, read through its tables `t`, in the order of the registry. -/
def Tables.findings {i : Input} (t : Tables i) : List Finding :=
  registry.flatMap fun r => (r.check t).map (Finding.of r)

theorem Tables.mem_findings {i : Input} {t : Tables i} {f : Finding} :
    f ∈ t.findings ↔ ∃ r ∈ registry, ∃ v ∈ r.check t, Finding.of r v = f := by
  simp [Tables.findings]

theorem Tables.findings_eq_nil_iff {i : Input} (t : Tables i) :
    t.findings = [] ↔ ∀ r ∈ registry, r.check t = [] := by
  simp [Tables.findings]

/-- Every finding of the input: the findings of each registered rule, in the order of the registry. -/
def Input.findings (i : Input) : List Finding :=
  i.tables.findings

theorem mem_findings {i : Input} {f : Finding} :
    f ∈ i.findings ↔ ∃ r ∈ registry, ∃ v ∈ r.check i.tables, Finding.of r v = f :=
  Tables.mem_findings

theorem findings_eq_nil_iff (i : Input) : i.findings = [] ↔ ∀ r ∈ registry, r.check i.tables = [] :=
  Tables.findings_eq_nil_iff i.tables

/-- The report of the closed input, read through its tables `t`: it passes exactly when no rule
reports a subject. -/
def Tables.report {i : Input} (t : Tables i) : Report :=
  match t.findings with
  | [] => .pass
  | first :: rest => .fail first rest

theorem Tables.report_findings {i : Input} (t : Tables i) : t.report.findings = t.findings := by
  simp only [Tables.report]
  cases t.findings <;> rfl

/-- A run over `t` passes exactly when no registered rule reports a subject, and otherwise fails: an
input of the closed form is never incomplete. -/
theorem Tables.report_pass_iff {i : Input} (t : Tables i) :
    t.report.verdict = .pass ↔ ∀ r ∈ registry, r.check t = [] := by
  rw [← Tables.findings_eq_nil_iff]
  simp only [Tables.report]
  cases t.findings <;> simp [Report.verdict]

theorem Tables.report_not_incomplete {i : Input} (t : Tables i) : t.report.verdict ≠ .incomplete := by
  simp only [Tables.report]
  cases t.findings <;> simp [Report.verdict]

/-- The report of the closed input: it passes exactly when no rule reports a subject. -/
def Input.report (i : Input) : Report :=
  i.tables.report

theorem report_findings (i : Input) : i.report.findings = i.findings :=
  Tables.report_findings i.tables

/-- A run passes exactly when no registered rule reports a subject, and otherwise fails: an input of
the closed form is never incomplete. -/
theorem report_pass_iff (i : Input) :
    i.report.verdict = .pass ↔ ∀ r ∈ registry, r.check i.tables = [] :=
  Tables.report_pass_iff i.tables

theorem report_not_incomplete (i : Input) : i.report.verdict ≠ .incomplete :=
  Tables.report_not_incomplete i.tables

/-- The report of a load that gave a closed input or an error: a build it cannot read is `incomplete`,
and otherwise the report is `Input.report`. A run evaluates `decisionPrepared`, which
`decisionPrepared_eq` proves equal to this when the prepared tables are `Input.tables`. -/
def decision : Except String Input → Report
  | .error why => .incomplete why
  | .ok input => input.report

/-- The report of a run, from a prepared load: a build it cannot read is `incomplete`, and
otherwise the report is `Tables.report` on the prepared tables. -/
def decisionPrepared : Except String Prepared → Report
  | .error why => .incomplete why
  | .ok p => p.tables.report

theorem decisionPrepared_eq {r : Except String Prepared}
    (ht : ∀ p, r = .ok p → p.tables = p.input.tables) :
    decisionPrepared r = decision (r.map (·.input)) := by
  cases r with
  | error why => rfl
  | ok p =>
    simp only [decisionPrepared, Except.map, decision, Input.report, ht p rfl]

end Regula.Closed
