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

public section

namespace Regula.Closed

def registry : List Rule :=
  [Regula.Rules.RG1001.rule, Regula.Rules.RG1002.rule, Regula.Rules.RG1003.rule, Regula.Rules.RG1004.rule,
    Regula.Rules.RG1005.rule, Regula.Rules.RG1006.rule, Regula.Rules.RG1011.rule,
    Regula.Rules.RG1012.rule, Regula.Rules.RG1013.rule]

def reservedSpellings : List String := ["RG1010", "RG2001"]

theorem spellings_nodup : (registry.map (·.spelling) ++ reservedSpellings).Nodup := by decide

def Tables.findings {i : Input} (t : Tables i) : List Finding :=
  registry.flatMap fun r => (r.check t).map (Finding.of r)

theorem Tables.mem_findings {i : Input} {t : Tables i} {f : Finding} :
    f ∈ t.findings ↔ ∃ r ∈ registry, ∃ v ∈ r.check t, Finding.of r v = f := by
  simp [Tables.findings]

theorem Tables.findings_eq_nil_iff {i : Input} (t : Tables i) :
    t.findings = [] ↔ ∀ r ∈ registry, r.check t = [] := by
  simp [Tables.findings]

def Input.findings (i : Input) : List Finding :=
  i.tables.findings

theorem mem_findings {i : Input} {f : Finding} :
    f ∈ i.findings ↔ ∃ r ∈ registry, ∃ v ∈ r.check i.tables, Finding.of r v = f :=
  Tables.mem_findings

theorem findings_eq_nil_iff (i : Input) : i.findings = [] ↔ ∀ r ∈ registry, r.check i.tables = [] :=
  Tables.findings_eq_nil_iff i.tables

def Tables.report {i : Input} (t : Tables i) : Report :=
  match t.findings with
  | [] => .pass
  | first :: rest => .fail first rest

theorem Tables.report_findings {i : Input} (t : Tables i) : t.report.findings = t.findings := by
  simp only [Tables.report]
  cases t.findings <;> rfl

theorem Tables.report_pass_iff {i : Input} (t : Tables i) :
    t.report.verdict = .pass ↔ ∀ r ∈ registry, r.check t = [] := by
  rw [← Tables.findings_eq_nil_iff]
  simp only [Tables.report]
  cases t.findings <;> simp [Report.verdict]

theorem Tables.report_not_incomplete {i : Input} (t : Tables i) : t.report.verdict ≠ .incomplete := by
  simp only [Tables.report]
  cases t.findings <;> simp [Report.verdict]

def Input.report (i : Input) : Report :=
  i.tables.report

theorem report_findings (i : Input) : i.report.findings = i.findings :=
  Tables.report_findings i.tables

theorem report_pass_iff (i : Input) :
    i.report.verdict = .pass ↔ ∀ r ∈ registry, r.check i.tables = [] :=
  Tables.report_pass_iff i.tables

theorem report_not_incomplete (i : Input) : i.report.verdict ≠ .incomplete :=
  Tables.report_not_incomplete i.tables

def decisionPrepared : Except String Prepared → Report
  | .error why => .incomplete why
  | .ok p => p.tables.report

def decision (r : Except String Input) : Report :=
  decisionPrepared (r.map fun i => ⟨i, i.tables⟩)

theorem decisionPrepared_eq {r : Except String Prepared}
    (ht : ∀ p, r = .ok p → p.tables = p.input.tables) :
    decisionPrepared r = decision (r.map (·.input)) := by
  cases r with
  | error why => rfl
  | ok p =>
    simp only [decisionPrepared, decision, Except.map, ht p rfl]

end Regula.Closed
