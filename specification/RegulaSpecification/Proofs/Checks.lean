import RegulaSpecification.Fates
import Regula.Rules
import RegulaCore.Rule

/-!
# What checks each rule, against its fate

`Regula.checkOf` is what `lake exe regula explain` and the rule-reference site state as what checks
a rule (`Regula.Guidance.checkedBy`), and `fate` is what the specification says happens to it.
`checkOf_fate` proves that they agree on each rule, so the registry states the specification's
hand-over of a rule to Lean and its retirement. `check_nil_of_not_lakeLint` proves that a rule that
`lake lint` does not check has no finding, which is why its page and its explanation state no
finding form (`Regula.Guidance.reportForm`).

**What this leaves out.** That the commands named do what the specification's records say is the
subject of the specification's measurements, not of these theorems. The converse of
`check_nil_of_not_lakeLint` does not hold: RG2001 is checked by `lake lint`, and `check` gives it no
finding because `lake lint` reports it as an incomplete run.
-/

namespace RegulaSpecification

namespace Link

/-- The check that a fate names. -/
def checkOfFate : Fate → Regula.RuleCheck
  | .kept => .lakeLint
  | .handedToLean .wfail => .lakeBuild
  | .handedToLean .lakeCheck => .lakeCheck
  | .retired => .retired

/-- The registry's check of each rule is the one that the specification's fate names. -/
theorem checkOf_fate (id : Regula.RuleId) : Regula.checkOf id = checkOfFate (fate id) := by
  cases id <;> rfl

/-- A rule that `lake lint` does not check has no finding in any environment. -/
theorem check_nil_of_not_lakeLint (i : Regula.Closed.Input) (a : Regula.Closed.Allowlists)
    (t : Regula.Closed.Tables) (id : Regula.RuleId)
    (h : Regula.checkOf id ≠ .lakeLint) : i.check a t id = [] := by
  cases id <;> first | rfl | exact absurd rfl h

end Link

end RegulaSpecification
