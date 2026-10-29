import RegulaSpecification.RuleRecord

/-!
# The parts of each deliverable's obligations, for the new RG6001

The owner's committed confirmation record names the project's deliverables: an implementation and
the intent record that states what it must do. The project's own code does not name them, so a
project cannot remove an obligation by removing a declaration, and an empty inventory passes only
when the record says so: a project with no record fails. For each named deliverable the rule
requires, from theorems of claimed modules: the implementation and the record exist in claimed
modules; each of lean-intent's obligations O1 to O5, O2 before a run and the degenerate check is
proved of the record; the record does not reach its implementation; each consequence the owner
confirmed or declined is still proved; and the implementation fulfils the record. A finding names
the deliverable and the part that fails.

This module states each part and what makes it hold in one environment (`IntentPart.Holds`). The
rule itself reads the bundle of the run's environments, since an environment holds only the
deliverables of the modules it loads: `Violates6001` in `RegulaSpecification.Gate`.

Here independence is the approximation `¬ Reaches record impl`, and `keeps` and `confirmed` stand
for lean-intent's consequence answers (`LeanIntent.Answers`) and the owner's confirmation record.
lean-intent's cone check (`LeanIntent.Cone`) is stronger than the approximation; #485 replaces
each with lean-intent's own. The order of confirmation and implementation, and the owner's act,
are facts of that record, not of the build.
-/

namespace RegulaSpecification

open Lean (Name)

/-- The part of a deliverable's obligations that a finding names. -/
inductive IntentPart where
  /-- No claimed module declares the intent record. -/
  | record
  /-- No claimed module declares the implementation that the owner's record names. -/
  | implementation
  /-- An obligation of the record is not proved. -/
  | obligation (k : Obligation)
  /-- The record reaches its implementation. -/
  | dependsOnImplementation
  /-- A consequence the owner confirmed or declined is not proved. -/
  | consequence (c : Name)
  /-- No theorem proves that the implementation fulfils the record. -/
  | fulfilment
  /-- The project has no committed confirmation record of the owner. -/
  | inventory
  deriving DecidableEq, Repr

/-- The part `part` of deliverable `(impl, record)` holds in the environment `i`. -/
def IntentPart.Holds (i : Input) (impl record : Name) : IntentPart → Prop
  | .record => i.ClaimedName record
  | .implementation => i.ClaimedName impl
  | .obligation k => Goal.obligation k record ∈ i.proved
  | .dependsOnImplementation => ¬ i.Reaches record impl
  | .consequence c => Goal.keeps record c ∈ i.proved
  | .fulfilment => Goal.fulfils impl record ∈ i.proved
  | .inventory => True

/-- The owner's record asks the part `part` of a deliverable whose intent record is `record`, given
the consequences `answered` that the owner confirmed or declined: each part of the deliverable, and
a consequence only when the owner answered it. The part `inventory` belongs to no deliverable. -/
def IntentPart.Asked (answered : List (Name × Name)) (record : Name) : IntentPart → Prop
  | .consequence c => (record, c) ∈ answered
  | .inventory => False
  | _ => True

end RegulaSpecification
