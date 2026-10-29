import RegulaSpecification.RuleRecord

/-!
# The lean-intent obligations of each deliverable: the new RG6001

The owner's committed confirmation record names the project's deliverables: an implementation and
the intent record that states what it must do. The project's own code does not name them, so a
project cannot remove an obligation by removing a declaration, and an empty inventory passes only
when the record says so: a project with no record fails. For each named deliverable the rule
requires, from theorems of claimed modules: the implementation and the record exist in claimed
modules; each of lean-intent's obligations O1 to O5, O2 before a run and the degenerate check is
proved of the record; the record does not reach its implementation; each consequence the owner
confirmed or declined is still proved; and the implementation fulfils the record. A finding names
the deliverable and the part that fails.

Here independence is the approximation `¬ Reaches record impl`, and `keeps` and `confirmed` stand
for the statements of lean-intent's consequence ledger and confirmation record; #485 replaces each
with lean-intent's own. The order of confirmation and implementation, and the owner's act, are
facts of that record, not of the build.
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

/-- The part `part` of deliverable `(impl, record)` fails. -/
def IntentPart.Fails (i : Input) (impl record : Name) : IntentPart → Prop
  | .record => ¬ i.ClaimedName record
  | .implementation => ¬ i.ClaimedName impl
  | .obligation k => Goal.obligation k record ∉ i.proved
  | .dependsOnImplementation => i.Reaches record impl
  | .consequence c => (record, c) ∈ i.confirmed ∧ Goal.keeps record c ∉ i.proved
  | .fulfilment => Goal.fulfils impl record ∉ i.proved
  | .inventory => False

/-- RG6001, new: a part of a deliverable that the owner's record names fails, or the project has
no such record. -/
def Violates6001 (i : Input) (s : Name × IntentPart) : Prop :=
  (∃ record, (s.1, record) ∈ i.inventory.getD [] ∧ s.2.Fails i s.1 record) ∨
    (i.inventory = none ∧ s = (Name.anonymous, .inventory))

/-- The intent record of RG6001. -/
def rg6001 := ruleRecord "RG6001" Violates6001

end RegulaSpecification
