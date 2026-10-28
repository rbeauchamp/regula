import RegulaSpecification.RuleRecord

/-!
# The lean-intent obligations of each deliverable: the new RG6001

A project declares its deliverables: an implementation and the intent record that states what it
must do. For each one the rule requires, from theorems of claimed modules: the record exists in a
claimed module; each of lean-intent's obligations O1 to O5 is proved of it; the record does not
reach its implementation; each consequence the owner confirmed or declined is still proved; and
the implementation fulfils the record. A finding names the deliverable and the part that fails.

lean-intent's port states O1 to O5 and the refinement link. It does not yet state the cone check
(lean-intent #2), the consequence ledger (lean-intent #3) or the owner's confirmation record
(lean-intent #5). Here independence is the approximation `¬ Reaches record impl`, and `keeps` and
`confirmed` stand for the statements those issues will define; #485 replaces each with
lean-intent's own when it exists.
-/

namespace RegulaSpecification

open Lean (Name)

/-- The part of a deliverable's obligations that a finding names. -/
inductive IntentPart where
  /-- No claimed module declares the intent record. -/
  | record
  /-- An obligation of the record is not proved. -/
  | obligation (k : Obligation)
  /-- The record reaches its implementation. -/
  | dependsOnImplementation
  /-- A consequence the owner confirmed or declined is not proved. -/
  | consequence (c : Name)
  /-- No theorem proves that the implementation fulfils the record. -/
  | fulfilment
  deriving DecidableEq, Repr

/-- The part `part` of deliverable `(impl, record)` fails. -/
def IntentPart.Fails (i : Input) (impl record : Name) : IntentPart → Prop
  | .record => ¬ i.ClaimedName record
  | .obligation k => Goal.obligation k record ∉ i.proved
  | .dependsOnImplementation => i.Reaches record impl
  | .consequence c => (record, c) ∈ i.confirmed ∧ Goal.keeps record c ∉ i.proved
  | .fulfilment => Goal.fulfils impl record ∉ i.proved

/-- RG6001, new: a part of a declared deliverable's obligations fails. -/
def Violates6001 (i : Input) (s : Name × IntentPart) : Prop :=
  ∃ record, (s.1, record) ∈ i.deliverables ∧ s.2.Fails i s.1 record

/-- The intent record of RG6001. -/
def rg6001 := ruleRecord "RG6001" Violates6001

end RegulaSpecification
