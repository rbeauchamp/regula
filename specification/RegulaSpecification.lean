module

public import RegulaSpecification.Input
public import RegulaSpecification.RuleRecord
public import RegulaSpecification.Foundation
public import RegulaSpecification.Witnesses
public import RegulaSpecification.Proofs.Link
public import RegulaSpecification.Proofs.Tables
public import RegulaSpecification.Rule
public import RegulaSpecification.Rules
public import RegulaSpecification.Refinement
public import RegulaSpecification.Gate
public import RegulaSpecification.CasesGate
public import RegulaSpecification.Language
public import RegulaSpecification.Effects
public import RegulaSpecification.EffectsRun
public import RegulaSpecification.EffectsRecord
public import RegulaSpecification.Proofs.Paths
public import RegulaSpecification.Proofs.Floor
public import RegulaSpecification.Proofs.Verdict
public import RegulaSpecification.Proofs.Load
public import RegulaSpecification.Proofs.Written
public import RegulaSpecification.Proofs.Owed
public import RegulaSpecification.Proofs.Occurrences
public import RegulaSpecification.Proofs.Language
public import RegulaSpecification.Proofs.Owner
public import RegulaSpecification.Proofs.Effects
public import RegulaSpecification.Proofs.ReaderParts
public import RegulaSpecification.Proofs.ReaderWalk
public import RegulaSpecification.Proofs.ReaderFiles
public import RegulaSpecification.Proofs.Reader
public import RegulaSpecification.Proofs.ReaderOnly
public import RegulaSpecification.Proofs.ShellLoad
public import RegulaSpecification.Proofs.ShellParts
public import RegulaSpecification.Proofs.Standing
public import RegulaSpecification.Proofs.Shell
public import RegulaSpecification.Proofs.Witness
public import RegulaSpecification.Proofs.Program
public import RegulaSpecification.Proofs.Behaviour
public import RegulaSpecification.Proofs.OwedModel
public import RegulaSpecification.Proofs.EffectScan
public import RegulaSpecification.Proofs.Gate
public import RegulaSpecification.Assumptions
public import RegulaSpecification.Meaning

/-!
# The specification of Regula

Each rule's formal statement, the cases that check each statement in both directions, and the proofs
of the functions that the checker runs against the statements. The document is `README.md` in this
directory.
-/
