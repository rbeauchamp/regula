import RegulaSpecification.Input
import RegulaSpecification.RuleRecord
import RegulaSpecification.Foundation
import RegulaSpecification.Witnesses
import RegulaSpecification.Proofs.Link
import RegulaSpecification.Proofs.Tables
import RegulaSpecification.Rule
import RegulaSpecification.Rules
import RegulaSpecification.Refinement
import RegulaSpecification.Gate
import RegulaSpecification.CasesGate
import RegulaSpecification.Language
import RegulaSpecification.Effects
import RegulaSpecification.EffectsRun
import RegulaSpecification.EffectsRecord
import RegulaSpecification.Proofs.Paths
import RegulaSpecification.Proofs.Floor
import RegulaSpecification.Proofs.Verdict
import RegulaSpecification.Proofs.Load
import RegulaSpecification.Proofs.Written
import RegulaSpecification.Proofs.Owed
import RegulaSpecification.Proofs.Occurrences
import RegulaSpecification.Proofs.Language
import RegulaSpecification.Proofs.Owner
import RegulaSpecification.Proofs.Effects
import RegulaSpecification.Proofs.ReaderParts
import RegulaSpecification.Proofs.ReaderWalk
import RegulaSpecification.Proofs.ReaderFiles
import RegulaSpecification.Proofs.Reader
import RegulaSpecification.Proofs.ReaderOnly
import RegulaSpecification.Proofs.ShellLoad
import RegulaSpecification.Proofs.ShellParts
import RegulaSpecification.Proofs.Standing
import RegulaSpecification.Proofs.Shell
import RegulaSpecification.Proofs.Witness
import RegulaSpecification.Proofs.Program
import RegulaSpecification.Proofs.Behaviour
import RegulaSpecification.Proofs.OwedModel
import RegulaSpecification.Proofs.EffectScan
import RegulaSpecification.Proofs.Gate
import RegulaSpecification.Assumptions
import RegulaSpecification.Meaning

/-!
# The specification of Regula

Each rule's formal statement, the cases that check each statement in both directions, and the proofs
of the functions that the checker runs against the statements. The document is `README.md` in this
directory.
-/
