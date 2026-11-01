/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Input
import RegulaSpecification.RuleRecord
import RegulaSpecification.Foundation
import RegulaSpecification.Safety
import RegulaSpecification.Gate
import RegulaSpecification.Language
import RegulaSpecification.Effects
import RegulaSpecification.EffectsRun
import RegulaSpecification.EffectsRecord
import RegulaSpecification.Witnesses
import RegulaSpecification.CasesDeclarations
import RegulaSpecification.CasesFoundation
import RegulaSpecification.CasesGate
import RegulaSpecification.Proofs.Link
import RegulaSpecification.Proofs.Tables
import RegulaSpecification.Proofs.Foundation
import RegulaSpecification.Proofs.Records
import RegulaSpecification.Proofs.Verdict
import RegulaSpecification.Proofs.Load
import RegulaSpecification.Proofs.Occurrences
import RegulaSpecification.Proofs.Language
import RegulaSpecification.Proofs.Effects
import RegulaSpecification.Proofs.ReaderParts
import RegulaSpecification.Proofs.ReaderWalk
import RegulaSpecification.Proofs.ReaderFiles
import RegulaSpecification.Proofs.Reader
import RegulaSpecification.Proofs.ReaderOnly
import RegulaSpecification.Proofs.ReaderFailed
import RegulaSpecification.Proofs.ShellLoad
import RegulaSpecification.Proofs.ShellParts
import RegulaSpecification.Proofs.Shell
import RegulaSpecification.Proofs.Witness
import RegulaSpecification.Proofs.Program
import RegulaSpecification.Proofs.Behaviour
import RegulaSpecification.Proofs.Gate

/-!
# The specification of Regula

Each rule's formal statement, the cases that check each statement in both directions, and the proofs
of the functions that the checker runs against the statements. The document is `README.md` in this
directory.
-/
