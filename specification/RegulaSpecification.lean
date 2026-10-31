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

/-!
# The specification of Regula

Each rule's formal statement, the cases that check each statement in both directions, and the proofs
of the functions that the checker runs against the statements. The document is `README.md` in this
directory.
-/
