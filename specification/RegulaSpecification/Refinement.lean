import RegulaSpecification.Rules.RG1002
import RegulaSpecification.Rules.RG1003
import RegulaSpecification.Rules.RG1004
import RegulaSpecification.Rules.RG1005

/-!
# RG1002 to RG1004 refine RG1005

The four rules refine one refusal: each axiom that RG1002, RG1003 or RG1004 names also violates RG1005 for
every profile, so a wrong choice among them changes the reported rule, never the verdict. The statement of what
a pass means in the terms of Lean's environment ({lit}`EnvFloor`, in {lit}`Proofs/Load.lean`) states RG1005 alone
for the first three by these theorems. This module relates rules, so it is no rule's module.
-/

namespace RegulaSpecification

open Lean (Name)

theorem rg1005_of_hole {i : Input} {c : Name} (h : Violates1002 i c) : Violates1005 i c :=
  rg1005_of_known h.1 h.2 (sorry_not_known i)

theorem rg1005_of_unknown {i : Input} {c : Name} (h : Violates1003 i c) : Violates1005 i c := by
  obtain ⟨hc, a, ha, hk, -⟩ := h
  exact rg1005_of_known hc ha hk

theorem rg1005_of_compiler {i : Input} {c : Name} (h : Violates1004 i c) : Violates1005 i c := by
  obtain ⟨hc, a, ha, hn⟩ := h
  refine rg1005_of_known hc ha fun hk => ?_
  rcases hn with hn | hn
  · exact native_not_logical hn hk.1
  · simp [compilerAxioms] at hn

end RegulaSpecification
