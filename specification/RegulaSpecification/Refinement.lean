module

public import RegulaSpecification.Rules.RG1002
public import RegulaSpecification.Rules.RG1003
public import RegulaSpecification.Rules.RG1004
public import RegulaSpecification.Rules.RG1005

@[expose] public section

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
