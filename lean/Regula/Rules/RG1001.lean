module

public import Regula.Rule

public section

namespace Regula.Rules.RG1001

open Regula.Closed

def fixGuidance : Guidance :=
  { text := "replace the axiom with function parameters, theorem hypotheses, or proof-bearing structure \
      fields so every dependent theorem exposes its assumptions in its type"
    nonblank := by simp [Char.isWhitespace] }

def nativeAxiomGuidance : Guidance :=
  { text := "replace the native-proof tactic (native_decide, decide +native, bv_decide) that generated \
      this axiom with kernel-checked tactics (decide +kernel, omega, simp, or under the proof verdict \
      only, grind; RG1010 refuses grind in the full gate), or if declared directly, replace the axiom \
      with parameters, hypotheses, or structure fields"
    nonblank := by simp [Char.isWhitespace] }

def check {i : Input} (t : Tables i) : List Violation :=
  t.claimed.filterMap fun d =>
    if d.kind == .axiom then
      some (violation d "declares an axiom" (if nativeProofAxiom d.name then nativeAxiomGuidance else fixGuidance))
    else none

@[expose] def rule : Rule := { spelling := "RG1001", check := check }

end Regula.Rules.RG1001
