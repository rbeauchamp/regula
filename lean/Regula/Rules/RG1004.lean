module

public import Regula.Rule

public section

namespace Regula.Rules.RG1004

open Regula.Closed

def fixGuidance : Guidance :=
  { text := "replace compiler-trusted tactics (native_decide, decide +native, bv_decide) with \
      kernel-checked tactics (decide +kernel, omega, simp, or under the proof verdict only, grind; \
      RG1010 refuses grind in the full gate)"
    nonblank := by simp [Char.isWhitespace] }

def check {i : Input} (t : Tables i) : List Violation :=
  t.claimed.filterMap fun d =>
    let compiler := (t.axiomSet d.name).filter fun a =>
      nativeProofAxiom a || compilerAxioms.contains a
    if !compiler.isEmpty then
      some (violation d s!"depends on the native-proof axioms {compiler}" fixGuidance)
    else none

@[expose] def rule : Rule := { spelling := "RG1004", check := check }

end Regula.Rules.RG1004
