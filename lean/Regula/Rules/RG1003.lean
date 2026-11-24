module

public import Regula.Rule

public section

namespace Regula.Rules.RG1003

open Regula.Closed

def fixGuidance : Guidance :=
  { text := "remove the dependency on non-standard axioms (replace project axioms with parameters, \
      hypotheses, or structure fields; no Regula profile admits axioms outside toolchain propext, \
      Quot.sound, and Classical.choice)"
    nonblank := by simp [Char.isWhitespace] }

def check {i : Input} (t : Tables i) : List Violation :=
  t.claimed.filterMap fun d =>
    let unknown := (t.axiomSet d.name).filter fun a =>
      !t.known a && a != ``sorryAx && !nativeProofAxiom a && !compilerAxioms.contains a
    if !unknown.isEmpty then
      some (violation d s!"depends on the unknown axioms {unknown}" fixGuidance)
    else none

@[expose] def rule : Rule := { spelling := "RG1003", check := check }

end Regula.Rules.RG1003
