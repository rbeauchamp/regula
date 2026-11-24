module

public import Regula.Rule

public section

namespace Regula.Rules.RG1005

open Regula.Closed

def kernelOnlyChoiceFreeGuidance : Guidance :=
  { text := "remove the dependency on logical axioms to stay within kernel-only, or run with \
      choice-free (propext, Quot.sound) or standard-logical (also Classical.choice) if intended"
    nonblank := by simp [Char.isWhitespace] }

def kernelOnlyChoiceGuidance : Guidance :=
  { text := "remove the dependency on logical axioms to stay within kernel-only, or run with \
      standard-logical if Classical.choice is intended (choice-free also refuses Classical.choice; \
      to avoid it, supply constructive Decidable instances or take [Decidable p] parameters \
      instead of Classical.propDecidable)"
    nonblank := by simp [Char.isWhitespace] }

def choiceFreeGuidance : Guidance :=
  { text := "avoid Classical.choice (supply constructive Decidable instances, take [Decidable p] \
      parameters instead of Classical.propDecidable, or write constructive proofs) to stay within \
      choice-free, or run with standard-logical if classical choice is intended"
    nonblank := by simp [Char.isWhitespace] }

def unprofiledGuidance : Guidance :=
  { text := "remove the dependency on axioms outside the configured profile (kernel-only, choice-free, \
      or standard-logical); sorryAx, native-proof, and non-standard axioms are refused by every profile"
    nonblank := by simp [Char.isWhitespace] }

def profileGuidance {i : Input} (t : Tables i) (excess : List Lean.Name) : Guidance :=
  match i.profile with
  | .kernelOnly =>
    if excess.all (t.admits .choiceFree) then kernelOnlyChoiceFreeGuidance
    else if excess.all (t.admits .standardLogical) then kernelOnlyChoiceGuidance
    else unprofiledGuidance
  | .choiceFree =>
    if excess.all (t.admits .standardLogical) then choiceFreeGuidance
    else unprofiledGuidance
  | .standardLogical => unprofiledGuidance

def check {i : Input} (t : Tables i) : List Violation :=
  t.claimed.filterMap fun d =>
    let excess := (t.axiomSet d.name).filter (!t.admits i.profile ·)
    if !excess.isEmpty then
      some (violation d s!"depends on {excess}, outside the profile" (profileGuidance t excess))
    else none

@[expose] def rule : Rule := { spelling := "RG1005", check := check }

end Regula.Rules.RG1005
