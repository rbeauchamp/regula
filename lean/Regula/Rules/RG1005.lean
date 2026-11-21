module

public import Regula.Rule

/-!
# RG1005: the profile

A constant of a claimed module depends on an axiom that the project's profile does not admit.
`specification/RegulaSpecification/Rules/RG1005.lean` states the rule and proves this check against it.
-/

public section

namespace Regula.Rules.RG1005

open Regula.Closed

/-- Fix guidance when excess axioms are known logical axioms outside `kernel-only`. -/
def kernelOnlyGuidance : Guidance :=
  { text := "remove the dependency on logical axioms to stay within kernel-only, or run with \
      choice-free (propext, Quot.sound) or standard-logical (also Classical.choice) if intended"
    nonblank := by simp [Char.isWhitespace] }

/-- Fix guidance when excess axioms are known logical axioms outside `choice-free` (`Classical.choice`). -/
def choiceFreeGuidance : Guidance :=
  { text := "avoid Classical.choice (for example use Decidable instead of Classical.dec or constructive \
      proofs) to stay within choice-free, or run with standard-logical if classical choice is intended"
    nonblank := by simp [Char.isWhitespace] }

/-- Fix guidance when excess axioms include axioms outside all Regula profiles. -/
def unprofiledGuidance : Guidance :=
  { text := "remove the dependency on axioms outside the configured profile (kernel-only, choice-free, \
      or standard-logical); sorryAx, native-proof, and non-standard axioms are refused by every profile"
    nonblank := by simp [Char.isWhitespace] }

/-- Fix guidance tailored to the configured profile and whether every excess axiom is a known logical axiom. -/
def profileGuidance {i : Input} (t : Tables i) (excess : List Lean.Name) : Guidance :=
  if excess.all t.known then
    match i.profile with
    | .kernelOnly => kernelOnlyGuidance
    | .choiceFree => choiceFreeGuidance
    | .standardLogical => unprofiledGuidance
  else unprofiledGuidance

/-- The constants of claimed modules that depend on an axiom that the project's profile does not
admit. -/
def check {i : Input} (t : Tables i) : List Violation :=
  t.claimed.filterMap fun d =>
    let excess := (t.axiomSet d.name).filter (!t.admits i.profile ·)
    if !excess.isEmpty then
      some (violation d s!"depends on {excess}, outside the profile" (profileGuidance t excess))
    else none

/-- RG1005, for the registry. Its body is exposed so that the registry reads its spelling (`Regula.Closed.spellings_nodup`). -/
@[expose] def rule : Rule := { spelling := "RG1005", check := check }

end Regula.Rules.RG1005
