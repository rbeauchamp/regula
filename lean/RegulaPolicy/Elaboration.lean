module

public import Regula.Contract
meta import Regula.Decision

/-! # Elaboration record decision

The decision behind the part of RG2003 that a build's messages do not show, for one claimed
module (standard §7.3): the record that Regula's elaboration observer wrote while Lean elaborated
the module (`RegulaObserver.Record`) is complete, the module runs no `#guard_msgs` or
`#guard_panic`, and Lean kept no warning or error out of its output.

`#guard_msgs` drops or checks the messages of the command it runs, so a warning it expects or
drops never reaches the build's output, and Lean runs no linter on a command that contains it.
`#guard_panic` clears every message of its command when one reports a panic. A silent message
(`Lean.Message.isSilent`) is left out of Lean's command-line output, so Lake never logs it. A
command that the observer neither ran on nor saw skipped was not observed. Each of these fails
the module.

## Main declarations

- `Observed`: what the observer recorded of one module.
- `failures`: the executed decision, every failure of one record in a fixed order; no record is
  a failure.
- `failures_eq_nil_iff`: no failure exactly when `Complete` holds.
- `checked_failures`: that equivalence registered as a two-way decision (`Regula.Decides`), with
  an accepted and a refused record.

## Boundaries

The record is read from the module's `.olean` by the operational adapter; these theorems concern
the decision over it, not the observer's reading of Lean's info trees and messages, nor that the
observer ran in the elaboration whose messages the build logged. Positions are compared as Lean
reports them, line and column. -/

@[expose] public section

namespace RegulaPolicy.Elaboration

open Lean (Name)

/-- A position in a module's source: its line and column, as Lean reports them. -/
abbrev Location := Nat × Nat

/-- The severity of a message (`Lean.MessageSeverity`). -/
inductive Severity where
  /-- An information message. -/
  | information
  /-- A warning. -/
  | warning
  /-- An error. -/
  | error
  deriving DecidableEq, Repr

/-- What the observer recorded of one module. -/
structure Observed where
  /-- Where each command before the module's terminal command starts. -/
  commands : List Location
  /-- Where each of those commands starts whose syntax contains `#guard_msgs`; Lean runs no linter
  on it. -/
  skipped : List Location
  /-- Where each command starts that the observer ran on. -/
  linted : List Location
  /-- Each `#guard_msgs` or `#guard_panic` the observer found elaborated, by its syntax kind. -/
  guards : List (Name × Location)
  /-- Each silent message, by its severity. -/
  silent : List (Severity × Location)
  deriving DecidableEq, Repr

/-- One way a module's record fails RG2003. -/
inductive Failure where
  /-- Regula's elaboration observer was not among the plugins Lean loaded for the module, or the
  module's target does not list it in its `needs`, so its record is not read. -/
  | unloaded
  /-- The module's `.olean` holds no complete record. -/
  | absent
  /-- The command at this location contains `#guard_msgs`. -/
  | guardMsgs (location : Location)
  /-- A `#guard_msgs` or `#guard_panic`, by its syntax kind, was elaborated here. -/
  | guard (kind : Name) (location : Location)
  /-- A silent warning or error is here. -/
  | silent (severity : Severity) (location : Location)
  /-- The command at this location was not observed. -/
  | unobserved (location : Location)
  deriving DecidableEq, Repr

/-- Every failure of a module: the observer not loaded, alone, when the audit does not read the
module's record as the running observer's (`loaded` false); otherwise a missing record alone;
otherwise each command that contains `#guard_msgs`, each elaborated guard, each silent warning or
error, and then each command the observer neither ran on nor saw skipped. -/
@[regula_decision]
def failures (loaded : Bool) : Option Observed → List Failure
  | none => if loaded then [.absent] else [.unloaded]
  | some o =>
    if !loaded then [.unloaded] else
    o.skipped.map .guardMsgs ++ o.guards.map (fun g => .guard g.1 g.2) ++
      (o.silent.filter (·.1 != .information)).map (fun s => .silent s.1 s.2) ++
      (o.commands.filter fun c => !o.linted.contains c && !o.skipped.contains c).map .unobserved

/-- The RG2003 obligation on one module's record, stated without the executed decision: Lean
loaded the observer for the module, there is a record, no command contains `#guard_msgs`, no
guard was elaborated, every silent message is an information message, and the observer ran on
every command. -/
def Complete (loaded : Bool) : Option Observed → Prop
  | none => False
  | some o => loaded = true ∧ o.skipped = [] ∧ o.guards = [] ∧
      (∀ s ∈ o.silent, s.1 = .information) ∧ ∀ c ∈ o.commands, c ∈ o.linted

/-- The decision reports no failure exactly when the record meets `Complete`. -/
theorem failures_eq_nil_iff (loaded : Bool) (r : Option Observed) :
    failures loaded r = [] ↔ Complete loaded r := by
  cases r with
  | none => cases loaded <;> simp [failures, Complete]
  | some o =>
    cases loaded
    · simp [failures, Complete]
    simp only [failures, Complete, Bool.not_true, Bool.false_eq_true, ite_false, true_and,
      List.append_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff, bne_iff_ne, ne_eq,
      Decidable.not_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not]
    constructor
    · rintro ⟨⟨⟨hs, hg⟩, hm⟩, hc⟩
      refine ⟨hs, hg, hm, fun c hcm => Classical.byContradiction fun hl => hc c hcm ⟨?_, ?_⟩⟩
      · exact Bool.eq_false_iff.mpr fun h => hl (List.contains_iff_mem.mp h)
      · simp [hs]
    · rintro ⟨hs, hg, hm, hc⟩
      refine ⟨⟨⟨hs, hg⟩, hm⟩, fun c hcm h => ?_⟩
      have hl := List.contains_iff_mem.mpr (hc c hcm)
      rw [h.1] at hl
      exact Bool.false_ne_true hl

/-- `failures` reports nothing exactly for a record that meets `Complete`
(`failures_eq_nil_iff`): nothing for a loaded observer's record of one observed command, and a
failure for no record. -/
theorem checked_failures : Regula.ExecutableContract failures (fun run =>
    Regula.Decides (· = []) (fun input : Bool × Option Observed => Complete input.1 input.2)
      (Function.uncurry run)) :=
  ⟨.of_iff (fun input => failures_eq_nil_iff input.1 input.2)
    ⟨(true, some ⟨[(1, 0)], [], [(1, 0)], [], []⟩), by decide⟩
    ⟨(true, none), by decide⟩⟩

end RegulaPolicy.Elaboration
