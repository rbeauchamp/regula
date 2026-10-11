/-
Positive control for the assumptions that the audit reports (`Regula.Assumption`). `twice_adds`
takes the assumption `Increments` about a modelled counter as a hypothesis, `unfolded_adds` writes
that hypothesis out and uses it through the proof of `twice_adds`, and `checked_reads` names the
checked operation `checkedStep` in its statement. The audit records, for each declaration, the
assumptions and the checked operations that the walk of the constants it uses reaches from it, and
prints them in its record (`assumptions=`, `checked=`).
-/
import Regula.Assumption

namespace Fixtures.RestsOnAssumption

structure Counter where
  State : Type
  read : State → Nat
  step : State → State

@[regula_assumption filesystem (document filesystem "control: no external system")]
def Increments (c : Counter) : Prop := ∀ s, c.read (c.step s) = c.read s + 1

def twice (c : Counter) (s : c.State) : c.State := c.step (c.step s)

theorem twice_adds (c : Counter) (increments : Increments c) (s : c.State) :
    c.read (twice c s) = c.read s + 2 := by
  unfold twice
  rw [increments, increments]

theorem unfolded_adds (c : Counter) (h : ∀ s, c.read (c.step s) = c.read s + 1) (s : c.State) :
    c.read (twice c s) = c.read s + 2 :=
  twice_adds c h s

def checkedStep (c : Counter) (s : c.State) : Option c.State :=
  if c.read (c.step s) = c.read s + 1 then some (c.step s) else none

theorem checkedStep_reads (c : Counter) (s t : c.State) (h : checkedStep c s = some t) :
    c.read t = c.read s + 1 := by
  unfold checkedStep at h
  split at h
  · cases h; assumption
  · cases h

attribute [regula_checked filesystem checkedStep_reads
  (document filesystem "control: no external system")] checkedStep

theorem checked_reads (c : Counter) (s t : c.State) (h : checkedStep c s = some t) :
    c.read t = c.read s + 1 :=
  checkedStep_reads c s t h

end Fixtures.RestsOnAssumption
