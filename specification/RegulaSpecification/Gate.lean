import RegulaSpecification.Foundation
import RegulaSpecification.Execution
import RegulaSpecification.Contracts
import RegulaSpecification.Project
import RegulaSpecification.Intent

/-!
# The verdict of a run, RG2001, and the new RG6001

Regula's verdict is a closed type with three values. The input of a run is a bundle of loaded
environments (`Bundle`). A build that Lean could not load, or a bundle that the admission refuses,
is `incomplete` (RG2001), never read as absent; an empty claim is refused too. A well-formed bundle
passes exactly when every kept rule and RG2007 hold of each of its environments, and RG6001 holds
of the bundle: the owner's inventory is the project's, and each deliverable is in the environments
that load its module. `gate_o5` proves the record determinate: any two verdict functions that meet
it are equal, so the record leaves nothing unsaid about the verdict.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

/-- The two allowlists the closed subset uses, fixed by #484. -/
structure Allowlists where
  /-- The option names a claimed target may set (RG2006). -/
  options : Name → Prop
  /-- The environment extensions a claimed module may have entries of (RG2007). -/
  extensions : Name → Prop

/-- Every rule that reads one environment holds of the input: each kept rule, and RG2007. -/
def AllHold (a : Allowlists) (i : Input) : Prop :=
  (∀ c, ¬ Violates1001 i c) ∧ (∀ c, ¬ Violates1002 i c) ∧ (∀ c, ¬ Violates1003 i c) ∧
    (∀ c, ¬ Violates1004 i c) ∧ (∀ c, ¬ Violates1005 i c) ∧ (∀ c, ¬ Violates1006 i c) ∧
    (∀ c, ¬ Violates1007 i c) ∧ (∀ c, ¬ Violates1008 i c) ∧ (∀ c, ¬ Violates1009 i c) ∧
    (∀ t, ¬ Violates2002 i t) ∧ (∀ m, ¬ Violates2004 i m) ∧ (∀ t, ¬ Violates2006 a.options i t) ∧
    (∀ m, ¬ Violates2007 a.extensions i m) ∧ (∀ c, ¬ Violates3001 i c) ∧
    (∀ c, ¬ Violates3002 i c)

/-- The verdict of a run. -/
inductive Verdict where
  | pass
  | fail
  | incomplete
  deriving DecidableEq, Repr

/-- The closed input of a run: one `Input` for each environment that the shell loads. A single
environment cannot hold the `main` of two executables, so the libraries and each executable root
are loaded in environments of their own. Each environment carries the same targets, claim, module
records and owner's record, and its own constants and the statements its theorems prove. -/
structure Bundle where
  /-- The loaded environments. -/
  envs : List Input

/-- The admission of a bundle: at least one environment, each well-formed; one project in all of
them, with one owner's record; each module of each target loaded in one of them; and a claim of at
least one target, so that an empty claim is not read as a pass. -/
structure Bundle.WellFormed (b : Bundle) : Prop where
  nonempty : b.envs ≠ []
  each : ∀ i ∈ b.envs, i.WellFormed
  oneProject : ∀ i ∈ b.envs, ∀ j ∈ b.envs,
    i.targets = j.targets ∧ i.manifest = j.manifest ∧ i.modules = j.modules ∧
      i.inventory = j.inventory ∧ i.confirmed = j.confirmed
  covered : ∀ i ∈ b.envs, ∀ t ∈ i.targets, ∀ m ∈ t.modules, ∃ j ∈ b.envs, m ∈ j.loads
  claims : ∃ i ∈ b.envs, ∃ t, i.ClaimedTarget t

instance : Admission Bundle := ⟨Bundle.WellFormed⟩

/-- The deliverables that the owner's record names, as the first environment carries them, or
`none` when the project has no such record. The admission makes them those of each environment. -/
def Bundle.inventory (b : Bundle) : Option (List (Name × Name)) :=
  b.envs.head?.bind (·.inventory)

/-- The owner's confirmed or declined consequences, as the first environment carries them. The
admission makes them those of each environment. -/
def Bundle.confirmed (b : Bundle) : List (Name × Name) :=
  (b.envs.head?.map (·.confirmed)).getD []

/-- The part `part` of deliverable `(impl, record)` fails in the bundle: the owner's record asks
it, and no environment that has `impl` in a claimed module satisfies it. So `implementation` fails
when no environment has `impl` in a claimed module. -/
def IntentPart.Fails (b : Bundle) (impl record : Name) (part : IntentPart) : Prop :=
  part.Asked b.confirmed record ∧ ¬ ∃ i ∈ b.envs, i.ClaimedName impl ∧ part.Holds i impl record

/-- RG6001, new: a part of a deliverable that the owner's record names fails in the bundle, or the
project has no such record. The rule reads the bundle, not one environment, so a deliverable of one
executable is not reported missing from the environment of another. -/
def Violates6001 (b : Bundle) (s : Name × IntentPart) : Prop :=
  (∃ record, (s.1, record) ∈ b.inventory.getD [] ∧ s.2.Fails b s.1 record) ∨
    (b.inventory = none ∧ s = (Name.anonymous, .inventory))

/-- The intent record of RG6001. -/
def rg6001 := ruleRecord "RG6001" Violates6001

/-- Every rule holds: each rule that reads one environment holds of each environment of the
bundle, and RG6001 holds of the bundle. -/
def Bundle.AllHold (a : Allowlists) (b : Bundle) : Prop :=
  (∀ i ∈ b.envs, RegulaSpecification.AllHold a i) ∧ ∀ s, ¬ Violates6001 b s

/-- The intent record of the verdict. `none` is a build Lean could not load. -/
def gateRecord (a : Allowlists) : IntentRecord (Option Bundle → Verdict) where
  shape := .function (Option Bundle) (fun _ => Verdict)
  dom := []
  props := [
    ⟨"RG2001: a build that Lean could not load is incomplete", fun g => g none = .incomplete⟩,
    ⟨"an input the admission refuses is incomplete",
      fun g => ∀ b : Bundle, ¬ b.WellFormed → g (some b) = .incomplete⟩,
    ⟨"a well-formed input is complete, and passes exactly when every rule holds",
      fun g => ∀ b : Bundle, b.WellFormed →
        g (some b) ≠ .incomplete ∧ (g (some b) = .pass ↔ b.AllHold a)⟩]
  vocab := [⟨"well-formed input", Bundle, Bundle.WellFormed⟩]

theorem gate_meets_iff (a : Allowlists) (g : Option Bundle → Verdict) :
    (gateRecord a).Meets g ↔ g none = .incomplete ∧
      (∀ b : Bundle, ¬ b.WellFormed → g (some b) = .incomplete) ∧
      ∀ b : Bundle, b.WellFormed →
        g (some b) ≠ .incomplete ∧ (g (some b) = .pass ↔ b.AllHold a) := by
  simp [IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props, gateRecord]

/-- The verdict is determinate: two verdict functions that meet the record are equal. -/
theorem gate_o5 (a : Allowlists) : O5 (gateRecord a) .eq := by
  rw [o5_correct]
  intro u v hu hv
  have hu' := (gate_meets_iff a u).mp ⟨hu.1, hu.2⟩
  have hv' := (gate_meets_iff a v).mp ⟨hv.1, hv.2⟩
  funext o
  cases o with
  | none => rw [hu'.1, hv'.1]
  | some b =>
    by_cases hb : b.WellFormed
    · obtain ⟨hun, hup⟩ := hu'.2.2 b hb
      obtain ⟨hvn, hvp⟩ := hv'.2.2 b hb
      by_cases hall : b.AllHold a
      · rw [hup.mpr hall, hvp.mpr hall]
      · have h1 : u (some b) ≠ .pass := fun h => hall (hup.mp h)
        have h2 : v (some b) ≠ .pass := fun h => hall (hvp.mp h)
        cases hx : u (some b) <;> cases hy : v (some b) <;> simp_all
    · rw [hu'.2.1 b hb, hv'.2.1 b hb]

/-- O4: the verdict function is total. -/
theorem gate_o4 (a : Allowlists) : O4 (gateRecord a) := o4_function _ rfl

end RegulaSpecification
