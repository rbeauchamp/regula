import RegulaSpecification.Proofs.Records

/-!
# The verdict, against its statement

`Regula.Closed.Input.refusal?` is the admission that the checker runs, and `Regula.Closed.run` its
verdict. `refusal_none_iff` proves that the admission refuses exactly an input that the specification's
`Input.WellFormed` refuses, or one that lacks the axiom set of a claimed constant. `run_refused` and
`run_complete` then state the verdict: a refused input is `incomplete`, and an admitted one is `pass`
or `fail`, and `pass` exactly when every rule holds of it. `run_meets` states that as the record
`gateRecord` over the specification's input.

That the shell (`Regula.Load`) fills the input through Lean's and Lake's interfaces is not proved, and
neither is its refusal of a build that it cannot load (`Regula.Shell.run`, the record's first
property, which `runChecker` reads as `none`).
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Link

theorem duplicate_none (seen : Std.HashSet Name) (l : List Name) :
    Regula.Closed.Input.duplicate? seen l = none ↔
      l.Nodup ∧ ∀ x ∈ l, seen.contains x = false := by
  induction l generalizing seen with
  | nil => simp [Regula.Closed.Input.duplicate?]
  | cons a l ih =>
    rw [Regula.Closed.Input.duplicate?]
    by_cases ha : seen.contains a = true
    · rw [ite_eq_left ha]
      constructor
      · intro h
        cases h
      · rintro ⟨-, h⟩
        have := h a (List.mem_cons_self ..)
        rw [ha] at this
        cases this
    · rw [ite_eq_right ha, ih, List.nodup_cons]
      have ha' : seen.contains a = false := by simpa using ha
      constructor
      · rintro ⟨hnd, hl⟩
        refine ⟨⟨fun hm => ?_, hnd⟩, fun x hx => ?_⟩
        · have := hl a hm
          simp [Std.HashSet.contains_insert] at this
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact ha'
          · have := hl x hx
            simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff] at this
            exact this.2
      · rintro ⟨⟨hm, hnd⟩, hl⟩
        refine ⟨hnd, fun x hx => ?_⟩
        have hb : (a == x) = false := by simpa using fun (h : a = x) => hm (h ▸ hx)
        simp [Std.HashSet.contains_insert, hb, hl x (List.mem_cons_of_mem _ hx)]

/-- The first constant without an axiom set is none exactly when each claimed constant has one. -/
theorem axiomsMissing_none (i : Regula.Closed.Input) :
    i.axiomsMissing? = none ↔
      ∀ d ∈ i.decls, (toSpec i).ClaimedModule d.module → d.axioms.isSome = true := by
  unfold Regula.Closed.Input.axiomsMissing?
  simp only [Option.map_eq_none_iff, List.find?_eq_none, Bool.and_eq_true,
    Option.isNone_iff_eq_none, not_and, claimed_contains]
  constructor
  · intro h d hd hm
    cases hx : d.axioms with
    | some _ => rfl
    | none => exact absurd hm (h d hd hx)
  · intro h d hd hn hm
    have := h d hd hm
    simp [hn] at this

theorem openMention_none (i : Regula.Closed.Input) :
    i.openMention? = none ↔ ∀ d ∈ (toSpec i).decls, ∀ u ∈ d.uses, (toSpec i).Resolves u := by
  have hnames : ∀ u, (Regula.Closed.setOf (i.decls.map (·.name))).contains u = true ↔
      (toSpec i).Resolves u := by
    intro u
    rw [mem_setOf, resolves_iff]
    simp
  unfold Regula.Closed.Input.openMention?
  simp only [List.findSome?_eq_none_iff, Option.map_eq_none_iff, List.find?_eq_none]
  constructor
  · intro h x hx u hu
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    exact (hnames u).mp (by simpa using h d hd u hu)
  · intro h d hd u hu
    have := (hnames u).mpr (h (decl d) (mem_decls.mpr ⟨d, hd, rfl⟩) u hu)
    simp [this]

theorem unloaded_none (i : Regula.Closed.Input) :
    i.unloaded? = none ↔ ∀ m ∈ (toSpec i).modules, m ∈ (toSpec i).loads := by
  unfold Regula.Closed.Input.unloaded?
  simp only [List.find?_eq_none, Bool.not_eq_true', Bool.not_eq_false]
  constructor
  · intro h m hm
    exact (mem_setOf i.loads m).mp (by simpa using h m hm)
  · intro h m hm
    have := (mem_setOf i.loads m).mpr (h m hm)
    simp [this]

end Link

open Link

/-- What the admission decides: it refuses nothing exactly when the input has the closed form and each
claimed constant has its axiom set. -/
theorem refusal_none_iff (i : Regula.Closed.Input) :
    i.refusal? = none ↔ (toSpec i).WellFormed ∧ i.axiomsMissing? = none := by
  have hunique : Regula.Closed.Input.duplicate? {} (i.decls.map (·.name)) = none ↔
      ((toSpec i).decls.map (·.name)).Nodup := by
    rw [duplicate_none, names_toSpec]
    simp
  have hclaims : i.modules.isEmpty = false ↔ (toSpec i).modules ≠ [] := by
    simp [toSpec]
  have hwf : (toSpec i).WellFormed ↔
      Regula.Closed.Input.duplicate? {} (i.decls.map (·.name)) = none ∧ i.openMention? = none ∧
        i.modules.isEmpty = false ∧ i.unloaded? = none := by
    rw [hunique, openMention_none, hclaims, unloaded_none]
    exact ⟨fun h => ⟨h.unique, h.closed, h.claims, h.loaded⟩,
      fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩
  rw [hwf]
  unfold Regula.Closed.Input.refusal?
  split
  · rename_i h
    simp [h]
  · rename_i h1
    split
    · rename_i h2
      simp [h2]
    · rename_i h2
      split
      · rename_i h3
        simp [h3]
      · rename_i h3
        split
        · rename_i h4
          simp [h4]
        · rename_i h4
          split
          · rename_i h5
            simp [h5]
          · rename_i h5
            simp [h1, h2, h3, h4, h5]

theorem nil_iff_no_subject (fs : List Regula.Closed.Finding) :
    fs = [] ↔ ∀ s, s ∉ fs.map (·.subject) := by
  cases fs with
  | nil => simp
  | cons f fs =>
    constructor
    · intro h
      cases h
    · intro h
      exact absurd (List.mem_cons_self ..) (h f.subject)

/-- An admitted input has no finding exactly when every rule holds of it. -/
theorem findings_nil_iff {i : Regula.Closed.Input} (h : Admitted i) :
    i.findings = [] ↔ AllHold (toSpec i) := by
  have hu := unique_of_wf h.wf
  have hall : i.findings = [] ↔ ∀ r, i.tables.check r = [] := by
    simp only [Regula.Closed.Input.findings, List.flatMap_eq_nil_iff]
    exact ⟨fun h r => h r (Regula.RuleId.mem_all r), fun h r _ => h r⟩
  rw [hall]
  constructor
  · intro hn
    have at' : ∀ r s, s ∉ (i.tables.check r).map (·.subject) :=
      fun r => (nil_iff_no_subject _).mp (hn r)
    exact ⟨fun c hv => at' .projectAxiom c ((rg1001_exact i c).mpr hv),
      fun c hv => at' .proofHole c ((rg1002_exact h c).mpr hv),
      fun c hv => at' .unknownAxiom c ((rg1003_exact h c).mpr hv),
      fun c hv => at' .nativeProof c ((rg1004_exact h c).mpr hv),
      fun c hv => at' .profileExceeded c ((rg1005_exact h c).mpr hv),
      fun c hv => at' .escapeHatch c ((rg1006_exact hu c).mpr hv)⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩ r
    refine (nil_iff_no_subject _).mpr fun s hs => ?_
    cases r
    · exact h1 s ((rg1001_exact i s).mp hs)
    · exact h2 s ((rg1002_exact h s).mp hs)
    · exact h3 s ((rg1003_exact h s).mp hs)
    · exact h4 s ((rg1004_exact h s).mp hs)
    · exact h5 s ((rg1005_exact h s).mp hs)
    · exact h6 s ((rg1006_exact hu s).mp hs)
    · simp [Regula.Closed.Tables.check] at hs

/-- An input that the admission refuses is `incomplete`: a part of the input that cannot be read is
never a pass and never an empty report. -/
theorem run_refused {i : Regula.Closed.Input} (h : i.refusal? ≠ none) :
    (Regula.Closed.run i).1 = .incomplete := by
  unfold Regula.Closed.run
  split
  · rfl
  · contradiction

/-- An admitted input is not `incomplete`, and it is `pass` exactly when every rule holds of it. -/
theorem run_complete {i : Regula.Closed.Input} (h : Admitted i) :
    (Regula.Closed.run i).1 ≠ .incomplete ∧
      ((Regula.Closed.run i).1 = .pass ↔ AllHold (toSpec i)) := by
  have hnone : i.refusal? = none :=
    (refusal_none_iff i).mpr ⟨h.wf, (axiomsMissing_none i).mpr h.axioms.present⟩
  unfold Regula.Closed.run
  rw [hnone]
  simp only
  constructor
  · split <;> simp
  · rw [← findings_nil_iff h]
    cases i.findings <;> simp

/-- A pass of the checker is an admitted input: an input that the admission refuses is never a
pass. -/
theorem run_pass_admitted {i : Regula.Closed.Input} (hp : (Regula.Closed.run i).1 = .pass) :
    i.refusal? = none := by
  cases hr : i.refusal? with
  | none => rfl
  | some why =>
    have := run_refused (i := i) (by simp [hr])
    rw [this] at hp
    cases hp

/-- A pass of the checker holds each rule, when the axiom sets of the input are the ones that `AxiomOf`
states. -/
theorem run_pass_holds {i : Regula.Closed.Input} (hax : AxiomsRead i)
    (hp : (Regula.Closed.run i).1 = .pass) : AllHold (toSpec i) :=
  (run_complete ⟨((refusal_none_iff i).mp (run_pass_admitted hp)).1, hax⟩).2.mp hp

/-- The verdict of the checker in the specification. -/
def verdict : Regula.Closed.Verdict → Verdict
  | .pass => .pass
  | .fail => .fail
  | .incomplete => .incomplete

/-- The checker's verdict over the specification's input, with `none` for a build that the shell
cannot load. -/
noncomputable def runChecker : Option Input → Verdict
  | none => .incomplete
  | some s => verdict (Regula.Closed.run (ofSpec s)).1

/-- The checker's verdict meets the record of the verdict. -/
theorem run_meets : gateRecord.Meets runChecker := by
  rw [gate_meets_iff]
  refine ⟨rfl, fun s hs => ?_, fun s hs => ?_⟩
  · have hr : (ofSpec s).refusal? ≠ none := fun hn => hs (by
      have := ((refusal_none_iff _).mp hn).1
      rwa [toSpec_ofSpec] at this)
    simp [runChecker, run_refused hr, verdict]
  · obtain ⟨hn, hp⟩ := run_complete (admitted_ofSpec hs)
    rw [toSpec_ofSpec] at hp
    simp only [runChecker]
    constructor
    · cases hv : (Regula.Closed.run (ofSpec s)).1 <;> simp_all [verdict]
    · rw [← hp]
      cases (Regula.Closed.run (ofSpec s)).1 <;> simp [verdict]

/-- Regula's checks are exactly RG1001 to RG1006 and RG2001. -/
theorem rule_spellings :
    Regula.RuleId.all.map (·.spelling) =
      ["RG1001", "RG1002", "RG1003", "RG1004", "RG1005", "RG1006", "RG2001"] := rfl

end RegulaSpecification
