import RegulaSpecification.CasesExecution

/-!
# Cases of RG6001, and lean-intent's obligations for the verdict

RG6001 reads the bundle: its record meets lean-intent's obligations (`rg6001_adequate`), a project
with no record or with a named deliverable that no environment has is refused, and two executables
whose environments each hold one complete deliverable pass (`rg6001_admits_split`).

The record of the verdict meets O2, O2 before a run, O3 and O4, and O5 with equality
(`gate_o5`): it determines the verdict of each input. The checker that always passes and the
checker that is always incomplete each fail it. A bundle with no environment, or with a claim of
no target, is refused (`no_claim_refused`).
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Witnesses

/-- An input the admission refuses: two constants with one name. -/
def duplicated : Input := withDecls [plain `Good.t `Good .theorem []]

theorem not_wf_duplicated : ¬ duplicated.WellFormed := by
  intro h
  have := h.unique
  simp [duplicated, withDecls, base, baseDecls, plain, toolchain, helperDecl] at this

/-- A bundle of one environment is well-formed when the environment is, loads each module of its
targets, and claims a target. -/
theorem wf_single {i : Input} (hi : i.WellFormed)
    (hl : ∀ t ∈ i.targets, ∀ m ∈ t.modules, m ∈ i.loads) (hc : ∃ t, i.ClaimedTarget t) :
    (⟨[i]⟩ : Bundle).WellFormed where
  nonempty := by simp
  each j hj := by
    simp only [List.mem_singleton] at hj
    subst hj
    exact hi
  oneProject j hj k hk := by
    simp only [List.mem_singleton] at hj hk
    subst hj hk
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  covered j hj t ht m hm := by
    simp only [List.mem_singleton] at hj
    subst hj
    exact ⟨j, by simp, hl t ht m hm⟩
  claims := ⟨i, by simp, hc⟩

theorem base_loads : ∀ t ∈ base.targets, ∀ m ∈ t.modules, m ∈ base.loads := by
  intro t ht m hm
  simp only [base, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> simp at hm <;> simp [base, hm]

theorem base_claims_target : ∃ t, base.ClaimedTarget t := ⟨`Good, .choiceFree, .report, by simp [base]⟩

/-- The compliant project, loaded in one environment. -/
def baseBundle : Bundle := ⟨[base]⟩

theorem wf_baseBundle : baseBundle.WellFormed := wf_single wf_base base_loads base_claims_target

/-! ## RG6001 -/

/-- The parts of a deliverable that a finding can name. -/
def partsOf (b : Bundle) (f : Name) : List (Name × IntentPart) :=
  [(f, .record), (f, .implementation), (f, .obligation .o1), (f, .obligation .o2),
    (f, .obligation .o3), (f, .obligation .o4), (f, .obligation .o5), (f, .obligation .o2Run),
    (f, .obligation .nondegenerate), (f, .dependsOnImplementation), (f, .fulfilment)] ++
    b.confirmed.map fun q => (f, .consequence q.2)

def withoutFulfilment : List Goal :=
  [.obligation .o1 `Good.intent, .obligation .o2 `Good.intent, .obligation .o3 `Good.intent,
    .obligation .o4 `Good.intent, .obligation .o5 `Good.intent, .obligation .o2Run `Good.intent,
    .obligation .nondegenerate `Good.intent, .corresponds `Good.f]

def refused6001 : Bundle := ⟨[{ base with proved := withoutFulfilment }]⟩

theorem base_claimed_f : base.ClaimedName `Good.f :=
  ⟨plain `Good.f `Good .definition [], by simp [base, baseDecls], rfl, _, _, base_claims_good⟩

def w6001 : Witnessed Violates6001 where
  support b := (b.inventory.getD []).flatMap (fun p => partsOf b p.1) ++
    [(Name.anonymous, .inventory)]
  support_complete b s h := by
    rcases h with ⟨record, hmem, hasked, -⟩ | ⟨-, rfl⟩
    · refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨(s.1, record), hmem, ?_⟩)
      obtain ⟨f, part⟩ := s
      cases part with
      | obligation k => cases k <;> simp [partsOf]
      | consequence c =>
        exact List.mem_append_right _ (List.mem_map.mpr ⟨(record, c), hasked, rfl⟩)
      | inventory => exact False.elim hasked
      | _ => simp [partsOf]
    · exact List.mem_append_right _ (by simp)
  refused := refused6001
  refused_wf := wf_single (wf_congr wf_base rfl rfl rfl) base_loads base_claims_target
  bad := (`Good.f, .fulfilment)
  bad_violates := by
    refine Or.inl ⟨`Good.intent, by simp [refused6001, Bundle.inventory, base], trivial, ?_⟩
    rintro ⟨i, hi, -, hp⟩
    simp only [refused6001, List.mem_singleton] at hi
    subst hi
    simp [IntentPart.Holds, withoutFulfilment] at hp
  admitted := baseBundle
  admitted_wf := wf_baseBundle
  fine := (`Good.f, .fulfilment)
  fine_admitted := by
    rintro (⟨r, hr, -, h⟩ | ⟨h, -⟩)
    · simp [baseBundle, Bundle.inventory, base] at hr
      subst hr
      exact h ⟨base, by simp [baseBundle], base_claimed_f, by simp [IntentPart.Holds, base]⟩
    · simp [baseBundle, Bundle.inventory, base] at h

theorem rg6001_adequate : O2 rg6001 ∧ O2Run rg6001 ∧ O3 rg6001 ∧ O4 rg6001 ∧
    O5 rg6001 (.rel SameReports) := adequate w6001

theorem rg6001_noisy : ¬ rg6001.Meets w6001.support :=
  noisy_fails w6001 (show ((`Good.f : Name), IntentPart.fulfilment) ∈
    (baseBundle.inventory.getD []).flatMap (fun p => partsOf baseBundle p.1) ++
      [(Name.anonymous, IntentPart.inventory)] from
    List.mem_append_left _ (List.mem_flatMap.mpr
      ⟨(`Good.f, `Good.intent), by simp [baseBundle, Bundle.inventory, base], by simp [partsOf]⟩))

/-- A project with no committed confirmation record violates RG6001, so an empty inventory is not
read as one that passes. -/
theorem rg6001_refuses_no_record :
    Violates6001 ⟨[{ base with inventory := none }]⟩ (Name.anonymous, .inventory) :=
  Or.inr ⟨rfl, rfl⟩

/-- A deliverable that the owner's record names and that no environment of the project has
violates RG6001. -/
theorem rg6001_refuses_missing :
    Violates6001 ⟨[{ base with inventory := some [(`Gone, `Good.intent)] }]⟩
      (`Gone, .implementation) := by
  refine Or.inl ⟨`Good.intent, by simp [Bundle.inventory], trivial, ?_⟩
  rintro ⟨i, hi, ⟨d, hd, hn, -⟩, -⟩
  simp only [List.mem_singleton] at hi
  subst hi
  simp only [base, baseDecls, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [plain, toolchain, helperDecl] at hn

/-! ### Two executables, each with a deliverable that the other does not load -/

def splitTargets : List Target :=
  [⟨`appA, .executable, [`AppA], strict, [], true⟩, ⟨`appB, .executable, [`AppB], strict, [], true⟩]

/-- The statements that the deliverable with implementation `f` and intent record `r` needs. -/
def proofsOf (f r : Name) : List Goal :=
  [.obligation .o1 r, .obligation .o2 r, .obligation .o3 r, .obligation .o4 r, .obligation .o5 r,
    .obligation .o2Run r, .obligation .nondegenerate r, .fulfils f r]

/-- The environment of the executable whose root module is `m`: it loads `m` only, which declares
the implementation `m.run` and its intent record `m.intent` and proves each statement they need. -/
def splitEnv (m : Name) : Input where
  targets := splitTargets
  manifest :=
    [⟨`appA, .claimed .standardLogical .report⟩, ⟨`appB, .claimed .standardLogical .report⟩]
  modules := [⟨`AppA, [`Init], []⟩, ⟨`AppB, [`Init], []⟩]
  decls := [plain (Name.str m "run") m .definition [], plain (Name.str m "intent") m .definition []]
  loads := [m]
  contracts := []
  decisions := []
  decidableResults := []
  inventory := some [(`AppA.run, `AppA.intent), (`AppB.run, `AppB.intent)]
  proved := proofsOf (Name.str m "run") (Name.str m "intent")
  confirmed := []

def splitBundle : Bundle := ⟨[splitEnv `AppA, splitEnv `AppB]⟩

theorem wf_splitEnv (m : Name) : (splitEnv m).WellFormed := by
  refine ⟨by simp [splitEnv, plain], ?_, ?_⟩
  · intro d hd u hu
    simp only [splitEnv, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> simp [plain] at hu
  · intro t ht n hn
    simp only [splitEnv, splitTargets, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp at hn <;> subst hn <;> simp [splitEnv]

theorem wf_splitBundle : splitBundle.WellFormed where
  nonempty := by simp [splitBundle]
  each i hi := by
    simp only [splitBundle, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> exact wf_splitEnv _
  oneProject i hi j hj := by
    simp only [splitBundle, List.mem_cons, List.not_mem_nil, or_false] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  covered i hi t ht n hn := by
    have ht' : t ∈ splitTargets := by
      simp only [splitBundle, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> exact ht
    simp only [splitTargets, List.mem_cons, List.not_mem_nil, or_false] at ht'
    rcases ht' with rfl | rfl <;> simp at hn <;> subst hn
    · exact ⟨splitEnv `AppA, by simp [splitBundle], by simp [splitEnv]⟩
    · exact ⟨splitEnv `AppB, by simp [splitBundle], by simp [splitEnv]⟩
  claims := ⟨splitEnv `AppA, by simp [splitBundle], `appA, .standardLogical, .report,
    by simp [splitEnv]⟩

theorem splitEnv_claimed {m : Name} (hm : m = `AppA ∨ m = `AppB) :
    (splitEnv m).ClaimedModule m := by
  rcases hm with rfl | rfl
  · exact ⟨.standardLogical, .report, ⟨`appA, .executable, [`AppA], strict, [], true⟩,
      by simp [splitEnv, splitTargets], by simp, by simp [splitEnv]⟩
  · exact ⟨.standardLogical, .report, ⟨`appB, .executable, [`AppB], strict, [], true⟩,
      by simp [splitEnv, splitTargets], by simp, by simp [splitEnv]⟩

/-- In the environment of `m`, each part that the owner's record asks of the deliverable of `m`
holds. -/
theorem splitEnv_holds {m : Name} (hm : m = `AppA ∨ m = `AppB) {part : IntentPart}
    (hasked : part.Asked [] (Name.str m "intent")) :
    part.Holds (splitEnv m) (Name.str m "run") (Name.str m "intent") := by
  have claimed (s : String) (hs : s = "run" ∨ s = "intent") :
      (splitEnv m).ClaimedName (Name.str m s) := by
    rcases hs with rfl | rfl
    · exact ⟨plain (Name.str m "run") m .definition [], by simp [splitEnv], rfl,
        splitEnv_claimed hm⟩
    · exact ⟨plain (Name.str m "intent") m .definition [], by simp [splitEnv], rfl,
        splitEnv_claimed hm⟩
  cases part with
  | record => exact claimed "intent" (Or.inr rfl)
  | implementation => exact claimed "run" (Or.inl rfl)
  | obligation k => cases k <;> simp [IntentPart.Holds, splitEnv, proofsOf]
  | dependsOnImplementation =>
    show ¬ (splitEnv m).Reaches (Name.str m "intent") (Name.str m "run")
    intro h
    have := reaches_closed (i := splitEnv m) (fun n => n = Name.str m "intent") (by
      intro d hd _ u hu
      simp only [splitEnv, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> simp [plain] at hu) rfl h
    simp at this
  | consequence c => simp [IntentPart.Asked] at hasked
  | fulfilment => simp [IntentPart.Holds, splitEnv, proofsOf]
  | inventory => trivial

/-- Two executables whose environments each hold one complete deliverable, which the environment
of the other does not load, form a well-formed bundle that RG6001 admits: the rule reads the
bundle, so neither deliverable is reported missing. -/
theorem rg6001_admits_split :
    splitBundle.WellFormed ∧ `AppA ∉ (splitEnv `AppB).loads ∧ `AppB ∉ (splitEnv `AppA).loads ∧
      ∀ s, ¬ Violates6001 splitBundle s := by
  refine ⟨wf_splitBundle, by simp [splitEnv], by simp [splitEnv], ?_⟩
  rintro ⟨f, part⟩ (⟨r, hr, hasked, hfail⟩ | ⟨h, -⟩)
  · simp [splitBundle, Bundle.inventory, splitEnv] at hr
    rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hfail ⟨splitEnv `AppA, by simp [splitBundle],
        splitEnv_holds (part := .implementation) (Or.inl rfl) trivial,
        splitEnv_holds (Or.inl rfl) hasked⟩
    · exact hfail ⟨splitEnv `AppB, by simp [splitBundle],
        splitEnv_holds (part := .implementation) (Or.inr rfl) trivial,
        splitEnv_holds (Or.inr rfl) hasked⟩
  · simp [splitBundle, Bundle.inventory, splitEnv] at h

/-- A bundle with an environment that the admission refuses. -/
def duplicatedBundle : Bundle := ⟨[duplicated]⟩

theorem not_wf_duplicatedBundle : ¬ duplicatedBundle.WellFormed :=
  fun h => not_wf_duplicated (h.each duplicated (by simp [duplicatedBundle]))

/-- A project whose claim excludes each target is refused, so an empty claim is no pass. -/
theorem no_claim_refused :
    ¬ (⟨[{ base with manifest := [⟨`Good, .excluded⟩, ⟨`app, .excluded⟩] }]⟩ : Bundle).WellFormed := by
  rintro ⟨-, -, -, -, i, hi, t, p, e, he⟩
  simp only [List.mem_singleton] at hi
  subst hi
  simp at he

open Classical in
/-- A verdict function that meets the record. -/
noncomputable def verdictOf (a : Allowlists) : Option Bundle → Verdict
  | none => .incomplete
  | some b => if b.WellFormed then (if b.AllHold a then .pass else .fail) else .incomplete

theorem verdictOf_meets (a : Allowlists) : (gateRecord a).Meets (verdictOf a) := by
  rw [gate_meets_iff]
  refine ⟨rfl, fun b hb => by simp [verdictOf, hb], fun b hb => ?_⟩
  by_cases hall : b.AllHold a <;> simp [verdictOf, hb, hall]

/-- The checker that always passes misses the build that Lean could not load. -/
theorem always_pass_fails (a : Allowlists) : ¬ (gateRecord a).Meets (fun _ => .pass) := by
  rw [gate_meets_iff]
  exact fun h => absurd h.1 (by decide)

/-- The checker that is always incomplete refuses each well-formed input. -/
theorem always_incomplete_fails (a : Allowlists) :
    ¬ (gateRecord a).Meets (fun _ => .incomplete) := by
  rw [gate_meets_iff]
  exact fun h => (h.2.2 baseBundle wf_baseBundle).1 rfl

theorem gate_adequate (a : Allowlists) :
    O2 (gateRecord a) ∧ O2Run (gateRecord a) ∧ O3 (gateRecord a) ∧ O4 (gateRecord a) ∧
      O5 (gateRecord a) .eq := by
  refine ⟨?_, o2Run_of_meets (verdictOf_meets a), ?_, gate_o4 a, gate_o5 a⟩
  · rw [o2_correct]
    refine ⟨⟨verdictOf a, by simp [gateRecord]⟩, ?_⟩
    intro p hp
    simp only [gateRecord, List.mem_singleton] at hp
    subst hp
    exact ⟨baseBundle, wf_baseBundle⟩
  · rw [o3_correct]
    intro p hp
    simp only [gateRecord, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨fun _ => .pass, by decide⟩
    · exact ⟨fun _ => .pass,
        fun h => absurd (h duplicatedBundle not_wf_duplicatedBundle) (by decide)⟩
    · exact ⟨fun _ => .incomplete, fun h => (h baseBundle wf_baseBundle).1 rfl⟩

end Witnesses

end RegulaSpecification
