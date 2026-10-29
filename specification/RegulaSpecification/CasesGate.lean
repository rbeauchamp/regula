import RegulaSpecification.CasesExecution

/-!
# Cases of RG6001, and lean-intent's obligations for the verdict

RG6001 reads the bundle: its record meets lean-intent's obligations (`rg6001_adequate`), a project
with no record or with a named deliverable that no environment has is refused, and two executables
whose environments each hold one complete deliverable pass (`rg6001_admits_split`). Each
deliverable is named by module and name, so the evidence of one `main` is not evidence of a `main`
in a different module (`rg6001_refuses_bare_evidence`).

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

/-- The parts of the deliverable `x` that a finding can name. -/
def partsOf (b : Bundle) (x : Deliverable) : List (Deliverable × IntentPart) :=
  [(x, .record), (x, .implementation), (x, .obligation .o1), (x, .obligation .o2),
    (x, .obligation .o3), (x, .obligation .o4), (x, .obligation .o5), (x, .obligation .o2Run),
    (x, .obligation .nondegenerate), (x, .dependsOnImplementation), (x, .fulfilment)] ++
    b.confirmed.map fun q => (x, .consequence q.2)

def withoutFulfilment : List Proof :=
  [⟨.obligation .o1 goodDeliverable.record, `Good.t⟩,
    ⟨.obligation .o2 goodDeliverable.record, `Good.t⟩,
    ⟨.obligation .o3 goodDeliverable.record, `Good.t⟩,
    ⟨.obligation .o4 goodDeliverable.record, `Good.t⟩,
    ⟨.obligation .o5 goodDeliverable.record, `Good.t⟩,
    ⟨.obligation .o2Run goodDeliverable.record, `Good.t⟩,
    ⟨.obligation .nondegenerate goodDeliverable.record, `Good.t⟩,
    ⟨.corresponds `Good.f `Good.f._unsafe_rec, `Good.t⟩]

def refused6001 : Bundle := ⟨[{ base with proved := withoutFulfilment }]⟩

theorem base_claimed_f : base.ClaimedConst goodDeliverable.impl :=
  ⟨fDecl, f_mem, rfl, rfl, _, _, base_claims_good⟩

def w6001 : Witnessed Violates6001 where
  support b := (b.inventory.getD []).flatMap (partsOf b) ++ [(noDeliverable, .inventory)]
  support_complete b s h := by
    rcases h with ⟨hmem, hasked, -⟩ | ⟨-, rfl⟩
    · refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨s.1, hmem, ?_⟩)
      obtain ⟨x, part⟩ := s
      cases part with
      | obligation k => cases k <;> simp [partsOf]
      | consequence c =>
        exact List.mem_append_right _ (List.mem_map.mpr ⟨(x.record, c), hasked, rfl⟩)
      | inventory => exact False.elim hasked
      | _ => simp [partsOf]
    · exact List.mem_append_right _ (by simp)
  refused := refused6001
  refused_wf := wf_single (wf_congr wf_base rfl rfl rfl) base_loads base_claims_target
  bad := (goodDeliverable, .fulfilment)
  bad_violates := by
    refine Or.inl ⟨by simp [refused6001, Bundle.inventory, base], trivial, ?_⟩
    rintro ⟨i, hi, -, hp⟩
    simp only [refused6001, List.mem_singleton] at hi
    subst hi
    simp [IntentPart.Holds, Input.ProvedClaimed, withoutFulfilment] at hp
  admitted := baseBundle
  admitted_wf := wf_baseBundle
  fine := (goodDeliverable, .fulfilment)
  fine_admitted := by
    rintro (⟨-, -, h⟩ | ⟨h, -⟩)
    · exact h ⟨base, by simp [baseBundle], base_claimed_f,
        ⟨⟨.fulfils goodDeliverable.impl goodDeliverable.record, `Good.t⟩, by simp [base, proofsOf],
          rfl, base_claimed_t⟩⟩
    · simp [baseBundle, Bundle.inventory, base] at h

theorem rg6001_adequate : O2 rg6001 ∧ O2Run rg6001 ∧ O3 rg6001 ∧ O4 rg6001 ∧
    O5 rg6001 (.rel SameReports) := adequate w6001

theorem rg6001_noisy : ¬ rg6001.Meets w6001.support :=
  noisy_fails w6001 (show (goodDeliverable, IntentPart.fulfilment) ∈
    (baseBundle.inventory.getD []).flatMap (partsOf baseBundle) ++
      [(noDeliverable, IntentPart.inventory)] from
    List.mem_append_left _ (List.mem_flatMap.mpr
      ⟨goodDeliverable, by simp [baseBundle, Bundle.inventory, base], by simp [partsOf]⟩))

/-- A project with no committed confirmation record violates RG6001, so an empty inventory is not
read as one that passes. -/
theorem rg6001_refuses_no_record :
    Violates6001 ⟨[{ base with inventory := none }]⟩ (noDeliverable, .inventory) :=
  Or.inr ⟨rfl, rfl⟩

/-- A deliverable whose implementation `Gone` no environment has. -/
def goneDeliverable : Deliverable := ⟨⟨`Good, `Gone⟩, ⟨`Good, `Good.intent⟩⟩

/-- A deliverable that the owner's record names and that no environment of the project has
violates RG6001. -/
theorem rg6001_refuses_missing :
    Violates6001 ⟨[{ base with inventory := some [goneDeliverable] }]⟩
      (goneDeliverable, .implementation) := by
  refine Or.inl ⟨by simp [Bundle.inventory], trivial, ?_⟩
  rintro ⟨i, hi, ⟨d, hd, hn, -⟩, -⟩
  simp only [List.mem_singleton] at hi
  subst hi
  simp only [base, baseDecls, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [plain, toolchain, helperDecl, goneDeliverable] at hn

/-! ### Two executables, each with a `main` in its own module -/

def splitTargets : List Target :=
  [⟨`appA, .executable, [`AppA], strict, [], true⟩, ⟨`appB, .executable, [`AppB], strict, [], true⟩]

/-- The deliverable of the executable whose root module is `m`: its `main` and the intent record
`m.intent`. -/
def splitDeliverable (m : Name) : Deliverable := ⟨⟨m, `main⟩, ⟨m, Name.str m "intent"⟩⟩

/-- The environment of the executable whose root module is `m`: it loads `m` only, which declares
`main`, its intent record `m.intent`, and the theorem `m.proof` of each statement they need. -/
def splitEnv (m : Name) : Input where
  targets := splitTargets
  manifest :=
    [⟨`appA, .claimed .standardLogical .report⟩, ⟨`appB, .claimed .standardLogical .report⟩]
  modules := [⟨`AppA, [`Init], []⟩, ⟨`AppB, [`Init], []⟩]
  decls := [plain `main m .definition [], plain (Name.str m "intent") m .definition [],
    plain (Name.str m "proof") m .theorem []]
  loads := [m]
  contracts := []
  decisions := []
  decidableResults := []
  inventory := some [splitDeliverable `AppA, splitDeliverable `AppB]
  proved := proofsOf (splitDeliverable m) (Name.str m "proof")
  confirmed := []

def splitBundle : Bundle := ⟨[splitEnv `AppA, splitEnv `AppB]⟩

theorem wf_splitEnv (m : Name) : (splitEnv m).WellFormed := by
  refine ⟨by simp [splitEnv, plain], ?_, ?_⟩
  · intro d hd u hu
    simp only [splitEnv, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> simp [plain] at hu
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
    (hasked : part.Asked [] (splitDeliverable m).record) :
    part.Holds (splitEnv m) (splitDeliverable m) := by
  have proved (g : Goal) (hg : ⟨g, Name.str m "proof"⟩ ∈ (splitEnv m).proved) :
      (splitEnv m).ProvedClaimed g :=
    ⟨_, hg, rfl, plain (Name.str m "proof") m .theorem [], by simp [splitEnv], rfl,
      splitEnv_claimed hm⟩
  cases part with
  | record => exact ⟨plain (Name.str m "intent") m .definition [], by simp [splitEnv], rfl, rfl,
      splitEnv_claimed hm⟩
  | implementation => exact ⟨plain `main m .definition [], by simp [splitEnv], rfl, rfl,
      splitEnv_claimed hm⟩
  | obligation k => exact proved _ (by cases k <;> simp [splitEnv, proofsOf, splitDeliverable])
  | dependsOnImplementation =>
    show ¬ (splitEnv m).Reaches (Name.str m "intent") `main
    intro h
    have := reaches_closed (i := splitEnv m) (fun n => n = Name.str m "intent") (by
      intro d hd _ u hu
      simp only [splitEnv, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> simp [plain] at hu) rfl h
    simp at this
  | consequence c => simp [IntentPart.Asked] at hasked
  | fulfilment => exact proved _ (by simp [splitEnv, proofsOf, splitDeliverable])
  | inventory => trivial

/-- Two executables, each with a `main` in its own module and a complete deliverable that the
environment of the other does not load, form a well-formed bundle that RG6001 admits. -/
theorem rg6001_admits_split :
    splitBundle.WellFormed ∧ `AppA ∉ (splitEnv `AppB).loads ∧ `AppB ∉ (splitEnv `AppA).loads ∧
      (splitDeliverable `AppA).impl.name = (splitDeliverable `AppB).impl.name ∧
      ∀ s, ¬ Violates6001 splitBundle s := by
  refine ⟨wf_splitBundle, by simp [splitEnv], by simp [splitEnv], rfl, ?_⟩
  rintro ⟨x, part⟩ (⟨hx, hasked, hfail⟩ | ⟨h, -⟩)
  · simp [splitBundle, Bundle.inventory, splitEnv] at hx
    rcases hx with rfl | rfl
    · exact hfail ⟨splitEnv `AppA, by simp [splitBundle],
        splitEnv_holds (part := .implementation) (Or.inl rfl) trivial,
        splitEnv_holds (Or.inl rfl) hasked⟩
    · exact hfail ⟨splitEnv `AppB, by simp [splitBundle],
        splitEnv_holds (part := .implementation) (Or.inr rfl) trivial,
        splitEnv_holds (Or.inr rfl) hasked⟩
  · simp [splitBundle, Bundle.inventory, splitEnv] at h

/-! ### Two `main` constants with one intent record in a shared library -/

def sharedTargets : List Target :=
  [⟨`Lib, .library, [`Lib], strict, [], true⟩,
    ⟨`appA, .executable, [`AppA], strict, [], true⟩, ⟨`appB, .executable, [`AppB], strict, [], true⟩]

/-- The intent record `Lib.intent` of the shared library. -/
def libRecord : QualName := ⟨`Lib, `Lib.intent⟩

/-- The deliverable of the executable whose root module is `m`: its `main` and `Lib.intent`. -/
def sharedDeliverable (m : Name) : Deliverable := ⟨⟨m, `main⟩, libRecord⟩

/-- The proofs, by the theorem `Lib.proof`, of each obligation of `Lib.intent`. -/
def libProofs : List Proof :=
  [⟨.obligation .o1 libRecord, `Lib.proof⟩, ⟨.obligation .o2 libRecord, `Lib.proof⟩,
    ⟨.obligation .o3 libRecord, `Lib.proof⟩, ⟨.obligation .o4 libRecord, `Lib.proof⟩,
    ⟨.obligation .o5 libRecord, `Lib.proof⟩, ⟨.obligation .o2Run libRecord, `Lib.proof⟩,
    ⟨.obligation .nondegenerate libRecord, `Lib.proof⟩]

/-- The environment of the executable whose root module is `m`: it loads `Lib`, with the record and
its obligations, and `m`, with `main` and the theorem `m.proof`, which proves `extra`. -/
def sharedEnv (m : Name) (extra : List Proof) : Input where
  targets := sharedTargets
  manifest := [⟨`Lib, .claimed .standardLogical .report⟩,
    ⟨`appA, .claimed .standardLogical .report⟩, ⟨`appB, .claimed .standardLogical .report⟩]
  modules := [⟨`Lib, [`Init], []⟩, ⟨`AppA, [`Init, `Lib], []⟩, ⟨`AppB, [`Init, `Lib], []⟩]
  decls := [plain `Lib.intent `Lib .definition [], plain `Lib.proof `Lib .theorem [],
    plain `main m .definition [], plain (Name.str m "proof") m .theorem []]
  loads := [`Lib, m]
  contracts := []
  decisions := []
  decidableResults := []
  inventory := some [sharedDeliverable `AppA, sharedDeliverable `AppB]
  proved := libProofs ++ extra
  confirmed := []

/-- The environment of `AppA`, which proves that its `main` fulfils `Lib.intent`. -/
def sharedA : Input :=
  sharedEnv `AppA [⟨.fulfils (sharedDeliverable `AppA).impl libRecord, `AppA.proof⟩]

/-- The environment of `AppB`, which proves nothing of its `main`. -/
def sharedB : Input := sharedEnv `AppB []

def sharedBundle : Bundle := ⟨[sharedA, sharedB]⟩

theorem wf_sharedEnv {m : Name} (hm : m = `AppA ∨ m = `AppB) (extra : List Proof) :
    (sharedEnv m extra).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · rcases hm with rfl | rfl <;> simp [sharedEnv, plain]
  · intro d hd u hu
    simp only [sharedEnv, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> simp [plain] at hu
  · intro t ht n hn
    simp only [sharedEnv, sharedTargets, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> simp at hn <;> subst hn <;> simp [sharedEnv]

theorem wf_sharedBundle : sharedBundle.WellFormed where
  nonempty := by simp [sharedBundle]
  each i hi := by
    simp only [sharedBundle, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact wf_sharedEnv (Or.inl rfl) _
    · exact wf_sharedEnv (Or.inr rfl) _
  oneProject i hi j hj := by
    simp only [sharedBundle, List.mem_cons, List.not_mem_nil, or_false] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  covered i hi t ht n hn := by
    have ht' : t ∈ sharedTargets := by
      simp only [sharedBundle, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> exact ht
    simp only [sharedTargets, List.mem_cons, List.not_mem_nil, or_false] at ht'
    rcases ht' with rfl | rfl | rfl <;> simp at hn <;> subst hn
    · exact ⟨sharedA, by simp [sharedBundle], by simp [sharedA, sharedEnv]⟩
    · exact ⟨sharedA, by simp [sharedBundle], by simp [sharedA, sharedEnv]⟩
    · exact ⟨sharedB, by simp [sharedBundle], by simp [sharedB, sharedEnv]⟩
  claims := ⟨sharedA, by simp [sharedBundle], `appA, .standardLogical, .report,
    by simp [sharedA, sharedEnv]⟩

/-- Two executables whose `main` constants share the name `main` and the intent record
`Lib.intent`: the environment of `AppA` holds the fulfilment of its deliverable, which under bare
names would be the entry of `AppB` too. RG6001 still refuses the deliverable of `AppB`, because
its `main` is in `AppB`, and no environment that has it there proves its fulfilment. -/
theorem rg6001_refuses_bare_evidence :
    sharedBundle.WellFormed ∧
      IntentPart.fulfilment.Holds sharedA (sharedDeliverable `AppA) ∧
      (sharedDeliverable `AppA).impl.name = (sharedDeliverable `AppB).impl.name ∧
      (sharedDeliverable `AppA).record = (sharedDeliverable `AppB).record ∧
      Violates6001 sharedBundle (sharedDeliverable `AppB, .fulfilment) := by
  refine ⟨wf_sharedBundle, ⟨⟨.fulfils (sharedDeliverable `AppA).impl libRecord, `AppA.proof⟩,
    by simp [sharedA, sharedEnv], rfl, plain `AppA.proof `AppA .theorem [],
    by simp [sharedA, sharedEnv], rfl, .standardLogical, .report,
    ⟨`appA, .executable, [`AppA], strict, [], true⟩, by simp [sharedA, sharedEnv, sharedTargets],
    by simp [plain], by simp [sharedA, sharedEnv]⟩, rfl, rfl,
    Or.inl ⟨by simp [sharedBundle, Bundle.inventory, sharedA, sharedEnv], trivial, ?_⟩⟩
  rintro ⟨i, hi, ⟨d, hd, hn, hmod, -⟩, q, hq, hs, -⟩
  simp only [sharedBundle, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · simp only [sharedA, sharedEnv, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> simp [plain, sharedDeliverable] at hn hmod
  · simp only [sharedB, sharedEnv, libProofs, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hs

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
