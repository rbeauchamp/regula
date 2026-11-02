/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.ShellParts

/-!
# What a whole run does

`run_meets` is the theorem the shell exists for: for every argument list and every response of Lean, Lake and the
operating system, a run of `Regula.Shell.run`, the program the `lint` executable interprets, does what
`RegulaSpecification.Effects.RunMeets` states.
-/

namespace RegulaSpecification.Effects

open Lean (Name)
open System (FilePath)
open Regula.Effect
open Regula.Reader
open Regula.Shell
open Regula.Language
open RegulaSpecification.Language

variable {L E : Type}

/-! ## The check -/

theorem quiet_of_saying {t : List (Event L E)} (h : ∀ e ∈ t, e.isOnlySaying = true) : Quiet t := by
  intro e he
  have hs := h e he
  obtain ⟨op, response⟩ := e
  cases op <;> first | trivial | cases hs

/-- What `check` decides rests on what the reader read, after a prefix that only observes and that holds the toolchain's answer; its acts are the
grammar's; an admission received no failed answer; and it builds nothing, loads no build for the rules, removes nothing and prints only details. -/
theorem check_spec {prior t : List (Event L E)} {sysroot : String} {dir tree : FilePath} {o : Outcome}
    (hq : Quiet prior) (hps : SysrootIs prior sysroot)
    (h : Runs (check sysroot dir tree : Prog L E Outcome) t o) :
    Decided (prior ++ t) dir tree o ∧ ReadingPreparation (prior ++ t) dir tree ∧ (o = .admitted → Clean t) ∧
      (∀ e ∈ t, e.isBuild = false ∧ e.isImportForRules = false ∧ NotRemoving e.op) ∧ (∀ l ∈ printed t, IsDetail l) := by
  unfold check at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  have hI : t₁ <:+: prior ++ (t₁ ++ t₂) := ⟨prior, t₂, by simp⟩
  have hsys : SysrootIs (prior ++ (t₁ ++ t₂)) sysroot := by simpa [SysrootIs] using .inl hps
  obtain ⟨g1, g2, g3⟩ := read_spec hI hsys hq hps h₁
  have honly := only_readProject (L := L) (E := E) sysroot dir tree _ _ h₁
  have hprinted₁ : printed t₁ = [] := by
    have hn : t₁.filterMap Event.line? = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro e he
      have := honly e he
      obtain ⟨o', r'⟩ := e
      cases o' <;> first | rfl | exact this.elim
    simp [printed, hn]
  have hrest : ∀ {t' : List (Event L E)}, Details t' →
      (∀ e ∈ t₁ ++ t', e.isBuild = false ∧ e.isImportForRules = false ∧ NotRemoving e.op) ∧
        (∀ l ∈ printed (t₁ ++ t'), IsDetail l) := by
    intro t' hd
    refine ⟨fun e he => ?_, fun l hl => ?_⟩
    · rcases List.mem_append.mp he with he | he
      · have := honly e he
        obtain ⟨o', r'⟩ := e
        cases o' <;> first | exact ⟨rfl, rfl, trivial⟩ | exact this.elim
      · have := hd.1 e he
        obtain ⟨o', r'⟩ := e
        cases o' <;> first | exact ⟨rfl, rfl, trivial⟩ | cases this
    · rw [printed_append, hprinted₁] at hl
      exact hd.2 l (by simpa using hl)
  have hprep : ∀ {t' : List (Event L E)}, Details t' → ReadingPreparation (prior ++ (t₁ ++ t')) dir tree := fun hd => by
    simpa [List.append_assoc] using g3.appendQuiet (quiet_of_saying hd.1)
  cases r with
  | error why =>
    obtain ⟨t₃, t₄, u, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
    obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₄
    have hd := say_spec h₃
    have : Details (t₃ ++ ([] : List (Event L E))) := by simpa using hd
    exact ⟨⟨fun he => (by cases he), fun _ => g2 ⟨why, rfl⟩, .inr rfl⟩, hprep this, fun he => (by cases he), hrest this⟩
  | ok x =>
    obtain ⟨reading, lines⟩ := x
    obtain ⟨t₃, t₄, u, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
    obtain ⟨t₅, t₆, u', rfl, h₅, h₆⟩ := runs_seq_iff.mp h₄
    obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₆
    have hd : Details (t₃ ++ (t₅ ++ ([] : List (Event L E)))) := by
      simpa using details_append (sayAll_spec h₃) (say_spec h₅)
    obtain ⟨g4, g5⟩ := g1 reading lines rfl
    have hsay : ∀ e ∈ t₃ ++ (t₅ ++ ([] : List (Event L E))), e.acted? = none := fun e he => acted_of_saying (hd.1 e he)
    have hstands : ∀ p, written (prior ++ (t₁ ++ (t₃ ++ (t₅ ++ [])))) p = written t₁ p := by
      intro p
      rw [written_after_no_acts hq.noActs p]
      exact written_before_no_acts hsay p
    have hback : decision reading = .admitted → ∃ real, (⟨.realPath tree, .ok real⟩ : Event L E) ∈ prior ++ (t₁ ++ (t₃ ++ (t₅ ++ []))) ∧
        ReadBack (prior ++ (t₁ ++ (t₃ ++ (t₅ ++ [])))) real := by
      intro ha
      obtain ⟨real, hm, hb⟩ := (g4 ha).2.1
      refine ⟨real, by simp [hm], ReadBack.prepend_no_acts hq.noActs (ReadBack.append_quiet hb (quiet_of_saying hd.1) ?_)⟩
      intro e he
      exact keeps_of_no_acts (hsay e he)
    refine ⟨⟨fun ha => ⟨reading, (hback ha).choose, (decision_admitted_iff reading).mp ha, (g4 ha).1 _ hstands, (hback ha).choose_spec.1, (hback ha).choose_spec.2⟩,
      fun hne => g5 _ rfl hne, .inl ⟨reading, rfl⟩⟩, hprep hd, fun ho => ?_, hrest hd⟩
    exact (g4 ho).2.2.append (fun e he => not_failed_of_saying (hd.1 e he))

/-! ## The build -/

/-- One Lake command in the tree. -/
theorem lake_spec {program tree : FilePath} {args : List String} {t : List (Event L E)} {b : Bool}
    (h : Runs (lake program tree args : Prog L E Bool) t b) :
    ∃ pre r post, t = pre ++ ⟨.runLake program tree args, r⟩ :: post ∧ Details pre ∧ Details post ∧
      (b = true ↔ r = .ok 0) := by
  unfold lake at h
  obtain ⟨t₁, t₂, u, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  obtain ⟨t₃, t₄, v, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
  obtain rfl := runs_call_iff.mp h₃
  obtain ⟨t₅, t₆, r, rfl, h₅, h₆⟩ := runs_seq_iff.mp h₄
  obtain rfl := runs_call_iff.mp h₅
  have hpre : Details (t₁ ++ [⟨.flush, v⟩]) := by
    refine details_append (say_spec h₁) ⟨fun e he => ?_, fun l hl => ?_⟩
    · have : e = _ := List.mem_singleton.mp he
      subst this
      rfl
    · simp [printed, Event.line?] at hl
  refine ⟨t₁ ++ [⟨.flush, v⟩], r, t₆, by simp, hpre, ?_⟩
  cases r with
  | ok code =>
    obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₆
    refine ⟨details_nil, ?_⟩
    constructor
    · intro hc
      have : code = 0 := by simpa using hc
      rw [this]
    · intro he
      cases he
      rfl
  | error e =>
    obtain ⟨t₇, t₈, u', rfl, h₇, h₈⟩ := runs_seq_iff.mp h₆
    obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₈
    exact ⟨by simpa using say_spec h₇, by simp⟩

/-- Every execution of the actual build function follows the closed build protocol, including a failed
spawn or nonzero child exit. Reporting is the only work between the identified commands. -/
theorem buildAndReplay_protocol {sysroot : String} {tree : FilePath} {t : List (Event L E)} {b : Bool}
    (h : Runs (buildAndReplay sysroot tree : Prog L E Bool) t b) : BuildProtocol sysroot tree t := by
  unfold buildAndReplay at h
  obtain ⟨t₁, t₂, x, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  obtain rfl := runs_call_iff.mp h₁
  obtain ⟨program, lakeLib⟩ := x
  dsimp only at h₂
  obtain ⟨first, rest, c, rfl, hfirst, hrest⟩ := runs_seq_iff.mp h₂
  obtain ⟨pre, r, post, ht, hpre, hpost, hc⟩ := lake_spec hfirst
  refine ⟨program, lakeLib, first, rest, r, rfl, ⟨pre, post, ht, hpre.1, hpost.1⟩, ?_⟩
  cases c with
  | false =>
    obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp hrest
    exact .inl ⟨fun hr => by simpa using hc.mpr hr, rfl⟩
  | true =>
    rw [ite_eq_left rfl] at hrest
    have hr : Runs (lake program tree replayArguments : Prog L E Bool) rest b := hrest
    obtain ⟨pre', r', post', ht', hpre', hpost', -⟩ := lake_spec hr
    exact .inr ⟨hc.mp rfl, r', pre', post', ht', hpre'.1, hpost'.1⟩

/-- What the events of a build are. -/
def BuildEvents (t : List (Event L E)) (tree : FilePath) : Prop :=
  (∀ e ∈ t, e.isImportForRules = false) ∧ (∀ l ∈ printed t, IsDetail l) ∧
    ∀ e ∈ t, ∀ p, e.acted? = some p → p = tree

theorem buildEvents_append {a b : List (Event L E)} {tree : FilePath} (ha : BuildEvents a tree)
    (hb : BuildEvents b tree) : BuildEvents (a ++ b) tree := by
  refine ⟨fun e he => ?_, fun l hl => ?_, fun e he p hp => ?_⟩
  · rcases List.mem_append.mp he with he | he
    · exact ha.1 e he
    · exact hb.1 e he
  · rw [printed_append] at hl
    rcases List.mem_append.mp hl with hl | hl
    · exact ha.2.1 l hl
    · exact hb.2.1 l hl
  · rcases List.mem_append.mp he with he | he
    · exact ha.2.2 e he p hp
    · exact hb.2.2 e he p hp

theorem buildEvents_of_details {t : List (Event L E)} {tree : FilePath} (h : Details t) :
    BuildEvents t tree := by
  refine ⟨fun e he => ?_, h.2, fun e he p hp => ?_⟩
  · have := h.1 e he
    obtain ⟨o', r'⟩ := e
    cases o' <;> first | rfl | cases this
  · rw [acted_of_saying (h.1 e he)] at hp
    cases hp

theorem buildEvents_lake {program tree : FilePath} {args : List String} {r}
    {pre post : List (Event L E)} (hpre : Details pre) (hpost : Details post) :
    BuildEvents (pre ++ ⟨.runLake program tree args, r⟩ :: post) tree := by
  have hmid : BuildEvents ([⟨.runLake program tree args, r⟩] : List (Event L E)) tree := by
    refine ⟨fun e he => ?_, fun l hl => ?_, fun e he p hp => ?_⟩
    · have : e = _ := List.mem_singleton.mp he
      subst this
      rfl
    · simp [printed, Event.line?] at hl
    · have : e = _ := List.mem_singleton.mp he
      subst this
      cases hp
      rfl
  have := buildEvents_append (buildEvents_append (buildEvents_of_details (tree := tree) hpre) hmid)
    (buildEvents_of_details (tree := tree) hpost)
  simpa using this

/-- What a `Details` holds is no failure. -/
theorem details_not_failed {t : List (Event L E)} (h : Details t) : ∀ e ∈ t, ¬ e.failed :=
  fun e he => not_failed_of_saying (h.1 e he)

/-- `buildAndReplay` passes only on both Lake commands ending with 0, and a command that did not end with 0 rejects the
build. -/
theorem buildAndReplay_spec {sysroot : String} {tree : FilePath} {t : List (Event L E)} {b : Bool}
    (h : Runs (buildAndReplay sysroot tree : Prog L E Bool) t b) :
    BuildEvents t tree ∧
      (b = true → (∃ program lakeLib,
        ([⟨.lakeInstall sysroot, (program, lakeLib)⟩, ⟨.runLake program tree ["build", "--wfail"], .ok 0⟩,
          ⟨.runLake program tree replayArguments, .ok 0⟩] : List (Event L E)).Sublist t) ∧ ∀ e ∈ t, ¬ e.failed) ∧
      (b = false → BuildRejected sysroot tree t) := by
  unfold buildAndReplay at h
  obtain ⟨t₁, t₂, x, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  obtain rfl := runs_call_iff.mp h₁
  obtain ⟨program, lakeLib⟩ := x
  dsimp only at h₂
  obtain ⟨t₃, t₄, c, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
  obtain ⟨pre, r, post, rfl, d1, d2, hc⟩ := lake_spec h₃
  have hinstall : BuildEvents ([⟨.lakeInstall sysroot, (program, lakeLib)⟩] : List (Event L E)) tree := by
    refine ⟨fun e he => ?_, fun l hl => ?_, fun e he p hp => ?_⟩
    · have : e = _ := List.mem_singleton.mp he
      subst this
      rfl
    · simp [printed, Event.line?] at hl
    · have : e = _ := List.mem_singleton.mp he
      subst this
      cases hp
  have hfirst := buildEvents_lake (program := program) (tree := tree) (args := ["build", "--wfail"]) (r := r) d1 d2
  cases c with
  | false =>
    obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₄
    refine ⟨by simpa using buildEvents_append hinstall hfirst, fun he => (by cases he), fun _ => ?_⟩
    exact .build (program := program) (lakeLib := lakeLib) (r := r) (by simp) (by simp)
      (fun he => by simpa using hc.mpr he)
  | true =>
    have hr : r = .ok 0 := hc.mp rfl
    subst hr
    rw [ite_eq_left rfl] at h₄
    have h₄' : Runs (lake program tree replayArguments : Prog L E Bool) t₄ b := h₄
    obtain ⟨pre₂, r₂, post₂, rfl, d3, d4, hc₂⟩ := lake_spec h₄'
    have hevents := buildEvents_lake (program := program) (tree := tree) (args := replayArguments) (r := r₂) d3 d4
    refine ⟨?_, fun he => ⟨?_, ?_⟩, fun he => ?_⟩
    · have := buildEvents_append (buildEvents_append hinstall hfirst) hevents
      simpa using this
    · have hr₂ := hc₂.mp he
      subst hr₂
      refine ⟨program, lakeLib, ?_⟩
      simp only [List.cons_append, List.nil_append, List.append_assoc]
      refine List.Sublist.cons_cons _ ?_
      refine List.Sublist.trans ?_ (List.sublist_append_right pre _)
      refine List.Sublist.cons_cons _ ?_
      refine List.Sublist.trans ?_ (List.sublist_append_right post _)
      refine List.Sublist.trans ?_ (List.sublist_append_right pre₂ _)
      exact List.Sublist.cons_cons _ (List.nil_sublist _)
    · have hr₂ := hc₂.mp he
      subst hr₂
      intro e hm
      simp only [List.cons_append, List.nil_append, List.append_assoc, List.mem_cons, List.mem_append] at hm
      rcases hm with rfl | hm | rfl | hm | hm | rfl | hm
      · exact id
      · exact details_not_failed d1 _ hm
      · exact fun hn => hn rfl
      · exact details_not_failed d2 _ hm
      · exact details_not_failed d3 _ hm
      · exact fun hn => hn rfl
      · exact details_not_failed d4 _ hm
    · refine .replay (program := program) (lakeLib := lakeLib) (r := r₂) (by simp) (by simp) (by simp) fun hr₂ => ?_
      have := hc₂.mpr hr₂
      rw [he] at this
      cases this

/-! ## The loads print nothing -/

/-- An operation that the loads may ask: none prints, builds, makes or removes anything. -/
def LoadOp : Op L E → Prop
  | .runLake .. | .println _ | .flush | .createTempDir | .removeDirAll _ | .leanVersion | .writeFile ..
  | .createDirAll _ => False
  | _ => True

theorem only_inputOf (root : Root L) (p : Regula.Closed.Profile) :
    OnlyAIn LoadOp (inputOf root p : Attempt L E _) := by
  have hdefault : ∀ targets, OnlyAIn LoadOp (defaultModules root targets : Attempt L E _) := by
    intro targets
    induction targets with
    | nil => rw [defaultModules]; exact onlyA_pure _
    | cons t ts ih =>
      rw [defaultModules]
      refine onlyA_seq ?_ fun _ => onlyA_seq ih fun _ => onlyA_pure _
      rw [modulesOfTarget]; only_steps
  have hmodules : ∀ names, OnlyAIn LoadOp (readModules root.leanPath root.leanLib root.rootLib names : Attempt L E _) := by
    intro names
    induction names with
    | nil => rw [readModules]; exact onlyA_pure _
    | cons n rest ih =>
      rw [readModules]
      exact onlyA_seq (onlyA_attempt (only_call trivial)) fun _ => onlyA_seq ih fun _ => onlyA_pure _
  rw [inputOf]
  refine onlyA_seq (hdefault _) fun modules => onlyA_seq (onlyA_attempt (only_call trivial)) fun env => onlyA_seq ?_ fun f => only_pure _
  rw [factsOf]
  exact onlyA_seq (hmodules _) fun _ => onlyA_pure _

theorem only_loadTree (sysroot : String) (tree : FilePath) (p : Regula.Closed.Profile) :
    OnlyAIn LoadOp (loadTree sysroot tree p : Attempt L E _) := by
  unfold loadTree
  exact onlyA_seq (onlyA_attempt (only_call trivial)) fun dir =>
    onlyA_seq (only_seq (only_call trivial) fun _ => only_pure _) fun _ => only_inputOf _ _

theorem only_loadPlain (p : Regula.Closed.Profile) : OnlyAIn LoadOp (loadPlain p : Attempt L E _) := by
  have henv (name why : String) : OnlyAIn LoadOp (requireEnv name why : Attempt L E _) := by
    rw [requireEnv]
    refine only_seq (only_call trivial) fun r => ?_
    cases r <;> exact only_pure _
  unfold loadPlain
  refine onlyA_seq (henv _ _) fun sysroot => onlyA_seq (onlyA_attempt (only_call trivial)) fun dir =>
    onlyA_seq (only_seq (only_call trivial) fun _ => only_pure _) fun root =>
      onlyA_seq (henv _ _) fun received => ?_
  try dsimp only
  split
  · exact onlyA_seq (only_inputOf _ _) fun _ => onlyA_pure _
  · exact onlyA_throw _

/-- Events of the loads print no line. -/
theorem printed_of_load {α : Type} {x : Attempt L E α} (hx : OnlyAIn LoadOp x) {t : List (Event L E)}
    {b : Except String α} (h : Runs x.run t b) : printed t = [] := by
  have hn : t.filterMap Event.line? = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro e he
    have := hx _ _ h e he
    obtain ⟨o', r'⟩ := e
    cases o' <;> first | rfl | exact this.elim
  simp [printed, hn]

theorem sayCoverage_spec {r : Except String Regula.Closed.Input} {t : List (Event L E)} {u : Unit}
    (h : Runs (sayCoverage r : Prog L E Unit) t u) : Details t := by
  cases r with
  | ok i =>
    rw [sayCoverage] at h
    exact say_spec h
  | error e =>
    rw [sayCoverage] at h
    obtain ⟨rfl, -⟩ := runs_pure_iff.mp h
    exact details_nil

/-- The rules on the finished build: their verdict is the decision's on what the load gave, and the phase meets `RulesPreparation`. It issues no
write, directory creation, allocation, removal or command request, on success or failure, and a pass received no failed answer. -/
theorem rules_spec {T t : List (Event L E)} {sysroot : String} {tree : FilePath} {p : Regula.Closed.Profile}
    {v : Regula.Closed.Verdict} (hT : t.Sublist T)
    (h : Runs (rules (loadTree sysroot tree p) : Prog L E _) t v) :
    (∃ result, Loaded (TreeRoot sysroot tree) (TreeReason sysroot tree) T p result ∧
      v = (Regula.Closed.decision result).verdict) ∧
      (∀ l ∈ printed t, IsDetail l) ∧ (∀ e ∈ t, ReloadOp e.op ∧ e.isBuild = false) ∧
      (v = .pass → Clean t) ∧ RulesPreparation sysroot tree t := by
  unfold rules at h
  obtain ⟨t₁, t₂, result, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  obtain ⟨t₃, t₄, u, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
  obtain ⟨t₅, t₆, u', rfl, h₅, h₆⟩ := runs_seq_iff.mp h₄
  obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₆
  obtain ⟨l1, l2, l3⟩ := loadTree_spec ((List.sublist_append_left _ _).trans hT) h₁
  have hd : Details (t₃ ++ (t₅ ++ ([] : List (Event L E)))) := by
    simpa using details_append (sayCoverage_spec h₃) (sayAll_spec h₅)
  refine ⟨⟨result, l1, rfl⟩, fun l hl => ?_, fun e he => ?_, fun hv e he => ?_, l3.appendQuiet (quiet_of_saying hd.1)⟩
  · rw [printed_append, printed_of_load (only_loadTree _ _ _) h₁] at hl
    exact hd.2 l (by simpa using hl)
  · rcases List.mem_append.mp he with he | he
    · have := only_loadTree (L := L) (E := E) sysroot tree p _ _ h₁ e he
      obtain ⟨o', r'⟩ := e
      cases o' <;> first | exact ⟨trivial, rfl⟩ | exact this.elim
    · have := hd.1 e he
      obtain ⟨o', r'⟩ := e
      cases o' <;> first | exact ⟨trivial, rfl⟩ | cases this
  · obtain ⟨i, hi, -⟩ := RegulaSpecification.Loader.decision_pass hv
    subst hi
    rcases List.mem_append.mp he with he | he
    · exact l2 i rfl e he
    · exact details_not_failed hd e he

/-! ## The gate in its tree -/

/-- What the gate's events are, and what it reports. -/
structure GateEvents (tRead tGate : List (Event L E)) (dir tree : FilePath) (p : Regula.Closed.Profile)
    (report : Report) : Prop where
  /-- The reading stage builds nothing, loads no build and issues no removal request. -/
  quiet : ∀ e ∈ tRead, e.isBuild = false ∧ e.isImportForRules = false ∧ NotRemoving e.op
  /-- What decided. -/
  decided : ∃ o, Decided tRead dir tree o ∧ (o = .admitted → ∀ e ∈ tRead, ¬ e.failed) ∧
    (o ≠ .admitted → tGate = [] ∧ report = (match o with
      | .refused => Report.refused
      | .proofOnly => Report.proofOnly
      | _ => Report.incomplete)) ∧
    (o = .admitted → ∃ sysroot tBuild tRules, SysrootIs tRead sysroot ∧ tGate = tBuild ++ tRules ∧
      BuildAndRules sysroot tBuild tRules tree p report)
  /-- A pass received no failed answer. -/
  healthy : report = .full .pass → ∀ e ∈ tRead ++ tGate, ¬ e.failed
  /-- Each line is a detail. -/
  lines : (∀ l ∈ printed tRead, IsDetail l) ∧ ∀ l ∈ printed tGate, IsDetail l
  /-- The reading's ordered acts and the context of every search consumer. -/
  readPrepared : ReadingPreparation tRead dir tree
  /-- The gate's acts. -/
  gateActs : ∀ e ∈ tGate, ∀ path, e.acted? = some path → path = tree

theorem gateIn_spec {p : Regula.Closed.Profile} {dir tree : FilePath} {t : List (Event L E)} {report : Report}
    (h : Runs (gateIn p dir tree : Prog L E Report) t report) :
    ∃ tRead tGate, t = tRead ++ tGate ∧ GateEvents tRead tGate dir tree p report := by
  unfold gateIn at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  obtain rfl := runs_call_iff.mp h₁
  cases r with
  | none =>
    obtain ⟨t₃, t₄, u, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
    obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₄
    have hd := say_spec h₃
    refine ⟨[⟨.getEnv "LEAN_SYSROOT", none⟩] ++ t₃, [], by simp, ?_⟩
    refine { quiet := ?_, decided := ⟨.incomplete, ⟨fun he => (by cases he), fun _ =>
                 .failed (e := ⟨.getEnv "LEAN_SYSROOT", none⟩) (by simp) .sysroot rfl, .inr rfl⟩,
               fun he => (by cases he), fun _ => ⟨rfl, rfl⟩, fun he => (by cases he)⟩,
             healthy := fun he => (by cases he),
             lines := ⟨?_, by simp [printed]⟩,
             readPrepared := .inl ((quiet_one (o := .getEnv "LEAN_SYSROOT") (r := none) trivial).append (quiet_of_saying hd.1)), gateActs := by simp }
    · intro e he
      rcases List.mem_append.mp he with he | he
      · obtain rfl := List.mem_singleton.mp he
        exact ⟨rfl, rfl, trivial⟩
      · have := hd.1 e he
        obtain ⟨o', r'⟩ := e
        cases o' <;> first | exact ⟨rfl, rfl, trivial⟩ | cases this
    · intro l hl
      rw [printed_append] at hl
      exact hd.2 l (by simpa [printed, Event.line?] using hl)
  | some sysroot =>
    unfold Regula.Language.gate at h₂
    obtain ⟨t₃, t₄, o, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
    have hsys : SysrootIs ([⟨.getEnv "LEAN_SYSROOT", some sysroot⟩] ++ t₃ : List (Event L E)) sysroot := by simp [SysrootIs]
    obtain ⟨c1, hprepared, c3, c4, c5⟩ := check_spec (prior := [⟨.getEnv "LEAN_SYSROOT", some sysroot⟩])
      (quiet_one trivial) (by simp [SysrootIs]) h₃
    have hquiet : ∀ e ∈ ([⟨.getEnv "LEAN_SYSROOT", some sysroot⟩] : List (Event L E)) ++ t₃,
        e.isBuild = false ∧ e.isImportForRules = false ∧ NotRemoving e.op := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · obtain rfl := List.mem_singleton.mp he
        exact ⟨rfl, rfl, trivial⟩
      · exact c4 e he
    have hlines : ∀ l ∈ printed (([⟨.getEnv "LEAN_SYSROOT", some sysroot⟩] : List (Event L E)) ++ t₃),
        IsDetail l := by
      intro l hl
      rw [printed_append] at hl
      exact c5 l (by simpa [printed, Event.line?] using hl)
    refine ⟨[⟨.getEnv "LEAN_SYSROOT", some sysroot⟩] ++ t₃, t₄, by simp, ?_⟩
    cases o with
    | refused =>
      obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₄
      exact { quiet := hquiet, decided := ⟨.refused, c1, fun he => (by cases he), fun _ => ⟨rfl, rfl⟩, fun he => (by cases he)⟩,
              healthy := fun he => (by cases he), lines := ⟨hlines, by simp [printed]⟩, readPrepared := hprepared, gateActs := by simp }
    | incomplete =>
      obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₄
      exact { quiet := hquiet, decided := ⟨.incomplete, c1, fun he => (by cases he), fun _ => ⟨rfl, rfl⟩, fun he => (by cases he)⟩,
              healthy := fun he => (by cases he), lines := ⟨hlines, by simp [printed]⟩, readPrepared := hprepared, gateActs := by simp }
    | proofOnly =>
      obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₄
      exact { quiet := hquiet, decided := ⟨.proofOnly, c1, fun he => (by cases he), fun _ => ⟨rfl, rfl⟩, fun he => (by cases he)⟩,
              healthy := fun he => (by cases he), lines := ⟨hlines, by simp [printed]⟩, readPrepared := hprepared, gateActs := by simp }
    | admitted =>
      have hnoFail : Outcome.admitted = Outcome.admitted →
          ∀ e ∈ ([⟨.getEnv "LEAN_SYSROOT", some sysroot⟩] : List (Event L E)) ++ t₃, ¬ e.failed :=
        fun _ => (clean_one (fun hn => by cases hn)).append (c3 rfl)
      obtain ⟨t₅, t₆, c, rfl, h₅, h₆⟩ := runs_seq_iff.mp h₄
      obtain ⟨b1, b2, b3⟩ := buildAndReplay_spec h₅
      have protocol := buildAndReplay_protocol h₅
      cases c with
      | false =>
        obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₆
        exact { quiet := hquiet,
                decided := ⟨.admitted, c1, hnoFail, fun he => absurd rfl he, fun _ =>
                  ⟨sysroot, t₅, [], hsys, by simp, protocol, by simp,
                    .inr ⟨rfl, by simp, b3 rfl⟩, .inl quiet_nil⟩⟩,
                healthy := fun he => (by cases he),
                lines := ⟨hlines, by simpa using b1.2.1⟩, readPrepared := hprepared,
                gateActs := by simpa using b1.2.2 }
      | true =>
        rw [ite_eq_left rfl] at h₆
        obtain ⟨t₇, t₈, v, rfl, h₇, h₈⟩ := runs_seq_iff.mp h₆
        obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₈
        simp only [List.append_nil] at h₇ ⊢
        obtain ⟨⟨result, r1, rfl⟩, r2, r3, r5, r6⟩ := rules_spec (List.Sublist.refl _) h₇
        obtain ⟨⟨program, lakeLib, hsub⟩, hb⟩ := b2 rfl
        refine { quiet := hquiet,
                 decided := ⟨.admitted, c1, hnoFail, fun he => absurd rfl he, fun _ =>
                   ⟨sysroot, t₅, t₇, hsys, rfl, protocol, fun e he => (r3 e he).1,
                     .inl ⟨program, lakeLib, result, fun e he => (r3 e he).2, hsub, r1, rfl⟩, r6⟩⟩,
                 healthy := ?_,
                 lines := ⟨hlines, ?_⟩, readPrepared := hprepared, gateActs := ?_ }
        · intro hrep e he
          rcases List.mem_append.mp he with he | he
          · exact hnoFail rfl e he
          · rcases List.mem_append.mp he with he | he
            · exact hb e he
            · exact r5 (Report.full.inj hrep) e he
        · intro l hl
          rw [printed_append] at hl
          rcases List.mem_append.mp hl with hl | hl
          · exact b1.2.1 l hl
          · exact r2 l hl
        · intro e he p' hp'
          rcases List.mem_append.mp he with he | he
          · exact b1.2.2 e he p' hp'
          · have := (r3 e he).1
            obtain ⟨o', r'⟩ := e
            cases o' <;> first | exact this.elim | cases hp'

/-! ## The whole run -/

/-- Each act of the reading stage, the gate and the removal, in the record's words. -/
theorem confined_of {tRead tGate last : List (Event L E)} {dir tree : FilePath} {tmp r}
    (hr : ReadActs tRead dir tree) (hg : ∀ e ∈ tGate, ∀ path, e.acted? = some path → path = tree)
    (hl : ∀ e ∈ last, e.isOnlySaying = true) :
    Confined (⟨.createTempDir, tmp⟩ :: tRead ++ tGate ++ ⟨.removeDirAll tree, r⟩ :: last) dir tree := by
  have hrest : ∀ e ∈ ⟨.createTempDir, tmp⟩ :: tRead ++ tGate ++ ⟨.removeDirAll tree, r⟩ :: last,
      e ∈ tRead ∨ ∀ path, e.acted? = some path → path = tree := by
    intro e he
    simp only [List.cons_append, List.mem_cons, List.mem_append] at he
    rcases he with rfl | (he | he) | rfl | he
    · exact .inr fun path hp => by cases hp
    · exact .inl he
    · exact .inr (hg e he)
    · exact .inr fun path hp => by cases hp; rfl
    · exact .inr fun path hp => by
        rw [acted_of_saying (hl e he)] at hp
        cases hp
  rcases hr with hr | ⟨project, real, hp, hreal, ha, hin⟩
  · refine .inl fun e he path hpath => ?_
    rcases hrest e he with h' | h'
    · rw [hr e h'] at hpath
      cases hpath
    · exact h' path hpath
  · refine .inr ⟨project, real, by simp [hp], by simp [hreal], ha, fun e he path hpath => ?_⟩
    rcases hrest e he with h' | h'
    · refine .inr ?_
      exact hin e h' path hpath
    · exact .inl (h' path hpath)

theorem runFull_spec {p : Regula.Closed.Profile} {dir : FilePath} {t : List (Event L E)} {c : UInt32}
    (h : Runs (runFull p dir : Prog L E UInt32) t c) : FullRun t dir p c := by
  unfold runFull at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  obtain rfl := runs_call_iff.mp h₁
  cases r with
  | error e =>
    obtain ⟨t₃, t₄, u, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
    have h₄' : Runs (finish Report.incomplete.label Report.incomplete.exitCode : Prog L E UInt32) t₄ c := h₄
    obtain ⟨hc, r', rfl⟩ := finish_spec h₄'
    have hd := say_spec h₃
    refine .inl ⟨e, t₃ ++ [⟨.println Report.incomplete.label, r'⟩], by simp, hc, ?_, fun x hx => ?_⟩
    · refine ⟨[⟨.createTempDir, .error e⟩] ++ t₃, r', by simp, reportLabel_no_break _, fun l hl => ?_⟩
      rw [printed_append] at hl
      exact hd.2 l (by simpa [printed, Event.line?] using hl)
    · rcases List.mem_append.mp hx with hx | hx
      · exact hd.1 x hx
      · have : x = _ := List.mem_singleton.mp hx
        subst this
        rfl
  | ok tree =>
    obtain ⟨t₃, t₄, report, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
    obtain ⟨tRead, tGate, rfl, G⟩ := gateIn_spec h₃
    obtain ⟨t₅, t₆, r₅, rfl, h₅, h₆⟩ := runs_seq_iff.mp h₄
    obtain rfl := runs_call_iff.mp h₅
    -- The removal, a line if it failed, and the last line.
    have hlast : ∃ last r', t₆ = last ++ [⟨.println (report.labelOn dir.toString), r'⟩] ∧ Details last ∧ c = report.exitCode := by
      cases r₅ with
      | ok u =>
        obtain ⟨hc, r', rfl⟩ := finish_spec h₆
        exact ⟨[], r', rfl, details_nil, hc⟩
      | error e =>
        obtain ⟨t₇, t₈, u, rfl, h₇, h₈⟩ := runs_seq_iff.mp h₆
        obtain ⟨hc, r', rfl⟩ := finish_spec h₈
        exact ⟨t₇, r', rfl, say_spec h₇, hc⟩
    obtain ⟨last, r', rfl, hd, hc⟩ := hlast
    obtain ⟨o, hdec, hnf, hn, ha⟩ := G.decided
    have hsaying : Confined (⟨.createTempDir, .ok tree⟩ :: tRead ++ tGate ++
        ⟨.removeDirAll tree, r₅⟩ :: (last ++ [⟨.println (report.labelOn dir.toString), r'⟩])) dir tree := by
      refine confined_of G.readPrepared.readActs G.gateActs fun e he => ?_
      rcases List.mem_append.mp he with he | he
      · exact hd.1 e he
      · have : e = _ := List.mem_singleton.mp he
        subst this
        rfl
    have hlastSaying : ∀ e ∈ last ++ [⟨.println (report.labelOn dir.toString), r'⟩], e.isOnlySaying = true := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hd.1 e he
      · have : e = _ := List.mem_singleton.mp he
        subst this
        rfl
    refine .inr ⟨tree, tRead, tGate, r₅, last ++ [⟨.println (report.labelOn dir.toString), r'⟩], by simp, fun e he => ⟨(G.quiet e he).1, (G.quiet e he).2.1⟩, hlastSaying, o, report,
      hdec, hnf, hn, ha, hc, ?_, hsaying, ?_, fun e he => (G.quiet e he).2.2, G.readPrepared⟩
    rotate_left
    · intro hzero e he
      have hrep : report = .full .pass := (Report.exitCode_eq_zero_iff report).mp (hc.symm.trans hzero)
      have he' : e = ⟨.createTempDir, .ok tree⟩ ∨ e ∈ tRead ++ tGate ∨ e = ⟨.removeDirAll tree, r₅⟩ ∨
          e ∈ last ++ [⟨.println (report.labelOn dir.toString), r'⟩] := by
        simpa [List.mem_append, or_assoc] using he
      rcases he' with rfl | he | rfl | he
      · rintro ⟨x, hx⟩
        cases hx
      · exact G.healthy hrep e he
      · exact id
      · exact not_failed_of_saying (hlastSaying e he)
    refine ⟨⟨.createTempDir, .ok tree⟩ :: tRead ++ tGate ++ ⟨.removeDirAll tree, r₅⟩ :: last,
      r', by simp, reportLabelOn_no_break _ _, ?_⟩
    intro l hl
    simp only [List.cons_append, printed, List.filterMap_cons, List.filterMap_append, Event.line?,
      List.flatMap_append, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact G.lines.1 l hl
    · exact G.lines.2 l hl
    · exact hd.2 l hl

theorem runPlain_spec {p : Regula.Closed.Profile} {t : List (Event L E)} {c : UInt32} {v}
    (h : Runs (runPlain p : Prog L E UInt32) t c) : PlainRun (⟨.leanVersion, v⟩ :: t) p c := by
  unfold runPlain at h
  obtain ⟨t₁, t₂, result, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  obtain ⟨t₃, t₄, u, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
  obtain ⟨hc, hend, hsay⟩ := finishPlain_spec h₄
  have hsub : t₁.Sublist (⟨.leanVersion, v⟩ :: (t₁ ++ (t₃ ++ t₄))) :=
    (List.sublist_append_left _ _).trans (List.sublist_cons_self _ _)
  obtain ⟨l1, ls, hprep⟩ := loadPlain_spec (prior := [⟨.leanVersion, v⟩]) hsub (quiet_one trivial) h₁
  have hd := sayCoverage_spec h₃
  have honly := only_loadPlain (L := L) (E := E) p _ _ h₁
  refine ⟨result.map (·.2), subjectOf result, l1, hc, ?_, ?_, fun e he => ?_, (fun hzero e he => ?_), ?_⟩
  · obtain ⟨pre, r, rfl, hn, hp⟩ := hend
    refine ⟨⟨.leanVersion, v⟩ :: (t₁ ++ (t₃ ++ pre)), r, by simp, hn, fun l hl => ?_⟩
    have hl' : l ∈ printed (t₁ ++ (t₃ ++ pre)) := hl
    rw [printed_append, printed_append, printed_of_load (only_loadPlain _) h₁] at hl'
    simp only [List.nil_append, List.mem_append] at hl'
    rcases hl' with hl' | hl'
    · exact hd.2 l hl'
    · exact hp l hl'
  · intro hv
    obtain ⟨i, hi, -⟩ := RegulaSpecification.Loader.decision_pass hv
    cases result with
    | error why => cases hi
    | ok x => exact (ls x.1 x.2 rfl).1
  · rcases List.mem_cons.mp he with rfl | he
    · rfl
    rcases List.mem_append.mp he with he | he
    · have := honly e he
      obtain ⟨o', r'⟩ := e
      cases o' <;> first | rfl | exact this.elim
    · rcases List.mem_append.mp he with he | he
      · exact acted_of_saying (hd.1 e he)
      · exact acted_of_saying (hsay e he)
  · have hv : (Regula.Closed.decision (result.map (·.2))).verdict = .pass :=
      (Regula.Closed.Verdict.exitCode_eq_zero_iff _).mp (hc.symm.trans hzero)
    obtain ⟨i, hi, -⟩ := RegulaSpecification.Loader.decision_pass hv
    have hok : ∃ x, result = .ok x := by
      cases result with
      | error why => cases hi
      | ok x => exact ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := hok
    rcases List.mem_cons.mp he with rfl | he
    · exact id
    rcases List.mem_append.mp he with he | he
    · exact (ls x.1 x.2 rfl).2 e he
    · rcases List.mem_append.mp he with he | he
      · exact details_not_failed hd e he
      · exact not_failed_of_saying (hsay e he)
  · simpa [List.append_assoc] using hprep.appendQuiet
      ((quiet_of_saying hd.1).append (quiet_of_saying hsay))

/-- Whether this is the Lean that this revision reads, as the shell tests it. -/
theorem supportsLean_iff (v : String × String) :
    supportsLean v.1 v.2 = true ↔ v = Regula.Closed.pinnedLean := by
  obtain ⟨a, b⟩ := v
  simp [supportsLean]

/-- A refusal: the first event asked which Lean this is, and the rest only said so. -/
theorem refusal_of {v} {why : String} {rest : List (Event L E)} {c : UInt32}
    (h : Runs (finishProof (.incomplete why) : Prog L E UInt32) rest c) :
    Refusal (⟨.leanVersion, v⟩ :: rest) c := by
  obtain ⟨hc, ⟨pre, r, he, hn, hp⟩, hsay⟩ := finishProof_spec h
  refine ⟨hc, ⟨⟨.leanVersion, v⟩ :: pre, r, by rw [he]; rfl, hn, fun l hl => ?_⟩, fun e he' => ?_⟩
  · exact hp l (by simpa [printed, Event.line?] using hl)
  · rcases List.mem_cons.mp he' with rfl | he'
    · rfl
    · exact hsay e he'

/-- Any argument list other than one word is refused, whatever the Lean. -/
theorem profileOfRun_other {version commit : String} {a : List String} (h : ∀ text, a ≠ [text]) :
    ∃ why, profileOfRun version commit a = .error why := by
  unfold profileOfRun
  split
  · exact ⟨_, rfl⟩
  · split
    · exact absurd rfl (h _)
    · exact ⟨_, rfl⟩

/-- A Lean that this revision does not read is refused, whatever the arguments. -/
theorem profileOfRun_lean {version commit : String} {a : List String}
    (h : (version, commit) ≠ Regula.Closed.pinnedLean) :
    ∃ why, profileOfRun version commit a = .error why := by
  have hs : supportsLean version commit = false := by
    cases hx : supportsLean version commit with
    | false => rfl
    | true => exact absurd ((supportsLean_iff (version, commit)).mp hx) h
  exact ⟨_, by unfold profileOfRun; rw [ite_eq_left (by simp [hs])]⟩

/-- A text that is no profile is refused, whatever the Lean. -/
theorem profileOfRun_text {version commit text : String}
    (h : Regula.Closed.Profile.ofSpelling? text = none) :
    ∃ why, profileOfRun version commit [text] = .error why := by
  unfold profileOfRun
  split
  · exact ⟨_, rfl⟩
  · simp only [h]
    exact ⟨_, rfl⟩

/-- On this Lean, the profile of its spelling. -/
theorem profileOfRun_ok' {version commit text : String} {p : Regula.Closed.Profile}
    (hv : (version, commit) = Regula.Closed.pinnedLean)
    (h : Regula.Closed.Profile.ofSpelling? text = some p) :
    profileOfRun version commit [text] = .ok p := by
  have hs : supportsLean version commit = true := (supportsLean_iff (version, commit)).mpr hv
  simp [profileOfRun, hs, h]

/-- The theorem of the shell: for every argument list and every response, a run of the program that the `lint`
executable interprets does what the record states. -/
theorem run_meets : RunMeets (Regula.Shell.run : List String → Prog L E UInt32) := by
  intro args t c h
  unfold Regula.Shell.run at h
  obtain ⟨t₁, t₂, v, rfl, h₁, h₂⟩ := runs_bind_iff.mp h
  obtain rfl := runs_call_iff.mp h₁
  obtain ⟨version, commit⟩ := v
  simp only [List.cons_append, List.nil_append]
  have h₃ : Runs (dispatch version commit args : Prog L E UInt32) t₂ c := h₂
  have hrefuse : ∀ {a : List String} {why : String}, profileOfRun version commit a = .error why →
      Runs (dispatch version commit a : Prog L E UInt32) t₂ c →
      Refusal (⟨.leanVersion, (version, commit)⟩ :: t₂) c := by
    intro a why he hr
    unfold dispatch at hr
    rw [he] at hr
    exact refusal_of hr
  match args, h₃ with
  | [text], h₃ =>
    cases hp : Regula.Closed.Profile.ofSpelling? text with
    | none =>
      obtain ⟨why, hw⟩ := profileOfRun_text (version := version) (commit := commit) hp
      simp only [hp]
      exact hrefuse hw h₃
    | some p =>
      simp only [hp]
      refine ⟨(version, commit), t₂, rfl, fun hv => ?_, fun hv => ?_⟩
      · unfold dispatch at h₃
        rw [profileOfRun_ok' hv hp] at h₃
        obtain ⟨t₄, t₅, r, rfl, h₄, h₅⟩ := runs_bind_iff.mp h₃
        obtain rfl := runs_call_iff.mp h₄
        refine ⟨(version, commit), r, t₅, rfl, ?_⟩
        cases r with
        | none => exact runPlain_spec h₅
        | some dir => exact runFull_spec h₅
      · obtain ⟨why, hw⟩ := profileOfRun_lean (a := [text]) hv
        exact hrefuse hw h₃
  | [], h₃ =>
    obtain ⟨why, hw⟩ := profileOfRun_other (version := version) (commit := commit) (a := []) (by simp)
    exact hrefuse hw h₃
  | a :: b :: more, h₃ =>
    obtain ⟨why, hw⟩ := profileOfRun_other (version := version) (commit := commit) (a := a :: b :: more) (by simp)
    exact hrefuse hw h₃

/-- **No argument selects what is audited.** For every argument list and every response, a run is a refusal, or it asked
`fullVariable`: unset, it is the proof verdict; set, it is the full gate on the directory that the answer names. The
arguments appear in none of it but as the profile. So what a project's `lintDriverArgs` hold selects no directory. -/
theorem run_subject {args : List String} {t : List (Event L E)} {c : UInt32}
    (h : Runs (Regula.Shell.run args : Prog L E UInt32) t c) :
    Refusal t c ∨ ∃ p v rest,
      (t = ⟨.leanVersion, v⟩ :: ⟨.getEnv fullVariable, none⟩ :: rest ∧ PlainRun (⟨.leanVersion, v⟩ :: rest) p c) ∨
      ∃ dir, t = ⟨.leanVersion, v⟩ :: ⟨.getEnv fullVariable, some dir⟩ :: rest ∧ FullRun rest (FilePath.mk dir) p c := by
  have hm := run_meets (L := L) (E := E) _ _ _ h
  match args, hm with
  | [text], hm =>
    simp only at hm
    cases hp : Regula.Closed.Profile.ofSpelling? text with
    | none =>
      rw [hp] at hm
      exact .inl hm
    | some p =>
      rw [hp] at hm
      obtain ⟨v, rest, ht, hrun, href⟩ := hm
      by_cases hv : v = Regula.Closed.pinnedLean
      · obtain ⟨v', r, rest', he, hf⟩ := hrun hv
        refine .inr ⟨p, v', rest', ?_⟩
        cases r with
        | none => exact .inl ⟨he, hf⟩
        | some dir => exact .inr ⟨dir, he, hf⟩
      · exact .inl (href hv)
  | [], hm => exact .inl hm
  | _ :: _ :: _, hm => exact .inl hm

/-- Any argument list other than one word is a refusal: a directory in `lintDriverArgs`, a relative path, `.` and a list
shorter or longer than the grammar all are. -/
theorem run_other {args : List String} (ha : ∀ text, args ≠ [text]) {t : List (Event L E)} {c : UInt32}
    (h : Runs (Regula.Shell.run args : Prog L E UInt32) t c) : Refusal t c := by
  have hm := run_meets (L := L) (E := E) _ _ _ h
  match args, ha, hm with
  | [text], ha, _ => exact absurd rfl (ha text)
  | [], _, hm => exact hm
  | _ :: _ :: _, _, hm => exact hm

/-- **A pass of the proof verdict is about the directory it names.** That is the current directory's real path, the workspace
was loaded from it, and Lake's search path starts with that workspace's (`PlainRoot`, whose read this states). -/
theorem plainRun_pass {t : List (Event L E)} {p : Regula.Closed.Profile} (h : PlainRun t p 0) :
    ∃ subject : FilePath, EndsWith t (Regula.Closed.Verdict.pass.proofLineOn subject.toString) ∧
      (⟨.realPath ".", .ok subject⟩ : Event L E) ∈ t ∧
      ∃ sysroot root log, (⟨.loadWorkspace sysroot subject, .ok (some root, log)⟩ : Event L E) ∈ t ∧ PlainRoot t root := by
  obtain ⟨result, subject, -, hc, he, hs, -⟩ := h
  have hv : (Regula.Closed.decision result).verdict = .pass :=
    (Regula.Closed.Verdict.exitCode_eq_zero_iff _).mp hc.symm
  rw [hv] at he
  obtain ⟨hr, sysroot, root, log, hl, hroot⟩ := hs hv
  exact ⟨subject, he, hr, sysroot, root, log, hl, hroot⟩

end RegulaSpecification.Effects
