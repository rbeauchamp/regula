/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.ReaderFailed
import RegulaSpecification.Proofs.ShellParts
import RegulaSpecification.Proofs.Preparation
import RegulaSpecification.Proofs.PreparationLoad

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

/-- The check meets `ReadingPreparation`, after any quiet prefix that holds the toolchain's answer. -/
theorem check_preparation {prior t : List (Event L E)} {sysroot : String} {dir tree : FilePath} {o : Outcome}
    (hq : Quiet prior) (hs : SysrootIs prior sysroot)
    (h : Runs (check sysroot dir tree : Prog L E Outcome) t o) : ReadingPreparation (prior ++ t) dir tree := by
  unfold check at h
  obtain ⟨first, last, response, rfl, hf, hl⟩ := runs_seq_iff.mp h
  have hp := read_preparation hq hs hf
  have hlast : Quiet last := by
    cases response with
    | error error =>
      obtain ⟨a, b, u, rfl, ha, hb⟩ := runs_seq_iff.mp hl
      obtain ⟨rfl, -⟩ := runs_pure_iff.mp hb
      simpa using quiet_of_saying (say_spec ha).1
    | ok pair =>
      obtain ⟨reading, lines⟩ := pair
      obtain ⟨a, b, u, rfl, ha, hb⟩ := runs_seq_iff.mp hl
      obtain ⟨c, d, v, rfl, hc, hd⟩ := runs_seq_iff.mp hb
      obtain ⟨rfl, -⟩ := runs_pure_iff.mp hd
      simpa using (quiet_of_saying (sayAll_spec ha).1).append (quiet_of_saying (say_spec hc).1)
  simpa [List.append_assoc] using hp.appendQuiet hlast

/-- What `check` decides rests on what the reader read, and it prints only details. -/
theorem check_spec {T t : List (Event L E)} {sysroot : String} {dir tree : FilePath} {o : Outcome}
    (hI : t <:+: T) (hsys : SysrootIs T sysroot) (h : Runs (check sysroot dir tree : Prog L E Outcome) t o) :
    Decided T dir tree o ∧ ReadActs t dir tree ∧
      (∀ e ∈ t, e.isBuild = false ∧ e.isImportForRules = false) ∧ (∀ l ∈ printed t, IsDetail l) := by
  unfold check at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  obtain ⟨g1, g2, g3⟩ := read_spec (List.infix_append_left.trans hI) hsys h₁
  have honly := only_readProject (L := L) (E := E) sysroot dir tree _ _ h₁
  have hquiet : ∀ e ∈ t₁, e.isBuild = false ∧ e.isImportForRules = false := by
    intro e he
    have := honly e he
    obtain ⟨o', r'⟩ := e
    cases o' <;> first | exact ⟨rfl, rfl⟩ | exact this.elim
  have hprinted₁ : printed t₁ = [] := by
    have hn : t₁.filterMap Event.line? = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro e he
      have := honly e he
      obtain ⟨o', r'⟩ := e
      cases o' <;> first | rfl | exact this.elim
    simp [printed, hn]
  have hacts : ∀ {t' : List (Event L E)}, Details t' → ReadActs (t₁ ++ t') dir tree := by
    intro t' hd
    rcases g3 with g3 | ⟨project, real, hp, hr, ha, hin⟩
    · refine .inl fun e he => ?_
      rcases List.mem_append.mp he with he | he
      · exact g3 e he
      · exact acted_of_saying (hd.1 e he)
    · refine .inr ⟨project, real, List.mem_append_left _ hp, List.mem_append_left _ hr, ha, fun e he p hp' => ?_⟩
      rcases List.mem_append.mp he with he | he
      · exact hin e he p hp'
      · rw [acted_of_saying (hd.1 e he)] at hp'
        cases hp'
  have hrest : ∀ {t' : List (Event L E)}, Details t' →
      (∀ e ∈ t₁ ++ t', e.isBuild = false ∧ e.isImportForRules = false) ∧
        (∀ l ∈ printed (t₁ ++ t'), IsDetail l) := by
    intro t' hd
    refine ⟨fun e he => ?_, fun l hl => ?_⟩
    · rcases List.mem_append.mp he with he | he
      · exact hquiet e he
      · have := hd.1 e he
        obtain ⟨o', r'⟩ := e
        cases o' <;> first | exact ⟨rfl, rfl⟩ | cases this
    · rw [printed_append, hprinted₁] at hl
      exact hd.2 l (by simpa using hl)
  cases r with
  | error why =>
    obtain ⟨t₃, t₄, u, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
    obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₄
    have hd := say_spec h₃
    have hr := g2 ⟨why, rfl⟩
    have : Details (t₃ ++ ([] : List (Event L E))) := by simpa using hd
    exact ⟨⟨fun he => (by cases he), fun _ => hr, .inr rfl⟩, hacts this, hrest this⟩
  | ok x =>
    obtain ⟨reading, lines⟩ := x
    obtain ⟨t₃, t₄, u, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
    obtain ⟨t₅, t₆, u', rfl, h₅, h₆⟩ := runs_seq_iff.mp h₄
    obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₆
    have hd : Details (t₃ ++ (t₅ ++ ([] : List (Event L E)))) := by
      simpa using details_append (sayAll_spec h₃) (say_spec h₅)
    obtain ⟨g4, g5⟩ := g1 reading lines rfl
    refine ⟨⟨fun ha => ⟨reading, (decision_admitted_iff reading).mp ha, g4 ha⟩,
      fun hne => g5 _ rfl hne, .inl ⟨reading, rfl⟩⟩, hacts hd, hrest hd⟩

/-- On an admission, nothing that `check` asked failed. -/
theorem check_no_failed {sysroot : String} {dir tree : FilePath} {t : List (Event L E)}
    (h : Runs (check sysroot dir tree : Prog L E Outcome) t .admitted) : ∀ e ∈ t, ¬ e.failed := by
  unfold check at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  cases r with
  | error why =>
    obtain ⟨t₃, t₄, u, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
    cases (runs_pure_iff.mp h₄).2
  | ok x =>
    obtain ⟨reading, lines⟩ := x
    obtain ⟨t₃, t₄, u, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
    obtain ⟨t₅, t₆, u', rfl, h₅, h₆⟩ := runs_seq_iff.mp h₄
    obtain ⟨rfl, hadm⟩ := runs_pure_iff.mp h₆
    unfold Regula.Reader.read at h₁
    obtain ⟨t₇, t₈, r₇, rfl, h₇, h₈⟩ := runs_attempt_bind_iff.mp h₁
    cases r₇ with
    | error w => cases h₈.2
    | ok y =>
      obtain ⟨r, srcs⟩ := y
      obtain ⟨rfl, he⟩ := runs_attempt_pure_iff.mp h₈
      cases he
      have hd := details_append (sayAll_spec h₃) (say_spec h₅)
      intro e he
      simp only [List.append_nil, List.mem_append] at he
      rcases he with he | he
      · exact readProject_no_failed h₇ hadm.symm e he
      · have hs : e.isOnlySaying = true := hd.1 e (by simpa using he)
        obtain ⟨o', r'⟩ := e
        cases o' <;> first | exact id | cases hs

/-! ## The build -/

/-- The reader and its reporting issue no removal request, on any outcome. -/
theorem check_notRemoving (sysroot : String) (dir tree : FilePath) :
    OnlyIn NotRemoving (check sysroot dir tree : Prog L E Outcome) := by
  have saying {t : List (Event L E)} (h : Details t) : ∀ e ∈ t, NotRemoving e.op := by
    intro e he
    have hs := h.1 e he
    obtain ⟨o, r⟩ := e
    cases o <;> first | trivial | cases hs
  have hsay (s : String) : OnlyIn NotRemoving (say s : Prog L E Unit) :=
    fun _ _ h => saying (say_spec h)
  have hall (ss : List String) : OnlyIn NotRemoving (sayAll ss : Prog L E Unit) :=
    fun _ _ h => saying (sayAll_spec h)
  unfold check
  refine only_seq ((only_readProject sysroot dir tree).mono ?_) fun r => ?_
  · intro o ho
    cases o <;> first | trivial | exact ho.elim
  · cases r with
    | error why => exact only_seq (hsay _) fun _ => only_pure _
    | ok pair =>
      obtain ⟨reading, lines⟩ := pair
      exact only_seq (hall _) fun _ => only_seq (hsay _) fun _ => only_pure _

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

/-- An event that only says something is no failure. -/
theorem not_failed_of_saying {e : Event L E} (h : e.isOnlySaying = true) : ¬ e.failed := by
  obtain ⟨o, r⟩ := e
  cases o <;> first | exact id | cases h

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

theorem only_readModules (a b : FilePath) (names : List Name) :
    OnlyAIn LoadOp (readModules a b names : Attempt L E _) := by
  induction names with
  | nil => rw [readModules]; exact onlyA_pure _
  | cons n rest ih =>
    rw [readModules]
    exact onlyA_seq (onlyA_attempt (only_call trivial)) fun _ => onlyA_seq ih fun _ => onlyA_pure _

theorem only_inputOf (root : Root L) (p : Regula.Closed.Profile) :
    OnlyAIn LoadOp (inputOf root p : Attempt L E _) := by
  rw [inputOf]
  have hdefault : ∀ targets, OnlyAIn LoadOp (defaultModules root targets : Attempt L E _) := by
    intro targets
    induction targets with
    | nil => rw [defaultModules]; exact onlyA_pure _
    | cons t ts ih =>
      rw [defaultModules]
      refine onlyA_seq ?_ fun _ => onlyA_seq ih fun _ => onlyA_pure _
      rw [modulesOfTarget]
      split
      · exact onlyA_seq (onlyA_attempt (only_call trivial)) fun _ => onlyA_pure _
      · split <;> exact onlyA_pure _
  refine onlyA_seq (hdefault _) fun modules => ?_
  refine onlyA_seq (onlyA_lift (only_call trivial)) fun _ => onlyA_seq (onlyA_attempt (only_call trivial)) fun env => ?_
  refine onlyA_seq ?_ fun f => only_pure _
  rw [factsOf]
  exact onlyA_seq (only_readModules _ _ _) fun _ => onlyA_pure _

theorem only_loadRoot (sysroot : String) (dir : FilePath) (what : String) :
    OnlyAIn LoadOp (ExceptT.mk (Prog.bind (Prog.call (.loadRoot sysroot dir)) fun r =>
      pure (loaded what r)) : Attempt L E (Root L)) :=
  only_seq (only_call trivial) fun _ => only_pure _

theorem only_loadTree (sysroot : String) (tree : FilePath) (p : Regula.Closed.Profile) :
    OnlyAIn LoadOp (loadTree sysroot tree p : Attempt L E _) := by
  unfold loadTree
  exact onlyA_seq (onlyA_attempt (only_call trivial)) fun dir =>
    onlyA_seq (only_loadRoot _ _ _) fun _ => only_inputOf _ _

theorem only_requireEnv (name why : String) : OnlyAIn LoadOp (requireEnv name why : Attempt L E _) := by
  rw [requireEnv]
  refine only_seq (only_call trivial) fun r => ?_
  cases r <;> exact only_pure _

theorem only_loadPlain (p : Regula.Closed.Profile) : OnlyAIn LoadOp (loadPlain p : Attempt L E _) := by
  unfold loadPlain
  refine onlyA_seq (only_requireEnv _ _) fun sysroot => onlyA_seq (onlyA_attempt (only_call trivial)) fun dir =>
    onlyA_seq (only_seq (only_call trivial) fun _ => only_pure _) fun root =>
      onlyA_seq (onlyA_lift (only_call trivial)) fun x => ?_
  obtain ⟨program, lakeLib⟩ := x
  dsimp only
  refine onlyA_seq (only_requireEnv _ _) fun received => ?_
  try dsimp only
  split
  · exact only_inputOf _ _
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

/-! ## A load that gives an input received no failed answer -/

theorem sound_call_lift {α : Type} {p : Prog L E α} (hp : ∀ t a, Runs p t a → ∀ e ∈ t, ¬ e.failed) :
    Sound (ExceptT.lift p : Attempt L E α) := by
  intro t a h e he
  obtain ⟨a', h₁, -⟩ := runs_lift_iff.mp h
  exact hp _ _ h₁ e he

theorem sound_requireEnv (name why : String) : Sound (requireEnv name why : Attempt L E _) := by
  intro t a h e he
  obtain ⟨r, rfl, h1, -⟩ := requireEnv_spec h
  have := h1 a rfl
  subst this
  have : e = _ := List.mem_singleton.mp he
  subst this
  exact fun hn => by cases hn

theorem sound_readModules (a b : FilePath) (names : List Name) : Sound (readModules a b names : Attempt L E _) := by
  induction names with
  | nil => rw [readModules]; exact sound_pure _
  | cons n rest ih =>
    rw [readModules]
    refine sound_seq ?_ fun _ => sound_seq ih fun _ => sound_pure _
    sound_io

theorem sound_factsOf (env : Lean.Environment) (a b : FilePath) : Sound (factsOf env a b : Attempt L E _) := by
  rw [factsOf]
  exact sound_seq (sound_readModules _ _ _) fun _ => sound_pure _

theorem sound_inputOf (root : Root L) (p : Regula.Closed.Profile) : Sound (inputOf root p : Attempt L E _) := by
  rw [inputOf]
  refine sound_seq (sound_defaultModules _ _) fun modules => sound_seq (sound_call_lift ?_) fun _ =>
    sound_seq ?_ fun env => sound_seq (sound_factsOf _ _ _) fun f => ?_
  · intro t a h e he
    obtain rfl := runs_call_iff.mp h
    have : e = _ := List.mem_singleton.mp he
    subst this
    exact id
  · sound_io
  · intro t a h e he
    obtain ⟨rfl, -⟩ := runs_done_iff.mp h
    cases he

theorem sound_loadRoot (sysroot : String) (dir : FilePath) (what : String) :
    Sound (ExceptT.mk (Prog.bind (Prog.call (.loadRoot sysroot dir)) fun r =>
      pure (loaded what r)) : Attempt L E (Root L)) := by
  intro t a h e he
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_bind_iff.mp h
  obtain rfl := runs_call_iff.mp h₁
  obtain ⟨rfl, hb⟩ := runs_done_iff.mp h₂
  simp only [List.append_nil, List.mem_singleton] at he
  subst he
  obtain ⟨log, rfl⟩ := (loaded_spec (what := what) (r := r)).1 a hb.symm
  rintro (⟨x, hx⟩ | ⟨x, hx⟩) <;> cases hx

theorem sound_loadWorkspace (sysroot : String) (dir : FilePath) (what : String) :
    Sound (ExceptT.mk (Prog.bind (Prog.call (.loadWorkspace sysroot dir)) fun r =>
      pure (loaded what r)) : Attempt L E (Root L)) := by
  intro t a h e he
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_bind_iff.mp h
  obtain rfl := runs_call_iff.mp h₁
  obtain ⟨rfl, hb⟩ := runs_done_iff.mp h₂
  simp only [List.append_nil, List.mem_singleton] at he
  subst he
  obtain ⟨log, rfl⟩ := (loaded_spec (what := what) (r := r)).1 a hb.symm
  rintro (⟨x, hx⟩ | ⟨x, hx⟩) <;> cases hx

theorem sound_loadTree (sysroot : String) (tree : FilePath) (p : Regula.Closed.Profile) :
    Sound (loadTree sysroot tree p : Attempt L E _) := by
  unfold loadTree
  exact sound_seq (sound_realPath _) fun dir => sound_seq (sound_loadRoot _ _ _) fun _ => sound_inputOf _ _

theorem sound_loadPlain (p : Regula.Closed.Profile) : Sound (loadPlain p : Attempt L E _) := by
  unfold loadPlain
  refine sound_seq (sound_requireEnv _ _) fun sysroot => sound_seq (sound_realPath _) fun dir =>
    sound_seq (sound_loadWorkspace _ _ _) fun root => sound_seq (sound_call_lift ?_) fun x => ?_
  · intro t a h e he
    obtain rfl := runs_call_iff.mp h
    have : e = _ := List.mem_singleton.mp he
    subst this
    exact id
  · obtain ⟨program, lakeLib⟩ := x
    refine sound_seq (sound_requireEnv _ _) fun received => ?_
    split
    · exact sound_inputOf _ _
    · exact sound_throw _

/-- The rules on the finished build: their verdict is the decision's on what the load gave. -/
theorem rules_spec {T t : List (Event L E)} {sysroot : String} {tree : FilePath} {p : Regula.Closed.Profile}
    {v : Regula.Closed.Verdict} (hT : t.Sublist T)
    (h : Runs (rules (loadTree sysroot tree p) : Prog L E _) t v) :
    (∃ result, Loaded (TreeRoot sysroot tree) (TreeReason sysroot tree) T p result ∧
      v = (Regula.Closed.decision result).verdict) ∧
      (∀ l ∈ printed t, IsDetail l) ∧ (∀ e ∈ t, e.acted? = none) ∧ (∀ e ∈ t, e.isBuild = false) ∧
      (v = .pass → ∀ e ∈ t, ¬ e.failed) := by
  unfold rules at h
  obtain ⟨t₁, t₂, result, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  obtain ⟨t₃, t₄, u, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
  obtain ⟨t₅, t₆, u', rfl, h₅, h₆⟩ := runs_seq_iff.mp h₄
  obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₆
  obtain ⟨l1, l2⟩ := loadTree_spec ((List.sublist_append_left _ _).trans hT) h₁
  have hd : Details (t₃ ++ (t₅ ++ ([] : List (Event L E)))) := by
    simpa using details_append (sayCoverage_spec h₃) (sayAll_spec h₅)
  refine ⟨⟨result, l1, rfl⟩, fun l hl => ?_, fun e he => ?_, fun e he => ?_, fun hv e he => ?_⟩
  · rw [printed_append, printed_of_load (only_loadTree _ _ _) h₁] at hl
    exact hd.2 l (by simpa using hl)
  · rcases List.mem_append.mp he with he | he
    · exact l2 e he
    · exact acted_of_saying (hd.1 e he)
  · rcases List.mem_append.mp he with he | he
    · have := only_loadTree (L := L) (E := E) sysroot tree p _ _ h₁ e he
      obtain ⟨o', r'⟩ := e
      cases o' <;> first | rfl | exact this.elim
    · have := hd.1 e he
      obtain ⟨o', r'⟩ := e
      cases o' <;> first | rfl | cases this
  · obtain ⟨i, hi, -⟩ := RegulaSpecification.Loader.decision_pass hv
    subst hi
    rcases List.mem_append.mp he with he | he
    · exact sound_loadTree _ _ _ _ _ h₁ e he
    · exact details_not_failed hd e he

/-- The actual rule phase issues no explicit mutation, allocation or command request, on success or failure. -/
theorem rules_reload {sysroot : String} {tree : FilePath} {p : Regula.Closed.Profile}
    {t : List (Event L E)} {v : Regula.Closed.Verdict}
    (h : Runs (rules (loadTree sysroot tree p) : Prog L E _) t v) : ∀ e ∈ t, ReloadOp e.op := by
  have hsay {u : List (Event L E)} (hd : Details u) : ∀ e ∈ u, ReloadOp e.op := by
    intro e he
    have hs := hd.1 e he
    obtain ⟨o, r⟩ := e
    cases o <;> first | trivial | cases hs
  unfold rules at h
  obtain ⟨t₁, t₂, result, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  obtain ⟨t₃, t₄, u, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
  obtain ⟨t₅, t₆, u', rfl, h₅, h₆⟩ := runs_seq_iff.mp h₄
  obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₆
  intro e he
  simp only [List.append_nil, List.mem_append] at he
  rcases he with he | he | he
  · have ho := only_loadTree (L := L) (E := E) sysroot tree p _ _ h₁ e he
    obtain ⟨o, r⟩ := e
    cases o <;> first | trivial | exact ho.elim
  · exact hsay (sayCoverage_spec h₃) e he
  · exact hsay (sayAll_spec h₅) e he

/-! ## The gate in its tree -/

/-- The rule phase meets `RulesPreparation`. -/
theorem rules_preparation {sysroot : String} {tree : FilePath} {p : Regula.Closed.Profile}
    {t : List (Event L E)} {v : Regula.Closed.Verdict}
    (h : Runs (rules (loadTree sysroot tree p) : Prog L E _) t v) : RulesPreparation sysroot tree t := by
  unfold rules at h
  obtain ⟨first, last, result, rfl, hf, hl⟩ := runs_seq_iff.mp h
  obtain ⟨a, b, u, rfl, ha, hb⟩ := runs_seq_iff.mp hl
  obtain ⟨c, d, v, rfl, hc, hd⟩ := runs_seq_iff.mp hb
  obtain ⟨rfl, -⟩ := runs_pure_iff.mp hd
  simpa using (loadTree_preparation hf).appendQuiet
    ((quiet_of_saying (sayCoverage_spec ha).1).append (quiet_of_saying (sayAll_spec hc).1))

/-- What the gate's events are, and what it reports. -/
structure GateEvents (tRead tGate : List (Event L E)) (dir tree : FilePath) (p : Regula.Closed.Profile)
    (report : Report) : Prop where
  /-- The reading stage builds nothing and loads no build. -/
  quiet : ∀ e ∈ tRead, e.isBuild = false ∧ e.isImportForRules = false
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
  /-- The reading stage's acts. -/
  readActs : ReadActs tRead dir tree
  /-- The reading stage issues no removal request before admission. -/
  readKeeps : ∀ e ∈ tRead, NotRemoving e.op
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
             lines := ⟨?_, by simp [printed]⟩, readActs := .inl ?_, readKeeps := ?_,
             readPrepared := .inl ?_, gateActs := by simp }
    · intro e he
      rcases List.mem_append.mp he with he | he
      · have : e = _ := List.mem_singleton.mp he
        subst this
        exact ⟨rfl, rfl⟩
      · have := hd.1 e he
        obtain ⟨o', r'⟩ := e
        cases o' <;> first | exact ⟨rfl, rfl⟩ | cases this
    · intro l hl
      rw [printed_append] at hl
      exact hd.2 l (by simpa [printed, Event.line?] using hl)
    · intro e he
      rcases List.mem_append.mp he with he | he
      · have : e = _ := List.mem_singleton.mp he
        subst this
        rfl
      · exact acted_of_saying (hd.1 e he)
    · intro e he
      rcases List.mem_append.mp he with he | he
      · have : e = _ := List.mem_singleton.mp he
        subst this
        trivial
      · have hs := hd.1 e he
        obtain ⟨o, r⟩ := e
        cases o <;> first | trivial | cases hs
    · exact (show Quiet ([⟨.getEnv "LEAN_SYSROOT", none⟩] : List (Event L E)) from by
        intro e he; obtain rfl := List.mem_singleton.mp he; trivial).append (quiet_of_saying hd.1)
  | some sysroot =>
    unfold Regula.Language.gate at h₂
    obtain ⟨t₃, t₄, o, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
    have hT : t₃ <:+: ([⟨.getEnv "LEAN_SYSROOT", some sysroot⟩] ++ t₃) := List.infix_append_right
    have hsys : SysrootIs ([⟨.getEnv "LEAN_SYSROOT", some sysroot⟩] ++ t₃ : List (Event L E)) sysroot := by simp [SysrootIs]
    obtain ⟨c1, c2, c3, c4⟩ := check_spec hT hsys h₃
    have hprepared := check_preparation
      (prior := [⟨.getEnv "LEAN_SYSROOT", some sysroot⟩])
      (by intro e he; obtain rfl := List.mem_singleton.mp he; trivial) (by simp [SysrootIs]) h₃
    have hkeep : ∀ e ∈ ([⟨.getEnv "LEAN_SYSROOT", some sysroot⟩] : List (Event L E)) ++ t₃,
        NotRemoving e.op := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · have : e = _ := List.mem_singleton.mp he
        subst this
        trivial
      · exact check_notRemoving sysroot dir tree _ _ h₃ e he
    have hquiet : ∀ e ∈ ([⟨.getEnv "LEAN_SYSROOT", some sysroot⟩] : List (Event L E)) ++ t₃,
        e.isBuild = false ∧ e.isImportForRules = false := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · have : e = _ := List.mem_singleton.mp he
        subst this
        exact ⟨rfl, rfl⟩
      · exact c3 e he
    have hlines : ∀ l ∈ printed (([⟨.getEnv "LEAN_SYSROOT", some sysroot⟩] : List (Event L E)) ++ t₃),
        IsDetail l := by
      intro l hl
      rw [printed_append] at hl
      exact c4 l (by simpa [printed, Event.line?] using hl)
    have hacts : ReadActs (([⟨.getEnv "LEAN_SYSROOT", some sysroot⟩] : List (Event L E)) ++ t₃) dir tree := by
      rcases c2 with c2 | ⟨project, real, hp, hr, ha, hin⟩
      · refine .inl fun e he => ?_
        rcases List.mem_append.mp he with he | he
        · have : e = _ := List.mem_singleton.mp he
          subst this
          rfl
        · exact c2 e he
      · refine .inr ⟨project, real, List.mem_append_right _ hp, List.mem_append_right _ hr, ha, fun e he p' hp' => ?_⟩
        rcases List.mem_append.mp he with he | he
        · have : e = _ := List.mem_singleton.mp he
          subst this
          cases hp'
        · exact hin e he p' hp'
    refine ⟨[⟨.getEnv "LEAN_SYSROOT", some sysroot⟩] ++ t₃, t₄, by simp, ?_⟩
    cases o with
    | refused =>
      obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₄
      exact { quiet := hquiet, decided := ⟨.refused, c1, fun he => (by cases he), fun _ => ⟨rfl, rfl⟩, fun he => (by cases he)⟩,
              healthy := fun he => (by cases he),
              lines := ⟨hlines, by simp [printed]⟩, readActs := hacts, readKeeps := hkeep,
              readPrepared := hprepared, gateActs := by simp }
    | incomplete =>
      obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₄
      exact { quiet := hquiet, decided := ⟨.incomplete, c1, fun he => (by cases he), fun _ => ⟨rfl, rfl⟩, fun he => (by cases he)⟩,
              healthy := fun he => (by cases he),
              lines := ⟨hlines, by simp [printed]⟩, readActs := hacts, readKeeps := hkeep,
              readPrepared := hprepared, gateActs := by simp }
    | proofOnly =>
      obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₄
      exact { quiet := hquiet, decided := ⟨.proofOnly, c1, fun he => (by cases he), fun _ => ⟨rfl, rfl⟩, fun he => (by cases he)⟩,
              healthy := fun he => (by cases he),
              lines := ⟨hlines, by simp [printed]⟩, readActs := hacts, readKeeps := hkeep,
              readPrepared := hprepared, gateActs := by simp }
    | admitted =>
      have hnoFail : Outcome.admitted = Outcome.admitted →
          ∀ e ∈ ([⟨.getEnv "LEAN_SYSROOT", some sysroot⟩] : List (Event L E)) ++ t₃, ¬ e.failed := by
        intro _ e he
        rcases List.mem_append.mp he with he | he
        · have : e = _ := List.mem_singleton.mp he
          subst this
          exact fun hn => by cases hn
        · exact check_no_failed h₃ e he
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
                lines := ⟨hlines, by simpa using b1.2.1⟩, readActs := hacts, readKeeps := hkeep,
                readPrepared := hprepared,
                gateActs := by simpa using b1.2.2 }
      | true =>
        rw [ite_eq_left rfl] at h₆
        obtain ⟨t₇, t₈, v, rfl, h₇, h₈⟩ := runs_seq_iff.mp h₆
        obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₈
        simp only [List.append_nil] at h₇ ⊢
        obtain ⟨⟨result, r1, rfl⟩, r2, r3, r4, r5⟩ := rules_spec (List.Sublist.refl _) h₇
        obtain ⟨⟨program, lakeLib, hsub⟩, hb⟩ := b2 rfl
        refine { quiet := hquiet,
                 decided := ⟨.admitted, c1, hnoFail, fun he => absurd rfl he, fun _ =>
                   ⟨sysroot, t₅, t₇, hsys, rfl, protocol, rules_reload h₇,
                     .inl ⟨program, lakeLib, result, r4, hsub, r1, rfl⟩, rules_preparation h₇⟩⟩,
                 healthy := ?_,
                 lines := ⟨hlines, ?_⟩, readActs := hacts, readKeeps := hkeep,
                 readPrepared := hprepared, gateActs := ?_ }
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
          · rw [r3 e he] at hp'
            cases hp'

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
      obtain ⟨rel, hrel⟩ := (inTree_iff real path).mp (hin e h' path hpath)
      exact ⟨rel, hrel.1.symm⟩
    · exact .inl (h' path hpath)

theorem runFull_spec {p : Regula.Closed.Profile} {dir : FilePath} {t : List (Event L E)} {c : UInt32}
    (h : Runs (runFull p dir : Prog L E UInt32) t c) : FullRun t dir p c := by
  unfold runFull at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  obtain rfl := runs_call_iff.mp h₁
  cases r with
  | error e =>
    obtain ⟨t₃, t₄, u, rfl, h₃, h₄⟩ := runs_seq_iff.mp h₂
    obtain ⟨hc, r', rfl⟩ := finish_spec h₄
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
    have hlast : ∃ last r', t₆ = last ++ [⟨.println report.label, r'⟩] ∧ Details last ∧ c = report.exitCode := by
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
        ⟨.removeDirAll tree, r₅⟩ :: (last ++ [⟨.println report.label, r'⟩])) dir tree := by
      refine confined_of G.readActs G.gateActs fun e he => ?_
      rcases List.mem_append.mp he with he | he
      · exact hd.1 e he
      · have : e = _ := List.mem_singleton.mp he
        subst this
        rfl
    have hlastSaying : ∀ e ∈ last ++ [⟨.println report.label, r'⟩], e.isOnlySaying = true := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hd.1 e he
      · have : e = _ := List.mem_singleton.mp he
        subst this
        rfl
    refine .inr ⟨tree, tRead, tGate, r₅, last ++ [⟨.println report.label, r'⟩], by simp, G.quiet, hlastSaying, o, report,
      hdec, hnf, hn, ha, hc, ?_, hsaying, ?_, G.readKeeps, G.readPrepared⟩
    rotate_left
    · intro hzero e he
      have hrep : report = .full .pass := (Report.exitCode_eq_zero_iff report).mp (hc.symm.trans hzero)
      have he' : e = ⟨.createTempDir, .ok tree⟩ ∨ e ∈ tRead ++ tGate ∨ e = ⟨.removeDirAll tree, r₅⟩ ∨
          e ∈ last ++ [⟨.println report.label, r'⟩] := by
        simpa [List.mem_append, or_assoc] using he
      rcases he' with rfl | he | rfl | he
      · rintro ⟨x, hx⟩
        cases hx
      · exact G.healthy hrep e he
      · exact id
      · exact not_failed_of_saying (hlastSaying e he)
    refine ⟨⟨.createTempDir, .ok tree⟩ :: tRead ++ tGate ++ ⟨.removeDirAll tree, r₅⟩ :: last,
      r', by simp, reportLabel_no_break _, ?_⟩
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
  obtain ⟨hc, hend, hsay⟩ := finishProof_spec h₄
  have hsub : t₁.Sublist (⟨.leanVersion, v⟩ :: (t₁ ++ (t₃ ++ t₄))) :=
    (List.sublist_append_left _ _).trans (List.sublist_cons_self _ _)
  obtain ⟨l1, l2⟩ := loadPlain_spec hsub h₁
  have hd := sayCoverage_spec h₃
  have hprep := loadPlain_preparation (prior := [⟨.leanVersion, v⟩])
    (by intro e he; obtain rfl := List.mem_singleton.mp he; trivial) h₁
  refine ⟨result, l1, hc, ?_, fun e he => ?_, (fun hzero e he => ?_), ?_⟩
  · obtain ⟨pre, r, rfl, hn, hp⟩ := hend
    refine ⟨⟨.leanVersion, v⟩ :: (t₁ ++ (t₃ ++ pre)), r, by simp, hn, fun l hl => ?_⟩
    have hl' : l ∈ printed (t₁ ++ (t₃ ++ pre)) := hl
    rw [printed_append, printed_append, printed_of_load (only_loadPlain _) h₁] at hl'
    simp only [List.nil_append, List.mem_append] at hl'
    rcases hl' with hl' | hl'
    · exact hd.2 l hl'
    · exact hp l hl'
  · rcases List.mem_cons.mp he with rfl | he
    · rfl
    rcases List.mem_append.mp he with he | he
    · exact l2 e he
    · rcases List.mem_append.mp he with he | he
      · exact acted_of_saying (hd.1 e he)
      · exact acted_of_saying (hsay e he)
  · have hv : (Regula.Closed.decision result).verdict = .pass :=
      (Regula.Closed.Verdict.exitCode_eq_zero_iff _).mp (hc.symm.trans hzero)
    obtain ⟨i, rfl, -⟩ := RegulaSpecification.Loader.decision_pass hv
    rcases List.mem_cons.mp he with rfl | he
    · exact id
    rcases List.mem_append.mp he with he | he
    · exact sound_loadPlain _ _ _ h₁ e he
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

/-- Arguments of neither form the shell reads are refused, whatever the Lean. -/
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

theorem argsOf_full (a dir : String) : argsOf [a, "full", dir] = ([a], some dir) := rfl

theorem argsOf_one (a : String) : argsOf [a] = ([a], none) := rfl

theorem argsOf_other {args : List String} (h : ∀ a dir, args ≠ [a, "full", dir]) :
    argsOf args = (args, none) := by
  unfold argsOf
  split
  · exact absurd rfl (h _ _)
  · rfl

/-- The theorem of the shell: for every argument list and every response, a run of the program that the `lint`
executable interprets does what the record states. -/
theorem run_meets : RunMeets (Regula.Shell.run : List String → Prog L E UInt32) := by
  intro args t c h
  unfold Regula.Shell.run at h
  obtain ⟨t₁, t₂, v, rfl, h₁, h₂⟩ := runs_bind_iff.mp h
  obtain rfl := runs_call_iff.mp h₁
  obtain ⟨version, commit⟩ := v
  simp only [List.cons_append, List.nil_append]
  have h₃ : Runs (dispatch version commit (argsOf args).1 (argsOf args).2 : Prog L E UInt32) t₂ c := h₂
  have hrefuse : ∀ {a : List String} {project : Option String} {why : String},
      profileOfRun version commit a = .error why →
      Runs (dispatch version commit a project : Prog L E UInt32) t₂ c →
      Refusal (⟨.leanVersion, (version, commit)⟩ :: t₂) c := by
    intro a project why he hr
    unfold dispatch at hr
    rw [he] at hr
    exact refusal_of hr
  have hother : ∀ a : List String, (∀ x dir, a ≠ [x, "full", dir]) → (∀ text, a ≠ [text]) →
      argsOf a = (a, none) ∧ ∃ why, profileOfRun version commit a = .error why :=
    fun a h₁ h₂ => ⟨argsOf_other h₁, profileOfRun_other h₂⟩
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, more⟩⟩⟩⟩
  · obtain ⟨he, why, hw⟩ := hother [] (by simp) (by simp)
    rw [he] at h₃
    exact hrefuse hw h₃
  · have h₄ : Runs (dispatch version commit [a] none : Prog L E UInt32) t₂ c := h₃
    cases hp : Regula.Closed.Profile.ofSpelling? a with
    | none =>
      obtain ⟨why, hw⟩ := profileOfRun_text (version := version) (commit := commit) hp
      simp only [hp]
      exact hrefuse hw h₄
    | some p =>
      simp only [hp]
      refine ⟨(version, commit), t₂, rfl, fun hv => ?_, fun hv => ?_⟩
      · unfold dispatch at h₄
        rw [profileOfRun_ok' hv hp] at h₄
        exact runPlain_spec h₄
      · obtain ⟨why, hw⟩ := profileOfRun_lean (a := [a]) hv
        exact hrefuse hw h₄
  · obtain ⟨he, why, hw⟩ := hother [a, b] (by simp) (by simp)
    rw [he] at h₃
    have hr := hrefuse hw h₃
    split
    · rename_i heq
      simp at heq
    · rename_i heq
      simp at heq
    · exact hr
  · by_cases hb : b = "full"
    · subst hb
      have h₄ : Runs (dispatch version commit [a] (some d) : Prog L E UInt32) t₂ c := h₃
      cases hp : Regula.Closed.Profile.ofSpelling? a with
      | none =>
        obtain ⟨why, hw⟩ := profileOfRun_text (version := version) (commit := commit) hp
        simp only [hp]
        exact hrefuse hw h₄
      | some p =>
        simp only [hp]
        refine ⟨(version, commit), t₂, rfl, fun hv => ?_, fun hv => ?_⟩
        · unfold dispatch at h₄
          rw [profileOfRun_ok' hv hp] at h₄
          exact ⟨t₂, (version, commit), rfl, runFull_spec h₄⟩
        · obtain ⟨why, hw⟩ := profileOfRun_lean (a := [a]) hv
          exact hrefuse hw h₄
    · obtain ⟨he, why, hw⟩ := hother [a, b, d] (by simp [hb]) (by simp)
      rw [he] at h₃
      have hr := hrefuse hw h₃
      split
      · rename_i heq
        simp at heq
      · rename_i heq
        simp at heq
        exact absurd heq.2.1 hb
      · exact hr
  · obtain ⟨he, why, hw⟩ := hother (a :: b :: d :: e :: more) (by simp) (by simp)
    rw [he] at h₃
    have hr := hrefuse hw h₃
    split
    · rename_i heq
      simp at heq
    · rename_i heq
      simp at heq
    · exact hr

end RegulaSpecification.Effects
