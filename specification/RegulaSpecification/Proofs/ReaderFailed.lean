/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.ReaderOnly

/-!
# A failed read is never admitted

For every response: when a read of the reader failed, the check does not admit the project. `readProject_no_failed` states
it of the definition that runs. So no failed answer is ever passed over on the way to an admission.
-/

namespace RegulaSpecification.Effects

open Lean (Name)
open System (FilePath)
open Regula.Effect
open Regula.Language
open Regula.Reader

variable {L E α β : Type}

/-- On every response, a success means that nothing failed on the way. -/
def Sound (x : Attempt L E α) : Prop :=
  ∀ t a, Runs x.run t (.ok a) → ∀ e ∈ t, ¬ e.failed

theorem sound_pure (a : α) : Sound (pure a : Attempt L E α) := by
  intro t b h e he
  obtain ⟨rfl, -⟩ := runs_attempt_pure_iff.mp h
  cases he

theorem sound_throw (w : String) : Sound (throw w : Attempt L E α) := by
  intro t b h
  obtain ⟨-, he⟩ := runs_attempt_throw_iff.mp h
  cases he

theorem sound_seq {x : Attempt L E α} {f : α → Attempt L E β} (hx : Sound x) (hf : ∀ a, Sound (f a)) :
    Sound (x >>= f) := by
  intro t b h e he
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  cases r with
  | error w => cases h₂.2
  | ok a =>
    rcases List.mem_append.mp he with he | he
    · exact hx _ _ h₁ e he
    · exact hf a _ _ h₂ e he

/-- One operation that can fail, whose failure is its error. -/
macro "sound_io" : tactic =>
  `(tactic| (
    intro t a h e he
    obtain ⟨r, h₁, hb⟩ := runs_attempt_iff.mp h
    have hte := runs_call_iff.mp h₁
    subst hte
    cases r with
    | error x => cases hb
    | ok v =>
      have heq : e = _ := List.mem_singleton.mp he
      subst heq
      rintro ⟨x, hx⟩
      cases hx))

theorem sound_realPath (p : FilePath) : Sound (realPath p : Attempt L E _) := by
  unfold realPath
  sound_io

theorem sound_readExact (project path : FilePath) : Sound (readExact project path : Attempt L E _) := by
  rw [readExact]
  refine sound_seq (sound_realPath _) fun real => ?_
  split
  · sound_io
  · exact sound_throw _

theorem sound_makeParent (tree path : FilePath) : Sound (makeParent tree path : Attempt L E _) := by
  rw [makeParent]
  split
  · exact sound_pure _
  · split
    · sound_io
    · exact sound_throw _

theorem sound_writeInTree (tree path : FilePath) (text : String) :
    Sound (writeInTree tree path text : Attempt L E _) := by
  rw [writeInTree]
  split
  · refine sound_seq (sound_makeParent _ _) fun _ => ?_
    sound_io
  · exact sound_throw _

theorem sound_readSource (project tree path : FilePath) : Sound (readSource project tree path : Attempt L E _) := by
  rw [readSource, readForTree]
  refine sound_seq ?_ fun text => sound_seq ?_ fun _ => sound_pure _
  · split
    · exact sound_throw _
    · split
      · exact sound_readExact _ _
      · exact sound_throw _
  · sound_io

theorem sound_writeSources (tree : FilePath) (srcs : List (Name × Source)) :
    Sound (writeSources tree srcs : Attempt L E _) := by
  induction srcs with
  | nil => rw [writeSources]; exact sound_pure _
  | cons x rest ih =>
    obtain ⟨m, s⟩ := x
    rw [writeSources]
    exact sound_seq (sound_writeInTree _ _ _) fun _ => ih

theorem sound_readBack (l : List (FilePath × String)) : Sound (readBack l : Attempt L E _) := by
  induction l with
  | nil => rw [readBack]; exact sound_pure _
  | cons x rest ih =>
    obtain ⟨path, text⟩ := x
    rw [readBack]
    refine sound_seq ?_ fun _ => ?_
    · sound_io
    · split
      · exact ih
      · exact sound_throw _

theorem sound_toolchainOLean (m : Name) : Sound (toolchainOLean m : Attempt L E _) := by
  rw [toolchainOLean]
  refine sound_seq ?_ fun _ => sound_pure _
  sound_io

theorem sound_defaultModules (root : Root L) (targets : List Name) :
    Sound (defaultModules root targets : Attempt L E _) := by
  induction targets with
  | nil => rw [defaultModules]; exact sound_pure _
  | cons t ts ih =>
    rw [defaultModules]
    refine sound_seq ?_ fun _ => sound_seq ih fun _ => sound_pure _
    rw [modulesOfTarget]
    split
    · refine sound_seq ?_ fun _ => sound_pure _
      sound_io
    · split <;> exact sound_pure _

/-- The events of a parse are no failures. -/
theorem parsed_not_failed {input env fuel state messages commands final} {t : List (Event L E)}
    (h : Parsed input env fuel state messages commands final t) : ∀ e ∈ t, ¬ e.failed := by
  induction h with
  | stop => intro e he; cases he
  | last _ =>
    intro e he
    have : e = _ := List.mem_singleton.mp he
    subst this
    exact id
  | next _ _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact id
    · exact ih e he

theorem sound_parseFiles (sources : List (Name × Source)) (toolchain : List Name) (todo : List (Name × Source))
    (cache : ParserCache E) : Sound (parseFiles sources toolchain cache todo : Attempt L E _) := by
  induction todo generalizing cache with
  | nil => rw [parseFiles]; exact sound_pure _
  | cons x todo ih =>
    obtain ⟨m, s⟩ := x
    rw [parseFiles]
    refine sound_seq ?_ fun r => sound_seq (ih _) fun _ => sound_pure _
    rw [parseFile]
    refine sound_seq ?_ fun r => ?_
    · rw [environmentFor]
      split
      · exact sound_pure _
      · refine sound_seq ?_ fun _ => sound_pure _
        sound_io
    · refine sound_seq ?_ fun _ => sound_pure _
      intro t a h e he
      obtain ⟨⟨commands, final⟩, h₁, -⟩ := runs_lift_iff.mp h
      exact parsed_not_failed (parseAll_parsed _ _ _ _ _ h₁) e he

/-- What a walk that left nothing unread asked did not fail, and it started with nothing unread. -/
theorem walk_no_failed (project tree : FilePath) (root : Root L) (modules : List (Name × FilePath))
    (fuel : Nat) (todo : List Name) (w w' : Walk) (t : List (Event L E))
    (h : Runs (walk project tree root modules fuel todo w) t w') (hu : w'.unread = []) :
    w.unread = [] ∧ ∀ e ∈ t, ¬ e.failed := by
  induction fuel generalizing todo w t with
  | zero =>
    cases todo with
    | nil =>
      rw [walk] at h
      obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h
      exact ⟨hu, by simp⟩
    | cons m rest =>
      rw [walk] at h
      obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h
      simp [Walk.leaveUnread] at hu
  | succ fuel ih =>
    cases todo with
    | nil =>
      rw [walk] at h
      obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h
      exact ⟨hu, by simp⟩
    | cons m rest =>
      rw [walk] at h
      split at h
      · exact ih _ _ _ h
      · split at h
        · have := (ih _ _ _ h).1
          simp [Walk.leaveUnread] at this
        · split at h
          · have hi := ih _ _ _ h
            exact ⟨hi.1, hi.2⟩
          · split at h
            · obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
              cases r with
              | ok s =>
                obtain ⟨h1, h2⟩ := ih _ _ _ h₂
                refine ⟨h1, fun e he => ?_⟩
                rcases List.mem_append.mp he with he | he
                · exact sound_readSource _ _ _ _ _ h₁ e he
                · exact h2 e he
              | error x =>
                have := (ih _ _ _ h₂).1
                simp [Walk.leaveUnread] at this
            · obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
              cases r with
              | ok s =>
                obtain ⟨h1, h2⟩ := ih _ _ _ h₂
                refine ⟨h1, fun e he => ?_⟩
                rcases List.mem_append.mp he with he | he
                · exact sound_toolchainOLean _ _ _ h₁ e he
                · exact h2 e he
              | error x =>
                have := (ih _ _ _ h₂).1
                simp [Walk.leaveUnread] at this

/-! ## The stages -/

open RegulaSpecification.Language

/-- What an admitted reading holds of its own fields. -/
theorem admitted_fields {r : Reading} (h : decision r = .admitted) :
    r.toolchainFile = some leanToolchain ∧ r.leanConfig = false ∧ r.openPaths = [] ∧ r.unread = [] ∧
      ¬ MathlibReached r ∧ ¬ RequiresDependency r := by
  obtain ⟨⟨h1, h2, h3, -⟩, h6, h7, h8, -⟩ := (decision_admitted_iff r).mp h
  exact ⟨h1, h2, h3, h6, h8, h7⟩

/-- A reading that stopped with a reason is not admitted. -/
theorem stopped_not_admitted {tf : Option String} {l : Bool} {k : List Name} {why : String} :
    decision (stopped tf l k (some why)) ≠ .admitted := by
  intro h
  have := (admitted_fields h).2.2.2.1
  simp [stopped] at this

theorem readFiles_no_failed {config : List (FilePath × String)} {project tree : FilePath} {root : Root L}
    {modules : List (Name × FilePath)}
    {start r : Reading} {srcs : List (Name × Source)} {t : List (Event L E)}
    (h : Runs (readFiles config project tree root modules start : Attempt L E _).run t (.ok (r, srcs)))
    (ha : decision r = .admitted) : (∀ e ∈ t, ¬ e.failed) ∧ r.toolchainFile = start.toolchainFile := by
  rw [readFiles] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨u, h₃, rfl⟩ := runs_lift_iff.mp h₁
  obtain rfl := runs_call_iff.mp h₃
  obtain ⟨t₅, t₆, r₅, rfl, h₆, h₇⟩ := runs_attempt_bind_iff.mp h₂
  obtain ⟨w, h₈, rfl⟩ := runs_lift_iff.mp h₆
  dsimp only at h₇
  have hcase : (∀ e ∈ t₆, ¬ e.failed) ∧ r.unread = (baseReading config start root modules w).unread ∧
      r.toolchainFile = start.toolchainFile := by
    split at h₇
    · obtain ⟨rfl, he⟩ := runs_attempt_pure_iff.mp h₇
      cases he
      exact ⟨fun e he => (by cases he), rfl, rfl⟩
    · obtain ⟨t₇, t₈, r₇, rfl, h₉, h₁₀⟩ := runs_attempt_bind_iff.mp h₇
      cases r₇ with
      | error x => cases h₁₀.2
      | ok files =>
        dsimp only at h₁₀
        split at h₁₀
        · obtain ⟨t₉, t₁₀, r₉, rfl, h₁₁, h₁₂⟩ := runs_attempt_bind_iff.mp h₁₀
          cases r₉ with
          | error x => cases h₁₂.2
          | ok v =>
            obtain ⟨t₁₁, t₁₂, r₁₁, rfl, h₁₃, h₁₄⟩ := runs_attempt_bind_iff.mp h₁₂
            cases r₁₁ with
            | error x => cases h₁₄.2
            | ok v' =>
              obtain ⟨t₂₁, t₂₂, r₂₁, rfl, h₂₁, h₂₂⟩ := runs_attempt_bind_iff.mp h₁₄
              obtain ⟨r₂, rfl, n1, -⟩ := noOtherConfig_spec h₂₁
              cases r₂₁ with
              | error x => cases h₂₂.2
              | ok u =>
                obtain ⟨rfl, he⟩ := runs_attempt_pure_iff.mp h₂₂
                cases he
                refine ⟨fun e he => ?_, rfl, rfl⟩
                simp only [List.append_nil, List.mem_append] at he
                rcases he with he | he | he | he
                · exact sound_parseFiles _ _ _ _ _ _ h₉ e he
                · exact sound_writeSources _ _ _ _ h₁₁ e he
                · exact sound_readBack _ _ _ h₁₃ e he
                · obtain ⟨err, rfl, name, code, details, rfl⟩ := n1 rfl
                  obtain rfl := List.mem_singleton.mp he
                  rintro ⟨x, hx, hne⟩
                  cases hx
                  exact hne _ _ _ rfl
        · obtain ⟨rfl, he⟩ := runs_attempt_pure_iff.mp h₁₀
          cases he
          refine ⟨fun e he => ?_, rfl, rfl⟩
          simp only [List.append_nil] at he
          exact sound_parseFiles _ _ _ _ _ _ h₉ e he
  have hw : w.unread = [] := by
    have := (admitted_fields ha).2.2.2.1
    rw [hcase.2.1] at this
    simp only [baseReading, List.append_eq_nil_iff, List.reverse_eq_nil_iff] at this
    exact this.1.1
  obtain ⟨-, hwalk⟩ := walk_no_failed _ _ _ _ _ _ _ _ _ h₈ hw
  refine ⟨fun e he => ?_, hcase.2.2⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at he
  rcases he with rfl | he | he
  · exact id
  · exact hwalk e he
  · exact hcase.1 e he


theorem readRoot_no_failed {config : List (FilePath × String)} {sysroot : String} {project tree : FilePath}
    {start r : Reading} {srcs : List (Name × Source)} {t : List (Event L E)}
    (h : Runs (readRoot config sysroot project tree start : Attempt L E _).run t (.ok (r, srcs)))
    (ha : decision r = .admitted) : (∀ e ∈ t, ¬ e.failed) ∧ r.toolchainFile = start.toolchainFile := by
  rw [readRoot] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨t₃, t₄, r₃, rfl, h₃, h₄⟩ := runs_bind_iff.mp h₁
  obtain rfl := runs_call_iff.mp h₃
  obtain ⟨rfl, rfl⟩ := runs_done_iff.mp h₄
  cases hl : loaded "the configuration" r₃ with
  | error w =>
    rw [hl] at h₂
    cases h₂.2
  | ok root =>
    rw [hl] at h₂
    have hev : ¬ Event.failed (⟨.loadRoot sysroot tree, r₃⟩ : Event L E) := by
      rintro (⟨e, rfl⟩ | ⟨log, rfl⟩) <;> cases hl
    dsimp only at h₂
    split at h₂
    · rename_i hopen
      obtain ⟨-, he⟩ := runs_attempt_pure_iff.mp h₂
      cases he
      have := (admitted_fields ha).2.2.1
      simp only at this
      simp [this] at hopen
    · obtain ⟨t₅, t₆, r₅, rfl, h₅, h₆⟩ := runs_attempt_bind_iff.mp h₂
      cases r₅ with
      | error w => cases h₆.2
      | ok modules =>
        dsimp only at h₆
        split at h₆
        · rename_i hfail
          obtain ⟨-, he⟩ := runs_attempt_pure_iff.mp h₆
          cases he
          have := (admitted_fields ha).2.2.2.1
          simp only at this
          simp [this] at hfail
        · obtain ⟨f1, f2⟩ := readFiles_no_failed h₆ ha
          refine ⟨fun e he => ?_, f2⟩
          simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.mem_append] at he
          rcases he with rfl | he | he
          · exact hev
          · exact sound_defaultModules _ _ _ _ h₅ e he
          · exact f1 e he

theorem readKeys_no_failed {sysroot : String} {project tree : FilePath} {tf : Option String} {text : String}
    {r : Reading} {srcs : List (Name × Source)} {t : List (Event L E)}
    (h : Runs (readKeys sysroot project tree tf text : Attempt L E _).run t (.ok (r, srcs)))
    (ha : decision r = .admitted) : (∀ e ∈ t, ¬ e.failed) ∧ r.toolchainFile = tf := by
  rw [readKeys] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r₂, h₃, rfl⟩ := runs_lift_iff.mp h₁
  obtain rfl := runs_call_iff.mp h₃
  cases r₂ with
  | error log =>
    obtain ⟨-, he⟩ := runs_attempt_pure_iff.mp h₂
    cases he
    exact absurd ha stopped_not_admitted
  | ok table =>
    dsimp only at h₂
    split at h₂
    · rename_i hcond
      obtain ⟨-, he⟩ := runs_attempt_pure_iff.mp h₂
      cases he
      obtain ⟨hc, -, hd, -⟩ := (decision_admitted_iff _).mp ha
      have hc' := (configClosed_iff _).mpr hc
      have hd' : (stopped tf false (keysOf 8 .anonymous table) none).requiresDependency = false := by
        cases hx : (stopped tf false (keysOf 8 .anonymous table) none).requiresDependency with
        | false => rfl
        | true => exact absurd ((requiresDependency_iff _).mp hx) hd
      simp [hc', hd'] at hcond
    · obtain ⟨t₃, t₄, r₃, rfl, h₄, h₅⟩ := runs_attempt_bind_iff.mp h₂
      cases r₃ with
      | error w => cases h₅.2
      | ok u =>
        obtain ⟨t₅, t₆, r₅, rfl, h₆, h₇⟩ := runs_attempt_bind_iff.mp h₅
        cases r₅ with
        | error w => cases h₇.2
        | ok v =>
          obtain ⟨f1, f2⟩ := readRoot_no_failed h₇ ha
          refine ⟨fun e he => ?_, f2⟩
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at he
          rcases he with rfl | he | he | he
          · exact fun ⟨x, hx⟩ => by cases hx
          · exact sound_writeInTree _ _ _ _ _ h₄ e he
          · exact sound_writeInTree _ _ _ _ _ h₆ e he
          · exact f1 e he

theorem readConfig_no_failed {sysroot : String} {project tree : FilePath} {tf : Option String} {r : Reading}
    {srcs : List (Name × Source)} {t : List (Event L E)}
    (h : Runs (readConfig sysroot project tree tf : Attempt L E _).run t (.ok (r, srcs)))
    (ha : decision r = .admitted) : (∀ e ∈ t, ¬ e.failed) ∧ r.toolchainFile = tf := by
  rw [readConfig] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r₃, rfl, e1, e2, e3⟩ := existsByName_spec h₁
  cases r₁ with
  | error w => cases h₂.2
  | ok present =>
    cases present with
    | true =>
      obtain ⟨-, he⟩ := runs_attempt_pure_iff.mp h₂
      cases he
      have := (admitted_fields ha).2.1
      simp [stopped] at this
    | false =>
      obtain ⟨x, rfl, name, code, details, rfl⟩ := e2 rfl
      have hev : ¬ Event.failed (⟨.symlinkMetadata (project / "lakefile.lean"),
          .error (.noFileOrDirectory name code details)⟩ : Event L E) := by
        rintro ⟨x, hx, hne⟩
        cases hx
        exact hne _ _ _ rfl
      obtain ⟨t₃, t₄, r₃', rfl, h₃, h₄⟩ := runs_attempt_bind_iff.mp h₂
      obtain ⟨r₅, h₅, rfl⟩ := runs_lift_iff.mp h₃
      cases r₅ with
      | error why =>
        obtain ⟨-, he⟩ := runs_attempt_pure_iff.mp h₄
        cases he
        exact absurd ha stopped_not_admitted
      | ok text =>
        obtain ⟨f1, f2⟩ := readKeys_no_failed h₄ ha
        refine ⟨fun e he => ?_, f2⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at he
        rcases he with rfl | he | he
        · exact hev
        · exact sound_readExact _ _ _ _ h₅ e he
        · exact f1 e he

/-- The theorem that a failed read is never admitted, of the definition that runs: on an admission, no answer that
the reader asked failed. So a run in which an answer failed gives no admission. -/
theorem readProject_no_failed {sysroot : String} {dir treeDir : FilePath} {r : Reading}
    {srcs : List (Name × Source)} {t : List (Event L E)}
    (h : Runs (readProject sysroot dir treeDir : Attempt L E _).run t (.ok (r, srcs)))
    (ha : decision r = .admitted) : ∀ e ∈ t, ¬ e.failed := by
  rw [readProject] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  cases r₁ with
  | error w => cases h₂.2
  | ok project =>
    obtain ⟨t₃, t₄, r₃, rfl, h₃, h₄⟩ := runs_attempt_bind_iff.mp h₂
    cases r₃ with
    | error w => cases h₄.2
    | ok tree =>
      obtain ⟨t₉, t₁₀, r₉, rfl, h₁₀, h₁₁⟩ := runs_attempt_bind_iff.mp h₄
      obtain ⟨tf, h₁₂, rfl⟩ := runs_lift_iff.mp h₁₀
      dsimp only at h₁₁
      rw [toolchainOf] at h₁₂
      obtain ⟨t₁₁, t₁₂, r₁₁, rfl, h₁₃, h₁₄⟩ := runs_seq_iff.mp h₁₂
      have hreal₁ := sound_realPath (L := L) (E := E) dir _ _ h₁
      have hreal₂ := sound_realPath (L := L) (E := E) treeDir _ _ h₃
      have hrest : (∀ e ∈ t₁₀, ¬ e.failed) ∧ r.toolchainFile = tf := by
        split at h₁₁
        · obtain ⟨-, he⟩ := runs_attempt_pure_iff.mp h₁₁
          cases he
          exact absurd ha stopped_not_admitted
        · exact readConfig_no_failed h₁₁ ha
      obtain ⟨f1, f2⟩ := hrest
      have htc : ∀ e ∈ t₁₁, ¬ e.failed := by
        cases r₁₁ with
        | ok text => exact sound_readExact _ _ _ _ h₁₃
        | error why =>
          obtain ⟨-, rfl⟩ := runs_pure_iff.mp h₁₄
          have := (admitted_fields ha).1
          rw [f2] at this
          cases this
      obtain ⟨rfl, -⟩ : t₁₂ = [] ∧ True := by
        cases r₁₁ with
        | ok text => exact ⟨(runs_pure_iff.mp h₁₄).1, trivial⟩
        | error why => exact ⟨(runs_pure_iff.mp h₁₄).1, trivial⟩
      intro e he
      simp only [List.append_nil, List.mem_append] at he
      rcases he with he | he | he | he
      · exact hreal₁ e he
      · exact hreal₂ e he
      · exact htc e he
      · exact f1 e he

end RegulaSpecification.Effects
