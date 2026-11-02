/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.EffectsRecord

/-!
# Consequences of ordered preparation

These consequences read the contract alone. The exact copy segments determine their first act;
`ReadingPreparation.first_directory` makes a directory that is the first tree act the TOML copy's parent, and
`manufacturedCopy_fails` excludes the reported trace with no toolchain answer, and `manufacturedCopyAnswered_fails` the
trace with that answer present, through the copy grammar and `parent_ne_self`, for every path, text, error, profile and
exit code.
`BuildAndRules.no_mutation` and `FullRun.after_removal_saying` constrain the later phases, and `ModuleCopies.not_barred` and
`InputPreparation.not_barred` state that no load, command, removal or allocation occurs among them. The one theorem of each stage (`readProject_spec`, `inputOf_spec`, `loadTree_spec`, `loadPlain_spec`, `rules_spec`) establishes the ordered
relations for the actual reader and loaders, composed in `run_meets`, for every response. No result
here assumes consistent filesystem responses or describes effects inside trusted Lean/Lake calls.
-/

namespace RegulaSpecification.Effects

open System (FilePath)
open Regula.Effect
open RegulaSpecification.Language
open String.Slice.Pattern String.Slice.Pattern.ToBackwardSearcher

variable {L E : Type}

/-! ## The structure of the grammar -/

theorem quiet_nil : Quiet (L := L) (E := E) [] := by simp [Quiet]

theorem Quiet.append {a b : List (Event L E)} (ha : Quiet a) (hb : Quiet b) : Quiet (a ++ b) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact ha e he
  · exact hb e he

theorem Quiet.noActs {t : List (Event L E)} (h : Quiet t) : ∀ e ∈ t, e.acted? = none := by
  intro e he
  have hq := h e he
  obtain ⟨o, r⟩ := e
  cases o <;> first | rfl | exact hq.elim

/-- Each event of a literal list of events is quiet. -/
macro "quiet_events" : tactic =>
  `(tactic| (
    intro x hx
    simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
    (repeat' rcases hx with rfl | hx) <;> subst_vars <;> exact trivial))

theorem quiet_one {o : Op L E} {r} (h : QuietOp o) : Quiet ([⟨o, r⟩] : List (Event L E)) := by
  intro e he
  obtain rfl := List.mem_singleton.mp he
  exact h

theorem ModuleCopies.append {project tree : FilePath} {root : Root L} {modules}
    {prior a b : List (Event L E)} (ha : ModuleCopies project tree root modules prior a)
    (hb : ModuleCopies project tree root modules (prior ++ a) b) :
    ModuleCopies project tree root modules prior (a ++ b) := by
  induction ha with
  | nil => simpa using hb
  | @observe prior e rest he ht ih =>
    exact .observe he (ih (by simpa [List.append_assoc] using hb))
  | @copy prior m path text step rest complete hn hp hs hc ht ih =>
    simpa [List.append_assoc] using ModuleCopies.copy hn hp hs hc
      (ih (by simpa [List.append_assoc] using hb))

theorem ModuleCopies.observations {project tree : FilePath} {root : Root L} {modules}
    (prior : List (Event L E)) {t : List (Event L E)} (h : ∀ e ∈ t, QuietOp e.op ∨ ParserSearchOp root e.op) :
    ModuleCopies project tree root modules prior t := by
  induction t generalizing prior with
  | nil => exact .nil
  | cons e t ih =>
    exact .observe (h e (by simp)) (ih _ fun x hx => h x (by simp [hx]))

theorem ReadingLoaded.prepend {prior before t : List (Event L E)} {project tree : FilePath} {root : Root L}
    (hq : Quiet before) (h : ReadingLoaded (prior ++ before) project tree root t) :
    ReadingLoaded prior project tree root (before ++ t) := by
  rcases h with h | ⟨pre, rest, modules, rfl, hp, hm, hc⟩
  · exact .inl (hq.append h)
  · exact .inr ⟨before ++ pre, rest, modules, by simp [List.append_assoc], hq.append hp,
      by simpa [List.append_assoc] using hm, by simpa [List.append_assoc] using hc⟩

theorem ReadingLoaded.appendQuiet {prior t after : List (Event L E)} {project tree : FilePath} {root : Root L}
    (h : ReadingLoaded prior project tree root t) (hq : Quiet after) :
    ReadingLoaded prior project tree root (t ++ after) := by
  rcases h with h | ⟨pre, rest, modules, rfl, hp, hm, hc⟩
  · exact .inl (h.append hq)
  · refine .inr ⟨pre, rest ++ after, modules, by simp, hp, hm, ?_⟩
    exact hc.append (.observations _ fun e he => .inl (hq e he))

theorem ReadingLoad.appendQuiet {prior t after : List (Event L E)} {sysroot : String} {project tree : FilePath}
    (h : ReadingLoad prior sysroot project tree t) (hq : Quiet after) :
    ReadingLoad prior sysroot project tree (t ++ after) := by
  rcases h with h | ⟨pre, response, rest, rfl, hp, hc⟩
  · exact .inl (h.append hq)
  · refine .inr ⟨pre, response, rest ++ after, by simp, hp, ?_⟩
    cases response with
    | error error => exact hc.append hq
    | ok pair =>
      obtain ⟨root, log⟩ := pair
      cases root with
      | none => exact hc.append hq
      | some root => exact hc.appendQuiet hq

theorem ConfigCopies.appendQuiet {prior t after : List (Event L E)} {sysroot : String}
    {project tree : FilePath} {copies} (h : ConfigCopies sysroot project tree copies prior t) (hq : Quiet after) :
    ConfigCopies sysroot project tree copies prior (t ++ after) := by
  induction h with
  | done h => exact .done (h.appendQuiet hq)
  | stopped h => exact .stopped (h.append hq)
  | failed hp hc hr => simpa [List.append_assoc] using ConfigCopies.failed hp hc (hr.append hq)
  | next hp hc hr ih => simpa [List.append_assoc] using ConfigCopies.next hp hc ih

theorem ReadingPreparation.appendQuiet {t after : List (Event L E)} {dir treeDir : FilePath}
    (h : ReadingPreparation t dir treeDir) (hq : Quiet after) : ReadingPreparation (t ++ after) dir treeDir := by
  rcases h with h | ⟨project, tree, sysroot, text, before, rest, rfl, hp, h1, h2, ha, h3, h4, hc⟩
  · exact .inl (h.append hq)
  · exact .inr ⟨project, tree, sysroot, text, before, rest ++ after, by simp [List.append_assoc],
      hp, h1, h2, ha, h3, h4, hc.appendQuiet hq⟩

theorem InputPreparation.prepend {before t : List (Event L E)} {root : Root L}
    (hq : Quiet before) (h : InputPreparation root t) : InputPreparation root (before ++ t) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact .inl (hq e he)
  · exact h e he

theorem InputPreparation.appendQuiet {t after : List (Event L E)} {root : Root L}
    (h : InputPreparation root t) (hq : Quiet after) : InputPreparation root (t ++ after) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact h e he
  · exact .inl (hq e he)

theorem RulesPreparation.appendQuiet {t after : List (Event L E)} {sysroot : String} {tree : FilePath}
    (h : RulesPreparation sysroot tree t) (hq : Quiet after) : RulesPreparation sysroot tree (t ++ after) := by
  rcases h with h | ⟨pre, real, response, rest, rfl, hp, hm, hr⟩
  · exact .inl (h.append hq)
  · refine .inr ⟨pre, real, response, rest ++ after, by simp, hp, hm, ?_⟩
    cases response with
    | error error => exact hr.append hq
    | ok pair =>
      obtain ⟨root, log⟩ := pair
      cases root with
      | none => exact hr.append hq
      | some root => exact hr.appendQuiet hq

theorem PlainPreparation.appendQuiet {t after : List (Event L E)}
    (h : PlainPreparation t) (hq : Quiet after) : PlainPreparation (t ++ after) := by
  rcases h with h | ⟨pre, sysroot, dir, response, rest, rfl, hp, hs, hd, hr⟩
  · exact .inl (h.append hq)
  · refine .inr ⟨pre, sysroot, dir, response, rest ++ after, by simp, hp, hs, hd, ?_⟩
    cases response with
    | error error => exact hr.append hq
    | ok pair =>
      obtain ⟨root, log⟩ := pair
      cases root with
      | none => exact hr.append hq
      | some root => exact hr.appendQuiet hq

/-! ## One copy -/

/-- What a copy that completed did: it made directories, each with a successful answer, and then wrote, and the path lies in the tree. -/
theorem CopyStep.complete {tree path : FilePath} {text : String} {t : List (Event L E)} {c : Bool}
    (h : CopyStep tree path text t c) (hc : c = true) :
    (∃ before, t = before ++ [⟨.writeFile path text, .ok ()⟩] ∧ ∀ e ∈ before, ∃ d, e = (⟨.createDirAll d, .ok ()⟩ : Event L E)) ∧
      ¬ OutsideTree tree path := by
  have inside : ∀ {rel}, TreeRelative (parts tree) (parts path) rel → (∀ d, path.parent = some d →
      ∃ rel, TreeRelative (parts tree) (parts d) rel) → ¬ OutsideTree tree path := by
    rintro rel hrel hd (hx | ⟨d, hp, hx⟩)
    · exact hx rel hrel
    · obtain ⟨rel', h'⟩ := hd d hp
      exact hx rel' h'
  cases h with
  | outside _ => cases hc
  | @noParent r hrel hp =>
    cases r with
    | error e => cases hc
    | ok u =>
      obtain ⟨rel, hrel⟩ := hrel
      exact ⟨⟨[], rfl, by simp⟩, inside hrel fun d hd => by rw [hp] at hd; cases hd⟩
  | parentFailed _ _ _ => cases hc
  | @parentWritten parent r hrel hp hd =>
    cases r with
    | error e => cases hc
    | ok u =>
      obtain ⟨rel, hrel⟩ := hrel
      refine ⟨⟨[⟨.createDirAll parent, .ok ()⟩], rfl, fun e he => ⟨parent, List.mem_singleton.mp he⟩⟩, inside hrel fun d hd' => ?_⟩
      rw [hp] at hd'
      cases hd'
      exact hd

/-- What a copy that did not complete shows: its path lies outside the tree, or an act of it failed. -/
theorem CopyStep.incomplete {tree path : FilePath} {text : String} {t : List (Event L E)} {c : Bool}
    (h : CopyStep tree path text t c) (hc : c = false) :
    OutsideTree tree path ∨ ∃ e ∈ t, Event.failed e ∧
      ((∃ d, path.parent = some d ∧ e.op = .createDirAll d) ∨ e.op = .writeFile path text) := by
  cases h with
  | outside h => exact .inl h
  | @noParent r _ _ =>
    cases r with
    | error x => exact .inr ⟨⟨.writeFile path text, .error x⟩, by simp, ⟨x, rfl⟩, .inr rfl⟩
    | ok u => cases hc
  | @parentFailed parent x _ hp _ => exact .inr ⟨⟨.createDirAll parent, .error x⟩, by simp, ⟨x, rfl⟩, .inl ⟨parent, hp, rfl⟩⟩
  | @parentWritten parent r _ _ _ =>
    cases r with
    | error x => exact .inr ⟨⟨.writeFile path text, .error x⟩, by simp, ⟨x, rfl⟩, .inr rfl⟩
    | ok u => cases hc

/-! ## Every act of a reading lies in the tree -/

/-- Every act of these events lies at or below the tree. -/
def ActsBelow (tree : FilePath) (t : List (Event L E)) : Prop :=
  ∀ e ∈ t, ∀ p, e.acted? = some p → AtOrBelow tree p

theorem ActsBelow.append {tree : FilePath} {a b : List (Event L E)} (ha : ActsBelow tree a) (hb : ActsBelow tree b) :
    ActsBelow tree (a ++ b) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact ha e he
  · exact hb e he

theorem Quiet.actsBelow {t : List (Event L E)} (h : Quiet t) (tree : FilePath) : ActsBelow tree t := by
  intro e he p hp
  rw [h.noActs e he] at hp
  cases hp

theorem CopyStep.actsBelow {tree path : FilePath} {text : String} {t : List (Event L E)} {c : Bool}
    (h : CopyStep tree path text t c) : ActsBelow tree t := by
  have below : ∀ {p}, (∃ rel, TreeRelative (parts tree) (parts p) rel) → AtOrBelow tree p :=
    fun ⟨rel, hrel⟩ => ⟨rel, hrel.1.symm⟩
  intro e he p hp
  cases h with
  | outside _ => cases he
  | noParent hrel _ =>
    obtain rfl := List.mem_singleton.mp he
    cases hp
    exact below hrel
  | parentFailed _ _ hd =>
    obtain rfl := List.mem_singleton.mp he
    cases hp
    exact below hd
  | parentWritten hrel _ hd =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> cases hp
    · exact below hd
    · exact below hrel

theorem ModuleCopies.actsBelow {project tree : FilePath} {root : Root L} {modules} {prior t : List (Event L E)}
    (h : ModuleCopies project tree root modules prior t) : ActsBelow tree t := by
  induction h with
  | nil => intro e he; cases he
  | @observe _ e _ hq _ ih =>
    intro x hx p hp
    rcases List.mem_cons.mp hx with rfl | hx
    · obtain ⟨o, r⟩ := x
      cases o <;> first | (rcases hq with hq | hq <;> exact hq.elim) | cases hp
    · exact ih x hx p hp
  | copy _ _ _ hstep _ ih => exact hstep.actsBelow.append ih

theorem ReadingLoaded.actsBelow {prior t : List (Event L E)} {project tree : FilePath} {root : Root L}
    (h : ReadingLoaded prior project tree root t) : ActsBelow tree t := by
  rcases h with h | ⟨pre, rest, modules, rfl, hp, -, hc⟩
  · exact h.actsBelow tree
  · exact (hp.actsBelow tree).append hc.actsBelow

theorem ReadingLoad.actsBelow {prior t : List (Event L E)} {sysroot : String} {project tree : FilePath}
    (h : ReadingLoad prior sysroot project tree t) : ActsBelow tree t := by
  rcases h with h | ⟨pre, response, rest, rfl, hp, hc⟩
  · exact h.actsBelow tree
  · refine (hp.actsBelow tree).append (ActsBelow.append (a := [⟨.loadRoot sysroot tree, response⟩]) ?_ ?_)
    · intro e he p hp'
      obtain rfl := List.mem_singleton.mp he
      cases hp'
    · cases response with
      | error error => exact Quiet.actsBelow hc tree
      | ok pair =>
        obtain ⟨root, log⟩ := pair
        cases root with
        | none => exact Quiet.actsBelow hc tree
        | some root => exact ReadingLoaded.actsBelow hc

theorem ConfigCopies.actsBelow {prior t : List (Event L E)} {sysroot : String} {project tree : FilePath} {copies}
    (h : ConfigCopies sysroot project tree copies prior t) : ActsBelow tree t := by
  induction h with
  | done h => exact h.actsBelow
  | stopped h => exact h.actsBelow tree
  | failed hp hc hr => exact ((hp.actsBelow tree).append hc.actsBelow).append (hr.actsBelow tree)
  | next hp hc _ ih => exact ((hp.actsBelow tree).append hc.actsBelow).append ih

/-- What the acts of a reading are: none, or all at or below a tree that lies apart from the project. -/
def ReadActs (t : List (Event L E)) (dir treeDir : FilePath) : Prop :=
  (∀ e ∈ t, e.acted? = none) ∨
    ∃ project tree, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t ∧
      (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t ∧ Apart project tree ∧ ActsBelow tree t

/-- The grammar of a reading places every act in the tree, so this needs no statement of its own about each stage. -/
theorem ReadingPreparation.readActs {t : List (Event L E)} {dir treeDir : FilePath} (h : ReadingPreparation t dir treeDir) :
    ReadActs t dir treeDir := by
  rcases h with h | ⟨project, tree, sysroot, text, before, rest, rfl, hq, h1, h2, ha, -, -, hc⟩
  · exact .inl h.noActs
  · exact .inr ⟨project, tree, List.mem_append_left _ h1, List.mem_append_left _ h2, ha,
      (hq.actsBelow tree).append hc.actsBelow⟩

/-- Only the specified command and reporting occur in a command segment. -/
theorem LakeInvocation.operations {program tree : FilePath} {args : List String} {response}
    {t : List (Event L E)} (h : LakeInvocation program tree args response t) :
    ∀ e ∈ t, e.isOnlySaying = true ∨ e.op = .runLake program tree args := by
  obtain ⟨pre, post, rfl, hp, hq⟩ := h
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact .inl (hp e he)
  · rcases List.mem_cons.mp he with rfl | he
    · exact .inr rfl
    · exact .inl (hq e he)

/-- All requests in the build phase identify Lake, invoke its specified commands or report. -/
theorem BuildProtocol.operations {sysroot : String} {tree : FilePath} {t : List (Event L E)}
    (h : BuildProtocol sysroot tree t) :
    ∃ program, ∀ e ∈ t, e.isOnlySaying = true ∨ e.op = .lakeInstall sysroot ∨
      e.op = .runLake program tree ["build", "--wfail"] ∨ e.op = .runLake program tree replayArguments := by
  obtain ⟨program, lakeLib, first, rest, response, rfl, hf, hr⟩ := h
  refine ⟨program, fun e he => ?_⟩
  rcases List.mem_cons.mp he with rfl | he
  · exact .inr (.inl rfl)
  · rcases List.mem_append.mp he with he | he
    · rcases hf.operations e he with hs | hl
      · exact .inl hs
      · exact .inr (.inr (.inl hl))
    · rcases hr with ⟨-, rfl⟩ | ⟨-, replay, hr⟩
      · cases he
      · rcases hr.operations e he with hs | hl
        · exact .inl hs
        · exact .inr (.inr (.inr hl))

/-- What may not occur among the module copies or the rules' reading: a load, a Lake command, a removal or an allocation.
Stated apart from `QuietOp`, `ParserSearchOp` and `RulesSearchOp`, so that a phase's list of allowed operations that came to hold one of these
fails `ModuleCopies.not_barred` or `InputPreparation.not_barred`. -/
def Barred : Op L E → Prop
  | .loadRoot .. | .loadWorkspace .. | .runLake .. | .removeDirAll _ | .createTempDir => True
  | _ => False

/-- The module copies of a reading hold nothing that `Barred` names. -/
theorem ModuleCopies.not_barred {project tree : FilePath} {root : Root L} {modules : List (Lean.Name × FilePath)}
    {prior t : List (Event L E)} (h : ModuleCopies project tree root modules prior t) : ∀ e ∈ t, ¬ Barred e.op := by
  induction h with
  | nil => simp
  | observe hq _ ih =>
    rename_i e rest
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · obtain ⟨o, r⟩ := x
      cases o <;> simp_all [Barred, QuietOp, ParserSearchOp]
    · exact ih x hx
  | copy _ _ _ hstep _ ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · cases hstep <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
        first
          | (subst hx; simp [Barred])
          | (rcases hx with rfl | rfl <;> simp [Barred])
          | cases hx
    · exact ih x hx

/-- What the rules read holds nothing that `Barred` names. -/
theorem InputPreparation.not_barred {root : Root L} {t : List (Event L E)} (h : InputPreparation root t) :
    ∀ e ∈ t, ¬ Barred e.op := by
  intro x hx
  obtain ⟨o, r⟩ := x
  have := h _ hx
  cases o <;> simp_all [Barred, QuietOp, RulesSearchOp]

/-- No explicit write, directory creation, allocation or removal belongs to either phase. Effects
inside trusted Lean/Lake calls are not events of this trace. -/
theorem BuildAndRules.no_mutation {sysroot : String} {tree : FilePath} {tBuild tRules : List (Event L E)}
    {p : Regula.Closed.Profile} {report : Regula.Language.Report}
    (h : BuildAndRules sysroot tBuild tRules tree p report) :
    ∀ e ∈ tBuild ++ tRules, (match e.op with
      | .writeFile .. | .createDirAll _ | .createTempDir | .removeDirAll _ => False
      | _ => True) := by
  obtain ⟨program, hp⟩ := h.1.operations
  intro e he
  rcases List.mem_append.mp he with he | he
  · rcases hp e he with hs | hi | hb | hr
    · obtain ⟨o, r⟩ := e
      cases o <;> first | trivial | cases hs
    · rw [hi]; trivial
    · rw [hb]; trivial
    · rw [hr]; trivial
  · have hr := h.2.1 e he
    obtain ⟨o, r⟩ := e
    cases o <;> first | trivial | exact hr.elim

/-- In every full run, no event removes a directory, or one does, with no removal before it and only
reporting after it, whatever its response. -/
theorem FullRun.removal_order {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile} {c : UInt32}
    (h : FullRun t dir p c) :
    (∀ e ∈ t, NotRemoving e.op) ∨
      ∃ tree response pre post, t = pre ++ ⟨.removeDirAll tree, response⟩ :: post ∧
        (∀ e ∈ pre, NotRemoving e.op) ∧ (∀ e ∈ post, e.isOnlySaying = true) := by
  have saying {e : Event L E} (hs : e.isOnlySaying = true) : NotRemoving e.op := by
    obtain ⟨o, r⟩ := e
    cases o <;> first | trivial | cases hs
  rcases h with ⟨error, rest, rfl, -, -, hs⟩ |
    ⟨tree, tRead, tGate, response, last, ht, -, hlast, o, report, -, -, hn, ha, -, -, -, -, hkeep, -⟩
  · left
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · trivial
    · exact saying (hs e he)
  · right
    refine ⟨tree, response, ⟨.createTempDir, .ok tree⟩ :: (tRead ++ tGate), last,
      by simpa using ht, ?_, hlast⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · trivial
    · rcases List.mem_append.mp he with he | he
      · exact hkeep e he
      · by_cases ho : o = .admitted
        · obtain ⟨sysroot, tBuild, tRules, -, hgate, hb⟩ := ha ho
          rw [hgate] at he
          have hm := hb.no_mutation e he
          obtain ⟨op, r⟩ := e
          cases op <;> first | trivial | exact hm.elim
        · rw [(hn ho).1] at he
          cases he

/-- Every operation following a removal only reports. The statement quantifies over all paths,
responses and trace positions, so it also excludes reload and import after removal. -/
theorem FullRun.after_removal_saying {t : List (Event L E)} {dir : FilePath}
    {p : Regula.Closed.Profile} {c : UInt32} (h : FullRun t dir p c) :
    ∀ pre path response rest, t = pre ++ ⟨.removeDirAll path, response⟩ :: rest →
      ∀ e ∈ rest, e.isOnlySaying = true := by
  intro pre path response rest ht
  rcases h.removal_order with hn | ⟨tree, r, before, after, he, hbefore, hafter⟩
  · have hm : (⟨.removeDirAll path, response⟩ : Event L E) ∈ t := by simp [ht]
    exact (hn _ hm).elim
  · have compare := List.append_eq_append_iff.mp (ht.symm.trans he)
    rcases compare with ⟨middle, hpre, htail⟩ | ⟨middle, hpre, htail⟩
    · cases middle with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at htail
        rw [htail.2]
        exact hafter
      | cons x xs =>
        simp only [List.cons_append, List.cons.injEq] at htail
        have hm : (⟨.removeDirAll path, response⟩ : Event L E) ∈ before := by
          rw [hpre]
          simp [← htail.1]
        exact (hbefore _ hm).elim
    · cases middle with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at htail
        rw [← htail.2]
        exact hafter
      | cons x xs =>
        simp only [List.cons_append, List.cons.injEq] at htail
        have hm : (⟨.removeDirAll path, response⟩ : Event L E) ∈ after := by
          rw [htail.2]
          simp
        have hs := hafter _ hm
        cases hs

/-- A removal cannot precede any later Lake command in a full run. -/
theorem FullRun.no_remove_before_command {t : List (Event L E)} {dir : FilePath}
    {p : Regula.Closed.Profile} {c : UInt32} (h : FullRun t dir p c) :
    ∀ pre path response rest, t = pre ++ ⟨.removeDirAll path, response⟩ :: rest →
      ∀ e ∈ rest, e.isBuild = false := by
  intro pre path response rest ht e he
  have hs := h.after_removal_saying pre path response rest ht e he
  obtain ⟨op, r⟩ := e
  cases op <;> first | rfl | cases hs

/-- The requests that change a file or a directory or run a command, retaining order and responses. -/
def treeActs (t : List (Event L E)) : List (Event L E) := t.filter fun e => e.acted?.isSome

theorem treeActs_append (a b : List (Event L E)) : treeActs (a ++ b) = treeActs a ++ treeActs b :=
  List.filter_append a b

theorem Quiet.treeActs_nil {t : List (Event L E)} (h : Quiet t) : treeActs t = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro e he
  have hq := h e he
  obtain ⟨op, response⟩ := e
  cases op <;> simp_all [QuietOp, Event.acted?]

/-- The first act of a copy is its own parent creation, or its write when it has no parent. -/
def CopyHead (path : FilePath) (text : String) (e : Event L E) : Prop :=
  (∃ parent response, path.parent = some parent ∧ e = ⟨.createDirAll parent, response⟩) ∨
    (path.parent = none ∧ ∃ response, e = ⟨.writeFile path text, response⟩)

theorem CopyStep.first {tree path : FilePath} {text : String} {t : List (Event L E)} {complete : Bool}
    (h : CopyStep tree path text t complete) :
    (complete = false ∧ treeActs t = []) ∨ ∃ e rest, treeActs t = e :: rest ∧ CopyHead path text e := by
  cases h with
  | outside _ => exact .inl ⟨rfl, rfl⟩
  | noParent _ hp => exact .inr ⟨_, [], rfl, .inr ⟨hp, _, rfl⟩⟩
  | parentFailed _ hp _ => exact .inr ⟨_, [], rfl, .inl ⟨_, _, hp, rfl⟩⟩
  | parentWritten _ hp _ => exact .inr ⟨_, [_], rfl, .inl ⟨_, _, hp, rfl⟩⟩

/-- No later copy can supply the first act: the first configuration step either makes it or stops all
acts. This rules out a preparation directory chosen independently of that step's parent. -/
theorem ConfigCopies.first {sysroot : String} {project tree path : FilePath} {text : String} {copies}
    {prior t : List (Event L E)} (h : ConfigCopies sysroot project tree ((path, text) :: copies) prior t) :
    treeActs t = [] ∨ ∃ e rest, treeActs t = e :: rest ∧ CopyHead path text e := by
  cases h with
  | stopped hq => exact .inl hq.treeActs_nil
  | failed hpre hc hrest =>
    rename_i before step rest
    have he : treeActs (before ++ step ++ rest) = treeActs step := by
      rw [treeActs_append, treeActs_append]
      rw [hpre.treeActs_nil, hrest.treeActs_nil]
      simp
    rcases hc.first with ⟨-, hn⟩ | ⟨e, rest, ht, hh⟩
    · exact .inl (he.trans hn)
    · exact .inr ⟨e, rest, he.trans ht, hh⟩
  | next hpre hc hrest =>
    rename_i before step after
    rcases hc.first with ⟨hf, -⟩ | ⟨e, rest, ht, hh⟩
    · cases hf
    · refine .inr ⟨e, rest ++ treeActs after, ?_, hh⟩
      rw [treeActs_append, treeActs_append]
      rw [hpre.treeActs_nil, ht]
      rfl

/-- When the first tree act of a prepared reading creates a directory, that directory is the parent
of its first TOML copy, irrespective of the creation's success or failure. -/
theorem ReadingPreparation.first_directory {t : List (Event L E)} {dir treeDir path : FilePath}
    {response : Except IO.Error Unit} {rest : List (Event L E)}
    (h : ReadingPreparation t dir treeDir) (hf : treeActs t = ⟨.createDirAll path, response⟩ :: rest) :
    ∃ tree, (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t ∧
      (tree / "lakefile.toml").parent = some path := by
  rcases h with hq | ⟨project, tree, sysroot, text, before, after, rfl, hq, -, ht, -, -, -, hc⟩
  · rw [hq.treeActs_nil] at hf; cases hf
  · have he : treeActs (before ++ after) = treeActs after := by
      rw [treeActs_append]
      rw [hq.treeActs_nil]
      rfl
    rw [he] at hf
    rcases hc.first with hn | ⟨e, tail, he, hh⟩
    · rw [hn] at hf; cases hf
    · have hx := (List.cons.inj (he.symm.trans hf)).1
      subst e
      rcases hh with ⟨parent, r, hp, he⟩ | ⟨-, r, he⟩
      · have hop := congrArg Event.op he
        cases hop
        exact ⟨tree, List.mem_append_left _ ht, hp⟩
      · cases congrArg Event.op he

/-- A reading without any toolchain response can only observe and report. -/
theorem ReadingPreparation.no_sysroot {t : List (Event L E)} {dir tree : FilePath}
    (h : ReadingPreparation t dir tree) (hn : ∀ s, ¬ SysrootIs t s) : Quiet t := by
  rcases h with h | ⟨project, real, sysroot, text, before, after, rfl, -, -, -, -, hs, -⟩
  · exact h
  · exact (hn sysroot (List.mem_append_left _ hs)).elim

/-- With no received toolchain, a full run cannot create a copy directory or write a file. This is a
property of every subject of the record, not an assumption that its responses are consistent. -/
theorem FullRun.no_sysroot_no_copy {t : List (Event L E)} {dir : FilePath}
    {p : Regula.Closed.Profile} {c : UInt32} (h : FullRun t dir p c) (hn : ∀ s, ¬ SysrootIs t s) :
    ∀ e ∈ t, (match e.op with | .createDirAll _ | .writeFile .. => False | _ => True) := by
  have quiet {u : List (Event L E)} (hq : Quiet u) :
      ∀ e ∈ u, (match e.op with | .createDirAll _ | .writeFile .. => False | _ => True) := by
    intro e he
    have hp := hq e he
    obtain ⟨op, response⟩ := e
    cases op <;> first | trivial | exact hp.elim
  have saying {u : List (Event L E)} (hs : ∀ e ∈ u, e.isOnlySaying = true) : Quiet u := by
    intro e he
    have hp := hs e he
    obtain ⟨op, response⟩ := e
    cases op <;> first | trivial | cases hp
  rcases h with ⟨error, rest, rfl, -, -, hs⟩ |
    ⟨tree, tRead, tGate, response, last, rfl, -, hs, o, report, -, -, hstop, hgate, -, -, -, -, -, hp⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · trivial
    · exact quiet (saying hs) e he
  · have hr : ∀ s, ¬ SysrootIs tRead s := by
      intro s h
      exact hn s (by
        simp only [SysrootIs, List.cons_append, List.mem_cons, List.mem_append]
        exact .inr (.inl (.inl h)))
    have hq := hp.no_sysroot hr
    have hg : tGate = [] := by
      by_cases ho : o = .admitted
      · obtain ⟨sysroot, _, _, hsys, -⟩ := hgate ho
        exact (hr sysroot hsys).elim
      · exact (hstop ho).1
    subst tGate
    intro e he
    simp only [List.append_nil, List.cons_append, List.mem_cons, List.mem_append] at he
    rcases he with rfl | (he | rfl | he)
    · trivial
    · exact quiet hq e he
    · trivial
    · exact quiet (saying hs) e he

/-- The reported manufactured refusal: read the requested TOML, create a directory at its destination,
fail the write, remove the tree, and report incomplete. -/
def manufacturedCopyTrace (dir tree : FilePath) (text : String) (error : IO.Error) : List (Event L E) :=
  [⟨.createTempDir, .ok tree⟩, ⟨.realPath dir, .ok dir⟩, ⟨.realPath tree, .ok tree⟩,
   ⟨.readFile (dir / "lakefile.toml"), .ok text⟩, ⟨.createDirAll (tree / "lakefile.toml"), .ok ()⟩,
   ⟨.writeFile (tree / "lakefile.toml") text, .error error⟩, ⟨.removeDirAll tree, .ok ()⟩,
   ⟨.println Regula.Language.Report.incomplete.label, .ok ()⟩]

/-- The reported trace, with no answer about the toolchain, fails the record, for every path, text, error, profile and
exit code. The proof rests on that absent answer. `manufacturedCopyAnswered_fails` excludes the trace with the answer
present, through the copy grammar. -/
theorem manufacturedCopy_fails (dir tree : FilePath) (text : String) (error : IO.Error)
    (p : Regula.Closed.Profile) (c : UInt32) :
    ¬ FullRun (manufacturedCopyTrace (L := L) (E := E) dir tree text error) dir p c := by
  intro h
  have hn : ∀ s, ¬ SysrootIs (manufacturedCopyTrace (L := L) (E := E) dir tree text error) s := by
    intro s hs
    simp only [SysrootIs, manufacturedCopyTrace, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h | h | h | h | h | h | h <;> cases congrArg Event.op h
  exact h.no_sysroot_no_copy hn ⟨.createDirAll (tree / "lakefile.toml"), .ok ()⟩
    (by simp [manufacturedCopyTrace])

/-- What the search for the last separator of a path returns lies strictly before where it starts. -/
theorem searcher_lt {p : Char → Bool} {s : String.Slice} (n : Nat) (c : s.Pos) (hn : c.offset.byteIdx < n) {r : s.Pos}
    (h : ((⟨⟨c⟩⟩ : Std.Iter (α := DefaultBackwardSearcher p s) (SearchStep s)).findSome?
      (fun | .matched startPos _ => some startPos | .rejected .. => none)) = some r) : r < c := by
  induction n generalizing c with
  | zero => omega
  | succ n ih =>
    rw [Std.Iter.findSome?_eq_match_step] at h
    have hp := (⟨⟨c⟩⟩ : Std.Iter (α := DefaultBackwardSearcher p s) (SearchStep s)).step.property
    generalize (⟨⟨c⟩⟩ : Std.Iter (α := DefaultBackwardSearcher p s) (SearchStep s)).step.val = st at h hp
    cases st with
    | done => cases h
    | skip it' => exact hp.elim
    | yield it' out =>
      cases out with
      | matched a b =>
        obtain ⟨hc, pos, h₀, ha, -, -⟩ := hp
        simp only [Option.some.injEq] at h
        subst h ha
        have := StrictBackwardPattern.ne_endPos _ _ h₀
        exact Std.lt_of_lt_of_le
          (String.Slice.Pos.ofSliceTo_lt_ofSliceTo_iff.2 ((String.Slice.Pos.lt_endPos_iff _).2 this))
          String.Slice.Pos.ofSliceTo_le
      | rejected a b =>
        obtain ⟨hc, -, -, -, hit⟩ := hp
        obtain ⟨⟨c'⟩⟩ := it'
        change c' = c.prev hc at hit
        subst hit
        have hlt : c.prev hc < c := String.Slice.Pos.prev_lt
        have hlt' := hlt
        rw [String.Slice.Pos.lt_iff, String.Pos.Raw.lt_iff] at hlt'
        exact Std.lt_trans (ih (c.prev hc) (by omega) h) hlt

/-- The last separator of a text is a position before its end. -/
theorem lastSep_ne_end (s : String) (x : s.Pos)
    (h : s.revFind? FilePath.pathSeparators.contains = some x) : x ≠ s.endPos := by
  unfold String.revFind? at h
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h
  have hlt := searcher_lt _ _ (Nat.lt_succ_self _) hy
  intro he
  have : y = s.toSlice.endPos := by
    apply String.Slice.Pos.ext
    have := congrArg String.Pos.offset he
    simpa using this
  subst this
  exact Std.lt_irrefl hlt

/-- A text cut at a position before its end is not that text. -/
theorem copy_sliceTo_ne (s : String) (x : s.Pos) (hx : x ≠ s.endPos) : (s.sliceTo x).copy ≠ s := by
  intro h
  apply hx
  have := congrArg String.utf8ByteSize h
  rw [String.Slice.utf8ByteSize_copy, String.utf8ByteSize_sliceTo] at this
  apply String.Pos.ext
  apply String.Pos.Raw.ext
  simpa using this

/-- No path is its own parent, on any platform: the proof reads `FilePath.parent` and takes both answers of
`isAbsolute`, so it needs no value of the `opaque` `System.Platform.isWindows`. -/
theorem parent_ne_self (p : FilePath) : p.parent ≠ some p := by
  have slice : ∀ x : p.toString.Pos, x ≠ p.toString.endPos →
      some (FilePath.mk (p.toString.sliceTo x).copy) ≠ some p := by
    intro x hx he
    exact copy_sliceTo_ne _ x hx (congrArg FilePath.toString (Option.some.inj he))
  have ext : ∀ o : Option p.toString.Pos, (∀ x, o = some x → x ≠ p.toString.endPos) →
      (FilePath.mk <$> String.Slice.copy <$> String.sliceTo _ <$> o) ≠ some p := by
    intro o ho
    cases o with
    | none => simp
    | some x => exact slice x (ho x rfl)
  unfold FilePath.parent
  simp only
  split
  · split
    · simp
    · split
      · rename_i hend _
        exact slice _ (fun e => hend (String.Pos.isAtEnd_iff.2 e))
      · exact ext _ fun x hx => lastSep_ne_end _ x hx
  · exact ext _ fun x hx => lastSep_ne_end _ x hx

/-- The reported manufactured refusal with the toolchain's answer present, and every other act as reported. -/
def manufacturedCopyAnsweredTrace (dir tree : FilePath) (sysroot text : String) (error : IO.Error) :
    List (Event L E) :=
  [⟨.createTempDir, .ok tree⟩, ⟨.realPath dir, .ok dir⟩, ⟨.realPath tree, .ok tree⟩,
   ⟨.getEnv "LEAN_SYSROOT", some sysroot⟩,
   ⟨.readFile (dir / "lakefile.toml"), .ok text⟩, ⟨.createDirAll (tree / "lakefile.toml"), .ok ()⟩,
   ⟨.writeFile (tree / "lakefile.toml") text, .error error⟩, ⟨.removeDirAll tree, .ok ()⟩,
   ⟨.println Regula.Language.Report.incomplete.label, .ok ()⟩]

/-- The attack itself fails the record, for every path, text, toolchain, error, profile and exit code, because
of the copy grammar: the trace's first tree act makes a directory at the destination, `first_directory` says
that directory is the parent of the destination, and `parent_ne_self` says it is not. No response is absent. -/
theorem manufacturedCopyAnswered_fails (dir tree : FilePath) (sysroot text : String) (error : IO.Error)
    (p : Regula.Closed.Profile) (c : UInt32) :
    ¬ FullRun (manufacturedCopyAnsweredTrace (L := L) (E := E) dir tree sysroot text error) dir p c := by
  intro h
  rcases h with ⟨e, rest, heq, -⟩ |
    ⟨tree', tRead, tGate, response, last, heq, -, -, o, report, -, -, hstop, hgate, -, -, -, -, -, hp⟩
  · have := (List.cons.inj heq).1
    cases this
  · obtain rfl : tree' = tree := by
      have := (List.cons.inj heq).1
      cases this
      rfl
    have hg : tGate = [] := by
      by_cases ho : o = .admitted
      · exfalso
        obtain ⟨sysroot', tBuild, tRules, -, rfl, hb⟩ := hgate ho
        obtain ⟨program, lakeLib, first, rest, -, rfl, -⟩ := hb.1
        have hm : (⟨.lakeInstall sysroot', (program, lakeLib)⟩ : Event L E) ∈
            manufacturedCopyAnsweredTrace (L := L) (E := E) dir tree' sysroot text error := by
          rw [heq]; simp
        simp only [manufacturedCopyAnsweredTrace, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with h | h | h | h | h | h | h | h | h <;> cases congrArg Event.op h
      · exact (hstop ho).1
    subst tGate
    have hreal : ∀ t', (⟨.realPath tree', .ok t'⟩ : Event L E) ∈ tRead → t' = tree' := by
      intro t' hm
      have hm' : (⟨.realPath tree', .ok t'⟩ : Event L E) ∈
          manufacturedCopyAnsweredTrace (L := L) (E := E) dir tree' sysroot text error := by
        rw [heq]; simp [hm]
      simp only [manufacturedCopyAnsweredTrace, List.mem_cons, List.not_mem_nil, or_false] at hm'
      rcases hm' with h | h | h | h | h | h | h | h | h
      · cases congrArg Event.op h
      · cases h; rfl
      · cases h; rfl
      all_goals cases congrArg Event.op h
    have hacts := congrArg treeActs (List.cons.inj heq).2
    change [⟨.createDirAll (tree' / "lakefile.toml"), .ok ()⟩, ⟨.writeFile (tree' / "lakefile.toml") text, .error error⟩,
      ⟨.removeDirAll tree', .ok ()⟩] = treeActs (tRead ++ [] ++ ⟨.removeDirAll tree', response⟩ :: last) at hacts
    rw [List.append_nil, treeActs_append] at hacts
    cases hta : treeActs tRead with
    | nil =>
      rw [hta] at hacts
      cases congrArg Event.op (List.cons.inj hacts).1
    | cons e rest =>
      rw [hta] at hacts
      obtain rfl := (List.cons.inj hacts).1
      obtain ⟨t', hm, hparent⟩ := hp.first_directory hta
      obtain rfl := hreal t' hm
      exact parent_ne_self _ hparent

end RegulaSpecification.Effects
