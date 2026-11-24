module

public import RegulaSpecification.Proofs.Owed
public import RegulaSpecification.Proofs.Written
public import RegulaSpecification.Proofs.ReaderParts
import all Regula.Reader

@[expose] public section

namespace RegulaSpecification.Effects

open Lean (Name Syntax Import MessageLog)
open Lean.Parser (InputContext ModuleParserState mkInputContext)
open System (FilePath)
open Regula.Effect
open Regula.Language
open Regula.Reader
open RegulaSpecification.Language

variable {L E : Type}

theorem readExact_spec {project path : FilePath} {t : List (Event L E)} {b : Except String String}
    (h : Runs (readExact project path : Attempt L E String).run t b) :
    (∀ text, b = .ok text → ∃ real, t = [⟨.realPath path, .ok real⟩, ⟨.readFile path, .ok text⟩] ∧
      Regula.Load.exactBelow project path real = true) ∧
    ((∃ e, b = .error e) → (∃ e ∈ t, Event.failed e ∧ (e.op = .realPath path ∨ e.op = .readFile path)) ∨
      ∃ real, t = [⟨.realPath path, .ok real⟩] ∧ Regula.Load.exactBelow project path real = false) ∧
    Quiet t := by
  rw [readExact] at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r', h₃, rfl⟩ := runs_attempt_iff.mp h₁
  obtain rfl := runs_call_iff.mp h₃
  cases r' with
  | error e =>
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨by simp, fun _ => .inl ⟨⟨.realPath path, .error e⟩, by simp, ⟨e, rfl⟩, .inl rfl⟩, by quiet_events⟩
  | ok real =>
    dsimp only [Except.mapError] at h₂
    split at h₂
    · rename_i hb
      obtain ⟨r'', h₄, rfl⟩ := runs_attempt_iff.mp h₂
      obtain rfl := runs_call_iff.mp h₄
      cases r'' with
      | ok text => exact ⟨fun _ he => (by cases he; exact ⟨real, rfl, hb⟩), fun ⟨_, he⟩ => (by cases he), by quiet_events⟩
      | error e => exact ⟨fun _ he => (by cases he), fun _ =>
          .inl ⟨⟨.readFile path, .error e⟩, by simp, ⟨e, rfl⟩, .inr rfl⟩, by quiet_events⟩
    · rename_i hb
      obtain ⟨rfl, rfl⟩ := runs_attempt_throw_iff.mp h₂
      exact ⟨by simp, fun _ => .inr ⟨real, rfl, by simpa using hb⟩, by quiet_events⟩

theorem inTree_iff (tree path : FilePath) :
    inTree tree path = true ↔ ∃ rel, TreeRelative (parts tree) (parts path) rel := by
  simp only [inTree, Option.isSome_iff_exists, treeRelative_iff]

theorem closedSourceDir_iff (tree dir : FilePath) :
    closedSourceDir tree dir = true ↔ ∃ rel, TreeRelative (parts tree) (parts dir) rel ∧ ∀ c ∈ rel, ClosedComponent c := by
  simp only [closedSourceDir]
  cases hr : treeRelative (parts tree) (parts dir) with
  | none =>
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨rel, hrel, -⟩
    rw [(treeRelative_iff _ _ _).mpr hrel] at hr; cases hr
  | some rel =>
    have hrel := (treeRelative_iff _ _ _).mp hr
    simp only [List.all_eq_true, closedComponent_iff]
    exact ⟨fun hc => ⟨rel, hrel, hc⟩, fun ⟨rel', hrel', hc⟩ => by
      have : rel' = rel := Option.some.inj (((treeRelative_iff _ _ _).mpr hrel').symm.trans hr)
      exact this ▸ hc⟩

theorem writeInTree_spec {tree path : FilePath} {text : String} {t : List (Event L E)}
    {b : Except String Unit} (h : Runs (writeInTree tree path text : Attempt L E Unit).run t b) :
    CopyStep tree path text t b.isOk := by
  rw [writeInTree] at h
  split at h
  · rename_i hin
    have hpath := (inTree_iff tree path).mp hin
    obtain ⟨a, b', result, rfl, ha, hb⟩ := runs_attempt_bind_iff.mp h
    rw [makeParent] at ha
    cases hp : path.parent with
    | none =>
      simp only [hp] at ha
      obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp ha
      obtain ⟨r, hc, rfl⟩ := runs_attempt_iff.mp hb
      obtain rfl := runs_call_iff.mp hc
      cases r <;> exact .noParent hpath hp
    | some parent =>
      simp only [hp] at ha
      split at ha
      · rename_i hparent
        obtain ⟨r, hc, rfl⟩ := runs_attempt_iff.mp ha
        obtain rfl := runs_call_iff.mp hc
        cases r with
        | error error =>
          obtain ⟨rfl, rfl⟩ := hb
          simpa [Except.isOk, Except.toBool] using (CopyStep.parentFailed (L := L) (E := E) (text := text) (error := error)
            hpath hp ((inTree_iff tree parent).mp hparent))
        | ok u =>
          obtain ⟨r, hc, rfl⟩ := runs_attempt_iff.mp hb
          obtain rfl := runs_call_iff.mp hc
          cases u; cases r <;> exact .parentWritten hpath hp ((inTree_iff tree parent).mp hparent)
      · rename_i hparent
        obtain ⟨rfl, rfl⟩ := runs_attempt_throw_iff.mp ha
        obtain ⟨rfl, rfl⟩ := hb
        exact .outside (.inr ⟨parent, hp, fun rel hr => hparent ((inTree_iff tree parent).mpr ⟨rel, hr⟩)⟩)
  · rename_i hout
    obtain ⟨rfl, rfl⟩ := runs_attempt_throw_iff.mp h
    exact .outside (.inl fun rel hr => hout ((inTree_iff tree path).mpr ⟨rel, hr⟩))

def SourceRead (T : List (Event L E)) (project tree path : FilePath) (s : Source) : Prop :=
  ∃ rel real text,
    TreeRelative (parts tree) (parts path) rel ∧ ¬ OutsideTree tree path ∧
    Regula.Load.exactBelow project (joinParts project rel) real = true ∧
    s.path = path ∧ s.text = text ∧
    s.input = mkInputContext text (inputNameOf path) ∧
    ([⟨.realPath (joinParts project rel), .ok real⟩, ⟨.readFile (joinParts project rel), .ok text⟩,
      ⟨.parseHeader s.input, .ok (s.header, s.state, s.messages, s.imports)⟩] :
        List (Event L E)).Sublist T

theorem SourceRead.mono {T T' : List (Event L E)} {project tree path : FilePath} {s : Source}
    (h : SourceRead T project tree path s) (hs : T.Sublist T') : SourceRead T' project tree path s := by
  obtain ⟨rel, real, text, h0, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨rel, real, text, h0, h1, h2, h3, h4, h5, h6.trans hs⟩

def SourceOp (T : List (Event L E)) (project tree path : FilePath) (o : Op L E) : Prop :=
  (∃ rel, TreeRelative (parts tree) (parts path) rel ∧
    (o = .realPath (under project rel) ∨ o = .readFile (under project rel))) ∨
  ∃ text, SourceText T project tree path text ∧ o = .parseHeader (mkInputContext text (inputNameOf path))

def SourceBad (t : List (Event L E)) (project tree path : FilePath) : Prop :=
  OutsideTree tree path ∨ (∃ e ∈ t, Event.failed e ∧ SourceOp t project tree path e.op) ∨
    ∃ rel real, TreeRelative (parts tree) (parts path) rel ∧
      (⟨.realPath (under project rel), .ok real⟩ : Event L E) ∈ t ∧
      Regula.Load.exactBelow project (under project rel) real = false

theorem not_outside_of {tree path : FilePath} {rel : List String} (hrel : TreeRelative (parts tree) (parts path) rel)
    (hp : parentInTree tree path = true) : ¬ OutsideTree tree path := by
  rintro (hx | ⟨d, hd, hx⟩)
  · exact hx rel hrel
  · rw [parentInTree, hd] at hp; obtain ⟨rel', hrel'⟩ := (inTree_iff tree d).mp hp; exact hx rel' hrel'

theorem readSource_spec {project tree path : FilePath} {t : List (Event L E)} {b : Except String Source}
    (h : Runs (readSource project tree path : Attempt L E Source).run t b) :
    (∀ s, b = .ok s → SourceRead t project tree path s ∧ Clean t) ∧
    ((∃ e, b = .error e) → SourceBad t project tree path) ∧
    Quiet t := by
  rw [readSource] at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  rw [readForTree] at h₁
  cases htr : treeRelative (Regula.Load.parts tree) (Regula.Load.parts path) with
  | none =>
    simp only [htr] at h₁
    obtain ⟨rfl, rfl⟩ := runs_attempt_throw_iff.mp h₁; obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨by simp, fun _ => .inl (.inl fun rel hr => by rw [(treeRelative_iff _ _ _).mpr hr] at htr; cases htr), quiet_nil⟩
  | some rel =>
    simp only [htr] at h₁
    have hrel := (treeRelative_iff _ _ _).mp htr
    split at h₁
    · rename_i hpar
      obtain ⟨e1, e2, e3⟩ := readExact_spec h₁
      cases r with
      | error why =>
        obtain ⟨rfl, rfl⟩ := h₂
        refine ⟨by simp, fun _ => ?_, by simpa using e3⟩
        rcases e2 ⟨why, rfl⟩ with ⟨e, he, hf, hop⟩ | ⟨real, rfl, hb⟩
        · exact .inr (.inl ⟨e, by simpa using he, hf, .inl ⟨rel, hrel, hop⟩⟩)
        · exact .inr (.inr ⟨rel, real, hrel, by simp [under, joinParts], hb⟩)
      | ok text =>
        obtain ⟨real, rfl, hexact⟩ := e1 text rfl
        obtain ⟨t₇, t₈, r₇, rfl, h₇, h₈⟩ := runs_attempt_bind_iff.mp h₂
        obtain ⟨r₉, h₉, rfl⟩ := runs_attempt_iff.mp h₇
        obtain rfl := runs_call_iff.mp h₉
        cases r₉ with
        | error e =>
          obtain ⟨rfl, rfl⟩ := h₈
          exact ⟨by simp, fun _ => .inr (.inl
            ⟨⟨.parseHeader (mkInputContext text (inputNameOf path)), .error e⟩, by simp, ⟨e, rfl⟩,
              .inr ⟨text, ⟨rel, hrel, by simp [under, joinParts]⟩, rfl⟩⟩), by quiet_events⟩
        | ok parsed =>
          obtain ⟨header, state, messages, imports⟩ := parsed
          obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₈
          exact ⟨fun _ he => by cases he; exact ⟨⟨rel, real, text, hrel, not_outside_of hrel hpar, hexact, rfl, rfl, rfl, by simp⟩, by clean_events⟩,
            by simp, by quiet_events⟩
    · rename_i hpar
      obtain ⟨rfl, rfl⟩ := runs_attempt_throw_iff.mp h₁; obtain ⟨rfl, rfl⟩ := h₂
      refine ⟨by simp, fun _ => .inl (.inr ?_), quiet_nil⟩
      cases hd : path.parent with
      | none => simp [parentInTree, hd] at hpar
      | some d => exact ⟨d, rfl, fun rel' hr => by simp [parentInTree, hd, (inTree_iff tree d).mpr ⟨rel', hr⟩] at hpar⟩

theorem toolchainOLean_spec {path : List FilePath} {m : Name} {t : List (Event L E)} {b : Except String Unit}
    (h : Runs (toolchainOLean path m : Attempt L E Unit).run t b) :
    (b = .ok () → ∃ olean, t = [⟨.findOLean path m, .ok olean⟩]) ∧
    ((∃ e, b = .error e) → ∃ x, t = [⟨.findOLean path m, .error x⟩]) := by
  rw [toolchainOLean] at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r', h₃, rfl⟩ := runs_attempt_iff.mp h₁; obtain rfl := runs_call_iff.mp h₃
  cases r' with
  | error e => obtain ⟨rfl, rfl⟩ := h₂; exact ⟨by simp, fun _ => ⟨e, rfl⟩⟩
  | ok olean => obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂; exact ⟨fun _ => ⟨olean, rfl⟩, by simp⟩

def Observes (root : Root L) (t : List (Event L E)) : Prop :=
  ∀ e ∈ t, QuietOp e.op ∨ ParserSearchOp root e.op

theorem Observes.append {root : Root L} {a b : List (Event L E)} (ha : Observes root a) (hb : Observes root b) :
    Observes root (a ++ b) := fun e he => by
  rcases List.mem_append.mp he with he | he
  · exact ha e he
  · exact hb e he

theorem Quiet.observes {t : List (Event L E)} (h : Quiet t) (root : Root L) : Observes root t :=
  fun e he => .inl (h e he)

theorem Observes.noActs {root : Root L} {t : List (Event L E)} (h : Observes root t) : ∀ e ∈ t, e.acted? = none := by
  intro ⟨o, r⟩ he; have hq := h _ he
  cases o <;> first | rfl | (rcases hq with hq | hq <;> exact hq.elim)

def Due (roots : List Name) (w : Walk) (n : Name) : Prop :=
  n ∈ roots ∨ ∃ x ∈ w.sources, ∃ i ∈ x.2.imports, i.module = n

structure WalkInv (T : List (Event L E)) (dir treeDir project tree : FilePath) (root : Root L)
    (modules : List (Name × FilePath)) (roots todo : List Name)
    (w : Walk) : Prop where
  sources : ∀ x ∈ w.sources, ∃ path, fileOf root modules x.1 = some path ∧
    SourceRead T project tree path x.2 ∧ x.1 ∈ w.reached
  held : ∀ n ∈ w.toolchain, fileOf root modules n = none ∧ HeldByToolchain T root n ∧
    closedModuleName n = true ∧ n.getRoot ≠ `Mathlib ∧ Named T project tree root modules n
  nodup : (w.sources.map (·.1)).Nodup
  reached : ∀ m ∈ w.reached, (∃ s, (m, s) ∈ w.sources) ∨ m.getRoot = `Mathlib ∨ w.unread ≠ []
  closed : ∀ m ∈ w.reached, closedModuleName m = true ∨ w.unread ≠ []
  named : ∀ m ∈ w.reached, Named T project tree root modules m
  todoNamed : ∀ m ∈ todo, Named T project tree root modules m
  unread : w.unread ≠ [] → Scene T dir treeDir project tree root modules → Reason T dir treeDir .incomplete
  visited : w.unread = [] → ∀ n, Due roots w n → n ∈ todo ∨ n ∈ w.reached ∨ n ∈ w.toolchain

theorem fileOf_mem {root : Root L} {modules : List (Name × FilePath)} {m : Name} {path : FilePath}
    (h : fileOf root modules m = some path) : (m, path) ∈ modules ∨ root.resolve m = some path := by
  rw [fileOf] at h
  cases hl : modules.lookup m with
  | some file => simp only [hl, Option.some.injEq] at h; exact .inl (h ▸ mem_of_lookup hl)
  | none => simp only [hl] at h; exact .inr h

section Invariant

variable {T : List (Event L E)} {dir treeDir project tree : FilePath} {root : Root L}
  {modules : List (Name × FilePath)} {roots : List Name}

theorem headerOf_read {m : Name} {s : Source} {path : FilePath} (hf : fileOf root modules m = some path)
    (hs : SourceRead T project tree path s) : HeaderOf T project tree root modules m s.imports := by
  obtain ⟨rel, real, text, hrel, -, -, -, -, hin, hsub⟩ := hs
  exact ⟨path, text, s.header, s.state, s.messages, fileOf_mem hf,
    ⟨rel, hrel, hsub.subset (by simp [under, joinParts])⟩, by rw [← hin]; exact hsub.subset (by simp)⟩

theorem visited_step {m n : Name} {rest todo : List Name} {r r' c c' : List Name}
    (hm : m ∈ r' ∨ m ∈ c') (hr : ∀ x ∈ r, x ∈ r') (hc : ∀ x ∈ c, x ∈ c') (ht : ∀ x ∈ rest, x ∈ todo)
    (h : n ∈ m :: rest ∨ n ∈ r ∨ n ∈ c) : n ∈ todo ∨ n ∈ r' ∨ n ∈ c' := by
  grind

theorem WalkInv.pop {m : Name} {rest : List Name} {w : Walk}
    (h : WalkInv T dir treeDir project tree root modules roots (m :: rest) w)
    (hm : m ∈ w.reached ∨ m ∈ w.toolchain) :
    WalkInv T dir treeDir project tree root modules roots rest w :=
  { h with
    todoNamed := fun n hn => h.todoNamed n (List.mem_cons_of_mem _ hn)
    visited := fun hu n hn => visited_step hm (fun _ h => h) (fun _ h => h) (fun _ h => h) (h.visited hu n hn) }

theorem WalkInv.leave {m : Name} {rest : List Name} {w : Walk} (why : String)
    (h : WalkInv T dir treeDir project tree root modules roots (m :: rest) w)
    (hr : Scene T dir treeDir project tree root modules → Reason T dir treeDir .incomplete) :
    WalkInv T dir treeDir project tree root modules roots rest (w.leaveUnread m why) where
  sources := fun x hx => let ⟨p, h1, h2, h3⟩ := h.sources x hx; ⟨p, h1, h2, List.mem_cons_of_mem _ h3⟩
  held := h.held
  nodup := h.nodup
  reached := fun _ _ => .inr (.inr (by simp [Walk.leaveUnread]))
  closed := fun _ _ => .inr (by simp [Walk.leaveUnread])
  named := fun n hn => by rcases List.mem_cons.mp hn with rfl | hn; exact h.todoNamed _ (by simp); exact h.named n hn
  todoNamed := fun n hn => h.todoNamed n (List.mem_cons_of_mem _ hn)
  unread := fun _ => hr
  visited := fun hu => by simp [Walk.leaveUnread] at hu

theorem WalkInv.stop {m : Name} {rest : List Name} {w : Walk} (why : String)
    (h : WalkInv T dir treeDir project tree root modules roots (m :: rest) w)
    (hr : Scene T dir treeDir project tree root modules → Reason T dir treeDir .incomplete) :
    WalkInv T dir treeDir project tree root modules roots [] (w.leaveUnread m why) :=
  have hl := h.leave why hr
  { hl with todoNamed := fun _ hn => (by cases hn), visited := fun hu => by simp [Walk.leaveUnread] at hu }

theorem WalkInv.mathlib {m : Name} {rest : List Name} {w : Walk}
    (h : WalkInv T dir treeDir project tree root modules roots (m :: rest) w)
    (hroot : m.getRoot = `Mathlib) (hc : closedModuleName m = true) :
    WalkInv T dir treeDir project tree root modules roots rest { w with reached := m :: w.reached } where
  sources := fun x hx => let ⟨p, h1, h2, h3⟩ := h.sources x hx; ⟨p, h1, h2, List.mem_cons_of_mem _ h3⟩
  held := h.held
  nodup := h.nodup
  reached := fun n hn => by rcases List.mem_cons.mp hn with rfl | hn; exact .inr (.inl hroot); exact h.reached n hn
  closed := fun n hn => by rcases List.mem_cons.mp hn with rfl | hn; exact .inl hc; exact h.closed n hn
  named := fun n hn => by rcases List.mem_cons.mp hn with rfl | hn; exact h.todoNamed _ (by simp); exact h.named n hn
  todoNamed := fun n hn => h.todoNamed n (List.mem_cons_of_mem _ hn)
  unread := h.unread
  visited := fun hu n hn => visited_step (.inl (by simp)) (fun _ h => List.mem_cons_of_mem _ h)
    (fun _ h => h) (fun _ h => h) (h.visited hu n hn)

theorem WalkInv.read {m : Name} {rest : List Name} {w : Walk} {s : Source} {path : FilePath}
    (h : WalkInv T dir treeDir project tree root modules roots (m :: rest) w)
    (hm : m ∉ w.reached) (hf : fileOf root modules m = some path) (hs : SourceRead T project tree path s)
    (hc : closedModuleName m = true) :
    WalkInv T dir treeDir project tree root modules roots (s.imports.toList.map (·.module) ++ rest)
      { w with reached := m :: w.reached, sources := (m, s) :: w.sources } where
  sources := fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨path, hf, hs, by simp⟩
    · let ⟨p, h1, h2, h3⟩ := h.sources x hx; exact ⟨p, h1, h2, List.mem_cons_of_mem _ h3⟩
  held := h.held
  nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, h.nodup⟩
    obtain ⟨x, hx, he⟩ := List.mem_map.mp hmem
    obtain ⟨_, _, _, h3⟩ := h.sources x hx
    exact hm (he ▸ h3)
  reached := fun n hn => by
    rcases List.mem_cons.mp hn with rfl | hn
    · exact .inl ⟨s, by simp⟩
    · rcases h.reached n hn with ⟨s', hs'⟩ | h' | h'
      · exact .inl ⟨s', List.mem_cons_of_mem _ hs'⟩
      · exact .inr (.inl h')
      · exact .inr (.inr h')
  closed := fun n hn => by rcases List.mem_cons.mp hn with rfl | hn; exact .inl hc; exact h.closed n hn
  named := fun n hn => by rcases List.mem_cons.mp hn with rfl | hn; exact h.todoNamed _ (by simp); exact h.named n hn
  todoNamed := fun n hn => by
    rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hn
      exact .imported (h.todoNamed _ (by simp)) (headerOf_read hf hs) (Array.mem_toList_iff.mp hi)
    · exact h.todoNamed n (List.mem_cons_of_mem _ hn)
  unread := h.unread
  visited := fun hu n hn => by
    have step := visited_step (m := m) (n := n) (rest := rest) (todo := s.imports.toList.map (·.module) ++ rest)
      (r := w.reached) (r' := m :: w.reached) (c := w.toolchain) (c' := w.toolchain) (.inl (by simp))
      (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h) (fun _ h => List.mem_append_right _ h)
    rcases hn with hn | ⟨x, hx, i, hi, rfl⟩
    · exact step (h.visited hu n (.inl hn))
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact .inl (List.mem_append_left _ (List.mem_map.mpr ⟨i, Array.mem_toList_iff.mpr hi, rfl⟩))
      · exact step (h.visited hu _ (.inr ⟨x, hx, i, hi, rfl⟩))

theorem WalkInv.toolchain {m : Name} {rest : List Name} {w : Walk}
    (h : WalkInv T dir treeDir project tree root modules roots (m :: rest) w)
    (hf : fileOf root modules m = none) (hh : HeldByToolchain T root m) (hc : closedModuleName m = true)
    (hr : m.getRoot ≠ `Mathlib) :
    WalkInv T dir treeDir project tree root modules roots rest
      { w with toolchain := m :: w.toolchain } :=
  { h with
    held := fun n hn => by
      rcases List.mem_cons.mp hn with rfl | hn
      · exact ⟨hf, hh, hc, hr, h.todoNamed _ (by simp)⟩
      · exact h.held n hn
    todoNamed := fun n hn => h.todoNamed n (List.mem_cons_of_mem _ hn)
    visited := fun hu n hn => visited_step (.inr (by simp)) (fun _ h => h)
      (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h) (h.visited hu n hn) }

theorem reason_of_sourceBad {m : Name} {path : FilePath}
    {t : List (Event L E)} (hn : Named T project tree root modules m) (hf : fileOf root modules m = some path)
    (ht : t.Sublist T) (h : SourceBad t project tree path) (scene : Scene T dir treeDir project tree root modules) :
    Reason T dir treeDir .incomplete := by
  have hfm := fileOf_mem hf
  rcases h with h | ⟨e, he, hb, hop⟩ | ⟨rel, real, hr, he, hb⟩
  · exact .moduleNotInTree scene hn hfm h
  · refine .failed (ht.subset he) ?_ hb
    rcases hop with ⟨rel, hrel, hop | hop⟩ | ⟨text, hst, hop⟩ <;> rw [hop]
    · exact .sourceReal scene hn hfm hrel
    · exact .sourceRead scene hn hfm hrel
    · exact .sourceHeader scene hn hfm (SourceText.mono ht hst)
  · exact .moduleNotExact scene hn hfm hr (ht.subset he) ((exactBelow_eq_false_iff _ _ _).mp hb)

abbrev sourceImports (sources : List (Name × Source)) : Nat :=
  (sources.map (·.2.imports.size)).sum

theorem walk_spec (fuel : Nat) (todo : List Name)
    (w : Walk) (t : List (Event L E)) (w' : Walk)
    (h : Runs (walk project tree root modules fuel todo w) t w')
    (hT : t.Sublist T)
    (hroots : roots.length = modules.length)
    (hb : fuel + roots.length + sourceImports w.sources = 1000000 + todo.length)
    (hi : WalkInv T dir treeDir project tree root modules roots todo w) :
    WalkInv T dir treeDir project tree root modules roots [] w' ∧ Observes root t ∧
      (w'.unread = [] → w.unread = [] ∧ Clean t ∧ modules.length + sourceImports w'.sources ≤ 1000000) := by
  induction fuel generalizing todo w t with
  | zero =>
    cases todo with
    | nil =>
      rw [walk] at h; obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h; simp only [List.length_nil] at hb
      exact ⟨hi, quiet_nil.observes _, fun hu => ⟨hu, clean_nil, by omega⟩⟩
    | cons m rest =>
      rw [walk] at h; obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h; simp only [List.length_cons] at hb
      have hms : ((w.sources.map fun x => (x.1, x.2.imports)).map (·.1)).Nodup := by
        simpa [Function.comp_def] using hi.nodup
      have hall : ∀ x ∈ w.sources.map (fun x => (x.1, x.2.imports)),
          Named T project tree root modules x.1 ∧ HeaderOf T project tree root modules x.1 x.2 := by
        rintro _ hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        obtain ⟨p, h1, h2, h3⟩ := hi.sources y hy; exact ⟨hi.named _ h3, headerOf_read h1 h2⟩
      have hsum : ((w.sources.map fun x => (x.1, x.2.imports)).map (·.2.size)).sum = sourceImports w.sources := by
        simp [sourceImports, Function.comp_def]
      exact ⟨hi.stop _ fun scene => .tooMany scene hms hall (by omega), quiet_nil.observes _,
        fun hu => by simp [Walk.leaveUnread] at hu⟩
  | succ fuel ih =>
    cases todo with
    | nil =>
      rw [walk] at h; obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h; simp only [List.length_nil] at hb
      exact ⟨hi, quiet_nil.observes _, fun hu => ⟨hu, clean_nil, by omega⟩⟩
    | cons m rest =>
      simp only [List.length_cons] at hb; rw [walk] at h
      split at h
      · rename_i hseen; exact ih rest w t h hT (by omega) (hi.pop (by simpa using hseen))
      · rename_i hseen
        have hnotReached : m ∉ w.reached := fun hm => hseen (by simp [hm])
        have hnamed := hi.todoNamed m (by simp)
        split at h
        · rename_i hclosed
          have hname : closedModuleName m = false := by simpa using hclosed
          obtain ⟨g1, g2, g3⟩ := ih rest _ t h hT (by simpa [Walk.leaveUnread] using (by omega))
            (hi.leave _ fun scene => .moduleName scene hnamed
              (fun hc => by simp [(closedModuleName_iff m).mpr hc] at hname))
          exact ⟨g1, g2, fun hu => by simpa [Walk.leaveUnread] using (g3 hu).1⟩
        · rename_i hclosed
          have hname : closedModuleName m = true := by simpa using hclosed
          split at h
          · rename_i hroot
            exact ih rest { w with reached := m :: w.reached } t h hT (by simpa using (by omega))
              (hi.mathlib (by simpa using hroot) hname)
          · rename_i hroot
            split at h
            · rename_i path hfile
              obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
              obtain ⟨s1, s2, s3⟩ := readSource_spec h₁
              have hT₁ := (List.sublist_append_left t₁ t₂).trans hT
              have hT' := (List.sublist_append_right t₁ t₂).trans hT
              cases r with
              | ok s =>
                obtain ⟨hread, hclean⟩ := s1 s rfl
                obtain ⟨hinv, hact, hcount⟩ := ih _ _ t₂ h₂ hT'
                  (by simp only [List.length_append, List.length_map, Array.length_toList, sourceImports, List.map_cons,
                        List.sum_cons] at hb ⊢; omega)
                  (hi.read hnotReached hfile (hread.mono hT₁) hname)
                exact ⟨hinv, (s3.observes _).append hact, fun hu =>
                  have := hcount hu; ⟨this.1, hclean.append this.2.1, this.2.2⟩⟩
              | error e =>
                obtain ⟨hinv, hact, hcount⟩ := ih rest _ t₂ h₂ hT'
                  (by simpa [Walk.leaveUnread] using (by omega))
                  (hi.leave _ (reason_of_sourceBad hnamed hfile hT₁ (s2 ⟨e, rfl⟩)))
                exact ⟨hinv, (s3.observes _).append hact, fun hu => by simpa [Walk.leaveUnread] using (hcount hu).1⟩
            · rename_i hfile
              obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
              obtain ⟨o1, o2⟩ := toolchainOLean_spec h₁
              have hT₁ := (List.sublist_append_left t₁ t₂).trans hT
              have hT' := (List.sublist_append_right t₁ t₂).trans hT
              have hnone : modules.lookup m = none ∧ root.resolve m = none := by
                rw [fileOf] at hfile; split at hfile
                · cases hfile
                · rename_i hl; exact ⟨hl, hfile⟩
              have hobs {r'} : Observes root ([⟨.findOLean root.toolchain m, r'⟩] : List (Event L E)) := fun x hx => by
                rw [List.mem_singleton.mp hx]; exact .inr rfl
              cases r with
              | ok _ =>
                obtain ⟨olean, rfl⟩ := o1 rfl
                obtain ⟨hinv, hact, hcount⟩ := ih rest _ t₂ h₂ hT' (by simpa using (by omega))
                  (hi.toolchain hfile ⟨olean, hT₁.subset (by simp)⟩ hname (by simpa using hroot))
                exact ⟨hinv, hobs.append hact, fun hu =>
                  have := hcount hu; ⟨this.1, (by clean_events : Clean _).append this.2.1, this.2.2⟩⟩
              | error e =>
                obtain ⟨x, rfl⟩ := o2 ⟨e, rfl⟩
                obtain ⟨hinv, hact, hcount⟩ := ih rest _ t₂ h₂ hT' (by simpa [Walk.leaveUnread] using (by omega))
                  (hi.leave _ fun scene => .failed (e := ⟨.findOLean root.toolchain m, .error x⟩) (hT₁.subset (by simp))
                    (.search scene hnamed hnone.1 hnone.2) ⟨x, rfl⟩)
                exact ⟨hinv, hobs.append hact, fun hu => by simpa [Walk.leaveUnread] using (hcount hu).1⟩

end Invariant

end RegulaSpecification.Effects
