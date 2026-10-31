/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.ReaderParts

/-!
# What the reader's walk over the imports gives

For every response: each source it holds was read by the exact-path test, its text written to the same relative
path of the tree and parsed from that same text; each toolchain module was found below the toolchain's library;
what it could not read has a `Reason`; and when nothing was left unread, each import of each source was reached.
-/

namespace RegulaSpecification.Effects

open Lean (Name Syntax Import MessageLog)
open Lean.Parser (InputContext ModuleParserState mkInputContext)
open System (FilePath)
open Regula.Effect
open Regula.Language
open Regula.Reader
open RegulaSpecification.Language

variable {L E : Type}

/-! ## One file -/

/-- `readExact` reads a file only through the exact-path test. -/
theorem readExact_spec {project path : FilePath} {t : List (Event L E)} {b : Except String String}
    (h : Runs (readExact project path : Attempt L E String).run t b) :
    (∀ text, b = .ok text → ∃ real, t = [⟨.realPath path, .ok real⟩, ⟨.readFile path, .ok text⟩] ∧
      Regula.Load.exactBelow project path real = true) ∧
    ((∃ e, b = .error e) → (∃ e ∈ t, Event.failedRead e) ∨
      ∃ real, t = [⟨.realPath path, .ok real⟩] ∧ Regula.Load.exactBelow project path real = false) ∧
    ∀ e ∈ t, e.acted? = none := by
  rw [readExact] at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r', h₃, rfl⟩ := runs_attempt_iff.mp h₁
  obtain rfl := runs_call_iff.mp h₃
  cases r' with
  | error e =>
    obtain ⟨rfl, rfl⟩ := h₂
    refine ⟨fun _ h' => (by cases h'),
      fun _ => .inl ⟨⟨.realPath path, .error e⟩, by simp, ⟨e, rfl⟩⟩, ?_⟩
    intro x hx
    have : x = ⟨.realPath path, .error e⟩ := by simpa using hx
    subst this
    rfl
  | ok real =>
    dsimp only [Except.mapError] at h₂
    split at h₂
    · rename_i hb
      obtain ⟨r'', h₄, rfl⟩ := runs_attempt_iff.mp h₂
      obtain rfl := runs_call_iff.mp h₄
      cases r'' with
      | ok text =>
        refine ⟨fun _ he => (by cases he; exact ⟨real, rfl, hb⟩), fun ⟨e, he⟩ => (by cases he), ?_⟩
        intro x hx
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> rfl
      | error e =>
        refine ⟨fun _ he => (by cases he), fun _ =>
          .inl ⟨⟨.readFile path, .error e⟩, by simp, ⟨e, rfl⟩⟩, ?_⟩
        intro x hx
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> rfl
    · rename_i hb
      obtain ⟨rfl, rfl⟩ := runs_attempt_throw_iff.mp h₂
      refine ⟨fun _ he => (by cases he), fun _ =>
        .inr ⟨real, rfl, by simpa using hb⟩, ?_⟩
      intro x hx
      have : x = ⟨.realPath path, .ok real⟩ := by simpa using hx
      subst this
      rfl

/-- `inTree` is `TreeRelative`. -/
theorem inTree_iff (tree path : FilePath) :
    inTree tree path = true ↔ ∃ rel, TreeRelative (parts tree) (parts path) rel := by
  simp only [inTree, Option.isSome_iff_exists, treeRelative_iff]

/-- Every act of these events lies in the tree. -/
def ActsIn (tree : FilePath) (t : List (Event L E)) : Prop :=
  ∀ e ∈ t, ∀ p, e.acted? = some p → inTree tree p = true

theorem actsIn_append {tree : FilePath} {t₁ t₂ : List (Event L E)} (h₁ : ActsIn tree t₁)
    (h₂ : ActsIn tree t₂) : ActsIn tree (t₁ ++ t₂) := by
  intro e he p hp
  rcases List.mem_append.mp he with h | h
  · exact h₁ e h p hp
  · exact h₂ e h p hp

theorem actsIn_nil {tree : FilePath} : ActsIn (L := L) (E := E) tree [] := by
  intro e he
  cases he

/-- `makeParent` makes a directory only after its test. -/
theorem makeParent_spec {tree path : FilePath} {t : List (Event L E)} {b : Except String Unit}
    (h : Runs (makeParent tree path : Attempt L E Unit).run t b) :
    ((∃ e, b = .error e) →
      (∃ d, path.parent = some d ∧ inTree tree d = false) ∨ ∃ e ∈ t, Event.failedRead e) ∧
    ActsIn tree t := by
  rw [makeParent] at h
  cases hp : path.parent with
  | none =>
    simp only [hp] at h
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h
    exact ⟨fun ⟨e, he⟩ => (by cases he), actsIn_nil⟩
  | some d =>
    simp only [hp] at h
    split at h
    · rename_i hd
      obtain ⟨r, h₁, rfl⟩ := runs_attempt_iff.mp h
      obtain rfl := runs_call_iff.mp h₁
      refine ⟨fun ⟨e, he⟩ => ?_, ?_⟩
      · cases r with
        | ok _ => cases he
        | error e' => exact .inr ⟨⟨.createDirAll d, .error e'⟩, by simp, ⟨e', rfl⟩⟩
      · intro e he p hp'
        have : e = ⟨.createDirAll d, r⟩ := by simpa using he
        subst this
        cases hp'
        exact hd
    · rename_i hd
      obtain ⟨rfl, rfl⟩ := runs_attempt_throw_iff.mp h
      exact ⟨fun _ => .inl ⟨d, rfl, by simpa using hd⟩, actsIn_nil⟩

/-- `writeInTree` writes only after its tests of the path and of the directory above it. -/
theorem writeInTree_spec {tree path : FilePath} {text : String} {t : List (Event L E)}
    {b : Except String Unit} (h : Runs (writeInTree tree path text : Attempt L E Unit).run t b) :
    (b = .ok () → ([⟨.writeFile path text, .ok ()⟩] : List (Event L E)).Sublist t) ∧
    ((∃ e, b = .error e) → OutsideTree tree path ∨ ∃ e ∈ t, Event.failedRead e) ∧
    ActsIn tree t := by
  rw [writeInTree] at h
  split at h
  · rename_i hin
    obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
    obtain ⟨m1, m2⟩ := makeParent_spec h₁
    have hout : (∃ d, path.parent = some d ∧ inTree tree d = false) → OutsideTree tree path := by
      rintro ⟨d, hd, hf⟩
      refine .inr ⟨d, hd, fun rel hr => ?_⟩
      have := (inTree_iff tree d).mpr ⟨rel, hr⟩
      simp [hf] at this
    cases r with
    | error e =>
      obtain ⟨rfl, rfl⟩ := h₂
      refine ⟨fun he => (by cases he), fun _ => ?_, by simpa using m2⟩
      rcases m1 ⟨e, rfl⟩ with h' | ⟨e', he', hf⟩
      · exact .inl (hout h')
      · exact .inr ⟨e', by simpa using he', hf⟩
    | ok u =>
      obtain ⟨r', h₃, rfl⟩ := runs_attempt_iff.mp h₂
      obtain rfl := runs_call_iff.mp h₃
      refine ⟨?_, ?_, actsIn_append m2 ?_⟩
      · intro he
        cases r' with
        | ok _ => simp
        | error _ => cases he
      · rintro ⟨e, he⟩
        cases r' with
        | ok _ => cases he
        | error e' => exact .inr ⟨⟨.writeFile path text, .error e'⟩, by simp, ⟨e', rfl⟩⟩
      · intro e he p hp
        have : e = ⟨.writeFile path text, r'⟩ := by simpa using he
        subst this
        cases hp
        exact hin
  · rename_i hin
    obtain ⟨rfl, rfl⟩ := runs_attempt_throw_iff.mp h
    refine ⟨fun he => (by cases he), fun _ => .inl (.inl fun rel hr => hin ?_), actsIn_nil⟩
    exact (inTree_iff tree path).mpr ⟨rel, hr⟩

/-- What one source holds, by these events: the exact-path test passed, the text read was written to `path`, and
Lean's header parser read that same text. -/
def SourceRead (T : List (Event L E)) (project tree path : FilePath) (s : Source) : Prop :=
  ∃ rel real text,
    TreeRelative (parts tree) (parts path) rel ∧
    Regula.Load.exactBelow project (joinParts project rel) real = true ∧
    s.input = mkInputContext text path.toString ∧
    ([⟨.realPath (joinParts project rel), .ok real⟩, ⟨.readFile (joinParts project rel), .ok text⟩,
      ⟨.writeFile path text, .ok ()⟩,
      ⟨.parseHeader s.input, .ok (s.header, s.state, s.messages, s.imports)⟩] :
        List (Event L E)).Sublist T

theorem SourceRead.mono {T T' : List (Event L E)} {project tree path : FilePath} {s : Source}
    (h : SourceRead T project tree path s) (hs : T.Sublist T') : SourceRead T' project tree path s := by
  obtain ⟨rel, real, text, h1, h2, h3, h4⟩ := h
  exact ⟨rel, real, text, h1, h2, h3, h4.trans hs⟩

/-- Why a source could not be read. -/
def SourceBad (t : List (Event L E)) (project tree path : FilePath) : Prop :=
  OutsideTree tree path ∨ (∃ e ∈ t, Event.failedRead e) ∨
    ∃ p real, (⟨.realPath p, .ok real⟩ : Event L E) ∈ t ∧ Regula.Load.exactBelow project p real = false

/-- `readSource` holds a source only as `SourceRead` states. -/
theorem readSource_spec {project tree path : FilePath} {t : List (Event L E)} {b : Except String Source}
    (h : Runs (readSource project tree path : Attempt L E Source).run t b) :
    (∀ s, b = .ok s → SourceRead t project tree path s) ∧
    ((∃ e, b = .error e) → SourceBad t project tree path) ∧
    ActsIn tree t := by
  rw [readSource] at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  rw [copyToTree] at h₁
  cases htr : treeRelative (Regula.Load.exactParts tree) (Regula.Load.exactParts path) with
  | none =>
    simp only [htr] at h₁
    obtain ⟨rfl, rfl⟩ := runs_attempt_throw_iff.mp h₁
    obtain ⟨rfl, rfl⟩ := h₂
    refine ⟨fun _ he => (by cases he), fun _ => .inl (.inl fun rel hr => ?_), actsIn_nil⟩
    rw [(treeRelative_iff _ _ _).mpr hr] at htr
    cases htr
  | some rel =>
    simp only [htr] at h₁
    obtain ⟨t₃, t₄, r₃, rfl, h₃, h₄⟩ := runs_attempt_bind_iff.mp h₁
    obtain ⟨e1, e2, e3⟩ := readExact_spec h₃
    have hread : ActsIn tree t₃ := fun e he p hp => by
      rw [e3 e he] at hp
      cases hp
    have hrel := (treeRelative_iff _ _ _).mp htr
    cases r₃ with
    | error why =>
      obtain ⟨rfl, rfl⟩ := h₄
      obtain ⟨rfl, rfl⟩ := h₂
      refine ⟨fun _ he => (by cases he), fun _ => ?_, by simpa using hread⟩
      rcases e2 ⟨why, rfl⟩ with ⟨e, he, hf⟩ | ⟨real, rfl, hb⟩
      · exact .inr (.inl ⟨e, by simpa using he, hf⟩)
      · exact .inr (.inr ⟨_, real, by simp, hb⟩)
    | ok text =>
      obtain ⟨real, rfl, hexact⟩ := e1 text rfl
      obtain ⟨t₅, t₆, r₅, rfl, h₅, h₆⟩ := runs_attempt_bind_iff.mp h₄
      obtain ⟨w1, w2, w3⟩ := writeInTree_spec h₅
      cases r₅ with
      | error why =>
        obtain ⟨rfl, rfl⟩ := h₆
        obtain ⟨rfl, rfl⟩ := h₂
        refine ⟨fun _ he => (by cases he), fun _ => ?_, by
          simpa using actsIn_append hread w3⟩
        rcases w2 ⟨why, rfl⟩ with h' | ⟨e, he, hf⟩
        · exact .inl h'
        · exact .inr (.inl ⟨e, by simp [he], hf⟩)
      | ok u =>
        obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₆
        obtain ⟨t₇, t₈, r₇, rfl, h₇, h₈⟩ := runs_attempt_bind_iff.mp h₂
        obtain ⟨r₉, h₉, rfl⟩ := runs_attempt_iff.mp h₇
        obtain rfl := runs_call_iff.mp h₉
        have hact : ActsIn tree (([⟨.realPath (joinParts project rel), .ok real⟩,
            ⟨.readFile (joinParts project rel), .ok text⟩] ++ t₅ ++ []) ++
              [⟨.parseHeader (mkInputContext text path.toString), r₉⟩]) := by
          refine actsIn_append (by simpa using actsIn_append hread w3) ?_
          intro e he p hp
          have : e = ⟨.parseHeader (mkInputContext text path.toString), r₉⟩ := by simpa using he
          subst this
          cases hp
        cases r₉ with
        | error e =>
          obtain ⟨rfl, rfl⟩ := h₈
          exact ⟨fun _ he => (by cases he), fun _ => .inr (.inl
            ⟨⟨.parseHeader (mkInputContext text path.toString), .error e⟩, by simp, ⟨e, rfl⟩⟩),
            by simpa using hact⟩
        | ok parsed =>
          obtain ⟨header, state, messages, imports⟩ := parsed
          obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₈
          refine ⟨fun s he => ?_, fun ⟨e, he⟩ => (by cases he), by simpa using hact⟩
          cases he
          refine ⟨rel, real, text, hrel, hexact, rfl, ?_⟩
          have hw := w1 rfl
          simp only [List.append_nil, List.cons_append, List.nil_append]
          refine List.Sublist.cons_cons _ (List.Sublist.cons_cons _ ?_)
          exact (List.Sublist.append hw (List.Sublist.refl _))

/-! ## The toolchain's modules -/

/-- `toolchainOLean` passes only on an `.olean` below one of `dirs`. -/
theorem toolchainOLean_spec {dirs : List FilePath} {m : Name} {t : List (Event L E)}
    {b : Except String Unit} (h : Runs (toolchainOLean dirs m : Attempt L E Unit).run t b) :
    (b = .ok () → ∃ olean real d, t = [⟨.findOLean m, .ok olean⟩, ⟨.realPath olean, .ok real⟩] ∧
      d ∈ dirs ∧ Regula.Load.below d real = true) ∧
    ((∃ e, b = .error e) → (∃ e ∈ t, Event.failedRead e) ∨
      ∃ olean real, t = [⟨.findOLean m, .ok olean⟩, ⟨.realPath olean, .ok real⟩] ∧
        ∀ d ∈ dirs, Regula.Load.below d real = false) ∧
    (∀ e ∈ t, e.acted? = none) := by
  rw [toolchainOLean] at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r', h₃, rfl⟩ := runs_attempt_iff.mp h₁
  obtain rfl := runs_call_iff.mp h₃
  cases r' with
  | error e =>
    obtain ⟨rfl, rfl⟩ := h₂
    refine ⟨fun he => (by cases he), fun _ => .inl ⟨⟨.findOLean m, .error e⟩, by simp, ⟨e, rfl⟩⟩, ?_⟩
    intro x hx
    have : x = ⟨.findOLean m, .error e⟩ := by simpa using hx
    subst this
    rfl
  | ok olean =>
    obtain ⟨t₃, t₄, r₃, rfl, h₄, h₅⟩ := runs_attempt_bind_iff.mp h₂
    obtain ⟨r₄, h₆, rfl⟩ := runs_attempt_iff.mp h₄
    obtain rfl := runs_call_iff.mp h₆
    cases r₄ with
    | error e =>
      obtain ⟨rfl, rfl⟩ := h₅
      refine ⟨fun he => (by cases he), fun _ => .inl ⟨⟨.realPath olean, .error e⟩, by simp, ⟨e, rfl⟩⟩, ?_⟩
      intro x hx
      simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | rfl <;> rfl
    | ok real =>
      have hacts : ∀ x ∈ ([⟨.findOLean m, .ok olean⟩, ⟨.realPath olean, .ok real⟩] : List (Event L E)),
          x.acted? = none := by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> rfl
      dsimp only [Except.mapError] at h₅
      split at h₅
      · rename_i hany
        obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₅
        obtain ⟨d, hd, hb⟩ := List.any_eq_true.mp hany
        exact ⟨fun _ => ⟨olean, real, d, rfl, hd, hb⟩, fun ⟨e, he⟩ => (by cases he), by simpa using hacts⟩
      · rename_i hany
        obtain ⟨rfl, rfl⟩ := runs_attempt_throw_iff.mp h₅
        refine ⟨fun he => (by cases he), fun _ => .inr ⟨olean, real, rfl, fun d hd => ?_⟩,
          by simpa using hacts⟩
        cases hb : Regula.Load.below d real with
        | false => rfl
        | true => exact absurd (List.any_eq_true.mpr ⟨d, hd, hb⟩) hany

/-! ## The importCount -/

theorem importCount_append (a b : List (Event L E)) :
    importCount (a ++ b) = importCount a + importCount b := by
  simp [importCount]

theorem importCount_mono {a b : List (Event L E)} (h : a.Sublist b) : importCount a ≤ importCount b := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons x _ ih =>
    simp only [importCount, List.map_cons, List.sum_cons] at ih ⊢
    omega
  | cons_cons x _ ih =>
    simp only [importCount, List.map_cons, List.sum_cons] at ih ⊢
    omega

/-! ## The walk -/

/-- What the walk reads against: the events `T` of the whole read, in which the project and the tree have real
paths, Lake's load gave `root` and the default targets gave `modules`, and each directory of the toolchain's library
has its real path in `reals`. -/
structure WalkCtx (T : List (Event L E)) (dir : FilePath) (project tree : FilePath) (root : Root L)
    (modules : List (Name × FilePath)) (reals : List (FilePath × FilePath)) : Prop where
  /-- The project's real path. -/
  project_real : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ T
  /-- The tree's real path. -/
  tree_real : ∃ treePath, (⟨.realPath treePath, .ok tree⟩ : Event L E) ∈ T
  /-- Lake's load. -/
  load : ∃ sysroot log, (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ T
  /-- The default targets' modules. -/
  default : DefaultModules T root root.defaultTargets modules
  /-- The directories of the toolchain's library. -/
  dirs_map : reals.map Prod.fst = root.toolchain
  /-- Their real paths. -/
  dirs_real : ∀ x ∈ reals, (⟨.realPath x.1, .ok x.2⟩ : Event L E) ∈ T

/-- What the walk has established of the state `w` with the names `todo` left to visit. -/
structure WalkInv (T : List (Event L E)) (dir project tree : FilePath) (root : Root L)
    (modules : List (Name × FilePath)) (reals : List (FilePath × FilePath)) (roots todo : List Name)
    (w : Walk) : Prop where
  /-- Each source was read. -/
  sources : ∀ x ∈ w.sources, ∃ path, fileOf root modules x.1 = some path ∧
    SourceRead T project tree path x.2 ∧ x.1 ∈ w.reached
  /-- Each toolchain module was found there. -/
  held : ∀ n ∈ w.toolchain, fileOf root modules n = none ∧ HeldByToolchain T root n
  /-- No module has two sources. -/
  nodup : (w.sources.map (·.1)).Nodup
  /-- What each module reached is. -/
  reached : ∀ m ∈ w.reached, (∃ s, (m, s) ∈ w.sources) ∨ m.getRoot = `Mathlib ∨ w.unread ≠ []
  /-- Each name reached is in the closed domain. -/
  closed : ∀ m ∈ w.reached, closedModuleName m = true ∨ w.unread ≠ []
  /-- Each name reached was named. -/
  named : ∀ m ∈ w.reached, Named T modules m
  /-- Each name left to visit was named. -/
  todoNamed : ∀ m ∈ todo, Named T modules m
  /-- What was left unread has a reason. -/
  unread : w.unread ≠ [] → Reason T dir .incomplete
  /-- Each import is visited, or left to visit. -/
  pending : w.unread = [] → ∀ x ∈ w.sources, ∀ i ∈ x.2.imports,
    i.module ∈ todo ∨ i.module ∈ w.reached ∨ i.module ∈ w.toolchain
  /-- Each root is visited, or left to visit. -/
  rootsIn : w.unread = [] → ∀ m ∈ roots, m ∈ todo ∨ m ∈ w.reached ∨ m ∈ w.toolchain

theorem fileOf_mem {root : Root L} {modules : List (Name × FilePath)} {m : Name} {path : FilePath}
    (h : fileOf root modules m = some path) : (m, path) ∈ modules ∨ root.resolve m = some path := by
  rw [fileOf] at h
  split at h
  · rename_i hl
    cases h
    left
    clear root
    induction modules with
    | nil => simp at hl
    | cons x xs ih =>
      obtain ⟨k, v⟩ := x
      simp only [List.lookup_cons] at hl
      by_cases hk : m = k
      · subst hk
        simp at hl
        subst hl
        simp
      · have : (m == k) = false := by simpa using hk
        simp only [this] at hl
        exact List.mem_cons_of_mem _ (ih hl)
  · exact .inr h

section Invariant

variable {T : List (Event L E)} {dir project tree : FilePath} {root : Root L}
  {modules : List (Name × FilePath)} {reals : List (FilePath × FilePath)} {roots : List Name}

theorem WalkInv.pop {m : Name} {rest : List Name} {w : Walk}
    (h : WalkInv T dir project tree root modules reals roots (m :: rest) w)
    (hm : m ∈ w.reached ∨ m ∈ w.toolchain) :
    WalkInv T dir project tree root modules reals roots rest w where
  sources := h.sources
  held := h.held
  nodup := h.nodup
  reached := h.reached
  closed := h.closed
  named := h.named
  todoNamed := fun n hn => h.todoNamed n (List.mem_cons_of_mem _ hn)
  unread := h.unread
  pending := fun hu x hx i hi => by
    rcases h.pending hu x hx i hi with h' | h'
    · rcases List.mem_cons.mp h' with h'' | h''
      · rw [h'']
        exact .inr hm
      · exact .inl h''
    · exact .inr h'
  rootsIn := fun hu n hn => by
    rcases h.rootsIn hu n hn with h' | h'
    · rcases List.mem_cons.mp h' with h'' | h''
      · rw [h'']
        exact .inr hm
      · exact .inl h''
    · exact .inr h'

theorem WalkInv.leave {m : Name} {rest : List Name} {w : Walk} (why : String)
    (h : WalkInv T dir project tree root modules reals roots (m :: rest) w)
    (hr : Reason T dir .incomplete) :
    WalkInv T dir project tree root modules reals roots rest (w.leaveUnread m why) where
  sources := fun x hx => by
    obtain ⟨path, h1, h2, h3⟩ := h.sources x hx
    exact ⟨path, h1, h2, List.mem_cons_of_mem _ h3⟩
  held := h.held
  nodup := h.nodup
  reached := fun _ _ => .inr (.inr (by simp [Walk.leaveUnread]))
  closed := fun _ _ => .inr (by simp [Walk.leaveUnread])
  named := fun n hn => by
    rcases List.mem_cons.mp hn with rfl | hn
    · exact h.todoNamed _ (List.mem_cons_self ..)
    · exact h.named n hn
  todoNamed := fun n hn => h.todoNamed n (List.mem_cons_of_mem _ hn)
  unread := fun _ => hr
  pending := fun hu => by simp [Walk.leaveUnread] at hu
  rootsIn := fun hu => by simp [Walk.leaveUnread] at hu

/-- A name that is left unread for the reasons of a stop in the walk: the whole state is then done, whatever was
left to visit. -/
theorem WalkInv.stop {m : Name} {rest : List Name} {w : Walk} (why : String)
    (h : WalkInv T dir project tree root modules reals roots (m :: rest) w)
    (hr : Reason T dir .incomplete) :
    WalkInv T dir project tree root modules reals roots [] (w.leaveUnread m why) :=
  have hl := h.leave why hr
  { sources := hl.sources, held := hl.held, nodup := hl.nodup, reached := hl.reached, closed := hl.closed,
    named := hl.named, todoNamed := fun _ hn => (by cases hn), unread := hl.unread,
    pending := fun hu => by simp [Walk.leaveUnread] at hu,
    rootsIn := fun hu => by simp [Walk.leaveUnread] at hu }

theorem WalkInv.mathlib {m : Name} {rest : List Name} {w : Walk}
    (h : WalkInv T dir project tree root modules reals roots (m :: rest) w)
    (hroot : m.getRoot = `Mathlib) (hc : closedModuleName m = true) :
    WalkInv T dir project tree root modules reals roots rest { w with reached := m :: w.reached } where
  sources := fun x hx => by
    obtain ⟨path, h1, h2, h3⟩ := h.sources x hx
    exact ⟨path, h1, h2, List.mem_cons_of_mem _ h3⟩
  held := h.held
  nodup := h.nodup
  reached := fun n hn => by
    rcases List.mem_cons.mp hn with rfl | hn
    · exact .inr (.inl hroot)
    · exact h.reached n hn
  closed := fun n hn => by
    rcases List.mem_cons.mp hn with rfl | hn
    · exact .inl hc
    · exact h.closed n hn
  named := fun n hn => by
    rcases List.mem_cons.mp hn with rfl | hn
    · exact h.todoNamed _ (List.mem_cons_self ..)
    · exact h.named n hn
  todoNamed := fun n hn => h.todoNamed n (List.mem_cons_of_mem _ hn)
  unread := h.unread
  pending := fun hu x hx i hi => by
    rcases h.pending hu x hx i hi with h' | h' | h'
    · rcases List.mem_cons.mp h' with h'' | h''
      · rw [h'']
        exact .inr (.inl (List.mem_cons_self ..))
      · exact .inl h''
    · exact .inr (.inl (List.mem_cons_of_mem _ h'))
    · exact .inr (.inr h')
  rootsIn := fun hu n hn => by
    rcases h.rootsIn hu n hn with h' | h' | h'
    · rcases List.mem_cons.mp h' with h'' | h''
      · rw [h'']
        exact .inr (.inl (List.mem_cons_self ..))
      · exact .inl h''
    · exact .inr (.inl (List.mem_cons_of_mem _ h'))
    · exact .inr (.inr h')

theorem WalkInv.read {m : Name} {rest : List Name} {w : Walk} {s : Source} {path : FilePath}
    (h : WalkInv T dir project tree root modules reals roots (m :: rest) w)
    (hm : m ∉ w.reached) (hf : fileOf root modules m = some path) (hs : SourceRead T project tree path s)
    (hc : closedModuleName m = true) :
    WalkInv T dir project tree root modules reals roots (s.imports.toList.map (·.module) ++ rest)
      { w with reached := m :: w.reached, sources := (m, s) :: w.sources } where
  sources := fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨path, hf, hs, List.mem_cons_self ..⟩
    · obtain ⟨p, h1, h2, h3⟩ := h.sources x hx
      exact ⟨p, h1, h2, List.mem_cons_of_mem _ h3⟩
  held := h.held
  nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, h.nodup⟩
    obtain ⟨x, hx, he⟩ := List.mem_map.mp hmem
    obtain ⟨_, _, _, h3⟩ := h.sources x hx
    exact hm (he ▸ h3)
  reached := fun n hn => by
    rcases List.mem_cons.mp hn with rfl | hn
    · exact .inl ⟨s, List.mem_cons_self ..⟩
    · rcases h.reached n hn with ⟨s', hs'⟩ | h' | h'
      · exact .inl ⟨s', List.mem_cons_of_mem _ hs'⟩
      · exact .inr (.inl h')
      · exact .inr (.inr h')
  closed := fun n hn => by
    rcases List.mem_cons.mp hn with rfl | hn
    · exact .inl hc
    · exact h.closed n hn
  named := fun n hn => by
    rcases List.mem_cons.mp hn with rfl | hn
    · exact h.todoNamed _ (List.mem_cons_self ..)
    · exact h.named n hn
  todoNamed := fun n hn => by
    rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hn
      obtain ⟨_, _, _, _, _, _, hsub⟩ := hs
      exact .inr ⟨s.input, s.header, s.state, s.messages, s.imports,
        hsub.subset (by simp), i, Array.mem_toList_iff.mp hi, rfl⟩
    · exact h.todoNamed n (List.mem_cons_of_mem _ hn)
  unread := h.unread
  pending := fun hu x hx i hi => by
    rcases List.mem_cons.mp hx with rfl | hx
    · refine .inl (List.mem_append_left _ (List.mem_map.mpr ⟨i, Array.mem_toList_iff.mpr hi, rfl⟩))
    · rcases h.pending hu x hx i hi with h' | h' | h'
      · rcases List.mem_cons.mp h' with h'' | h''
        · rw [h'']
          exact .inr (.inl (List.mem_cons_self ..))
        · exact .inl (List.mem_append_right _ h'')
      · exact .inr (.inl (List.mem_cons_of_mem _ h'))
      · exact .inr (.inr h')
  rootsIn := fun hu n hn => by
    rcases h.rootsIn hu n hn with h' | h' | h'
    · rcases List.mem_cons.mp h' with h'' | h''
      · rw [h'']
        exact .inr (.inl (List.mem_cons_self ..))
      · exact .inl (List.mem_append_right _ h'')
    · exact .inr (.inl (List.mem_cons_of_mem _ h'))
    · exact .inr (.inr h')

theorem WalkInv.toolchain {m : Name} {rest : List Name} {w : Walk}
    (h : WalkInv T dir project tree root modules reals roots (m :: rest) w)
    (hf : fileOf root modules m = none) (hh : HeldByToolchain T root m) :
    WalkInv T dir project tree root modules reals roots rest
      { w with toolchain := m :: w.toolchain } where
  sources := h.sources
  held := fun n hn => by
    rcases List.mem_cons.mp hn with rfl | hn
    · exact ⟨hf, hh⟩
    · exact h.held n hn
  nodup := h.nodup
  reached := h.reached
  closed := h.closed
  named := h.named
  todoNamed := fun n hn => h.todoNamed n (List.mem_cons_of_mem _ hn)
  unread := h.unread
  pending := fun hu x hx i hi => by
    rcases h.pending hu x hx i hi with h' | h' | h'
    · rcases List.mem_cons.mp h' with h'' | h''
      · rw [h'']
        exact .inr (.inr (List.mem_cons_self ..))
      · exact .inl h''
    · exact .inr (.inl h')
    · exact .inr (.inr (List.mem_cons_of_mem _ h'))
  rootsIn := fun hu n hn => by
    rcases h.rootsIn hu n hn with h' | h' | h'
    · rcases List.mem_cons.mp h' with h'' | h''
      · rw [h'']
        exact .inr (.inr (List.mem_cons_self ..))
      · exact .inl h''
    · exact .inr (.inl h')
    · exact .inr (.inr (List.mem_cons_of_mem _ h'))

/-- From what a source's reading could not do, a `Reason`. -/
theorem reason_of_sourceBad (c : WalkCtx T dir project tree root modules reals) {m : Name} {path : FilePath}
    {t : List (Event L E)} (hf : fileOf root modules m = some path) (ht : ∀ e ∈ t, e ∈ T)
    (h : SourceBad t project tree path) : Reason T dir .incomplete := by
  rcases h with h | ⟨e, he, hb⟩ | ⟨p, real, he, hb⟩
  · obtain ⟨treePath, htree⟩ := c.tree_real
    obtain ⟨sysroot, log, hload⟩ := c.load
    exact .moduleNotInTree htree hload c.default (fileOf_mem hf) h
  · exact .failed (ht e he) hb
  · exact .notExact c.project_real (ht _ he) hb

/-- The walk, for every response. `tDone` is what the read has asked so far, and the bound on `fuel` says how many
names it can still take: so it stops at its bound only when the imports it read reach that many. -/
theorem walk_spec (c : WalkCtx T dir project tree root modules reals) (fuel : Nat) (todo : List Name)
    (w : Walk) (tDone t : List (Event L E)) (w' : Walk)
    (h : Runs (walk project tree root modules (reals.map Prod.snd) fuel todo w) t w')
    (hT : (tDone ++ t).Sublist T)
    (hb : 1000000 + todo.length ≤ fuel + roots.length + importCount tDone)
    (hi : WalkInv T dir project tree root modules reals roots todo w) :
    WalkInv T dir project tree root modules reals roots [] w' ∧ ActsIn tree t := by
  induction fuel generalizing todo w tDone t with
  | zero =>
    cases todo with
    | nil =>
      rw [walk] at h
      obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h
      exact ⟨hi, actsIn_nil⟩
    | cons m rest =>
      rw [walk] at h
      obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h
      have hcount : importCount tDone ≤ importCount T :=
        importCount_mono ((List.sublist_append_left _ _).trans hT)
      simp only [List.length_cons] at hb
      exact ⟨hi.stop _ (.tooMany (roots := roots) (by omega)), actsIn_nil⟩
  | succ fuel ih =>
    cases todo with
    | nil =>
      rw [walk] at h
      obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h
      exact ⟨hi, actsIn_nil⟩
    | cons m rest =>
      simp only [List.length_cons] at hb
      rw [walk] at h
      split at h
      · rename_i hseen
        refine ih rest w tDone t h hT (by omega) (hi.pop ?_)
        simpa using hseen
      · rename_i hseen
        have hnotReached : m ∉ w.reached := fun hm => hseen (by simp [hm])
        split at h
        · rename_i hclosed
          have hname : closedModuleName m = false := by simpa using hclosed
          obtain ⟨sysroot, log, hload⟩ := c.load
          exact ih rest _ tDone t h hT (by omega)
            (hi.leave _ (.moduleName hload c.default (hi.todoNamed m (List.mem_cons_self ..))
              (fun hc => by simp [(closedModuleName_iff m).mpr hc] at hname)))
        · rename_i hclosed
          have hname : closedModuleName m = true := by simpa using hclosed
          split at h
          · rename_i hroot
            exact ih rest _ tDone t h hT (by omega) (hi.mathlib (by simpa using hroot) hname)
          · split at h
            · rename_i path hfile
              obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
              obtain ⟨s1, s2, s3⟩ := readSource_spec h₁
              have hT₁ : t₁.Sublist T :=
                ((List.sublist_append_left t₁ t₂).trans (List.sublist_append_right tDone _)).trans hT
              have hT' : (tDone ++ t₁ ++ t₂).Sublist T := by simpa using hT
              cases r with
              | ok s =>
                have hread := s1 s rfl
                have hcount : s.imports.size ≤ importCount t₁ := by
                  obtain ⟨_, _, _, _, _, _, hsub⟩ := hread
                  have hone : ([⟨.parseHeader s.input, .ok (s.header, s.state, s.messages, s.imports)⟩] :
                      List (Event L E)).Sublist t₁ := by
                    exact List.Sublist.trans (by simp) hsub
                  have := importCount_mono hone
                  simpa [importCount, Event.importsStated] using this
                have hcount' : importCount tDone + importCount t₁ = importCount (tDone ++ t₁) :=
                  (importCount_append _ _).symm
                obtain ⟨hinv, hact⟩ := ih _ _ (tDone ++ t₁) t₂ h₂ hT'
                  (by simp only [List.length_append, List.length_map, Array.length_toList]; omega)
                  (hi.read hnotReached hfile (hread.mono hT₁) hname)
                exact ⟨hinv, actsIn_append s3 hact⟩
              | error e =>
                obtain ⟨hinv, hact⟩ := ih rest _ (tDone ++ t₁) t₂ h₂ hT'
                  (by have := importCount_append tDone t₁; omega)
                  (hi.leave _ (reason_of_sourceBad c hfile hT₁.subset (s2 ⟨e, rfl⟩)))
                exact ⟨hinv, actsIn_append s3 hact⟩
            · rename_i hfile
              obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
              obtain ⟨o1, o2, o3⟩ := toolchainOLean_spec h₁
              have hT₁ : t₁.Sublist T :=
                ((List.sublist_append_left t₁ t₂).trans (List.sublist_append_right tDone _)).trans hT
              have hT' : (tDone ++ t₁ ++ t₂).Sublist T := by simpa using hT
              have hact₁ : ActsIn tree t₁ := fun e he p hp => by
                rw [o3 e he] at hp
                cases hp
              cases r with
              | ok u =>
                obtain ⟨olean, real, d, ht, hd, hbelow⟩ := o1 rfl
                subst ht
                obtain ⟨x, hx, hxd⟩ := List.mem_map.mp hd
                have hheld : HeldByToolchain T root m := by
                  refine ⟨olean, real, x.1, d, hT₁, ?_, ?_, hbelow⟩
                  · rw [← c.dirs_map]
                    exact List.mem_map.mpr ⟨x, hx, rfl⟩
                  · rw [← hxd]
                    exact c.dirs_real x hx
                obtain ⟨hinv, hact⟩ := ih rest _ (tDone ++ _) t₂ h₂ hT'
                  (by have := importCount_append tDone
                        [⟨.findOLean m, .ok olean⟩, ⟨.realPath olean, .ok real⟩]; omega)
                  (hi.toolchain hfile hheld)
                exact ⟨hinv, actsIn_append hact₁ hact⟩
              | error e =>
                have hreason : Reason T dir .incomplete := by
                  rcases o2 ⟨e, rfl⟩ with ⟨x, hx, hbad⟩ | ⟨olean, real, ht, hnot⟩
                  · exact .failed (hT₁.subset hx) hbad
                  · subst ht
                    obtain ⟨sysroot, log, hload⟩ := c.load
                    refine .notToolchain (m := m) (olean := olean) (real := real) hload
                      (hT₁.subset (by simp)) (hT₁.subset (by simp)) c.dirs_map fun x hx =>
                        ⟨c.dirs_real x hx, hnot _ (List.mem_map.mpr ⟨x, hx, rfl⟩)⟩
                obtain ⟨hinv, hact⟩ := ih rest _ (tDone ++ t₁) t₂ h₂ hT'
                  (by have := importCount_append tDone t₁; omega)
                  (hi.leave _ hreason)
                exact ⟨hinv, actsIn_append hact₁ hact⟩

end Invariant

end RegulaSpecification.Effects
