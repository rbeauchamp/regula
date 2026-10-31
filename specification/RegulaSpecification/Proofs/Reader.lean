/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Load
import RegulaSpecification.Proofs.ReaderFiles

/-!
# What the reader gives

`readProject_spec` is the theorem the reader exists for, for every response: a reading the check admits rests on
`Evidence`, so every file Lake would compile for the claim is read and the text judged is the text in the tree;
any other outcome rests on a `Reason`, so a project with no such reason is admitted; and every act lies in the
tree.
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

/-! ## The decision on what the stages give -/

theorem decision_not_closed {r : Reading} (h : r.configClosed = false) : decision r = .refused := by
  simp [decision, h]

theorem decision_not_full {r : Reading} (hc : r.configClosed = true) (h : r.readInFull = false) :
    decision r = .incomplete := by
  simp [decision, hc, h]

theorem decision_dependency {r : Reading} (hc : r.configClosed = true) (hf : r.readInFull = true)
    (h : r.requiresDependency = true) : decision r = .proofOnly := by
  simp [decision, hc, hf, h]

theorem decision_mathlib {r : Reading} (hc : r.configClosed = true) (hf : r.readInFull = true)
    (hd : r.requiresDependency = false) (h : r.mathlibReached = true) : decision r = .proofOnly := by
  simp [decision, hc, hf, hd, h]

theorem decision_not_covered {r : Reading} (hc : r.configClosed = true) (hf : r.readInFull = true)
    (hd : r.requiresDependency = false) (hm : r.mathlibReached = false) (h : r.covered = false) :
    decision r = .incomplete := by
  simp [decision, hc, hf, hd, hm, h]

theorem decision_files {r : Reading} (hc : r.configClosed = true) (hf : r.readInFull = true)
    (hd : r.requiresDependency = false) (hm : r.mathlibReached = false) (hv : r.covered = true)
    (h : r.filesAdmitted = false) : decision r = .refused := by
  simp [decision, hc, hf, hd, hm, hv, h]

theorem decision_admitted {r : Reading} (hc : r.configClosed = true) (hf : r.readInFull = true)
    (hd : r.requiresDependency = false) (hm : r.mathlibReached = false) (hv : r.covered = true)
    (h : r.filesAdmitted = true) : decision r = .admitted := by
  simp [decision, hc, hf, hd, hm, hv, h]

/-! ## The real paths of the toolchain's library -/

theorem realPaths_spec {paths : List FilePath} {t : List (Event L E)} {b : Except String (List FilePath)}
    (h : Runs (realPaths paths : Attempt L E _).run t b) :
    (∀ dirs, b = .ok dirs → ∃ reals : List (FilePath × FilePath), reals.map Prod.fst = paths ∧
      reals.map Prod.snd = dirs ∧ ∀ x ∈ reals, (⟨.realPath x.1, .ok x.2⟩ : Event L E) ∈ t) ∧
    ((∃ e, b = .error e) → ∃ e ∈ t, Event.failedRead e) ∧
    ∀ e ∈ t, e.acted? = none := by
  induction paths generalizing t b with
  | nil =>
    rw [realPaths] at h
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h
    refine ⟨fun dirs he => ?_, fun ⟨e, he⟩ => (by cases he), fun e he => (by cases he)⟩
    cases he
    exact ⟨[], rfl, rfl, by simp⟩
  | cons p rest ih =>
    rw [realPaths] at h
    obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
    obtain ⟨r', h₃, rfl⟩ := runs_attempt_iff.mp h₁
    obtain rfl := runs_call_iff.mp h₃
    cases r' with
    | error e =>
      obtain ⟨rfl, rfl⟩ := h₂
      refine ⟨fun _ he => (by cases he), fun _ => ⟨⟨.realPath p, .error e⟩, by simp, ⟨e, rfl⟩⟩,
        fun x hx => ?_⟩
      simp only [List.append_nil, List.mem_singleton] at hx
      subst hx
      rfl
    | ok real =>
      obtain ⟨t₃, t₄, r₃, rfl, h₄, h₅⟩ := runs_attempt_bind_iff.mp h₂
      obtain ⟨i1, i2, i3⟩ := ih h₄
      have hacts : ∀ x ∈ ([⟨.realPath p, .ok real⟩] : List (Event L E)) ++ t₃, x.acted? = none := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · have : x = ⟨.realPath p, .ok real⟩ := by simpa using hx
          subst this
          rfl
        · exact i3 x hx
      cases r₃ with
      | error w =>
        obtain ⟨rfl, rfl⟩ := h₅
        obtain ⟨e', he', hf⟩ := i2 ⟨w, rfl⟩
        exact ⟨fun _ he => (by cases he), fun _ => ⟨e', by simp [he'], hf⟩, by simpa using hacts⟩
      | ok reals =>
        obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₅
        refine ⟨fun dirs he => ?_, fun ⟨e, he⟩ => (by cases he), by simpa using hacts⟩
        cases he
        obtain ⟨xs, x1, x2, x3⟩ := i1 reals rfl
        refine ⟨(p, real) :: xs, by simp [x1], by simp [x2], fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · have := x3 x hx
          simp [this]

/-! ## From a source and its file to what the record states -/

theorem readAs_of {T : List (Event L E)} {project tree path : FilePath} {s : Source} {f : FileRead}
    {sources : List (Name × Source)} {toolchain : List Name} {m : Name}
    (hs : SourceRead T project tree path s) (hf : FileFrom T sources toolchain m s f) :
    ReadAs T project tree f path s.imports
      (visibleToolchain (fun n => (sources.lookup n).map (·.imports)) toolchain.contains
        (s.imports.toList.map (·.module)) []
        ((s.imports.toList.map (·.module)).length + (sources.map (·.2.imports.size)).sum + 1)).eraseDups := by
  obtain ⟨rel, real, text, h1, h2, h3, h4⟩ := hs
  obtain ⟨-, hheader, env, final, commands, hev, hp, hsub, hparsed⟩ := hf
  have hex := (RegulaSpecification.Loader.exactBelow_iff project (joinParts project rel) real).mp h2
  refine ⟨rel, real, text, s.state, s.messages, final, env, commands, h1, hex.1, hex.2, ?_, hev, ?_, hsub,
    hparsed⟩
  · rw [hheader, ← h3]
    exact h4
  · rw [← h3]
    exact hp

/-- The headers the parser's search reads, as the record states them. -/
def headersOf (sources : List (Name × Source)) : List (Name × Array Import) :=
  sources.map fun x => (x.1, x.2.imports)

theorem lookup_headersOf (sources : List (Name × Source)) (n : Name) :
    (headersOf sources).lookup n = (sources.lookup n).map (·.imports) := by
  induction sources with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨k, v⟩ := x
    simp only [headersOf, List.map_cons, List.lookup_cons] at ih ⊢
    cases hk : n == k <;> simp [ih]

theorem sum_headersOf (sources : List (Name × Source)) :
    ((headersOf sources).map (·.2.size)).sum = (sources.map (·.2.imports.size)).sum := by
  simp [headersOf, Function.comp_def]

/-- What the file's parser sees, in the record's words. -/
theorem mem_mods_iff (sources : List (Name × Source)) (toolchain : List Name) (s : Source) (n : Name) :
    n ∈ (visibleToolchain (fun n => (sources.lookup n).map (·.imports)) toolchain.contains
        (s.imports.toList.map (·.module)) []
        ((s.imports.toList.map (·.module)).length + (sources.map (·.2.imports.size)).sum + 1)).eraseDups ↔
      ∃ m ∈ s.imports, Sees (headersOf sources) toolchain m.module n := by
  rw [List.mem_eraseDups]
  have hfun : (fun n => (sources.lookup n).map (·.imports)) = fun n => (headersOf sources).lookup n := by
    funext x
    exact (lookup_headersOf sources x).symm
  rw [hfun, mem_visible_iff (headersOf sources) toolchain _ _
    (by rw [sum_headersOf]; omega) n]
  constructor
  · rintro ⟨m, hm, hs⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    exact ⟨i, Array.mem_toList_iff.mp hi, hs⟩
  · rintro ⟨i, hi, hs⟩
    exact ⟨i.module, List.mem_map.mpr ⟨i, Array.mem_toList_iff.mpr hi, rfl⟩, hs⟩

/-! ## The last stage: the walk and the commands -/

/-- What the reader's result must rest on, by the events `T`. -/
def ReadGoal (T : List (Event L E)) (dir treeDir : FilePath) (r : Reading) : Prop :=
  (decision r = .admitted → Evidence T dir treeDir r) ∧
    ∀ o, decision r = o → o ≠ .admitted → Reason T dir o

/-- What the stages before Lake's load established, by the events `T`. -/
structure Prior (T : List (Event L E)) (dir treeDir project tree : FilePath) (keys : List Name) : Prop where
  /-- The project's real path. -/
  project_real : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ T
  /-- The tree's real path. -/
  tree_real : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ T
  /-- They lie apart. -/
  apart : Apart project tree
  /-- The start from outside. -/
  started : ∃ sysroot program lakeLib, (⟨.lakeInstall sysroot, (program, lakeLib)⟩ : Event L E) ∈ T ∧
    StartedOutside T project lakeLib
  /-- `lean-toolchain`. -/
  toolchain : ∃ text real, (⟨.readFile (project / "lean-toolchain"), .ok text⟩ : Event L E) ∈ T ∧
    (⟨.realPath (project / "lean-toolchain"), .ok real⟩ : Event L E) ∈ T ∧
    parts real = parts (project / "lean-toolchain") ∧
    parts project <+: parts (project / "lean-toolchain") ∧
    text.trimAscii.toString = leanToolchain
  /-- No `lakefile.lean`. -/
  absent : ∃ e, (⟨.symlinkMetadata (project / "lakefile.lean"), .error e⟩ : Event L E) ∈ T ∧
    ∃ name code details, e = .noFileOrDirectory name code details
  /-- `lakefile.toml`. -/
  toml : ∃ text real table,
    (⟨.realPath (project / "lakefile.toml"), .ok real⟩ : Event L E) ∈ T ∧
    parts real = parts (project / "lakefile.toml") ∧
    parts project <+: parts (project / "lakefile.toml") ∧
    (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ T ∧
    (⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∈ T ∧
    (⟨.writeFile (tree / "lakefile.toml") text, .ok ()⟩ : Event L E) ∈ T ∧
    keys = keysOf 8 .anonymous table

/-- Each key path is in an admitted reading: the deep key is in no closed set. -/
theorem keyPaths_in {r : Reading} {table : Lake.Toml.Table} (hi : Inside r)
    (hk : r.configKeys = keysOf 8 .anonymous table) (n : Name) (hn : KeyPath .anonymous table n) :
    n ∈ r.configKeys := by
  rw [hk]
  rcases keysOf_complete hn 8 with h | ⟨d, hd, hdeep⟩
  · exact h
  · exfalso
    obtain ⟨hc, -, hnd, -⟩ := hi
    have hdr : d ∈ r.configKeys := hk ▸ hd
    by_cases hroot : d.getRoot = `require
    · exact hnd ⟨d, hdr, hroot⟩
    · exact deepKey_not_admitted hdeep (hc.2.2.2 d hdr hroot)

/-- What `configUnread` empty says: each default root is its name's one file, also by Lake's import resolution. -/
theorem configUnread_nil {root : Root L} {modules : List (Name × FilePath)}
    (h : configUnread root modules = []) :
    (∀ m file other, (m, file) ∈ modules → root.resolve m = some other → other = file) ∧
      (∀ m file other, (m, file) ∈ modules → (m, other) ∈ modules → other = file) := by
  simp only [configUnread, List.append_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff] at h
  obtain ⟨⟨-, h1⟩, h2⟩ := h
  constructor
  · intro m file other hm hr
    have := h1 (m, file) hm
    simp only [hr, bne_eq_false_iff_eq, Bool.not_eq_true] at this
    exact this
  · intro m file other hm ho
    have := h2 (m, file) hm
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, not_exists, not_and] at this
    by_cases he : other = file
    · exact he
    · exact absurd he (fun _ => this (m, other) ho rfl he)

/-- A module of the default targets has its own file, when no name has two. -/
theorem fileOf_of_mem {root : Root L} {modules : List (Name × FilePath)} {m : Name} {path : FilePath}
    (ht : ∀ m file other, (m, file) ∈ modules → (m, other) ∈ modules → other = file)
    (hm : (m, path) ∈ modules) : fileOf root modules m = some path := by
  have hl : ∃ file, modules.lookup m = some file := by
    cases hl : modules.lookup m with
    | some file => exact ⟨file, rfl⟩
    | none =>
      exfalso
      clear ht
      induction modules with
      | nil => cases hm
      | cons x xs ih =>
        obtain ⟨k, v⟩ := x
        by_cases hk : m = k
        · subst hk
          simp at hl
        · have hne : (m == k) = false := by simpa using hk
          simp only [List.lookup_cons, hne] at hl
          rcases List.mem_cons.mp hm with he | hm'
          · cases he
            exact hk rfl
          · exact ih hm' hl
  obtain ⟨file, hl⟩ := hl
  have := ht m file path (mem_of_lookup hl) hm
  subst this
  simp [fileOf, hl]

/-- The evidence of an admitted reading, from what the walk and the parse established. -/
theorem lastStage_evidence {T : List (Event L E)} {dir treeDir project tree : FilePath} {root : Root L}
    {modules : List (Name × FilePath)} {start r : Reading} {sysroot : String} {log : List String}
    {reals : List (FilePath × FilePath)} {w : Walk} {files : List FileRead}
    (hp : Prior T dir treeDir project tree start.configKeys)
    (hload : (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ T)
    (hmods : DefaultModules T root root.defaultTargets modules)
    (hreached : ∀ m, m ∈ r.reached ↔ m ∈ w.reached) (hrfiles : r.files = files)
    (hrroots : r.roots = modules.map (·.1)) (hrkeys : r.configKeys = start.configKeys)
    (hinside : Inside r)
    (I : WalkInv T dir project tree root modules reals (modules.map (·.1)) [] w) (hu : w.unread = [])
    (hfacts : (∀ m file other, (m, file) ∈ modules → root.resolve m = some other → other = file) ∧
      (∀ m file other, (m, file) ∈ modules → (m, other) ∈ modules → other = file))
    (hroots : ∀ m path, (m, path) ∈ modules → m ∈ w.reached)
    (hread : ∀ m path, fileOf root modules m = some path → m ∈ w.reached →
      ∃ f ∈ files, f.module = m ∧ ∃ imports mods, ReadAs T project tree f path imports mods)
    (hsomeFile : ∀ n path', root.resolve n = some path' → fileOf root modules n = some path')
    (hlookup : ∀ x ∈ w.sources, (headersOf w.sources.reverse).lookup x.1 = some x.2.imports)
    (hfileRead : ∀ f ∈ files, ∃ x ∈ w.sources, ∃ path,
      fileOf root modules x.1 = some path ∧ SourceRead T project tree path x.2 ∧
      FileFrom T w.sources.reverse w.toolchain x.1 x.2 f) :
    Evidence T dir treeDir r := by
  obtain ⟨text, real, table, t1, t2, t3, t4, t5, t6, hk⟩ := hp.toml
  have hkeys := keyPaths_in hinside (hrkeys.trans hk)
  refine ⟨project, tree, hp.project_real, hp.tree_real, hp.apart, hp.started, hp.toolchain, hp.absent,
    ⟨text, real, table, t1, t2, t3, t4, t5, t6, hkeys⟩, sysroot, root, log, modules, hload, hmods, hrroots,
    headersOf w.sources.reverse, w.toolchain, ?_, fun n hn => (I.held n hn).2, ?_⟩
  · intro m path hc
    rw [hrfiles]
    induction hc with
    | root hm => exact hread _ _ (fileOf_of_mem hfacts.2 hm) (hroots _ _ hm)
    | @imported m path imports n path' _ hl hn hres _ =>
      obtain ⟨i, hi, rfl⟩ := hn
      have hmem := mem_of_lookup hl
      obtain ⟨x, hx, he⟩ := List.mem_map.mp hmem
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hxs := List.mem_reverse.mp hx
      rcases I.pending hu x hxs i hi with h' | h' | h'
      · cases h'
      · exact hread _ _ (hsomeFile _ _ hres) h'
      · have := (I.held _ h').1
        rw [hsomeFile _ _ hres] at this
        cases this
  · intro f hf
    rw [hrfiles] at hf
    obtain ⟨x, hx, path, _, hs, hfrom⟩ := hfileRead f hf
    refine ⟨path, x.2.imports, _, readAs_of hs hfrom, ?_, mem_mods_iff _ _ _, ?_⟩
    · rw [hfrom.1]
      exact hlookup x hx
    · intro i hi
      rcases I.pending hu x hx i hi with h' | h' | h'
      · cases h'
      · exact .inl ((hreached _).mpr h')
      · obtain ⟨hnone, hheld⟩ := I.held _ h'
        rw [fileOf] at hnone
        split at hnone
        · cases hnone
        · rename_i hl
          exact .inr ⟨hnone, hl, hheld⟩

/-- What the last stage's reading rests on, once every file has its commands. -/
theorem lastStage_goal {T : List (Event L E)} {dir treeDir project tree : FilePath} {root : Root L}
    {modules : List (Name × FilePath)} {start : Reading} {sysroot : String} {log : List String}
    {reals : List (FilePath × FilePath)} {w : Walk} {files : List FileRead}
    (hp : Prior T dir treeDir project tree start.configKeys) (hc : start.configClosed = true)
    (hd : start.requiresDependency = false)
    (hload : (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ T)
    (hmods : DefaultModules T root root.defaultTargets modules)
    (hfacts : (∀ m file other, (m, file) ∈ modules → root.resolve m = some other → other = file) ∧
      (∀ m file other, (m, file) ∈ modules → (m, other) ∈ modules → other = file))
    (I : WalkInv T dir project tree root modules reals (modules.map (·.1)) [] w)
    (hu : w.unread = [])
    (hf : (baseReading start root modules w).readInFull = true)
    (hm : (baseReading start root modules w).mathlibReached = false)
    (g1 : ∀ f ∈ files, ∃ x ∈ w.sources.reverse, FileFrom T w.sources.reverse w.toolchain x.1 x.2 f)
    (g2 : ∀ x ∈ w.sources.reverse, ∃ f ∈ files, FileFrom T w.sources.reverse w.toolchain x.1 x.2 f) :
    ReadGoal T dir treeDir { baseReading start root modules w with files } := by
  obtain ⟨r, hr⟩ : ∃ r : Reading, r = { baseReading start root modules w with files } := ⟨_, rfl⟩
  rw [← hr]
  have hrc : r.configClosed = true := by rw [hr]; exact hc
  have hrd : r.requiresDependency = false := by rw [hr]; exact hd
  have hrm : r.mathlibReached = false := by rw [hr]; exact hm
  have hrf : r.readInFull = true := by rw [hr]; exact hf
  have hrfiles : r.files = files := by rw [hr]
  have hrroots : r.roots = modules.map (·.1) := by rw [hr]; rfl
  have hrkeys : r.configKeys = start.configKeys := by rw [hr]; rfl
  have hreached : ∀ m, m ∈ r.reached ↔ m ∈ w.reached := by
    intro m
    rw [hr]
    simp [baseReading]
  have hroots : ∀ m path, (m, path) ∈ modules → m ∈ w.reached := by
    intro m path hmp
    rcases I.rootsIn hu m (List.mem_map.mpr ⟨(m, path), hmp, rfl⟩) with h' | h' | h'
    · cases h'
    · exact h'
    · have := (I.held m h').1
      rw [fileOf_of_mem hfacts.2 hmp] at this
      cases this
  have hsource : ∀ m ∈ w.reached, ∃ s, (m, s) ∈ w.sources := by
    intro m hmr
    rcases I.reached m hmr with h' | h' | h'
    · exact h'
    · exfalso
      have : (baseReading start root modules w).mathlibReached = true := by
        refine List.any_eq_true.mpr ⟨m, by simpa [baseReading] using hmr, by simpa using h'⟩
      rw [hm] at this
      cases this
    · exact absurd hu h'
  have hclosed : ∀ m ∈ w.reached, closedModuleName m = true := by
    intro m hmr
    rcases I.closed m hmr with h' | h'
    · exact h'
    · exact absurd hu h'
  have hnodup : ((w.sources.reverse).map (·.1)).Nodup := by
    rw [List.map_reverse]
    exact List.pairwise_reverse.mpr (I.nodup.imp fun h h' => h h'.symm)
  have hlookup : ∀ x ∈ w.sources, (headersOf w.sources.reverse).lookup x.1 = some x.2.imports := by
    intro x hx
    rw [lookup_headersOf, lookup_of_mem hnodup (List.mem_reverse.mpr hx)]
    rfl
  have hread : ∀ m path, fileOf root modules m = some path → m ∈ w.reached →
      ∃ f ∈ files, f.module = m ∧ ∃ imports mods, ReadAs T project tree f path imports mods := by
    intro m path hfile hmr
    obtain ⟨s, hs⟩ := hsource m hmr
    obtain ⟨p, h1, h2, -⟩ := I.sources _ hs
    have hp' : p = path := by
      simp only at h1
      rw [hfile] at h1
      cases h1
      rfl
    subst hp'
    obtain ⟨f, hf', hfrom⟩ := g2 (m, s) (List.mem_reverse.mpr hs)
    exact ⟨f, hf', hfrom.1, _, _, readAs_of h2 hfrom⟩
  have hsomeFile : ∀ n path', root.resolve n = some path' → fileOf root modules n = some path' := by
    intro n path' hres
    rw [fileOf]
    split
    · rename_i q hl
      rw [hfacts.1 n q path' (mem_of_lookup hl) hres]
    · exact hres
  by_cases hmod : modules = []
  · have hcov : r.covered = false := by
      simp [Reading.covered, hrroots, hmod]
    have hdec := decision_not_covered hrc hrf hrd hrm hcov
    refine ⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho hne => ?_⟩
    rw [hdec] at ho
    subst ho
    exact .noClaim hload (hmod ▸ hmods)
  · have hcov : r.covered = true := by
      simp only [Reading.covered, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · rw [hrroots]
        cases modules with
        | nil => exact absurd rfl hmod
        | cons _ _ => rfl
      · intro m hmr
        rw [hrroots] at hmr
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hmr
        simpa using (hreached _).mpr (hroots x.1 x.2 hx)
      · intro m hmr
        exact hclosed m ((hreached m).mp hmr)
      · intro m hmr
        obtain ⟨s, hs⟩ := hsource m ((hreached m).mp hmr)
        obtain ⟨f, hf', hfrom⟩ := g2 (m, s) (List.mem_reverse.mpr hs)
        rw [hrfiles]
        exact List.any_eq_true.mpr ⟨f, hf', by simpa using hfrom.1⟩
    have hfileRead : ∀ f ∈ files, ∃ x ∈ w.sources, ∃ path,
        fileOf root modules x.1 = some path ∧ SourceRead T project tree path x.2 ∧
        FileFrom T w.sources.reverse w.toolchain x.1 x.2 f := by
      intro f hf'
      obtain ⟨x, hx, hfrom⟩ := g1 f hf'
      have hx' := List.mem_reverse.mp hx
      obtain ⟨p, h1, h2, -⟩ := I.sources x hx'
      exact ⟨x, hx', p, h1, h2, hfrom⟩
    by_cases hfa : r.filesAdmitted = true
    · have hdec := decision_admitted hrc hrf hrd hrm hcov hfa
      refine ⟨fun _ => ?_, fun o ho hne => absurd (ho.symm.trans hdec) hne⟩
      exact lastStage_evidence hp hload hmods hreached hrfiles hrroots hrkeys
        ((decision_admitted_iff r).mp hdec) I hu hfacts hroots hread hsomeFile hlookup hfileRead
    · have hfa' : r.filesAdmitted = false := by simpa using hfa
      have hdec := decision_files hrc hrf hrd hrm hcov hfa'
      refine ⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho hne => ?_⟩
      rw [hdec] at ho
      subst ho
      have hnot : ¬ FilesAdmitted r := fun h => hfa ((filesAdmitted_iff r).mpr h)
      obtain ⟨f, hf', hna⟩ : ∃ f ∈ r.files, ¬ FileAdmitted f := by
        refine Classical.byContradiction fun hx => hnot fun f hf' => ?_
        refine Classical.byContradiction fun hy => hx ⟨f, hf', hy⟩
      rw [hrfiles] at hf'
      obtain ⟨x, -, p, -, h2, hfrom⟩ := hfileRead f hf'
      exact .file hp.project_real (readAs_of h2 hfrom) hna


/-- The last stage of the reader. -/
theorem readFiles_spec {T t : List (Event L E)} {dir treeDir project tree : FilePath} {root : Root L}
    {modules : List (Name × FilePath)} {start : Reading} {sysroot : String} {log : List String}
    {b : Except String (Reading × List (Name × Source))} (hT : t.Sublist T)
    (hp : Prior T dir treeDir project tree start.configKeys) (hc : start.configClosed = true)
    (hd : start.requiresDependency = false) (hout : start.outside = true)
    (hload : (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ T)
    (hmods : DefaultModules T root root.defaultTargets modules)
    (hunread : configUnread root modules = [])
    (h : Runs (readFiles project tree root modules start : Attempt L E _).run t b) :
    (∀ r srcs, b = .ok (r, srcs) → ReadGoal T dir treeDir r) ∧
      ((∃ e, b = .error e) → Reason T dir .incomplete) ∧ ActsIn tree t := by
  rw [readFiles] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨u, h₃, rfl⟩ := runs_lift_iff.mp h₁
  obtain rfl := runs_call_iff.mp h₃
  have hT₂ : t₂.Sublist T := (List.sublist_append_right _ _).trans hT
  have hact₁ : ActsIn (L := L) (E := E) tree [⟨.setSearchPath root.toolchain, u⟩] := by
    intro e he p hp'
    have : e = ⟨.setSearchPath root.toolchain, u⟩ := by simpa using he
    subst this
    cases hp'
  obtain ⟨t₃, t₄, r₃, rfl, h₄, h₅⟩ := runs_attempt_bind_iff.mp h₂
  have hT₃ : t₃.Sublist T := (List.sublist_append_left _ _).trans hT₂
  have hT₄ : t₄.Sublist T := (List.sublist_append_right _ _).trans hT₂
  obtain ⟨d1, d2, d3⟩ := realPaths_spec h₄
  have hact₃ : ActsIn tree t₃ := fun e he p hp' => by
    rw [d3 e he] at hp'
    cases hp'
  cases r₃ with
  | error why =>
    obtain ⟨rfl, rfl⟩ := h₅
    obtain ⟨e', he', hf⟩ := d2 ⟨why, rfl⟩
    exact ⟨fun _ _ he => (by cases he), fun _ => .failed (hT₃.subset he') hf,
      by simpa using actsIn_append hact₁ hact₃⟩
  | ok dirs =>
    obtain ⟨reals, x1, rfl, x3⟩ := d1 dirs rfl
    obtain ⟨t₅, t₆, r₅, rfl, h₆, h₇⟩ := runs_attempt_bind_iff.mp h₅
    have hT₅ : t₅.Sublist T := (List.sublist_append_left _ _).trans hT₄
    have hT₆ : t₆.Sublist T := (List.sublist_append_right _ _).trans hT₄
    obtain ⟨w, h₈, rfl⟩ := runs_lift_iff.mp h₆
    have ctx : WalkCtx T dir project tree root modules reals :=
      { project_real := hp.project_real, tree_real := ⟨treeDir, hp.tree_real⟩,
        load := ⟨sysroot, log, hload⟩, default := hmods, dirs_map := x1,
        dirs_real := fun x hx => hT₃.subset (x3 x hx) }
    have hinit : WalkInv T dir project tree root modules reals (modules.map (·.1)) (modules.map (·.1)) {} :=
      { sources := by simp, held := by simp, nodup := by simp, reached := by simp, closed := by simp,
        named := by simp, todoNamed := fun m hm => .inl hm, unread := by simp, pending := by simp,
        rootsIn := fun _ m hm => .inl hm }
    obtain ⟨I, hactWalk⟩ := walk_spec (roots := modules.map (·.1)) ctx 1000000 (modules.map (·.1)) {} [] t₅ w
      h₈ (by simpa using hT₅) (by simp) hinit
    have hfacts := configUnread_nil hunread
    have hprefix : ActsIn tree ([⟨.setSearchPath root.toolchain, u⟩] ++ t₃) := actsIn_append hact₁ hact₃
    have hw : ActsIn tree t₅ := hactWalk
    have hacts : ActsIn tree ([⟨.setSearchPath root.toolchain, u⟩] ++ (t₃ ++ (t₅ ++ []))) := by
      simpa using actsIn_append hprefix hw
    have hbc : (baseReading start root modules w).configClosed = true := hc
    have hbd : (baseReading start root modules w).requiresDependency = false := hd
    have hsrcEv : ∀ x ∈ w.sources, ∃ path, fileOf root modules x.1 = some path ∧
        SourceRead T project tree path x.2 := fun x hx => by
      obtain ⟨p, h1, h2, -⟩ := I.sources x hx
      exact ⟨p, h1, h2⟩
    dsimp only at h₇
    split at h₇
    · rename_i hcond
      obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₇
      refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), by simpa using hacts⟩
      cases he
      by_cases hf : (baseReading start root modules w).readInFull = true
      · have hm : (baseReading start root modules w).mathlibReached = true := by
          simpa [hf] using hcond
        have hdec := decision_mathlib hbc hf hbd hm
        refine ⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho hne => ?_⟩
        rw [hdec] at ho
        subst ho
        obtain ⟨m, hm', hroot⟩ := List.any_eq_true.mp hm
        have hmr : m ∈ w.reached := by simpa [baseReading] using hm'
        exact .mathlib hload hmods (I.named m hmr) (by simpa using hroot)
      · have hf' : (baseReading start root modules w).readInFull = false := by simpa using hf
        have hdec := decision_not_full hbc hf'
        refine ⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho hne => ?_⟩
        rw [hdec] at ho
        subst ho
        have hne' : w.unread.reverse ++ importedExecutableRoots root modules w.sources.reverse ≠ [] := by
          intro hnil
          have : (baseReading start root modules w).readInFull = true := by
            simp [Reading.readInFull, baseReading, hout, hnil]
          simp [this] at hf'
        by_cases hu : w.unread = []
        · have himp : importedExecutableRoots root modules w.sources.reverse ≠ [] := by
            simpa [hu] using hne'
          obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ himp
          simp only [importedExecutableRoots, List.mem_map, List.mem_filter, List.mem_eraseDups,
            List.mem_flatMap, Bool.and_eq_true] at hx
          obtain ⟨m, ⟨⟨y, hy, hmy⟩, hl, hr⟩, -⟩ := hx
          obtain ⟨i, hi, rfl⟩ := hmy
          obtain ⟨p, -, ⟨rel, real, text, -, -, -, hsub⟩⟩ := hsrcEv y (List.mem_reverse.mp hy)
          exact .importedRoot hload hmods (hsub.subset (by simp)) (Array.mem_toList_iff.mp hi) hl
            (by simpa using hr)
        · exact I.unread hu
    · rename_i hcond
      have hf : (baseReading start root modules w).readInFull = true := by
        cases hx : (baseReading start root modules w).readInFull with
        | true => rfl
        | false => exact absurd (by simp [hx]) hcond
      have hm : (baseReading start root modules w).mathlibReached = false := by
        cases hx : (baseReading start root modules w).mathlibReached with
        | false => rfl
        | true => exact absurd (by simp [hx]) hcond
      have hu : w.unread = [] := by
        have := hf
        simp only [Reading.readInFull, baseReading, hout, Bool.true_and, List.isEmpty_iff,
          List.append_eq_nil_iff, List.reverse_eq_nil_iff] at this
        exact this.1
      obtain ⟨t₇, t₈, r₇, rfl, h₉, h₁₀⟩ := runs_attempt_bind_iff.mp h₇
      have hT₇ : t₇.Sublist T := (List.sublist_append_left _ _).trans hT₆
      obtain ⟨p1, p2, p3⟩ := parseFiles_spec w.sources.reverse w.toolchain w.sources.reverse [] hT₇ (by simp) h₉
      have hact₇ : ActsIn tree t₇ := fun e he p hp' => by
        rw [p3 e he] at hp'
        cases hp'
      cases r₇ with
      | error why =>
        obtain ⟨rfl, rfl⟩ := h₁₀
        obtain ⟨e', he', hb⟩ := p2 ⟨why, rfl⟩
        exact ⟨fun _ _ he => (by cases he), fun _ => .failed (hT₇.subset he') hb,
          by simpa using actsIn_append (actsIn_append hprefix hw) hact₇⟩
      | ok files =>
        obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₁₀
        refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he),
          by simpa using actsIn_append (actsIn_append hprefix hw) hact₇⟩
        cases he
        obtain ⟨g1, g2⟩ := p1 files rfl
        exact lastStage_goal hp hc hd hload hmods hfacts I hu hf hm g1 g2

end RegulaSpecification.Effects
