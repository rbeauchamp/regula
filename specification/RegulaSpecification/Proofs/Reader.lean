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
    ((∃ e, b = .error e) → ∃ p ∈ paths, ∃ x, (⟨.realPath p, .error x⟩ : Event L E) ∈ t) ∧
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
      refine ⟨fun _ he => (by cases he), fun _ => ⟨p, List.mem_cons_self .., e, by simp⟩,
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
        obtain ⟨q, hq, x, hx⟩ := i2 ⟨w, rfl⟩
        exact ⟨fun _ he => (by cases he), fun _ => ⟨q, List.mem_cons_of_mem _ hq, x, by simp [hx]⟩, by simpa using hacts⟩
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

theorem readText_of {T : List (Event L E)} {project tree path : FilePath} {s : Source} {f : FileRead}
    {sources : List (Name × Source)} {toolchain : List Name} {m : Name}
    (hs : SourceRead T project tree path s) (hf : FileFrom T sources toolchain m s f) :
    ReadText T project tree f path s.imports
      (visibleToolchain (fun n => (sources.lookup n).map (·.imports)) toolchain.contains
        (s.imports.toList.map (·.module)) []
        ((s.imports.toList.map (·.module)).length + (sources.map (·.2.imports.size)).sum + 1)).eraseDups s.text := by
  obtain ⟨rel, real, text, h1, -, h2, -, h3t, h3, h4⟩ := hs
  obtain ⟨-, hheader, env, final, commands, hev, hp, hsub, hparsed⟩ := hf
  have hex := (RegulaSpecification.Loader.exactBelow_iff project (joinParts project rel) real).mp h2
  rw [h3t]
  refine ⟨rel, real, s.state, s.messages, final, env, commands, h1, hex.1, hex.2, ?_, hev, ?_, hsub,
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

/-- What an admission has the tree hold: the configuration, the pinned `lean-toolchain`, and each source's text at its file,
in the order the run writes them. -/
abbrev planOf (tree : FilePath) (text : String) (srcs : List (Name × Source)) : List (FilePath × String) :=
  [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] ++ srcs.map fun x => (x.2.path, x.2.text)

/-- `held` holds what the plan says at each of its paths, and nothing else. -/
def Holds (tree : FilePath) (text : String) (srcs : List (Name × Source)) (held : List String → Option String) : Prop :=
  (∀ x ∈ planOf tree text srcs, held (parts x.1) = some x.2) ∧
    ∀ p v, held p = some v → ∃ x ∈ planOf tree text srcs, parts x.1 = p ∧ x.2 = v

theorem Holds.congr {tree : FilePath} {text : String} {srcs : List (Name × Source)} {a b : List String → Option String}
    (he : ∀ p, b p = a p) (h : Holds tree text srcs a) : Holds tree text srcs b := by
  have : b = a := funext he
  rw [this]
  exact h

theorem Holds.toml {tree : FilePath} {text : String} {srcs : List (Name × Source)} {held : List String → Option String}
    (h : Holds tree text srcs held) : held (parts (tree / "lakefile.toml")) = some text :=
  h.1 (tree / "lakefile.toml", text) (List.mem_append_left _ (List.mem_cons_self ..))

theorem Holds.toolchain {tree : FilePath} {text : String} {srcs : List (Name × Source)} {held : List String → Option String}
    (h : Holds tree text srcs held) : held (parts (tree / "lean-toolchain")) = some leanToolchain :=
  h.1 (tree / "lean-toolchain", leanToolchain)
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

/-- What the reader's result must rest on, by the events `T`, for each state of the tree that `H` admits. -/
def ReadGoal (T : List (Event L E)) (dir treeDir : FilePath) (H : (List String → Option String) → Prop)
    (r : Reading) : Prop :=
  (decision r = .admitted → ∀ held, H held → Evidence T dir treeDir held r) ∧
    ∀ o, decision r = o → o ≠ .admitted → Reason T dir treeDir o

/-- What the stages before Lake's load established, by the events `T`: `text` is the text of `lakefile.toml`. -/
structure Prior (T : List (Event L E)) (dir treeDir project tree : FilePath) (text : String) (keys : List Name) : Prop where
  /-- The project's real path. -/
  project_real : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ T
  /-- The tree's real path. -/
  tree_real : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ T
  /-- They lie apart. -/
  apart : Apart project tree
  /-- The start from outside. -/
  started : ∃ sysroot program lakeLib, (⟨.getEnv "LEAN_SYSROOT", some sysroot⟩ : Event L E) ∈ T ∧
    (⟨.lakeInstall sysroot, (program, lakeLib)⟩ : Event L E) ∈ T ∧ StartedOutside T project lakeLib
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
  toml : ∃ real table,
    (⟨.realPath (project / "lakefile.toml"), .ok real⟩ : Event L E) ∈ T ∧
    parts real = parts (project / "lakefile.toml") ∧
    parts project <+: parts (project / "lakefile.toml") ∧
    (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ T ∧
    (⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∈ T ∧
    keys = keysOf 8 .anonymous table
  /-- The tree's copy of `lakefile.toml` lies below it. -/
  copyToml : ¬ OutsideTree tree (tree / "lakefile.toml")
  /-- The tree's `lean-toolchain` too. -/
  copyToolchain : ¬ OutsideTree tree (tree / "lean-toolchain")

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
    (∀ n ∈ root.targets, ClosedModuleName n) ∧
    (∀ m file other, (m, file) ∈ modules → root.resolve m = some other → other = file) ∧
      (∀ m file other, (m, file) ∈ modules → (m, other) ∈ modules → other = file) := by
  simp only [configUnread, List.append_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  refine ⟨fun n hn => ?_, ?_, ?_⟩
  · have := h0 n hn
    exact (closedModuleName_iff n).mp (by simpa using this)
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
    {reals : List (FilePath × FilePath)} {w : Walk} {files : List FileRead} {text : String}
    {held : List String → Option String}
    (hheld : Holds tree text w.sources.reverse held)
    (hp : Prior T dir treeDir project tree text start.configKeys)
    (hsys : SysrootIs T sysroot)
    (hload : (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ T)
    (hmods : DefaultModules T root root.defaultTargets modules)
    (hopen : openPathsOf tree root = [])
    (hreached : ∀ m, m ∈ r.reached ↔ m ∈ w.reached) (hrfiles : r.files = files)
    (hrroots : r.roots = modules.map (·.1)) (hrkeys : r.configKeys = start.configKeys)
    (hinside : Inside r)
    (I : WalkInv T dir treeDir project tree root modules reals (modules.map (·.1)) [] w) (hu : w.unread = [])
    (hfacts : (∀ n ∈ root.targets, ClosedModuleName n) ∧
      (∀ m file other, (m, file) ∈ modules → root.resolve m = some other → other = file) ∧
      (∀ m file other, (m, file) ∈ modules → (m, other) ∈ modules → other = file))
    (hroots : ∀ m path, (m, path) ∈ modules → m ∈ w.reached)
    (hcount : modules.length + sourceImports w.sources ≤ 1000000)
    (hnodup : ((headersOf w.sources.reverse).map (·.1)).Nodup)
    (hexec : ∀ x ∈ w.sources, ∀ i ∈ x.2.imports, (modules.lookup i.module).isSome = true →
      (root.resolve i.module).isSome = true)
    (hcl : ∀ m ∈ w.reached, closedModuleName m = true) (hnm : ∀ m ∈ w.reached, m.getRoot ≠ `Mathlib)
    (hread : ∀ m path, fileOf root modules m = some path → m ∈ w.reached → ¬ OutsideTree tree path ∧
      ∃ f ∈ files, f.module = m ∧ ∃ imports mods text', (headersOf w.sources.reverse).lookup m = some imports ∧
        ReadText T project tree f path imports mods text' ∧ held (parts path) = some text')
    (hsomeFile : ∀ n path', root.resolve n = some path' → fileOf root modules n = some path')
    (hlookup : ∀ x ∈ w.sources, (headersOf w.sources.reverse).lookup x.1 = some x.2.imports)
    (hfileRead : ∀ f ∈ files, ∃ x ∈ w.sources, ∃ path,
      fileOf root modules x.1 = some path ∧ SourceRead T project tree path x.2 ∧
      FileFrom T w.sources.reverse w.toolchain x.1 x.2 f)
    (hstored : ∀ x ∈ w.sources, ∃ f ∈ files, ∃ path imports mods, FileOfModule root modules f.module path ∧
      parts path = parts x.2.path ∧ ReadText T project tree f path imports mods x.2.text) :
    Evidence T dir treeDir held r := by
  obtain ⟨real, table, t1, t2, t3, t4, t5, hk⟩ := hp.toml
  have hkeys := keyPaths_in hinside (hrkeys.trans hk)
  have hnodeep : ¬ Deeper 8 table := by
    intro hd
    obtain ⟨d, hd', hdeep⟩ := keysOf_deep (pre := .anonymous) hd
    obtain ⟨hc, -, hnd, -⟩ := hinside
    have hdr : d ∈ r.configKeys := (hrkeys.trans hk) ▸ hd'
    by_cases hroot : d.getRoot = `require
    · exact hnd ⟨d, hdr, hroot⟩
    · exact deepKey_not_admitted hdeep (hc.2.2.2 d hdr hroot)
  have hdirs : ∀ d ∈ root.sourceDirs, ∃ rel, TreeRelative (parts tree) (parts d) rel := by
    intro d hd
    refine (inTree_iff tree d).mp ?_
    have h0 := hopen
    simp only [openPathsOf, List.append_eq_nil_iff, List.map_eq_nil_iff] at h0
    cases hin : inTree tree d with
    | true => rfl
    | false =>
      have hmem : d ∈ (root.sourceDirs.filter (!inTree tree ·)).eraseDups :=
        List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨hd, by simp [hin]⟩)
      rw [h0.1] at hmem
      cases hmem
  have hglobs : ∀ lib ∈ root.libraries, ∀ g ∈ lib.2, ∃ n, g = .one n := by
    intro lib hl g hg
    have h0 := hopen
    simp only [openPathsOf, List.append_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff, Bool.not_eq_true',
      Bool.not_eq_false, List.all_eq_true] at h0
    have h1 := h0.2 lib hl g hg
    cases g with
    | one n => exact ⟨n, rfl⟩
    | submodules n => cases h1
    | andSubmodules n => cases h1
  refine ⟨project, tree, hp.project_real, hp.tree_real, hp.apart, hp.started, hp.toolchain, hp.absent,
    ⟨text, real, table, t1, t2, t3, t4, t5, hheld.toml, hnodeep, hkeys⟩, hheld.toolchain, hp.copyToml,
    hp.copyToolchain, sysroot, root, log,
    modules, hsys, hload, hmods, hrroots, hdirs, hglobs, hfacts.1, hfacts.2.1, hfacts.2.2, headersOf w.sources.reverse,
    w.toolchain, ?_, hnodup, ?_, fun n hn => (I.held n hn).2.1, ?_, ?_⟩
  · rw [sum_headersOf, List.map_reverse, List.sum_reverse]
    exact hcount
  · intro m path hc
    rw [hrfiles]
    induction hc with
    | root hm => exact hread _ _ (fileOf_of_mem hfacts.2.2 hm) (hroots _ _ hm)
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
    obtain ⟨x, hx, path, hfp, hs, hfrom⟩ := hfileRead f hf
    obtain ⟨-, -, -, -, -, -, hpath, -⟩ := id hs
    have hstands : held (parts path) = some x.2.text := by
      rw [← hpath]
      exact hheld.1 (x.2.path, x.2.text)
        (List.mem_append_right _ (List.mem_map.mpr ⟨x, List.mem_reverse.mpr hx, rfl⟩))
    refine ⟨path, x.2.imports, _, x.2.text, by rw [hfrom.1]; exact fileOf_mem hfp, readText_of hs hfrom, hstands, ?_,
      mem_mods_iff _ _ _, ?_⟩
    · rw [hfrom.1]
      exact hlookup x hx
    · intro i hi
      have hsome := hexec x hx i hi
      rcases I.pending hu x hx i hi with h' | h' | h'
      · cases h'
      · exact ⟨.inl ((hreached _).mpr h'), (closedModuleName_iff _).mp (hcl _ h'), hnm _ h', hsome⟩
      · obtain ⟨hnone, hheld, hc', hr', -⟩ := I.held _ h'
        rw [fileOf] at hnone
        split at hnone
        · cases hnone
        · rename_i hl
          exact ⟨.inr ⟨hnone, hl, hheld⟩, (closedModuleName_iff _).mp hc', hr', hsome⟩
  · intro p v hv
    obtain ⟨x, hx, h1, h2⟩ := hheld.2 p v hv
    rcases List.mem_append.mp hx with hx | hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact .inl h1.symm
      · exact .inr (.inl h1.symm)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨f, hf, path, imports, mods, g1, g2, g3⟩ := hstored y (List.mem_reverse.mp hy)
      rw [hrfiles]
      exact .inr (.inr ⟨f, hf, path, imports, mods, g1, g2.trans h1, h2 ▸ g3⟩)

/-- What the last stage's reading rests on, once every file has its commands. -/
theorem lastStage_goal {T : List (Event L E)} {dir treeDir project tree : FilePath} {root : Root L}
    {modules : List (Name × FilePath)} {start : Reading} {sysroot : String} {log : List String}
    {reals : List (FilePath × FilePath)} {w : Walk} {files : List FileRead} {text : String}
    {config : List (FilePath × String)}
    (hp : Prior T dir treeDir project tree text start.configKeys) (hc : start.configClosed = true)
    (hd : start.requiresDependency = false)
    (hsys : SysrootIs T sysroot)
    (hload : (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ T)
    (hprepared : PreparedLoad T dir treeDir sysroot tree (.ok (some root, log)))
    (hmods : DefaultModules T root root.defaultTargets modules)
    (hopen : openPathsOf tree root = [])
    (hfacts : (∀ n ∈ root.targets, ClosedModuleName n) ∧
      (∀ m file other, (m, file) ∈ modules → root.resolve m = some other → other = file) ∧
      (∀ m file other, (m, file) ∈ modules → (m, other) ∈ modules → other = file))
    (I : WalkInv T dir treeDir project tree root modules reals (modules.map (·.1)) [] w)
    (hu : w.unread = []) (hcount : modules.length + sourceImports w.sources ≤ 1000000)
    (hf : (baseReading config start root modules w).readInFull = true)
    (hm : (baseReading config start root modules w).mathlibReached = false)
    (g1 : ∀ f ∈ files, ∃ x ∈ w.sources.reverse, FileFrom T w.sources.reverse w.toolchain x.1 x.2 f)
    (g2 : ∀ x ∈ w.sources.reverse, ∃ f ∈ files, FileFrom T w.sources.reverse w.toolchain x.1 x.2 f) :
    ReadGoal T dir treeDir (Holds tree text w.sources.reverse) { baseReading config start root modules w with files } := by
  obtain ⟨r, hr⟩ : ∃ r : Reading, r = { baseReading config start root modules w with files } := ⟨_, rfl⟩
  rw [← hr]
  have hrc : r.configClosed = true := by rw [hr]; exact hc
  have hrd : r.requiresDependency = false := by rw [hr]; exact hd
  have hrm : r.mathlibReached = false := by rw [hr]; exact hm
  have hrf : r.readInFull = true := by rw [hr]; exact hf
  have hrfiles : r.files = files := by rw [hr]
  have hscene : Scene T dir treeDir project tree root modules :=
    ⟨hp.project_real, ⟨hp.tree_real, sysroot, log, hsys, hload, hprepared⟩, hmods⟩
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
      rw [fileOf_of_mem hfacts.2.2 hmp] at this
      cases this
  have hsource : ∀ m ∈ w.reached, ∃ s, (m, s) ∈ w.sources := by
    intro m hmr
    rcases I.reached m hmr with h' | h' | h'
    · exact h'
    · exfalso
      have : (baseReading config start root modules w).mathlibReached = true := by
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
  have hread0 : ∀ m s, (m, s) ∈ w.sources → ∃ path, fileOf root modules m = some path ∧ s.path = path ∧
      ¬ OutsideTree tree path ∧ ∃ f ∈ files, f.module = m ∧ ∃ imports mods,
        (headersOf w.sources.reverse).lookup m = some imports ∧ ReadText T project tree f path imports mods s.text := by
    intro m s hs
    obtain ⟨p, h1, h2, -⟩ := I.sources _ hs
    obtain ⟨f, hf', hfrom⟩ := g2 (m, s) (List.mem_reverse.mpr hs)
    obtain ⟨_, _, _, _, hout, _, hpath, _⟩ := id h2
    exact ⟨p, h1, hpath, hout, f, hf', hfrom.1, _, _, hlookup (m, s) hs, readText_of h2 hfrom⟩
  have hread : ∀ {held : List String → Option String}, Holds tree text w.sources.reverse held →
      ∀ m path, fileOf root modules m = some path → m ∈ w.reached → ¬ OutsideTree tree path ∧
      ∃ f ∈ files, f.module = m ∧ ∃ imports mods text', (headersOf w.sources.reverse).lookup m = some imports ∧
        ReadText T project tree f path imports mods text' ∧ held (parts path) = some text' := by
    intro held hheld m path hfile hmr
    obtain ⟨s, hs⟩ := hsource m hmr
    obtain ⟨p, h1, hpath, hout, f, hf', hmod, imports, mods, hl, hrt⟩ := hread0 m s hs
    have hp' : p = path := by
      rw [hfile] at h1
      cases h1
      rfl
    subst hp'
    refine ⟨hout, f, hf', hmod, imports, mods, s.text, hl, hrt, ?_⟩
    rw [← hpath]
    exact hheld.1 (s.path, s.text) (List.mem_append_right _ (List.mem_map.mpr ⟨(m, s), List.mem_reverse.mpr hs, rfl⟩))
  have hstored : ∀ x ∈ w.sources, ∃ f ∈ files, ∃ path imports mods, FileOfModule root modules f.module path ∧
      parts path = parts x.2.path ∧ ReadText T project tree f path imports mods x.2.text := by
    intro x hx
    obtain ⟨p, h1, hpath, -, f, hf', hmod, imports, mods, -, hrt⟩ := hread0 x.1 x.2 hx
    exact ⟨f, hf', p, imports, mods, by rw [hmod]; exact fileOf_mem h1, by rw [hpath], hrt⟩
  have hsomeFile : ∀ n path', root.resolve n = some path' → fileOf root modules n = some path' := by
    intro n path' hres
    rw [fileOf]
    split
    · rename_i q hl
      rw [hfacts.2.1 n q path' (mem_of_lookup hl) hres]
    · exact hres
  by_cases hmod : modules = []
  · have hcov : r.covered = false := by
      simp [Reading.covered, hrroots, hmod]
    have hdec := decision_not_covered hrc hrf hrd hrm hcov
    refine ⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho hne => ?_⟩
    rw [hdec] at ho
    subst ho
    exact .noClaim (hmod ▸ hscene)
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
      refine ⟨fun _ held hheld => ?_, fun o ho hne => absurd (ho.symm.trans hdec) hne⟩
      have hinside := (decision_admitted_iff r).mp hdec
      have hnodupH : ((headersOf w.sources.reverse).map (·.1)).Nodup := by
        simpa [headersOf, Function.comp_def] using hnodup
      have hexec : ∀ x ∈ w.sources, ∀ i ∈ x.2.imports, (modules.lookup i.module).isSome = true →
          (root.resolve i.module).isSome = true := by
        intro x hx i hi hl
        have hf0 := hf
        simp only [Reading.readInFull, baseReading, Bool.and_eq_true, List.isEmpty_iff, List.append_eq_nil_iff,
          importedExecutableRoots, List.map_eq_nil_iff, List.filter_eq_nil_iff] at hf0
        have h1 := hf0.2.1.2 i.module (List.mem_eraseDups.mpr (List.mem_flatMap.mpr
          ⟨x, List.mem_reverse.mpr hx, List.mem_map.mpr ⟨i, Array.mem_toList_iff.mpr hi, rfl⟩⟩))
        simp only [hl, Option.isNone_iff_eq_none] at h1
        cases hres : root.resolve i.module with
        | none => simp [hres] at h1
        | some _ => rfl
      have hnm : ∀ m ∈ w.reached, m.getRoot ≠ `Mathlib := fun m hm' hroot =>
        hinside.2.2.2.1 ⟨m, (hreached m).mpr hm', hroot⟩
      exact lastStage_evidence hheld hp hsys hload hmods hopen hreached hrfiles hrroots hrkeys hinside I hu hfacts hroots hcount
        hnodupH hexec hclosed hnm (hread hheld) hsomeFile hlookup hfileRead hstored
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
      obtain ⟨x, hx, p, h1, h2, hfrom⟩ := hfileRead f hf'
      obtain ⟨-, -, -, hxr⟩ := I.sources x hx
      have hsrc : ∀ m ∈ w.reached, ((headersOf w.sources.reverse).lookup m).isSome = true := by
        intro m hm'
        obtain ⟨s, hs⟩ := hsource m hm'
        rw [hlookup (m, s) hs]
        rfl
      have hclosure : ∀ y ∈ w.sources, ∀ i ∈ y.2.imports, i.module ∈ w.toolchain ∨
          ((headersOf w.sources.reverse).lookup i.module).isSome = true := by
        intro y hy i hi
        rcases I.pending hu y hy i hi with h' | h' | h'
        · cases h'
        · exact .inr (hsrc _ h')
        · exact .inl h'
      refine .file hscene (hfrom.1 ▸ I.named _ hxr) (by rw [hfrom.1]; exact fileOf_mem h1) ⟨_, readText_of h2 hfrom⟩
        (headers := headersOf w.sources.reverse) (held := w.toolchain) ?_ (fun n hn => ⟨(I.held n hn).2.2.2.2, (I.held n hn).2.1⟩)
        (hclosure x hx) ?_ (mem_mods_iff _ _ _) hna
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        obtain ⟨q, q1, q2, -⟩ := I.sources z (List.mem_reverse.mp hz)
        exact headerOf_read q1 q2
      · intro y hy i hi
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        exact hclosure z (List.mem_reverse.mp hz) i hi


/-- What `twoTexts` empty says: no two entries of the plan hold two texts at one path. -/
theorem twoTexts_nil {planned : List (Name × FilePath × String)} (h : twoTexts planned = []) :
    ∀ x ∈ planned, ∀ y ∈ planned, parts x.2.1 = parts y.2.1 → x.2.2 = y.2.2 := by
  intro x hx y hy hp
  simp only [twoTexts, List.map_eq_nil_iff, List.filter_eq_nil_iff] at h
  have h1 := h x hx
  simp only [Bool.not_eq_true, List.any_eq_false, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, not_and, ne_eq, Decidable.not_not] at h1
  exact h1 y hy hp

/-- What `twoTexts` not empty says: two entries of the plan hold two texts at one path. -/
theorem twoTexts_cons {planned : List (Name × FilePath × String)} (h : twoTexts planned ≠ []) :
    ∃ x ∈ planned, ∃ y ∈ planned, parts x.2.1 = parts y.2.1 ∧ x.2.2 ≠ y.2.2 := by
  obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ h
  simp only [twoTexts, List.mem_map, List.mem_filter, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hz
  obtain ⟨x, ⟨hx, y, hy, hp, hne⟩, -⟩ := hz
  exact ⟨x, hx, y, hy, hp, hne⟩

/-- The plan without the names of its entries. -/
theorem plannedOf_map (tree : FilePath) (text : String) (srcs : List (Name × Source)) :
    (plannedOf [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] srcs).map (·.2) =
      planOf tree text srcs := by
  simp [plannedOf, planOf, Function.comp_def]

/-- A trace that acts as the plan, with no two of its entries in disagreement, leaves exactly the plan. -/
theorem holds_of_leavesAs {t : List (Event L E)} {tree : FilePath} {text : String} {srcs : List (Name × Source)}
    (h : LeavesAs t (planOf tree text srcs))
    (hc : twoTexts (plannedOf [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] srcs) = []) :
    Holds tree text srcs (written t) := by
  have hag : ∀ x ∈ planOf tree text srcs, ∀ y ∈ planOf tree text srcs, parts y.1 = parts x.1 → y.2 = x.2 := by
    intro x hx y hy hp
    rw [← plannedOf_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
    exact twoTexts_nil hc y' hy' x' hx' hp
  refine ⟨fun x hx => ?_, fun p v hv => ?_⟩
  · rw [h.written]
    exact writesOf_agree (fun y hy hp => hag x hx y hy hp) (.inr ⟨x, hx, rfl⟩)
  · rw [h.written] at hv
    rcases writesOf_mem hv with he | hm
    · cases he
    · exact hm

/-- A successful write has only successful directory creations before its final write, stated of the
exact trace and not of a subsequence. -/
theorem writeInTree_trace {tree path : FilePath} {text : String} {t : List (Event L E)} {u : Unit}
    (h : Runs (writeInTree tree path text : Attempt L E Unit).run t (.ok u)) :
    ∃ before, t = before ++ [⟨.writeFile path text, .ok ()⟩] ∧
      ∀ e ∈ before, ∃ d, e = (⟨.createDirAll d, .ok ()⟩ : Event L E) := by
  rw [writeInTree] at h
  split at h
  · obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
    cases r with
    | error why => cases h₂.2
    | ok v =>
      obtain ⟨r, hcall, hr⟩ := runs_attempt_iff.mp h₂
      obtain rfl := runs_call_iff.mp hcall
      cases r with
      | error why => cases hr
      | ok v' =>
        cases v'
        refine ⟨t₁, rfl, ?_⟩
        rw [makeParent] at h₁
        split at h₁
        · obtain ⟨rfl, -⟩ := runs_attempt_pure_iff.mp h₁
          simp
        · rename_i d hd
          split at h₁
          · obtain ⟨r, hc, hr⟩ := runs_attempt_iff.mp h₁
            obtain rfl := runs_call_iff.mp hc
            cases r with
            | error why => cases hr
            | ok v' =>
              cases v'
              intro e he
              exact ⟨d, List.mem_singleton.mp he⟩
          · obtain ⟨-, he⟩ := runs_attempt_throw_iff.mp h₁
            cases he
  · obtain ⟨-, he⟩ := runs_attempt_throw_iff.mp h
    cases he

/-- A successful write acts as one write. -/
theorem writeInTree_leaves {tree path : FilePath} {text : String} {t : List (Event L E)} {u : Unit}
    (h : Runs (writeInTree tree path text : Attempt L E Unit).run t (.ok u)) : LeavesAs t [(path, text)] := by
  obtain ⟨before, rfl, hb⟩ := writeInTree_trace h
  exact leavesAs_write hb

/-- `writeSources` for every response: on success it acts as the writes of the sources; a failure names a source and why. -/
theorem writeSources_spec {tree : FilePath} {srcs : List (Name × Source)} {t : List (Event L E)} {b : Except String Unit}
    (h : Runs (writeSources tree srcs : Attempt L E Unit).run t b) :
    (b = .ok () → LeavesAs t (srcs.map fun x => (x.2.path, x.2.text))) ∧
    ((∃ e, b = .error e) → ∃ x ∈ srcs, OutsideTree tree x.2.path ∨ ∃ e ∈ t, Event.failed e ∧
      ((∃ d, x.2.path.parent = some d ∧ e.op = .createDirAll d) ∨ e.op = .writeFile x.2.path x.2.text)) ∧
    ActsIn tree t := by
  induction srcs generalizing t b with
  | nil =>
    rw [writeSources] at h
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h
    exact ⟨fun _ _ _ => rfl, fun ⟨e, he⟩ => (by cases he), actsIn_nil⟩
  | cons x rest ih =>
    obtain ⟨m, s⟩ := x
    rw [writeSources] at h
    obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
    obtain ⟨w1, w2, w3⟩ := writeInTree_spec h₁
    cases r with
    | error why =>
      obtain ⟨rfl, rfl⟩ := h₂
      refine ⟨fun he => (by cases he), fun _ => ?_, by simpa using w3⟩
      rcases w2 ⟨why, rfl⟩ with h' | ⟨e, he, hf, hop⟩
      · exact ⟨(m, s), List.mem_cons_self .., .inl h'⟩
      · exact ⟨(m, s), List.mem_cons_self .., .inr ⟨e, by simpa using he, hf, hop⟩⟩
    | ok u =>
      obtain ⟨i1, i2, i3⟩ := ih h₂
      refine ⟨fun hb => ?_, fun he => ?_, actsIn_append w3 i3⟩
      · have hl := writeInTree_leaves h₁
        exact hl.append (i1 hb)
      · obtain ⟨x, hx, hh⟩ := i2 he
        refine ⟨x, List.mem_cons_of_mem _ hx, ?_⟩
        rcases hh with h' | ⟨e, he', hf, hop⟩
        · exact .inl h'
        · exact .inr ⟨e, List.mem_append_right _ he', hf, hop⟩

/-- A plan's entry is what `Planned` states. -/
theorem planned_of_mem {T : List (Event L E)} {project tree : FilePath} {root : Root L} {modules : List (Name × FilePath)}
    {text : String} {srcs : List (Name × Source)}
    (htoml : (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ T)
    (hsrc : ∀ x ∈ srcs, Named T project tree root modules x.1 ∧ FileOfModule root modules x.1 x.2.path ∧
      SourceText T project tree x.2.path x.2.text)
    {x : FilePath × String} (hx : x ∈ planOf tree text srcs) : Planned T project tree root modules x.1 x.2 := by
  rcases List.mem_append.mp hx with hx | hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact .toml htoml
    · exact .toolchain
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨h1, h2, h3⟩ := hsrc y hy
    exact .source h1 h2 h3

/-- A source's fact, as the plan's entry needs it. -/
theorem source_facts {T : List (Event L E)} {dir treeDir project tree : FilePath} {root : Root L}
    {modules : List (Name × FilePath)} {reals : List (FilePath × FilePath)} {roots todo : List Name} {w : Walk}
    (I : WalkInv T dir treeDir project tree root modules reals roots todo w) :
    ∀ x ∈ w.sources, Named T project tree root modules x.1 ∧ FileOfModule root modules x.1 x.2.path ∧
      SourceText T project tree x.2.path x.2.text := by
  intro x hx
  obtain ⟨p, h1, h2, h3⟩ := I.sources x hx
  obtain ⟨rel, real, text, hrel, -, -, hpath, ht, -, hsub⟩ := h2
  subst hpath
  refine ⟨I.named _ h3, fileOf_mem h1, rel, hrel, ?_⟩
  rw [ht]
  exact hsub.subset (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- The last stage of the reader. On an admission its acts are the writes of the sources, whose plan with `lakefile.toml`
and `lean-toolchain` has no two texts at one path. -/
theorem readFiles_spec {T t : List (Event L E)} {dir treeDir project tree : FilePath} {root : Root L}
    {modules : List (Name × FilePath)} {start : Reading} {sysroot text : String} {log : List String}
    {b : Except String (Reading × List (Name × Source))} (hT : t.Sublist T)
    (hp : Prior T dir treeDir project tree text start.configKeys) (hc : start.configClosed = true)
    (hd : start.requiresDependency = false) (hout : start.outside = true)
    (hsys : SysrootIs T sysroot)
    (hload : (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ T)
    (hprepared : PreparedLoad T dir treeDir sysroot tree (.ok (some root, log)))
    (hmods : DefaultModules T root root.defaultTargets modules)
    (hopen : openPathsOf tree root = [])
    (hunread : configUnread root modules = [])
    (h : Runs (readFiles [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] project tree root modules
      start : Attempt L E _).run t b) :
    (∀ r srcs, b = .ok (r, srcs) → ReadGoal T dir treeDir (Holds tree text srcs) r ∧
      (decision r = .admitted → LeavesAs t (srcs.map fun x => (x.2.path, x.2.text)) ∧
        twoTexts (plannedOf [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] srcs) = [])) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧ ActsIn tree t := by
  rw [readFiles] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨u, h₃, rfl⟩ := runs_lift_iff.mp h₁
  obtain rfl := runs_call_iff.mp h₃
  have hT₂ : t₂.Sublist T := (List.sublist_append_right _ _).trans hT
  have hTL : TreeLoaded T dir treeDir tree root := ⟨hp.tree_real, sysroot, log, hsys, hload, hprepared⟩
  have hscene : Scene T dir treeDir project tree root modules := ⟨hp.project_real, hTL, hmods⟩
  have hact₁ : ActsIn (L := L) (E := E) tree [⟨.setSearchPath root.toolchain, u⟩] := by
    intro e he p hp'
    have : e = ⟨.setSearchPath root.toolchain, u⟩ := by simpa using he
    subst this
    cases hp'
  have hno₁ : ∀ e ∈ ([⟨.setSearchPath root.toolchain, u⟩] : List (Event L E)), e.acted? = none := by
    intro e he
    obtain rfl := List.mem_singleton.mp he
    rfl
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
    obtain ⟨q, hq, x, hx⟩ := d2 ⟨why, rfl⟩
    exact ⟨fun _ _ he => (by cases he), fun _ => .failed (hT₃.subset hx) (.toolchainDir hTL hq) ⟨x, rfl⟩,
      by simpa using actsIn_append hact₁ hact₃⟩
  | ok dirs =>
    obtain ⟨reals, x1, rfl, x3⟩ := d1 dirs rfl
    obtain ⟨t₅, t₆, r₅, rfl, h₆, h₇⟩ := runs_attempt_bind_iff.mp h₅
    have hT₅ : t₅.Sublist T := (List.sublist_append_left _ _).trans hT₄
    have hT₆ : t₆.Sublist T := (List.sublist_append_right _ _).trans hT₄
    obtain ⟨w, h₈, rfl⟩ := runs_lift_iff.mp h₆
    have ctx : WalkCtx T dir treeDir project tree root modules reals :=
      { scene := hscene, dirs_map := x1,
        dirs_real := fun x hx => hT₃.subset (x3 x hx) }
    have hinit : WalkInv T dir treeDir project tree root modules reals (modules.map (·.1)) (modules.map (·.1)) {} :=
      { sources := by simp, held := by simp, nodup := by simp, reached := by simp, closed := by simp,
        named := by simp, todoNamed := fun m hm => .root hm, unread := by simp, pending := by simp,
        rootsIn := fun _ m hm => .inl hm }
    obtain ⟨I, hactWalk, hcount⟩ := walk_spec (roots := modules.map (·.1)) ctx 1000000 (modules.map (·.1)) {} t₅ w
      h₈ hT₅ (by simp) (by simp [sourceImports]) hinit
    have hfacts := configUnread_nil hunread
    have hprefix : ActsIn tree ([⟨.setSearchPath root.toolchain, u⟩] ++ t₃) := actsIn_append hact₁ hact₃
    have hw : ActsIn tree t₅ := hactWalk.actsIn tree
    have hacts : ActsIn tree ([⟨.setSearchPath root.toolchain, u⟩] ++ (t₃ ++ (t₅ ++ []))) := by
      simpa using actsIn_append hprefix hw
    obtain ⟨config, hconfig⟩ : ∃ c : List (FilePath × String),
        c = [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] := ⟨_, rfl⟩
    rw [← hconfig] at h₇
    have hbc : (baseReading config start root modules w).configClosed = true := hc
    have hbd : (baseReading config start root modules w).requiresDependency = false := hd
    have hsrcEv : ∀ x ∈ w.sources, ∃ path, fileOf root modules x.1 = some path ∧
        SourceRead T project tree path x.2 := fun x hx => by
      obtain ⟨p, h1, h2, -⟩ := I.sources x hx
      exact ⟨p, h1, h2⟩
    have hfacts' := source_facts I
    obtain ⟨_, _, _, _, _, htomlRead, _, _⟩ := hp.toml
    dsimp only at h₇
    split at h₇
    · rename_i hcond
      obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₇
      refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), by simpa using hacts⟩
      cases he
      by_cases hf : (baseReading config start root modules w).readInFull = true
      · have hm : (baseReading config start root modules w).mathlibReached = true := by
          simpa [hf] using hcond
        have hdec := decision_mathlib hbc hf hbd hm
        refine ⟨⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho hne => ?_⟩, fun ha => (by rw [hdec] at ha; cases ha)⟩
        rw [hdec] at ho
        subst ho
        obtain ⟨m, hm', hroot⟩ := List.any_eq_true.mp hm
        have hmr : m ∈ w.reached := by simpa [baseReading] using hm'
        exact .mathlib hscene (I.named m hmr) (by simpa using hroot)
      · have hf' : (baseReading config start root modules w).readInFull = false := by simpa using hf
        have hdec := decision_not_full hbc hf'
        refine ⟨⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho hne => ?_⟩, fun ha => (by rw [hdec] at ha; cases ha)⟩
        rw [hdec] at ho
        subst ho
        have hne' : w.unread.reverse ++ importedExecutableRoots root modules w.sources.reverse ++
            twoTexts (plannedOf config w.sources.reverse) ≠ [] := by
          intro hnil
          have : (baseReading config start root modules w).readInFull = true := by
            simp only [Reading.readInFull, baseReading, hout, Bool.true_and, hnil, List.isEmpty_nil]
          simp [this] at hf'
        by_cases hu : w.unread = []
        · by_cases himp : importedExecutableRoots root modules w.sources.reverse = []
          · have htwo : twoTexts (plannedOf config w.sources.reverse) ≠ [] := by
              simpa [hu, himp] using hne'
            obtain ⟨x, hx, y, hy, hxy, hne⟩ := twoTexts_cons htwo
            have hmem {z} (hz : z ∈ plannedOf config w.sources.reverse) : z.2 ∈ planOf tree text w.sources.reverse := by
              rw [← plannedOf_map, ← hconfig]
              exact List.mem_map.mpr ⟨z, hz, rfl⟩
            have hsrc : ∀ z ∈ w.sources.reverse, Named T project tree root modules z.1 ∧
                FileOfModule root modules z.1 z.2.path ∧ SourceText T project tree z.2.path z.2.text :=
              fun z hz => hfacts' z (List.mem_reverse.mp hz)
            exact .twoTexts hscene (planned_of_mem htomlRead hsrc (hmem hx)) (planned_of_mem htomlRead hsrc (hmem hy)) hxy hne
          · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ himp
            simp only [importedExecutableRoots, List.mem_map, List.mem_filter, List.mem_eraseDups,
              List.mem_flatMap, Bool.and_eq_true] at hx
            obtain ⟨m, ⟨⟨y, hy, hmy⟩, hl, hr⟩, -⟩ := hx
            obtain ⟨i, hi, rfl⟩ := hmy
            obtain ⟨p, p1, p2, p3⟩ := I.sources y (List.mem_reverse.mp hy)
            exact .importedRoot hscene (I.named _ p3) (headerOf_read p1 p2) (Array.mem_toList_iff.mp hi) hl (by simpa using hr)
        · exact I.unread hu
    · rename_i hcond
      have hf : (baseReading config start root modules w).readInFull = true := by
        cases hx : (baseReading config start root modules w).readInFull with
        | true => rfl
        | false => exact absurd (by simp [hx]) hcond
      have hm : (baseReading config start root modules w).mathlibReached = false := by
        cases hx : (baseReading config start root modules w).mathlibReached with
        | false => rfl
        | true => exact absurd (by simp [hx]) hcond
      have hnil3 := hf
      simp only [Reading.readInFull, baseReading, hout, Bool.true_and, List.isEmpty_iff,
        List.append_eq_nil_iff, List.reverse_eq_nil_iff] at hnil3
      have hu : w.unread = [] := hnil3.1.1
      have htwo : twoTexts (plannedOf config w.sources.reverse) = [] := hnil3.2
      obtain ⟨t₇, t₈, r₇, rfl, h₉, h₁₀⟩ := runs_attempt_bind_iff.mp h₇
      have hT₇ : t₇.Sublist T := (List.sublist_append_left _ _).trans hT₆
      have hT₈ : t₈.Sublist T := (List.sublist_append_right _ _).trans hT₆
      obtain ⟨p1, p2, p3⟩ := parseFiles_spec w.sources.reverse w.toolchain w.sources.reverse [] hT₇ (by simp) h₉
      have hact₇ : ActsIn tree t₇ := fun e he p hp' => by
        rw [p3 e he] at hp'
        cases hp'
      have hbefore := actsIn_append (actsIn_append hprefix hw) hact₇
      cases r₇ with
      | error why =>
        obtain ⟨rfl, rfl⟩ := h₁₀
        obtain ⟨mods, x, hx, hn⟩ := p2 ⟨why, rfl⟩
        exact ⟨fun _ _ he => (by cases he), fun _ => .failed (hT₇.subset hx)
            (.parser hscene fun n hm => ⟨(I.held n (hn n hm)).2.2.2.2, (I.held n (hn n hm)).2.1⟩) ⟨x, rfl⟩,
          by simpa using hbefore⟩
      | ok files =>
        obtain ⟨g1, g2⟩ := p1 files rfl
        have hgoal := lastStage_goal (config := config) hp hc hd hsys hload hprepared hmods hopen hfacts I hu (hcount hu) hf hm g1 g2
        have hnoacts : ∀ e ∈ ([⟨.setSearchPath root.toolchain, u⟩] ++ t₃ ++ t₅ ++ t₇ : List (Event L E)), e.acted? = none := by
          intro e he
          simp only [List.mem_append] at he
          rcases he with ((he | he) | he) | he
          · exact hno₁ e he
          · exact d3 e he
          · exact hactWalk e he
          · exact p3 e he
        dsimp only at h₁₀
        split at h₁₀
        · rename_i hadm
          obtain ⟨t₉, t₁₀, r₉, rfl, h₁₁, h₁₂⟩ := runs_attempt_bind_iff.mp h₁₀
          obtain ⟨s1, s2, s3⟩ := writeSources_spec h₁₁
          have hT₉ : t₉.Sublist T := (List.sublist_append_left _ _).trans hT₈
          cases r₉ with
          | error why =>
            obtain ⟨rfl, rfl⟩ := h₁₂
            refine ⟨fun _ _ he => (by cases he), fun _ => ?_, by simpa using actsIn_append hbefore s3⟩
            obtain ⟨x, hx, hh⟩ := s2 ⟨why, rfl⟩
            obtain ⟨h1, h2, h3⟩ := hfacts' x (List.mem_reverse.mp hx)
            rcases hh with h' | ⟨e, he, hbad, ⟨d, hd', hop⟩ | hop⟩
            · exact .moduleNotInTree hscene h1 h2 h'
            · exact .failed (hT₉.subset he) (by rw [hop]; exact .sourceParent hscene h1 h2 hd') hbad
            · exact .failed (hT₉.subset he) (by rw [hop]; exact .sourceWrite hscene h1 h2 h3) hbad
          | ok v =>
            obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₁₂
            refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), by simpa using actsIn_append hbefore s3⟩
            cases he
            refine ⟨hgoal, fun _ => ⟨?_, hconfig ▸ htwo⟩⟩
            have hl := (leavesAs_nil_of_no_act hnoacts).append (s1 rfl)
            simpa [List.append_assoc] using hl
        · rename_i hnadm
          obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₁₀
          refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), by simpa using hbefore⟩
          cases he
          exact ⟨hgoal, fun ha => (hnadm ha).elim⟩

/-! ## Lake's load, and the paths it names -/

theorem openPaths_reason {T : List (Event L E)} {dir treeDir tree : FilePath} {root : Root L}
    (hload : TreeLoaded T dir treeDir tree root) (h : openPathsOf tree root ≠ []) : Reason T dir treeDir .refused := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h
  simp only [openPathsOf, List.mem_append, List.mem_map, List.mem_eraseDups, List.mem_filter] at hx
  rcases hx with ⟨d, ⟨hd, hn⟩, -⟩ | ⟨lib, ⟨hl, hn⟩, -⟩
  · refine .openDir hload hd fun rel hr => ?_
    have := (inTree_iff tree d).mpr ⟨rel, hr⟩
    simp [this] at hn
  · have hne : ∃ g ∈ lib.2, ∀ n, g ≠ .one n := by
      simp only [Bool.not_eq_true', List.all_eq_false] at hn
      obtain ⟨g, hg, hs⟩ := hn
      refine ⟨g, hg, fun n he => ?_⟩
      subst he
      simp at hs
    obtain ⟨g, hg, hs⟩ := hne
    exact .openGlob hload hl hg hs

theorem configUnread_reason {T : List (Event L E)} {dir treeDir project tree : FilePath} {root : Root L}
    {modules : List (Name × FilePath)} (hscene : Scene T dir treeDir project tree root modules)
    (h : configUnread root modules ≠ []) : Reason T dir treeDir .incomplete := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h
  simp only [configUnread, List.mem_append, List.mem_map, List.mem_filter] at hx
  rcases hx with (⟨n, ⟨hn, hc⟩, -⟩ | ⟨y, ⟨hy, hr⟩, -⟩) | ⟨y, ⟨hy, hr⟩, -⟩
  · refine .targetName hscene.loaded hn fun hclosed => ?_
    simp [(closedModuleName_iff n).mpr hclosed] at hc
  · cases hres : root.resolve y.1 with
    | none => simp [hres] at hr
    | some other =>
      simp only [hres, bne_iff_ne] at hr
      exact .twoFiles hscene hy hres hr
  · obtain ⟨o, ho, hb⟩ := List.any_eq_true.mp hr
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hb
    obtain ⟨h1, h2⟩ := hb
    exact .twoRoots (m := y.1) (file := y.2) (other := o.2) hscene hy (by rw [← h1]; exact ho) h2

/-- What a stage that has the root package gives. -/
theorem readRoot_spec {T t : List (Event L E)} {dir treeDir project tree : FilePath} {start : Reading}
    {sysroot text : String} {b : Except String (Reading × List (Name × Source))} (hT : t.Sublist T)
    (hsys : SysrootIs T sysroot)
    (hp : Prior T dir treeDir project tree text start.configKeys) (hc : start.configClosed = true)
    (hd : start.requiresDependency = false) (hout : start.outside = true)
    (hprepared : ∀ response rest, t = ⟨.loadRoot sysroot tree, response⟩ :: rest →
      PreparedLoad T dir treeDir sysroot tree response)
    (h : Runs (readRoot [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] sysroot project tree start :
      Attempt L E _).run t b) :
    (∀ r srcs, b = .ok (r, srcs) → ReadGoal T dir treeDir (Holds tree text srcs) r ∧
      (decision r = .admitted → LeavesAs t (srcs.map fun x => (x.2.path, x.2.text)) ∧
        twoTexts (plannedOf [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] srcs) = [])) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧ ActsIn tree t := by
  rw [readRoot] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨t₃, t₄, r₃, rfl, h₃, h₄⟩ := runs_bind_iff.mp h₁
  obtain rfl := runs_call_iff.mp h₃
  obtain ⟨rfl, rfl⟩ := runs_done_iff.mp h₄
  have hT' : (([⟨.loadRoot sysroot tree, r₃⟩] : List (Event L E)) ++ t₂).Sublist T := by simpa using hT
  have hT₁ : ([⟨.loadRoot sysroot tree, r₃⟩] : List (Event L E)).Sublist T :=
    (List.sublist_append_left _ _).trans hT'
  have hT₂ : t₂.Sublist T := (List.sublist_append_right _ _).trans hT
  have hmem₁ : (⟨.loadRoot sysroot tree, r₃⟩ : Event L E) ∈ T := hT₁.subset (by simp)
  have hready := hprepared r₃ t₂ (by simp)
  have hact₁ : ActsIn tree ([⟨.loadRoot sysroot tree, r₃⟩] ++ ([] : List (Event L E))) := by
    intro e he p hp'
    have : e = ⟨.loadRoot sysroot tree, r₃⟩ := by simpa using he
    subst this
    cases hp'
  have hfail : ∀ why, loaded "the configuration" r₃ = .error why → Reason T dir treeDir .incomplete := by
    intro why he
    cases r₃ with
    | error e => exact .load hready (.inl ⟨e, rfl⟩)
    | ok v =>
      obtain ⟨o, log⟩ := v
      cases o with
      | none => exact .load hready (.inr ⟨log, rfl⟩)
      | some root => cases he
  cases hl : loaded "the configuration" r₃ with
  | error why =>
    rw [hl] at h₂
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨fun _ _ he => (by cases he), fun _ => hfail why hl, by simpa using hact₁⟩
  | ok root =>
    rw [hl] at h₂
    have hev : ∃ log, r₃ = .ok (some root, log) := by
      cases r₃ with
      | error e => cases hl
      | ok v =>
        obtain ⟨o, log⟩ := v
        cases o with
        | none => cases hl
        | some root' =>
          cases hl
          exact ⟨log, rfl⟩
    obtain ⟨log, rfl⟩ := hev
    have hTL : TreeLoaded T dir treeDir tree root := ⟨hp.tree_real, sysroot, log, hsys, hmem₁, hready⟩
    dsimp only at h₂
    split at h₂
    · rename_i hopen
      obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂
      refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), by simpa using hact₁⟩
      cases he
      have hne : openPathsOf tree root ≠ [] := by
        intro hnil
        simp [hnil] at hopen
      have hclosed : ({ start with openPaths := openPathsOf tree root } : Reading).configClosed = false := by
        simp [Reading.configClosed, hne]
      have hdec := decision_not_closed hclosed
      refine ⟨⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho hne' => ?_⟩, fun ha => (by rw [hdec] at ha; cases ha)⟩
      rw [hdec] at ho
      subst ho
      exact openPaths_reason hTL hne
    · rename_i hopen
      have hopenNil : openPathsOf tree root = [] := by simpa using hopen
      obtain ⟨t₅, t₆, r₅, rfl, h₅, h₆⟩ := runs_attempt_bind_iff.mp h₂
      have hT₅ : t₅.Sublist T := (List.sublist_append_left _ _).trans hT₂
      have hT₆ : t₆.Sublist T := (List.sublist_append_right _ _).trans hT₂
      obtain ⟨m1, m2⟩ := defaultModules_spec (T := T) root root.defaultTargets hT₅.subset h₅
      have hact₅ : ActsIn tree t₅ := by
        have : ∀ e ∈ t₅, e.acted? = none := defaultModules_no_act h₅
        intro e he p hp'
        rw [this e he] at hp'
        cases hp'
      cases r₅ with
      | error why =>
        obtain ⟨rfl, rfl⟩ := h₆
        obtain ⟨tg, lib, x, hg, hl', hx⟩ := m2 ⟨why, rfl⟩
        exact ⟨fun _ _ he => (by cases he), fun _ => .failed (hT₅.subset hx) (.library hTL hg hl') ⟨x, rfl⟩,
          by simpa using actsIn_append hact₁ hact₅⟩
      | ok modules =>
        have hmods := m1 modules rfl
        dsimp only at h₆
        split at h₆
        · rename_i hfails
          obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₆
          refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he),
            by simpa using actsIn_append hact₁ hact₅⟩
          cases he
          have hne : configUnread root modules ≠ [] := by
            intro hnil
            simp [hnil] at hfails
          have hfull : ({ start with roots := modules.map (·.1), unread := configUnread root modules } : Reading).readInFull = false := by
            simp [Reading.readInFull, hne]
          have hdec := decision_not_full (r := { start with roots := modules.map (·.1), unread := configUnread root modules }) hc hfull
          refine ⟨⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho hne' => ?_⟩, fun ha => (by rw [hdec] at ha; cases ha)⟩
          rw [hdec] at ho
          subst ho
          exact configUnread_reason ⟨hp.project_real, hTL, hmods⟩ hne
        · rename_i hfails
          have hnil : configUnread root modules = [] := by
            simpa using hfails
          obtain ⟨f1, f2, f3⟩ := readFiles_spec hT₆ hp hc hd hout hsys hmem₁ hready hmods hopenNil hnil h₆
          refine ⟨fun r srcs he => ?_, f2, by simpa using actsIn_append (actsIn_append hact₁ hact₅) f3⟩
          obtain ⟨g1, g2⟩ := f1 r srcs he
          refine ⟨g1, fun ha => ?_⟩
          obtain ⟨l1, l2⟩ := g2 ha
          refine ⟨?_, l2⟩
          have hl := (leavesAs_nil_of_no_act (t := ([⟨.loadRoot sysroot tree, .ok (some root, log)⟩] ++ []) ++ t₅) ?_).append l1
          · simpa using hl
          · intro e he'
            simp only [List.append_nil, List.mem_append, List.mem_singleton] at he'
            rcases he' with rfl | he'
            · rfl
            · exact defaultModules_no_act h₅ e he'

/-! ## The configuration -/

/-- What the stages before the configuration established, by the events `T`. -/
structure Early (T : List (Event L E)) (dir treeDir project tree : FilePath) (tf : Option String) : Prop where
  /-- The project's real path. -/
  project_real : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ T
  /-- The tree's real path. -/
  tree_real : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ T
  /-- They lie apart. -/
  apart : Apart project tree
  /-- The start from outside. -/
  started : ∃ sysroot program lakeLib, (⟨.getEnv "LEAN_SYSROOT", some sysroot⟩ : Event L E) ∈ T ∧
    (⟨.lakeInstall sysroot, (program, lakeLib)⟩ : Event L E) ∈ T ∧ StartedOutside T project lakeLib
  /-- What `lean-toolchain` said, when it is the pinned Lean. -/
  toolchain : tf = some leanToolchain → ∃ text real,
    (⟨.readFile (project / "lean-toolchain"), .ok text⟩ : Event L E) ∈ T ∧
    (⟨.realPath (project / "lean-toolchain"), .ok real⟩ : Event L E) ∈ T ∧
    parts real = parts (project / "lean-toolchain") ∧
    parts project <+: parts (project / "lean-toolchain") ∧
    text.trimAscii.toString = leanToolchain
  /-- Why anything else is refused. -/
  toolchain_reason : tf ≠ some leanToolchain → Reason T dir treeDir .refused

/-- A reading that stopped at a stage that has its own reason. -/
theorem stopped_goal {T : List (Event L E)} {dir treeDir : FilePath} {tf : Option String} {why : String}
    {H : (List String → Option String) → Prop}
    (hr : tf ≠ some leanToolchain → Reason T dir treeDir .refused) (hi : Reason T dir treeDir .incomplete) :
    ReadGoal T dir treeDir H (stopped tf false [] (some why)) := by
  by_cases ht : tf = some leanToolchain
  · have hc : (stopped tf false [] (some why)).configClosed = true := by
      subst ht
      simp [stopped, Reading.configClosed]
    have hf : (stopped tf false [] (some why)).readInFull = false := by
      simp [stopped, Reading.readInFull]
    have hdec := decision_not_full hc hf
    refine ⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho _ => ?_⟩
    rw [hdec] at ho
    subst ho
    exact hi
  · have hc : (stopped tf false [] (some why)).configClosed = false := by
      cases htf : tf with
      | none => simp [stopped, Reading.configClosed]
      | some s =>
        have hs : s ≠ leanToolchain := fun h => ht (by rw [htf, h])
        simp [stopped, Reading.configClosed, hs]
    have hdec := decision_not_closed hc
    refine ⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho _ => ?_⟩
    rw [hdec] at ho
    subst ho
    exact hr ht

/-- A reading that stopped with a reason is not admitted. -/
theorem stopped_why_not_admitted {tf : Option String} {why : String} :
    decision (stopped tf false [] (some why)) ≠ .admitted := by
  intro ha
  by_cases ht : (stopped tf false [] (some why)).configClosed = true
  · have hf : (stopped tf false [] (some why)).readInFull = false := by
      simp [stopped, Reading.readInFull]
    rw [decision_not_full ht hf] at ha
    cases ha
  · rw [decision_not_closed (by simpa using ht)] at ha
    cases ha

/-- Copying `lakefile.toml` and `lean-toolchain` to the tree, then what follows. -/
theorem readKeys_spec {T t : List (Event L E)} {dir treeDir project tree : FilePath} {tf : Option String}
    {sysroot text : String} {real : FilePath} {b : Except String (Reading × List (Name × Source))}
    (hI : t <:+: T) (hsys : SysrootIs T sysroot) (hE : Early T dir treeDir project tree tf)
    (habs : ∃ e, (⟨.symlinkMetadata (project / "lakefile.lean"), .error e⟩ : Event L E) ∈ T ∧
      ∃ name code details, e = .noFileOrDirectory name code details)
    (hreal : (⟨.realPath (project / "lakefile.toml"), .ok real⟩ : Event L E) ∈ T)
    (hexact : parts real = parts (project / "lakefile.toml") ∧
      parts project <+: parts (project / "lakefile.toml"))
    (hread : (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ T)
    (h : Runs (readKeys sysroot project tree tf text : Attempt L E _).run t b) :
    (∀ r srcs, b = .ok (r, srcs) → ReadGoal T dir treeDir (Holds tree text srcs) r ∧
      (decision r = .admitted → Holds tree text srcs (written t))) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧ ActsIn tree t := by
  have hT := hI.sublist
  rw [readKeys] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r₂, h₃, rfl⟩ := runs_lift_iff.mp h₁
  obtain rfl := runs_call_iff.mp h₃
  have hT' : (([⟨.parseToml (mkInputContext text "lakefile.toml"), r₂⟩] : List (Event L E)) ++ t₂).Sublist T :=
    by simpa using hT
  have hT₂ : t₂.Sublist T := (List.sublist_append_right _ _).trans hT'
  have hmem : (⟨.parseToml (mkInputContext text "lakefile.toml"), r₂⟩ : Event L E) ∈ T :=
    hT'.subset (by simp)
  have htoml {table} (ht : (⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∈ T) :
      TomlRead T dir table := ⟨project, text, hE.project_real, hread, ht⟩
  have hact₁ : ActsIn tree ([⟨.parseToml (mkInputContext text "lakefile.toml"), r₂⟩] : List (Event L E)) := by
    intro e he p hp'
    have : e = ⟨.parseToml (mkInputContext text "lakefile.toml"), r₂⟩ := by simpa using he
    subst this
    cases hp'
  cases r₂ with
  | error log =>
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂
    refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), by simpa using hact₁⟩
    cases he
    exact ⟨stopped_goal hE.toolchain_reason (.failed hmem (.tomlParse hE.project_real hread) ⟨log, rfl⟩),
      fun ha => absurd ha stopped_why_not_admitted⟩
  | ok table =>
    dsimp only at h₂
    split at h₂
    · rename_i hcond
      obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂
      refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), by simpa using hact₁⟩
      cases he
      by_cases hc : (stopped tf false (keysOf 8 .anonymous table) none).configClosed = true
      · have hd : (stopped tf false (keysOf 8 .anonymous table) none).requiresDependency = true := by
          simpa [hc] using hcond
        have hf : (stopped tf false (keysOf 8 .anonymous table) none).readInFull = true := by
          simp [stopped, Reading.readInFull]
        have hdec := decision_dependency hc hf hd
        refine ⟨⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho _ => ?_⟩, fun ha => (by rw [hdec] at ha; cases ha)⟩
        rw [hdec] at ho
        subst ho
        obtain ⟨k, hk, hroot⟩ := List.any_eq_true.mp hd
        rcases keysOf_sound 8 .anonymous table k hk with h' | h'
        · exact .dependency (htoml hmem) h' (by simpa using hroot)
        · exact .deepDependency (htoml hmem) h'
      · have hc' : (stopped tf false (keysOf 8 .anonymous table) none).configClosed = false := by
          simpa using hc
        have hdec := decision_not_closed hc'
        refine ⟨⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho _ => ?_⟩, fun ha => (by rw [hdec] at ha; cases ha)⟩
        rw [hdec] at ho
        subst ho
        by_cases ht : tf = some leanToolchain
        · have hnot : ¬ ConfigClosed (stopped tf false (keysOf 8 .anonymous table) none) :=
            fun hx => hc ((configClosed_iff _).mpr hx)
          have : ∃ k ∈ keysOf 8 .anonymous table, k.getRoot ≠ `require ∧ ¬ ConfigKeyAdmitted k := by
            refine Classical.byContradiction fun hx => hnot ⟨by simpa [stopped] using ht, rfl, rfl, ?_⟩
            intro k hk hroot
            refine Classical.byContradiction fun hy => hx ⟨k, hk, hroot, hy⟩
          obtain ⟨k, hk, hroot, hna⟩ := this
          rcases keysOf_sound 8 .anonymous table k hk with h' | h'
          · exact .key (htoml hmem) h' hroot hna
          · exact .deep (htoml hmem) h'
        · exact hE.toolchain_reason ht
    · rename_i hcond
      have hc : (stopped tf false (keysOf 8 .anonymous table) none).configClosed = true := by
        cases hx : (stopped tf false (keysOf 8 .anonymous table) none).configClosed with
        | true => rfl
        | false => exact absurd (by simp [hx]) hcond
      have hd : (stopped tf false (keysOf 8 .anonymous table) none).requiresDependency = false := by
        cases hx : (stopped tf false (keysOf 8 .anonymous table) none).requiresDependency with
        | false => rfl
        | true => exact absurd (by simp [hx]) hcond
      obtain ⟨t₃, t₄, r₃, rfl, h₄, h₅⟩ := runs_attempt_bind_iff.mp h₂
      have hT₃ : t₃.Sublist T := (List.sublist_append_left _ _).trans hT₂
      have hT₄ : t₄.Sublist T := (List.sublist_append_right _ _).trans hT₂
      obtain ⟨w1, w2, w3⟩ := writeInTree_spec h₄
      have hwriteFail : ∀ {path text'} {t' : List (Event L E)}, t'.Sublist T →
          (path = tree / "lakefile.toml" ∨ path = tree / "lean-toolchain") →
          (∀ {o : Op L E}, o = .writeFile path text' → Needed T dir treeDir o) →
          (OutsideTree tree path ∨ ∃ e ∈ t', Event.failed e ∧
            ((∃ d, path.parent = some d ∧ e.op = .createDirAll d) ∨ e.op = .writeFile path text')) →
          Reason T dir treeDir .incomplete := by
        intro path text' t' hs hp hw h'
        rcases h' with h' | ⟨e, he, hf, ⟨d, hd, hop⟩ | hop⟩
        · exact .configNotInTree hE.tree_real hp h'
        · exact .failed (hs.subset he) (by rw [hop]; exact .copyParent hE.tree_real hp hd) hf
        · exact .failed (hs.subset he) (hw hop) hf
      cases r₃ with
      | error why =>
        obtain ⟨rfl, rfl⟩ := h₅
        exact ⟨fun _ _ he => (by cases he), fun _ => hwriteFail hT₃ (.inl rfl) (fun ho => by rw [ho]; exact .copyToml hE.project_real hE.tree_real hread) (w2 ⟨why, rfl⟩),
          by simpa using actsIn_append hact₁ w3⟩
      | ok u =>
        obtain ⟨t₅, t₆, r₅, rfl, h₆, h₇⟩ := runs_attempt_bind_iff.mp h₅
        have hT₅ : t₅.Sublist T := (List.sublist_append_left _ _).trans hT₄
        have hT₆ : t₆.Sublist T := (List.sublist_append_right _ _).trans hT₄
        obtain ⟨v1, v2, v3⟩ := writeInTree_spec h₆
        cases r₅ with
        | error why =>
          obtain ⟨rfl, rfl⟩ := h₇
          exact ⟨fun _ _ he => (by cases he), fun _ => hwriteFail hT₅ (.inr rfl) (fun ho => by rw [ho]; exact .copyToolchain hE.tree_real) (v2 ⟨why, rfl⟩),
            by simpa using actsIn_append (actsIn_append hact₁ w3) v3⟩
        | ok v =>
          have hto : tf = some leanToolchain := by
            have := ((configClosed_iff _).mp hc).1
            simpa [stopped] using this
          have hp : Prior T dir treeDir project tree text
              (stopped tf false (keysOf 8 .anonymous table) none).configKeys :=
            { project_real := hE.project_real, tree_real := hE.tree_real, apart := hE.apart,
              started := hE.started, toolchain := hE.toolchain hto, absent := habs,
              toml := ⟨real, table, hreal, hexact.1, hexact.2, hread, hmem, rfl⟩,
              copyToml := (w1 rfl).2, copyToolchain := (v1 rfl).2 }
          have hprepared : ∀ response rest, t₆ = ⟨.loadRoot sysroot tree, response⟩ :: rest →
              PreparedLoad T dir treeDir sysroot tree response := by
            intro response rest ht₆
            obtain ⟨before, hb, -⟩ := writeInTree_trace h₄
            obtain ⟨between, hm, hbetween⟩ := writeInTree_trace h₆
            obtain ⟨toolchain, _, htc, _, _, _, htcText⟩ := hE.toolchain hto
            refine ⟨project, text, toolchain, between, hE.project_real, hE.tree_real, hsys,
              hread, htc, htcText, ?_, hbetween⟩
            apply List.IsInfix.trans _ hI
            refine ⟨[⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩] ++ before, rest, ?_⟩
            simp [hb, hm, ht₆, List.append_assoc]
          obtain ⟨f1, f2, f3⟩ := readRoot_spec hT₆ hsys hp hc hd (by simp [stopped]) hprepared h₇
          refine ⟨fun r srcs he => ?_, f2, by
            simpa using actsIn_append (actsIn_append (actsIn_append hact₁ w3) v3) f3⟩
          obtain ⟨g1, g2⟩ := f1 r srcs he
          refine ⟨g1, fun ha => ?_⟩
          obtain ⟨l1, l2⟩ := g2 ha
          refine holds_of_leavesAs ?_ l2
          have hl0 : LeavesAs (L := L) (E := E) [⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩] [] :=
            leavesAs_nil_of_no_act (fun e he => by obtain rfl := List.mem_singleton.mp he; rfl)
          have hl := (hl0.append (writeInTree_leaves h₄)).append ((writeInTree_leaves h₆).append l1)
          simpa [List.append_assoc] using hl

/-- `existsByName` asks one thing, and only an answer of no such name says that it is absent. -/
theorem existsByName_spec {path : FilePath} {t : List (Event L E)} {b : Except String Bool}
    (h : Runs (existsByName path : Attempt L E Bool).run t b) :
    ∃ r, t = [⟨.symlinkMetadata path, r⟩] ∧
      (b = .ok true → ∃ metadata, r = .ok metadata) ∧
      (b = .ok false → ∃ e, r = .error e ∧ ∃ name code details, e = .noFileOrDirectory name code details) ∧
      ((∃ e, b = .error e) → Event.failed (⟨.symlinkMetadata path, r⟩ : Event L E)) := by
  rw [existsByName] at h
  obtain ⟨t₃, t₄, r₃, rfl, h₃, h₄⟩ := runs_bind_iff.mp h
  obtain rfl := runs_call_iff.mp h₃
  refine ⟨r₃, ?_⟩
  cases r₃ with
  | ok metadata =>
    obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₄
    exact ⟨rfl, fun _ => ⟨metadata, rfl⟩, fun he => (by cases he), fun ⟨e, he⟩ => (by cases he)⟩
  | error e =>
    cases e with
    | noFileOrDirectory name code details =>
      obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₄
      exact ⟨rfl, fun he => (by cases he), fun _ => ⟨_, rfl, name, code, details, rfl⟩,
        fun ⟨e, he⟩ => (by cases he)⟩
    | _ =>
      obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₄
      exact ⟨rfl, fun he => (by cases he), fun he => (by cases he),
        fun _ => ⟨_, rfl, fun _ _ _ he => (by cases he)⟩⟩

/-- `lakefile.lean` by its name, `lakefile.toml`, and what follows. -/
theorem readConfig_spec {T t : List (Event L E)} {dir treeDir project tree : FilePath} {tf : Option String}
    {sysroot : String} {b : Except String (Reading × List (Name × Source))} (hI : t <:+: T)
    (hsys : SysrootIs T sysroot) (hE : Early T dir treeDir project tree tf)
    (h : Runs (readConfig sysroot project tree tf : Attempt L E _).run t b) :
    (∀ r srcs, b = .ok (r, srcs) → ∃ text, ReadGoal T dir treeDir (Holds tree text srcs) r ∧
      (decision r = .admitted → Holds tree text srcs (written t))) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧ ActsIn tree t := by
  have hT := hI.sublist
  rw [readConfig] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r₃, rfl, e1, e2, e3⟩ := existsByName_spec h₁
  have hT' : (([⟨.symlinkMetadata (project / "lakefile.lean"), r₃⟩] : List (Event L E)) ++ t₂).Sublist T := hT
  have hmem : (⟨.symlinkMetadata (project / "lakefile.lean"), r₃⟩ : Event L E) ∈ T :=
    hT'.subset (by simp)
  have hT₂ : t₂.Sublist T := (List.sublist_append_right _ _).trans hT'
  have hact : ActsIn tree ([⟨.symlinkMetadata (project / "lakefile.lean"), r₃⟩] : List (Event L E)) := by
    intro e he p hp'
    have : e = ⟨.symlinkMetadata (project / "lakefile.lean"), r₃⟩ := by simpa using he
    subst this
    cases hp'
  cases r₁ with
  | error why =>
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨fun _ _ he => (by cases he), fun _ => .failed hmem (.leanConfig hE.project_real) (e3 ⟨why, rfl⟩), by simpa using hact⟩
  | ok present =>
    cases present with
    | true =>
      obtain ⟨metadata, rfl⟩ := e1 rfl
      obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂
      refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), by simpa using hact⟩
      cases he
      have hc : (stopped tf true [] none).configClosed = false := by
        simp [stopped, Reading.configClosed]
      have hdec := decision_not_closed hc
      refine ⟨"", ⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho _ => ?_⟩, fun ha => (by rw [hdec] at ha; cases ha)⟩
      rw [hdec] at ho
      subst ho
      exact .leanConfig hE.project_real hmem
    | false =>
      obtain ⟨e, rfl, habs⟩ := e2 rfl
      obtain ⟨t₃, t₄, r₃', rfl, h₃, h₄⟩ := runs_attempt_bind_iff.mp h₂
      obtain ⟨r₅, h₅, rfl⟩ := runs_lift_iff.mp h₃
      obtain ⟨x1, x2, x3⟩ := readExact_spec h₅
      have hT₃ : t₃.Sublist T := (List.sublist_append_left _ _).trans hT₂
      have hT₄ : t₄.Sublist T := (List.sublist_append_right _ _).trans hT₂
      have hact₃ : ActsIn tree t₃ := fun x hx p hp' => by
        rw [x3 x hx] at hp'
        cases hp'
      cases r₅ with
      | error why =>
        obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₄
        refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he),
          by simpa using actsIn_append hact hact₃⟩
        cases he
        refine ⟨"", stopped_goal hE.toolchain_reason ?_, fun ha => absurd ha stopped_why_not_admitted⟩
        rcases x2 ⟨why, rfl⟩ with ⟨y, hy, hf, hop | hop⟩ | ⟨real, rfl, hb⟩
        · exact .failed (hT₃.subset hy) (by rw [hop]; exact .tomlReal hE.project_real) hf
        · exact .failed (hT₃.subset hy) (by rw [hop]; exact .tomlRead hE.project_real) hf
        · exact .tomlNotExact hE.project_real (hT₃.subset (by simp)) hb
      | ok text =>
        obtain ⟨real, rfl, hb⟩ := x1 text rfl
        have hex := (RegulaSpecification.Loader.exactBelow_iff _ _ _).mp hb
        have hI₄ : t₄ <:+: T :=
          (List.infix_append_right.trans List.infix_append_right).trans hI
        obtain ⟨f1, f2, f3⟩ := readKeys_spec hI₄ hsys hE ⟨e, hmem, habs⟩ (hT₃.subset (by simp)) hex
          (hT₃.subset (by simp)) h₄
        refine ⟨fun r srcs he => ?_, f2, by simpa using actsIn_append (actsIn_append hact hact₃) f3⟩
        obtain ⟨g1, g2⟩ := f1 r srcs he
        refine ⟨text, g1, fun ha => ?_⟩
        have hh := g2 ha
        have hno : ∀ x ∈ ([⟨.symlinkMetadata (project / "lakefile.lean"), .error e⟩,
            ⟨.realPath (project / "lakefile.toml"), .ok real⟩, ⟨.readFile (project / "lakefile.toml"), .ok text⟩] :
              List (Event L E)), x.acted? = none := by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl <;> rfl
        refine Holds.congr (fun p => ?_) hh
        have := written_after_no_acts (b := t₄) hno p
        simpa [List.append_assoc] using this

/-! ## The start, and the whole reader -/

/-- `startedOutside` passes only on what `StartedOutside` states. -/
theorem startedOutside_spec {T t : List (Event L E)} {dir treeDir : FilePath} {project lakeLib : FilePath}
    {sysroot : String} {program : FilePath} {b : Except String Bool} (hT : t.Sublist T)
    (hproject : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ T) (hsys : SysrootIs T sysroot)
    (hlake : (⟨.lakeInstall sysroot, (program, lakeLib)⟩ : Event L E) ∈ T)
    (h : Runs (startedOutside lakeLib project : Attempt L E Bool).run t b) :
    (b = .ok true → StartedOutside T project lakeLib) ∧
      (b = .ok false → Reason T dir treeDir .incomplete) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧
      ∀ e ∈ t, e.acted? = none := by
  rw [startedOutside] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r₃, h₃, rfl⟩ := runs_attempt_iff.mp h₁
  obtain rfl := runs_call_iff.mp h₃
  cases r₃ with
  | error e =>
    obtain ⟨rfl, rfl⟩ := h₂
    refine ⟨fun he => (by cases he), fun he => (by cases he),
      fun _ => .failed (hT.subset (by simp) : (⟨.appPath, .error e⟩ : Event L E) ∈ T) .app ⟨e, rfl⟩, ?_⟩
    intro x hx
    simp only [List.append_nil, List.mem_singleton] at hx
    subst hx
    rfl
  | ok app =>
    obtain ⟨t₃, t₄, r₄, rfl, h₄, h₅⟩ := runs_attempt_bind_iff.mp h₂
    obtain ⟨r₅, h₆, rfl⟩ := runs_attempt_iff.mp h₄
    obtain rfl := runs_call_iff.mp h₆
    cases r₅ with
    | error e =>
      obtain ⟨rfl, rfl⟩ := h₅
      refine ⟨fun he => (by cases he), fun he => (by cases he),
        fun _ => .failed (hT.subset (by simp) : (⟨.realPath app, .error e⟩ : Event L E) ∈ T)
          (.appReal (hT.subset (by simp))) ⟨e, rfl⟩, ?_⟩
      intro x hx
      simp only [List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | rfl <;> rfl
    | ok real =>
      obtain ⟨t₅, t₆, r₆, rfl, h₇, h₈⟩ := runs_attempt_bind_iff.mp h₅
      obtain ⟨t₇, t₈, r₈, rfl, h₉, h₁₀⟩ := runs_bind_iff.mp h₇
      obtain rfl := runs_call_iff.mp h₉
      cases r₈ with
      | none =>
        obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₁₀
        obtain ⟨rfl, rfl⟩ := h₈
        refine ⟨fun he => (by cases he), fun he => (by cases he),
          fun _ => .failed (hT.subset (by simp) : (⟨.getEnv "LEAN_PATH", none⟩ : Event L E) ∈ T) .searchPath rfl, ?_⟩
        intro x hx
        simp only [List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | rfl | rfl <;> rfl
      | some received =>
        obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₁₀
        obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₈
        have happ : (⟨.appPath, .ok app⟩ : Event L E) ∈ T := hT.subset (by simp)
        have hreal : (⟨.realPath app, .ok real⟩ : Event L E) ∈ T := hT.subset (by simp)
        have henv : (⟨.getEnv "LEAN_PATH", some received⟩ : Event L E) ∈ T := hT.subset (by simp)
        have hacts : ∀ e ∈ ([⟨.appPath, .ok app⟩] ++ [] ++ ([⟨.realPath app, .ok real⟩] ++ [] ++
            ([⟨.getEnv "LEAN_PATH", some received⟩] ++ [] ++ [])) : List (Event L E)), e.acted? = none := by
          intro x hx
          simp only [List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hx
          rcases hx with rfl | rfl | rfl <;> rfl
        refine ⟨fun he => ?_, fun he => ?_, fun ⟨e, he⟩ => (by cases he), hacts⟩
        · have he' := Except.ok.inj he
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at he'
          obtain ⟨hb, hd⟩ := he'
          cases hown : (real.parent.bind (·.parent)).map (· / "lib" / "lean") with
          | none => simp [hown] at hd
          | some own =>
            simp only [hown, Option.any_some] at hd
            exact ⟨app, real, own, received, happ, hreal, henv, hown, hb, hd⟩
        · have he' := Except.ok.inj he
          simp only [Bool.and_eq_false_iff, Bool.not_eq_false'] at he'
          refine .started hproject hsys hlake happ hreal henv ?_
          rcases he' with hb | hd
          · exact .inl hb
          · refine .inr fun own hown => ?_
            rw [hown] at hd
            simpa using hd

/-- How `readExact` fails, by its events. -/
theorem readExact_error {project path : FilePath} {t : List (Event L E)} {why : String}
    (h : Runs (readExact project path : Attempt L E String).run t (.error why)) :
    (∃ e, t = [⟨.realPath path, .error e⟩]) ∨
      (∃ real, t = [⟨.realPath path, .ok real⟩] ∧ Regula.Load.exactBelow project path real = false) ∨
      ∃ real e, t = [⟨.realPath path, .ok real⟩, ⟨.readFile path, .error e⟩] := by
  rw [readExact] at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r', h₃, rfl⟩ := runs_attempt_iff.mp h₁
  obtain rfl := runs_call_iff.mp h₃
  cases r' with
  | error e =>
    obtain ⟨rfl, -⟩ := h₂
    exact .inl ⟨e, rfl⟩
  | ok real =>
    dsimp only [Except.mapError] at h₂
    split at h₂
    · obtain ⟨r'', h₄, he⟩ := runs_attempt_iff.mp h₂
      obtain rfl := runs_call_iff.mp h₄
      cases r'' with
      | ok text => cases he
      | error e => exact .inr (.inr ⟨real, e, rfl⟩)
    · rename_i hb
      obtain ⟨rfl, -⟩ := runs_attempt_throw_iff.mp h₂
      exact .inr (.inl ⟨real, rfl, by simpa using hb⟩)

/-- What `toolchainOf` gives: what the file says, through the exact-path test, or none with why. -/
theorem toolchainOf_spec {T t : List (Event L E)} {dir treeDir project : FilePath} {tf : Option String}
    (hT : t.Sublist T) (hproject : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ T)
    (h : Runs (toolchainOf project : Prog L E (Option String)) t tf) :
    (tf = some leanToolchain → ∃ text real,
      (⟨.readFile (project / "lean-toolchain"), .ok text⟩ : Event L E) ∈ T ∧
      (⟨.realPath (project / "lean-toolchain"), .ok real⟩ : Event L E) ∈ T ∧
      parts real = parts (project / "lean-toolchain") ∧
      parts project <+: parts (project / "lean-toolchain") ∧
      text.trimAscii.toString = leanToolchain) ∧
    (tf ≠ some leanToolchain → Reason T dir treeDir .refused) ∧
    ∀ e ∈ t, e.acted? = none := by
  rw [toolchainOf] at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  obtain ⟨x1, x2, x3⟩ := readExact_spec h₁
  have hT₁ : t₁.Sublist T := (List.sublist_append_left _ _).trans hT
  cases r with
  | ok text =>
    obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₂
    obtain ⟨real, rfl, hb⟩ := x1 text rfl
    have hex := (RegulaSpecification.Loader.exactBelow_iff _ _ _).mp hb
    refine ⟨fun he => ⟨text, real, hT₁.subset (by simp), hT₁.subset (by simp), hex.1, hex.2, ?_⟩,
      fun hne => ?_, by simpa using x3⟩
    · simpa using he
    · exact .toolchain (text := text) hproject (hT₁.subset (by simp)) (fun heq => hne (by rw [heq]))
  | error why =>
    obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₂
    refine ⟨fun he => (by cases he), fun _ => ?_, by simpa using x3⟩
    rcases readExact_error h₁ with ⟨e, rfl⟩ | ⟨real, rfl, hb⟩ | ⟨real, e, rfl⟩
    · exact .toolchainNoReal (e := e) hproject (hT₁.subset (by simp))
    · exact .toolchainNotExact hproject (hT₁.subset (by simp)) hb
    · exact .toolchainFailed (e := e) hproject (hT₁.subset (by simp))

/-- `apart` is `Apart`. -/
theorem apart_iff (a b : FilePath) : apart a b = true ↔ Apart a b := by
  have hp (x y : List String) : x.isPrefixOf y = false ↔ ¬ x <+: y := by
    constructor
    · intro h hprefix
      have := List.isPrefixOf_iff_prefix.mpr hprefix
      simp [h] at this
    · intro h
      cases hx : x.isPrefixOf y with
      | false => rfl
      | true => exact absurd (List.isPrefixOf_iff_prefix.mp hx) h
  simp [apart, Apart, hp]

/-- What the acts of a read are: none, or all in a tree that lies apart from the project. -/
def ReadActs (t : List (Event L E)) (dir treeDir : FilePath) : Prop :=
  (∀ e ∈ t, e.acted? = none) ∨
    ∃ project tree, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t ∧
      (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t ∧ Apart project tree ∧ ActsIn tree t

/-- The theorem of the reader, for every response. -/
theorem readProject_spec {T t : List (Event L E)} {dir treeDir : FilePath} {sysroot : String}
    {b : Except String (Reading × List (Name × Source))} (hI : t <:+: T) (hsys : SysrootIs T sysroot)
    (h : Runs (readProject sysroot dir treeDir : Attempt L E _).run t b) :
    (∀ r srcs, b = .ok (r, srcs) → ∃ tree text, ReadGoal T dir treeDir (Holds tree text srcs) r ∧
      (decision r = .admitted → Holds tree text srcs (written t))) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧ ReadActs t dir treeDir := by
  have hT := hI.sublist
  rw [readProject] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r₃, h₃, rfl⟩ := runs_attempt_iff.mp h₁
  obtain rfl := runs_call_iff.mp h₃
  cases r₃ with
  | error e =>
    obtain ⟨rfl, rfl⟩ := h₂
    refine ⟨fun _ _ he => (by cases he), fun _ => .failed (e := ⟨.realPath dir, .error e⟩) (hT.subset (by simp)) .project ⟨e, rfl⟩,
      .inl fun x hx => ?_⟩
    simp only [List.append_nil, List.mem_singleton] at hx
    subst hx
    rfl
  | ok project =>
    obtain ⟨t₃, t₄, r₄, rfl, h₄, h₅⟩ := runs_attempt_bind_iff.mp h₂
    obtain ⟨r₅, h₆, rfl⟩ := runs_attempt_iff.mp h₄
    obtain rfl := runs_call_iff.mp h₆
    cases r₅ with
    | error e =>
      obtain ⟨rfl, rfl⟩ := h₅
      refine ⟨fun _ _ he => (by cases he), fun _ =>
        .failed (e := ⟨.realPath treeDir, .error e⟩) (hT.subset (by simp)) .tree ⟨e, rfl⟩, .inl fun x hx => ?_⟩
      simp only [List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | rfl <;> rfl
    | ok tree =>
      obtain ⟨t₅, t₆, r₆, rfl, h₇, h₈⟩ := runs_attempt_bind_iff.mp h₅
      obtain ⟨r₇, h₉, rfl⟩ := runs_lift_iff.mp h₇
      obtain rfl := runs_call_iff.mp h₉
      obtain ⟨program, lakeLib⟩ := r₇
      dsimp only at h₈
      obtain ⟨t₇, t₈, r₈, rfl, h₁₀, h₁₁⟩ := runs_attempt_bind_iff.mp h₈
      -- The events so far, and those to come, are all of `T`.
      generalize hZ : ([⟨.realPath dir, .ok project⟩] ++ ([⟨.realPath treeDir, .ok tree⟩] ++
        ([⟨.lakeInstall sysroot, (program, lakeLib)⟩] ++ (t₇ ++ t₈))) : List (Event L E)) = Z at hT ⊢
      have hsub₇ : t₇.Sublist T := by
        refine List.Sublist.trans ?_ hT
        rw [← hZ]
        simp only [List.cons_append, List.nil_append]
        exact ((List.sublist_append_left _ _).trans (List.sublist_cons_self _ _)).trans
          ((List.sublist_cons_self _ _).trans (List.sublist_cons_self _ _))
      have hsub₈ : t₈.Sublist T := by
        refine List.Sublist.trans ?_ hT
        rw [← hZ]
        simp only [List.cons_append, List.nil_append]
        exact ((List.sublist_append_right _ _).trans (List.sublist_cons_self _ _)).trans
          ((List.sublist_cons_self _ _).trans (List.sublist_cons_self _ _))
      have hprojectZ : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ Z := by simp [← hZ]
      have htreeZ : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ Z := by simp [← hZ]
      have hproject : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ T := hT.subset hprojectZ
      have htree : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ T := hT.subset htreeZ
      have hlake : (⟨.lakeInstall sysroot, (program, lakeLib)⟩ : Event L E) ∈ T :=
        hT.subset (by simp [← hZ])
      obtain ⟨o1, o2, o3, o4⟩ := startedOutside_spec hsub₇ hproject hsys hlake h₁₀
      cases r₈ with
      | error why =>
        obtain ⟨rfl, rfl⟩ := h₁₁
        refine ⟨fun _ _ he => (by cases he), fun _ => o3 ⟨why, rfl⟩, .inl fun x hx => ?_⟩
        rw [← hZ] at hx
        simp only [List.append_nil, List.cons_append, List.nil_append, List.mem_cons] at hx
        rcases hx with rfl | rfl | rfl | hx
        · rfl
        · rfl
        · rfl
        · exact o4 x hx
      | ok outside =>
        obtain ⟨t₉, t₁₀, r₁₀, rfl, h₁₂, h₁₃⟩ := runs_attempt_bind_iff.mp h₁₁
        obtain ⟨tf, h₁₄, rfl⟩ := runs_lift_iff.mp h₁₂
        dsimp only at h₁₃
        have hsub₉ : t₉.Sublist T := ((List.sublist_append_left _ _).trans hsub₈)
        have hsub₁₀ : t₁₀.Sublist T := ((List.sublist_append_right _ _).trans hsub₈)
        obtain ⟨u1, u2, u3⟩ := toolchainOf_spec hsub₉ hproject h₁₄
        have hquiet : ∀ x ∈ Z, x ∈ t₁₀ ∨ x.acted? = none := by
          intro x hx
          rw [← hZ] at hx
          simp only [List.cons_append, List.nil_append, List.mem_cons,
            List.mem_append] at hx
          rcases hx with rfl | rfl | rfl | hx | hx | hx
          · exact .inr rfl
          · exact .inr rfl
          · exact .inr rfl
          · exact .inr (o4 x hx)
          · exact .inr (u3 x hx)
          · exact .inl hx
        split at h₁₃
        · rename_i hout
          obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₁₃
          have houtside : outside = false := by simpa using hout
          subst houtside
          refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), .inl fun x hx => ?_⟩
          · cases he
            by_cases ht : tf = some leanToolchain
            · have hc : ({ stopped tf false [] none with outside := false } : Reading).configClosed = true := by
                subst ht
                simp [stopped, Reading.configClosed]
              have hf : ({ stopped tf false [] none with outside := false } : Reading).readInFull = false := by
                simp [Reading.readInFull]
              have hdec := decision_not_full hc hf
              refine ⟨treeDir, "", ⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho _ => ?_⟩, fun ha => (by rw [hdec] at ha; cases ha)⟩
              rw [hdec] at ho
              subst ho
              exact o2 rfl
            · have hc : ({ stopped tf false [] none with outside := false } : Reading).configClosed = false := by
                cases htf : tf with
                | none => simp [stopped, Reading.configClosed]
                | some s =>
                  have hs : s ≠ leanToolchain := fun h' => ht (by rw [htf, h'])
                  simp [stopped, Reading.configClosed, hs]
              have hdec := decision_not_closed hc
              refine ⟨treeDir, "", ⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho _ => ?_⟩, fun ha => (by rw [hdec] at ha; cases ha)⟩
              rw [hdec] at ho
              subst ho
              exact u2 ht
          · rcases hquiet x hx with h' | h'
            · cases h'
            · exact h'
        · rename_i hout
          have houtside : outside = true := by simpa using hout
          subst houtside
          have hstart := o1 rfl
          rw [ite_eq_right (by simp)] at h₁₃
          split at h₁₃
          · rename_i hnotApart
            obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₁₃
            refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), .inl fun x hx => ?_⟩
            · cases he
              refine ⟨treeDir, "", stopped_goal u2 (.notApart hproject htree fun ha => ?_), fun ha => absurd ha stopped_why_not_admitted⟩
              simp [(apart_iff _ _).mpr ha] at hnotApart
            · rcases hquiet x hx with h' | h'
              · cases h'
              · exact h'
          · rename_i hisApart
            have hap : Apart project tree := (apart_iff _ _).mp (by simpa using hisApart)
            have hE : Early T dir treeDir project tree tf :=
              { project_real := hproject, tree_real := htree, apart := hap,
                started := ⟨sysroot, program, lakeLib, hsys, hlake, hstart⟩, toolchain := u1,
                toolchain_reason := u2 }
            have hI₁₀ : t₁₀ <:+: T := by
              apply List.IsInfix.trans _ hI
              exact List.infix_append_right.trans (List.infix_append_right.trans
                (List.infix_append_right.trans (List.infix_append_right.trans List.infix_append_right)))
            obtain ⟨f1, f2, f3⟩ := readConfig_spec hI₁₀ hsys hE h₁₃
            refine ⟨fun r srcs he => ?_, f2, .inr ⟨project, tree, hprojectZ, htreeZ, hap, fun x hx p hp' => ?_⟩⟩
            · obtain ⟨text, g1, g2⟩ := f1 r srcs he
              refine ⟨tree, text, g1, fun ha => ?_⟩
              have hno : ∀ x ∈ ([⟨.realPath dir, .ok project⟩, ⟨.realPath treeDir, .ok tree⟩,
                  ⟨.lakeInstall sysroot, (program, lakeLib)⟩] ++ t₇ ++ t₉ : List (Event L E)), x.acted? = none := by
                intro x hx
                simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with ((rfl | rfl | rfl) | hx) | hx
                · rfl
                · rfl
                · rfl
                · exact o4 x hx
                · exact u3 x hx
              refine Holds.congr (fun p => ?_) (g2 ha)
              rw [← hZ]
              have := written_after_no_acts (b := t₁₀) hno p
              simpa [List.append_assoc] using this
            · rcases hquiet x hx with h' | h'
              · exact f3 x h' p hp'
              · rw [h'] at hp'
                cases hp'

/-- What a whole read rests on, by the events `T`, for a state of the tree that is what `t` leaves. -/
def ReadDone (T t : List (Event L E)) (dir treeDir : FilePath) (r : Reading) : Prop :=
  (decision r = .admitted → ∀ held : List String → Option String, (∀ p, held p = written t p) →
    Evidence T dir treeDir held r) ∧ ∀ o, decision r = o → o ≠ .admitted → Reason T dir treeDir o

/-- The reader, with the lines that report what it read. -/
theorem read_spec {T t : List (Event L E)} {dir treeDir : FilePath} {sysroot : String}
    {b : Except String (Reading × List String)} (hI : t <:+: T) (hsys : SysrootIs T sysroot)
    (h : Runs (read sysroot dir treeDir : Attempt L E _).run t b) :
    (∀ r lines, b = .ok (r, lines) → ReadDone T t dir treeDir r) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧ ReadActs t dir treeDir := by
  have hT := hI.sublist
  unfold Regula.Reader.read at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨p1, p2, p3'⟩ := readProject_spec (T := T) (List.infix_append_left.trans hI) hsys h₁
  have p3 := p3'
  cases r₁ with
  | error why =>
    obtain ⟨rfl, rfl⟩ := h₂
    simp only [List.append_nil] at hT ⊢
    exact ⟨fun _ _ he => (by cases he), fun _ => p2 ⟨why, rfl⟩, p3⟩
  | ok x =>
    obtain ⟨r, srcs⟩ := x
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂
    simp only [List.append_nil] at hT ⊢
    refine ⟨fun r' lines he => ?_, fun ⟨e, he⟩ => (by cases he), p3⟩
    cases he
    obtain ⟨tree, text, g1, g2⟩ := p1 r srcs rfl
    refine ⟨fun ha held hheld => g1.1 ha held ?_, g1.2⟩
    have heq : held = written t₁ := funext hheld
    rw [heq]
    exact g2 ha

end RegulaSpecification.Effects
