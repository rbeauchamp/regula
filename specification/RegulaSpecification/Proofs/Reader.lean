/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Load
import RegulaSpecification.Proofs.ReaderFiles
import RegulaSpecification.Proofs.Standing

/-!
# What the reader gives

`readProject_spec` is the theorem the reader exists for, for every response: a reading the check admits rests on
`Evidence` of each state of the tree that holds what the plan of the reading says (`Holds`), and the state that the
reader's own acts leave is one (`holds_of_leavesAs`), so every file `Compiled` names is read and the text judged is the text
that stands (that `Compiled` is what Lake compiles is the hypothesis `LakeBehaviour`); any other outcome rests on a `Reason`, so a project with no such reason is admitted; an admission received no failed answer; and its acts meet the grammar `ReadingPreparation`, which places every act in the
tree (`ReadingPreparation.readActs`). Each stage states this once.
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

/-! ## From a source and its file to what the record states -/

theorem readText_of {T : List (Event L E)} {root : Root L} {project tree path : FilePath} {s : Source} {f : FileRead}
    {sources : List (Name × Source)} {toolchain : List Name} {m : Name}
    (hs : SourceRead T project tree path s) (hf : FileFrom T root sources toolchain m s f) :
    ReadText T root project tree f path s.imports
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

/-- A reading depends on a path by its components alone, the name of its parser input included. -/
theorem ReadText.respell {t : List (Event L E)} {root : Root L} {project tree : FilePath} {f : FileRead} {path path' : FilePath}
    {imports : Array Lean.Import} {mods : List Name} {text : String} (hp : parts path = parts path')
    (h : ReadText t root project tree f path imports mods text) : ReadText t root project tree f path' imports mods text := by
  have hn : inputNameOf path = inputNameOf path' := congrArg ("/".intercalate ·) hp
  obtain ⟨rel, real, s, m, fin, env, cmds, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  rw [hp] at h1
  rw [hn] at h4 h6
  exact ⟨rel, real, s, m, fin, env, cmds, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- What `configUnread` empty says, as a statement of its own: each target's name is closed, each module has one file by components,
and each spelling of it lies below the tree. -/
structure ConfigFacts (tree : FilePath) (root : Root L) (modules : List (Name × FilePath)) : Prop where
  /-- Each target's name. -/
  names : ∀ n ∈ root.targets, ClosedModuleName n
  /-- What Lake's resolution gives for a root's name has the components of the root's file. -/
  found : ∀ m file, (m, file) ∈ modules → ∃ other, root.resolve m = some other ∧ parts other = parts file
  /-- Each spelling, by the tests that the reader's writes ask. -/
  placed : ∀ m file path, (m, file) ∈ modules → (path = file ∨ root.resolve m = some path) →
    inTree tree path = true ∧ parentInTree tree path = true

/-- Two entries of one name have one list of components, because resolution gives a name one file. -/
theorem ConfigFacts.two {tree : FilePath} {root : Root L} {modules : List (Name × FilePath)}
    (h : ConfigFacts tree root modules) (m : Name) (file other : FilePath) (hm : (m, file) ∈ modules)
    (ho : (m, other) ∈ modules) : parts other = parts file := by
  obtain ⟨g, hg, hp⟩ := h.found m file hm
  obtain ⟨g', hg', hp'⟩ := h.found m other ho
  rw [hg] at hg'
  cases hg'
  exact hp'.symm.trans hp

/-- What `configUnread` empty says: each default root is its name's one file, also by Lake's import resolution. -/
theorem configUnread_nil {tree : FilePath} {root : Root L} {modules : List (Name × FilePath)}
    (h : configUnread tree root modules = []) : ConfigFacts tree root modules := by
  simp only [configUnread, List.append_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff] at h
  obtain ⟨⟨h0, h1⟩, h3⟩ := h
  refine ⟨fun n hn => ?_, ?_, ?_⟩
  · have := h0 n hn
    exact (closedModuleName_iff n).mp (by simpa using this)
  · intro m file hm
    have := h1 (m, file) hm
    cases hr : root.resolve m with
    | none => simp [hr] at this
    | some other =>
      simp only [hr, bne_iff_ne, ne_eq, Decidable.not_not] at this
      exact ⟨other, rfl, this⟩
  · intro m file path hm hp
    have hmem : (m, path) ∈ modules.flatMap (fun x => x :: (root.resolve x.1).toList.map (x.1, ·)) := by
      refine List.mem_flatMap.mpr ⟨(m, file), hm, ?_⟩
      rcases hp with rfl | hr
      · exact List.mem_cons_self ..
      · simp [hr]
    have := h3 _ hmem
    simpa [Bool.or_eq_false_iff] using this

/-- A module of the default targets has its own file, when no name has two. -/
theorem fileOf_of_mem {root : Root L} {modules : List (Name × FilePath)} {m : Name} {path : FilePath}
    (ht : ∀ m file other, (m, file) ∈ modules → (m, other) ∈ modules → parts other = parts file)
    (hm : (m, path) ∈ modules) : ∃ q, fileOf root modules m = some q ∧ parts q = parts path := by
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
  exact ⟨file, by simp [fileOf, hl], (ht m file path (mem_of_lookup hl) hm).symm⟩

/-- The evidence of an admitted reading, from what the walk and the parse established. -/
theorem lastStage_evidence {T : List (Event L E)} {dir treeDir project tree : FilePath} {root : Root L}
    {modules : List (Name × FilePath)} {start r : Reading} {sysroot : String} {log : List String}
    {w : Walk} {files : List FileRead} {text : String}
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
    (I : WalkInv T dir treeDir project tree root modules (modules.map (·.1)) [] w) (hu : w.unread = [])
    (hfacts : ConfigFacts tree root modules)
    (hroots : ∀ m path, (m, path) ∈ modules → m ∈ w.reached)
    (hcount : modules.length + sourceImports w.sources ≤ 1000000)
    (hnodup : ((headersOf w.sources.reverse).map (·.1)).Nodup)
    (hcl : ∀ m ∈ w.reached, closedModuleName m = true) (hnm : ∀ m ∈ w.reached, m.getRoot ≠ `Mathlib)
    (hread : ∀ m path, fileOf root modules m = some path → m ∈ w.reached → ¬ OutsideTree tree path ∧
      ∃ f ∈ files, f.module = m ∧ ∃ imports mods text', (headersOf w.sources.reverse).lookup m = some imports ∧
        ReadText T root project tree f path imports mods text' ∧ held (parts path) = some text')
    (hsomeFile : ∀ n path', root.resolve n = some path' → ∃ q, fileOf root modules n = some q ∧ parts q = parts path' ∧
      (¬ OutsideTree tree q → ¬ OutsideTree tree path'))
    (hlookup : ∀ x ∈ w.sources, (headersOf w.sources.reverse).lookup x.1 = some x.2.imports)
    (hfileRead : ∀ f ∈ files, ∃ x ∈ w.sources, ∃ path,
      fileOf root modules x.1 = some path ∧ SourceRead T project tree path x.2 ∧
      FileFrom T root w.sources.reverse w.toolchain x.1 x.2 f)
    (hstored : ∀ x ∈ w.sources, ∃ f ∈ files, ∃ path imports mods, FileOfModule root modules f.module path ∧
      parts path = parts x.2.path ∧ ReadText T root project tree f path imports mods x.2.text) :
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
  have hdirs : ∀ d ∈ root.sourceDirs, ∃ rel, TreeRelative (parts tree) (parts d) rel ∧ ∀ c ∈ rel, ClosedComponent c := by
    intro d hd
    refine (closedSourceDir_iff tree d).mp ?_
    have h0 := hopen
    simp only [openPathsOf, List.append_eq_nil_iff, List.map_eq_nil_iff] at h0
    cases hin : closedSourceDir tree d with
    | true => rfl
    | false =>
      have hmem : d ∈ (root.sourceDirs.filter (!closedSourceDir tree ·)).eraseDups :=
        List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨hd, by simp [hin]⟩)
      rw [h0.1.1] at hmem
      cases hmem
  have hglobs : ∀ lib ∈ root.libraries, ∀ g ∈ lib.2, ∃ n, g = .one n := by
    intro lib hl g hg
    have h0 := hopen
    simp only [openPathsOf, List.append_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff, Bool.not_eq_true',
      Bool.not_eq_false, List.all_eq_true] at h0
    have h1 := h0.1.2 lib hl g hg
    cases g with
    | one n => exact ⟨n, rfl⟩
    | submodules n => cases h1
    | andSubmodules n => cases h1
  have htargets : ∀ target ∈ root.defaultTargets, (root.findLib target).isSome = true := by
    intro target ht
    have h0 := hopen
    simp only [openPathsOf, List.append_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff] at h0
    have h1 := h0.2 target ht
    simpa [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] using h1
  refine ⟨project, tree, hp.project_real, hp.tree_real, hp.apart, hp.toolchain, hp.absent,
    ⟨text, real, table, t1, t2, t3, t4, t5, hheld.toml, hnodeep, hkeys⟩, hheld.toolchain, hp.copyToml,
    hp.copyToolchain, sysroot, root, log,
    modules, hsys, hload, hmods, hrroots, hdirs, hglobs, hfacts.names, hfacts.found, htargets, headersOf w.sources.reverse,
    w.toolchain, ?_, hnodup, ?_, fun n hn => (I.held n hn).2.1, ?_, ?_⟩
  · rw [sum_headersOf, List.map_reverse, List.sum_reverse]
    exact hcount
  · have hrespell : ∀ {m : Name} {q path : FilePath}, parts q = parts path → ¬ OutsideTree tree path →
        (¬ OutsideTree tree q ∧ ∃ f ∈ files, f.module = m ∧ ∃ imports mods text', (headersOf w.sources.reverse).lookup m = some imports ∧
          ReadText T root project tree f q imports mods text' ∧ held (parts q) = some text') →
        (¬ OutsideTree tree path ∧ ∃ f ∈ files, f.module = m ∧ ∃ imports mods text', (headersOf w.sources.reverse).lookup m = some imports ∧
          ReadText T root project tree f path imports mods text' ∧ held (parts path) = some text') :=
      fun hp hout ⟨_, f, hf, hm, i, md, tx, hl, hrt, hs⟩ => ⟨hout, f, hf, hm, i, md, tx, hl, ReadText.respell hp hrt, hp ▸ hs⟩
    have hplaced : ∀ {m : Name} {file path : FilePath}, (m, file) ∈ modules → (path = file ∨ root.resolve m = some path) →
        ¬ OutsideTree tree path := by
      intro m file path hm hp
      obtain ⟨h1, h2⟩ := hfacts.placed m file path hm hp
      obtain ⟨rel, hrel⟩ := (inTree_iff tree path).mp h1
      exact not_outside_of hrel h2
    intro m path hc
    rw [hrfiles]
    induction hc with
    | root hm =>
      obtain ⟨q, hq, hp⟩ := fileOf_of_mem hfacts.two hm
      exact hrespell hp (hplaced hm (.inl rfl)) (hread _ _ hq (hroots _ _ hm))
    | resolved hm hres =>
      obtain ⟨q, hq, hp, hout⟩ := hsomeFile _ _ hres
      exact hrespell hp (hout (hread _ _ hq (hroots _ _ hm)).1) (hread _ _ hq (hroots _ _ hm))
    | @imported m path imports n path' _ hl hn hres _ =>
      obtain ⟨i, hi, rfl⟩ := hn
      have hmem := mem_of_lookup hl
      obtain ⟨x, hx, he⟩ := List.mem_map.mp hmem
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hxs := List.mem_reverse.mp hx
      rcases I.visited hu i.module (.inr ⟨x, hxs, i, hi, rfl⟩) with h' | h' | h'
      · cases h'
      · obtain ⟨q, hq, hp, hout⟩ := hsomeFile _ _ hres
        exact hrespell hp (hout (hread _ _ hq h').1) (hread _ _ hq h')
      · obtain ⟨q, hq, -⟩ := hsomeFile _ _ hres
        have := (I.held _ h').1
        rw [hq] at this
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
      rcases I.visited hu i.module (.inr ⟨x, hx, i, hi, rfl⟩) with h' | h' | h'
      · cases h'
      · exact ⟨.inl ((hreached _).mpr h'), (closedModuleName_iff _).mp (hcl _ h'), hnm _ h'⟩
      · obtain ⟨hnone, hheld, hc', hr', -⟩ := I.held _ h'
        rw [fileOf] at hnone
        split at hnone
        · cases hnone
        · rename_i hl
          exact ⟨.inr ⟨hnone, hl, hheld⟩, (closedModuleName_iff _).mp hc', hr'⟩
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
    {w : Walk} {files : List FileRead} {text : String}
    {config : List (FilePath × String)}
    (hp : Prior T dir treeDir project tree text start.configKeys) (hc : start.configClosed = true)
    (hd : start.requiresDependency = false)
    (hsys : SysrootIs T sysroot)
    (hload : (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ T)
    (hprepared : PreparedLoad T dir treeDir sysroot tree (.ok (some root, log)))
    (hmods : DefaultModules T root root.defaultTargets modules)
    (hopen : openPathsOf tree root = [])
    (hfacts : ConfigFacts tree root modules)
    (I : WalkInv T dir treeDir project tree root modules (modules.map (·.1)) [] w)
    (hu : w.unread = []) (hcount : modules.length + sourceImports w.sources ≤ 1000000)
    (hf : (baseReading config start modules w).readInFull = true)
    (hm : (baseReading config start modules w).mathlibReached = false)
    (g1 : ∀ f ∈ files, ∃ x ∈ w.sources.reverse, FileFrom T root w.sources.reverse w.toolchain x.1 x.2 f)
    (g2 : ∀ x ∈ w.sources.reverse, ∃ f ∈ files, FileFrom T root w.sources.reverse w.toolchain x.1 x.2 f) :
    ReadGoal T dir treeDir (Holds tree text w.sources.reverse) { baseReading config start modules w with files } := by
  obtain ⟨r, hr⟩ : ∃ r : Reading, r = { baseReading config start modules w with files } := ⟨_, rfl⟩
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
    rcases I.visited hu m (.inl (List.mem_map.mpr ⟨(m, path), hmp, rfl⟩)) with h' | h' | h'
    · cases h'
    · exact h'
    · have := (I.held m h').1
      obtain ⟨q, hq, -⟩ := fileOf_of_mem hfacts.two hmp
      rw [hq] at this
      cases this
  have hsource : ∀ m ∈ w.reached, ∃ s, (m, s) ∈ w.sources := by
    intro m hmr
    rcases I.reached m hmr with h' | h' | h'
    · exact h'
    · exfalso
      have : (baseReading config start modules w).mathlibReached = true := by
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
        (headersOf w.sources.reverse).lookup m = some imports ∧ ReadText T root project tree f path imports mods s.text := by
    intro m s hs
    obtain ⟨p, h1, h2, -⟩ := I.sources _ hs
    obtain ⟨f, hf', hfrom⟩ := g2 (m, s) (List.mem_reverse.mpr hs)
    obtain ⟨_, _, _, _, hout, _, hpath, _⟩ := id h2
    exact ⟨p, h1, hpath, hout, f, hf', hfrom.1, _, _, hlookup (m, s) hs, readText_of h2 hfrom⟩
  have hread : ∀ {held : List String → Option String}, Holds tree text w.sources.reverse held →
      ∀ m path, fileOf root modules m = some path → m ∈ w.reached → ¬ OutsideTree tree path ∧
      ∃ f ∈ files, f.module = m ∧ ∃ imports mods text', (headersOf w.sources.reverse).lookup m = some imports ∧
        ReadText T root project tree f path imports mods text' ∧ held (parts path) = some text' := by
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
      parts path = parts x.2.path ∧ ReadText T root project tree f path imports mods x.2.text := by
    intro x hx
    obtain ⟨p, h1, hpath, -, f, hf', hmod, imports, mods, -, hrt⟩ := hread0 x.1 x.2 hx
    exact ⟨f, hf', p, imports, mods, by rw [hmod]; exact fileOf_mem h1, by rw [hpath], hrt⟩
  have hsomeFile : ∀ n path', root.resolve n = some path' → ∃ q, fileOf root modules n = some q ∧ parts q = parts path' ∧
      (¬ OutsideTree tree q → ¬ OutsideTree tree path') := by
    intro n path' hres
    cases hl : modules.lookup n with
    | some q =>
      obtain ⟨h1, h2⟩ := hfacts.placed n q path' (mem_of_lookup hl) (.inr hres)
      obtain ⟨rel, hrel⟩ := (inTree_iff tree path').mp h1
      obtain ⟨g, hg, hgp⟩ := hfacts.found n q (mem_of_lookup hl)
      rw [hres] at hg
      cases hg
      exact ⟨q, by simp [fileOf, hl], hgp.symm, fun _ => not_outside_of hrel h2⟩
    | none => exact ⟨path', by simp [fileOf, hl, hres], rfl, id⟩
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
        FileFrom T root w.sources.reverse w.toolchain x.1 x.2 f := by
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
      have hnm : ∀ m ∈ w.reached, m.getRoot ≠ `Mathlib := fun m hm' hroot =>
        hinside.2.2.2.1 ⟨m, (hreached m).mpr hm', hroot⟩
      exact lastStage_evidence hheld hp hsys hload hmods hopen hreached hrfiles hrroots hrkeys hinside I hu hfacts hroots hcount
        hnodupH hclosed hnm (hread hheld) hsomeFile hlookup hfileRead hstored
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
        rcases I.visited hu i.module (.inr ⟨y, hy, i, hi, rfl⟩) with h' | h' | h'
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


/-- The two configuration copies, each with a successful answer. -/
abbrev configWrites (tree : FilePath) (text : String) : List (Event L E) :=
  [⟨.writeFile (tree / "lakefile.toml") text, .ok ()⟩, ⟨.writeFile (tree / "lean-toolchain") leanToolchain, .ok ()⟩]

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

/-- `noOtherConfig` asks one thing: on success nothing answers to the name, and on a failure something does or the question failed. -/
theorem noOtherConfig_spec {tree : FilePath} {t : List (Event L E)} {b : Except String Unit}
    (h : Runs (noOtherConfig tree : Attempt L E Unit).run t b) :
    ∃ r, t = [⟨.symlinkMetadata (tree / "lakefile.lean"), r⟩] ∧
      (b = .ok () → ∃ e, r = .error e ∧ ∃ name code details, e = .noFileOrDirectory name code details) ∧
      ((∃ e, b = .error e) → (∃ metadata, r = .ok metadata) ∨
        Event.failed (⟨.symlinkMetadata (tree / "lakefile.lean"), r⟩ : Event L E)) := by
  rw [noOtherConfig] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r, rfl, n1, n2, n3⟩ := existsByName_spec h₁
  cases r₁ with
  | error why =>
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨r, rfl, fun he => (by cases he), fun _ => .inr (n3 ⟨why, rfl⟩)⟩
  | ok v =>
    cases v with
    | true =>
      obtain ⟨rfl, hb⟩ := runs_pure_iff.mp h₂
      subst hb
      exact ⟨r, rfl, fun he => (by cases he), fun _ => .inl (n1 rfl)⟩
    | false =>
      obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂
      exact ⟨r, rfl, fun _ => n2 rfl, fun ⟨_, he⟩ => (by cases he)⟩

/-- What a reading the decision admits did to the tree: its acts leave what the list `writes` leaves, each write it asks is in
that list, and it ends with a segment that holds no act, with a read of each entry of `plan` that gave its text. -/
structure AdmittedActs (tree : FilePath) (t : List (Event L E)) (writes plan : List (FilePath × String)) : Prop where
  /-- What its acts leave. -/
  leaves : LeavesAs t writes
  /-- What it writes. -/
  writesIn : WritesIn t writes
  /-- What the file system answered after its last act. -/
  back : ∃ a b, t = a ++ b ∧ Quiet b ∧ (∀ x ∈ plan, (⟨.readFile x.1, .ok x.2⟩ : Event L E) ∈ b) ∧
    ∃ e, (⟨.symlinkMetadata (tree / "lakefile.lean"), .error e⟩ : Event L E) ∈ b ∧ ∃ name code details, e = .noFileOrDirectory name code details

/-- Earlier events that act as a list of writes come before those of the reading. -/
theorem AdmittedActs.prepend {tree : FilePath} {pre t : List (Event L E)} {k writes plan : List (FilePath × String)}
    (hl : LeavesAs pre k) (hw : WritesIn pre k) (h : AdmittedActs tree t writes plan) : AdmittedActs tree (pre ++ t) (k ++ writes) plan := by
  obtain ⟨a, b, rfl, hq, hr, habs⟩ := h.back
  exact ⟨hl.append h.leaves, hw.append h.writesIn, pre ++ a, b, by simp, hq, hr, habs⟩

theorem AdmittedActs.cast {tree : FilePath} {t : List (Event L E)} {w w' plan : List (FilePath × String)} (h : AdmittedActs tree t w plan) (he : w = w') :
    AdmittedActs tree t w' plan :=
  he ▸ h

/-- What a reading that wrote only its plan and read each of it back gives the record. -/
theorem AdmittedActs.readBack {tree : FilePath} {t : List (Event L E)} {plan : List (FilePath × String)} (h : AdmittedActs tree t plan plan) : ReadBack t tree := by
  obtain ⟨a, b, he, hq, hr, habs⟩ := h.back
  exact ⟨a, b, he, hq, (fun path text r hw _ => hr (path, text) (h.writesIn path text r hw)), habs⟩

/-- Two events, each in its list of two in order. -/
theorem pair_sublist {x y : Event L E} {a b : List (Event L E)} (hx : x ∈ a) (hy : y ∈ b) : [x, y].Sublist (a ++ b) :=
  (List.singleton_sublist.mpr hx).append (List.singleton_sublist.mpr hy)

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

/-- A copy that completed received no failed answer. -/
theorem CopyStep.clean {tree path : FilePath} {text : String} {t : List (Event L E)} {c : Bool}
    (h : CopyStep tree path text t c) (hc : c = true) : Clean t := by
  obtain ⟨⟨before, rfl, hb⟩, -⟩ := h.complete hc
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨d, rfl⟩ := hb e he
    rintro ⟨x, hx⟩
    cases hx
  · obtain rfl := List.mem_singleton.mp he
    rintro ⟨x, hx⟩
    cases hx

/-- `readBack` for every response: on success each entry's read gave its text, a failure names an entry and an answer that differs,
and all it asks is quiet. -/
theorem readBack_spec {l : List (FilePath × String)} {t : List (Event L E)} {b : Except String Unit}
    (h : Runs (readBack l : Attempt L E Unit).run t b) :
    (b = .ok () → (∀ x ∈ l, (⟨.readFile x.1, .ok x.2⟩ : Event L E) ∈ t) ∧ Clean t) ∧
    ((∃ e, b = .error e) → ∃ x ∈ l, ∃ r, (⟨.readFile x.1, r⟩ : Event L E) ∈ t ∧ r ≠ .ok x.2) ∧ Quiet t := by
  induction l generalizing t b with
  | nil =>
    rw [readBack] at h
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h
    exact ⟨fun _ => ⟨fun x hx => (by cases hx), clean_nil⟩, fun ⟨e, he⟩ => (by cases he), quiet_nil⟩
  | cons x rest ih =>
    obtain ⟨path, text⟩ := x
    rw [readBack] at h
    obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
    obtain ⟨r', hc, rfl⟩ := runs_attempt_iff.mp h₁
    obtain rfl := runs_call_iff.mp hc
    have hno : Quiet (L := L) (E := E) [⟨.readFile path, r'⟩] := quiet_one trivial
    cases r' with
    | error err =>
      obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨fun he => (by cases he), fun _ => ⟨(path, text), List.mem_cons_self .., .error err, by simp, fun he => by cases he⟩, by simpa using hno⟩
    | ok held =>
      dsimp only [Except.mapError] at h₂
      split at h₂
      · rename_i heq
        have hheld : held = text := by simpa using heq
        subst hheld
        obtain ⟨i1, i2, i3⟩ := ih h₂
        refine ⟨fun hb => ⟨fun y hy => ?_, (clean_one (by rintro ⟨y, hy⟩; cases hy)).append (i1 hb).2⟩, fun he => ?_, hno.append i3⟩
        · rcases List.mem_cons.mp hy with rfl | hy
          · simp
          · exact List.mem_cons_of_mem _ ((i1 hb).1 y hy)
        · obtain ⟨y, hy, r₁, hm, hne⟩ := i2 he
          exact ⟨y, List.mem_cons_of_mem _ hy, r₁, List.mem_cons_of_mem _ hm, hne⟩
      · rename_i hne
        obtain ⟨rfl, rfl⟩ := runs_attempt_throw_iff.mp h₂
        refine ⟨fun he => (by cases he), fun _ => ⟨(path, text), List.mem_cons_self .., .ok held, by simp, ?_⟩, by simpa using hno⟩
        intro he
        exact hne (by simpa using Except.ok.inj he)

/-- `writeSources` for every response: on success it acts as the writes of the sources; a failure names a source and why; and its acts
are the grammar's, each step using what the prefix read. -/
theorem writeSources_spec {project tree : FilePath} {root : Root L} {modules : List (Name × FilePath)}
    {srcs : List (Name × Source)} {prior t : List (Event L E)} {b : Except String Unit}
    (hs : ∀ x ∈ srcs, Named prior project tree root modules x.1 ∧ FileOfModule root modules x.1 x.2.path ∧
      SourceText prior project tree x.2.path x.2.text)
    (h : Runs (writeSources tree srcs : Attempt L E Unit).run t b) :
    (b = .ok () → LeavesAs t (srcs.map fun x => (x.2.path, x.2.text)) ∧ WritesIn t (srcs.map fun x => (x.2.path, x.2.text)) ∧
      (∀ x ∈ srcs, (⟨.writeFile x.2.path x.2.text, .ok ()⟩ : Event L E) ∈ t) ∧ Clean t) ∧
    ((∃ e, b = .error e) → ∃ x ∈ srcs, OutsideTree tree x.2.path ∨ ∃ e ∈ t, Event.failed e ∧
      ((∃ d, x.2.path.parent = some d ∧ e.op = .createDirAll d) ∨ e.op = .writeFile x.2.path x.2.text)) ∧
    ModuleCopies project tree root modules prior t := by
  induction srcs generalizing prior t b with
  | nil =>
    rw [writeSources] at h
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h
    exact ⟨fun _ => ⟨fun _ _ => rfl, fun _ _ _ he => (by cases he), fun x hx => (by cases hx), clean_nil⟩,
      fun ⟨e, he⟩ => (by cases he), .nil⟩
  | cons x rest ih =>
    obtain ⟨m, s⟩ := x
    rw [writeSources] at h
    obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
    have hstep := writeInTree_spec h₁
    obtain ⟨hn, hf, hst⟩ := hs (m, s) (List.mem_cons_self ..)
    cases r with
    | error why =>
      obtain ⟨rfl, rfl⟩ := h₂
      refine ⟨fun he => (by cases he), fun _ => ?_, .copy hn hf hst hstep .nil⟩
      rcases hstep.incomplete rfl with h' | ⟨e, he, hbad, hop⟩
      · exact ⟨(m, s), List.mem_cons_self .., .inl h'⟩
      · exact ⟨(m, s), List.mem_cons_self .., .inr ⟨e, by simpa using he, hbad, hop⟩⟩
    | ok u =>
      obtain ⟨i1, i2, i3⟩ := ih (prior := prior ++ t₁) (fun y hy => by
        obtain ⟨g1, g2, g3⟩ := hs y (List.mem_cons_of_mem _ hy)
        exact ⟨Named.mono (List.sublist_append_left _ _) g1, g2, SourceText.mono (List.sublist_append_left _ _) g3⟩) h₂
      refine ⟨fun hb => ?_, fun he => ?_, .copy hn hf hst hstep i3⟩
      · obtain ⟨l1, l2, l3, l4⟩ := i1 hb
        have hclean := hstep.clean rfl
        obtain ⟨⟨before, hbefore, hdirs⟩, -⟩ := hstep.complete rfl
        subst hbefore
        refine ⟨(leavesAs_write hdirs).append l1, (writesIn_write hdirs).append l2, fun y hy => ?_, hclean.append l4⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · simp
        · exact List.mem_append_right _ (l3 y hy)
      · obtain ⟨x, hx, hh⟩ := i2 he
        refine ⟨x, List.mem_cons_of_mem _ hx, ?_⟩
        rcases hh with h' | ⟨e, he', hf', hop⟩
        · exact .inl h'
        · exact .inr ⟨e, List.mem_append_right _ he', hf', hop⟩

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
    {modules : List (Name × FilePath)} {roots todo : List Name} {w : Walk}
    (I : WalkInv T dir treeDir project tree root modules roots todo w) :
    ∀ x ∈ w.sources, Named T project tree root modules x.1 ∧ FileOfModule root modules x.1 x.2.path ∧
      SourceText T project tree x.2.path x.2.text := by
  intro x hx
  obtain ⟨p, h1, h2, h3⟩ := I.sources x hx
  obtain ⟨rel, real, text, hrel, -, -, hpath, ht, -, hsub⟩ := h2
  subst hpath
  refine ⟨I.named _ h3, fileOf_mem h1, rel, hrel, ?_⟩
  rw [ht]
  exact hsub.subset (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- The last stage of the reader. On an admission its acts leave what the writes of the sources leave, whose plan with `lakefile.toml`
and `lean-toolchain` has no two texts at one path, and no answer it received failed. Its acts are the grammar's `ReadingLoaded`: each lookup and
parser import names the toolchain's library, and each copy is of a needed name's file, by a text the events before it read. -/
theorem readFiles_spec {T prior t : List (Event L E)} {dir treeDir project tree : FilePath} {root : Root L}
    {modules : List (Name × FilePath)} {start : Reading} {sysroot text : String} {log : List String}
    {b : Except String (Reading × List (Name × Source))} (hT : t.Sublist T)
    (hp : Prior T dir treeDir project tree text start.configKeys) (hc : start.configClosed = true)
    (hd : start.requiresDependency = false)
    (hsys : SysrootIs T sysroot)
    (hcopies : (configWrites tree text ++ t : List (Event L E)).Sublist T)
    (hload : (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ T)
    (hprepared : PreparedLoad T dir treeDir sysroot tree (.ok (some root, log)))
    (hmods : DefaultModules T root root.defaultTargets modules)
    (hprior : DefaultModules prior root root.defaultTargets modules)
    (hopen : openPathsOf tree root = [])
    (hunread : configUnread tree root modules = [])
    (h : Runs (readFiles [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] project tree root modules
      start : Attempt L E _).run t b) :
    (∀ r srcs, b = .ok (r, srcs) → ReadGoal T dir treeDir (Holds tree text srcs) r ∧
      (decision r = .admitted → AdmittedActs tree t (srcs.map fun x => (x.2.path, x.2.text)) (planOf tree text srcs) ∧
        twoTexts (plannedOf [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] srcs) = [] ∧ Clean t)) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧ ReadingLoaded prior project tree root t := by
  rw [readFiles] at h
  have hTL : TreeLoaded T dir treeDir tree root := ⟨hp.tree_real, sysroot, log, hsys, hload, hprepared⟩
  have hscene : Scene T dir treeDir project tree root modules := ⟨hp.project_real, hTL, hmods⟩
  obtain ⟨t₅, t₆, r₅, rfl, h₆, h₇⟩ := runs_attempt_bind_iff.mp h
  have hT₅ : t₅.Sublist T := (List.sublist_append_left _ _).trans hT
  have hT₆ : t₆.Sublist T := (List.sublist_append_right _ _).trans hT
  obtain ⟨w, h₈, rfl⟩ := runs_lift_iff.mp h₆
  have hinit {T' : List (Event L E)} : WalkInv T' dir treeDir project tree root modules (modules.map (·.1)) (modules.map (·.1)) {} :=
    { sources := by simp, held := by simp, nodup := by simp, reached := by simp, closed := by simp,
      named := by simp, todoNamed := fun m hm => .root hm, unread := by simp,
      visited := fun _ n hn => by
        rcases hn with hn | ⟨x, hx, -⟩
        · exact .inl hn
        · cases hx }
  obtain ⟨I, hobs, hcount⟩ := walk_spec (roots := modules.map (·.1)) 1000000 (modules.map (·.1)) {} t₅ w
    h₈ hT₅ (by simp) (by simp [sourceImports]) hinit
  obtain ⟨I', -, -⟩ := walk_spec (T := prior ++ t₅) (roots := modules.map (·.1)) 1000000 (modules.map (·.1)) {} t₅ w
    h₈ (List.sublist_append_right _ _) (by simp) (by simp [sourceImports]) hinit
  have hgram : ∀ {u}, ModuleCopies project tree root modules (prior ++ t₅) u → ReadingLoaded prior project tree root (t₅ ++ u) :=
    fun hu => .inr ⟨[], _, modules, rfl, quiet_nil, by simpa using hprior, by simpa using (ModuleCopies.observations (modules := modules) (project := project) (tree := tree) prior hobs).append hu⟩
  have hfacts := configUnread_nil hunread
  obtain ⟨config, hconfig⟩ : ∃ c : List (FilePath × String),
      c = [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] := ⟨_, rfl⟩
  rw [← hconfig] at h₇
  have hbc : (baseReading config start modules w).configClosed = true := hc
  have hbd : (baseReading config start modules w).requiresDependency = false := hd
  have hfacts' := source_facts I
  obtain ⟨_, _, _, _, _, htomlRead, _, _⟩ := hp.toml
  dsimp only at h₇
  split at h₇
  · rename_i hcond
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₇
    refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), by simpa using hgram .nil⟩
    cases he
    by_cases hf : (baseReading config start modules w).readInFull = true
    · have hm : (baseReading config start modules w).mathlibReached = true := by
        simpa [hf] using hcond
      have hdec := decision_mathlib hbc hf hbd hm
      refine ⟨⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho hne => ?_⟩, fun ha => (by rw [hdec] at ha; cases ha)⟩
      rw [hdec] at ho
      subst ho
      obtain ⟨m, hm', hroot⟩ := List.any_eq_true.mp hm
      have hmr : m ∈ w.reached := by simpa [baseReading] using hm'
      exact .mathlib hscene (I.named m hmr) (by simpa using hroot)
    · have hf' : (baseReading config start modules w).readInFull = false := by simpa using hf
      have hdec := decision_not_full hbc hf'
      refine ⟨⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho hne => ?_⟩, fun ha => (by rw [hdec] at ha; cases ha)⟩
      rw [hdec] at ho
      subst ho
      have hne' : w.unread.reverse ++ twoTexts (plannedOf config w.sources.reverse) ≠ [] := by
        intro hnil
        have : (baseReading config start modules w).readInFull = true := by
          simp only [Reading.readInFull, baseReading, hnil, List.isEmpty_nil]
        simp [this] at hf'
      by_cases hu : w.unread = []
      · have htwo : twoTexts (plannedOf config w.sources.reverse) ≠ [] := by
          simpa [hu] using hne'
        obtain ⟨x, hx, y, hy, hxy, hne⟩ := twoTexts_cons htwo
        have hmem {z} (hz : z ∈ plannedOf config w.sources.reverse) : z.2 ∈ planOf tree text w.sources.reverse := by
          rw [← plannedOf_map, ← hconfig]
          exact List.mem_map.mpr ⟨z, hz, rfl⟩
        have hsrc : ∀ z ∈ w.sources.reverse, Named T project tree root modules z.1 ∧
            FileOfModule root modules z.1 z.2.path ∧ SourceText T project tree z.2.path z.2.text :=
          fun z hz => hfacts' z (List.mem_reverse.mp hz)
        exact .twoTexts hscene (planned_of_mem htomlRead hsrc (hmem hx)) (planned_of_mem htomlRead hsrc (hmem hy)) hxy hne
      · exact I.unread hu hscene
  · rename_i hcond
    have hf : (baseReading config start modules w).readInFull = true := by
      cases hx : (baseReading config start modules w).readInFull with
      | true => rfl
      | false => exact absurd (by simp [hx]) hcond
    have hm : (baseReading config start modules w).mathlibReached = false := by
      cases hx : (baseReading config start modules w).mathlibReached with
      | false => rfl
      | true => exact absurd (by simp [hx]) hcond
    have hnil3 := hf
    simp only [Reading.readInFull, baseReading, List.isEmpty_iff,
      List.append_eq_nil_iff, List.reverse_eq_nil_iff] at hnil3
    have hu : w.unread = [] := hnil3.1
    have htwo : twoTexts (plannedOf config w.sources.reverse) = [] := hnil3.2
    obtain ⟨-, hclean₅, hcount'⟩ := hcount hu
    obtain ⟨t₇, t₈, r₇, rfl, h₉, h₁₀⟩ := runs_attempt_bind_iff.mp h₇
    have hT₇ : t₇.Sublist T := (List.sublist_append_left _ _).trans hT₆
    have hT₈ : t₈.Sublist T := (List.sublist_append_right _ _).trans hT₆
    obtain ⟨p1, p2, p3⟩ := parseFiles_spec root w.sources.reverse w.toolchain w.sources.reverse [] hT₇ (by simp) h₉
    have hobs₇ : ModuleCopies project tree root modules (prior ++ t₅) t₇ := .observations _ p3
    cases r₇ with
    | error why =>
      obtain ⟨rfl, rfl⟩ := h₁₀
      obtain ⟨mods, x, hx, hn⟩ := p2 ⟨why, rfl⟩
      exact ⟨fun _ _ he => (by cases he), fun _ => .failed (hT₇.subset hx)
          (.parser hscene fun n hm => ⟨(I.held n (hn n hm)).2.2.2.2, (I.held n (hn n hm)).2.1⟩) ⟨x, rfl⟩,
        by simpa using hgram hobs₇⟩
    | ok files =>
      obtain ⟨g1, g2, hclean₇⟩ := p1 files rfl
      have hgoal := lastStage_goal (config := config) hp hc hd hsys hload hprepared hmods hopen hfacts I hu hcount' hf hm g1 g2
      dsimp only at h₁₀
      split at h₁₀
      · rename_i hadm
        obtain ⟨t₉, t₁₀, r₉, rfl, h₁₁, h₁₂⟩ := runs_attempt_bind_iff.mp h₁₀
        obtain ⟨s1, s2, s3⟩ := writeSources_spec (project := project) (root := root) (modules := modules)
          (prior := prior ++ t₅ ++ t₇) (fun x hx => by
            have := source_facts I' x (List.mem_reverse.mp hx)
            exact ⟨Named.mono (List.sublist_append_left _ _) this.1, this.2.1,
              SourceText.mono (List.sublist_append_left _ _) this.2.2⟩) h₁₁
        have hT₉ : t₉.Sublist T := (List.sublist_append_left _ _).trans hT₈
        have hcopied : ModuleCopies project tree root modules (prior ++ t₅) (t₇ ++ t₉) := hobs₇.append s3
        cases r₉ with
        | error why =>
          obtain ⟨rfl, rfl⟩ := h₁₂
          refine ⟨fun _ _ he => (by cases he), fun _ => ?_, by simpa [List.append_assoc] using hgram hcopied⟩
          obtain ⟨x, hx, hh⟩ := s2 ⟨why, rfl⟩
          obtain ⟨h1, h2, h3⟩ := hfacts' x (List.mem_reverse.mp hx)
          rcases hh with h' | ⟨e, he, hbad, ⟨d, hd', hop⟩ | hop⟩
          · exact .moduleNotInTree hscene h1 h2 h'
          · exact .failed (hT₉.subset he) (by rw [hop]; exact .sourceParent hscene h1 h2 hd') hbad
          · exact .failed (hT₉.subset he) (by rw [hop]; exact .sourceWrite hscene h1 h2 h3) hbad
        | ok v =>
          obtain ⟨t₁₁, t₁₂, r₁₁, rfl, h₁₃, h₁₄⟩ := runs_attempt_bind_iff.mp h₁₂
          obtain ⟨b1, b2, b3⟩ := readBack_spec h₁₃
          obtain ⟨w1, w2, w3, hclean₉⟩ := s1 rfl
          have hT₁₁ : t₁₁.Sublist T := by
            refine List.Sublist.trans ?_ hT₈
            exact ((List.sublist_append_left _ _).trans (List.sublist_append_right _ _))
          have hplan : config ++ w.sources.reverse.map (fun x => (x.2.path, x.2.text)) = planOf tree text w.sources.reverse := by
            rw [hconfig]
          rw [hplan] at b1 b2
          have hgram' {u} (hq : Quiet u) : ReadingLoaded prior project tree root (t₅ ++ (t₇ ++ (t₉ ++ u))) := by
            simpa [List.append_assoc] using hgram (hcopied.append (.observations _ (hq.observes root)))
          cases r₁₁ with
          | error why =>
            obtain ⟨rfl, rfl⟩ := h₁₄
            refine ⟨fun _ _ he => (by cases he), fun _ => ?_, by simpa [List.append_assoc] using hgram' b3⟩
            obtain ⟨x, hx, r', hm, hne⟩ := b2 ⟨why, rfl⟩
            have hsrc : ∀ z ∈ w.sources.reverse, Named T project tree root modules z.1 ∧
                FileOfModule root modules z.1 z.2.path ∧ SourceText T project tree z.2.path z.2.text :=
              fun z hz => hfacts' z (List.mem_reverse.mp hz)
            refine .treeDiffers hscene (planned_of_mem htomlRead hsrc hx) ?_ hne
            rcases List.mem_append.mp hx with hx | hx
            · refine (pair_sublist ?_ (a := configWrites tree text)
                (b := _) (y := ⟨.readFile x.1, r'⟩) ?_).trans hcopies
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with rfl | rfl <;> simp
              · simp [hm]
            · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
              refine (pair_sublist (w3 y hy) hm).trans ?_
              refine List.Sublist.trans ?_ hT₈
              simp
          | ok v' =>
            obtain ⟨t₂₁, t₂₂, r₂₁, rfl, h₂₁, h₂₂⟩ := runs_attempt_bind_iff.mp h₁₄
            obtain ⟨r₂, rfl, n1, n2⟩ := noOtherConfig_spec h₂₁
            have hq₂ : Quiet ([⟨.symlinkMetadata (tree / "lakefile.lean"), r₂⟩] : List (Event L E)) := quiet_one trivial
            cases r₂₁ with
            | error why =>
              obtain ⟨rfl, rfl⟩ := h₂₂
              refine ⟨fun _ _ he => (by cases he), fun _ => ?_, by simpa [List.append_assoc] using hgram' (b3.append hq₂)⟩
              have hmem : (⟨.symlinkMetadata (tree / "lakefile.lean"), r₂⟩ : Event L E) ∈ T :=
                List.Sublist.subset (List.Sublist.trans (by simp) hT₈) (List.mem_singleton.mpr rfl)
              rcases n2 ⟨why, rfl⟩ with ⟨md, rfl⟩ | hbad
              · exact .configShadowed hp.tree_real hmem
              · exact .failed hmem (.treeLeanConfig hp.tree_real) hbad
            | ok v'' =>
            obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂₂
            refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), by simpa [List.append_assoc] using hgram' (b3.append hq₂)⟩
            cases he
            refine ⟨hgoal, fun _ => ⟨?_, hconfig ▸ htwo, ?_⟩⟩
            · have hbq : Quiet (t₁₁ ++ [⟨.symlinkMetadata (tree / "lakefile.lean"), r₂⟩] ++ ([] : List (Event L E))) := by
                simpa using Quiet.append b3 hq₂
              have hback : AdmittedActs tree (t₁₁ ++ [⟨.symlinkMetadata (tree / "lakefile.lean"), r₂⟩] ++ ([] : List (Event L E))) [] (planOf tree text w.sources.reverse) :=
                { leaves := by simpa using leavesAs_nil_of_no_act hbq.noActs
                  writesIn := by simpa using writesIn_nil_of_no_act hbq.noActs
                  back := by
                    obtain ⟨e, rfl, hn⟩ := n1 rfl
                    exact ⟨[], t₁₁ ++ [⟨.symlinkMetadata (tree / "lakefile.lean"), .error e⟩] ++ [], by simp, by simpa using hbq,
                      fun x hx => by simp [(b1 rfl).1 x hx], e, by simp, hn⟩ }
              have hnoacts : ∀ e ∈ (t₅ ++ t₇ : List (Event L E)), e.acted? = none := by
                intro e he
                rcases List.mem_append.mp he with he | he
                · exact hobs.noActs e he
                · exact p3.noActs e he
              have hall := (hback.prepend w1 w2).prepend (leavesAs_nil_of_no_act hnoacts) (writesIn_nil_of_no_act hnoacts)
              simpa [List.append_assoc] using hall
            · obtain ⟨e, rfl, name, code, details, rfl⟩ := n1 rfl
              have hlast : Clean ([⟨.symlinkMetadata (tree / "lakefile.lean"), .error (.noFileOrDirectory name code details)⟩] : List (Event L E)) :=
                clean_one (by rintro ⟨x, hx, hne⟩; cases hx; exact hne _ _ _ rfl)
              simpa [List.append_assoc] using hclean₅.append (hclean₇.append (hclean₉.append ((b1 rfl).2.append hlast)))
      · rename_i hnadm
        obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₁₀
        refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), by simpa using hgram hobs₇⟩
        cases he
        exact ⟨hgoal, fun ha => (hnadm ha).elim⟩

/-! ## Lake's load, and the paths it names -/

theorem openPaths_reason {T : List (Event L E)} {dir treeDir tree : FilePath} {root : Root L}
    (hload : TreeLoaded T dir treeDir tree root) (h : openPathsOf tree root ≠ []) : Reason T dir treeDir .refused := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h
  simp only [openPathsOf, List.mem_append, List.mem_map, List.mem_eraseDups, List.mem_filter] at hx
  rcases hx with (⟨d, ⟨hd, hn⟩, -⟩ | ⟨lib, ⟨hl, hn⟩, -⟩) | ⟨target, ⟨ht, hn⟩, -⟩
  · refine .openDir hload hd fun rel hr => ?_
    refine Classical.byContradiction fun hall => ?_
    have := (closedSourceDir_iff tree d).mpr ⟨rel, hr, fun c hc => Classical.byContradiction fun hbad => hall ⟨c, hc, hbad⟩⟩
    simp [this] at hn
  · have hne : ∃ g ∈ lib.2, ∀ n, g ≠ .one n := by
      simp only [Bool.not_eq_true', List.all_eq_false] at hn
      obtain ⟨g, hg, hs⟩ := hn
      refine ⟨g, hg, fun n he => ?_⟩
      subst he
      simp at hs
    obtain ⟨g, hg, hs⟩ := hne
    exact .openGlob hload hl hg hs
  · exact .notLibrary hload ht (by simpa [Option.isNone_iff_eq_none] using hn)

/-- A default target that is no library keeps a project from admission: a default executable, such as the one of the `lake new` application
template, or a name of no target. The owner named this refusal on 2026-11-01. -/
theorem openPaths_of_notLibrary {tree : FilePath} {root : Root L} {target : Name} (ht : target ∈ root.defaultTargets)
    (hn : root.findLib target = none) : openPathsOf tree root ≠ [] := by
  intro h
  simp only [openPathsOf, List.append_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff] at h
  have := h.2 target ht
  simp [hn] at this

/-- A source directory that `closedSourceDir` refuses keeps a project from admission. -/
theorem openPaths_of_openDir {tree d : FilePath} {root : Root L} (hd : d ∈ root.sourceDirs)
    (hn : closedSourceDir tree d = false) : openPathsOf tree root ≠ [] := by
  intro h
  simp only [openPathsOf, List.append_eq_nil_iff, List.map_eq_nil_iff] at h
  have hmem : d ∈ (root.sourceDirs.filter (!closedSourceDir tree ·)).eraseDups :=
    List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨hd, by simp [hn]⟩)
  rw [h.1.1] at hmem
  cases hmem

/-- A character outside the closed set, in a component of a source directory below the tree, makes `closedSourceDir` refuse that directory. -/
theorem closedSourceDir_of_char {tree d : FilePath} {rel : List String} {c : String} {ch : Char}
    (hr : TreeRelative (parts tree) (parts d) rel) (hc : c ∈ rel) (hch : ch ∈ c.toList) (hbad : ¬ ClosedChar ch) :
    closedSourceDir tree d = false := by
  cases h : closedSourceDir tree d with
  | false => rfl
  | true =>
    obtain ⟨rel', hr', hall⟩ := (closedSourceDir_iff tree d).mp h
    have hsame : rel' = rel := List.append_cancel_left (hr'.1.symm.trans hr.1)
    subst hsame
    exact absurd ((hall c hc).2 ch hch) hbad

/-- A space is outside the closed set. The owner named this refusal of a source directory on 2026-11-01. -/
theorem space_not_closed : ¬ ClosedChar ' ' := by decide

/-- A character outside ASCII is outside the closed set. The owner named this refusal of a source directory on 2026-11-01. -/
theorem nonAscii_not_closed {c : Char} (h : 127 < c.toNat) : ¬ ClosedChar c := by
  have hval : 127 < c.val.toNat := h
  rintro (hc | rfl | rfl)
  · simp only [Char.isAlphanum, Char.isAlpha, Char.isDigit, Char.isUpper, Char.isLower, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, UInt32.le_iff_toNat_le] at hc
    have h1 : ('Z').val.toNat = 90 := by decide
    have h2 : ('z').val.toNat = 122 := by decide
    have h3 : ('9').val.toNat = 57 := by decide
    rcases hc with (⟨-, hc⟩ | ⟨-, hc⟩) | ⟨-, hc⟩ <;> omega
  · revert h; decide
  · revert h; decide

theorem configUnread_reason {T : List (Event L E)} {dir treeDir project tree : FilePath} {root : Root L}
    {modules : List (Name × FilePath)} (hscene : Scene T dir treeDir project tree root modules)
    (h : configUnread tree root modules ≠ []) : Reason T dir treeDir .incomplete := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h
  simp only [configUnread, List.mem_append, List.mem_map, List.mem_filter] at hx
  rcases hx with (⟨n, ⟨hn, hc⟩, -⟩ | ⟨y, ⟨hy, hr⟩, -⟩) | ⟨y, ⟨hy, hr⟩, -⟩
  · refine .targetName hscene.loaded hn fun hclosed => ?_
    simp [(closedModuleName_iff n).mpr hclosed] at hc
  · refine .rootElsewhere (m := y.1) (file := y.2) hscene hy fun other hres => ?_
    simpa only [hres, bne_iff_ne] using hr
  · obtain ⟨⟨m, file⟩, hmf, hin⟩ := List.mem_flatMap.mp hy
    have hfile : FileOfModule root modules m y.2 ∧ y.1 = m := by
      rcases List.mem_cons.mp hin with rfl | hin
      · exact ⟨.inl hmf, rfl⟩
      · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hin
        have : root.resolve m = some o := by simpa [Option.mem_toList] using ho
        exact ⟨.inr this, rfl⟩
    have hout : OutsideTree tree y.2 := by
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at hr
      rcases hr with hn | hn
      · exact .inl fun rel hrel => by rw [(inTree_iff tree y.2).mpr ⟨rel, hrel⟩] at hn; cases hn
      · cases hd : y.2.parent with
        | none => rw [parentInTree, hd] at hn; cases hn
        | some d =>
          rw [parentInTree, hd] at hn
          dsimp only at hn
          exact .inr ⟨d, hd, fun rel hrel => by rw [(inTree_iff tree d).mpr ⟨rel, hrel⟩] at hn; cases hn⟩
    exact .moduleNotInTree hscene (.root (List.mem_map.mpr ⟨(m, file), hmf, rfl⟩)) hfile.1 hout

/-- What a stage that has the root package gives. -/
theorem readRoot_spec {T prior t : List (Event L E)} {dir treeDir project tree : FilePath} {start : Reading}
    {sysroot text : String} {b : Except String (Reading × List (Name × Source))} (hT : t.Sublist T)
    (hsys : SysrootIs T sysroot)
    (hcopies : (configWrites tree text ++ t : List (Event L E)).Sublist T)
    (hp : Prior T dir treeDir project tree text start.configKeys) (hc : start.configClosed = true)
    (hd : start.requiresDependency = false)
    (hprepared : ∀ response rest, t = ⟨.loadRoot sysroot tree, response⟩ :: rest →
      PreparedLoad T dir treeDir sysroot tree response)
    (h : Runs (readRoot [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] sysroot project tree start :
      Attempt L E _).run t b) :
    (∀ r srcs, b = .ok (r, srcs) → ReadGoal T dir treeDir (Holds tree text srcs) r ∧
      (decision r = .admitted → AdmittedActs tree t (srcs.map fun x => (x.2.path, x.2.text)) (planOf tree text srcs) ∧
        twoTexts (plannedOf [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] srcs) = [] ∧ Clean t)) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧ ReadingLoad prior sysroot project tree t := by
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
  have hfail : ∀ why, loaded "the configuration" r₃ = .error why → Reason T dir treeDir .incomplete ∧
      ReadingLoad prior sysroot project tree [⟨.loadRoot sysroot tree, r₃⟩] := by
    intro why he
    cases r₃ with
    | error e => exact ⟨.load hready (.inl ⟨e, rfl⟩), .inr ⟨[], .error e, [], by simp, quiet_nil, quiet_nil⟩⟩
    | ok v =>
      obtain ⟨o, log⟩ := v
      cases o with
      | none => exact ⟨.load hready (.inr ⟨log, rfl⟩), .inr ⟨[], .ok (none, log), [], by simp, quiet_nil, quiet_nil⟩⟩
      | some root => cases he
  cases hl : loaded "the configuration" r₃ with
  | error why =>
    rw [hl] at h₂
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨fun _ _ he => (by cases he), fun _ => (hfail why hl).1, by simpa using (hfail why hl).2⟩
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
    have hgram {u : List (Event L E)} (hu : ReadingLoaded (prior ++ [] ++ [⟨.loadRoot sysroot tree, .ok (some root, log)⟩]) project tree root u) :
        ReadingLoad prior sysroot project tree ([⟨.loadRoot sysroot tree, .ok (some root, log)⟩] ++ u) :=
      .inr ⟨[], .ok (some root, log), u, by simp, quiet_nil, hu⟩
    have hTL : TreeLoaded T dir treeDir tree root := ⟨hp.tree_real, sysroot, log, hsys, hmem₁, hready⟩
    dsimp only at h₂
    split at h₂
    · rename_i hopen
      obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂
      refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), by simpa using hgram (u := []) (.inl quiet_nil)⟩
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
      obtain ⟨m1, m2, m3⟩ := defaultModules_spec (T := T) root root.defaultTargets hT₅.subset h₅
      obtain ⟨m1', -, -⟩ := defaultModules_spec (T := prior ++ [] ++ [⟨.loadRoot sysroot tree, .ok (some root, log)⟩] ++ t₅)
        root root.defaultTargets (fun e he => List.mem_append_right _ he) h₅
      cases r₅ with
      | error why =>
        obtain ⟨rfl, rfl⟩ := h₆
        obtain ⟨tg, lib, x, hg, hl', hx⟩ := m2 ⟨why, rfl⟩
        exact ⟨fun _ _ he => (by cases he), fun _ => .failed (hT₅.subset hx) (.library hTL hg hl') ⟨x, rfl⟩,
          by simpa using hgram (u := t₅) (.inl m3)⟩
      | ok modules =>
        obtain ⟨hmods, hclean₅⟩ := m1 modules rfl
        dsimp only at h₆
        split at h₆
        · rename_i hfails
          obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₆
          refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), by simpa using hgram (u := t₅) (.inl m3)⟩
          cases he
          have hne : configUnread tree root modules ≠ [] := by
            intro hnil
            simp [hnil] at hfails
          have hfull : ({ start with roots := modules.map (·.1), unread := configUnread tree root modules } : Reading).readInFull = false := by
            simp [Reading.readInFull, hne]
          have hdec := decision_not_full (r := { start with roots := modules.map (·.1), unread := configUnread tree root modules }) hc hfull
          refine ⟨⟨fun ha => (by rw [hdec] at ha; cases ha), fun o ho hne' => ?_⟩, fun ha => (by rw [hdec] at ha; cases ha)⟩
          rw [hdec] at ho
          subst ho
          exact configUnread_reason ⟨hp.project_real, hTL, hmods⟩ hne
        · rename_i hfails
          have hnil : configUnread tree root modules = [] := by
            simpa using hfails
          have hcopies₆ : (configWrites tree text ++ t₆ : List (Event L E)).Sublist T := by
            refine List.Sublist.trans (List.Sublist.append_left ?_ _) hcopies
            simp
          obtain ⟨f1, f2, f3⟩ := readFiles_spec hT₆ hp hc hd hsys hcopies₆ hmem₁ hready hmods (m1' modules rfl).1 hopenNil hnil h₆
          refine ⟨fun r srcs he => ?_, f2, by simpa using hgram (u := t₅ ++ t₆) (f3.prepend m3)⟩
          obtain ⟨g1, g2⟩ := f1 r srcs he
          refine ⟨g1, fun ha => ?_⟩
          obtain ⟨l1, l2, l3⟩ := g2 ha
          refine ⟨?_, l2, ?_⟩
          · have hno : ∀ e ∈ ([⟨.loadRoot sysroot tree, .ok (some root, log)⟩] ++ [] ++ t₅ : List (Event L E)), e.acted? = none := by
              intro e he'
              simp only [List.append_nil, List.mem_append, List.mem_singleton] at he'
              rcases he' with rfl | he'
              · rfl
              · exact m3.noActs e he'
            have hl := l1.prepend (leavesAs_nil_of_no_act hno) (writesIn_nil_of_no_act hno)
            simpa [List.append_assoc] using hl
          · have hload : Clean ([⟨.loadRoot sysroot tree, .ok (some root, log)⟩] : List (Event L E)) :=
              clean_one (by rintro (⟨x, hx⟩ | ⟨x, hx⟩) <;> cases hx)
            simpa [List.append_assoc] using hload.append (hclean₅.append l3)

/-! ## The configuration -/

/-- What the stages before the configuration established, by the events `T`. -/
structure Early (T : List (Event L E)) (dir treeDir project tree : FilePath) (tf : Option String) : Prop where
  /-- The project's real path. -/
  project_real : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ T
  /-- The tree's real path. -/
  tree_real : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ T
  /-- They lie apart. -/
  apart : Apart project tree
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

/-- The parse of `lakefile.toml` and, when it is closed, the writes of its text and of the pinned `lean-toolchain`, then what
follows. -/
theorem readKeys_spec {T prior t : List (Event L E)} {dir treeDir project tree : FilePath} {tf : Option String}
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
      (decision r = .admitted → Holds tree text srcs (written t) ∧ ReadBack t tree ∧ Clean t ∧ tf = some leanToolchain)) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧
      ConfigCopies sysroot project tree [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] prior t := by
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
  have hq : Quiet ([⟨.parseToml (mkInputContext text "lakefile.toml"), r₂⟩] : List (Event L E)) := quiet_one trivial
  cases r₂ with
  | error log =>
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂
    refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), .stopped (by simpa using hq)⟩
    cases he
    exact ⟨stopped_goal hE.toolchain_reason (.failed hmem (.tomlParse hE.project_real hread) ⟨log, rfl⟩),
      fun ha => absurd ha stopped_why_not_admitted⟩
  | ok table =>
    dsimp only at h₂
    split at h₂
    · rename_i hcond
      obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂
      refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), .stopped (by simpa using hq)⟩
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
      have w := writeInTree_spec h₄
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
        exact ⟨fun _ _ he => (by cases he), fun _ => hwriteFail hT₃ (.inl rfl) (fun ho => by rw [ho]; exact .copyToml hE.project_real hE.tree_real hread) (w.incomplete rfl),
          by simpa using ConfigCopies.failed (rest := []) hq w quiet_nil⟩
      | ok u =>
        obtain ⟨t₅, t₆, r₅, rfl, h₆, h₇⟩ := runs_attempt_bind_iff.mp h₅
        have hT₅ : t₅.Sublist T := (List.sublist_append_left _ _).trans hT₄
        have hT₆ : t₆.Sublist T := (List.sublist_append_right _ _).trans hT₄
        have v := writeInTree_spec h₆
        cases r₅ with
        | error why =>
          obtain ⟨rfl, rfl⟩ := h₇
          refine ⟨fun _ _ he => (by cases he), fun _ => hwriteFail hT₅ (.inr rfl) (fun ho => by rw [ho]; exact .copyToolchain hE.tree_real) (v.incomplete rfl), ?_⟩
          apply ConfigCopies.next hq (show CopyStep tree _ text t₃ true from w)
          simpa using ConfigCopies.failed (before := []) (rest := []) quiet_nil v quiet_nil
        | ok u' =>
          have hto : tf = some leanToolchain := by
            have := ((configClosed_iff _).mp hc).1
            simpa [stopped] using this
          obtain ⟨⟨before, hb, hbd⟩, hout₁⟩ := w.complete rfl
          obtain ⟨⟨between, hm, hmd⟩, hout₂⟩ := v.complete rfl
          have hp : Prior T dir treeDir project tree text
              (stopped tf false (keysOf 8 .anonymous table) none).configKeys :=
            { project_real := hE.project_real, tree_real := hE.tree_real, apart := hE.apart,
              toolchain := hE.toolchain hto, absent := habs,
              toml := ⟨real, table, hreal, hexact.1, hexact.2, hread, hmem, rfl⟩,
              copyToml := hout₁, copyToolchain := hout₂ }
          have hprepared : ∀ response rest, t₆ = ⟨.loadRoot sysroot tree, response⟩ :: rest →
              PreparedLoad T dir treeDir sysroot tree response := by
            intro response rest ht₆
            obtain ⟨toolchain, _, htc, _, _, _, htcText⟩ := hE.toolchain hto
            refine ⟨project, text, toolchain, between, hE.project_real, hE.tree_real, hsys,
              hread, htc, htcText, ?_, hmd⟩
            apply List.IsInfix.trans _ hI
            refine ⟨[⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩] ++ before, rest, ?_⟩
            simp [hb, hm, ht₆, List.append_assoc]
          have hs₁ : ([⟨.writeFile (tree / "lakefile.toml") text, .ok ()⟩] : List (Event L E)).Sublist t₃ := by
            rw [hb]; simp
          have hs₂ : ([⟨.writeFile (tree / "lean-toolchain") leanToolchain, .ok ()⟩] : List (Event L E)).Sublist t₅ := by
            rw [hm]; simp
          have hcopies : (configWrites tree text ++ t₆ : List (Event L E)).Sublist T := by
            refine List.Sublist.trans ?_ hT₂
            simpa using hs₁.append (hs₂.append (List.Sublist.refl t₆))
          obtain ⟨f1, f2, f3⟩ := readRoot_spec (prior := prior ++ [⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩] ++ t₃ ++ [] ++ t₅)
            hT₆ hsys hcopies hp hc hd hprepared h₇
          refine ⟨fun r srcs he => ?_, f2, ?_⟩
          rotate_left
          · apply ConfigCopies.next hq (show CopyStep tree _ text t₃ true from w)
            exact ConfigCopies.next quiet_nil (show CopyStep tree _ _ t₅ true from v) (.done f3)
          obtain ⟨g1, g2⟩ := f1 r srcs he
          refine ⟨g1, fun ha => ?_⟩
          obtain ⟨l1, l2, l3⟩ := g2 ha
          have hl₄ : LeavesAs t₃ [(tree / "lakefile.toml", text)] := by rw [hb]; exact leavesAs_write hbd
          have hw₄ : WritesIn t₃ [(tree / "lakefile.toml", text)] := by rw [hb]; exact writesIn_write hbd
          have hl₆ : LeavesAs t₅ [(tree / "lean-toolchain", leanToolchain)] := by rw [hm]; exact leavesAs_write hmd
          have hw₆ : WritesIn t₅ [(tree / "lean-toolchain", leanToolchain)] := by rw [hm]; exact writesIn_write hmd
          have hnoParse : ∀ e ∈ ([⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩] : List (Event L E)), e.acted? = none :=
            fun e he => by obtain rfl := List.mem_singleton.mp he; rfl
          have hA : AdmittedActs tree ([⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩] ++ (t₃ ++ (t₅ ++ t₆)))
              (planOf tree text srcs) (planOf tree text srcs) :=
            ((((l1.prepend hl₆ hw₆).prepend hl₄ hw₄).prepend (leavesAs_nil_of_no_act hnoParse)
              (writesIn_nil_of_no_act hnoParse)).cast (by simp [planOf]))
          have hH := holds_of_leavesAs hA.leaves l2
          have hB := hA.readBack
          have hCl : Clean ([⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩] ++ (t₃ ++ (t₅ ++ t₆))) :=
            (clean_one (by rintro ⟨x, hx⟩; cases hx)).append ((w.clean rfl).append ((v.clean rfl).append l3))
          simp only [List.cons_append, List.nil_append] at hH hB hCl ⊢
          exact ⟨hH, hB, hCl, hto⟩

/-- `lakefile.lean` by its name, `lakefile.toml`, and what follows. The events before it are `prior`: they only observe, and they told the run
the real paths, which lie apart, and the toolchain, so what follows meets the grammar of a whole reading. -/
theorem readConfig_spec {T prior t : List (Event L E)} {dir treeDir project tree : FilePath} {tf : Option String}
    {sysroot : String} {b : Except String (Reading × List (Name × Source))} (hI : t <:+: T)
    (hsys : SysrootIs T sysroot) (hE : Early T dir treeDir project tree tf) (hq : Quiet prior)
    (hpp : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ prior) (hpt : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ prior)
    (hps : SysrootIs prior sysroot)
    (h : Runs (readConfig sysroot project tree tf : Attempt L E _).run t b) :
    (∀ r srcs, b = .ok (r, srcs) → ∃ text, ReadGoal T dir treeDir (Holds tree text srcs) r ∧
      (decision r = .admitted → Holds tree text srcs (written t) ∧ ReadBack t tree ∧ Clean t ∧ tf = some leanToolchain)) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧ ReadingPreparation (prior ++ t) dir treeDir := by
  have hT := hI.sublist
  rw [readConfig] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r₃, rfl, e1, e2, e3⟩ := existsByName_spec h₁
  have hT' : (([⟨.symlinkMetadata (project / "lakefile.lean"), r₃⟩] : List (Event L E)) ++ t₂).Sublist T := hT
  have hmem : (⟨.symlinkMetadata (project / "lakefile.lean"), r₃⟩ : Event L E) ∈ T :=
    hT'.subset (by simp)
  have hT₂ : t₂.Sublist T := (List.sublist_append_right _ _).trans hT'
  have hq₁ : Quiet ([⟨.symlinkMetadata (project / "lakefile.lean"), r₃⟩] : List (Event L E)) := quiet_one trivial
  cases r₁ with
  | error why =>
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨fun _ _ he => (by cases he), fun _ => .failed hmem (.leanConfig hE.project_real) (e3 ⟨why, rfl⟩), .inl (by simpa using hq.append hq₁)⟩
  | ok present =>
    cases present with
    | true =>
      obtain ⟨metadata, rfl⟩ := e1 rfl
      obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂
      refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), .inl (by simpa using hq.append hq₁)⟩
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
      have hq₂ := (hq.append hq₁).append x3
      cases r₅ with
      | error why =>
        obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₄
        refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), .inl (by simpa [List.append_assoc] using hq₂)⟩
        cases he
        refine ⟨"", stopped_goal hE.toolchain_reason ?_, fun ha => absurd ha stopped_why_not_admitted⟩
        rcases x2 ⟨why, rfl⟩ with ⟨y, hy, hf, hop | hop⟩ | ⟨real, rfl, hb⟩
        · exact .failed (hT₃.subset hy) (by rw [hop]; exact .tomlReal hE.project_real) hf
        · exact .failed (hT₃.subset hy) (by rw [hop]; exact .tomlRead hE.project_real) hf
        · exact .tomlNotExact hE.project_real (hT₃.subset (by simp)) ((exactBelow_eq_false_iff _ _ _).mp hb)
      | ok text =>
        obtain ⟨real, rfl, hb⟩ := x1 text rfl
        have hex := (RegulaSpecification.Loader.exactBelow_iff _ _ _).mp hb
        have hI₄ : t₄ <:+: T :=
          (List.infix_append_right.trans List.infix_append_right).trans hI
        obtain ⟨f1, f2, f3⟩ := readKeys_spec (prior := prior ++ [⟨.symlinkMetadata (project / "lakefile.lean"), .error e⟩] ++ [⟨.realPath (project / "lakefile.toml"), .ok real⟩, ⟨.readFile (project / "lakefile.toml"), .ok text⟩])
          hI₄ hsys hE ⟨e, hmem, habs⟩ (hT₃.subset (by simp)) hex (hT₃.subset (by simp)) h₄
        refine ⟨fun r srcs he => ?_, f2, .inr ⟨project, tree, sysroot, text, prior ++ [⟨.symlinkMetadata (project / "lakefile.lean"), .error e⟩] ++ [⟨.realPath (project / "lakefile.toml"), .ok real⟩, ⟨.readFile (project / "lakefile.toml"), .ok text⟩], t₄,
          by simp [List.append_assoc], hq₂, by simp [hpp], by simp [hpt], hE.apart, by simpa [SysrootIs] using .inl hps, by simp, f3⟩⟩
        obtain ⟨g1, g2⟩ := f1 r srcs he
        refine ⟨text, g1, fun ha => ?_⟩
        obtain ⟨hh1, hh2, hh3, hh4⟩ := g2 ha
        have hno : ∀ x ∈ ([⟨.symlinkMetadata (project / "lakefile.lean"), .error e⟩,
            ⟨.realPath (project / "lakefile.toml"), .ok real⟩, ⟨.readFile (project / "lakefile.toml"), .ok text⟩] :
              List (Event L E)), x.acted? = none := by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl <;> rfl
        have hB := ReadBack.prepend_no_acts hno hh2
        have hCl : Clean ([⟨.symlinkMetadata (project / "lakefile.lean"), .error e⟩,
            ⟨.realPath (project / "lakefile.toml"), .ok real⟩, ⟨.readFile (project / "lakefile.toml"), .ok text⟩] ++ t₄ : List (Event L E)) := by
          refine Clean.append ?_ hh3
          obtain ⟨name, code, details, rfl⟩ := habs
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl
          · rintro ⟨y, hy, hne⟩
            cases hy
            exact hne _ _ _ rfl
          · rintro ⟨y, hy⟩; cases hy
          · rintro ⟨y, hy⟩; cases hy
        simp only [List.cons_append, List.nil_append] at hB hCl ⊢
        refine ⟨Holds.congr (fun p => ?_) hh1, hB, hCl, hh4⟩
        have := written_after_no_acts (b := t₄) hno p
        simpa [List.append_assoc] using this

/-! ## The whole reader -/

/-- How `readExact` fails, by its events. -/
theorem readExact_error {project path : FilePath} {t : List (Event L E)} {why : String}
    (h : Runs (readExact project path : Attempt L E String).run t (.error why)) :
    (∃ e, t = [⟨.realPath path, .error e⟩]) ∨
      (∃ real, t = [⟨.realPath path, .ok real⟩] ∧ ¬ ExactlyBelow project path real) ∨
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
      exact .inr (.inl ⟨real, rfl, (exactBelow_eq_false_iff _ _ _).mp (by simpa using hb)⟩)

/-- `toolchainOf` gives the pinned Lean only when the file says it through the exact-path test, and anything else has a reason
to refuse. -/
theorem toolchainOf_spec {T t : List (Event L E)} {dir treeDir project : FilePath} {tf : Option String}
    (hT : t.Sublist T) (hproject : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ T)
    (h : Runs (toolchainOf project : Prog L E (Option String)) t tf) :
    (tf = some leanToolchain → (∃ text real,
      (⟨.readFile (project / "lean-toolchain"), .ok text⟩ : Event L E) ∈ T ∧
      (⟨.realPath (project / "lean-toolchain"), .ok real⟩ : Event L E) ∈ T ∧
      parts real = parts (project / "lean-toolchain") ∧
      parts project <+: parts (project / "lean-toolchain") ∧
      text.trimAscii.toString = leanToolchain) ∧ Clean t) ∧
    (tf ≠ some leanToolchain → Reason T dir treeDir .refused) ∧ Quiet t := by
  rw [toolchainOf] at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  obtain ⟨x1, x2, x3⟩ := readExact_spec h₁
  have hT₁ : t₁.Sublist T := (List.sublist_append_left _ _).trans hT
  cases r with
  | ok text =>
    obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₂
    obtain ⟨real, rfl, hb⟩ := x1 text rfl
    have hex := (RegulaSpecification.Loader.exactBelow_iff _ _ _).mp hb
    refine ⟨fun he => ⟨⟨text, real, hT₁.subset (by simp), hT₁.subset (by simp), hex.1, hex.2, ?_⟩, by clean_events⟩,
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

/-- The theorem of the reader, for every response: what its result rests on, that a whole admitted reading received no failed answer, and
the grammar of its acts, after a prefix that only observes and that holds the toolchain's answer. -/
theorem readProject_spec {T prior t : List (Event L E)} {dir treeDir : FilePath} {sysroot : String}
    {b : Except String (Reading × List (Name × Source))} (hI : t <:+: T) (hsys : SysrootIs T sysroot)
    (hq : Quiet prior) (hps : SysrootIs prior sysroot)
    (h : Runs (readProject sysroot dir treeDir : Attempt L E _).run t b) :
    (∀ r srcs, b = .ok (r, srcs) → ∃ tree text, ReadGoal T dir treeDir (Holds tree text srcs) r ∧
      (decision r = .admitted → Holds tree text srcs (written t) ∧ (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t ∧ ReadBack t tree ∧ Clean t)) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧ ReadingPreparation (prior ++ t) dir treeDir := by
  have hT := hI.sublist
  rw [readProject] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r₃, h₃, rfl⟩ := runs_attempt_iff.mp h₁
  obtain rfl := runs_call_iff.mp h₃
  cases r₃ with
  | error e =>
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨fun _ _ he => (by cases he), fun _ => .failed (e := ⟨.realPath dir, .error e⟩) (hT.subset (by simp)) .project ⟨e, rfl⟩,
      .inl (by simpa using hq.append (quiet_one (o := .realPath dir) (r := .error e) trivial))⟩
  | ok project =>
    obtain ⟨t₃, t₄, r₄, rfl, h₄, h₅⟩ := runs_attempt_bind_iff.mp h₂
    obtain ⟨r₅, h₆, rfl⟩ := runs_attempt_iff.mp h₄
    obtain rfl := runs_call_iff.mp h₆
    cases r₅ with
    | error e =>
      obtain ⟨rfl, rfl⟩ := h₅
      exact ⟨fun _ _ he => (by cases he), fun _ =>
        .failed (e := ⟨.realPath treeDir, .error e⟩) (hT.subset (by simp)) .tree ⟨e, rfl⟩,
        .inl (by simpa using hq.append (by quiet_events : Quiet ([⟨.realPath dir, .ok project⟩, ⟨.realPath treeDir, .error e⟩] : List (Event L E))))⟩
    | ok tree =>
      obtain ⟨t₉, t₁₀, r₁₀, rfl, h₁₂, h₁₃⟩ := runs_attempt_bind_iff.mp h₅
      obtain ⟨tf, h₁₄, rfl⟩ := runs_lift_iff.mp h₁₂
      dsimp only at h₁₃
      -- The events so far, and those to come, are all of `T`.
      generalize hZ : ([⟨.realPath dir, .ok project⟩] ++ ([⟨.realPath treeDir, .ok tree⟩] ++ (t₉ ++ t₁₀)) : List (Event L E)) = Z at hT ⊢
      have hsub₉ : t₉.Sublist T := by
        refine List.Sublist.trans ?_ hT
        rw [← hZ]
        simp only [List.cons_append, List.nil_append]
        exact (List.sublist_append_left _ _).trans ((List.sublist_cons_self _ _).trans (List.sublist_cons_self _ _))
      have hproject : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ T := hT.subset (by simp [← hZ])
      have htree : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ T := hT.subset (by simp [← hZ])
      obtain ⟨u1, u2, u3⟩ := toolchainOf_spec (treeDir := treeDir) hsub₉ hproject h₁₄
      have hpre : Quiet (prior ++ ([⟨.realPath dir, .ok project⟩, ⟨.realPath treeDir, .ok tree⟩] ++ t₉) : List (Event L E)) :=
        hq.append ((by quiet_events : Quiet ([⟨.realPath dir, .ok project⟩, ⟨.realPath treeDir, .ok tree⟩] : List (Event L E))).append u3)
      split at h₁₃
      · rename_i hnotApart
        obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₁₃
        refine ⟨fun r srcs he => ?_, fun ⟨e, he⟩ => (by cases he), .inl (by simpa [← hZ, List.append_assoc] using hpre)⟩
        cases he
        refine ⟨treeDir, "", stopped_goal u2 (.notApart hproject htree fun ha => ?_), fun ha => absurd ha stopped_why_not_admitted⟩
        simp [(apart_iff _ _).mpr ha] at hnotApart
      · rename_i hisApart
        have hap : Apart project tree := (apart_iff _ _).mp (by simpa using hisApart)
        have hE : Early T dir treeDir project tree tf :=
          { project_real := hproject, tree_real := htree, apart := hap,
            toolchain := fun he => (u1 he).1, toolchain_reason := u2 }
        have hI₁₀ : t₁₀ <:+: T := by
          apply List.IsInfix.trans _ hI
          exact List.infix_append_right.trans (List.infix_append_right.trans List.infix_append_right)
        obtain ⟨f1, f2, f3⟩ := readConfig_spec (prior := prior ++ ([⟨.realPath dir, .ok project⟩, ⟨.realPath treeDir, .ok tree⟩] ++ t₉))
          hI₁₀ hsys hE hpre (by simp) (by simp) (by simpa [SysrootIs] using .inl hps) h₁₃
        refine ⟨fun r srcs he => ?_, f2, by simpa [← hZ, List.append_assoc] using f3⟩
        obtain ⟨text, g1, g2⟩ := f1 r srcs he
        refine ⟨tree, text, g1, fun ha => ?_⟩
        have hno : ∀ x ∈ ([⟨.realPath dir, .ok project⟩, ⟨.realPath treeDir, .ok tree⟩] ++ t₉ : List (Event L E)), x.acted? = none :=
          ((by quiet_events : Quiet ([⟨.realPath dir, .ok project⟩, ⟨.realPath treeDir, .ok tree⟩] : List (Event L E))).append u3).noActs
        obtain ⟨hh, hb, hcl, hto⟩ := g2 ha
        have hB := ReadBack.prepend_no_acts hno hb
        refine ⟨Holds.congr (fun p => ?_) hh, by simp [← hZ], ?_, ?_⟩
        · rw [← hZ]
          have := written_after_no_acts (b := t₁₀) hno p
          simpa [List.append_assoc] using this
        · rw [← hZ]
          simpa [List.append_assoc] using hB
        · rw [← hZ]
          have hc₂ : Clean ([⟨.realPath dir, .ok project⟩, ⟨.realPath treeDir, .ok tree⟩] : List (Event L E)) := by clean_events
          simpa [List.append_assoc] using hc₂.append ((u1 hto).2.append hcl)

/-- A failed read is never admitted, of the definition that runs: on an admission, no answer that the reader asked failed. So a run in which an
answer failed gives no admission. -/
theorem readProject_no_failed {sysroot : String} {dir treeDir : FilePath} {r : Reading}
    {srcs : List (Name × Source)} {t : List (Event L E)}
    (h : Runs (readProject sysroot dir treeDir : Attempt L E _).run t (.ok (r, srcs)))
    (ha : decision r = .admitted) : ∀ e ∈ t, ¬ e.failed := by
  obtain ⟨p1, -⟩ := readProject_spec (T := [⟨.getEnv "LEAN_SYSROOT", some sysroot⟩] ++ t) (prior := [⟨.getEnv "LEAN_SYSROOT", some sysroot⟩])
    List.infix_append_right (by simp [SysrootIs]) (quiet_one trivial) (by simp [SysrootIs]) h
  obtain ⟨tree, text, -, g⟩ := p1 r srcs rfl
  exact (g ha).2.2.2

/-- What a whole read rests on, by the events `T`, for a state of the tree that is what `t` leaves. An admission received no failed answer. -/
def ReadDone (T t : List (Event L E)) (dir treeDir : FilePath) (r : Reading) : Prop :=
  (decision r = .admitted → (∀ held : List String → Option String, (∀ p, held p = written t p) →
    Evidence T dir treeDir held r) ∧ (∃ real, (⟨.realPath treeDir, .ok real⟩ : Event L E) ∈ t ∧ ReadBack t real) ∧ Clean t) ∧
    ∀ o, decision r = o → o ≠ .admitted → Reason T dir treeDir o

/-- The reader, whatever lines it returns. -/
theorem read_spec {T prior t : List (Event L E)} {dir treeDir : FilePath} {sysroot : String}
    {b : Except String (Reading × List String)} (hI : t <:+: T) (hsys : SysrootIs T sysroot)
    (hq : Quiet prior) (hps : SysrootIs prior sysroot)
    (h : Runs (read sysroot dir treeDir : Attempt L E _).run t b) :
    (∀ r lines, b = .ok (r, lines) → ReadDone T t dir treeDir r) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧ ReadingPreparation (prior ++ t) dir treeDir := by
  have hT := hI.sublist
  unfold Regula.Reader.read at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨p1, p2, p3⟩ := readProject_spec (T := T) (prior := prior) (List.infix_append_left.trans hI) hsys hq hps h₁
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
    refine ⟨fun ha => ⟨fun held hheld => g1.1 ha held ?_, ⟨tree, (g2 ha).2.1, (g2 ha).2.2.1⟩, (g2 ha).2.2.2⟩, g1.2⟩
    have heq : held = written t₁ := funext hheld
    rw [heq]
    exact (g2 ha).1

end RegulaSpecification.Effects
