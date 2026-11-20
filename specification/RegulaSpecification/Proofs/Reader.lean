module

public import RegulaSpecification.Proofs.Load
public import RegulaSpecification.Proofs.ReaderFiles
public import RegulaSpecification.Proofs.Standing
import all Regula.Language
import all Regula.Reader

/-!
# What the reader gives

{lit}`readProject_spec` is the theorem about the reader, for every response: a reading the check admits rests on
{name (full := RegulaSpecification.Effects.Evidence)}`Evidence` of each state of the tree that holds what the plan of the reading says ({lit}`Holds`), and the state
that the reader's own acts leave is one ({lit}`holds_of_leavesAs`), so every file {name (full := RegulaSpecification.Effects.Compiled)}`Compiled` names is read and
the text judged is the text that stands (that {name (full := RegulaSpecification.Effects.Compiled)}`Compiled` is what Lake compiles is the hypothesis
{lit}`LakeBehaviour`); any other outcome rests on a {name (full := RegulaSpecification.Effects.Reason)}`Reason`, so a project with no such reason is admitted; an
admission received no failed answer; and its acts meet the grammar {name (full := RegulaSpecification.Effects.ReadingPreparation)}`ReadingPreparation`, which places every
act in the tree ({name (full := RegulaSpecification.Effects.ReadingPreparation.readActs)}`ReadingPreparation.readActs`).
-/

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
  exact ⟨rel, real, s.state, s.messages, final, env, commands, h1, hex.1, hex.2,
    by rw [hheader, ← h3]; exact h4, hev, by rw [← h3]; exact hp, hsub, hparsed⟩

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
    cases n == k <;> simp [ih]

theorem sum_headersOf (sources : List (Name × Source)) :
    ((headersOf sources).map (·.2.size)).sum = (sources.map (·.2.imports.size)).sum := by
  simp [headersOf, Function.comp_def]

theorem mem_mods_iff (sources : List (Name × Source)) (toolchain : List Name) (s : Source) (n : Name) :
    n ∈ (visibleToolchain (fun n => (sources.lookup n).map (·.imports)) toolchain.contains
        (s.imports.toList.map (·.module)) []
        ((s.imports.toList.map (·.module)).length + (sources.map (·.2.imports.size)).sum + 1)).eraseDups ↔
      ∃ m ∈ s.imports, Sees (headersOf sources) toolchain m.module n := by
  rw [List.mem_eraseDups]
  have hfun : (fun n => (sources.lookup n).map (·.imports)) = fun n => (headersOf sources).lookup n :=
    funext fun x => (lookup_headersOf sources x).symm
  rw [hfun, mem_visible_iff (headersOf sources) toolchain _ _ (by rw [sum_headersOf]; omega) n]
  constructor
  · rintro ⟨m, hm, hs⟩; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm; exact ⟨i, Array.mem_toList_iff.mp hi, hs⟩
  · rintro ⟨i, hi, hs⟩; exact ⟨i.module, List.mem_map.mpr ⟨i, Array.mem_toList_iff.mpr hi, rfl⟩, hs⟩

/-- What an admission has the tree hold: the configuration, the pinned {lit}`lean-toolchain`, and each source's text at its file,
in the order the run writes them. -/
abbrev planOf (tree : FilePath) (text : String) (srcs : List (Name × Source)) : List (FilePath × String) :=
  [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] ++ srcs.map fun x => (x.2.path, x.2.text)

/-- {name}`held` holds what the plan says at each of its paths, and nothing else. -/
def Holds (tree : FilePath) (text : String) (srcs : List (Name × Source)) (held : List String → Option String) : Prop :=
  (∀ x ∈ planOf tree text srcs, held (parts x.1) = some x.2) ∧
    ∀ p v, held p = some v → ∃ x ∈ planOf tree text srcs, parts x.1 = p ∧ x.2 = v

theorem Holds.congr {tree : FilePath} {text : String} {srcs : List (Name × Source)} {a b : List String → Option String}
    (he : ∀ p, b p = a p) (h : Holds tree text srcs a) : Holds tree text srcs b :=
  (funext he : b = a) ▸ h

theorem Holds.toml {tree : FilePath} {text : String} {srcs : List (Name × Source)} {held : List String → Option String}
    (h : Holds tree text srcs held) : held (parts (tree / "lakefile.toml")) = some text :=
  h.1 (tree / "lakefile.toml", text) (List.mem_append_left _ (List.mem_cons_self ..))

theorem Holds.toolchain {tree : FilePath} {text : String} {srcs : List (Name × Source)} {held : List String → Option String}
    (h : Holds tree text srcs held) : held (parts (tree / "lean-toolchain")) = some leanToolchain :=
  h.1 (tree / "lean-toolchain", leanToolchain)
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

/-- What the reader's result must rest on, by the events {name}`T`, for each state of the tree that {name}`H` admits. -/
def ReadGoal (T : List (Event L E)) (dir treeDir : FilePath) (H : (List String → Option String) → Prop)
    (r : Reading) : Prop :=
  (decision r = .admitted → ∀ held, H held → Evidence T dir treeDir held r) ∧
    ∀ o, decision r = o → o ≠ .admitted → Reason T dir treeDir o

theorem Stage.early {T : List (Event L E)} {dir treeDir : FilePath}
    {H : (List String → Option String) → Prop} {s : Stage} {P : Prop}
    (hne : s.outcome ≠ .admitted) (hr : Reason T dir treeDir s.outcome) :
    ReadGoal T dir treeDir H s.toReading ∧ (s.outcome = .admitted → P) :=
  ⟨⟨fun ha => absurd (s.decision_toReading ▸ ha) hne, fun o ho _ => by
      rw [s.decision_toReading] at ho; exact ho ▸ hr⟩, fun ha => absurd ha hne⟩

theorem earlyUnread_early {T : List (Event L E)} {dir treeDir : FilePath}
    {H : (List String → Option String) → Prop} {tf : Option String} {why : String} {P : Prop}
    (hr : tf ≠ some leanToolchain → Reason T dir treeDir .refused)
    (hi : Reason T dir treeDir .incomplete) :
    ReadGoal T dir treeDir H (Stage.earlyUnread tf why).toReading ∧
      ((Stage.earlyUnread tf why).outcome = .admitted → P) := by
  unfold Stage.earlyUnread
  split
  · exact Stage.early (by simp [Stage.outcome]) hi
  · rename_i ht; exact Stage.early (by simp [Stage.outcome]) (hr (by simpa using ht))

/-- What the stages before Lake's load established, by the events {name}`T`: {name}`text` is the text of `lakefile.toml`. -/
structure Prior (T : List (Event L E)) (dir treeDir project tree : FilePath) (text : String) (keys : List Name) : Prop where
  /-- The project's real path. -/
  project_real : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ T
  /-- The tree's real path. -/
  tree_real : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ T
  /-- They lie apart. -/
  apart : Apart project tree
  /-- {lit}`lean-toolchain`. -/
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
  /-- The tree's {lit}`lean-toolchain` too. -/
  copyToolchain : ¬ OutsideTree tree (tree / "lean-toolchain")

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

theorem ReadText.respell {t : List (Event L E)} {root : Root L} {project tree : FilePath} {f : FileRead} {path path' : FilePath}
    {imports : Array Lean.Import} {mods : List Name} {text : String} (hp : parts path = parts path')
    (h : ReadText t root project tree f path imports mods text) : ReadText t root project tree f path' imports mods text := by
  have hn : inputNameOf path = inputNameOf path' := congrArg ("/".intercalate ·) hp
  obtain ⟨rel, real, s, m, fin, env, cmds, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  rw [hp] at h1; rw [hn] at h4 h6
  exact ⟨rel, real, s, m, fin, env, cmds, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- What {name}`configUnread` empty says, as a statement of its own: each target's name is closed, each module has one file by components,
and each spelling of it lies below the tree. -/
structure ConfigFacts (tree : FilePath) (root : Root L) (modules : List (Name × FilePath)) : Prop where
  /-- Each target's name. -/
  names : ∀ n ∈ root.targets, ClosedModuleName n
  /-- What Lake's resolution gives for a root's name has the components of the root's file. -/
  found : ∀ m file, (m, file) ∈ modules → ∃ other, root.resolve m = some other ∧ parts other = parts file
  /-- Each spelling, by the tests that the reader's writes ask. -/
  placed : ∀ m file path, (m, file) ∈ modules → (path = file ∨ root.resolve m = some path) →
    inTree tree path = true ∧ parentInTree tree path = true

theorem ConfigFacts.two {tree : FilePath} {root : Root L} {modules : List (Name × FilePath)}
    (h : ConfigFacts tree root modules) (m : Name) (file other : FilePath) (hm : (m, file) ∈ modules)
    (ho : (m, other) ∈ modules) : parts other = parts file := by
  obtain ⟨g, hg, hp⟩ := h.found m file hm
  obtain ⟨g', hg', hp'⟩ := h.found m other ho
  rw [hg] at hg'; cases hg'; exact hp'.symm.trans hp

theorem configUnread_nil {tree : FilePath} {root : Root L} {modules : List (Name × FilePath)}
    (h : configUnread tree root modules = []) : ConfigFacts tree root modules := by
  simp only [configUnread, List.append_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff] at h
  obtain ⟨⟨h0, h1⟩, h3⟩ := h
  refine ⟨fun n hn => (closedModuleName_iff n).mp (by simpa using h0 n hn), fun m file hm => ?_, fun m file path hm hp => ?_⟩
  · have := h1 (m, file) hm
    cases hr : root.resolve m with
    | none => simp [hr] at this
    | some other => simp only [hr, bne_iff_ne, ne_eq, Decidable.not_not] at this; exact ⟨other, rfl, this⟩
  · have hmem : (m, path) ∈ modules.flatMap (fun x => x :: (root.resolve x.1).toList.map (x.1, ·)) :=
      List.mem_flatMap.mpr ⟨(m, file), hm, hp.elim (fun he => he ▸ List.mem_cons_self)
        (fun hr => List.mem_cons_of_mem _ (by simp [hr]))⟩
    simpa [Bool.or_eq_false_iff] using h3 _ hmem

theorem fileOf_of_mem {root : Root L} {modules : List (Name × FilePath)} {m : Name} {path : FilePath}
    (ht : ∀ m file other, (m, file) ∈ modules → (m, other) ∈ modules → parts other = parts file)
    (hm : (m, path) ∈ modules) : ∃ q, fileOf root modules m = some q ∧ parts q = parts path := by
  cases hl : modules.lookup m with
  | some file => exact ⟨file, by simp [fileOf, hl], (ht m file path (mem_of_lookup hl) hm).symm⟩
  | none => exact absurd (by simp : (m == (m, path).1) = true) (by simpa using List.lookup_eq_none_iff.mp hl (m, path) hm)

theorem openPathsOf_nil {tree : FilePath} {root : Root L} (hopen : openPathsOf tree root = []) :
    (∀ d ∈ root.sourceDirs, ∃ rel, TreeRelative (parts tree) (parts d) rel ∧ ∀ c ∈ rel, ClosedComponent c) ∧
    (∀ lib ∈ root.libraries, ∀ g ∈ lib.2, ∃ n, g = .one n) ∧
    (∀ target ∈ root.defaultTargets, (root.findLib target).isSome = true) := by
  simp only [openPathsOf, List.append_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff] at hopen
  obtain ⟨⟨h1, h2⟩, h3⟩ := hopen
  refine ⟨fun d hd => (closedSourceDir_iff tree d).mp ?_, fun lib hl g hg => ?_, fun target ht => ?_⟩
  · cases hin : closedSourceDir tree d with
    | true => rfl
    | false =>
      have hmem : d ∈ (root.sourceDirs.filter (!closedSourceDir tree ·)).eraseDups :=
        List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨hd, by simp [hin]⟩)
      rw [h1] at hmem; cases hmem
  · simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at h2
    have hg' := h2 lib hl g hg
    cases g with
    | one n => exact ⟨n, rfl⟩
    | submodules _ | andSubmodules _ => cases hg'
  · simpa [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] using h3 target ht

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
  subst hrfiles
  obtain ⟨real, table, t1, t2, t3, t4, t5, hk⟩ := hp.toml
  obtain ⟨hdirs, hglobs, htargets⟩ := openPathsOf_nil hopen
  have hnodeep : ¬ Deeper 8 table := fun hd => by
    obtain ⟨d, hd', hdeep⟩ := keysOf_deep (pre := .anonymous) hd
    obtain ⟨hc, -, hnd, -⟩ := hinside
    have hdr : d ∈ r.configKeys := (hrkeys.trans hk) ▸ hd'
    by_cases hroot : d.getRoot = `require
    · exact hnd ⟨d, hdr, hroot⟩
    · exact deepKey_not_admitted hdeep (hc.2.2.2 d hdr hroot)
  refine ⟨project, tree, hp.project_real, hp.tree_real, hp.apart, hp.toolchain, hp.absent,
    ⟨text, real, table, t1, t2, t3, t4, t5, hheld.toml, hnodeep, keyPaths_in hinside (hrkeys.trans hk)⟩,
    hheld.toolchain, hp.copyToml, hp.copyToolchain, sysroot, root, log, modules, hsys, hload, hmods,
    hrroots, hdirs, hglobs, hfacts.names, hfacts.found, htargets, headersOf w.sources.reverse, w.toolchain,
    by rw [sum_headersOf, List.map_reverse, List.sum_reverse]; exact hcount,
    hnodup, ?_, fun n hn => (I.held n hn).2.1, ?_, ?_⟩
  · let P (m : Name) (p : FilePath) : Prop := ¬ OutsideTree tree p ∧ ∃ f ∈ r.files, f.module = m ∧ ∃ imports mods text',
      (headersOf w.sources.reverse).lookup m = some imports ∧ ReadText T root project tree f p imports mods text' ∧ held (parts p) = some text'
    have hrespell {m q path} (hp' : parts q = parts path) (hout : ¬ OutsideTree tree path) (h : P m q) : P m path :=
      let ⟨_, f, hf, hm', i, md, tx, hl, hrt, hs⟩ := h
      ⟨hout, f, hf, hm', i, md, tx, hl, ReadText.respell hp' hrt, hp' ▸ hs⟩
    intro m path hc
    induction hc with
    | root hm' =>
      obtain ⟨q, hq, hp'⟩ := fileOf_of_mem hfacts.two hm'
      obtain ⟨h1, h2⟩ := hfacts.placed _ _ _ hm' (.inl rfl)
      obtain ⟨rel, hrel⟩ := (inTree_iff tree _).mp h1
      exact hrespell hp' (not_outside_of hrel h2) (hread _ _ hq (hroots _ _ hm'))
    | resolved hm' hres =>
      obtain ⟨q, hq, hp', hout⟩ := hsomeFile _ _ hres
      exact hrespell hp' (hout (hread _ _ hq (hroots _ _ hm')).1) (hread _ _ hq (hroots _ _ hm'))
    | @imported m path imports n path' _ hl hn hres _ =>
      obtain ⟨i, hi, rfl⟩ := hn
      obtain ⟨x, hx, he⟩ := List.mem_map.mp (mem_of_lookup hl)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rcases I.visited hu i.module (.inr ⟨x, List.mem_reverse.mp hx, i, hi, rfl⟩) with h' | h' | h'
      · cases h'
      · obtain ⟨q, hq, hp', hout⟩ := hsomeFile _ _ hres
        exact hrespell hp' (hout (hread _ _ hq h').1) (hread _ _ hq h')
      · obtain ⟨q, hq, -⟩ := hsomeFile _ _ hres
        have h1 := (I.held _ h').1; rw [hq] at h1; cases h1
  · intro f hf
    obtain ⟨x, hx, path, hfp, hs, hfrom⟩ := hfileRead f hf
    obtain ⟨-, -, -, -, -, -, hpath, -⟩ := id hs
    refine ⟨path, x.2.imports, _, x.2.text, by rw [hfrom.1]; exact fileOf_mem hfp, readText_of hs hfrom,
      hpath ▸ hheld.1 (x.2.path, x.2.text) (List.mem_append_right _ (List.mem_map.mpr ⟨x, List.mem_reverse.mpr hx, rfl⟩)),
      by rw [hfrom.1]; exact hlookup x hx, mem_mods_iff _ _ _, fun i hi => ?_⟩
    rcases I.visited hu i.module (.inr ⟨x, hx, i, hi, rfl⟩) with h' | h' | h'
    · cases h'
    · exact ⟨.inl ((hreached _).mpr h'), (closedModuleName_iff _).mp (hcl _ h'), hnm _ h'⟩
    · obtain ⟨hnone, hheld', hc', hr', -⟩ := I.held _ h'
      rw [fileOf] at hnone; split at hnone
      · cases hnone
      · exact ⟨.inr ⟨hnone, ‹_›, hheld'⟩, (closedModuleName_iff _).mp hc', hr'⟩
  · intro p v hv
    obtain ⟨x, hx, h1, h2⟩ := hheld.2 p v hv
    rcases List.mem_append.mp hx with hx | hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact .inl h1.symm
      · exact .inr (.inl h1.symm)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨f, hf, path, imports, mods, g1, g2, g3⟩ := hstored y (List.mem_reverse.mp hy)
      exact .inr (.inr ⟨f, hf, path, imports, mods, g1, g2.trans h1, h2 ▸ g3⟩)

theorem ofFiles_goal {T : List (Event L E)} {dir treeDir project tree : FilePath} {root : Root L}
    {modules : List (Name × FilePath)} {cfg : ClosedConfig} {sysroot text : String} {log : List String}
    {w : Walk} {files : List FileRead}
    (hp : Prior T dir treeDir project tree text cfg.keys)
    (hsys : SysrootIs T sysroot)
    (hload : (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ T)
    (hprepared : PreparedLoad T dir treeDir sysroot tree (.ok (some root, log)))
    (hmods : DefaultModules T root root.defaultTargets modules)
    (hopen : openPathsOf tree root = [])
    (hfacts : ConfigFacts tree root modules)
    (I : WalkInv T dir treeDir project tree root modules (modules.map (·.1)) [] w)
    (hu : w.unread = []) (hcount : modules.length + sourceImports w.sources ≤ 1000000)
    (hm : w.reached.reverse.any (·.getRoot == `Mathlib) = false)
    (g1 : ∀ f ∈ files, ∃ x ∈ w.sources.reverse, FileFrom T root w.sources.reverse w.toolchain x.1 x.2 f)
    (g2 : ∀ x ∈ w.sources.reverse, ∃ f ∈ files, FileFrom T root w.sources.reverse w.toolchain x.1 x.2 f) :
    ReadGoal T dir treeDir (Holds tree text w.sources.reverse)
      (Stage.ofFiles cfg (modules.map (·.1)) w.reached.reverse files hm).toReading := by
  have hscene : Scene T dir treeDir project tree root modules :=
    ⟨hp.project_real, ⟨hp.tree_real, sysroot, log, hsys, hload, hprepared⟩, hmods⟩
  have hroots : ∀ m path, (m, path) ∈ modules → m ∈ w.reached := fun m path hmp => by
    rcases I.visited hu m (.inl (List.mem_map.mpr ⟨(m, path), hmp, rfl⟩)) with h' | h' | h'
    · cases h'
    · exact h'
    · obtain ⟨q, hq, -⟩ := fileOf_of_mem hfacts.two hmp
      have h1 := (I.held m h').1; rw [hq] at h1; cases h1
  have hnm : ∀ m ∈ w.reached, m.getRoot ≠ `Mathlib := fun m hmr hroot => by
    have := List.any_eq_false.mp hm m (List.mem_reverse.mpr hmr); simp [hroot] at this
  have hsource : ∀ m ∈ w.reached, ∃ s, (m, s) ∈ w.sources := fun m hmr => by
    rcases I.reached m hmr with h' | h' | h'
    · exact h'
    · exact absurd h' (hnm m hmr)
    · exact absurd hu h'
  have hclosed : ∀ m ∈ w.reached, closedModuleName m = true := fun m hmr =>
    (I.closed m hmr).resolve_right (by simp [hu])
  have hnodup : ((w.sources.reverse).map (·.1)).Nodup := by
    rw [List.map_reverse]; exact List.pairwise_reverse.mpr (I.nodup.imp fun h h' => h h'.symm)
  have hlookup : ∀ x ∈ w.sources, (headersOf w.sources.reverse).lookup x.1 = some x.2.imports := fun x hx => by
    rw [lookup_headersOf, lookup_of_mem hnodup (List.mem_reverse.mpr hx)]; rfl
  have hfileRead : ∀ f ∈ files, ∃ x ∈ w.sources, ∃ path,
      fileOf root modules x.1 = some path ∧ SourceRead T project tree path x.2 ∧
      FileFrom T root w.sources.reverse w.toolchain x.1 x.2 f := fun f hf' => by
    obtain ⟨x, hx, hfrom⟩ := g1 f hf'
    obtain ⟨p, h1, h2, -⟩ := I.sources x (List.mem_reverse.mp hx)
    exact ⟨x, List.mem_reverse.mp hx, p, h1, h2, hfrom⟩
  unfold Stage.ofFiles
  split
  · rename_i huncov
    refine (Stage.early (P := True) (by simp [Stage.outcome]) ?_).1
    dsimp only [Stage.outcome]
    cases hms : modules with
    | nil => exact .noClaim (hms ▸ hscene)
    | cons hd tl =>
      exfalso; subst hms
      have hcov : covers ((hd :: tl).map (·.1)) w.reached.reverse files = true := by
        simp only [covers, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.contains_iff_mem, List.mem_reverse]
        refine ⟨⟨⟨rfl, fun m hmr => ?_⟩, fun m hmr => hclosed m hmr⟩, fun m hmr => ?_⟩
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hmr; exact hroots x.1 x.2 hx
        · obtain ⟨s, hs⟩ := hsource m hmr
          obtain ⟨f, hf', hfrom⟩ := g2 (m, s) (List.mem_reverse.mpr hs)
          exact List.any_eq_true.mpr ⟨f, hf', by simpa using hfrom.1⟩
      rw [hcov] at huncov; cases huncov
  · split
    · rename_i hcov hbad
      refine (Stage.early (P := True) (by simp [Stage.outcome]) ?_).1
      obtain ⟨f, hf', hna⟩ := List.all_eq_false.mp hbad
      obtain ⟨x, hx, p, h1, h2, hfrom⟩ := hfileRead f hf'
      obtain ⟨-, -, -, hxr⟩ := I.sources x hx
      have hclosure : ∀ y ∈ w.sources, ∀ i ∈ y.2.imports, i.module ∈ w.toolchain ∨
          ((headersOf w.sources.reverse).lookup i.module).isSome = true := fun y hy i hi => by
        rcases I.visited hu i.module (.inr ⟨y, hy, i, hi, rfl⟩) with h' | h' | h'
        · cases h'
        · obtain ⟨s, hs⟩ := hsource _ h'; exact .inr (by rw [hlookup (_, s) hs]; rfl)
        · exact .inl h'
      refine .file hscene (hfrom.1 ▸ I.named _ hxr) (by rw [hfrom.1]; exact fileOf_mem h1) ⟨_, readText_of h2 hfrom⟩
        (headers := headersOf w.sources.reverse) (held := w.toolchain) ?_
        (fun n hn => ⟨(I.held n hn).2.2.2.2, (I.held n hn).2.1⟩) (hclosure x hx) ?_ (mem_mods_iff _ _ _)
        fun had => hna ((fileAdmitted_iff f).mpr had)
      · intro y hy; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        obtain ⟨q, q1, q2, -⟩ := I.sources z (List.mem_reverse.mp hz); exact headerOf_read q1 q2
      · intro y hy i hi; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        exact hclosure z (List.mem_reverse.mp hz) i hi
    · rename_i hcov hadm
      refine ⟨fun ha held hheld => ?_, fun o ho hne => absurd (ho.symm.trans (Stage.decision_toReading _)) hne⟩
      have hread0 : ∀ m s, (m, s) ∈ w.sources → ∃ path, fileOf root modules m = some path ∧ s.path = path ∧
          ¬ OutsideTree tree path ∧ ∃ f ∈ files, f.module = m ∧ ∃ imports mods,
            (headersOf w.sources.reverse).lookup m = some imports ∧ ReadText T root project tree f path imports mods s.text :=
        fun m s hs => by
          obtain ⟨p, h1, h2, -⟩ := I.sources _ hs
          obtain ⟨f, hf', hfrom⟩ := g2 (m, s) (List.mem_reverse.mpr hs)
          obtain ⟨_, _, _, _, hout, _, hpath, _⟩ := id h2
          exact ⟨p, h1, hpath, hout, f, hf', hfrom.1, _, _, hlookup (m, s) hs, readText_of h2 hfrom⟩
      have hread : ∀ m path, fileOf root modules m = some path → m ∈ w.reached → ¬ OutsideTree tree path ∧
          ∃ f ∈ files, f.module = m ∧ ∃ imports mods text', (headersOf w.sources.reverse).lookup m = some imports ∧
            ReadText T root project tree f path imports mods text' ∧ held (parts path) = some text' :=
        fun m path hfile hmr => by
          obtain ⟨s, hs⟩ := hsource m hmr
          obtain ⟨p, h1, hpath, hout, f, hf', hmod, imports, mods, hl, hrt⟩ := hread0 m s hs
          have : p = path := Option.some.inj (h1.symm.trans hfile); subst this
          exact ⟨hout, f, hf', hmod, imports, mods, s.text, hl, hrt,
            hpath ▸ hheld.1 (s.path, s.text) (List.mem_append_right _ (List.mem_map.mpr ⟨(m, s), List.mem_reverse.mpr hs, rfl⟩))⟩
      have hsomeFile : ∀ n path', root.resolve n = some path' → ∃ q, fileOf root modules n = some q ∧ parts q = parts path' ∧
          (¬ OutsideTree tree q → ¬ OutsideTree tree path') := fun n path' hres => by
        cases hl : modules.lookup n with
        | some q =>
          obtain ⟨h1, h2⟩ := hfacts.placed n q path' (mem_of_lookup hl) (.inr hres)
          obtain ⟨rel, hrel⟩ := (inTree_iff tree path').mp h1
          obtain ⟨g, hg, hgp⟩ := hfacts.found n q (mem_of_lookup hl)
          rw [hres] at hg; cases hg
          exact ⟨q, by simp [fileOf, hl], hgp.symm, fun _ => not_outside_of hrel h2⟩
        | none => exact ⟨path', by simp [fileOf, hl, hres], rfl, id⟩
      exact lastStage_evidence
        (start := (Stage.admitted cfg (modules.map (·.1)) w.reached.reverse files hm hcov hadm).toReading)
        hheld hp hsys hload hmods hopen (fun _ => List.mem_reverse) rfl rfl rfl ((decision_admitted_iff _).mp ha) I hu hfacts
        hroots hcount (by simpa [headersOf, Function.comp_def] using hnodup) hclosed hnm hread hsomeFile hlookup hfileRead
        fun x hx => by
          obtain ⟨p, h1, hpath, -, f, hf', hmod, imports, mods, -, hrt⟩ := hread0 x.1 x.2 hx
          exact ⟨f, hf', p, imports, mods, by rw [hmod]; exact fileOf_mem h1, by rw [hpath], hrt⟩

/-- The two configuration copies, each with a successful answer. -/
abbrev configWrites (tree : FilePath) (text : String) : List (Event L E) :=
  [⟨.writeFile (tree / "lakefile.toml") text, .ok ()⟩, ⟨.writeFile (tree / "lean-toolchain") leanToolchain, .ok ()⟩]

theorem existsByName_spec {path : FilePath} {t : List (Event L E)} {b : Except String Bool}
    (h : Runs (existsByName path : Attempt L E Bool).run t b) :
    ∃ r, t = [⟨.symlinkMetadata path, r⟩] ∧
      (b = .ok true → ∃ metadata, r = .ok metadata) ∧
      (b = .ok false → ∃ e, r = .error e ∧ ∃ name code details, e = .noFileOrDirectory name code details) ∧
      ((∃ e, b = .error e) → Event.failed (⟨.symlinkMetadata path, r⟩ : Event L E)) := by
  rw [existsByName] at h
  obtain ⟨t₃, t₄, r₃, rfl, h₃, h₄⟩ := runs_bind_iff.mp h; obtain rfl := runs_call_iff.mp h₃
  refine ⟨r₃, ?_⟩
  cases r₃ with
  | ok metadata => obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₄; exact ⟨rfl, fun _ => ⟨metadata, rfl⟩, by simp, by simp⟩
  | error e =>
    cases e with
    | noFileOrDirectory name code details =>
      obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₄
      exact ⟨rfl, by simp, fun _ => ⟨_, rfl, name, code, details, rfl⟩, by simp⟩
    | _ =>
      obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₄
      exact ⟨rfl, by simp, by simp, fun _ => ⟨_, rfl, fun _ _ _ he => by cases he⟩⟩

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
  | error why => obtain ⟨rfl, rfl⟩ := h₂; exact ⟨r, rfl, by simp, fun _ => .inr (n3 ⟨why, rfl⟩)⟩
  | ok v =>
    cases v with
    | true => obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₂; exact ⟨r, rfl, by simp, fun _ => .inl (n1 rfl)⟩
    | false => obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂; exact ⟨r, rfl, fun _ => n2 rfl, by simp⟩

/-- What a reading the decision admits did to the tree: its acts leave what the list {name}`writes` leaves, each write it asks is in
that list, and it ends with a segment that holds no act, with a read of each entry of {name}`plan` that gave its text. -/
structure AdmittedActs (tree : FilePath) (t : List (Event L E)) (writes plan : List (FilePath × String)) : Prop where
  /-- What its acts leave. -/
  leaves : LeavesAs t writes
  /-- What it writes. -/
  writesIn : WritesIn t writes
  /-- What the file system answered after its last act. -/
  back : ∃ a b, t = a ++ b ∧ Quiet b ∧ (∀ x ∈ plan, (⟨.readFile x.1, .ok x.2⟩ : Event L E) ∈ b) ∧
    ∃ e, (⟨.symlinkMetadata (tree / "lakefile.lean"), .error e⟩ : Event L E) ∈ b ∧ ∃ name code details, e = .noFileOrDirectory name code details

theorem AdmittedActs.prepend {tree : FilePath} {pre t : List (Event L E)} {k writes plan : List (FilePath × String)}
    (hl : LeavesAs pre k) (hw : WritesIn pre k) (h : AdmittedActs tree t writes plan) : AdmittedActs tree (pre ++ t) (k ++ writes) plan := by
  obtain ⟨a, b, rfl, hq, hr, habs⟩ := h.back
  exact ⟨hl.append h.leaves, hw.append h.writesIn, pre ++ a, b, by simp, hq, hr, habs⟩

theorem AdmittedActs.cast {tree : FilePath} {t : List (Event L E)} {w w' plan : List (FilePath × String)} (h : AdmittedActs tree t w plan) (he : w = w') :
    AdmittedActs tree t w' plan :=
  he ▸ h

theorem AdmittedActs.readBack {tree : FilePath} {t : List (Event L E)} {plan : List (FilePath × String)}
    (h : AdmittedActs tree t plan plan) : ReadBack t tree := by
  obtain ⟨a, b, he, hq, hr, habs⟩ := h.back
  exact ⟨a, b, he, hq, fun path text r hw _ => hr (path, text) (h.writesIn path text r hw), habs⟩

theorem pair_sublist {x y : Event L E} {a b : List (Event L E)} (hx : x ∈ a) (hy : y ∈ b) : [x, y].Sublist (a ++ b) :=
  (List.singleton_sublist.mpr hx).append (List.singleton_sublist.mpr hy)

theorem twoTexts_nil {planned : List (Name × FilePath × String)} (h : twoTexts planned = []) :
    ∀ x ∈ planned, ∀ y ∈ planned, parts x.2.1 = parts y.2.1 → x.2.2 = y.2.2 := by
  intro x hx y hy hp
  simp only [twoTexts, List.map_eq_nil_iff, List.filter_eq_nil_iff] at h
  have h1 := h x hx
  simp only [Bool.not_eq_true, List.any_eq_false, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, not_and, ne_eq, Decidable.not_not] at h1
  exact h1 y hy hp

theorem twoTexts_cons {planned : List (Name × FilePath × String)} (h : twoTexts planned ≠ []) :
    ∃ x ∈ planned, ∃ y ∈ planned, parts x.2.1 = parts y.2.1 ∧ x.2.2 ≠ y.2.2 := by
  obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ h
  simp only [twoTexts, List.mem_map, List.mem_filter, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hz
  obtain ⟨x, ⟨hx, y, hy, hp, hne⟩, -⟩ := hz; exact ⟨x, hx, y, hy, hp, hne⟩

theorem plannedOf_map (tree : FilePath) (text : String) (srcs : List (Name × Source)) :
    (plannedOf [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] srcs).map (·.2) =
      planOf tree text srcs := by
  simp [plannedOf, planOf, Function.comp_def]

theorem holds_of_leavesAs {t : List (Event L E)} {tree : FilePath} {text : String} {srcs : List (Name × Source)}
    (h : LeavesAs t (planOf tree text srcs))
    (hc : twoTexts (plannedOf [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] srcs) = []) :
    Holds tree text srcs (written t) := by
  have hag : ∀ x ∈ planOf tree text srcs, ∀ y ∈ planOf tree text srcs, parts y.1 = parts x.1 → y.2 = x.2 := by
    intro x hx y hy hp; rw [← plannedOf_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx; obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
    exact twoTexts_nil hc y' hy' x' hx' hp
  refine ⟨fun x hx => h.written _ ▸ writesOf_agree (fun y hy hp => hag x hx y hy hp) (.inr ⟨x, hx, rfl⟩),
    fun p v hv => ?_⟩
  rw [h.written] at hv
  rcases writesOf_mem hv with he | hm
  · cases he
  · exact hm

theorem CopyStep.clean {tree path : FilePath} {text : String} {t : List (Event L E)} {c : Bool}
    (h : CopyStep tree path text t c) (hc : c = true) : Clean t := by
  obtain ⟨⟨before, rfl, hb⟩, -⟩ := h.complete hc
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨d, rfl⟩ := hb e he; rintro ⟨_, hx⟩; cases hx
  · rw [List.mem_singleton.mp he]; rintro ⟨_, hx⟩; cases hx

theorem readBack_spec {l : List (FilePath × String)} {t : List (Event L E)} {b : Except String Unit}
    (h : Runs (readBack l : Attempt L E Unit).run t b) :
    (b = .ok () → (∀ x ∈ l, (⟨.readFile x.1, .ok x.2⟩ : Event L E) ∈ t) ∧ Clean t) ∧
    ((∃ e, b = .error e) → ∃ x ∈ l, ∃ r, (⟨.readFile x.1, r⟩ : Event L E) ∈ t ∧ r ≠ .ok x.2) ∧ Quiet t := by
  induction l generalizing t b with
  | nil =>
    rw [readBack] at h; obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h
    exact ⟨fun _ => ⟨fun _ hx => (by cases hx), clean_nil⟩, by simp, quiet_nil⟩
  | cons x rest ih =>
    obtain ⟨path, text⟩ := x; rw [readBack] at h
    obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
    obtain ⟨r', hc, rfl⟩ := runs_attempt_iff.mp h₁; obtain rfl := runs_call_iff.mp hc
    have hno : Quiet (L := L) (E := E) [⟨.readFile path, r'⟩] := quiet_one trivial
    cases r' with
    | error err =>
      obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨by simp, fun _ => ⟨(path, text), by simp, .error err, (by simp), (by intro he; cases he)⟩, by simpa using hno⟩
    | ok held =>
      dsimp only [Except.mapError] at h₂
      split at h₂
      · rename_i heq
        have hht : held = text := by simpa using heq
        subst hht
        obtain ⟨i1, i2, i3⟩ := ih h₂
        refine ⟨fun hb => ⟨fun y hy => ?_, (by clean_events : Clean _).append (i1 hb).2⟩, fun he => ?_, hno.append i3⟩
        · rcases List.mem_cons.mp hy with rfl | hy
          · simp
          · exact List.mem_cons_of_mem _ ((i1 hb).1 y hy)
        · obtain ⟨y, hy, r₁, hm, hne⟩ := i2 he; exact ⟨y, List.mem_cons_of_mem _ hy, r₁, List.mem_cons_of_mem _ hm, hne⟩
      · rename_i hne; obtain ⟨rfl, rfl⟩ := runs_attempt_throw_iff.mp h₂
        exact ⟨by simp, fun _ => ⟨(path, text), by simp, .ok held, (by simp), fun he => hne (by simpa using Except.ok.inj he)⟩,
          by simpa using hno⟩

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
    rw [writeSources] at h; obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h
    exact ⟨fun _ => ⟨fun _ _ => rfl, fun _ _ _ he => (by cases he), fun _ hx => (by cases hx), clean_nil⟩, by simp, .nil⟩
  | cons x rest ih =>
    obtain ⟨m, s⟩ := x; rw [writeSources] at h
    obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
    have hstep := writeInTree_spec h₁
    obtain ⟨hn, hf, hst⟩ := hs (m, s) (by simp)
    cases r with
    | error why =>
      obtain ⟨rfl, rfl⟩ := h₂
      refine ⟨by simp, fun _ => ⟨(m, s), by simp, ?_⟩, .copy hn hf hst hstep .nil⟩
      rcases hstep.incomplete rfl with h' | ⟨e, he, hbad, hop⟩
      · exact .inl h'
      · exact .inr ⟨e, by simpa using he, hbad, hop⟩
    | ok _ =>
      obtain ⟨i1, i2, i3⟩ := ih (prior := prior ++ t₁) (fun y hy =>
        let ⟨g1, g2, g3⟩ := hs y (List.mem_cons_of_mem _ hy)
        ⟨Named.mono (List.sublist_append_left _ _) g1, g2, SourceText.mono (List.sublist_append_left _ _) g3⟩) h₂
      refine ⟨fun hb => ?_, fun he => ?_, .copy hn hf hst hstep i3⟩
      · obtain ⟨l1, l2, l3, l4⟩ := i1 hb
        have hclean := hstep.clean rfl
        obtain ⟨⟨before, rfl, hdirs⟩, -⟩ := hstep.complete rfl
        refine ⟨(leavesAs_write hdirs).append l1, (writesIn_write hdirs).append l2, fun y hy => ?_, hclean.append l4⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · simp
        · exact List.mem_append_right _ (l3 y hy)
      · obtain ⟨x, hx, hh⟩ := i2 he
        refine ⟨x, List.mem_cons_of_mem _ hx, ?_⟩
        rcases hh with h' | ⟨e, he', hf', hop⟩
        · exact .inl h'
        · exact .inr ⟨e, List.mem_append_right _ he', hf', hop⟩

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
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; obtain ⟨h1, h2, h3⟩ := hsrc y hy; exact .source h1 h2 h3

theorem source_facts {T : List (Event L E)} {dir treeDir project tree : FilePath} {root : Root L}
    {modules : List (Name × FilePath)} {roots todo : List Name} {w : Walk}
    (I : WalkInv T dir treeDir project tree root modules roots todo w) :
    ∀ x ∈ w.sources, Named T project tree root modules x.1 ∧ FileOfModule root modules x.1 x.2.path ∧
      SourceText T project tree x.2.path x.2.text := fun x hx => by
  obtain ⟨p, h1, ⟨rel, _, _, hrel, -, -, hpath, ht, -, hsub⟩, h3⟩ := I.sources x hx
  subst hpath
  exact ⟨I.named _ h3, fileOf_mem h1, rel, hrel, ht ▸ hsub.subset (by simp [under, joinParts])⟩

private theorem clean_notFound {path : FilePath} {e : IO.Error}
    (h : ∃ name code details, e = .noFileOrDirectory name code details) :
    Clean ([⟨.symlinkMetadata path, .error e⟩] : List (Event L E)) := by
  obtain ⟨name, code, details, rfl⟩ := h
  exact clean_one (by rintro ⟨_, hx, hne⟩; cases hx; exact hne _ _ _ rfl)

theorem readFiles_spec {T prior t : List (Event L E)} {dir treeDir project tree : FilePath} {root : Root L}
    {modules : List (Name × FilePath)} {cfg : ClosedConfig} {sysroot text : String} {log : List String}
    {b : Except String (Stage × List (Name × Source))} (hT : t.Sublist T)
    (hp : Prior T dir treeDir project tree text cfg.keys)
    (hsys : SysrootIs T sysroot)
    (hcopies : (configWrites tree text ++ t : List (Event L E)).Sublist T)
    (hload : (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ T)
    (hprepared : PreparedLoad T dir treeDir sysroot tree (.ok (some root, log)))
    (hmods : DefaultModules T root root.defaultTargets modules)
    (hprior : DefaultModules prior root root.defaultTargets modules)
    (hopen : openPathsOf tree root = [])
    (hunread : configUnread tree root modules = [])
    (h : Runs (readFiles [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] project tree root modules
      cfg : Attempt L E _).run t b) :
    (∀ s srcs, b = .ok (s, srcs) → ReadGoal T dir treeDir (Holds tree text srcs) s.toReading ∧
      (s.outcome = .admitted → AdmittedActs tree t (srcs.map fun x => (x.2.path, x.2.text)) (planOf tree text srcs) ∧
        twoTexts (plannedOf [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] srcs) = [] ∧ Clean t)) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧ ReadingLoaded prior project tree root t := by
  rw [readFiles] at h
  have hTL : TreeLoaded T dir treeDir tree root := ⟨hp.tree_real, sysroot, log, hsys, hload, hprepared⟩
  have hscene : Scene T dir treeDir project tree root modules := ⟨hp.project_real, hTL, hmods⟩
  obtain ⟨t₅, t₆, r₅, rfl, h₆, h₇⟩ := runs_attempt_bind_iff.mp h
  have hT₆ := (List.sublist_append_right _ _).trans hT
  obtain ⟨w, h₈, rfl⟩ := runs_lift_iff.mp h₆
  have hinit {T' : List (Event L E)} : WalkInv T' dir treeDir project tree root modules (modules.map (·.1)) (modules.map (·.1)) {} :=
    { sources := by simp, held := by simp, nodup := by simp, reached := by simp, closed := by simp,
      named := by simp, todoNamed := fun m hm => .root hm, unread := by simp,
      visited := fun _ _ hn => by rcases hn with hn | ⟨_, hx, -⟩; exact .inl hn; cases hx }
  obtain ⟨I, hobs, hcount⟩ := walk_spec (roots := modules.map (·.1)) 1000000 (modules.map (·.1)) {} t₅ w
    h₈ ((List.sublist_append_left _ _).trans hT) (by simp) (by simp [sourceImports]) hinit
  obtain ⟨I', -, -⟩ := walk_spec (T := prior ++ t₅) (roots := modules.map (·.1)) 1000000 (modules.map (·.1)) {} t₅ w
    h₈ (List.sublist_append_right _ _) (by simp) (by simp [sourceImports]) hinit
  have hgram {u} (hu : ModuleCopies project tree root modules (prior ++ t₅) u) :
      ReadingLoaded prior project tree root (t₅ ++ u) :=
    .inr ⟨[], _, modules, rfl, quiet_nil, by simpa using hprior,
      by simpa using (ModuleCopies.observations (modules := modules) (project := project) (tree := tree) prior hobs).append hu⟩
  have hfacts := configUnread_nil hunread
  have hfacts' := source_facts I
  have hsrc : ∀ z ∈ w.sources.reverse, Named T project tree root modules z.1 ∧
      FileOfModule root modules z.1 z.2.path ∧ SourceText T project tree z.2.path z.2.text :=
    fun z hz => hfacts' z (List.mem_reverse.mp hz)
  obtain ⟨_, _, _, _, _, htomlRead, _, _⟩ := hp.toml
  dsimp only at h₇
  split at h₇
  · rename_i hu
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₇
    refine ⟨fun _ _ he => ?_, by simp, by simpa using hgram .nil⟩
    cases he
    refine Stage.early (by simp [Stage.outcome]) ?_
    have hne : w.unread.reverse ++ twoTexts (plannedOf [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] w.sources.reverse) ≠ [] := by
      intro hnil; simp [hnil] at hu
    by_cases hwu : w.unread = []
    · obtain ⟨x, hx, y, hy, hxy, hne'⟩ := twoTexts_cons (by simpa [hwu] using hne)
      have hmem {z} (hz : z ∈ plannedOf [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] w.sources.reverse) :
          z.2 ∈ planOf tree text w.sources.reverse := by
        rw [← plannedOf_map]; exact List.mem_map.mpr ⟨z, hz, rfl⟩
      exact .twoTexts hscene (planned_of_mem htomlRead hsrc (hmem hx)) (planned_of_mem htomlRead hsrc (hmem hy)) hxy hne'
    · exact I.unread hwu hscene
  · rename_i hu
    have hnil : w.unread = [] ∧
        twoTexts (plannedOf [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] w.sources.reverse) = [] := by
      simpa [List.isEmpty_iff, List.append_eq_nil_iff] using hu
    obtain ⟨hwu, htwo⟩ := hnil
    obtain ⟨-, hclean₅, hcount'⟩ := hcount hwu
    split at h₇
    · rename_i hm
      obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₇
      refine ⟨fun _ _ he => ?_, by simp, by simpa using hgram .nil⟩
      cases he
      obtain ⟨m, hm', hroot⟩ := List.any_eq_true.mp hm
      exact Stage.early (by simp [Stage.outcome]) (.mathlib hscene (I.named m (List.mem_reverse.mp hm')) (by simpa using hroot))
    · rename_i hm
      obtain ⟨t₇, t₈, r₇, rfl, h₉, h₁₀⟩ := runs_attempt_bind_iff.mp h₇
      have hT₇ := (List.sublist_append_left _ _).trans hT₆
      have hT₈ := (List.sublist_append_right _ _).trans hT₆
      obtain ⟨p1, p2, p3⟩ := parseFiles_spec root w.sources.reverse w.toolchain w.sources.reverse [] hT₇ (by simp) h₉
      have hobs₇ : ModuleCopies project tree root modules (prior ++ t₅) t₇ := .observations _ p3
      cases r₇ with
      | error why =>
        obtain ⟨rfl, rfl⟩ := h₁₀; obtain ⟨mods, x, hx, hn⟩ := p2 ⟨why, rfl⟩
        exact ⟨by simp, fun _ => .failed (hT₇.subset hx)
            (.parser hscene fun n hm' => ⟨(I.held n (hn n hm')).2.2.2.2, (I.held n (hn n hm')).2.1⟩) ⟨x, rfl⟩,
          by simpa using hgram hobs₇⟩
      | ok files =>
        obtain ⟨g1, g2, hclean₇⟩ := p1 files rfl
        have hgoal := ofFiles_goal hp hsys hload hprepared hmods hopen hfacts I hwu hcount' hm g1 g2
        dsimp only at h₁₀
        split at h₁₀
        · rename_i cfg' roots' reached' files' hm' hcov' hadm' hst
          obtain ⟨t₉, t₁₀, r₉, rfl, h₁₁, h₁₂⟩ := runs_attempt_bind_iff.mp h₁₀
          obtain ⟨s1, s2, s3⟩ := writeSources_spec (project := project) (root := root) (modules := modules)
            (prior := prior ++ t₅ ++ t₇) (fun x hx =>
              let f := source_facts I' x (List.mem_reverse.mp hx)
              ⟨Named.mono (List.sublist_append_left _ _) f.1, f.2.1, SourceText.mono (List.sublist_append_left _ _) f.2.2⟩) h₁₁
          have hT₉ := (List.sublist_append_left _ _).trans hT₈
          have hcopied : ModuleCopies project tree root modules (prior ++ t₅) (t₇ ++ t₉) := hobs₇.append s3
          cases r₉ with
          | error why =>
            obtain ⟨rfl, rfl⟩ := h₁₂
            refine ⟨by simp, fun _ => ?_, by simpa [List.append_assoc] using hgram hcopied⟩
            obtain ⟨x, hx, hh⟩ := s2 ⟨why, rfl⟩; obtain ⟨h1, h2, h3⟩ := hfacts' x (List.mem_reverse.mp hx)
            rcases hh with h' | ⟨e, he, hbad, ⟨d, hd', hop⟩ | hop⟩
            · exact .moduleNotInTree hscene h1 h2 h'
            · exact .failed (hT₉.subset he) (by rw [hop]; exact .sourceParent hscene h1 h2 hd') hbad
            · exact .failed (hT₉.subset he) (by rw [hop]; exact .sourceWrite hscene h1 h2 h3) hbad
          | ok _ =>
            obtain ⟨t₁₁, t₁₂, r₁₁, rfl, h₁₃, h₁₄⟩ := runs_attempt_bind_iff.mp h₁₂
            obtain ⟨b1, b2, b3⟩ := readBack_spec h₁₃
            obtain ⟨w1, w2, w3, hclean₉⟩ := s1 rfl
            have hgram' {u} (hq : Quiet u) : ReadingLoaded prior project tree root (t₅ ++ (t₇ ++ (t₉ ++ u))) := by
              simpa [List.append_assoc] using hgram (hcopied.append (.observations _ (hq.observes root)))
            cases r₁₁ with
            | error why =>
              obtain ⟨rfl, rfl⟩ := h₁₄
              refine ⟨by simp, fun _ => ?_, by simpa [List.append_assoc] using hgram' b3⟩
              obtain ⟨x, hx, r', hmx, hne⟩ := b2 ⟨why, rfl⟩
              refine .treeDiffers hscene (planned_of_mem htomlRead hsrc hx) ?_ hne
              rcases List.mem_append.mp hx with hx | hx
              · refine (pair_sublist (a := configWrites tree text) (b := _) (y := ⟨.readFile x.1, r'⟩) ?_ (by simp [hmx])).trans hcopies
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> simp
              · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
                exact (pair_sublist (w3 y hy) hmx).trans (by simpa using hT₈)
            | ok _ =>
              obtain ⟨t₂₁, t₂₂, r₂₁, rfl, h₂₁, h₂₂⟩ := runs_attempt_bind_iff.mp h₁₄
              obtain ⟨r₂, rfl, n1, n2⟩ := noOtherConfig_spec h₂₁
              have hq₂ : Quiet ([⟨.symlinkMetadata (tree / "lakefile.lean"), r₂⟩] : List (Event L E)) := quiet_one trivial
              cases r₂₁ with
              | error why =>
                obtain ⟨rfl, rfl⟩ := h₂₂
                refine ⟨by simp, fun _ => ?_, by simpa [List.append_assoc] using hgram' (b3.append hq₂)⟩
                have hmem : (⟨.symlinkMetadata (tree / "lakefile.lean"), r₂⟩ : Event L E) ∈ T :=
                  hT₈.subset (by simp)
                rcases n2 ⟨why, rfl⟩ with ⟨_, rfl⟩ | hbad
                · exact .configShadowed hp.tree_real hmem
                · exact .failed hmem (.treeLeanConfig hp.tree_real) hbad
              | ok _ =>
                obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂₂
                refine ⟨fun _ _ he => ?_, by simp, by simpa [List.append_assoc] using hgram' (b3.append hq₂)⟩
                cases he
                refine ⟨hgoal, fun _ => ⟨?_, htwo, ?_⟩⟩
                · have hbq : Quiet (t₁₁ ++ [⟨.symlinkMetadata (tree / "lakefile.lean"), r₂⟩] ++ ([] : List (Event L E))) := by
                    simpa using Quiet.append b3 hq₂
                  have hback : AdmittedActs tree (t₁₁ ++ [⟨.symlinkMetadata (tree / "lakefile.lean"), r₂⟩] ++ ([] : List (Event L E)))
                      [] (planOf tree text w.sources.reverse) :=
                    { leaves := by simpa using leavesAs_nil_of_no_act hbq.noActs
                      writesIn := by simpa using writesIn_nil_of_no_act hbq.noActs
                      back := by
                        obtain ⟨e, rfl, hn⟩ := n1 rfl
                        exact ⟨[], t₁₁ ++ [⟨.symlinkMetadata (tree / "lakefile.lean"), .error e⟩] ++ [], by simp,
                          by simpa using hbq, fun x hx => by simp [(b1 rfl).1 x hx], e, by simp, hn⟩ }
                  have hnoacts : ∀ e ∈ (t₅ ++ t₇ : List (Event L E)), e.acted? = none := fun e he => by
                    rcases List.mem_append.mp he with he | he
                    · exact hobs.noActs e he
                    · exact p3.noActs e he
                  simpa [List.append_assoc] using (hback.prepend w1 w2).prepend
                    (leavesAs_nil_of_no_act hnoacts) (writesIn_nil_of_no_act hnoacts)
                · obtain ⟨e, rfl, habs⟩ := n1 rfl
                  simpa [List.append_assoc] using hclean₅.append (hclean₇.append (hclean₉.append ((b1 rfl).2.append (clean_notFound habs))))
        · rename_i hnadm
          obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₁₀
          refine ⟨fun _ _ he => ?_, by simp, by simpa using hgram hobs₇⟩
          cases he
          refine ⟨hgoal, fun ha => ?_⟩
          cases hst : Stage.ofFiles cfg (modules.map (·.1)) w.reached.reverse files hm <;>
            first | exact absurd hst (hnadm _ _ _ _ _ _ _) | (rw [hst] at ha; cases ha)

theorem openPaths_reason {T : List (Event L E)} {dir treeDir tree : FilePath} {root : Root L}
    (hload : TreeLoaded T dir treeDir tree root) (h : openPathsOf tree root ≠ []) : Reason T dir treeDir .refused := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h
  simp only [openPathsOf, List.mem_append, List.mem_map, List.mem_eraseDups, List.mem_filter] at hx
  rcases hx with (⟨d, ⟨hd, hn⟩, -⟩ | ⟨lib, ⟨hl, hn⟩, -⟩) | ⟨target, ⟨ht, hn⟩, -⟩
  · refine .openDir hload hd fun rel hr => Classical.byContradiction fun hall => ?_
    have := (closedSourceDir_iff tree d).mpr ⟨rel, hr, fun c hc => Classical.byContradiction fun hbad => hall ⟨c, hc, hbad⟩⟩
    simp [this] at hn
  · simp only [Bool.not_eq_true', List.all_eq_false] at hn
    obtain ⟨g, hg, hs⟩ := hn
    exact .openGlob hload hl hg fun n he => by subst he; simp at hs
  · exact .notLibrary hload ht (by simpa [Option.isNone_iff_eq_none] using hn)

/-- A default target that is no library keeps a project from admission: a default executable, such as the one of the {lit}`lake new` application
template, or a name of no target. The owner named this refusal on 2026-11-01. -/
theorem openPaths_of_notLibrary {tree : FilePath} {root : Root L} {target : Name} (ht : target ∈ root.defaultTargets)
    (hn : root.findLib target = none) : openPathsOf tree root ≠ [] := fun h => by
  have := (openPathsOf_nil h).2.2 target ht; simp [hn] at this

theorem openPaths_of_openDir {tree d : FilePath} {root : Root L} (hd : d ∈ root.sourceDirs)
    (hn : closedSourceDir tree d = false) : openPathsOf tree root ≠ [] := fun h => by
  have := (closedSourceDir_iff tree d).mpr ((openPathsOf_nil h).1 d hd); simp [this] at hn

theorem closedSourceDir_of_char {tree d : FilePath} {rel : List String} {c : String} {ch : Char}
    (hr : TreeRelative (parts tree) (parts d) rel) (hc : c ∈ rel) (hch : ch ∈ c.toList) (hbad : ¬ ClosedChar ch) :
    closedSourceDir tree d = false := by
  cases h : closedSourceDir tree d with
  | false => rfl
  | true =>
    obtain ⟨rel', hr', hall⟩ := (closedSourceDir_iff tree d).mp h
    have : rel' = rel := List.append_cancel_left (hr'.1.symm.trans hr.1)
    subst this; exact absurd ((hall c hc).2 ch hch) hbad

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
  · exact .targetName hscene.loaded hn fun hclosed => by simp [(closedModuleName_iff n).mpr hclosed] at hc
  · exact .rootElsewhere (m := y.1) (file := y.2) hscene hy fun other hres => by simpa only [hres, bne_iff_ne] using hr
  · obtain ⟨⟨m, file⟩, hmf, hin⟩ := List.mem_flatMap.mp hy
    have hfile : FileOfModule root modules m y.2 := by
      rcases List.mem_cons.mp hin with rfl | hin
      · exact .inl hmf
      · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hin; exact .inr (by simpa [Option.mem_toList] using ho)
    have hout : OutsideTree tree y.2 := by
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at hr
      rcases hr with hn | hn
      · exact .inl fun rel hrel => by rw [(inTree_iff tree y.2).mpr ⟨rel, hrel⟩] at hn; cases hn
      · cases hd : y.2.parent with
        | none => simp [parentInTree, hd] at hn
        | some d =>
          rw [parentInTree, hd] at hn; dsimp only at hn
          exact .inr ⟨d, hd, fun rel hrel => by rw [(inTree_iff tree d).mpr ⟨rel, hrel⟩] at hn; cases hn⟩
    exact .moduleNotInTree hscene (.root (List.mem_map.mpr ⟨(m, file), hmf, rfl⟩)) hfile hout

theorem readRoot_spec {T prior t : List (Event L E)} {dir treeDir project tree : FilePath} {cfg : ClosedConfig}
    {sysroot text : String} {b : Except String (Stage × List (Name × Source))} (hT : t.Sublist T)
    (hsys : SysrootIs T sysroot)
    (hcopies : (configWrites tree text ++ t : List (Event L E)).Sublist T)
    (hp : Prior T dir treeDir project tree text cfg.keys)
    (hprepared : ∀ response rest, t = ⟨.loadRoot sysroot tree, response⟩ :: rest →
      PreparedLoad T dir treeDir sysroot tree response)
    (h : Runs (readRoot [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] sysroot project tree cfg :
      Attempt L E _).run t b) :
    (∀ s srcs, b = .ok (s, srcs) → ReadGoal T dir treeDir (Holds tree text srcs) s.toReading ∧
      (s.outcome = .admitted → AdmittedActs tree t (srcs.map fun x => (x.2.path, x.2.text)) (planOf tree text srcs) ∧
        twoTexts (plannedOf [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] srcs) = [] ∧ Clean t)) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧ ReadingLoad prior sysroot project tree t := by
  rw [readRoot] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨t₃, t₄, r₃, rfl, h₃, h₄⟩ := runs_bind_iff.mp h₁
  obtain rfl := runs_call_iff.mp h₃; obtain ⟨rfl, rfl⟩ := runs_done_iff.mp h₄
  have hT' : (([⟨.loadRoot sysroot tree, r₃⟩] : List (Event L E)) ++ t₂).Sublist T := by simpa using hT
  have hT₂ := (List.sublist_append_right _ _).trans hT
  have hmem₁ : (⟨.loadRoot sysroot tree, r₃⟩ : Event L E) ∈ T := hT'.subset (by simp)
  have hready := hprepared r₃ t₂ (by simp)
  cases r₃ with
  | error e =>
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨by simp, fun _ => .load hready (.inl ⟨e, rfl⟩), .inr ⟨[], .error e, [], by simp, quiet_nil, quiet_nil⟩⟩
  | ok v =>
    obtain ⟨o, log⟩ := v
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨by simp, fun _ => .load hready (.inr ⟨log, rfl⟩), .inr ⟨[], .ok (none, log), [], by simp, quiet_nil, quiet_nil⟩⟩
    | some root =>
      have hgram {u : List (Event L E)} (hu : ReadingLoaded (prior ++ [] ++ [⟨.loadRoot sysroot tree, .ok (some root, log)⟩]) project tree root u) :
          ReadingLoad prior sysroot project tree ([⟨.loadRoot sysroot tree, .ok (some root, log)⟩] ++ u) :=
        .inr ⟨[], .ok (some root, log), u, by simp, quiet_nil, hu⟩
      have hTL : TreeLoaded T dir treeDir tree root := ⟨hp.tree_real, sysroot, log, hsys, hmem₁, hready⟩
      dsimp only [loaded] at h₂
      split at h₂
      · rename_i hopen
        obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂
        refine ⟨fun _ _ he => ?_, by simp, by simpa using hgram (u := []) (.inl quiet_nil)⟩
        cases he
        exact Stage.early (by simp [Stage.mkOpenPaths, Stage.outcome]) (openPaths_reason hTL (by intro hnil; simp [hnil] at hopen))
      · rename_i hopen
        obtain ⟨t₅, t₆, r₅, rfl, h₅, h₆⟩ := runs_attempt_bind_iff.mp h₂
        have hT₅ := (List.sublist_append_left _ _).trans hT₂
        have hT₆ := (List.sublist_append_right _ _).trans hT₂
        obtain ⟨m1, m2, m3⟩ := defaultModules_spec (T := T) root root.defaultTargets hT₅.subset h₅
        obtain ⟨m1', -, -⟩ := defaultModules_spec (T := prior ++ [] ++ [⟨.loadRoot sysroot tree, .ok (some root, log)⟩] ++ t₅)
          root root.defaultTargets (fun _ he => List.mem_append_right _ he) h₅
        cases r₅ with
        | error why =>
          obtain ⟨rfl, rfl⟩ := h₆; obtain ⟨tg, lib, x, hg, hl', hx⟩ := m2 ⟨why, rfl⟩
          exact ⟨by simp, fun _ => .failed (hT₅.subset hx) (.library hTL hg hl') ⟨x, rfl⟩,
            by simpa using hgram (u := t₅) (.inl m3)⟩
        | ok modules =>
          obtain ⟨hmods, hclean₅⟩ := m1 modules rfl
          dsimp only at h₆
          split at h₆
          · rename_i hfails
            obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₆
            refine ⟨fun _ _ he => ?_, by simp, by simpa using hgram (u := t₅) (.inl m3)⟩
            cases he
            exact Stage.early (by simp [Stage.outcome]) (configUnread_reason ⟨hp.project_real, hTL, hmods⟩ (by intro hnil; simp [hnil] at hfails))
          · rename_i hfails
            have hcopies₆ : (configWrites tree text ++ t₆ : List (Event L E)).Sublist T :=
              List.Sublist.trans (List.Sublist.append_left (by simp) _) hcopies
            obtain ⟨f1, f2, f3⟩ := readFiles_spec hT₆ hp hsys hcopies₆ hmem₁ hready hmods (m1' modules rfl).1
              (List.isEmpty_iff.mp hopen) (List.isEmpty_iff.mp hfails) h₆
            refine ⟨fun s srcs he => ?_, f2, by simpa using hgram (u := t₅ ++ t₆) (f3.prepend m3)⟩
            obtain ⟨g1, g2⟩ := f1 s srcs he
            refine ⟨g1, fun ha => ?_⟩
            obtain ⟨l1, l2, l3⟩ := g2 ha
            have hno : ∀ e ∈ ([⟨.loadRoot sysroot tree, .ok (some root, log)⟩] ++ [] ++ t₅ : List (Event L E)), e.acted? = none := fun e he' => by
              simp only [List.append_nil, List.mem_append, List.mem_singleton] at he'
              exact he'.elim (· ▸ rfl) (m3.noActs e)
            have hloadC : Clean ([⟨.loadRoot sysroot tree, .ok (some root, log)⟩] : List (Event L E)) :=
              clean_one (by rintro (⟨_, hx⟩ | ⟨_, hx⟩) <;> cases hx)
            exact ⟨by simpa [List.append_assoc] using l1.prepend (leavesAs_nil_of_no_act hno) (writesIn_nil_of_no_act hno),
              l2, by simpa [List.append_assoc] using hloadC.append (hclean₅.append l3)⟩

/-- What the stages before the configuration established, by the events {name}`T`. -/
structure Early (T : List (Event L E)) (dir treeDir project tree : FilePath) (tf : Option String) : Prop where
  /-- The project's real path. -/
  project_real : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ T
  /-- The tree's real path. -/
  tree_real : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ T
  /-- They lie apart. -/
  apart : Apart project tree
  /-- What {lit}`lean-toolchain` said, when it is the pinned Lean. -/
  toolchain : tf = some leanToolchain → ∃ text real,
    (⟨.readFile (project / "lean-toolchain"), .ok text⟩ : Event L E) ∈ T ∧
    (⟨.realPath (project / "lean-toolchain"), .ok real⟩ : Event L E) ∈ T ∧
    parts real = parts (project / "lean-toolchain") ∧
    parts project <+: parts (project / "lean-toolchain") ∧
    text.trimAscii.toString = leanToolchain
  /-- Why anything else is refused. -/
  toolchain_reason : tf ≠ some leanToolchain → Reason T dir treeDir .refused

theorem ofConfig_spec {T : List (Event L E)} {dir treeDir project tree : FilePath} {tf : Option String}
    {table : Lake.Toml.Table} (hE : Early T dir treeDir project tree tf) (htoml : TomlRead T dir table) :
    (∀ s, Stage.ofConfig tf (keysOf 8 .anonymous table) = .error s →
      s.outcome ≠ .admitted ∧ Reason T dir treeDir s.outcome) ∧
    (∀ cfg, Stage.ofConfig tf (keysOf 8 .anonymous table) = .ok cfg →
      tf = some leanToolchain ∧ cfg.keys = keysOf 8 .anonymous table) := by
  unfold Stage.ofConfig
  split
  · rename_i hc
    refine ⟨fun s hs => ?_, fun _ hs => (by cases hs)⟩
    cases hs
    refine ⟨by simp [Stage.outcome], ?_⟩
    by_cases ht : tf = some leanToolchain
    · simp only [configIsClosed, configKeysClosed, ht, beq_self_eq_true, Bool.not_false,
        List.isEmpty_nil, Bool.true_and, Bool.and_true, List.all_eq_false] at hc
      obtain ⟨k, hk, hbad⟩ := hc
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hbad
      obtain ⟨hroot, hna⟩ := hbad
      rcases keysOf_sound 8 .anonymous table k hk with h' | h'
      · exact .key htoml h' hroot fun ha => hna ((configKeyAdmitted_iff k).mpr ha)
      · exact .deep htoml h'
    · exact hE.toolchain_reason ht
  · rename_i hc
    split
    · rename_i hr
      refine ⟨fun s hs => ?_, fun _ hs => (by cases hs)⟩
      cases hs
      refine ⟨by simp [Stage.outcome], ?_⟩
      obtain ⟨k, hk, hroot⟩ := List.any_eq_true.mp hr
      rcases keysOf_sound 8 .anonymous table k hk with h' | h'
      · exact .dependency htoml h' (by simpa using hroot)
      · exact .deepDependency htoml h'
    · refine ⟨fun _ hs => (by cases hs), fun cfg hs => ?_⟩
      cases hs
      simp only [configIsClosed, Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨hc.1.1.1, rfl⟩

theorem readKeys_spec {T prior t : List (Event L E)} {dir treeDir project tree : FilePath} {tf : Option String}
    {sysroot text : String} {real : FilePath} {b : Except String (Stage × List (Name × Source))}
    (hI : t <:+: T) (hsys : SysrootIs T sysroot) (hE : Early T dir treeDir project tree tf)
    (habs : ∃ e, (⟨.symlinkMetadata (project / "lakefile.lean"), .error e⟩ : Event L E) ∈ T ∧
      ∃ name code details, e = .noFileOrDirectory name code details)
    (hreal : (⟨.realPath (project / "lakefile.toml"), .ok real⟩ : Event L E) ∈ T)
    (hexact : parts real = parts (project / "lakefile.toml") ∧
      parts project <+: parts (project / "lakefile.toml"))
    (hread : (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ T)
    (h : Runs (readKeys sysroot project tree tf text : Attempt L E _).run t b) :
    (∀ s srcs, b = .ok (s, srcs) → ReadGoal T dir treeDir (Holds tree text srcs) s.toReading ∧
      (s.outcome = .admitted → Holds tree text srcs (written t) ∧ ReadBack t tree ∧ Clean t ∧ tf = some leanToolchain)) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧
      ConfigCopies sysroot project tree [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)] prior t := by
  have hT := hI.sublist
  rw [readKeys] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r₂, h₃, rfl⟩ := runs_lift_iff.mp h₁; obtain rfl := runs_call_iff.mp h₃
  have hT' : (([⟨.parseToml (mkInputContext text "lakefile.toml"), r₂⟩] : List (Event L E)) ++ t₂).Sublist T := by simpa using hT
  have hT₂ := (List.sublist_append_right _ _).trans hT'
  have hmem : (⟨.parseToml (mkInputContext text "lakefile.toml"), r₂⟩ : Event L E) ∈ T := hT'.subset (by simp)
  have hq : Quiet ([⟨.parseToml (mkInputContext text "lakefile.toml"), r₂⟩] : List (Event L E)) := quiet_one trivial
  cases r₂ with
  | error log =>
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂
    exact ⟨fun _ _ he => by cases he; exact earlyUnread_early hE.toolchain_reason (.failed hmem (.tomlParse hE.project_real hread) ⟨log, rfl⟩),
      by simp, .stopped (by simpa using hq)⟩
  | ok table =>
    dsimp only at h₂
    have hcfg := ofConfig_spec hE ⟨project, text, hE.project_real, hread, hmem⟩
    cases ho : Stage.ofConfig tf (keysOf 8 .anonymous table) with
    | error stage =>
      rw [ho] at h₂; obtain ⟨hne, hrea⟩ := hcfg.1 stage ho
      obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂
      exact ⟨fun _ _ he => by cases he; exact Stage.early hne hrea, by simp, .stopped (by simpa using hq)⟩
    | ok cfg =>
      rw [ho] at h₂; obtain ⟨hto, hkeys⟩ := hcfg.2 cfg ho
      obtain ⟨t₃, t₄, r₃, rfl, h₄, h₅⟩ := runs_attempt_bind_iff.mp h₂
      have hT₃ := (List.sublist_append_left _ _).trans hT₂
      have hT₄ := (List.sublist_append_right _ _).trans hT₂
      have w := writeInTree_spec h₄
      have hwriteFail {path text'} {t' : List (Event L E)} (hs : t'.Sublist T)
          (hp : path = tree / "lakefile.toml" ∨ path = tree / "lean-toolchain")
          (hw : ∀ {o : Op L E}, o = .writeFile path text' → Needed T dir treeDir o)
          (h' : OutsideTree tree path ∨ ∃ e ∈ t', Event.failed e ∧
            ((∃ d, path.parent = some d ∧ e.op = .createDirAll d) ∨ e.op = .writeFile path text')) :
          Reason T dir treeDir .incomplete := by
        rcases h' with h' | ⟨e, he, hf, ⟨d, hd, hop⟩ | hop⟩
        · exact .configNotInTree hE.tree_real hp h'
        · exact .failed (hs.subset he) (by rw [hop]; exact .copyParent hE.tree_real hp hd) hf
        · exact .failed (hs.subset he) (hw hop) hf
      cases r₃ with
      | error why =>
        obtain ⟨rfl, rfl⟩ := h₅
        exact ⟨by simp, fun _ => hwriteFail hT₃ (.inl rfl) (fun ho => by rw [ho]; exact .copyToml hE.project_real hE.tree_real hread) (w.incomplete rfl),
          by simpa using ConfigCopies.failed (rest := []) hq w quiet_nil⟩
      | ok _ =>
        obtain ⟨t₅, t₆, r₅, rfl, h₆, h₇⟩ := runs_attempt_bind_iff.mp h₅
        have hT₅ := (List.sublist_append_left _ _).trans hT₄
        have hT₆ := (List.sublist_append_right _ _).trans hT₄
        have v := writeInTree_spec h₆
        cases r₅ with
        | error why =>
          obtain ⟨rfl, rfl⟩ := h₇
          refine ⟨by simp, fun _ => hwriteFail hT₅ (.inr rfl) (fun ho => by rw [ho]; exact .copyToolchain hE.tree_real) (v.incomplete rfl), ?_⟩
          simpa using ConfigCopies.next hq (show CopyStep tree _ text t₃ true from w)
            (ConfigCopies.failed (before := []) (rest := []) quiet_nil v quiet_nil)
        | ok _ =>
          obtain ⟨⟨before, hb, hbd⟩, hout₁⟩ := w.complete rfl
          obtain ⟨⟨between, hm, hmd⟩, hout₂⟩ := v.complete rfl
          have hp : Prior T dir treeDir project tree text cfg.keys :=
            { project_real := hE.project_real, tree_real := hE.tree_real, apart := hE.apart,
              toolchain := hE.toolchain hto, absent := habs,
              toml := ⟨real, table, hreal, hexact.1, hexact.2, hread, hmem, hkeys⟩,
              copyToml := hout₁, copyToolchain := hout₂ }
          have hprepared : ∀ response rest, t₆ = ⟨.loadRoot sysroot tree, response⟩ :: rest →
              PreparedLoad T dir treeDir sysroot tree response := fun response rest ht₆ => by
            obtain ⟨toolchain, _, htc, _, _, _, htcText⟩ := hE.toolchain hto
            refine ⟨project, text, toolchain, between, hE.project_real, hE.tree_real, hsys, hread, htc, htcText, ?_, hmd⟩
            exact List.IsInfix.trans ⟨[⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩] ++ before, rest,
              by simp [hb, hm, ht₆, List.append_assoc]⟩ hI
          have hsub₃ : ([⟨.writeFile (tree / "lakefile.toml") text, .ok ()⟩] : List (Event L E)).Sublist t₃ := by rw [hb]; simp
          have hsub₅ : ([⟨.writeFile (tree / "lean-toolchain") leanToolchain, .ok ()⟩] : List (Event L E)).Sublist t₅ := by rw [hm]; simp
          have hcopies : (configWrites tree text ++ t₆ : List (Event L E)).Sublist T :=
            List.Sublist.trans (by simpa using hsub₃.append (hsub₅.append (List.Sublist.refl t₆))) hT₂
          obtain ⟨f1, f2, f3⟩ := readRoot_spec (prior := prior ++ [⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩] ++ t₃ ++ [] ++ t₅)
            hT₆ hsys hcopies hp hprepared h₇
          refine ⟨fun s srcs he => ?_, f2, ?_⟩
          · obtain ⟨g1, g2⟩ := f1 s srcs he
            refine ⟨g1, fun ha => ?_⟩
            obtain ⟨l1, l2, l3⟩ := g2 ha
            have hA : AdmittedActs tree ([⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩] ++ (t₃ ++ (t₅ ++ t₆)))
                (planOf tree text srcs) (planOf tree text srcs) :=
              (((l1.prepend (hm ▸ leavesAs_write hmd) (hm ▸ writesIn_write hmd)).prepend
                (hb ▸ leavesAs_write hbd) (hb ▸ writesIn_write hbd)).prepend
                (leavesAs_nil_of_no_act hq.noActs) (writesIn_nil_of_no_act hq.noActs)).cast (by simp [planOf])
            have hCl : Clean ([⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩] ++ (t₃ ++ (t₅ ++ t₆))) :=
              (by clean_events : Clean _).append ((w.clean rfl).append ((v.clean rfl).append l3))
            simpa using ⟨holds_of_leavesAs hA.leaves l2, hA.readBack, hCl, hto⟩
          · simpa [List.append_assoc] using ConfigCopies.next hq (show CopyStep tree _ text t₃ true from w)
              (ConfigCopies.next quiet_nil (show CopyStep tree _ _ t₅ true from v) (.done f3))

theorem readConfig_spec {T prior t : List (Event L E)} {dir treeDir project tree : FilePath} {tf : Option String}
    {sysroot : String} {b : Except String (Stage × List (Name × Source))} (hI : t <:+: T)
    (hsys : SysrootIs T sysroot) (hE : Early T dir treeDir project tree tf) (hq : Quiet prior)
    (hpp : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ prior) (hpt : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ prior)
    (hps : SysrootIs prior sysroot)
    (h : Runs (readConfig sysroot project tree tf : Attempt L E _).run t b) :
    (∀ s srcs, b = .ok (s, srcs) → ∃ text, ReadGoal T dir treeDir (Holds tree text srcs) s.toReading ∧
      (s.outcome = .admitted → Holds tree text srcs (written t) ∧ ReadBack t tree ∧ Clean t ∧ tf = some leanToolchain)) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧ ReadingPreparation (prior ++ t) dir treeDir := by
  have hT := hI.sublist
  rw [readConfig] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r₃, rfl, e1, e2, e3⟩ := existsByName_spec h₁
  have hmem : (⟨.symlinkMetadata (project / "lakefile.lean"), r₃⟩ : Event L E) ∈ T := hT.subset (by simp)
  have hT₂ := (List.sublist_append_right _ _).trans hT
  have hq₁ : Quiet ([⟨.symlinkMetadata (project / "lakefile.lean"), r₃⟩] : List (Event L E)) := quiet_one trivial
  cases r₁ with
  | error why =>
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨by simp, fun _ => .failed hmem (.leanConfig hE.project_real) (e3 ⟨why, rfl⟩), .inl (by simpa using hq.append hq₁)⟩
  | ok present =>
    cases present with
    | true =>
      obtain ⟨_, rfl⟩ := e1 rfl; obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂
      exact ⟨fun _ _ he => by cases he; exact ⟨"", Stage.early (by simp [Stage.mkLeanConfig, Stage.outcome]) (.leanConfig hE.project_real hmem)⟩,
        by simp, .inl (by simpa using hq.append hq₁)⟩
    | false =>
      obtain ⟨e, rfl, habs⟩ := e2 rfl
      obtain ⟨t₃, t₄, r₃', rfl, h₃, h₄⟩ := runs_attempt_bind_iff.mp h₂
      obtain ⟨r₅, h₅, rfl⟩ := runs_lift_iff.mp h₃
      obtain ⟨x1, x2, x3⟩ := readExact_spec h₅
      have hT₃ := (List.sublist_append_left _ _).trans hT₂
      have hq₂ := (hq.append hq₁).append x3
      cases r₅ with
      | error why =>
        obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₄
        refine ⟨fun _ _ he => ?_, by simp, .inl (by simpa [List.append_assoc] using hq₂)⟩
        cases he
        refine ⟨"", earlyUnread_early hE.toolchain_reason ?_⟩
        rcases x2 ⟨why, rfl⟩ with ⟨y, hy, hf, hop | hop⟩ | ⟨real, rfl, hb⟩
        · exact .failed (hT₃.subset hy) (by rw [hop]; exact .tomlReal hE.project_real) hf
        · exact .failed (hT₃.subset hy) (by rw [hop]; exact .tomlRead hE.project_real) hf
        · exact .tomlNotExact hE.project_real (hT₃.subset (by simp)) ((exactBelow_eq_false_iff _ _ _).mp hb)
      | ok text =>
        obtain ⟨real, rfl, hb⟩ := x1 text rfl
        have hex := (RegulaSpecification.Loader.exactBelow_iff _ _ _).mp hb
        have hI₄ : t₄ <:+: T := (List.infix_append_right.trans List.infix_append_right).trans hI
        obtain ⟨f1, f2, f3⟩ := readKeys_spec (prior := prior ++ [⟨.symlinkMetadata (project / "lakefile.lean"), .error e⟩] ++
            [⟨.realPath (project / "lakefile.toml"), .ok real⟩, ⟨.readFile (project / "lakefile.toml"), .ok text⟩])
          hI₄ hsys hE ⟨e, hmem, habs⟩ (hT₃.subset (by simp)) hex (hT₃.subset (by simp)) h₄
        refine ⟨fun s srcs he => ?_, f2, .inr ⟨project, tree, sysroot, text,
          prior ++ [⟨.symlinkMetadata (project / "lakefile.lean"), .error e⟩] ++
            [⟨.realPath (project / "lakefile.toml"), .ok real⟩, ⟨.readFile (project / "lakefile.toml"), .ok text⟩], t₄,
          by simp [List.append_assoc], hq₂, by simp [hpp], by simp [hpt], hE.apart, by simpa [SysrootIs] using .inl hps, by simp, f3⟩⟩
        obtain ⟨g1, g2⟩ := f1 s srcs he
        refine ⟨text, g1, fun ha => ?_⟩
        obtain ⟨hh1, hh2, hh3, hh4⟩ := g2 ha
        have hno := (hq₁.append x3).noActs
        have hCl : Clean ([⟨.symlinkMetadata (project / "lakefile.lean"), .error e⟩] ++
            [⟨.realPath (project / "lakefile.toml"), .ok real⟩, ⟨.readFile (project / "lakefile.toml"), .ok text⟩] ++ t₄ : List (Event L E)) :=
          ((clean_notFound habs).append (by clean_events : Clean _)).append hh3
        simpa [List.append_assoc] using ⟨Holds.congr (fun p => written_after_no_acts (b := t₄) hno p) hh1,
          ReadBack.prepend_no_acts hno hh2, hCl, hh4⟩

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
  | error e => obtain ⟨rfl, -⟩ := h₂; exact .inl ⟨e, rfl⟩
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
  obtain ⟨x1, -, x3⟩ := readExact_spec h₁
  have hT₁ := (List.sublist_append_left _ _).trans hT
  cases r with
  | ok text =>
    obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₂
    obtain ⟨real, rfl, hb⟩ := x1 text rfl
    have hex := (RegulaSpecification.Loader.exactBelow_iff _ _ _).mp hb
    exact ⟨fun he => ⟨⟨text, real, hT₁.subset (by simp), hT₁.subset (by simp), hex.1, hex.2, by simpa using he⟩, by clean_events⟩,
      fun hne => .toolchain (text := text) hproject (hT₁.subset (by simp)) fun heq => hne (by rw [heq]), by simpa using x3⟩
  | error why =>
    obtain ⟨rfl, rfl⟩ := runs_pure_iff.mp h₂
    refine ⟨by simp, fun _ => ?_, by simpa using x3⟩
    rcases readExact_error h₁ with ⟨e, rfl⟩ | ⟨real, rfl, hb⟩ | ⟨real, e, rfl⟩
    · exact .toolchainNoReal (e := e) hproject (hT₁.subset (by simp))
    · exact .toolchainNotExact hproject (hT₁.subset (by simp)) hb
    · exact .toolchainFailed (e := e) hproject (hT₁.subset (by simp))

theorem apart_iff (a b : FilePath) : apart a b = true ↔ Apart a b := by
  simp [apart, Apart, ← Bool.not_eq_true, List.isPrefixOf_iff_prefix]

theorem readProjectStage_spec {T prior t : List (Event L E)} {dir treeDir : FilePath} {sysroot : String}
    {b : Except String (Stage × List (Name × Source))} (hI : t <:+: T) (hsys : SysrootIs T sysroot)
    (hq : Quiet prior) (hps : SysrootIs prior sysroot)
    (h : Runs (readProjectStage sysroot dir treeDir : Attempt L E _).run t b) :
    (∀ s srcs, b = .ok (s, srcs) → ∃ tree text, ReadGoal T dir treeDir (Holds tree text srcs) s.toReading ∧
      (s.outcome = .admitted → Holds tree text srcs (written t) ∧ (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t ∧ ReadBack t tree ∧ Clean t)) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧ ReadingPreparation (prior ++ t) dir treeDir := by
  have hT := hI.sublist
  rw [readProjectStage] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r₃, h₃, rfl⟩ := runs_attempt_iff.mp h₁; obtain rfl := runs_call_iff.mp h₃
  cases r₃ with
  | error e =>
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨by simp, fun _ => .failed (e := ⟨.realPath dir, .error e⟩) (hT.subset (by simp)) .project ⟨e, rfl⟩,
      .inl (by simpa using hq.append (quiet_one (o := .realPath dir) (r := .error e) trivial))⟩
  | ok project =>
    obtain ⟨t₃, t₄, r₄, rfl, h₄, h₅⟩ := runs_attempt_bind_iff.mp h₂
    obtain ⟨r₅, h₆, rfl⟩ := runs_attempt_iff.mp h₄; obtain rfl := runs_call_iff.mp h₆
    cases r₅ with
    | error e =>
      obtain ⟨rfl, rfl⟩ := h₅
      exact ⟨by simp, fun _ => .failed (e := ⟨.realPath treeDir, .error e⟩) (hT.subset (by simp)) .tree ⟨e, rfl⟩,
        .inl (by simpa using hq.append (by quiet_events : Quiet ([⟨.realPath dir, .ok project⟩, ⟨.realPath treeDir, .error e⟩] : List (Event L E))))⟩
    | ok tree =>
      obtain ⟨t₉, t₁₀, r₁₀, rfl, h₁₂, h₁₃⟩ := runs_attempt_bind_iff.mp h₅
      obtain ⟨tf, h₁₄, rfl⟩ := runs_lift_iff.mp h₁₂; dsimp only at h₁₃
      generalize hZ : ([⟨.realPath dir, .ok project⟩] ++ ([⟨.realPath treeDir, .ok tree⟩] ++ (t₉ ++ t₁₀)) : List (Event L E)) = Z at hT ⊢
      have hsub₉ : t₉.Sublist T := List.Sublist.trans (by
        rw [← hZ]; simp only [List.cons_append, List.nil_append]
        exact (List.sublist_append_left _ _).trans ((List.sublist_cons_self _ _).trans (List.sublist_cons_self _ _))) hT
      have hproject : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ T := hT.subset (by simp [← hZ])
      have htree : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ T := hT.subset (by simp [← hZ])
      obtain ⟨u1, u2, u3⟩ := toolchainOf_spec (treeDir := treeDir) hsub₉ hproject h₁₄
      have hpre : Quiet (prior ++ ([⟨.realPath dir, .ok project⟩, ⟨.realPath treeDir, .ok tree⟩] ++ t₉) : List (Event L E)) :=
        hq.append ((by quiet_events : Quiet ([⟨.realPath dir, .ok project⟩, ⟨.realPath treeDir, .ok tree⟩] : List (Event L E))).append u3)
      split at h₁₃
      · rename_i hnotApart
        obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₁₃
        refine ⟨fun _ _ he => ?_, by simp, .inl (by simpa [← hZ, List.append_assoc] using hpre)⟩
        cases he
        exact ⟨treeDir, "", earlyUnread_early u2 (.notApart hproject htree fun ha => by simp [(apart_iff _ _).mpr ha] at hnotApart)⟩
      · rename_i hisApart
        have hE : Early T dir treeDir project tree tf :=
          { project_real := hproject, tree_real := htree, apart := (apart_iff _ _).mp (by simpa using hisApart),
            toolchain := fun he => (u1 he).1, toolchain_reason := u2 }
        have hI₁₀ : t₁₀ <:+: T :=
          (List.infix_append_right.trans (List.infix_append_right.trans List.infix_append_right)).trans hI
        obtain ⟨f1, f2, f3⟩ := readConfig_spec (prior := prior ++ ([⟨.realPath dir, .ok project⟩, ⟨.realPath treeDir, .ok tree⟩] ++ t₉))
          hI₁₀ hsys hE hpre (by simp) (by simp) (by simpa [SysrootIs] using .inl hps) h₁₃
        refine ⟨fun s srcs he => ?_, f2, by simpa [← hZ, List.append_assoc] using f3⟩
        obtain ⟨text, g1, g2⟩ := f1 s srcs he
        refine ⟨tree, text, g1, fun ha => ?_⟩
        have hno := ((by quiet_events : Quiet ([⟨.realPath dir, .ok project⟩, ⟨.realPath treeDir, .ok tree⟩] : List (Event L E))).append u3).noActs
        obtain ⟨hh, hb, hcl, hto⟩ := g2 ha
        have hc₂ : Clean ([⟨.realPath dir, .ok project⟩, ⟨.realPath treeDir, .ok tree⟩] : List (Event L E)) := by clean_events
        rw [← hZ]
        exact ⟨Holds.congr (fun p => by simpa [List.append_assoc] using written_after_no_acts (b := t₁₀) hno p) hh,
          by simp, by simpa [List.append_assoc] using ReadBack.prepend_no_acts hno hb,
          by simpa [List.append_assoc] using hc₂.append ((u1 hto).2.append hcl)⟩

theorem readProject_spec {T prior t : List (Event L E)} {dir treeDir : FilePath} {sysroot : String}
    {b : Except String (Reading × List (Name × Source))} (hI : t <:+: T) (hsys : SysrootIs T sysroot)
    (hq : Quiet prior) (hps : SysrootIs prior sysroot)
    (h : Runs (readProject sysroot dir treeDir : Attempt L E _).run t b) :
    (∀ r srcs, b = .ok (r, srcs) → ∃ tree text, ReadGoal T dir treeDir (Holds tree text srcs) r ∧
      (decision r = .admitted → Holds tree text srcs (written t) ∧ (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t ∧ ReadBack t tree ∧ Clean t)) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧ ReadingPreparation (prior ++ t) dir treeDir := by
  rw [readProject] at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨p1, p2, p3⟩ := readProjectStage_spec (List.infix_append_left.trans hI) hsys hq hps h₁
  cases r₁ with
  | error why =>
    obtain ⟨rfl, rfl⟩ := h₂; simp only [List.append_nil]
    exact ⟨by simp, fun _ => p2 ⟨why, rfl⟩, p3⟩
  | ok x =>
    obtain ⟨s, srcs⟩ := x; obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂; simp only [List.append_nil]
    refine ⟨fun _ _ he => ?_, by simp, p3⟩
    cases he; obtain ⟨tree, text, g1, g2⟩ := p1 s srcs rfl
    exact ⟨tree, text, g1, fun ha => g2 (s.decision_toReading ▸ ha)⟩

theorem readProject_no_failed {sysroot : String} {dir treeDir : FilePath} {r : Reading}
    {srcs : List (Name × Source)} {t : List (Event L E)}
    (h : Runs (readProject sysroot dir treeDir : Attempt L E _).run t (.ok (r, srcs)))
    (ha : decision r = .admitted) : ∀ e ∈ t, ¬ e.failed := by
  obtain ⟨p1, -⟩ := readProject_spec (T := [⟨.getEnv "LEAN_SYSROOT", some sysroot⟩] ++ t)
    (prior := [⟨.getEnv "LEAN_SYSROOT", some sysroot⟩])
    List.infix_append_right (by simp [SysrootIs]) (quiet_one trivial) (by simp [SysrootIs]) h
  obtain ⟨_, _, -, g⟩ := p1 r srcs rfl
  exact (g ha).2.2.2

/-- What a whole read rests on, by the events {name}`T`, for a state of the tree that is what {name}`t` leaves. An admission received no failed answer. -/
def ReadDone (T t : List (Event L E)) (dir treeDir : FilePath) (r : Reading) : Prop :=
  (decision r = .admitted → (∀ held : List String → Option String, (∀ p, held p = written t p) →
    Evidence T dir treeDir held r) ∧ (∃ real, (⟨.realPath treeDir, .ok real⟩ : Event L E) ∈ t ∧ ReadBack t real) ∧ Clean t) ∧
    ∀ o, decision r = o → o ≠ .admitted → Reason T dir treeDir o

theorem read_spec {T prior t : List (Event L E)} {dir treeDir : FilePath} {sysroot : String}
    {b : Except String (Reading × List String)} (hI : t <:+: T) (hsys : SysrootIs T sysroot)
    (hq : Quiet prior) (hps : SysrootIs prior sysroot)
    (h : Runs (read sysroot dir treeDir : Attempt L E _).run t b) :
    (∀ r lines, b = .ok (r, lines) → ReadDone T t dir treeDir r) ∧
      ((∃ e, b = .error e) → Reason T dir treeDir .incomplete) ∧ ReadingPreparation (prior ++ t) dir treeDir := by
  unfold Regula.Reader.read at h
  obtain ⟨t₁, t₂, r₁, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨p1, p2, p3⟩ := readProject_spec (T := T) (prior := prior) (List.infix_append_left.trans hI) hsys hq hps h₁
  cases r₁ with
  | error why =>
    obtain ⟨rfl, rfl⟩ := h₂; simp only [List.append_nil]
    exact ⟨by simp, fun _ => p2 ⟨why, rfl⟩, p3⟩
  | ok x =>
    obtain ⟨r, srcs⟩ := x; obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂; simp only [List.append_nil]
    refine ⟨fun _ _ he => ?_, by simp, p3⟩
    cases he; obtain ⟨tree, text, g1, g2⟩ := p1 r srcs rfl
    exact ⟨fun ha => ⟨fun held hheld => g1.1 ha held ((funext hheld : held = written t₁) ▸ (g2 ha).1),
      ⟨tree, (g2 ha).2.1, (g2 ha).2.2.1⟩, (g2 ha).2.2.2⟩, g1.2⟩

end RegulaSpecification.Effects
