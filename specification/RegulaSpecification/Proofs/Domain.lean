/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Domain
import RegulaSpecification.Proofs.OwedExact
import RegulaSpecification.Proofs.ReaderFiles

/-!
# The domain of the full verdict, and the run

`RegulaSpecification.Domain` states which projects a full verdict is owed to, apart from `Reason`. This module relates that
statement to what a run received.

`Answers p t dir tree` says that the responses of a reading are what the files of the project `p` state: it says what a read,
Lake's load and Lean's parser answered, and names no reason. `reason_excluded` is the theorem that decides who gets a full
pass: no case of `Reason` holds of a project in the domain whose reads answer so. `reason_classified` sorts each case under a
failed or differing answer, a project outside the domain, or a conflict in which one admission could not be about what is
consumed. `domain_owed` states the result at the whole run, for every program that meets the record, without naming `Reason`.

`Answers` holds what the program observes and what no proof can reach: each clause is about a response in the trace, never about
every value. So a run in which another process changes a file between two reads, or a parser that answers two ways, is not
covered by `domain_owed`: `Answers` fails, which is the accepted risk that the owner's account leaves unsaid. `domain_model`
states that these premises are met by a run.
-/

namespace RegulaSpecification.Effects

open Lean (Name Import)
open Lean.Parser (mkInputContext)
open System (FilePath)
open Regula.Effect
open Regula.Language
open RegulaSpecification.Language
open RegulaSpecification.Domain
open RegulaSpecification.Loader

variable {L E : Type}

/-- What Lake's load gave of the tree `tree` is what the configuration `c` states, by the file each name selects. It reads the
root that a response gave, for the names a default target or an import states. That Lake's load is this function of the text is
what `Lake/Load/Toml.lean:484-500`, `Lake/Config/Module.lean:58-59` and `Lake/Config/LeanLibConfig.lean:144-146` say at v4.35.0, and
what no proof reaches, so it is a premise over the response. -/
structure LakeAgrees (c : Configuration) (imported : Name → Prop) (tree : FilePath) (t : List (Event L E)) (root : Root L) : Prop where
  /-- Each source directory is the tree joined with one the text states. -/
  sourceDirs : ∀ d ∈ root.sourceDirs, ∃ s ∈ c.sourceDirs, parts d = parts tree ++ RegulaSpecification.Domain.components s
  /-- Each library's `globs`. -/
  libraries : ∀ x ∈ root.libraries, ∃ lib ∈ c.libraries, x = (lib.name, lib.globs)
  /-- The default targets. -/
  defaultTargets : root.defaultTargets = c.defaultTargets
  /-- The targets' names. -/
  targets : ∀ n ∈ root.targets, n ∈ c.targetNames
  /-- A default target that Lake's search takes as a library is that library, and it lists what `listed` gives. -/
  findLib : ∀ n ∈ c.defaultTargets, ∀ l, root.findLib n = some l → ∃ lib, c.libraries.find? (·.name == n) = some lib ∧
    ∀ ms, (⟨.libModules l, .ok ms⟩ : Event L E) ∈ t → ms.toList.map (·.1) = Configuration.listed lib ∧
      ∀ x ∈ ms.toList, parts x.2 = parts tree ++ c.fileIn lib x.1
  /-- A default target that Lake's search takes as no library is none. -/
  noLib : ∀ n ∈ c.defaultTargets, root.findLib n = none → c.libraries.find? (·.name == n) = none
  /-- A default target that Lake's search takes as an executable. -/
  findExe : ∀ n ∈ c.defaultTargets, ∀ m, root.findExe n = some m → ∃ exe, c.executables.find? (·.name == n) = some exe ∧
    exe.root = m.1 ∧ parts m.2 = parts tree ++ c.exeFile exe
  /-- A default target that Lake's search takes as no executable. -/
  noExe : ∀ n ∈ c.defaultTargets, root.findExe n = none → c.executables.find? (·.name == n) = none
  /-- Lake's resolution of a name. -/
  resolve : ∀ m path, root.resolve m = some path → ∃ rel, c.resolve m = some rel ∧ parts path = parts tree ++ rel
  /-- A name that an import states, and Lake's resolution gives no file for. -/
  noResolve : ∀ m, imported m → root.resolve m = none → c.resolve m = none

/-- The responses of a reading of the project `p` at `dir`, in the checker's tree at `treeDir`, are what the files of `p` state. Each
clause reads a response, and no clause names a reason. -/
structure Answers (p : Project) (t : List (Event L E)) (dir treeDir : FilePath) : Prop where
  /-- No answer failed. -/
  answered : ∀ e ∈ t, ¬ e.failed
  /-- A file of the project answers with what `p` states of it. -/
  read : ∀ project, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t → ∀ rel text,
    (⟨.readFile (under project rel), .ok text⟩ : Event L E) ∈ t →
      (rel = ["lean-toolchain"] → p.toolchainFile = some text) ∧ (rel = ["lakefile.toml"] → p.configFile = some text) ∧
        ∀ s ∈ p.sources, s.rel = rel → s.text = text
  /-- A file of the project crosses no link. -/
  real : ∀ project, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t → ∀ rel real,
    (rel = ["lean-toolchain"] ∨ rel = ["lakefile.toml"] ∨ ∃ s ∈ p.sources, s.rel = rel) →
    (⟨.realPath (under project rel), .ok real⟩ : Event L E) ∈ t →
      Regula.Load.exactBelow project (under project rel) real = true
  /-- The name `lakefile.lean` answers when `p` holds it. -/
  leanConfig : ∀ project, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t → ∀ metadata,
    (⟨.symlinkMetadata (project / "lakefile.lean"), .ok metadata⟩ : Event L E) ∈ t → p.leanConfig = true
  /-- What Lake's TOML parser gave of a text: the key paths and the nesting that `p` states. -/
  toml : ∀ text table, (⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∈ t →
    (∀ k, KeyPath .anonymous table k → k ∈ p.config.keys) ∧ ∀ n, Deeper n table → n ≤ p.config.nesting
  /-- This program was started from outside the project. -/
  start : ∀ project sysroot program lakeLib app real leanPath, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
    SysrootIs t sysroot → (⟨.lakeInstall sysroot, (program, lakeLib)⟩ : Event L E) ∈ t →
    (⟨.appPath, .ok app⟩ : Event L E) ∈ t → (⟨.realPath app, .ok real⟩ : Event L E) ∈ t →
    (⟨.getEnv "LEAN_PATH", some leanPath⟩ : Event L E) ∈ t →
    Regula.Load.below project real = false ∧ ∃ own, (real.parent.bind (·.parent)).map (· / "lib" / "lean") = some own ∧
      Regula.Load.dispatchedFrom own.toString lakeLib.toString ((System.SearchPath.parse leanPath).map toString) = true
  /-- The project and the checker's tree lie apart. -/
  apart : ∀ project tree, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t → (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
    Apart project tree
  /-- The tree's two copies lie below it, at the components their names give. -/
  copies : ∀ tree, (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
    ¬ OutsideTree tree (tree / "lakefile.toml") ∧ ¬ OutsideTree tree (tree / "lean-toolchain") ∧
      parts (tree / "lakefile.toml") = parts tree ++ ["lakefile.toml"] ∧
      parts (tree / "lean-toolchain") = parts tree ++ ["lean-toolchain"]
  /-- Lake's load of the tree gave what the configuration states. -/
  lake : ∀ tree sysroot root log, (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
    (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ t →
    LakeAgrees p.config (fun m => ∃ s ∈ p.sources, ∃ i ∈ s.imports, i.module = m) tree t root
  /-- The directory above a file Lake names lies below the tree. -/
  parents : ∀ project tree root modules m path d, Scene t dir treeDir project tree root modules →
    FileOfModule root modules m path → path.parent = some d → ∃ rel', TreeRelative (parts tree) (parts d) rel'
  /-- What Lean's header parser gave of a text is what `p` states of a file with that text. -/
  header : ∀ text name h state messages imports, (⟨.parseHeader (mkInputContext text name), .ok (h, state, messages, imports)⟩ : Event L E) ∈ t →
    ∀ s ∈ p.sources, s.text = text → imports = s.imports
  /-- What Lean's parser read of a file is in the closed language when what `p` states of that file is. -/
  parse : ∀ project tree f path imports mods, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t → ReadAs t project tree f path imports mods →
    ∀ s ∈ p.sources, s.module = f.module → TreeRelative (parts tree) (parts path) s.rel → FileAdmitted s.read → FileAdmitted f
  /-- A module that `p` takes from the toolchain lies below the toolchain's library. -/
  toolchain : ∀ tree sysroot root log m olean real, (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
    (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ t → m ∈ p.toolchainModules → (⟨.findOLean m, .ok olean⟩ : Event L E) ∈ t →
    (⟨.realPath olean, .ok real⟩ : Event L E) ∈ t →
    ∃ d ∈ root.toolchain, ∀ dr, (⟨.realPath d, .ok dr⟩ : Event L E) ∈ t → Regula.Load.below dr real = true
  /-- A file written answers with what was written. -/
  writes : ∀ project tree root modules path text r, Scene t dir treeDir project tree root modules →
    Planned t project tree root modules path text →
    ([⟨.writeFile path text, .ok ()⟩, ⟨.readFile path, r⟩] : List (Event L E)).Sublist t → r = .ok text
  /-- Nothing answers to the name that Lake prefers as its configuration, in the tree. -/
  shadow : ∀ tree metadata, (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
    (⟨.symlinkMetadata (tree / "lakefile.lean"), .ok metadata⟩ : Event L E) ∉ t

section

variable {p : Project} {t : List (Event L E)} {dir treeDir : FilePath}

/-- The modules of targets that Lake listed are those the configuration states, each at the file it states. -/
theorem defaultModules_agree {c : Configuration} {imported : Name → Prop} {tree : FilePath} {root : Root L}
    (h : LakeAgrees c imported tree t root) {targets : List Name} {modules : List (Name × FilePath)}
    (hd : DefaultModules t root targets modules) (hsub : ∀ n ∈ targets, n ∈ c.defaultTargets) :
    modules.map (·.1) = (targets.flatMap c.modulesOf).map (·.1) ∧
      ∀ x ∈ modules, ∃ rel, (x.1, rel) ∈ targets.flatMap c.modulesOf ∧ parts x.2 = parts tree ++ rel := by
  induction hd with
  | nil => exact ⟨rfl, by simp⟩
  | @lib target l targets ms modules hl he _ ih =>
    have hin : target ∈ c.defaultTargets := hsub _ (List.mem_cons_self ..)
    obtain ⟨i1, i2⟩ := ih fun n hn => hsub n (List.mem_cons_of_mem _ hn)
    obtain ⟨lib, hfind, hms⟩ := h.findLib _ hin _ hl
    obtain ⟨hnames, hfiles⟩ := hms _ he
    have hmods : c.modulesOf target = (Configuration.listed lib).map fun m => (m, c.fileIn lib m) := by
      simp [Configuration.modulesOf, hfind]
    refine ⟨?_, fun x hx => ?_⟩
    · simp only [List.map_append, List.flatMap_cons, i1, hnames, hmods, List.map_map]
      congr 1
      simp [Function.comp_def]
    · rcases List.mem_append.mp hx with hx | hx
      · refine ⟨c.fileIn lib x.1, ?_, hfiles x hx⟩
        rw [List.flatMap_cons, hmods]
        refine List.mem_append_left _ (List.mem_map.mpr ⟨x.1, ?_, rfl⟩)
        rw [← hnames]
        exact List.mem_map_of_mem hx
      · obtain ⟨rel, h1, h2⟩ := i2 x hx
        refine ⟨rel, ?_, h2⟩
        rw [List.flatMap_cons]
        exact List.mem_append_right _ h1
  | @exe target m targets modules hl hx _ ih =>
    have hin : target ∈ c.defaultTargets := hsub _ (List.mem_cons_self ..)
    obtain ⟨i1, i2⟩ := ih fun n hn => hsub n (List.mem_cons_of_mem _ hn)
    obtain ⟨exe, hfind, hroot, hfile⟩ := h.findExe _ hin _ hx
    have hmods : c.modulesOf target = [(exe.root, c.exeFile exe)] := by
      simp [Configuration.modulesOf, h.noLib _ hin hl, hfind]
    refine ⟨?_, fun y hy => ?_⟩
    · simp [List.flatMap_cons, i1, hmods, hroot]
    · rcases List.mem_cons.mp hy with rfl | hy
      · refine ⟨c.exeFile exe, ?_, hfile⟩
        rw [List.flatMap_cons, hmods, hroot]
        simp
      · obtain ⟨rel, h1, h2⟩ := i2 y hy
        refine ⟨rel, ?_, h2⟩
        rw [List.flatMap_cons]
        exact List.mem_append_right _ h1
  | @other target targets modules hl hx _ ih =>
    have hin : target ∈ c.defaultTargets := hsub _ (List.mem_cons_self ..)
    obtain ⟨i1, i2⟩ := ih fun n hn => hsub n (List.mem_cons_of_mem _ hn)
    have hmods : c.modulesOf target = [] := by
      simp [Configuration.modulesOf, h.noLib _ hin hl, h.noExe _ hin hx]
    refine ⟨by simp [List.flatMap_cons, i1, hmods], fun y hy => ?_⟩
    obtain ⟨rel, h1, h2⟩ := i2 y hy
    refine ⟨rel, ?_, h2⟩
    simpa [List.flatMap_cons, hmods] using h1

theorem lookup_isSome_of_mem {α β : Type} [BEq α] [LawfulBEq α] {a : α} {b : β} {l : List (α × β)} (h : (a, b) ∈ l) :
    (l.lookup a).isSome = true := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    obtain ⟨k, v⟩ := x
    by_cases hk : a = k
    · subst hk
      simp
    · have hne : (a == k) = false := by simpa using hk
      simp only [List.lookup_cons, hne]
      rcases List.mem_cons.mp h with he | h'
      · cases he
        exact absurd rfl hk
      · exact ih h'

/-- What a scene of the run says, on these answers: Lake's load agrees with the configuration, and the modules of the default targets
are the claim, each at its file. -/
theorem scene_agrees (ha : Answers p t dir treeDir) {project tree : FilePath} {root : Root L} {modules : List (Name × FilePath)}
    (hs : Scene t dir treeDir project tree root modules) :
    LakeAgrees p.config (fun m => ∃ s ∈ p.sources, ∃ i ∈ s.imports, i.module = m) tree t root ∧
      modules.map (·.1) = p.config.claim.map (·.1) ∧
      ∀ x ∈ modules, ∃ rel, (x.1, rel) ∈ p.config.claim ∧ parts x.2 = parts tree ++ rel := by
  obtain ⟨hreal, s, log, -, hload, -⟩ := hs.loaded
  have hag := ha.lake tree s root log hreal hload
  have hd := hs.default
  rw [hag.defaultTargets] at hd
  exact ⟨hag, defaultModules_agree hag hd fun _ h => h⟩

/-- A file that Lake names for a name the build needs is a source of the project, and the name is a source's or the toolchain's. -/
theorem named_source (hd : p.InDomain) (ha : Answers p t dir treeDir) {project tree : FilePath} {root : Root L}
    {modules : List (Name × FilePath)} (hs : Scene t dir treeDir project tree root modules) {m : Name}
    (hn : Named t project tree root modules m) :
    (∀ path, FileOfModule root modules m path → ∃ s ∈ p.sources, s.module = m ∧ parts path = parts tree ++ s.rel) ∧
      ((∃ s ∈ p.sources, s.module = m) ∨ m ∈ p.toolchainModules) := by
  obtain ⟨hag, hnames, hclaim⟩ := scene_agrees ha hs
  have hOfModule : ∀ x ∈ modules, ∃ s ∈ p.sources, s.module = x.1 ∧ parts x.2 = parts tree ++ s.rel := by
    intro x hx
    obtain ⟨rel, h1, h2⟩ := hclaim x hx
    obtain ⟨s, hs', h3, h4⟩ := hd.claimRead _ h1
    exact ⟨s, hs', h3, by rw [h2, h4]⟩
  induction hn with
  | @root m hm =>
    obtain ⟨⟨k, file⟩, hx, rfl⟩ := List.mem_map.mp hm
    obtain ⟨s₀, hs₀, hmod₀, -⟩ := hOfModule _ hx
    refine ⟨fun path hf => ?_, .inl ⟨s₀, hs₀, hmod₀⟩⟩
    rcases hf with hf | hf
    · exact hOfModule _ hf
    · obtain ⟨rel, hr, hp⟩ := hag.resolve _ _ hf
      obtain ⟨rel₀, hc, -⟩ := hclaim _ hx
      obtain rfl := hd.config.resolvesToClaim _ hc _ hr
      obtain ⟨s, hs', h3, h4⟩ := hd.claimRead _ hc
      exact ⟨s, hs', h3, by rw [hp, h4]⟩
  | @imported m imports i hn₀ hh hi ih =>
    obtain ⟨ih1, -⟩ := ih
    obtain ⟨path₀, text, header, state, messages, hf₀, ⟨rel, hrel, hread⟩, he⟩ := hh
    obtain ⟨s, hsm, hmod, hp⟩ := ih1 _ hf₀
    have hrel' : rel = s.rel := List.append_cancel_left (hrel.1.symm.trans hp)
    subst hrel'
    have htext := (ha.read _ hs.project_real _ _ hread).2.2 s hsm rfl
    have himports := ha.header _ _ _ _ _ _ he s hsm htext
    have hi' : i ∈ s.imports := himports ▸ hi
    rcases hd.imports s hsm i hi' with ⟨s', hs', h1, h2⟩ | ⟨h1, h2, h3⟩
    · refine ⟨fun path hf => ?_, .inl ⟨s', hs', h1⟩⟩
      rcases hf with hf | hf
      · exact hOfModule _ hf
      · obtain ⟨rel', hr, hp'⟩ := hag.resolve _ _ hf
        rw [h2] at hr
        obtain rfl := Option.some.inj hr
        exact ⟨s', hs', h1, hp'⟩
    · refine ⟨fun path hf => ?_, .inr h1⟩
      rcases hf with hf | hf
      · obtain ⟨rel', hc, -⟩ := hclaim _ hf
        have h4 : (p.config.claim.lookup i.module).isSome = true := lookup_isSome_of_mem hc
        rw [Option.isNone_iff_eq_none] at h3
        rw [h3] at h4
        cases h4
      · obtain ⟨rel', hr, -⟩ := hag.resolve _ _ hf
        rw [h2] at hr
        cases hr

/-- What a file's header states is what `p` states of the source of its name. -/
theorem header_source (hd : p.InDomain) (ha : Answers p t dir treeDir) {project tree : FilePath} {root : Root L}
    {modules : List (Name × FilePath)} (hs : Scene t dir treeDir project tree root modules) {m : Name} {imports : Array Import}
    (hn : Named t project tree root modules m) (hh : HeaderOf t project tree root modules m imports) :
    ∃ s ∈ p.sources, s.module = m ∧ imports = s.imports := by
  obtain ⟨path₀, text, header, state, messages, hf₀, ⟨rel, hrel, hread⟩, he⟩ := hh
  obtain ⟨s, hsm, hmod, hp⟩ := (named_source hd ha hs hn).1 _ hf₀
  have hrel' : rel = s.rel := List.append_cancel_left (hrel.1.symm.trans hp)
  subst hrel'
  have htext := (ha.read _ hs.project_real _ _ hread).2.2 s hsm rfl
  exact ⟨s, hsm, hmod, ha.header _ _ _ _ _ _ he s hsm htext⟩

/-- A text that the plan would have the tree hold at a path: below the tree, by what `p` states. -/
theorem planned_text (hd : p.InDomain) (ha : Answers p t dir treeDir) {project tree : FilePath} {root : Root L}
    {modules : List (Name × FilePath)} (hs : Scene t dir treeDir project tree root modules) {path : FilePath} {text : String}
    (h : Planned t project tree root modules path text) :
    (parts path = parts tree ++ ["lakefile.toml"] ∧ p.configFile = some text) ∨
      (parts path = parts tree ++ ["lean-toolchain"] ∧ text = leanToolchain) ∨
      ∃ s ∈ p.sources, parts path = parts tree ++ s.rel ∧ s.text = text := by
  obtain ⟨hreal, -⟩ := hs.loaded
  obtain ⟨-, -, h3, h4⟩ := ha.copies tree hreal
  cases h with
  | toml hr =>
    exact .inl ⟨h3, (ha.read project hs.project_real ["lakefile.toml"] text hr).2.1 rfl⟩
  | toolchain => exact .inr (.inl ⟨h4, rfl⟩)
  | source hn hf hst =>
    obtain ⟨s, hsm, -, hp⟩ := (named_source hd ha hs hn).1 _ hf
    obtain ⟨rel, hrel, hread⟩ := hst
    have hrel' : rel = s.rel := List.append_cancel_left (hrel.1.symm.trans hp)
    subst hrel'
    exact .inr (.inr ⟨s, hsm, hp, (ha.read _ hs.project_real _ _ hread).2.2 s hsm rfl⟩)

/-- **No reason holds of a project in the domain whose reads answer as its files state.** Each case of `Reason` meets a clause of the
domain or of the answers, so each refusal that the record allows is explained by the published statement, and a case that a healthy
project could meet would not prove here. -/
theorem reason_excluded (hd : p.InDomain) (ha : Answers p t dir treeDir) {o : Outcome} : ¬ Reason t dir treeDir o := by
  intro hr
  have hsources {tree : FilePath} {path : FilePath} {s : SourceFile} (hs : s ∈ p.sources) (hp : parts path = parts tree ++ s.rel) :
      TreeRelative (parts tree) (parts path) s.rel := ⟨hp, hd.sourcePath s hs⟩
  cases hr with
  | failed he _ hf => exact ha.answered _ he hf
  | load hp hf => exact ha.answered _ hp.event hf
  | toolchain hp hr hne =>
    obtain ⟨t₀, h₀, htrim⟩ := hd.toolchain
    have := (ha.read _ hp ["lean-toolchain"] _ hr).1 rfl
    rw [h₀] at this
    obtain rfl := Option.some.inj this
    exact hne htrim
  | toolchainFailed hp hr => exact ha.answered _ hr ⟨_, rfl⟩
  | toolchainNotExact hp hr hne =>
    cases (ha.real _ hp ["lean-toolchain"] _ (.inl rfl) hr).symm.trans hne
  | toolchainNoReal hp hr => exact ha.answered _ hr ⟨_, rfl⟩
  | started hp hs hi hap hre hen hor =>
    obtain ⟨h1, own, h2, h3⟩ := ha.start _ _ _ _ _ _ _ hp hs hi hap hre hen
    rcases hor with hb | hb
    · rw [h1] at hb
      cases hb
    · rw [hb own h2] at h3
      cases h3
  | tomlNotExact hp hr hne =>
    cases (ha.real _ hp ["lakefile.toml"] _ (.inr (.inl rfl)) hr).symm.trans hne
  | notApart hp ht hne => exact hne (ha.apart _ _ hp ht)
  | configNotInTree ht hpath hout =>
    obtain ⟨h1, h2, -⟩ := ha.copies _ ht
    rcases hpath with rfl | rfl
    · exact h1 hout
    · exact h2 hout
  | moduleNotInTree hs hn hf hout =>
    obtain ⟨s, hsm, -, hp⟩ := (named_source hd ha hs hn).1 _ hf
    rcases hout with hx | ⟨d, hdp, hx⟩
    · exact hx _ (hsources hsm hp)
    · obtain ⟨rel', h'⟩ := ha.parents _ _ _ _ _ _ _ hs hf hdp
      exact hx _ h'
  | moduleNotExact hs hn hf hrel hr hne =>
    obtain ⟨s, hsm, -, hp⟩ := (named_source hd ha hs hn).1 _ hf
    obtain rfl : _ = s.rel := List.append_cancel_left (hrel.1.symm.trans hp)
    have := ha.real _ hs.project_real _ _ (.inr (.inr ⟨s, hsm, rfl⟩)) hr
    rw [hne] at this
    cases this
  | leanConfig hp hr =>
    have := ha.leanConfig _ hp _ hr
    rw [hd.noLeanConfig] at this
    cases this
  | key hr hk hroot hna =>
    obtain ⟨project, text, -, -, h3⟩ := hr
    exact hna (hd.config.keys _ ((ha.toml _ _ h3).1 _ hk))
  | deep hr hn =>
    obtain ⟨project, text, -, -, h3⟩ := hr
    have := (ha.toml _ _ h3).2 _ hn
    have := hd.config.shallow
    omega
  | deepDependency hr hn =>
    obtain ⟨project, text, -, -, h3⟩ := hr
    have := (ha.toml _ _ h3).2 _ hn
    have := hd.config.shallow
    omega
  | dependency hr hk hroot =>
    obtain ⟨project, text, -, -, h3⟩ := hr
    exact hd.config.noDependency _ ((ha.toml _ _ h3).1 _ hk) hroot
  | openDir hl hdir hno =>
    obtain ⟨hreal, sy, log, -, hload, -⟩ := hl
    obtain ⟨s, hsm, hp⟩ := (ha.lake _ sy _ log hreal hload).sourceDirs _ hdir
    refine hno _ ⟨hp, fun c hc => ?_⟩
    obtain ⟨-, hc2⟩ := List.mem_filter.mp hc
    simp only [Bool.and_eq_true, bne_iff_ne] at hc2
    exact ⟨hc2.1, (hd.config.sourceDirs s hsm).2 c hc⟩
  | openGlob hl hlib hg hne =>
    obtain ⟨hreal, sy, log, -, hload, -⟩ := hl
    obtain ⟨lib, hlm, rfl⟩ := (ha.lake _ sy _ log hreal hload).libraries _ hlib
    obtain ⟨n, hn⟩ := hd.config.globs lib hlm _ hg
    exact hne n hn
  | noClaim hs =>
    obtain ⟨-, hnames, -⟩ := scene_agrees ha hs
    have : p.config.claim = [] := by simpa using hnames.symm
    exact hd.config.claimsSomething this
  | targetName hl hn hc =>
    obtain ⟨hreal, sy, log, -, hload, -⟩ := hl
    exact hc (hd.config.targetNames _ ((ha.lake _ sy _ log hreal hload).targets _ hn))
  | twoFiles hs hm hres hne =>
    obtain ⟨hag, -, hclaim⟩ := scene_agrees ha hs
    obtain ⟨rel, hc, hp⟩ := hclaim _ hm
    obtain ⟨rel', hr, hp'⟩ := hag.resolve _ _ hres
    obtain rfl := hd.config.resolvesToClaim _ hc _ hr
    exact hne (hp'.trans hp.symm)
  | twoRoots hs hm hm' hne =>
    obtain ⟨-, -, hclaim⟩ := scene_agrees ha hs
    obtain ⟨rel, hc, hp⟩ := hclaim _ hm
    obtain ⟨rel', hc', hp'⟩ := hclaim _ hm'
    obtain rfl := hd.config.oneFile _ hc _ hc' rfl
    exact hne (hp'.trans hp.symm)
  | configShadowed ht hm => exact ha.shadow _ _ ht hm
  | treeDiffers hs hpl hsub hne => exact hne (ha.writes _ _ _ _ _ _ _ hs hpl hsub)
  | twoTexts hs h1 h2 hparts hne =>
    have hrole : ∀ {x : SourceFile}, x ∈ p.sources → x.rel ≠ ["lakefile.toml"] ∧ x.rel ≠ ["lean-toolchain"] :=
      fun hx => (hd.oneRole _ hx).2
    rcases planned_text hd ha hs h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨x, hx, a1, a2⟩ <;>
      rcases planned_text hd ha hs h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩ | ⟨y, hy, b1, b2⟩
    · exact hne (Option.some.inj (a2.symm.trans b2))
    · rw [a1, b1] at hparts
      exact absurd (List.append_cancel_left hparts) (by decide)
    · rw [a1, b1] at hparts
      exact (hrole hy).1 (List.append_cancel_left hparts).symm
    · rw [a1, b1] at hparts
      exact absurd (List.append_cancel_left hparts) (by decide)
    · exact hne (a2.trans b2.symm)
    · rw [a1, b1] at hparts
      exact (hrole hy).2 (List.append_cancel_left hparts).symm
    · rw [a1, b1] at hparts
      exact (hrole hx).1 (List.append_cancel_left hparts)
    · rw [a1, b1] at hparts
      exact (hrole hx).2 (List.append_cancel_left hparts)
    · rw [a1, b1] at hparts
      exact hne (a2.symm.trans ((hd.oneText x hx y hy (List.append_cancel_left hparts)).trans b2))
  | moduleName hs hn hc =>
    rcases (named_source hd ha hs hn).2 with ⟨s, hsm, rfl⟩ | hm
    · exact hc (hd.moduleNames s hsm)
    · exact hc (hd.toolchainNames _ hm)
  | importedRoot hs hn hh hi hl hres =>
    obtain ⟨hag, -, hclaim⟩ := scene_agrees ha hs
    obtain ⟨s, hsm, -, rfl⟩ := header_source hd ha hs hn hh
    rcases hd.imports s hsm _ hi with ⟨s', -, -, h2⟩ | ⟨-, -, h3⟩
    · rw [hag.noResolve _ ⟨s, hsm, _, hi, rfl⟩ hres] at h2
      cases h2
    · obtain ⟨file, hf⟩ := Option.isSome_iff_exists.mp hl
      obtain ⟨rel, hc, -⟩ := hclaim _ (mem_of_lookup hf)
      have h4 := lookup_isSome_of_mem hc
      simp only [] at h4
      rw [Option.isNone_iff_eq_none] at h3
      rw [h3] at h4
      cases h4
  | @notToolchain project tree root modules m olean real reals hs hn hl hres hf hre hreals hall =>
    obtain ⟨hag, hnames, hclaim⟩ := scene_agrees ha hs
    have hm : m ∈ p.toolchainModules := by
      cases hn with
      | root hm =>
        obtain ⟨⟨k, file⟩, hx, rfl⟩ := List.mem_map.mp hm
        have := lookup_isSome_of_mem hx
        rw [hl] at this
        cases this
      | imported hn₀ hh hi =>
        obtain ⟨s, hsm, -, rfl⟩ := header_source hd ha hs hn₀ hh
        rcases hd.imports s hsm _ hi with ⟨s', -, -, h2⟩ | ⟨h1, -, -⟩
        · rw [hag.noResolve _ ⟨s, hsm, _, hi, rfl⟩ hres] at h2
          cases h2
        · exact h1
    obtain ⟨hreal, sy, log, -, hload, -⟩ := hs.loaded
    obtain ⟨d, hdm, hbelow⟩ := ha.toolchain _ sy _ log _ _ _ hreal hload hm hf hre
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (hreals ▸ hdm)
    obtain ⟨h1, h2⟩ := hall x hx
    rw [hbelow _ h1] at h2
    cases h2
  | tooMany hs hnd hall hgt =>
    obtain ⟨-, hnames, -⟩ := scene_agrees ha hs
    have hlen := congrArg List.length hnames
    simp only [List.length_map] at hlen
    have hsub := sum_le_of_subset (g := fun x : Name × Array Import => x.2.size) (hnd.of_map _ fun _ _ h he => h (by rw [he]))
      (b := p.sources.map fun s => (s.module, s.imports)) fun x hx => by
        obtain ⟨h1, h2⟩ := hall x hx
        obtain ⟨s, hsm, h3, h4⟩ := header_source hd ha hs h1 h2
        exact List.mem_map.mpr ⟨s, hsm, Prod.ext h3 h4.symm⟩
    simp only [List.map_map] at hsub
    have hb := hd.bounded
    have hb' : (p.sources.map fun s => s.imports.size).sum = (p.sources.map (·.imports.size)).sum := rfl
    simp only [Function.comp_def] at hsub
    omega
  | mathlib hs hn hroot =>
    rcases (named_source hd ha hs hn).2 with ⟨s, hsm, rfl⟩ | hm
    · exact hd.noMathlib.1 s hsm hroot
    · exact hd.noMathlib.2 _ hm hroot
  | file hs hn hf hra _ _ _ _ _ hna =>
    obtain ⟨s, hsm, hmod, hp⟩ := (named_source hd ha hs hn).1 _ hf
    exact hna (ha.parse _ _ _ _ _ _ hs.project_real hra s hsm hmod (hsources hsm hp) (hd.language s hsm).2)

/-! ## Why each reason is a reason -/

/-- A failed or differing external answer: an answer failed, a planned file answered otherwise than what was written to it, or the
answers about this program say that it was not started from outside the project. -/
inductive ExternalAnswer (t : List (Event L E)) (dir treeDir : FilePath) : Prop where
  /-- An answer failed. -/
  | failed {e : Event L E} : e ∈ t → e.failed → ExternalAnswer t dir treeDir
  /-- A file written answered otherwise. -/
  | differs {path text r} : ([⟨.writeFile path text, .ok ()⟩, ⟨.readFile path, r⟩] : List (Event L E)).Sublist t → r ≠ .ok text →
      ExternalAnswer t dir treeDir
  /-- The answers about this program's place and the Lake that started it. -/
  | start {project sysroot program lakeLib app real leanPath} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t → SysrootIs t sysroot →
      (⟨.lakeInstall sysroot, (program, lakeLib)⟩ : Event L E) ∈ t → (⟨.appPath, .ok app⟩ : Event L E) ∈ t →
      (⟨.realPath app, .ok real⟩ : Event L E) ∈ t → (⟨.getEnv "LEAN_PATH", some leanPath⟩ : Event L E) ∈ t →
      (Regula.Load.below project real = true ∨
        ∀ own, (real.parent.bind (·.parent)).map (· / "lib" / "lean") = some own →
          Regula.Load.dispatchedFrom own.toString lakeLib.toString ((System.SearchPath.parse leanPath).map toString) = false) →
      ExternalAnswer t dir treeDir

/-- A conflict in which one admission could not be about what is consumed: writing to the tree would write to the project, a file
would be written outside the tree, one name has two files, one path has two texts, an import names a file other than the one read
for that name, or a file of the plan is what Lake would take as its configuration. -/
inductive Conflict (t : List (Event L E)) (dir treeDir : FilePath) : Prop where
  /-- The project and the tree do not lie apart. -/
  | notApart {project tree} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t → (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
      ¬ Apart project tree → Conflict t dir treeDir
  /-- A file that would be written lies outside the tree. -/
  | outsideTree {tree path} : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t → OutsideTree tree path → Conflict t dir treeDir
  /-- One name, two files. -/
  | twoFiles {project tree root modules m file other} : Scene t dir treeDir project tree root modules →
      (m, file) ∈ modules → (root.resolve m = some other ∨ (m, other) ∈ modules) → parts other ≠ parts file → Conflict t dir treeDir
  /-- One path, two texts. -/
  | twoTexts {project tree root modules path text path' text'} : Scene t dir treeDir project tree root modules →
      Planned t project tree root modules path text → Planned t project tree root modules path' text' →
      parts path = parts path' → text ≠ text' → Conflict t dir treeDir
  /-- An import names a default executable's root that no library holds, so not the file read for that name. -/
  | importedRoot {project tree root modules i} : Scene t dir treeDir project tree root modules →
      (modules.lookup i).isSome = true → root.resolve i = none → Conflict t dir treeDir
  /-- A file of the plan is what Lake would take as its configuration. -/
  | shadowed {tree metadata} : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
      (⟨.symlinkMetadata (tree / "lakefile.lean"), .ok metadata⟩ : Event L E) ∈ t → Conflict t dir treeDir

/-- The project is outside the published domain: no project in the domain gives these answers. -/
def OutsideDomain (t : List (Event L E)) (dir treeDir : FilePath) : Prop :=
  ∀ p : Project, Answers p t dir treeDir → ¬ p.InDomain

/-- **Each reason falls under one of three**: a failed or differing external answer, the project outside the published domain, or a
conflict in which one admission could not be about what is consumed. The first and third are stated apart from the domain, and the
second by it, through `reason_excluded`, whose proof fails on a new case of `Reason` that a project in the domain could meet. -/
theorem reason_classified {o : Outcome} (h : Reason t dir treeDir o) :
    ExternalAnswer t dir treeDir ∨ Conflict t dir treeDir ∨ OutsideDomain t dir treeDir := by
  have houtside : OutsideDomain t dir treeDir := fun p ha hd => reason_excluded hd ha h
  cases h with
  | failed he _ hf => exact .inl (.failed he hf)
  | load hp hf => exact .inl (.failed hp.event hf)
  | toolchainFailed _ hr => exact .inl (.failed hr ⟨_, rfl⟩)
  | toolchainNoReal _ hr => exact .inl (.failed hr ⟨_, rfl⟩)
  | started h1 h2 h3 h4 h5 h6 h7 => exact .inl (.start h1 h2 h3 h4 h5 h6 h7)
  | treeDiffers _ _ hsub hne => exact .inl (.differs hsub hne)
  | notApart hp ht hne => exact .inr (.inl (.notApart hp ht hne))
  | configNotInTree ht _ hout => exact .inr (.inl (.outsideTree ht hout))
  | moduleNotInTree hs _ _ hout =>
    obtain ⟨hreal, -⟩ := hs.loaded
    exact .inr (.inl (.outsideTree hreal hout))
  | twoFiles hs hm hr hne => exact .inr (.inl (.twoFiles hs hm (.inl hr) hne))
  | twoRoots hs hm hm' hne => exact .inr (.inl (.twoFiles hs hm (.inr hm') hne))
  | twoTexts hs h1 h2 hp hne => exact .inr (.inl (.twoTexts hs h1 h2 hp hne))
  | importedRoot hs _ _ _ hl hr => exact .inr (.inl (.importedRoot hs hl hr))
  | configShadowed ht hm => exact .inr (.inl (.shadowed ht hm))
  | _ => exact .inr (.inr houtside)

/-- A rejected build is a failed answer, of Lean's own commands. -/
theorem buildRejected_external {sysroot : String} {tree : FilePath} (h : BuildRejected sysroot tree t) : ∃ e ∈ t, e.failed := by
  cases h with
  | build _ h2 h3 => exact ⟨_, h2, h3⟩
  | replay _ _ h3 h4 => exact ⟨_, h3, h4⟩

/-- What keeps the load of a finished build from giving an input is a failed answer. -/
theorem treeReason_external {sysroot : String} {tree : FilePath} (h : TreeReason sysroot tree t) : ∃ e ∈ t, e.failed := by
  cases h with
  | noTree h1 => exact ⟨_, h1, ⟨_, rfl⟩⟩
  | load _ h2 h3 => exact ⟨_, h2, h3⟩
  | build _ hf =>
    cases hf with
    | library _ _ h3 => exact ⟨_, h3, ⟨_, rfl⟩⟩
    | «import» _ h3 => exact ⟨_, h3, ⟨_, rfl⟩⟩
    | search _ _ _ h3 => exact ⟨_, h3, ⟨_, rfl⟩⟩

/-! ## A pass is owed to a project in the domain -/

/-- What a run of the full gate received on a project in the domain, whose reads answer as its files state, whose Lake commands and
every other operation answered, and whose rules hold. It names no reason. -/
structure DomainRun (p : Project) (t : List (Event L E)) (dir : FilePath) (prof : Regula.Closed.Profile) : Prop where
  /-- The project is in the domain. -/
  inDomain : p.InDomain
  /-- No answer of the run failed, the build's and the replay's included. -/
  answered : ∀ e ∈ t, ¬ e.failed
  /-- The reads answer as its files state. -/
  answers : ∀ tree rest, t = ⟨.createTempDir, .ok tree⟩ :: rest → Answers p (readPhase t) dir tree
  /-- The rules hold of what Lean's import gave. -/
  rules : ∀ tree rest sysroot root f roots, t = ⟨.createTempDir, .ok tree⟩ :: rest → SysrootIs (readPhase t) sysroot →
    TreeRoot sysroot tree (rulesPhase t) root → BuildRead (rulesPhase t) root f roots → LoadFloor f roots prof

/-- That gives what `FullOwed` states. -/
theorem DomainRun.fullOwed {p : Project} {prof : Regula.Closed.Profile} (h : DomainRun p t dir prof) : FullOwed t dir prof := by
  have hrules : ∀ {e : Event L E}, e ∈ rulesPhase t → e ∈ t := fun he => rulesPhase_subset he
  refine ⟨fun e he => h.answered _ he ⟨_, rfl⟩, fun tree rest o he => reason_excluded h.inDomain (h.answers tree rest he),
    fun tree rest s he _ hr => ?_, fun tree rest s he _ hr => ?_, h.rules⟩
  · obtain ⟨e, h1, h2⟩ := buildRejected_external hr
    exact h.answered e h1 h2
  · obtain ⟨e, h1, h2⟩ := treeReason_external hr
    exact h.answered e (hrules h1) h2

/-- **A project in the published domain is owed a full pass.** For every program that meets the record and every run of the full gate
on the pinned Lean: when the project at the directory is in the domain, its reads answer as its files state, no operation failed, the
Lake commands included, and the rules hold of what the build gave, the run exits with 0 and its last line is the full pass. This
statement names no case of `Reason`. What it leaves out is what `Answers` and `answered` state: a failed read, a file that another process
changes between two reads, and a Lake command that fails are no fault of the project, and they are not owed a pass. -/
theorem domain_owed {w : List String → Prog L E UInt32} (hw : RunMeets w) {text dir : String} {prof : Regula.Closed.Profile}
    (hp : Regula.Closed.Profile.ofSpelling? text = some prof) {rest : List (Event L E)} {c : UInt32}
    (h : Runs (w [text, "full", dir]) (⟨.leanVersion, Regula.Closed.pinnedLean⟩ :: rest) c) {project : Project}
    (hd : DomainRun project rest (FilePath.mk dir) prof) : c = 0 ∧ EndsWith rest fullPass :=
  run_full_owed hw hp h hd.fullOwed

end

end RegulaSpecification.Effects
