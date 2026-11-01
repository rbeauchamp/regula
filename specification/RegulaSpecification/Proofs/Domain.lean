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
Lake's load, Lean's parser and the operating system answered, and names no reason and none of the checker's functions. Some of its clauses are about the project. Those on the tree and failed answers are about no
project, and each negates an external answer that a reason cites, so that such a reason is ruled out by `Answers` and not by the domain. `reason_classified` sorts
each case of `Reason` under a failed or differing answer, a conflict in which one admission could not be about what is consumed, or a clause of the domain that
the project fails. `reason_excluded` states that no case holds of a project in the domain whose reads answer so. `domain_owed` states the result at the whole
run, for every program that meets the record, without naming `Reason`.

`Answers` holds what the program observes and what no proof can reach: each clause is about a response in the trace, never about
every value. So a run in which another process changes a file between two reads, so that two reads of one file differ, is not
covered by `domain_owed`: `Answers` fails, which is the accepted risk that the owner's account leaves unsaid. `domain_model`
states that these premises are met on the witness's answers, which `DomainModel.lean` says more of.
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
root that a response gave. That Lake's load is this function of the text is
what `Lake/Load/Toml.lean:484-500`, `Lake/Config/Module.lean:58-59` and `Lake/Config/LeanLibConfig.lean:144-146` say at v4.35.0, and
what no proof reaches, so it is a premise over the response. -/
structure LakeAgrees (c : Configuration) (imported : Name → Prop) (tree : FilePath) (t : List (Event L E)) (root : Root L) : Prop where
  /-- Each source directory is the tree joined with what the text's directories name, each target's below the package's. -/
  sourceDirs : ∀ d ∈ root.sourceDirs, ∃ rel ∈ c.sourceParts, parts d = parts tree ++ rel
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

/-- The responses of a reading of the project `p` at `dir`, in the checker's tree at `treeDir`, are what the files of `p` state, and the tree is as a run needs it. Each clause reads a response, and no clause names a reason. -/
structure Answers (p : Project) (t : List (Event L E)) (dir treeDir : FilePath) : Prop where
  /-- No answer failed. -/
  answered : ∀ e ∈ t, ¬ e.failed
  /-- A file of the project answers with what `p` states of it. -/
  read : ∀ project, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t → ∀ rel text,
    (⟨.readFile (under project rel), .ok text⟩ : Event L E) ∈ t →
      (rel = ["lean-toolchain"] → p.toolchainFile = some text) ∧ (rel = ["lakefile.toml"] → p.configFile = some text) ∧
        ∀ s ∈ p.sources, s.rel = rel → s.text = text
  /-- A file that `p` holds as a plain file is, by its real path, that path. -/
  real : ∀ project, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t → ∀ rel real,
    ((rel = ["lean-toolchain"] ∧ p.toolchainFile.isSome = true) ∨ (rel = ["lakefile.toml"] ∧ p.configFile.isSome = true) ∨ ∃ s ∈ p.sources, s.rel = rel) →
    (⟨.realPath (under project rel), .ok real⟩ : Event L E) ∈ t →
      ExactlyBelow project (under project rel) real
  /-- When the name `lakefile.lean` answers, `p` holds it. -/
  leanConfig : ∀ project, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t → ∀ metadata,
    (⟨.symlinkMetadata (project / "lakefile.lean"), .ok metadata⟩ : Event L E) ∈ t → p.leanConfig = true
  /-- What Lake's TOML parser gave of a text: the key paths and the nesting that `p` states. -/
  toml : ∀ text table, (⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∈ t →
    (∀ k, KeyPath .anonymous table k → k ∈ p.config.keys) ∧ ∀ n, Deeper n table → n ≤ p.config.nesting
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
domain or of the answers. A case of `Reason` that no clause meets does not prove here. A clause of `Answers` that only negates a case would hide that, and those are
the external answers and `notApart`, `configNotInTree`, the part of `moduleNotInTree` about a directory above a file, and `configShadowed`. -/
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
    exact hne (ha.real _ hp ["lean-toolchain"] _ (.inl ⟨rfl, by obtain ⟨t₀, h₀, -⟩ := hd.toolchain; rw [h₀]; rfl⟩) hr)
  | toolchainNoReal hp hr => exact ha.answered _ hr ⟨_, rfl⟩
  | tomlNotExact hp hr hne =>
    exact hne (ha.real _ hp ["lakefile.toml"] _ (.inr (.inl ⟨rfl, hd.plainConfig⟩)) hr)
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
    exact hne (ha.real _ hs.project_real _ _ (.inr (.inr ⟨s, hsm, rfl⟩)) hr)
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
    obtain ⟨rel, hrm, hp⟩ := (ha.lake _ sy _ log hreal hload).sourceDirs _ hdir
    have hone {s : String} (hs : s ∈ p.config.sourceDirs) {c : String} (hc : c ∈ RegulaSpecification.Domain.components s) : c ≠ "" ∧ c.front ≠ '.' := by
      obtain ⟨-, hc2⟩ := List.mem_filter.mp hc
      simp only [Bool.and_eq_true, bne_iff_ne] at hc2
      exact ⟨hc2.1, (hd.config.sourceDirs s hs).2 c hc⟩
    have hpkg : p.config.srcDir ∈ p.config.sourceDirs := by simp [Configuration.sourceDirs]
    refine hno _ ⟨hp, fun c hc => ?_⟩
    simp only [Configuration.sourceParts, List.mem_cons, List.mem_append, List.mem_map] at hrm
    rcases hrm with (rfl | ⟨lib, hl, rfl⟩) | ⟨exe, hx, rfl⟩
    · exact hone hpkg hc
    · rcases List.mem_append.mp hc with hc | hc
      · exact hone hpkg hc
      · exact hone (by simp only [Configuration.sourceDirs, List.mem_cons, List.mem_append, List.mem_map]; exact .inl (.inr ⟨lib, hl, rfl⟩)) hc
    · rcases List.mem_append.mp hc with hc | hc
      · exact hone hpkg hc
      · exact hone (by simp only [Configuration.sourceDirs, List.mem_cons, List.mem_append, List.mem_map]; exact .inr ⟨exe, hx, rfl⟩) hc
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

/-- A failed or differing external answer: an answer failed, or a planned file answered otherwise than what was written to it. -/
inductive ExternalAnswer (t : List (Event L E)) (dir treeDir : FilePath) : Prop where
  /-- An answer failed. -/
  | failed {e : Event L E} : e ∈ t → e.failed → ExternalAnswer t dir treeDir
  /-- A planned file answered otherwise than what was written to it. -/
  | differs {project tree root modules path text r} : Scene t dir treeDir project tree root modules →
      Planned t project tree root modules path text →
      ([⟨.writeFile path text, .ok ()⟩, ⟨.readFile path, r⟩] : List (Event L E)).Sublist t → r ≠ .ok text →
      ExternalAnswer t dir treeDir
/-- A conflict in which one admission could not be about what is consumed: writing to the tree would write to the project, a file
that would be written lies outside the tree, one name has two files, one path has two texts, an import names a file other than the
one read for that name, or something in the tree is what Lake would take as its configuration. -/
inductive Conflict (t : List (Event L E)) (dir treeDir : FilePath) : Prop where
  /-- The project and the tree do not lie apart. -/
  | notApart {project tree} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t → (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
      ¬ Apart project tree → Conflict t dir treeDir
  /-- A copy of the configuration would lie outside the tree. -/
  | configOutside {tree path} : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
      (path = tree / "lakefile.toml" ∨ path = tree / "lean-toolchain") → OutsideTree tree path → Conflict t dir treeDir
  /-- A needed file would lie outside the tree. -/
  | moduleOutside {project tree root modules m path} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → FileOfModule root modules m path → OutsideTree tree path → Conflict t dir treeDir
  /-- One name, two files, by components. -/
  | twoFiles {project tree root modules m file other} : Scene t dir treeDir project tree root modules →
      (m, file) ∈ modules → (root.resolve m = some other ∨ (m, other) ∈ modules) → parts other ≠ parts file → Conflict t dir treeDir
  /-- One path, two texts. -/
  | twoTexts {project tree root modules path text path' text'} : Scene t dir treeDir project tree root modules →
      Planned t project tree root modules path text → Planned t project tree root modules path' text' →
      parts path = parts path' → text ≠ text' → Conflict t dir treeDir
  /-- An import, by a file the build needs, names a default executable's root that no library holds, so not the file read for that name. -/
  | importedRoot {project tree root modules m imports i} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → HeaderOf t project tree root modules m imports → i ∈ imports →
      (modules.lookup i.module).isSome = true → root.resolve i.module = none → Conflict t dir treeDir
  /-- Something in the tree answers to the name that Lake prefers as its configuration. -/
  | shadowed {tree metadata} : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
      (⟨.symlinkMetadata (tree / "lakefile.lean"), .ok metadata⟩ : Event L E) ∈ t → Conflict t dir treeDir

/-- A project outside the published domain, each case named for the clause of `Project.InDomain` that it bears on, and holding what a response said. The line that a run
prints for such a case is read from the code (`Regula.Reader.findingLines`), and no theorem here states it. -/
inductive OutsideDomain (t : List (Event L E)) (dir treeDir : FilePath) : Prop where
  /-- `toolchain`: `lean-toolchain` names another Lean. -/
  | toolchain {project text} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.readFile (project / "lean-toolchain"), .ok text⟩ : Event L E) ∈ t → text.trimAscii.toString ≠ leanToolchain → OutsideDomain t dir treeDir
  /-- `toolchain`: `lean-toolchain` is not a plain file by exactly that name. -/
  | toolchainNotPlain {project real} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.realPath (project / "lean-toolchain"), .ok real⟩ : Event L E) ∈ t →
      ¬ ExactlyBelow project (project / "lean-toolchain") real → OutsideDomain t dir treeDir
  /-- `plainConfig`: `lakefile.toml` is not a plain file by exactly that name. -/
  | tomlNotPlain {project real} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.realPath (project / "lakefile.toml"), .ok real⟩ : Event L E) ∈ t →
      ¬ ExactlyBelow project (project / "lakefile.toml") real → OutsideDomain t dir treeDir
  /-- `noLeanConfig`: something has the name `lakefile.lean`. -/
  | leanConfig {project metadata} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.symlinkMetadata (project / "lakefile.lean"), .ok metadata⟩ : Event L E) ∈ t → OutsideDomain t dir treeDir
  /-- `keys`: a key outside the closed set. -/
  | key {table k} : TomlRead t dir table → KeyPath .anonymous table k → k.getRoot ≠ `require → ¬ ConfigKeyAdmitted k → OutsideDomain t dir treeDir
  /-- `shallow`: a key deeper than the reader follows. -/
  | deep {table} : TomlRead t dir table → Deeper 8 table → OutsideDomain t dir treeDir
  /-- `noDependency`: a `require`. -/
  | dependency {table k} : TomlRead t dir table → KeyPath .anonymous table k → k.getRoot = `require → OutsideDomain t dir treeDir
  /-- `sourceDirs`: a source directory that does not lie below the tree. -/
  | openDir {tree root d} : TreeLoaded t dir treeDir tree root → d ∈ root.sourceDirs →
      (∀ rel, ¬ TreeRelative (parts tree) (parts d) rel) → OutsideDomain t dir treeDir
  /-- `globs`: a `globs` entry that is no single module. -/
  | openGlob {tree root lib g} : TreeLoaded t dir treeDir tree root → lib ∈ root.libraries → g ∈ lib.2 → (∀ n, g ≠ .one n) → OutsideDomain t dir treeDir
  /-- `claimsSomething`: no module is claimed. -/
  | noClaim {project tree root} : Scene t dir treeDir project tree root [] → OutsideDomain t dir treeDir
  /-- `targetNames`: a target's name outside the closed domain. -/
  | targetName {tree root n} : TreeLoaded t dir treeDir tree root → n ∈ root.targets → ¬ ClosedModuleName n → OutsideDomain t dir treeDir
  /-- `claimRead` and `imports`: the file of a needed name is not a plain file by exactly its path, as a source is. -/
  | moduleNotPlain {project tree root modules m path rel real} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → FileOfModule root modules m path → TreeRelative (parts tree) (parts path) rel →
      (⟨.realPath (under project rel), .ok real⟩ : Event L E) ∈ t → ¬ ExactlyBelow project (under project rel) real →
      OutsideDomain t dir treeDir
  /-- `moduleNames`: a needed name outside the closed domain. -/
  | moduleName {project tree root modules m} : Scene t dir treeDir project tree root modules → Named t project tree root modules m →
      ¬ ClosedModuleName m → OutsideDomain t dir treeDir
  /-- `bounded`: more names than the reader follows. -/
  | tooMany {project tree root modules} {ms : List (Name × Array Import)} : Scene t dir treeDir project tree root modules → (ms.map (·.1)).Nodup →
      (∀ x ∈ ms, Named t project tree root modules x.1 ∧ HeaderOf t project tree root modules x.1 x.2) →
      1000000 < modules.length + (ms.map (·.2.size)).sum → OutsideDomain t dir treeDir
  /-- `noMathlib`: Mathlib is in what the build needs. -/
  | mathlib {project tree root modules m} : Scene t dir treeDir project tree root modules → Named t project tree root modules m →
      m.getRoot = `Mathlib → OutsideDomain t dir treeDir
  /-- `language`: a needed file is not in the closed language. -/
  | file {project tree root modules f path imports mods} {headers : List (Name × Array Import)} {held : List Name} :
      Scene t dir treeDir project tree root modules → Named t project tree root modules f.module → FileOfModule root modules f.module path →
      ReadAs t project tree f path imports mods → (∀ x ∈ headers, HeaderOf t project tree root modules x.1 x.2) →
      (∀ n ∈ held, Named t project tree root modules n ∧ HeldByToolchain t n) → (∀ i ∈ imports, i.module ∈ held ∨ (headers.lookup i.module).isSome = true) →
      (∀ x ∈ headers, ∀ i ∈ x.2, i.module ∈ held ∨ (headers.lookup i.module).isSome = true) →
      (∀ n, n ∈ mods ↔ ∃ m ∈ imports, Sees headers held m.module n) → ¬ FileAdmitted f → OutsideDomain t dir treeDir

/-- **Each reason falls under one of three**: a failed or differing external answer, a conflict in which one admission
could not be about what is consumed, or a clause of the domain that the project fails. Its proof sends each case of `Reason` to one. -/
theorem reason_classified {o : Outcome} (h : Reason t dir treeDir o) :
    ExternalAnswer t dir treeDir ∨ Conflict t dir treeDir ∨ OutsideDomain t dir treeDir := by
  cases h with
  | failed he _ hf => exact .inl (.failed he hf)
  | load hp hf => exact .inl (.failed hp.event hf)
  | toolchainFailed _ hr => exact .inl (.failed hr ⟨_, rfl⟩)
  | toolchainNoReal _ hr => exact .inl (.failed hr ⟨_, rfl⟩)
  | treeDiffers hs hp hsub hne => exact .inl (.differs hs hp hsub hne)
  | notApart hp ht hne => exact .inr (.inl (.notApart hp ht hne))
  | configNotInTree ht hp hout => exact .inr (.inl (.configOutside ht hp hout))
  | moduleNotInTree hs hn hf hout => exact .inr (.inl (.moduleOutside hs hn hf hout))
  | twoFiles hs hm hr hne => exact .inr (.inl (.twoFiles hs hm (.inl hr) hne))
  | twoRoots hs hm hm' hne => exact .inr (.inl (.twoFiles hs hm (.inr hm') hne))
  | twoTexts hs h1 h2 hp hne => exact .inr (.inl (.twoTexts hs h1 h2 hp hne))
  | importedRoot hs hn hh hi hl hr => exact .inr (.inl (.importedRoot hs hn hh hi hl hr))
  | configShadowed ht hm => exact .inr (.inl (.shadowed ht hm))
  | toolchain h1 h2 h3 => exact .inr (.inr (.toolchain h1 h2 h3))
  | toolchainNotExact h1 h2 h3 => exact .inr (.inr (.toolchainNotPlain h1 h2 h3))
  | tomlNotExact h1 h2 h3 => exact .inr (.inr (.tomlNotPlain h1 h2 h3))
  | moduleNotExact h1 h2 h3 h4 h5 h6 => exact .inr (.inr (.moduleNotPlain h1 h2 h3 h4 h5 h6))
  | leanConfig h1 h2 => exact .inr (.inr (.leanConfig h1 h2))
  | key h1 h2 h3 h4 => exact .inr (.inr (.key h1 h2 h3 h4))
  | deep h1 h2 => exact .inr (.inr (.deep h1 h2))
  | deepDependency h1 h2 => exact .inr (.inr (.deep h1 h2))
  | dependency h1 h2 h3 => exact .inr (.inr (.dependency h1 h2 h3))
  | openDir h1 h2 h3 => exact .inr (.inr (.openDir h1 h2 h3))
  | openGlob h1 h2 h3 h4 => exact .inr (.inr (.openGlob h1 h2 h3 h4))
  | noClaim h1 => exact .inr (.inr (.noClaim h1))
  | targetName h1 h2 h3 => exact .inr (.inr (.targetName h1 h2 h3))
  | moduleName h1 h2 h3 => exact .inr (.inr (.moduleName h1 h2 h3))
  | tooMany h1 h2 h3 h4 => exact .inr (.inr (.tooMany h1 h2 h3 h4))
  | mathlib h1 h2 h3 => exact .inr (.inr (.mathlib h1 h2 h3))
  | file h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => exact .inr (.inr (.file h1 h2 h3 h4 h5 h6 h7 h8 h9 h10))

/-- A failed or differing answer is no answer of the kind `Answers` states, for any project. -/
theorem ExternalAnswer.not_answers (h : ExternalAnswer t dir treeDir) (ha : Answers p t dir treeDir) : False := by
  cases h with
  | failed he hf => exact ha.answered _ he hf
  | differs hs hp hsub hne => exact hne (ha.writes _ _ _ _ _ _ _ hs hp hsub)

/-- A conflict is a reason, so no project in the domain whose reads answer as its files state has one. -/
theorem Conflict.excluded (h : Conflict t dir treeDir) (hd : p.InDomain) (ha : Answers p t dir treeDir) : False := by
  cases h with
  | notApart h1 h2 h3 => exact reason_excluded hd ha (.notApart h1 h2 h3)
  | configOutside h1 h2 h3 => exact reason_excluded hd ha (.configNotInTree h1 h2 h3)
  | moduleOutside h1 h2 h3 h4 => exact reason_excluded hd ha (.moduleNotInTree h1 h2 h3 h4)
  | twoFiles h1 h2 h3 h4 =>
    rcases h3 with h3 | h3
    · exact reason_excluded hd ha (.twoFiles h1 h2 h3 h4)
    · exact reason_excluded hd ha (.twoRoots h1 h2 h3 h4)
  | twoTexts h1 h2 h3 h4 h5 => exact reason_excluded hd ha (.twoTexts h1 h2 h3 h4 h5)
  | importedRoot h1 h2 h3 h4 h5 h6 => exact reason_excluded hd ha (.importedRoot h1 h2 h3 h4 h5 h6)
  | shadowed h1 h2 => exact reason_excluded hd ha (.configShadowed h1 h2)

/-- **A reason of this class holds of no project in the domain**, among those whose reads answer so. -/
theorem OutsideDomain.excluded (h : OutsideDomain t dir treeDir) (ha : Answers p t dir treeDir) : ¬ p.InDomain := by
  intro hd
  cases h with
  | toolchain h1 h2 h3 => exact reason_excluded hd ha (.toolchain h1 h2 h3)
  | toolchainNotPlain h1 h2 h3 => exact reason_excluded hd ha (.toolchainNotExact h1 h2 h3)
  | tomlNotPlain h1 h2 h3 => exact reason_excluded hd ha (.tomlNotExact h1 h2 h3)
  | leanConfig h1 h2 => exact reason_excluded hd ha (.leanConfig h1 h2)
  | key h1 h2 h3 h4 => exact reason_excluded hd ha (.key h1 h2 h3 h4)
  | deep h1 h2 => exact reason_excluded hd ha (.deep h1 h2)
  | dependency h1 h2 h3 => exact reason_excluded hd ha (.dependency h1 h2 h3)
  | openDir h1 h2 h3 => exact reason_excluded hd ha (.openDir h1 h2 h3)
  | openGlob h1 h2 h3 h4 => exact reason_excluded hd ha (.openGlob h1 h2 h3 h4)
  | noClaim h1 => exact reason_excluded hd ha (.noClaim h1)
  | targetName h1 h2 h3 => exact reason_excluded hd ha (.targetName h1 h2 h3)
  | moduleNotPlain h1 h2 h3 h4 h5 h6 => exact reason_excluded hd ha (.moduleNotExact h1 h2 h3 h4 h5 h6)
  | moduleName h1 h2 h3 => exact reason_excluded hd ha (.moduleName h1 h2 h3)
  | tooMany h1 h2 h3 h4 => exact reason_excluded hd ha (.tooMany h1 h2 h3 h4)
  | mathlib h1 h2 h3 => exact reason_excluded hd ha (.mathlib h1 h2 h3)
  | file h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => exact reason_excluded hd ha (.file h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)

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
  rules : ∀ tree rest sysroot root a roots, t = ⟨.createTempDir, .ok tree⟩ :: rest → SysrootIs (readPhase t) sysroot →
    TreeRoot sysroot tree (rulesPhase t) root → BuildAnswered (rulesPhase t) root a roots → a.Floor roots prof

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
on the pinned Lean: when the project at the directory is in the domain, its reads answer as `Answers` states, no answer failed as `Event.failed` counts one, the
Lake commands' included, and the rules hold of what the build gave, the run exits with 0 and its last line is the full pass. This
statement names no case of `Reason`. What it leaves out is what `Answers` and `answered` state: a failed read and a file that another process changes
between two reads, which are no fault of the project, and a Lake command that fails, which a proof that does not check also gives, are not owed a pass. -/
theorem domain_owed {w : List String → Prog L E UInt32} (hw : RunMeets w) {text dir : String} {prof : Regula.Closed.Profile}
    (hp : text = prof.spelling) {rest : List (Event L E)} {c : UInt32}
    (h : Runs (w [text]) (⟨.leanVersion, Regula.Closed.pinnedLean⟩ :: ⟨.getEnv Regula.Shell.fullVariable, some dir⟩ :: rest) c) {project : Project}
    (hd : DomainRun project rest (FilePath.mk dir) prof) : c = 0 ∧ EndsWith rest (fullPass (FilePath.mk dir)) :=
  run_full_owed hw hp h hd.fullOwed

end

end RegulaSpecification.Effects
