/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Program
import RegulaSpecification.Proofs.Standing

/-!
# What a pass means, and what it rests on

The theorems about a run read only what the run received. What those answers mean is what Lean, Lake and the operating
system do, and each such statement is a hypothesis of the theorem that needs it, re-read at each upgrade of Lean:
`LakeBehaviour` (H3), `RealPathBehaviour` (H4) and `LakeSelection` (H5) here, and `RegulaSpecification.Language.LeanBehaviour` (H1 and H2).
-/

namespace RegulaSpecification.Effects

open Lean (Name Import)
open System (FilePath)
open Regula.Effect
open Regula.Language
open RegulaSpecification.Language
open RegulaSpecification.Loader

variable {L E : Type}

/-- What a load of a build with a pass says of the environment: `pass_floor` on the path of the run. -/
theorem loaded_pass {gave : List (Event L E) → Root L → Prop} {why : List (Event L E) → Prop} {T : List (Event L E)}
    {p : Regula.Closed.Profile} {result : Except String Regula.Closed.Input} (hl : Loaded gave why T p result) (hv : (Regula.Closed.decision result).verdict = .pass) :
    ∃ (root : Root L) (f : Regula.Load.Facts) (roots : List Name), gave T root ∧ BuildRead T root f roots ∧
      EnvForm f ∧ EnvFloor f p ∧ (∀ r ∈ roots, r ∈ f.claimed) := by
  rcases hl with ⟨root, f, roots, hg, hb, rfl⟩ | ⟨-, m, rfl⟩
  · obtain ⟨h1, -, -, h4, h5⟩ := pass_floor hv
    exact ⟨root, f, roots, hg, hb, h4, h5, h1⟩
  · cases hv

/-- Exit 0 from a run of the proof verdict: the environment that Lean and Lake returned for the build has the closed form
and the floor. -/
theorem plain_exit_zero {t : List (Event L E)} {p : Regula.Closed.Profile} (h : PlainRun t p 0) :
    ∃ (root : Root L) (f : Regula.Load.Facts) (roots : List Name), PlainRoot t root ∧ BuildRead t root f roots ∧
      EnvForm f ∧ EnvFloor f p ∧ (∀ r ∈ roots, r ∈ f.claimed) := by
  obtain ⟨result, -, hl, hc, -⟩ := h
  exact loaded_pass hl ((Regula.Closed.Verdict.exitCode_eq_zero_iff _).mp hc.symm)

/-- Exit 0 from the full gate: a reading inside the closed language, on `Evidence`, with no read that failed; both Lake
commands ended with 0 on the tree; and the rules passed on what the load of that build gave. -/
theorem full_exit_zero {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile} (h : FullRun t dir p 0) :
    ∃ (tree : FilePath) (sysroot : String) (tRead tBuild tRules : List (Event L E)) (r : Reading), Inside r ∧
      Evidence tRead dir tree (written tRead) r ∧ (∀ e ∈ tRead, ¬ e.failed) ∧
      (∃ program lakeLib,
        ([⟨.lakeInstall sysroot, (program, lakeLib)⟩, ⟨.runLake program tree ["build", "--wfail"], .ok 0⟩,
          ⟨.runLake program tree replayArguments, .ok 0⟩] : List (Event L E)).Sublist tBuild) ∧
      ∃ (root : Root L) (f : Regula.Load.Facts) (roots : List Name),
        TreeRoot sysroot tree tRules root ∧ BuildRead tRules root f roots ∧ EnvForm f ∧ EnvFloor f p := by
  rcases h with ⟨e, rest, -, hc, -⟩ | ⟨tree, tRead, tGate, r, last, -, -, -, o, report, hdec, hnf, hn, ha, hc, -⟩
  · exact absurd hc (by decide)
  · have hrep : report = .full .pass := (Report.exitCode_eq_zero_iff report).mp hc.symm
    subst hrep
    cases o with
    | refused => cases (hn (by simp)).2
    | proofOnly => cases (hn (by simp)).2
    | incomplete => cases (hn (by simp)).2
    | admitted =>
      obtain ⟨r', -, hi, hev, -⟩ := hdec.1 rfl
      obtain ⟨sysroot, tBuild, tRules, -, -, hb⟩ := ha rfl
      rcases hb.2.2.1 with ⟨program, lakeLib, result, -, hsub, hl, hrep⟩ | ⟨hrep, -⟩
      · have hv : (Regula.Closed.decision result).verdict = .pass := (Report.full.inj hrep).symm
        obtain ⟨root, f, roots, hg, hbr, h1, h2, -⟩ := loaded_pass hl hv
        exact ⟨tree, sysroot, tRead, tBuild, tRules, r', hi, hev, hnf rfl, ⟨program, lakeLib, hsub⟩, root, f,
          roots, hg, hbr, h1, h2⟩
      · cases hrep

/-- H3: what Lake's build compiles for the default targets. A hypothesis about what a function of Lake does, at v4.35.0:
the modules of the default targets are those of each default library and the root of each default executable
(`Package.recCollectDefaultModules`, `Lake/Build/Package.lean:45-61`), and each other module is one that an import of what
it compiles reaches, through `findModule?` (`Module.recFetchInput`, `Lake/Build/Module.lean:30-38`,
`Lake/Config/Workspace.lean:279-280`), with the file `Module.leanFile`. A module of a default target may also have the file
that `findModule?` gives for its name (`Compiled.resolved`). No proof reaches it, because Lake's build is Lake's. -/
structure LakeBehaviour (headers : List (Name × Array Import)) (root : Root L)
    (modules : List (Name × FilePath)) where
  /-- Lake's build compiles this file for this module. -/
  Compiles : Name → FilePath → Prop
  /-- H3. -/
  h3 : ∀ m path, Compiles m path → Compiled headers root modules m path

/-- Every file Lake would compile for the claim is read, under H3, and its state is what was judged: for an admitted reading
and the state `held` of its `Evidence`, the file of each module that Lake compiles holds the text that the reading's file of
that module was parsed from. H3 says what Lake compiles. That Lake reads such a file as it stands is the rest of H3, and no
theorem here examines it. -/
theorem read_what_lake_compiles {t : List (Event L E)} {dir tree : FilePath} {held : List String → Option String} {r : Reading}
    (h : Evidence t dir tree held r) :
    ∃ (project real : FilePath) (sysroot : String) (root : Root L) (log : List String)
      (modules : List (Name × FilePath)) (headers : List (Name × Array Import)),
      (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t ∧
      (⟨.loadRoot sysroot real, .ok (some root, log)⟩ : Event L E) ∈ t ∧
      DefaultModules t root root.defaultTargets modules ∧
      ∀ (B : LakeBehaviour headers root modules) m path, B.Compiles m path →
        ∃ f ∈ r.files, f.module = m ∧ ∃ imports mods text, ReadText t project real f path imports mods text ∧
          held (parts path) = some text := by
  obtain ⟨project, real, hp, -, -, -, -, -, -, -, -, sysroot, root, log, modules, -, hl, hd, -, -, -, -, -, -, headers, -, -, -,
    hc, -⟩ := h
  refine ⟨project, real, sysroot, root, log, modules, headers, hp, hl, hd, fun B m path hb => ?_⟩
  obtain ⟨-, f, hf, hm, i, md, tx, -, hra, hst⟩ := hc m path (B.h3 m path hb)
  exact ⟨f, hf, hm, i, md, tx, hra, hst⟩

/-- H5: what Lake takes as the configuration of a directory, when its command line loads it. Lake's command line asks for a configuration with
no extension (`defaultConfigFile`, `Lake/CLI/Main.lean:48`, `Lake/Load/Config.lean:44`), and takes `lakefile.lean` when that name resolves, and
otherwise `lakefile.toml` when that name resolves (`resolveConfigFile`, `Lake/Load/Package.lean:109-117`). No proof reaches it, because Lake's
load is Lake's. `Takes` is the file it reads as the configuration, as a name in the tree. -/
structure LakeSelection (t : List (Event L E)) (real : FilePath) where
  /-- Lake takes this file as the configuration of the directory `real`. -/
  Takes : FilePath → Prop
  /-- H5, read at a run whose file system answered that nothing has the preferred name. -/
  h5 : ∀ err path, (⟨.symlinkMetadata (real / "lakefile.lean"), .error err⟩ : Event L E) ∈ t →
    (∃ name code details, err = .noFileOrDirectory name code details) → Takes path → parts path = parts (real / "lakefile.toml")

/-- H5 has a model: with an answer of an error for the preferred name, Lake takes `lakefile.toml`, and on a trace with no such answer it can take the preferred name. -/
theorem lakeSelection_model (real : FilePath) (err : IO.Error) :
    (∃ B : LakeSelection (L := L) (E := E) [] real, B.Takes (real / "lakefile.lean")) ∧
      ∃ B : LakeSelection (L := L) (E := E) [⟨.symlinkMetadata (real / "lakefile.lean"), .error err⟩] real, B.Takes (real / "lakefile.toml") :=
  ⟨⟨⟨(· = real / "lakefile.lean"), fun _ _ h => by cases h⟩, rfl⟩,
    ⟨(parts · = parts (real / "lakefile.toml")), fun _ _ _ _ h => h⟩, rfl⟩

/-- **Under H5, Lake takes the configuration judged**, at each consumer of a full run, on one answer for each operation: `real` is the real path of this run's tree, `path`
has the components of `lakefile.toml` there, a read through `path` in the last part of the reading gave the text that Lake's parser read, and each file that Lake takes in
`real` has those components. That the answer still holds when Lake runs is another process's matter, which this leaves unsaid. -/
theorem lake_takes_judged {t pre post : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile} {c : UInt32} (h : FullRun t dir p c) {e : Event L E}
    (ht : t = pre ++ e :: post) (he : e.consumesTree = true) (hone : OneAnswer t) :
    ∃ (tree real path : FilePath) (before suffix mid : List (Event L E)) (text : String) (table : Lake.Toml.Table),
      pre = (⟨.createTempDir, .ok tree⟩ :: (before ++ suffix)) ++ mid ∧ Quiet suffix ∧ (⟨.realPath tree, .ok real⟩ : Event L E) ∈ before ++ suffix ∧
      parts path = parts (real / "lakefile.toml") ∧ (⟨.readFile path, .ok text⟩ : Event L E) ∈ suffix ∧
      (⟨.parseToml (Lean.Parser.mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∈ before ++ suffix ∧
      ∀ B : LakeSelection pre real, ∀ taken, B.Takes taken → parts taken = parts path := by
  obtain ⟨tree, real, before, suffix, mid, err, path, text, table, hpre, hq, -, hreal, herr, hno, hp, hr, hpar⟩ := h.config_at_consumer ht he hone
  have hin {x : Event L E} (hx : x ∈ before ++ suffix) : x ∈ pre := by
    rw [hpre]
    simp only [List.mem_append, List.mem_cons]
    exact .inl (.inr (List.mem_append.mp hx))
  refine ⟨tree, real, path, before, suffix, mid, text, table, hpre, hq, hreal, hp, hr, hpar, fun B taken ht' => ?_⟩
  rw [hp]
  exact B.h5 err taken (hin (List.mem_append_right _ herr)) hno ht'


/-- H4: what successful `IO.FS.realPath` responses in this trace mean. Lean documents that the result contains no
symbolic links and coincides with POSIX `realpath` (`Init/System/IO.lean:874-881` at v4.35.0). The hypothesis relates
crossings to those responses, not to arbitrary paths; it says nothing about the filesystem after the observation. -/
structure RealPathBehaviour (t : List (Event L E)) where
  /-- The path crosses a link at the real-path observations in this trace. -/
  Crosses : FilePath → Prop
  /-- H4, only for a successful response actually received. -/
  h4 : ∀ path real, (⟨.realPath path, .ok real⟩ : Event L E) ∈ t →
    Crosses path → parts real ≠ parts path

/-- H4 is realizable with a crossing and an unchanged path: for any two different component lists, a trace can
resolve the first path to the second and leave the second unchanged. This is a model of the hypothesis, not a claim
that the filesystem is in that state. -/
theorem realPathBehaviour_crossing (link target : FilePath) (hne : parts target ≠ parts link) :
    ∃ B : RealPathBehaviour (L := L) (E := E)
      [⟨.realPath link, .ok target⟩, ⟨.realPath target, .ok target⟩],
      B.Crosses link ∧ ¬ B.Crosses target := by
  have hpaths : target ≠ link := fun h => hne (congrArg parts h)
  refine ⟨⟨(· = link), ?_⟩, rfl, hpaths⟩
  intro path real hm hc
  subst path
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h
  · cases h
    exact hne
  · have he := congrArg Event.op h
    have : link = target := by cases he; rfl
    exact (hpaths this.symm).elim

/-- Under H4, the file of a reading crossed no link, for the real path that the run received. -/
theorem read_no_link {t : List (Event L E)} {project tree path : FilePath} {f : FileRead}
    {imports : Array Import} {mods : List Name} (B : RealPathBehaviour t)
    (h : ReadAs t project tree f path imports mods) :
    ∃ (rel : List String) (real : FilePath), (⟨.realPath (under project rel), .ok real⟩ : Event L E) ∈ t ∧
      ¬ B.Crosses (under project rel) := by
  obtain ⟨_, rel, real, _, _, _, _, _, -, hr, -, hsub, -⟩ := h
  have observed := hsub.subset (by simp : (⟨.realPath (under project rel), .ok real⟩ : Event L E) ∈ _)
  exact ⟨rel, real, observed, fun hc => B.h4 _ _ observed hc hr⟩

end RegulaSpecification.Effects
