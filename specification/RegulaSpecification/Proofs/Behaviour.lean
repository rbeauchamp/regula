/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Program

/-!
# What a pass means, and what it rests on

The theorems about a run read only what the run received. What those answers mean is what Lean, Lake and the operating
system do, and each such statement is a hypothesis of the theorem that needs it, re-read at each upgrade of Lean:
`LakeBehaviour` (H3) and `RealPathBehaviour` (H4) here, and `RegulaSpecification.Language.LeanBehaviour` (H1 and H2).
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
theorem loaded_pass {T : List (Event L E)} {p : Regula.Closed.Profile} {result : Except String Regula.Closed.Input}
    (hl : Loaded T p result) (hv : (Regula.Closed.decision result).verdict = .pass) :
    ∃ (root : Root L) (f : Regula.Load.Facts) (roots : List Name), BuildRead T root f roots ∧ EnvForm f ∧
      EnvFloor f p ∧ (∀ r ∈ roots, r ∈ f.claimed) := by
  rcases hl with ⟨root, f, roots, hb, rfl⟩ | ⟨-, why, rfl⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, why, rfl⟩
  · obtain ⟨h1, -, -, h4, h5⟩ := pass_floor hv
    exact ⟨root, f, roots, hb, h4, h5, h1⟩
  · cases hv
  · cases hv

/-- Exit 0 from a run of the proof verdict: the environment that Lean and Lake returned for the build has the closed form
and the floor. -/
theorem plain_exit_zero {t : List (Event L E)} {p : Regula.Closed.Profile} (h : PlainRun t p 0) :
    ∃ (root : Root L) (f : Regula.Load.Facts) (roots : List Name), BuildRead t root f roots ∧ EnvForm f ∧
      EnvFloor f p ∧ (∀ r ∈ roots, r ∈ f.claimed) := by
  obtain ⟨result, hl, hc, -, -⟩ := h
  exact loaded_pass hl ((Regula.Closed.Verdict.exitCode_eq_zero_iff _).mp hc.symm)

/-- Exit 0 from the full gate: a reading inside the closed language, on `Evidence`, with no read that failed; both Lake
commands ended with 0 on the tree; and the rules passed on what the load of that build gave. -/
theorem full_exit_zero {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile} (h : FullRun t dir p 0) :
    ∃ (tree : FilePath) (tRead tBuild tRules : List (Event L E)) (r : Reading), Inside r ∧ Evidence tRead dir tree r ∧ (∀ e ∈ tRead, ¬ e.failedRead) ∧
      (∃ program args,
        ([⟨.runLake program tree ["build", "--wfail"], .ok 0⟩, ⟨.runLake program tree ("check" :: args), .ok 0⟩] :
          List (Event L E)).Sublist tBuild) ∧
      ∃ (root : Root L) (f : Regula.Load.Facts) (roots : List Name),
        BuildRead tRules root f roots ∧ EnvForm f ∧ EnvFloor f p := by
  rcases h with ⟨e, -, hc, -⟩ | ⟨tree, tRead, tGate, r, last, -, -, o, report, hdec, hnf, hn, ha, hc, -, -⟩
  · exact absurd hc (by decide)
  · have hrep : report = .full .pass := (Report.exitCode_eq_zero_iff report).mp hc.symm
    subst hrep
    cases o with
    | refused => cases (hn (by simp)).2
    | proofOnly => cases (hn (by simp)).2
    | incomplete => cases (hn (by simp)).2
    | admitted =>
      obtain ⟨r', hi, hev⟩ := hdec.1 rfl
      obtain ⟨tBuild, tRules, -, hb⟩ := ha rfl
      rcases hb with ⟨program, args, result, hsub, hl, hrep⟩ | ⟨hrep, -⟩
      · have hv : (Regula.Closed.decision result).verdict = .pass := (Report.full.inj hrep).symm
        obtain ⟨root, f, roots, hbr, h1, h2, -⟩ := loaded_pass hl hv
        exact ⟨tree, tRead, tBuild, tRules, r', hi, hev, hnf rfl, ⟨program, args, hsub⟩, root, f, roots, hbr, h1, h2⟩
      · cases hrep

/-- H3: what Lake's build compiles for the default targets. A hypothesis about what a function of Lake does, at v4.35.0:
the modules of the default targets are those of each default library and the root of each default executable
(`Package.recCollectDefaultModules`, `Lake/Build/Package.lean:45-61`), and each other module is one that an import of what
it compiles reaches, through `findModule?` (`Module.recFetchInput`, `Lake/Build/Module.lean:30-38`,
`Lake/Config/Workspace.lean:279-280`), with the file `Module.leanFile`. No proof reaches it, because Lake's build is
Lake's. -/
structure LakeBehaviour (headers : List (Name × Array Import)) (root : Root L)
    (modules : List (Name × FilePath)) where
  /-- Lake's build compiles this file for this module. -/
  Compiles : Name → FilePath → Prop
  /-- H3. -/
  h3 : ∀ m path, Compiles m path → Compiled headers root modules m path

/-- Every file Lake would compile for the claim is read, under H3: for an admitted reading, the file of each module that
Lake compiles is what the reading holds of it. -/
theorem read_what_lake_compiles {t : List (Event L E)} {dir tree : FilePath} {r : Reading}
    (h : Evidence t dir tree r) :
    ∃ (project real : FilePath) (sysroot : String) (root : Root L) (log : List String)
      (modules : List (Name × FilePath)) (headers : List (Name × Array Import)),
      (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t ∧
      (⟨.loadRoot sysroot real, .ok (some root, log)⟩ : Event L E) ∈ t ∧
      DefaultModules t root root.defaultTargets modules ∧
      ∀ (B : LakeBehaviour headers root modules) m path, B.Compiles m path →
        ∃ f ∈ r.files, f.module = m ∧ ∃ imports mods, ReadAs t project real f path imports mods := by
  obtain ⟨project, real, hp, -, -, -, -, -, -, sysroot, root, log, modules, hl, hd, -, headers, -, hc, -⟩ := h
  exact ⟨project, real, sysroot, root, log, modules, headers, hp, hl, hd,
    fun B m path hb => hc m path (B.h3 m path hb)⟩

/-- H4: what `IO.FS.realPath` gives. A hypothesis about the operating system's function as Lean gives it: it coincides with
POSIX `realpath` (`Init/System/IO.lean:876-879` at v4.35.0), so the real path of a path that crosses a link differs from it. -/
structure RealPathBehaviour where
  /-- The path crosses a link at some depth. -/
  Crosses : FilePath → Prop
  /-- H4. -/
  h4 : ∀ path real, Crosses path → parts real ≠ parts path

/-- Under H4, the file of a reading crossed no link, for the real path that the run received. -/
theorem read_no_link {t : List (Event L E)} {project tree path : FilePath} {f : FileRead}
    {imports : Array Import} {mods : List Name} (B : RealPathBehaviour)
    (h : ReadAs t project tree f path imports mods) :
    ∃ (rel : List String) (real : FilePath), (⟨.realPath (under project rel), .ok real⟩ : Event L E) ∈ t ∧
      ¬ B.Crosses (under project rel) := by
  obtain ⟨rel, real, _, _, _, _, _, _, -, hr, -, hsub, -⟩ := h
  exact ⟨rel, real, hsub.subset (by simp), fun hc => B.h4 _ _ hc hr⟩

end RegulaSpecification.Effects
