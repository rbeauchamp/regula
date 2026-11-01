/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Domain
import RegulaSpecification.Proofs.DomainCases
import RegulaSpecification.Proofs.OwedModel

/-!
# The premises of `domain_owed` are met by a run

`domain_model` states that the program the executable interprets, on the answers of the witness (`RegulaSpecification.Effects.answers`), meets
`DomainRun` for a project of one module, and exits with 0. Like `full_model`, it is conditional on `WitnessPaths` and `EnvModel`, for the reason
they state, and on `WitnessDomain`, which says what the paths of that witness are. So `Answers` and `InDomain` hold together on those answers. They are no
answers of a real Lake, whose root lists the library that `witnessRoot` leaves out: a real run's `Answers` rests on what the specification measures of `LakeAgrees`.

`answers_admit_outside` states that `Answers` does not imply the domain: the same answers fit a project that is outside it. `build_fails_model`
states that `Answers` and the domain do not settle the verdict: on the same reading, a build that fails gives no exit 0.

`twoSpellings_read` is the audit's project at the level of the program: `configUnread` leaves unread no name that two targets hold with two
spellings of one path.
-/

namespace RegulaSpecification.Effects

open Lean (Name)
open System (FilePath)
open Regula.Effect
open Regula.Language
open Regula.Reader
open Regula.Shell
open RegulaSpecification.Language
open RegulaSpecification.Domain
open RegulaSpecification.Domain.Configuration

/-- `Answers` holds of each part of a trace it holds of, for a segment within it. -/
theorem Answers.of_infix {L E : Type} {p : Project} {T T' : List (Event L E)} {dir treeDir : FilePath} (hi : T <:+: T')
    (h : Answers p T' dir treeDir) : Answers p T dir treeDir := by
  have m {e : Event L E} (he : e ∈ T) : e ∈ T' := hi.subset he
  refine ⟨fun e he => h.answered e (m he), fun pr hp rel text hr => h.read pr (m hp) rel text (m hr),
    fun pr hp rel real hrel hr => h.real pr (m hp) rel real hrel (m hr), fun pr hp md hr => h.leanConfig pr (m hp) md (m hr),
    fun text table hr => h.toml text table (m hr),
    fun pr s pg ll app real lp h1 h2 h3 h4 h5 h6 => h.start pr s pg ll app real lp (m h1) (m h2) (m h3) (m h4) (m h5) (m h6),
    fun pr tr h1 h2 => h.apart pr tr (m h1) (m h2), fun tr h1 => h.copies tr (m h1), fun tr s root log h1 h2 => ?_,
    fun pr tr root mods md path d hs hf hd => h.parents pr tr root mods md path d (Scene.mono hi hs) hf hd,
    fun text name hh st ms imports he => h.header text name hh st ms imports (m he),
    fun pr tr f path i md h1 h2 => h.parse pr tr f path i md (m h1) (ReadAs.mono hi.sublist h2),
    fun tr s root log md ol real h1 h2 h3 h4 h5 =>
      let ⟨d, hd, hb⟩ := h.toolchain tr s root log md ol real (m h1) (m h2) h3 (m h4) (m h5)
      ⟨d, hd, fun dr hx => hb dr (m hx)⟩,
    fun pr tr root mods path text r hs hp hsub =>
      h.writes pr tr root mods path text r (Scene.mono hi hs) (Planned.mono hi.sublist hp) (hsub.trans hi.sublist),
    fun tr md h1 h2 => h.shadow tr md (m h1) (m h2)⟩
  · have ha := h.lake tr s root log (m h1) (m h2)
    refine ⟨ha.sourceDirs, ha.libraries, ha.defaultTargets, ha.targets, fun n hn l hl => ?_, ha.noLib, ha.findExe, ha.noExe,
      ha.resolve, ha.noResolve⟩
    obtain ⟨lib, h3, h4⟩ := ha.findLib n hn l hl
    exact ⟨lib, h3, fun ms he => h4 ms (m he)⟩

/-- The configuration of the witness: one library `Good`. -/
def witnessConfig : Configuration :=
  ⟨[`name], 0, ".", [⟨`Good, ".", [`Good], [.one `Good]⟩], [], [`Good]⟩

/-- The project of the witness: every read gives the pinned text, and one module, `Good`, whose file imports nothing. -/
def witnessProject : Project where
  toolchainFile := some leanToolchain
  leanConfig := false
  configFile := some leanToolchain
  config := witnessConfig
  sources := [⟨`Good, ["Good.lean"], leanToolchain, #[], goodFile⟩]
  toolchainModules := []

theorem witnessConfig_claim : witnessConfig.claim = [(`Good, ["Good.lean"])] := by decide +kernel

theorem witnessConfig_in : witnessConfig.InDomain := (check_iff _).mp (by decide +kernel)

/-- That project is in the domain, given that the pinned text trimmed is itself, which `WitnessPaths` holds. -/
theorem witnessProject_in (hpin : leanToolchain.trimAscii.toString = leanToolchain) : witnessProject.InDomain := by
  refine ⟨⟨leanToolchain, rfl, hpin⟩, rfl, rfl, witnessConfig_in, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change x ∈ witnessConfig.claim at hx
    rw [witnessConfig_claim, List.mem_singleton] at hx
    subst hx
    exact ⟨_, List.mem_singleton.mpr rfl, rfl, rfl⟩
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    refine .inl ?_
    change _ ∈ witnessConfig.claim
    rw [witnessConfig_claim]
    exact List.mem_singleton.mpr rfl
  · decide +kernel
  · intro s hs i hi
    obtain rfl := List.mem_singleton.mp hs
    cases hi with | mk h => cases h
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact good_closed_name
  · intro m hm
    cases hm
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    decide +kernel
  · intro m hm
    cases hm
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact ⟨rfl, goodFile_admitted⟩
  · intro s hs s' hs' _
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hs'
    rfl
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    decide +kernel
  · intro s hs c hc
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hc
    decide +kernel
  · decide +kernel

/-- What the witness's paths must be for its project to be the one its answers describe: the file of `Good` lies at `Good.lean` below the
tree, and the two copies at their names. As with `WitnessPaths`, `System.FilePath` depends on an opaque constant, so no theorem discharges
these. -/
structure WitnessDomain (w : WitnessPaths) : Prop where
  /-- Its components below the tree. -/
  rel : w.rel = ["Good.lean"]
  /-- Its file. -/
  file : parts w.file = parts w.tree ++ ["Good.lean"]
  /-- The copy of the configuration. -/
  toml : parts (w.tree / "lakefile.toml") = parts w.tree ++ ["lakefile.toml"]
  /-- The copy of the toolchain's file. -/
  chain : parts (w.tree / "lean-toolchain") = parts w.tree ++ ["lean-toolchain"]

variable {α : Type}

/-- On the answers of the witness, the reads answer as the witness's project states. -/
theorem answers_witness {w : WitnessPaths} {env : Lean.Environment} (hw : WitnessDomain w) (q : Prog Unit Unit α) :
    Answers witnessProject (traceWith (answers w env) q) w.project w.tree := by
  have hreal : ∀ {a b : FilePath}, (⟨.realPath a, .ok b⟩ : Event Unit Unit) ∈ traceWith (answers w env) q → b = a := fun h =>
    Except.ok.inj (resp_eq h : (Except.ok _ : Except IO.Error FilePath) = .ok _)
  have hread : ∀ {a : FilePath} {x : String}, (⟨.readFile a, .ok x⟩ : Event Unit Unit) ∈ traceWith (answers w env) q → x = leanToolchain :=
    fun h => Except.ok.inj (resp_eq h : (Except.ok _ : Except IO.Error String) = .ok _)
  have hplanned : ∀ {pr tr root mods path text},
      Planned (traceWith (answers w env) q) pr tr root mods path text → text = leanToolchain := by
    intro pr tr root mods path text hpl
    cases hpl with
    | toml h => exact hread h
    | toolchain => rfl
    | source _ _ hst =>
      obtain ⟨_, _, h⟩ := hst
      exact hread h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he hf
    obtain ⟨op, r⟩ := e
    have hrr := resp_eq he
    subst hrr
    cases op <;> first
      | exact hf.elim
      | exact hf rfl
      | (obtain ⟨e, he, hne⟩ := hf
         cases (he : Except.error _ = Except.error e)
         exact hne _ _ _ rfl
         done)
      | (rcases hf with ⟨e, he⟩ | ⟨l, he⟩
         · cases (he : (Except.ok (some (witnessRoot w), []) :
             Except String (Option (Root Unit) × List String)) = .error e)
         · cases (he : (Except.ok (some (witnessRoot w), []) :
             Except String (Option (Root Unit) × List String)) = .ok (none, l))
         done)
      | (simp [Event.failed, answers] at hf
         done)
  · intro pr _ rel text hr
    obtain rfl := hread hr
    refine ⟨fun _ => rfl, fun _ => rfl, fun s hs _ => ?_⟩
    obtain rfl := List.mem_singleton.mp hs
    rfl
  · intro pr hp rel real hrel hr
    obtain rfl := hreal hp
    obtain rfl := hreal hr
    rcases hrel with rfl | rfl | ⟨s, hs, rfl⟩
    · exact w.toolchainExact
    · exact w.tomlExact
    · obtain rfl := List.mem_singleton.mp hs
      have := w.fileExact
      rw [hw.rel] at this
      exact this
  · intro pr _ md hr
    cases resp_eq hr
  · intro text table hr
    have ht : table = Lake.Toml.Table.empty :=
      Except.ok.inj (resp_eq hr : (Except.ok _ : Except Lean.MessageLog Lake.Toml.Table) = .ok _)
    subst ht
    refine ⟨fun k hk => absurd hk keyPath_empty, fun n hn => ?_⟩
    cases n with
    | zero => exact Nat.le_refl _
    | succ n =>
      exfalso
      generalize ht : Lake.Toml.Table.empty = t at hn
      cases hn <;> (subst ht; simp [Lake.Toml.Table.empty, Lake.Toml.RBDict.empty] at *)
  · intro pr s pg ll app real lp hp _ hl ha hr hen
    obtain rfl := hreal hp
    have hla : (pg, ll) = (w.tree, w.lakeLib) := resp_eq hl
    cases hla
    have happ := Except.ok.inj (resp_eq ha : (Except.ok _ : Except IO.Error FilePath) = .ok _)
    subst happ
    obtain rfl := hreal hr
    have hlp : some lp = some w.leanPath := resp_eq hen
    cases hlp
    refine ⟨w.outside, ?_⟩
    have hd := w.dispatched
    cases hown : (w.app.parent.bind (·.parent)).map (· / "lib" / "lean") with
    | none =>
      rw [hown] at hd
      cases hd
    | some own =>
      rw [hown] at hd
      exact ⟨own, rfl, hd⟩
  · intro pr tr hp ht
    obtain rfl := hreal hp
    obtain rfl := hreal ht
    have ha := w.apart
    simp only [apart, Bool.and_eq_true, Bool.not_eq_true'] at ha
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [(List.isPrefixOf_iff_prefix).mpr h] at ha
      cases ha.1
    · rw [(List.isPrefixOf_iff_prefix).mpr h] at ha
      cases ha.2
  · intro tr ht
    obtain rfl := hreal ht
    exact ⟨w.tomlInTree, w.toolchainInTree, hw.toml, hw.chain⟩
  · intro tr s root log ht hl
    obtain rfl := hreal ht
    have he : (Except.ok (some root, log) : Except String (Option (Root Unit) × List String)) =
        .ok (some (witnessRoot w), []) := resp_eq hl
    have hr : root = witnessRoot w := by
      have := Except.ok.inj he
      simp only [Prod.mk.injEq, Option.some.injEq] at this
      exact this.1
    subst hr
    refine ⟨fun d hd => (by cases hd), fun x hx => (by cases hx), rfl, fun n hn => (by cases hn), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n hn l _
      obtain rfl : n = `Good := List.mem_singleton.mp hn
      refine ⟨⟨`Good, ".", [`Good], [.one `Good]⟩, by rfl, fun ms hev => ?_⟩
      have hms : ms = #[(`Good, w.file)] :=
        Except.ok.inj (resp_eq hev : (Except.ok _ : Except IO.Error (Array (Name × FilePath))) = .ok _)
      subst hms
      refine ⟨by rfl, fun x hx => ?_⟩
      obtain rfl : x = (`Good, w.file) := by simpa using hx
      rw [hw.file]
      congr 1
    · intro n _ hl
      cases hl
    · intro n _ m hm
      cases hm
    · intro n _ _
      rfl
    · intro m path hm
      cases hm
    · rintro m ⟨s, hs, i, hi, -⟩
      obtain rfl := List.mem_singleton.mp hs
      cases hi with | mk h => cases h
  · intro pr tr root mods m path d hs hf hd
    obtain ⟨-, rfl, rfl, rfl⟩ := scene_witness hs
    rcases hf with hf | hf
    · obtain ⟨-, rfl⟩ : m = `Good ∧ path = w.file := by simpa using hf
      refine Classical.byContradiction fun hno => w.fileInTree (.inr ⟨d, hd, fun rel hrel => hno ⟨rel, hrel⟩⟩)
    · cases hf
  · intro text name hh st ms imports he s hs _
    obtain rfl := List.mem_singleton.mp hs
    have h1 : (Except.ok (hh, st, ms, imports) : Except IO.Error (Lean.Syntax × Lean.Parser.ModuleParserState × Lean.MessageLog × Array Lean.Import)) =
        .ok (moduleHeader, default, {}, #[]) := resp_eq he
    have := Except.ok.inj h1
    simp only [Prod.mk.injEq] at this
    exact this.2.2.2
  · intro pr tr f path i md _ hra s hs _ _ _
    exact good_file hra
  · intro tr s root log m ol real _ _ hm
    cases hm
  · intro pr tr root mods path text r hs hpl hsub
    have hrr := resp_eq (hsub.subset (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    rw [hrr, hplanned hpl]
    rfl
  · intro tr md _ hm
    cases resp_eq hm

/-- **The premises of `domain_owed` are met.** For paths that meet `WitnessPaths` and `WitnessDomain` and an environment with the floor, the
program that runs receives what `DomainRun` states of the project of the witness, and exits with 0. -/
theorem domain_model (w : WitnessPaths) (env : Lean.Environment) (hm : EnvModel w env .standardLogical) (hw : WitnessDomain w) :
    ∃ rest, Runs (Regula.Shell.run ["standard-logical", "full", w.project.toString] : Prog Unit Unit UInt32)
      (⟨.leanVersion, Regula.Closed.pinnedLean⟩ :: rest) 0 ∧
      DomainRun witnessProject rest (FilePath.mk w.project.toString) .standardLogical := by
  have hr := runs_with (answers w env) (Regula.Shell.run ["standard-logical", "full", w.project.toString] :
    Prog Unit Unit UInt32)
  generalize hc : valueWith (answers w env) _ = c at hr
  have hshape : traceWith (answers w env) (Regula.Shell.run ["standard-logical", "full", w.project.toString] :
      Prog Unit Unit UInt32) = ⟨.leanVersion, Regula.Closed.pinnedLean⟩ ::
        traceWith (answers w env) (dispatch Regula.Closed.pinnedLean.1 Regula.Closed.pinnedLean.2
          (argsOf ["standard-logical", "full", w.project.toString]).1
          (argsOf ["standard-logical", "full", w.project.toString]).2) := rfl
  rw [hshape] at hr
  have hsp : Regula.Closed.Profile.ofSpelling? "standard-logical" = some .standardLogical := rfl
  generalize hq : (dispatch Regula.Closed.pinnedLean.1 Regula.Closed.pinnedLean.2
      (argsOf ["standard-logical", "full", w.project.toString]).1
      (argsOf ["standard-logical", "full", w.project.toString]).2 : Prog Unit Unit UInt32) = q at hr
  have howed : FullOwed (traceWith (answers w env) q) (FilePath.mk w.project.toString) .standardLogical := fullOwed_answers hm _
  have := (run_full_owed run_meets hsp hr howed).1
  subst this
  have hreadT : readPhase (traceWith (answers w env) q) <:+: traceWith (answers w env) q :=
    List.IsInfix.trans (List.takeWhile_prefix _).isInfix (List.drop_suffix _ _).isInfix
  have hdomain := witnessProject_in w.pinned
  have hanswered : ∀ e ∈ traceWith (answers w env) q, ¬ e.failed := (answers_witness hw q).answered
  have htree : ∀ {tree rest}, traceWith (answers w env) q = ⟨.createTempDir, .ok tree⟩ :: rest → tree = w.tree := by
    intro tree rest he
    have hmem : (⟨.createTempDir, .ok tree⟩ : Event Unit Unit) ∈ traceWith (answers w env) q := by simp [he]
    exact Except.ok.inj (resp_eq hmem : (Except.ok _ : Except IO.Error FilePath) = .ok _)
  refine ⟨_, hr, hdomain, hanswered, fun tree rest he => ?_, fun tree rest s root f roots he hs hg hb => howed.floor tree rest s root f roots he hs hg hb⟩
  obtain rfl := htree he
  exact Answers.of_infix hreadT (answers_witness hw q)

/-- **`Answers` does not imply the domain.** The answers of the witness also fit a project that states a `lakefile.lean`, since no response on them says
otherwise, and that project is outside the domain. So the premise of `domain_owed` that excludes it is the domain itself. -/
theorem answers_admit_outside {w : WitnessPaths} {env : Lean.Environment} (hw : WitnessDomain w) (q : Prog Unit Unit α) :
    Answers ({ witnessProject with leanConfig := true } : Project) (traceWith (answers w env) q) w.project w.tree ∧
      ¬ ({ witnessProject with leanConfig := true } : Project).InDomain := by
  have h := answers_witness (env := env) hw q
  exact ⟨⟨h.answered, h.read, h.real, fun _ _ _ _ => rfl, h.toml, h.start, h.apart, h.copies, h.lake, h.parents, h.header, h.parse, h.toolchain,
    h.writes, h.shadow⟩, fun hd => by cases hd.noLeanConfig⟩

/-- The answers of the witness, but for a Lake command, which ends with 1. -/
def answersBuildFails (w : WitnessPaths) (env : Lean.Environment) : (o : Op Unit Unit) → Resp o
  | .runLake .. => .ok 1
  | o => answers w env o

/-- Two sets of answers that agree but for Lake's commands give one trace up to the first such command. -/
theorem takeWhile_traceWith {f g : (o : Op Unit Unit) → Resp o} (P : Event Unit Unit → Bool) (hP : ∀ e : Event Unit Unit, e.isBuild = true → P e = false)
    (hfg : ∀ o, (∀ a b c, o ≠ .runLake a b c) → f o = g o) (q : Prog Unit Unit α) :
    (traceWith f q).takeWhile P = (traceWith g q).takeWhile P := by
  induction q with
  | done a => rfl
  | ask o next ih =>
    by_cases ho : ∃ a b c, o = .runLake a b c
    · obtain ⟨a, b, c, rfl⟩ := ho
      simp only [traceWith, List.takeWhile_cons, hP ⟨.runLake a b c, f _⟩ rfl, hP ⟨.runLake a b c, g _⟩ rfl]
      simp
    · simp only [traceWith]
      rw [hfg o fun a b c h => ho ⟨a, b, c, h⟩]
      simp only [List.takeWhile_cons]
      split
      · rw [ih]
      · rfl

/-- **`Answers` and the domain do not settle the verdict.** On the reading of the witness, in the domain and with its reads answering as its files
state, a build that ends with 1 gives no exit 0. So the premise that the Lake commands succeed does work in `domain_owed`. -/
theorem build_fails_model (w : WitnessPaths) (env : Lean.Environment) (hw : WitnessDomain w) :
    ∃ rest c, Runs (Regula.Shell.run ["standard-logical", "full", w.project.toString] : Prog Unit Unit UInt32)
      (⟨.leanVersion, Regula.Closed.pinnedLean⟩ :: rest) c ∧ witnessProject.InDomain ∧
      (∀ tree tail, rest = ⟨.createTempDir, .ok tree⟩ :: tail → Answers witnessProject (readPhase rest) (FilePath.mk w.project.toString) tree) ∧
      c ≠ 0 := by
  have hr := runs_with (answersBuildFails w env) (Regula.Shell.run ["standard-logical", "full", w.project.toString] :
    Prog Unit Unit UInt32)
  generalize hc : valueWith (answersBuildFails w env) _ = c at hr
  have hshape : traceWith (answersBuildFails w env) (Regula.Shell.run ["standard-logical", "full", w.project.toString] :
      Prog Unit Unit UInt32) = ⟨.leanVersion, Regula.Closed.pinnedLean⟩ ::
        traceWith (answersBuildFails w env) (dispatch Regula.Closed.pinnedLean.1 Regula.Closed.pinnedLean.2
          (argsOf ["standard-logical", "full", w.project.toString]).1
          (argsOf ["standard-logical", "full", w.project.toString]).2) := rfl
  rw [hshape] at hr
  generalize hq : (dispatch Regula.Closed.pinnedLean.1 Regula.Closed.pinnedLean.2
      (argsOf ["standard-logical", "full", w.project.toString]).1
      (argsOf ["standard-logical", "full", w.project.toString]).2 : Prog Unit Unit UInt32) = q at hr
  have hf : ∀ o, (∀ a b c, o ≠ .runLake a b c) → answersBuildFails w env o = answers w env o := by
    intro o ho
    cases o with
    | runLake a b c => exact absurd rfl (ho a b c)
    | _ => rfl
  refine ⟨_, c, hr, witnessProject_in w.pinned, fun tree tail he => ?_, ?_⟩
  · cases q with
    | done a => cases he
    | ask o next =>
      have hhead : o = .createTempDir := by
        simp only [traceWith, List.cons.injEq] at he
        exact congrArg Event.op he.1
      subst hhead
      have hsame : answersBuildFails w env .createTempDir = answers w env .createTempDir := rfl
      have htree : tree = w.tree := by
        simp only [traceWith, List.cons.injEq] at he
        have h3 := he.1
        injection h3 with _ h4
        exact (Except.ok.inj (h4 : (Except.ok w.tree : Except IO.Error FilePath) = .ok tree)).symm
      subst htree
      have hphase : readPhase (traceWith (answersBuildFails w env) (.ask .createTempDir next)) =
          readPhase (traceWith (answers w env) (.ask .createTempDir next)) := by
        simp only [readPhase, traceWith, List.drop_succ_cons, List.drop_zero, hsame]
        exact takeWhile_traceWith _ (fun e he => by simp [he]) hf _
      rw [hphase]
      exact Answers.of_infix (List.IsInfix.trans (List.takeWhile_prefix _).isInfix (List.drop_suffix _ _).isInfix) (answers_witness hw _)
  · rintro rfl
    have hm := run_meets _ _ _ hr
    have hsp : Regula.Closed.Profile.ofSpelling? "standard-logical" = some .standardLogical := rfl
    simp only [hsp] at hm
    obtain ⟨v, rest', he, hrun, -⟩ := hm
    cases he
    obtain ⟨rest'', v', he', hfull⟩ := hrun rfl
    cases he'
    rcases hfull with ⟨e, tl, -, hcode, -⟩ | ⟨tree, tRead, tGate, r, last, ht, -, -, o, report, -, -, hn, ha, hcode, -⟩
    · cases hcode
    · have hrep : report = .full .pass := (Report.exitCode_eq_zero_iff report).mp hcode.symm
      subst hrep
      by_cases ho : o = .admitted
      · subst ho
        obtain ⟨sysroot, tBuild, tRules, -, rfl, hb⟩ := ha rfl
        rcases hb.2.2.1 with ⟨program, lakeLib, result, -, hsub, -⟩ | ⟨hx, -⟩
        · have hmem : (⟨.runLake program tree ["build", "--wfail"], .ok 0⟩ : Event Unit Unit) ∈ tBuild :=
            hsub.subset (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          have hin : (⟨.runLake program tree ["build", "--wfail"], .ok 0⟩ : Event Unit Unit) ∈
              traceWith (answersBuildFails w env) q := by
            rw [ht]
            simp [hmem]
          have h0 : (Except.ok 0 : Except IO.Error UInt32) = .ok 1 := resp_eq hin
          exact absurd (Except.ok.inj h0) (by decide)
        · cases hx
      · obtain ⟨-, hrep⟩ := hn ho
        cases o <;> first | exact absurd rfl ho | cases hrep

/-- **The audit's project at the level of the program.** Two entries of one name whose paths have the same components leave nothing unread,
when the targets' names are closed and each spelling lies below the tree. -/
theorem twoSpellings_read {L : Type} {tree : FilePath} {root : Root L} {m : Name} {a b : FilePath} (hparts : parts a = parts b)
    (hres : root.resolve m = some a) (hnames : ∀ n ∈ root.targets, closedModuleName n = true)
    (hplaced : ∀ path, path = a ∨ path = b → inTree tree path = true ∧ parentInTree tree path = true) :
    configUnread tree root [(m, a), (m, b)] = [] := by
  have ha := hplaced a (.inl rfl)
  have hb := hplaced b (.inr rfl)
  simp only [parts] at hparts
  have hn : root.targets.filter (!closedModuleName ·) = [] := by
    simp only [List.filter_eq_nil_iff, Bool.not_eq_true']
    intro n hx
    simp [hnames n hx]
  simp [configUnread, hres, hn, hparts, ha.1, ha.2, hb.1, hb.2]

end RegulaSpecification.Effects
