/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Witness
import Regula.Table

/-!
# The program against its record, and what the executable runs

The checker's program meets `programRecord` (`run_meets_record`); the record has lean-intent's obligations; `refuser`, which
reads nothing and refuses, does not meet it; and what `Prog.interpret` computes is the value of such a run, for any table
of effects (`executed_meets`). Each row of the one table is a straight line of calls (`table_rows`), so the table makes no
decision.
-/

namespace RegulaSpecification.Effects

open Lean (Name Environment)
open System (FilePath)
open LeanIntent
open Regula.Effect
open Regula.Language
open RegulaSpecification.Language

variable {L E : Type}

/-! ## The record -/

theorem program_meets_iff (w : List String → Prog L E UInt32) :
    (programRecord L E).Meets w ↔ RunMeets w := by
  simp [IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props, programRecord]

/-- The program that the `lint` executable interprets meets the record, for every response. -/
theorem run_meets_record : (programRecord L E).Meets (Regula.Shell.run : List String → Prog L E UInt32) :=
  (program_meets_iff _).mpr run_meets

/-- O2 before running: the implementation is a model of the record. -/
theorem program_o2Run : O2Run (programRecord L E) := o2Run_of_meets run_meets_record

/-- O2 at confirmation: the record has no domain hypothesis, and each predicate has an instance. -/
theorem program_o2 : O2 (programRecord L E) := by
  rw [o2_correct]
  refine ⟨⟨Regula.Shell.run, by simp [programRecord]⟩, ?_⟩
  intro p hp
  simp only [programRecord, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨"  ", "", by simp⟩
  · exact ⟨goodReading, goodReading_inside⟩

/-- A run that says nothing and ends with 0, whatever it is asked, does not meet the record: a program that does nothing and ends with other than 2
is ruled out. -/
theorem constant_program_fails (c : UInt32) (hc : c ≠ 2) :
    ¬ RunMeets (fun _ => .done c : List String → Prog L E UInt32) := by
  intro h
  exact hc (h [] [] c (.done c)).1

/-- O3: the one property can fail. -/
theorem program_o3 : O3 (programRecord L E) := by
  rw [o3_correct]
  intro p hp
  simp only [programRecord, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  exact ⟨fun _ => .done 0, constant_program_fails 0 (by decide)⟩

/-- O4: the subject gives a program for each argument list. -/
theorem program_o4 : O4 (programRecord L E) := o4_function _ rfl

/-- O5 at `.widest`, which every record meets, so it adds no agreement between programs. The record leaves the order of independent
reads, and the wording of each line before the last, to the program, and two programs ask different events, so no relation
between their traces is fixed. -/
theorem program_o5 : O5 (programRecord L E) .widest := o5_widest _

/-! ## A reader that refuses everything -/

theorem reason_nil {dir tree : FilePath} {o : Outcome} : ¬ Reason ([] : List (Event L E)) dir tree o := by
  intro h
  have hs {a b c d : FilePath} {r : Root L} {q : List (Name × FilePath)} :
      ¬ Scene ([] : List (Event L E)) a b c d r q := fun x => by simpa using x.project_real
  have ht {a b c : FilePath} {r : Root L} : ¬ TreeLoaded ([] : List (Event L E)) a b c r := fun x => by simpa using x.1
  have hl {a b c s response} : ¬ PreparedLoad ([] : List (Event L E)) a b s c response := by
    intro hp
    have := hp.event
    cases this
  have hm {a : FilePath} {x : Lake.Toml.Table} : ¬ TomlRead ([] : List (Event L E)) a x := by
    rintro ⟨_, _, h, -⟩
    simp at h
  cases h <;> first | exact hs (by assumption) | exact ht (by assumption) | exact hm (by assumption) |
    exact hl (by assumption) | simp_all

/-- A program that says it refused, and read nothing. -/
def refuser (_ : List String) : Prog L E UInt32 :=
  .ask .leanVersion fun _ =>
    .ask .createTempDir fun r =>
      match r with
      | .error _ => .done 1
      | .ok tree =>
        .ask (.removeDirAll tree) fun _ =>
          .ask (.println Report.refused.label) fun _ => .done 1

/-- A reader that reads nothing and refuses everything does not meet the record: no `Reason` holds of what it read. -/
theorem refuser_fails (tree : FilePath) :
    ¬ RunMeets (refuser : List String → Prog L E UInt32) := by
  intro h
  have hr : Runs (refuser ["standard-logical", "full", "d"] : Prog L E UInt32)
      [⟨.leanVersion, Regula.Closed.pinnedLean⟩, ⟨.createTempDir, .ok tree⟩, ⟨.removeDirAll tree, .ok ()⟩,
        ⟨.println Report.refused.label, .ok ()⟩] 1 :=
    .ask _ _ _ (.ask _ _ _ (.ask _ _ _ (.ask _ _ _ (.done _))))
  have hm := h _ _ _ hr
  have hsp : Regula.Closed.Profile.ofSpelling? "standard-logical" = some .standardLogical := rfl
  simp only [hsp] at hm
  obtain ⟨v, rest, he, hp, -⟩ := hm
  cases he
  obtain ⟨rest', v', he', hfull⟩ := hp rfl
  cases he'
  rcases hfull with ⟨e, rest, hlist, -⟩ | ⟨tree', tRead, tGate, r, last, hlist, -, -, o, report, hdec, -⟩
  · cases hlist
  · have hnil : tRead = [] := by
      cases tRead with
      | nil => rfl
      | cons a as =>
        exfalso
        simp only [List.cons_append, List.append_assoc] at hlist
        injection hlist with _ h2
        injection h2 with _ h3
        have hl := congrArg List.length h3
        simp only [List.length_cons, List.length_nil, List.length_append] at hl
        have h0 : as = [] := List.eq_nil_of_length_eq_zero (by omega)
        have h1 : tGate = [] := List.eq_nil_of_length_eq_zero (by omega)
        have h2' : last = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst h0 h1 h2'
        simp only [List.nil_append] at h3
        injection h3 with h4
        cases h4
    subst hnil
    cases o with
    | admitted =>
      obtain ⟨r', -, hev⟩ := hdec.1 rfl
      obtain ⟨project, _, hp', -⟩ := hev.1.places
      cases hp'
    | refused => exact reason_nil (hdec.2.1 (by simp))
    | proofOnly => exact reason_nil (hdec.2.1 (by simp))
    | incomplete => exact reason_nil (hdec.2.1 (by simp))

/-! ## What the executable runs -/

/-- What `Prog.interpret` computes is the value of a run of the program, from any state of the world and for any
table: so all that `run_meets` states holds of it. That `Regula.LintMain.main` is that interpretation is read from the code,
and that the compiled program does what its definition says stays with
Lean's compiler, which the trusted base lists. -/
theorem executed_meets (table : (o : Op L E) → BaseIO (Resp o)) (args : List String) (w : Void IO.RealWorld) :
    Runs (Regula.Shell.run args : Prog L E UInt32)
      (traceFrom table (Regula.Shell.run args) w)
      (Prog.interpret table (Regula.Shell.run args) w).val :=
  interpret_runs table _ w

/-! ## The one table -/

/-- What each operation calls. Each row is a straight line of calls of Lean, of the operating system's function as Lean gives
it, or of a row of `LakeCalls`, with `spawnLake` and `importParsers`, which `spawnLake_eq` and `importParsers_eq` state. No
row holds a test or a branch on a result. This is the closed form of "so thin that it only calls Lean" for this table. -/
inductive Row (enable : BaseIO Unit) (lake : LakeCalls L) : (o : Op L Environment) → BaseIO (Resp o) → Prop where
  /-- Lean's own constants. -/
  | leanVersion : Row enable lake .leanVersion (pure (Lean.versionString, Lean.githash))
  /-- `IO.getEnv`. -/
  | getEnv {name} : Row enable lake (.getEnv name) (IO.getEnv name)
  /-- `IO.appPath`. -/
  | appPath : Row enable lake .appPath IO.appPath.toBaseIO
  /-- `IO.FS.realPath`. -/
  | realPath {p} : Row enable lake (.realPath p) (IO.FS.realPath p).toBaseIO
  /-- `IO.FS.readFile`. -/
  | readFile {p} : Row enable lake (.readFile p) (IO.FS.readFile p).toBaseIO
  /-- `System.FilePath.symlinkMetadata`. -/
  | symlinkMetadata {p} : Row enable lake (.symlinkMetadata p) p.symlinkMetadata.toBaseIO
  /-- `IO.FS.writeFile`. -/
  | writeFile {p text} : Row enable lake (.writeFile p text) (IO.FS.writeFile p text).toBaseIO
  /-- `IO.FS.createDirAll`. -/
  | createDirAll {p} : Row enable lake (.createDirAll p) (IO.FS.createDirAll p).toBaseIO
  /-- `IO.FS.createTempDir`. -/
  | createTempDir : Row enable lake .createTempDir IO.FS.createTempDir.toBaseIO
  /-- `IO.FS.removeDirAll`. -/
  | removeDirAll {p} : Row enable lake (.removeDirAll p) (IO.FS.removeDirAll p).toBaseIO
  /-- `IO.println`. -/
  | println {text} : Row enable lake (.println text) (IO.println text).toBaseIO
  /-- The flush of standard output. -/
  | flush : Row enable lake .flush (do (← IO.getStdout).flush : IO Unit).toBaseIO
  /-- `Lean.Parser.parseHeader`, and what its header imports. -/
  | parseHeader {input} : Row enable lake (.parseHeader input)
      (do
        let (header, state, messages) ← Lean.Parser.parseHeader input
        return (header.raw, state, messages, Lean.Elab.HeaderSyntax.imports header) :
        IO (Lean.Syntax × Lean.Parser.ModuleParserState × Lean.MessageLog × Array Lean.Import)).toBaseIO
  /-- `Lean.Parser.parseCommand`. -/
  | parseCommand {input env state messages} : Row enable lake (.parseCommand input env state messages)
      (pure (Lean.Parser.parseCommand input { env, options := {} } state messages))
  /-- The set of `Lean.searchPathRef`. -/
  | setSearchPath {p} : Row enable lake (.setSearchPath p) (Lean.searchPathRef.set p)
  /-- `Lean.findOLean`. -/
  | findOLean {m} : Row enable lake (.findOLean m) (Lean.findOLean m).toBaseIO
  /-- `Lean.importModules`, for the rules. -/
  | importForRules {ms} : Row enable lake (.importForRules ms)
      (Lean.importModules (ms.map ({ module := · })) {} (loadExts := false) (level := .private)).toBaseIO
  /-- `Lean.importModules`, for the parser. -/
  | importForParser {ms} : Row enable lake (.importForParser ms) (importParsers enable ms).toBaseIO
  /-- Lake's row. -/
  | parseToml {input} : Row enable lake (.parseToml input) (lake.parseToml input)
  /-- Lake's row. -/
  | lakeInstall {s} : Row enable lake (.lakeInstall s) (lake.lakeInstall s)
  /-- Lake's row. -/
  | loadWorkspace {s d} : Row enable lake (.loadWorkspace s d) (lake.loadWorkspace s d)
  /-- Lake's row. -/
  | loadRoot {s d} : Row enable lake (.loadRoot s d) (lake.loadRoot s d)
  /-- Lake's row. -/
  | libModules {l} : Row enable lake (.libModules l) (lake.libModules l)
  /-- `spawnLake`. -/
  | runLake {program cwd args} : Row enable lake (.runLake program cwd args)
      (spawnLake program cwd args).toBaseIO

/-- Each operation is answered by its row, over the closed type of the operations. -/
theorem table_rows (enable : BaseIO Unit) (lake : LakeCalls L) (o : Op L Environment) :
    Row enable lake o (table enable lake o) := by
  cases o <;> constructor

/-- `spawnLake` starts the command and waits for it: two calls, with no test. -/
theorem spawnLake_eq (program cwd : FilePath) (args : List String) :
    spawnLake program cwd args = (do
      let child ← IO.Process.spawn
        { cmd := program.toString, args := args.toArray, cwd := some cwd, stdin := .null,
          env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none), ("LAKE_ARTIFACT_CACHE", some "false")] }
      child.wait) := rfl

/-- `importParsers` enables Lean's initializers and imports: two calls, with no test, and it reads the scoped parsers of
what it imported. -/
theorem importParsers_eq (enable : BaseIO Unit) (modules : List Name) :
    importParsers enable modules = (do
      enable
      let env ← Lean.importModules (modules.toArray.map ({ module := · })) {} (loadExts := true)
        (level := .exported)
      return (env, scopedParsersOf env)) := rfl

end RegulaSpecification.Effects
