module

public import RegulaSpecification.Proofs.Witness
public import Regula.Table
import all Regula.Input
import all Regula.Table

@[expose] public section

namespace RegulaSpecification.Effects

open Lean (Name Environment)
open System (FilePath)
open LeanIntent
open Regula.Effect
open Regula.Language
open RegulaSpecification.Language

variable {L E : Type}

theorem program_meets_iff (w : List String → Prog L E UInt32) :
    (programRecord L E).Meets w ↔ RunMeets w := by
  simp [IntentRecord.Meets, IntentRecord.Dom, IntentRecord.Props, programRecord]

theorem run_meets_record : (programRecord L E).Meets (Regula.Shell.run : List String → Prog L E UInt32) :=
  (program_meets_iff _).mpr run_meets

theorem program_o2Run : O2Run (programRecord L E) := o2Run_of_meets run_meets_record

theorem program_o2 : O2 (programRecord L E) := by
  rw [o2_correct]
  refine ⟨⟨Regula.Shell.run, by simp [programRecord]⟩, ?_⟩
  intro p hp
  simp only [programRecord, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨"  ", "", by simp⟩
  · exact ⟨goodReading, goodReading_inside⟩

theorem constant_program_fails (c : UInt32) (hc : c ≠ 2) :
    ¬ RunMeets (fun _ => .done c : List String → Prog L E UInt32) := by
  intro h
  exact hc (h [] [] c (.done c)).1

theorem program_o3 : O3 (programRecord L E) := by
  rw [o3_correct]
  intro p hp
  simp only [programRecord, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  exact ⟨fun _ => .done 0, constant_program_fails 0 (by decide)⟩

theorem program_o4 : O4 (programRecord L E) := o4_function _ rfl

theorem program_o5 : O5 (programRecord L E) .widest := o5_widest _

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

def refuser (_ : List String) : Prog L E UInt32 :=
  .ask .leanVersion fun _ =>
    .ask (.getEnv Regula.Shell.fullVariable) fun _ =>
      .ask (.getEnv Regula.Shell.proofVariable) fun _ =>
        .ask .createTempDir fun r =>
          match r with
          | .error _ => .done 1
          | .ok tree =>
            .ask (.removeDirAll tree) fun _ =>
              .ask (.println Report.refused.label) fun _ => .done 1

theorem refuser_fails (tree : FilePath) :
    ¬ RunMeets (refuser : List String → Prog L E UInt32) := by
  intro h
  have hr : Runs (refuser ["standard-logical"] : Prog L E UInt32)
      [⟨.leanVersion, Regula.Closed.pinnedLean⟩, ⟨.getEnv Regula.Shell.fullVariable, some "d"⟩,
        ⟨.getEnv Regula.Shell.proofVariable, none⟩, ⟨.createTempDir, .ok tree⟩,
        ⟨.removeDirAll tree, .ok ()⟩, ⟨.println Report.refused.label, .ok ()⟩] 1 :=
    .ask _ _ _ (.ask _ _ _ (.ask _ _ _ (.ask _ _ _ (.ask _ _ _ (.ask _ _ _ (.done _))))))
  have hm := h _ _ _ hr
  have hsp : Regula.Closed.Profile.ofSpelling? "standard-logical" = some .standardLogical := rfl
  simp only [hsp] at hm
  obtain ⟨v, rest, he, hp, -⟩ := hm
  cases he
  obtain ⟨v', rf, rp, rest', he', hfull⟩ := hp rfl
  cases he'
  simp only at hfull
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
      obtain ⟨r', -, -, hev, -⟩ := hdec.1 rfl
      obtain ⟨project, _, hp', -⟩ := hev.places
      cases hp'
    | refused => exact reason_nil (hdec.2.1 (by simp))
    | proofOnly => exact reason_nil (hdec.2.1 (by simp))
    | incomplete => exact reason_nil (hdec.2.1 (by simp))

theorem executed_meets (table : (o : Op L E) → BaseIO (Resp o)) (args : List String) (w : Void IO.RealWorld) :
    Runs (Regula.Shell.run args : Prog L E UInt32)
      (traceFrom table (Regula.Shell.run args) w)
      (Prog.interpret table (Regula.Shell.run args) w).val :=
  interpret_runs table _ w

inductive Row (enable : BaseIO Unit) (lake : LakeCalls L) : (o : Op L Environment) → BaseIO (Resp o) → Prop where
  | leanVersion : Row enable lake .leanVersion (pure (Lean.versionString, Lean.githash))
  | getEnv {name} : Row enable lake (.getEnv name) (IO.getEnv name)
  | realPath {p} : Row enable lake (.realPath p) (IO.FS.realPath p).toBaseIO
  | readFile {p} : Row enable lake (.readFile p) (IO.FS.readFile p).toBaseIO
  | symlinkMetadata {p} : Row enable lake (.symlinkMetadata p) p.symlinkMetadata.toBaseIO
  | writeFile {p text} : Row enable lake (.writeFile p text) (IO.FS.writeFile p text).toBaseIO
  | createDirAll {p} : Row enable lake (.createDirAll p) (IO.FS.createDirAll p).toBaseIO
  | createTempDir : Row enable lake .createTempDir IO.FS.createTempDir.toBaseIO
  | removeDirAll {p} : Row enable lake (.removeDirAll p) (IO.FS.removeDirAll p).toBaseIO
  | println {text} : Row enable lake (.println text) (IO.println text).toBaseIO
  | flush : Row enable lake .flush (do (← IO.getStdout).flush : IO Unit).toBaseIO
  | parseHeader {input} : Row enable lake (.parseHeader input)
      (do
        let (header, state, messages) ← Lean.Parser.parseHeader input
        return (header.raw, state, messages, Lean.Elab.HeaderSyntax.imports header) :
        IO (Lean.Syntax × Lean.Parser.ModuleParserState × Lean.MessageLog × Array Lean.Import)).toBaseIO
  | parseCommand {input env state messages} : Row enable lake (.parseCommand input env state messages)
      (pure (Lean.Parser.parseCommand input { env, options := {} } state messages))
  | findOLean {p m} : Row enable lake (.findOLean p m)
      (do Lean.searchPathRef.set p; Lean.findOLean m : IO FilePath).toBaseIO
  | importForRules {p ms} : Row enable lake (.importForRules p ms)
      (do
        Lean.searchPathRef.set p
        Lean.importModules (ms.map ({ module := · })) {} (loadExts := false) (level := .private) : IO Environment).toBaseIO
  | importForParser {p ms} : Row enable lake (.importForParser p ms)
      (do Lean.searchPathRef.set p; importParsers enable ms : IO (Environment × List Name)).toBaseIO
  | kernelReplay {constants} : Row enable lake (.kernelReplay constants)
      (do let _ ← (← Lean.mkEmptyEnvironment).toKernelEnv.replay constants : IO Unit).toBaseIO
  | parseToml {input} : Row enable lake (.parseToml input) (lake.parseToml input)
  | lakeInstall {s} : Row enable lake (.lakeInstall s) (lake.lakeInstall s)
  | loadWorkspace {s d} : Row enable lake (.loadWorkspace s d) (lake.loadWorkspace s d)
  | loadRoot {s d} : Row enable lake (.loadRoot s d) (lake.loadRoot s d)
  | libModules {l} : Row enable lake (.libModules l) (lake.libModules l)
  | runLake {program cwd args} : Row enable lake (.runLake program cwd args)
      (spawnLake program cwd args).toBaseIO

theorem table_rows (enable : BaseIO Unit) (lake : LakeCalls L) (o : Op L Environment) :
    Row enable lake o (table enable lake o) := by
  cases o <;> constructor

theorem spawnLake_eq (program cwd : FilePath) (args : List String) :
    spawnLake program cwd args = (do
      let child ← IO.Process.spawn
        { cmd := "/usr/bin/env", args := #["-i", "PATH=/usr/bin:/bin", "LAKE_ARTIFACT_CACHE=false", program.toString] ++ args.toArray,
          cwd := some cwd, stdin := .null }
      child.wait) := by rfl

theorem importParsers_eq (enable : BaseIO Unit) (modules : List Name) :
    importParsers enable modules = (do
      enable
      let env ← Lean.importModules (modules.toArray.map ({ module := · })) {} (loadExts := true)
        (level := .exported)
      return (env, (Lean.Parser.parserExtension.ext.getState env).scopedEntries.map.toList.map (·.1))) := by rfl

end RegulaSpecification.Effects
