module

public import RegulaSpecification.Assumptions

@[expose] public section

namespace RegulaSpecification.Meaning

open Lean (Name ConstantInfo Import)
open System (FilePath)
open Regula.Effect
open Regula.Language
open RegulaSpecification.Effects
open RegulaSpecification.Language
open RegulaSpecification.Loader
open RegulaSpecification.Assumptions

def _root_.RegulaSpecification.Assumptions.Route.Runs {L E : Type} : Route → List (Event L E) → UInt32 → Prop
  | .proof, t, c => ∃ p v rest,
      t = ⟨.leanVersion, v⟩ :: ⟨.getEnv Regula.Shell.fullVariable, none⟩ ::
        ⟨.getEnv Regula.Shell.proofVariable, none⟩ :: rest ∧
      PlainRun (⟨.leanVersion, v⟩ :: rest) p c
  | .outOfTreeProof, t, c => ∃ p v rest, ∃ dir : String,
      t = ⟨.leanVersion, v⟩ :: ⟨.getEnv Regula.Shell.fullVariable, none⟩ ::
        ⟨.getEnv Regula.Shell.proofVariable, some dir⟩ :: rest ∧
      OutProofRun rest (FilePath.mk dir) p c
  | .full, t, c => ∃ p v rest, ∃ dir : String,
      t = ⟨.leanVersion, v⟩ :: ⟨.getEnv Regula.Shell.fullVariable, some dir⟩ ::
        ⟨.getEnv Regula.Shell.proofVariable, none⟩ :: rest ∧
      FullRun rest (FilePath.mk dir) p c

theorem run_route {L E : Type} {args : List String} {t : List (Event L E)} {c : UInt32}
    (h : Runs (Regula.Shell.run args : Prog L E UInt32) t c) :
    Refusal t c ∨ ConflictingRefusal t c ∨ ∃ r : Route, r.Runs t c := by
  rcases run_subject h with hr | hc | ⟨p, v, rest, ⟨ht, hp⟩ | ⟨dir, ht, ho⟩ | ⟨dir, ht, hf⟩⟩
  · exact .inl hr
  · exact .inr (.inl hc)
  · exact .inr (.inr ⟨.proof, p, v, rest, ht, hp⟩)
  · exact .inr (.inr ⟨.outOfTreeProof, p, v, rest, dir, ht, ho⟩)
  · exact .inr (.inr ⟨.full, p, v, rest, dir, ht, hf⟩)

structure Meaning : Prop where
  record : ∀ {L E : Type}, RunMeets (Regula.Shell.run : List String → Prog L E UInt32)
  executed : ∀ {L E : Type} (table : (o : Op L E) → BaseIO (Resp o)) (args : List String) (w : Void IO.RealWorld),
    Runs (Regula.Shell.run args : Prog L E UInt32) (traceFrom table (Regula.Shell.run args) w)
      (Prog.interpret table (Regula.Shell.run args) w).val
  routes : ∀ {L E : Type} {args : List String} {t : List (Event L E)} {c : UInt32},
    Runs (Regula.Shell.run args : Prog L E UInt32) t c →
    Refusal t c ∨ ConflictingRefusal t c ∨ ∃ r : Route, r.Runs t c
  plainPass : ∀ {L E : Type} {t : List (Event L E)} {p : Regula.Closed.Profile}, PlainRun t p 0 →
    ∃ subject : FilePath, EndsWith t (Regula.Closed.Verdict.pass.proofLineOn subject.toString) ∧
      (⟨.realPath ".", .ok subject⟩ : Event L E) ∈ t ∧
      ∃ sysroot root log, (⟨.loadWorkspace sysroot subject, .ok (some root, log)⟩ : Event L E) ∈ t ∧ PlainRoot t root
  plainExit : ∀ {L E : Type} {t : List (Event L E)} {p : Regula.Closed.Profile}, PlainRun t p 0 →
    ∃ (root : Root L) (f : Regula.Load.Facts) (roots : List Name), PlainRoot t root ∧ BuildRead t root f roots ∧
      EnvForm f ∧ EnvFloor f p ∧ (∀ r ∈ roots, r ∈ f.claimed) ∧
      ∃ i, f.input roots p = .ok i ∧ (⟨.kernelReplay (f.replayConstants i), .ok ()⟩ : Event L E) ∈ t
  outProofPass : ∀ {L E : Type} {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile},
    OutProofRun t dir p 0 →
    ∃ subject : FilePath, EndsWith t (Regula.Closed.Verdict.pass.proofLineOn subject.toString) ∧
      (⟨.realPath dir, .ok subject⟩ : Event L E) ∈ t ∧
      ∃ sysroot root log err name code details,
        SysrootIs t sysroot ∧
        (⟨.symlinkMetadata (subject / "lakefile.lean"), .error err⟩ : Event L E) ∈ t ∧
        err = .noFileOrDirectory name code details ∧
        (⟨.loadRoot sysroot subject, .ok (some root, log)⟩ : Event L E) ∈ t ∧ OutProofRoot dir t root
  outProofExit : ∀ {L E : Type} {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile},
    OutProofRun t dir p 0 →
    ∃ (root : Root L) (f : Regula.Load.Facts) (roots : List Name), OutProofRoot dir t root ∧ BuildRead t root f roots ∧
      EnvForm f ∧ EnvFloor f p ∧ (∀ r ∈ roots, r ∈ f.claimed) ∧
      ∃ i, f.input roots p = .ok i ∧ (⟨.kernelReplay (f.replayConstants i), .ok ()⟩ : Event L E) ∈ t
  fullExit : ∀ {L E : Type} {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile}, FullRun t dir p 0 →
    ∃ (tree : FilePath) (sysroot : String) (tRead tBuild tRules : List (Event L E)) (r : Reading), Inside r ∧
      Evidence tRead dir tree (written tRead) r ∧ (∀ e ∈ tRead, ¬ e.failed) ∧
      (∃ program lakeLib,
        ([⟨.lakeInstall sysroot, (program, lakeLib)⟩, ⟨.runLake program tree ["build", "--wfail"], .ok 0⟩] :
          List (Event L E)).Sublist tBuild) ∧
      ∃ (root : Root L) (f : Regula.Load.Facts) (roots : List Name),
        TreeRoot sysroot tree tRules root ∧ BuildRead tRules root f roots ∧ EnvForm f ∧ EnvFloor f p ∧
        ∃ i, f.input roots p = .ok i ∧ (⟨.kernelReplay (f.replayConstants i), .ok ()⟩ : Event L E) ∈ tRules
  cone : ∀ {f : Regula.Load.Facts} {roots : List Name} {p : Regula.Closed.Profile} {i : Regula.Closed.Input},
    f.input roots p = .ok i → ∀ (n : Name) (info : ConstantInfo),
      (f.replayConstants i)[n]? = some info ↔
        (f.env.constants.map₁[n]? = some info ∧ InCone f n ∧ ∀ v, info = .quotInfo v → v.kind = .type) ∨
          (n, info) ∈ copyEntries f
  claimedReplayed : ∀ {f : Regula.Load.Facts} {roots : List Name} {p : Regula.Closed.Profile} {i : Regula.Closed.Input},
    f.input roots p = .ok i → ∀ {m n : Name} {v : Lean.TheoremVal}, (m, n, .thmInfo v) ∈ f.claimedConstants →
      (f.env.constants.map₁[n]? == some (.thmInfo v)) = true ∨
        ∃ k, (f.replayConstants i)[(Regula.Load.copyAt (Regula.Load.copyRoot f.env.constants.map₁) (v, k)).1]? =
          some (Regula.Load.copyAt (Regula.Load.copyRoot f.env.constants.map₁) (v, k)).2
  loaderPass : ∀ {f : Regula.Load.Facts} {roots : List Name} {p : Regula.Closed.Profile} {i : Regula.Closed.Input},
    f.input roots p = .ok i → (i.report.verdict = .pass ↔ EnvForm f ∧ EnvFloor f p)
  loaderFloor : ∀ {f : Regula.Load.Facts} {roots : List Name} {p : Regula.Closed.Profile},
    (Regula.Closed.decision (f.input roots p)).verdict = .pass →
      (∀ r ∈ roots, r ∈ f.claimed) ∧ (∀ m ∈ f.claimed, m ∈ f.env.header.moduleNames.toList) ∧
      (∀ n info, f.env.constants.map₁[n]? = some info → ∃ m, f.moduleOf? n = some m) ∧ EnvForm f ∧ EnvFloor f p
  loaderHeld : ∀ {f : Regula.Load.Facts} {roots : List Name} {p : Regula.Closed.Profile},
    (Regula.Closed.decision (f.input roots p)).verdict = .pass → ∀ {m n : Name} {info : ConstantInfo},
      (m, n, info) ∈ f.claimedConstants →
      (ModuleUnreplaced f.env m n ∨ ModuleCtorIdxEntryOnly f.env m n info) ∧
      ((∃ v, info = .defnInfo v) → ModuleUninitialized f.env m n) ∧
      (∀ v, info ≠ .axiomInfo v) ∧
      ((info.isUnsafe = true ∨ info.isPartial = true ∨ ∃ b, n = .str b "_unsafe_rec") →
        (info.isPartial = true ∧ info.isUnsafe = false) ∨
          (info.isUnsafe = true ∧ ∃ ind, ctorIdxShape f.env n info = .impl ind)) ∧
      (∀ l ∈ loopConstructs, ¬ ValueMentions info l) ∧
      ((∃ v, info = .defnInfo v) ∨ (∃ v, info = .opaqueInfo v) → ¬ ValueMentions info ``Lean.Order.fix) ∧
      ((∃ v, info = .defnInfo v) ∨ (∃ v, info = .opaqueInfo v) → ∀ u, ValueMentions info u → ¬ EnvPanic f u) ∧
      ∀ u, Mentions info u → ∀ a, EnvReaches f u a → EnvAxiom f a → EnvAdmits f p a
  occurs : ∀ {f : Regula.Load.Facts} {roots : List Name} {p : Regula.Closed.Profile}, UsedConstantsComplete →
    (Regula.Closed.decision (f.input roots p)).verdict = .pass → ∀ {n m : Name} {info : ConstantInfo},
      f.env.constants.map₁[n]? = some info → f.moduleOf? n = some m → m ∈ f.claimed →
      (∀ l ∈ loopConstructs, ¬ ValueOccurs info l) ∧
      ((∃ v, info = .defnInfo v) ∨ (∃ v, info = .opaqueInfo v) → ¬ ValueOccurs info ``Lean.Order.fix) ∧
      ∀ a, OccursReaches f n a → EnvAxiom f a → EnvAdmits f p a
  claimed : ∀ {f : Regula.Load.Facts}, Assumption.ModuleDataComplete f → ∀ {k : Nat} {lm : Regula.Load.LoadedModule},
    f.modules[k]? = some lm → lm.claimed = true →
    ∃ data, f.env.header.moduleData[k]? = some data ∧
      ∀ n info, (n, info) ∈ data.constNames.zip data.constants → (lm.name, n, info) ∈ f.claimedConstants
  gate : ∀ {L E : Type} {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile} {c : UInt32},
    FullRun t dir p c → ∀ {pre post : List (Event L E)} {e : Event L E}, t = pre ++ e :: post → e.consumesTree = true →
    ∃ (tree : FilePath) (tRead tGate : List (Event L E)) (resp : Except IO.Error Unit) (last : List (Event L E))
      (r : Reading),
      t = (⟨.createTempDir, .ok tree⟩ :: tRead) ++ (tGate ++ ⟨.removeDirAll tree, resp⟩ :: last) ∧
      (∃ mid rest, tGate = mid ++ e :: rest ∧ pre = (⟨.createTempDir, .ok tree⟩ :: tRead) ++ mid) ∧
      Inside r ∧ Evidence tRead dir tree (written tRead) r ∧
      (∃ real, (⟨.realPath tree, .ok real⟩ : Event L E) ∈ tRead ∧ ReadBack tRead real) ∧
      (∀ x ∈ tRead, ¬ x.failed) ∧ (∀ x ∈ tGate, x.keepsFiles) ∧
      ∀ u v, tGate = u ++ v → ∀ q, written ((⟨.createTempDir, .ok tree⟩ :: tRead) ++ u) q = written tRead q
  answered : ∀ {L E : Type} {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile} {c : UInt32},
    FullRun t dir p c → ∀ {pre post : List (Event L E)} {e : Event L E}, t = pre ++ e :: post → e.consumesTree = true →
    ∃ (tree : FilePath) (before suffix mid : List (Event L E)),
      pre = (⟨.createTempDir, .ok tree⟩ :: (before ++ suffix)) ++ mid ∧ Quiet suffix ∧ (∀ x ∈ mid, x.keepsFiles) ∧
      (∀ path text r, (⟨.writeFile path text, r⟩ : Event L E) ∈ before ++ suffix → written pre (parts path) = some text →
        (⟨.readFile path, .ok text⟩ : Event L E) ∈ suffix) ∧
      ∃ real err, (⟨.realPath tree, .ok real⟩ : Event L E) ∈ before ++ suffix ∧
        (⟨.symlinkMetadata (real / "lakefile.lean"), .error err⟩ : Event L E) ∈ suffix ∧
        ∃ name code details, err = .noFileOrDirectory name code details
  config : ∀ {L E : Type} {t pre post : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile} {c : UInt32},
    FullRun t dir p c → ∀ {e : Event L E}, t = pre ++ e :: post → e.consumesTree = true → OneRealPath t →
    ∃ (tree real path : FilePath) (before suffix mid : List (Event L E)) (text : String) (table : Lake.Toml.Table),
      pre = (⟨.createTempDir, .ok tree⟩ :: (before ++ suffix)) ++ mid ∧ Quiet suffix ∧
      (⟨.realPath tree, .ok real⟩ : Event L E) ∈ before ++ suffix ∧
      parts path = parts (real / "lakefile.toml") ∧ (⟨.readFile path, .ok text⟩ : Event L E) ∈ suffix ∧
      (⟨.parseToml (Lean.Parser.mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∈ before ++ suffix ∧
      ∀ B : LakeSelection pre real, ∀ taken, B.Takes taken → parts taken = parts path
  compiled : ∀ {L E : Type} {t : List (Event L E)} {dir tree : FilePath} {held : List String → Option String}
    {r : Reading}, Evidence t dir tree held r →
    ∃ (project real : FilePath) (sysroot : String) (root : Root L) (log : List String)
      (modules : List (Name × FilePath)) (headers : List (Name × Array Import)),
      (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t ∧
      (⟨.loadRoot sysroot real, .ok (some root, log)⟩ : Event L E) ∈ t ∧
      DefaultModules t root root.defaultTargets modules ∧
      ∀ (B : LakeBehaviour headers root modules) m path, B.Compiles m path →
        ∃ f ∈ r.files, f.module = m ∧ ∃ imports mods text, ReadText t root project real f path imports mods text ∧
          held (parts path) = some text
  noLink : ∀ {L E : Type} {t : List (Event L E)} {root : Root L} {project tree path : FilePath} {f : FileRead}
    {imports : Array Import} {mods : List Name} (B : RealPathBehaviour t), ReadAs t root project tree f path imports mods →
    ∃ (rel : List String) (real : FilePath), (⟨.realPath (under project rel), .ok real⟩ : Event L E) ∈ t ∧
      ¬ B.Crosses (under project rel)
  noProjectCode : ∀ (B : LeanBehaviour) {d : Reading → Outcome}, languageRecord.Meets d → ∀ (r : Reading),
    d r = .admitted → ∀ f ∈ r.files, ∃ ts, B.Elaborates f ts ∧ B.NoProjectCode ts
  helper : ∀ {i : RegulaSpecification.Input}, SafeMentionsSafe i → ∀ {d p : RegulaSpecification.Decl}, d ∈ i.decls →
    d.safety = .safe → p ∈ i.decls → i.HelperForm p → ¬ i.Reaches d.name p.name
  ctorIdx : ∀ {i : RegulaSpecification.Input}, SafeMentionsSafe i → ∀ {d p : RegulaSpecification.Decl}, d ∈ i.decls →
    d.safety = .safe → p ∈ i.decls → i.CtorIdxImpl p → ¬ i.Reaches d.name p.name

theorem meaning : Meaning where
  record := Effects.run_meets
  executed := executed_meets
  routes := run_route
  plainPass := plainRun_pass
  plainExit := plain_exit_zero
  outProofPass := outProofRun_pass
  outProofExit := outProof_exit_zero
  fullExit := full_exit_zero
  cone := fun h => replayConstants_env (input_loaded h)
  claimedReplayed := fun h => claimed_theorem_replayed (input_loaded h)
  loaderPass := pass_iff
  loaderFloor := pass_floor
  loaderHeld := pass_held
  occurs := pass_occurs
  claimed := claimedConstants_complete
  gate := FullRun.gate_stands
  answered := FullRun.answered_at_consumer
  config := lake_takes_judged
  compiled := read_what_lake_compiles
  noLink := read_no_link
  noProjectCode := admitted_runs_no_project_code
  helper := helperForm_unreached
  ctorIdx := ctorIdxImpl_unreached

end RegulaSpecification.Meaning
