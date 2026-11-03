import RegulaSpecification.Assumptions

/-!
# What a verdict means

{lit}`Meaning` states, once, each theorem of this package that says what a verdict of {name}`Regula.Shell.run` means: what every run
rests on for every response, which route a run is, what a pass of each verdict says, what the loader's input says of the
environment that Lean gave, and what H1 to H6 and the other premises about Lean, Lake and the operating system add.
{lit}`meaning` proves it from those theorems.

Each premise of a field about Lean, Lake or the operating system is the formal statement of an entry of
{name (full := RegulaSpecification.Assumptions.Assumption)}`Assumptions.Assumption` ({name (full := RegulaSpecification.Assumptions.Assumption.formal)}`Assumption.formal`): {name (full := RegulaSpecification.Language.LeanBehaviour)}`LeanBehaviour`, {name (full := RegulaSpecification.Effects.LakeBehaviour)}`LakeBehaviour`, {name (full := RegulaSpecification.Effects.RealPathBehaviour)}`RealPathBehaviour`, {name (full := RegulaSpecification.Effects.OneRealPath)}`OneRealPath`,
{name (full := RegulaSpecification.Effects.LakeSelection)}`LakeSelection`, {name (full := RegulaSpecification.SafeMentionsSafe)}`SafeMentionsSafe`, {name (full := RegulaSpecification.Loader.UsedConstantsComplete)}`UsedConstantsComplete` and {name (full := RegulaSpecification.Assumptions.Assumption.ModuleDataComplete)}`ModuleDataComplete`. Every other premise states what the
run asked and received, or what the loader gave. So a premise added to one of these theorems, or to a lemma that one of them
uses, is either proved there or changes that theorem's statement, which then differs from its field, and {lit}`meaning` fails.

This covers the statements of these theorems. {lit}`Meaning` itself is the one definition of what a verdict means: a premise
written into one of its fields changes the contract, which review judges, and no check classifies it, because whether a
proposition is about Lean, Lake or the operating system depends on what it means and not on its form. A definition that a
field uses, such as {name (full := RegulaSpecification.Effects.FullRun)}`FullRun`, means what its own definition says, and the published text cites no other theorem as
stating what a verdict means.
-/

namespace RegulaSpecification.Meaning

open Lean (Name ConstantInfo Import)
open System (FilePath)
open Regula.Effect
open Regula.Language
open RegulaSpecification.Effects
open RegulaSpecification.Language
open RegulaSpecification.Loader
open RegulaSpecification.Assumptions

/-- What a run of each route is, by what it asked and received: its first two events ask for the Lean release and for
{lit}`REGULA_FULL`, whose answer selects the route. -/
def _root_.RegulaSpecification.Assumptions.Route.Runs {L E : Type} : Route → List (Event L E) → UInt32 → Prop
  | .proof, t, c => ∃ p v rest, t = ⟨.leanVersion, v⟩ :: ⟨.getEnv Regula.Shell.fullVariable, none⟩ :: rest ∧
      PlainRun (⟨.leanVersion, v⟩ :: rest) p c
  | .full, t, c => ∃ p v rest, ∃ dir : String,
      t = ⟨.leanVersion, v⟩ :: ⟨.getEnv Regula.Shell.fullVariable, some dir⟩ :: rest ∧ FullRun rest (FilePath.mk dir) p c

/-- **Every run is a refusal or a run of a route**, for every argument list and every response. A mode added to
{name}`Regula.Shell.run` changes {name}`run_subject`, and this proof fails until the mode is a {name}`Route` with what it relies on. -/
theorem run_route {L E : Type} {args : List String} {t : List (Event L E)} {c : UInt32}
    (h : Runs (Regula.Shell.run args : Prog L E UInt32) t c) : Refusal t c ∨ ∃ r : Route, r.Runs t c := by
  rcases run_subject h with hr | ⟨p, v, rest, ⟨ht, hp⟩ | ⟨dir, ht, hf⟩⟩
  · exact .inl hr
  · exact .inr ⟨.proof, p, v, rest, ht, hp⟩
  · exact .inr ⟨.full, p, v, rest, dir, ht, hf⟩

/-- What a verdict means, each field the statement of the theorem that its docstring names. -/
structure Meaning : Prop where
  /-- {name}`Effects.run_meets`: every run of the program meets the record, for every argument list and every response. -/
  record : ∀ {L E : Type}, RunMeets (Regula.Shell.run : List String → Prog L E UInt32)
  /-- {name}`executed_meets`: what the executable computes is the value of a run, with each answer of the table. -/
  executed : ∀ {L E : Type} (table : (o : Op L E) → BaseIO (Resp o)) (args : List String) (w : Void IO.RealWorld),
    Runs (Regula.Shell.run args : Prog L E UInt32) (traceFrom table (Regula.Shell.run args) w)
      (Prog.interpret table (Regula.Shell.run args) w).val
  /-- {name}`run_route`: every run is a refusal or a run of a route. -/
  routes : ∀ {L E : Type} {args : List String} {t : List (Event L E)} {c : UInt32},
    Runs (Regula.Shell.run args : Prog L E UInt32) t c → Refusal t c ∨ ∃ r : Route, r.Runs t c
  /-- {name}`plainRun_pass`: a pass of the proof verdict names the current directory's real path, from which the workspace it
  read was loaded. -/
  plainPass : ∀ {L E : Type} {t : List (Event L E)} {p : Regula.Closed.Profile}, PlainRun t p 0 →
    ∃ subject : FilePath, EndsWith t (Regula.Closed.Verdict.pass.proofLineOn subject.toString) ∧
      (⟨.realPath ".", .ok subject⟩ : Event L E) ∈ t ∧
      ∃ sysroot root log, (⟨.loadWorkspace sysroot subject, .ok (some root, log)⟩ : Event L E) ∈ t ∧ PlainRoot t root
  /-- {name}`plain_exit_zero`: exit 0 of the proof verdict gives the closed form and the floor of what Lean and Lake returned, and
  that Lean's replay of the cone of the claim answered with success. -/
  plainExit : ∀ {L E : Type} {t : List (Event L E)} {p : Regula.Closed.Profile}, PlainRun t p 0 →
    ∃ (root : Root L) (f : Regula.Load.Facts) (roots : List Name), PlainRoot t root ∧ BuildRead t root f roots ∧
      EnvForm f ∧ EnvFloor f p ∧ (∀ r ∈ roots, r ∈ f.claimed) ∧
      ∃ i, f.input roots p = .ok i ∧ (⟨.kernelReplay (f.replayConstants i), .ok ()⟩ : Event L E) ∈ t
  /-- {name}`full_exit_zero`: exit 0 of the full gate gives an admitted reading on {name}`Evidence`, the build ending with 0, the
  floor of the build, and that Lean's replay of the cone of its claim answered with success. -/
  fullExit : ∀ {L E : Type} {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile}, FullRun t dir p 0 →
    ∃ (tree : FilePath) (sysroot : String) (tRead tBuild tRules : List (Event L E)) (r : Reading), Inside r ∧
      Evidence tRead dir tree (written tRead) r ∧ (∀ e ∈ tRead, ¬ e.failed) ∧
      (∃ program lakeLib,
        ([⟨.lakeInstall sysroot, (program, lakeLib)⟩, ⟨.runLake program tree ["build", "--wfail"], .ok 0⟩] :
          List (Event L E)).Sublist tBuild) ∧
      ∃ (root : Root L) (f : Regula.Load.Facts) (roots : List Name),
        TreeRoot sysroot tree tRules root ∧ BuildRead tRules root f roots ∧ EnvForm f ∧ EnvFloor f p ∧
        ∃ i, f.input roots p = .ok i ∧ (⟨.kernelReplay (f.replayConstants i), .ok ()⟩ : Event L E) ∈ tRules
  /-- {name}`Loader.replayConstants_env`: what Lean's replay is given is exactly the cone of the claim, each constant as the environment
  keeps it, but the companions of {lit}`Quot`, and the copies, each under a name of its own. -/
  cone : ∀ {f : Regula.Load.Facts} {roots : List Name} {p : Regula.Closed.Profile} {i : Regula.Closed.Input},
    f.input roots p = .ok i → ∀ (n : Name) (info : ConstantInfo),
      (f.replayConstants i)[n]? = some info ↔
        (f.env.constants.map₁[n]? = some info ∧ InCone f n ∧ ∀ v, info = .quotInfo v → v.kind = .type) ∨
          (n, info) ∈ copyEntries f
  /-- {name}`Loader.claimed_theorem_replayed`: each theorem of a claimed module, as its own module states it, is the kept constant by
  {lit}`==` or is given to the replay under a name of its own. -/
  claimedReplayed : ∀ {f : Regula.Load.Facts} {roots : List Name} {p : Regula.Closed.Profile} {i : Regula.Closed.Input},
    f.input roots p = .ok i → ∀ {m n : Name} {v : Lean.TheoremVal}, (m, n, .thmInfo v) ∈ f.claimedConstants →
      (f.env.constants.map₁[n]? == some (.thmInfo v)) = true ∨
        ∃ k, (f.replayConstants i)[(Regula.Load.copyAt (Regula.Load.copyRoot f.env.constants.map₁) (v, k)).1]? =
          some (Regula.Load.copyAt (Regula.Load.copyRoot f.env.constants.map₁) (v, k)).2
  /-- {name}`Loader.pass_iff`: the rules pass on the loader's input exactly when the environment has {name}`EnvForm` and {name}`EnvFloor`. -/
  loaderPass : ∀ {f : Regula.Load.Facts} {roots : List Name} {p : Regula.Closed.Profile} {i : Regula.Closed.Input},
    f.input roots p = .ok i → (i.report.verdict = .pass ↔ EnvForm f ∧ EnvFloor f p)
  /-- {name}`Loader.pass_floor`: the floor on the path that the shell decides. -/
  loaderFloor : ∀ {f : Regula.Load.Facts} {roots : List Name} {p : Regula.Closed.Profile},
    (Regula.Closed.decision (f.input roots p)).verdict = .pass →
      (∀ r ∈ roots, r ∈ f.claimed) ∧ (∀ m ∈ f.claimed, m ∈ f.env.header.moduleNames.toList) ∧
      (∀ n info, f.env.constants.map₁[n]? = some info → ∃ m, f.moduleOf? n = some m) ∧ EnvForm f ∧ EnvFloor f p
  /-- {name}`Loader.pass_held`: on a pass, what each constant of a claimed module's own {lit}`.olean` holds. -/
  loaderHeld : ∀ {f : Regula.Load.Facts} {roots : List Name} {p : Regula.Closed.Profile},
    (Regula.Closed.decision (f.input roots p)).verdict = .pass → ∀ {m n : Name} {info : ConstantInfo},
      (m, n, info) ∈ f.claimedConstants →
      (∀ v, info ≠ .axiomInfo v) ∧
      ((info.isUnsafe = true ∨ info.isPartial = true ∨ ∃ b, n = .str b "_unsafe_rec") →
        info.isPartial = true ∧ info.isUnsafe = false) ∧
      (∀ l ∈ loopConstructs, ¬ ValueMentions info l) ∧
      ∀ u, Mentions info u → ∀ a, EnvReaches f u a → EnvAxiom f a → EnvAdmits f p a
  /-- {name}`Loader.pass_occurs`, under {name}`UsedConstantsComplete`: the floor over the constants that occur. -/
  occurs : ∀ {f : Regula.Load.Facts} {roots : List Name} {p : Regula.Closed.Profile}, UsedConstantsComplete →
    (Regula.Closed.decision (f.input roots p)).verdict = .pass → ∀ {n m : Name} {info : ConstantInfo},
      f.env.constants.map₁[n]? = some info → f.moduleOf? n = some m → m ∈ f.claimed →
      (∀ l ∈ loopConstructs, ¬ ValueOccurs info l) ∧ ∀ a, OccursReaches f n a → EnvAxiom f a → EnvAdmits f p a
  /-- {name}`Loader.claimedConstants_complete`, under {name (full := RegulaSpecification.Assumptions.Assumption.ModuleDataComplete)}`ModuleDataComplete`: each constant of each claimed module is read. -/
  claimed : ∀ {f : Regula.Load.Facts}, Assumption.ModuleDataComplete f → ∀ {k : Nat} {lm : Regula.Load.LoadedModule},
    f.modules[k]? = some lm → lm.claimed = true →
    ∃ data, f.env.header.moduleData[k]? = some data ∧
      ∀ n info, (n, info) ∈ data.constNames.zip data.constants → (lm.name, n, info) ∈ f.claimedConstants
  /-- {name}`FullRun.gate_stands`: at each consumer of a full run, what stands is what an admitted reading left. -/
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
  /-- {name}`FullRun.answered_at_consumer`: what the tree's file system answered after the reading's last act. -/
  answered : ∀ {L E : Type} {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile} {c : UInt32},
    FullRun t dir p c → ∀ {pre post : List (Event L E)} {e : Event L E}, t = pre ++ e :: post → e.consumesTree = true →
    ∃ (tree : FilePath) (before suffix mid : List (Event L E)),
      pre = (⟨.createTempDir, .ok tree⟩ :: (before ++ suffix)) ++ mid ∧ Quiet suffix ∧ (∀ x ∈ mid, x.keepsFiles) ∧
      (∀ path text r, (⟨.writeFile path text, r⟩ : Event L E) ∈ before ++ suffix → written pre (parts path) = some text →
        (⟨.readFile path, .ok text⟩ : Event L E) ∈ suffix) ∧
      ∃ real err, (⟨.realPath tree, .ok real⟩ : Event L E) ∈ before ++ suffix ∧
        (⟨.symlinkMetadata (real / "lakefile.lean"), .error err⟩ : Event L E) ∈ suffix ∧
        ∃ name code details, err = .noFileOrDirectory name code details
  /-- {name}`lake_takes_judged`, under {name}`OneRealPath` and H5 ({name}`LakeSelection`): Lake takes the configuration judged. -/
  config : ∀ {L E : Type} {t pre post : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile} {c : UInt32},
    FullRun t dir p c → ∀ {e : Event L E}, t = pre ++ e :: post → e.consumesTree = true → OneRealPath t →
    ∃ (tree real path : FilePath) (before suffix mid : List (Event L E)) (text : String) (table : Lake.Toml.Table),
      pre = (⟨.createTempDir, .ok tree⟩ :: (before ++ suffix)) ++ mid ∧ Quiet suffix ∧
      (⟨.realPath tree, .ok real⟩ : Event L E) ∈ before ++ suffix ∧
      parts path = parts (real / "lakefile.toml") ∧ (⟨.readFile path, .ok text⟩ : Event L E) ∈ suffix ∧
      (⟨.parseToml (Lean.Parser.mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∈ before ++ suffix ∧
      ∀ B : LakeSelection pre real, ∀ taken, B.Takes taken → parts taken = parts path
  /-- {name}`read_what_lake_compiles`, under H3 ({name}`LakeBehaviour`): every file that Lake compiles for the claim was read and judged. -/
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
  /-- {name}`read_no_link`, under H4 ({name}`RealPathBehaviour`): the file of a reading crossed no link. -/
  noLink : ∀ {L E : Type} {t : List (Event L E)} {root : Root L} {project tree path : FilePath} {f : FileRead}
    {imports : Array Import} {mods : List Name} (B : RealPathBehaviour t), ReadAs t root project tree f path imports mods →
    ∃ (rel : List String) (real : FilePath), (⟨.realPath (under project rel), .ok real⟩ : Event L E) ∈ t ∧
      ¬ B.Crosses (under project rel)
  /-- {name}`admitted_runs_no_project_code`, under H1 and H2 ({name}`LeanBehaviour`): an admitted reading runs no project code. -/
  noProjectCode : ∀ (B : LeanBehaviour) {d : Reading → Outcome}, languageRecord.Meets d → ∀ (r : Reading),
    d r = .admitted → ∀ f ∈ r.files, ∃ ts, B.Elaborates f ts ∧ B.NoProjectCode ts
  /-- {name}`helperForm_unreached`, under H6 ({name}`SafeMentionsSafe`): no safe constant reaches one of the exempted form. -/
  helper : ∀ {i : RegulaSpecification.Input}, SafeMentionsSafe i → ∀ {d p : RegulaSpecification.Decl}, d ∈ i.decls →
    d.safety = .safe → p ∈ i.decls → i.HelperForm p → ¬ i.Reaches d.name p.name

/-- **What a verdict means, from the theorems that state it.** -/
theorem meaning : Meaning where
  record := Effects.run_meets
  executed := executed_meets
  routes := run_route
  plainPass := plainRun_pass
  plainExit := plain_exit_zero
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

end RegulaSpecification.Meaning
