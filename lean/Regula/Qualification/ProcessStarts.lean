import Lean
import Lake

/-! # Process starts of Regula's own code

Each declaration of Regula's libraries that refers directly to a function that starts a process
(`starters`) must be an entry of `allowed`, which says how the program it starts is chosen, and no
declaration may refer to a function that finds a toolchain program through `PATH`
(`pathFinders`). The operational self-audit (`Regula.Qualification.SelfAudit`) reads the
references from the kernel value and type of every constant of the modules it audits
(`references`) and decides them with `violations` (`violations_eq_empty`). It is a tripwire for
direct references to the listed starters only: a process started through another function, such as
Lake's build API, is not a direct reference, so this check does not see it. Following references
into dependencies is the reach check of issue #362 (its part 1b). Regula gives Lake the
installation it builds with (`Regula.Checker.Workspace`). A program named by a string that a
caller passes is chosen by that caller, which the entry of the starting declaration names. -/
namespace Regula.Qualification.ProcessStarts

open Lean

/-- The functions of Lean and of the pinned Lake that start a process: Lean's `IO.Process.spawn`,
`output` and `run`, and each public function of Lake v4.34.1 whose own body starts one, by its
source file in `src/lean/lake`: `Lake.rawProc` (`Lake/Util/Proc.lean:29`), `Lake.captureProc?`
(`:61`) and `Lake.testProc` (`:69`); `Lake.env` (`Lake/CLI/Actions.lean:20`) and
`Lake.Workspace.evalLeanFile` (`:108`); `Lake.lake.env` (`Lake/CLI/Main.lean:1158`);
`Lake.serve` (`Lake/CLI/Serve.lean:90`); `Lake.CacheService.downloadArtifacts`
(`Lake/Config/Cache.lean:911`); and `Lake.LeanInstall.get` (`Lake/Config/InstallPath.lean:272`),
which runs its installation's `lean --githash` by its path. It also lists the wrappers of
`Lake.rawProc` in `Lake/Util/Proc.lean`: `Lake.proc` (`:38`), `Lake.captureProc'` (`:49`) and
`Lake.captureProc` (`:58`). The functions of that Lake that are not public, such as
`Lake.Workspace.updateToolchain` (`Lake/Load/Resolve.lean:369`), cannot be referenced from Regula.
`Lake.lake.env` and `Lake.serve` are in modules of Lake's command line, which `import Lake` does not
import, so they are named without a check that they resolve. This is a list of direct starters: a
function that starts a process through one of them, such as Lake's build functions, is not on it
(`references`). -/
def starters : List Name :=
  [``IO.Process.spawn, ``IO.Process.output, ``IO.Process.run, ``Lake.rawProc, ``Lake.proc,
    ``Lake.captureProc', ``Lake.captureProc, ``Lake.captureProc?, ``Lake.testProc, ``Lake.env,
    ``Lake.Workspace.evalLeanFile, `Lake.lake.env, `Lake.serve,
    ``Lake.CacheService.downloadArtifacts, ``Lake.LeanInstall.get]

/-- The functions of Lean and of the pinned Lake that find the toolchain by running a `lean` that
`PATH` (or `LEAN`) names when no other source names it (`Lean.findSysroot`,
`Lake.findLeanSysroot?`) or that treat the running program as a `lake` beside its `lean`
(`Lake.findInstall?`). -/
def pathFinders : List Name :=
  [``Lean.findSysroot, ``Lake.findInstall?, ``Lake.findLeanInstall?, ``Lake.findLeanSysroot?,
    ``Lake.findLeanCmdInstall?]

/-- One declaration that refers directly to a function of `starters` or `pathFinders`. -/
structure Start where
  /-- The module that declares it. -/
  «module» : String
  /-- Its name as written in its source (`Lean.privateToUserName?`). -/
  declaration : String
  /-- The functions of `starters` and `pathFinders` it refers to. -/
  references : Array String
  deriving ToJson, FromJson, Inhabited

/-- One declaration that may start a process, with how the program it starts is chosen. -/
structure Allowed where
  /-- The module that declares it. -/
  «module» : String
  /-- Its name as written in its source. -/
  declaration : String
  /-- How the program it starts is chosen. -/
  program : String

/-- The declarations of Regula's libraries that may start a process. -/
def allowed : List Allowed := [
  ⟨"Regula.Checker.CheckerSelftest", "Regula.Checker.CheckerSelftest.driverCopyControl",
    "the toolchain's `lean`, by its path (`Regula.Toolchain.program`)"⟩,
  ⟨"Regula.Checker.Common", "Regula.Checker.runProcess",
    "the caller's program; a toolchain program's bare name is refused \
      (`Regula.Toolchain.refuseBareName`)"⟩,
  ⟨"Regula.Checker.Common", "Regula.Checker.runProcessShowing",
    "the caller's program; a toolchain program's bare name is refused \
      (`Regula.Toolchain.refuseBareName`)"⟩,
  ⟨"Regula.Checker.Common", "Regula.Checker.runTypedWorker",
    "this checker's own executable (`workerBinary`)"⟩,
  ⟨"Regula.Checker.Environment", "Regula.Checker.Environment.replacementHistory",
    "the built `axiomGate` of the package under check, by its path"⟩,
  ⟨"Regula.Checker.Producer", "Regula.Checker.Producer._aux_Regula_Checker_Producer___elabRules_\
      Regula_Checker_Producer_termRegula_build_revision_1",
    "`git`, found on `PATH`, at elaboration; not a toolchain program"⟩,
  ⟨"Regula.Checker.Workspace", "Regula.Checker.Workspace.detectEnvironment",
    "Lake's `LeanInstall.get` for the identity-checked installation (`Regula.Toolchain.sysroot`), \
      as collocated, so it starts no `lean --githash`"⟩,
  ⟨"Regula.Checker.Snapshot", "Regula.Checker.Snapshot.statusBytes",
    "`git`, found on `PATH`; not a toolchain program"⟩,
  ⟨"Regula.CompilerObservation", "Regula.CompilerObservation.identifiedRoot",
    "the `bin/lean` of the toolchain root Lake gives (`toolchainRoot`), by its path"⟩,
  ⟨"Regula.CompilerProbe", "Regula.Toolchain.selectedLean",
    "`elan`, found on `PATH`: `doctor` reports the compiler the adopter's Elan selects; Elan is \
      not a program of the toolchain"⟩,
  ⟨"Regula.CompilerProbe", "Regula.Toolchain.probe",
    "the `lean` that the adopter's Elan lists for the selector (`selectedLean`), by its path"⟩,
  ⟨"Regula.DiagnosticsGate", "Regula.DiagnosticsGate.git",
    "`git`, found on `PATH`; not a toolchain program"⟩,
  ⟨"Regula.Qualification.Acceptance", "Regula.Qualification.Acceptance.worker",
    "the real `axiomGate` beside this proxy, by its path"⟩,
  ⟨"Regula.Qualification.Acceptance", "Regula.Qualification.Acceptance.qualify",
    "the built `axiomGate`, by its path"⟩,
  ⟨"Regula.Qualification.InputInventory", "Regula.Qualification.InputInventory.worker",
    "the path in `INVENTORY_LAKE`, which the campaign sets to the toolchain's `lake`"⟩,
  ⟨"Regula.Qualification.ReceiptBoundary", "Regula.Qualification.ReceiptBoundary.check",
    "`/bin/chmod` and this executable, by their paths"⟩,
  ⟨"Regula.Qualification.RuleExamples", "Regula.Qualification.RuleExamples.observe",
    "the built detector binary the caller passes, by its path"⟩,
  ⟨"Regula.Qualification.Support", "Regula.Qualification.timeoutCommand",
    "GNU `gtimeout` or `timeout`, found on `PATH`; not a toolchain program"⟩,
  ⟨"Regula.Qualification.Support", "Regula.Qualification.run",
    "the caller's program; a toolchain program's bare name is refused \
      (`Regula.Toolchain.refuseBareName`)"⟩,
  ⟨"Regula.Qualification.Support", "Regula.Qualification.runBounded",
    "GNU timeout (`timeoutCommand`), which runs the caller's program"⟩,
  ⟨"Regula.Release", "Regula.Release.gh", "`gh`, found on `PATH`; not a toolchain program"⟩,
  ⟨"Regula.Release", "Regula.Release.git", "`git`, found on `PATH`; not a toolchain program"⟩,
  ⟨"Regula.Release", "Regula.Release.lakeVersion",
    "the `lake` beside the `lean` that runs this program (`IO.appDir`), by its path"⟩,
  ⟨"Regula.Site.Deployment", "Regula.Site.Deployment.fetch",
    "`env`, found on `PATH`, which runs `curl`, found on `PATH`; neither is a toolchain program"⟩,
  ⟨"RegulaProvision", "RegulaProvision.run",
    "the caller's program; a toolchain program's bare name is refused, and the toolchain's run \
      by their paths beside the running `lean` (`toolchain`)"⟩,
  ⟨"RegulaProvision", "RegulaProvision.stream",
    "the caller's program; a toolchain program's bare name is refused, and the toolchain's run \
      by their paths beside the running `lean` (`toolchain`)"⟩,
  ⟨"RegulaProvision", "RegulaProvision.requireReleasedCompiler",
    "the `lean` beside the running `lean` (`toolchain`), by its path"⟩,
  ⟨"RegulaVerification", "RegulaVerification.requireCompiler",
    "the `lean` that runs this driver (`IO.appPath`), by its path"⟩,
  ⟨"RegulaVerification", "RegulaVerification.start",
    "the recipe's program; `lake`, `lean` and the program of `lake env` by their paths beside \
      the running `lean` (`Command.resolve`), through `nice` at low priority"⟩]

/-- The declarations among `names` whose kernel value or type refers to a function of `starters`
or `pathFinders`, each with its module in `env` and the functions it refers to. A name that `env`
does not hold, or whose module it does not record, is left out. -/
def references (env : Environment) (names : Array Name) : Array Start :=
  names.filterMap fun name => do
    let info ← env.find? name
    let used := info.getUsedConstantsAsSet
    let found := (starters ++ pathFinders).filter used.contains
    if found.isEmpty then none
    let idx ← env.getModuleIdxFor? name
    let owner ← env.header.moduleNames[idx.toNat]?
    some ⟨owner.toString, ((privateToUserName? name).getD name).toString,
      found.toArray.map toString⟩

/-- Whether `start` is an entry of `allowed`, by module and declaration. -/
def Start.allowed (start : Start) : Bool :=
  ProcessStarts.allowed.any fun entry =>
    entry.module == start.module && entry.declaration == start.declaration

/-- Whether `start` refers to a function of `pathFinders`. -/
def Start.findsPath (start : Start) : Bool :=
  start.references.any ((pathFinders.map toString).contains ·)

/-- The finding for each declaration of `starts` that refers to a function of `pathFinders` or is
no entry of `allowed`, then for each entry of `allowed` whose module is not one of `audited` or
that no declaration of `starts` is. -/
def violations (starts : Array Start) (audited : List String) : Array String :=
  let unlisted := starts.filterMap fun start =>
    if start.findsPath then
      some s!"{start.declaration} ({start.module}) finds a toolchain program through PATH: \
        {start.references}"
    else if start.allowed then none
    else
      some s!"{start.declaration} ({start.module}) starts a process ({start.references}) and is \
        no entry of Regula.Qualification.ProcessStarts.allowed, which says how each program is \
        chosen"
  let stale := ProcessStarts.allowed.toArray.filterMap fun entry =>
    if audited.contains entry.module &&
        starts.any (fun start => start.module == entry.module &&
          start.declaration == entry.declaration) then none
    else
      some s!"{entry.declaration} ({entry.module}) is an entry of \
        Regula.Qualification.ProcessStarts.allowed that the audit did not find starting a process"
  unlisted ++ stale

/-- No finding means every declaration of `starts` is an entry of `allowed` and refers to no
function of `pathFinders`, and every entry of `allowed` is in an audited module and is a
declaration of `starts`. -/
theorem violations_eq_empty {starts : Array Start} {audited : List String}
    (h : violations starts audited = #[]) :
    (∀ start ∈ starts, start.findsPath = false ∧ start.allowed = true) ∧
    ∀ entry ∈ ProcessStarts.allowed, entry.module ∈ audited ∧
      ∃ start ∈ starts, start.module = entry.module ∧ start.declaration = entry.declaration := by
  simp only [violations, Array.append_eq_empty_iff, Array.filterMap_eq_empty_iff] at h
  obtain ⟨unlisted, stale⟩ := h
  refine ⟨fun start mem => ?_, fun entry mem => ?_⟩
  · have := unlisted start mem
    split at this
    · simp at this
    · rename_i paths
      split at this
      · rename_i listed
        exact ⟨by simpa using paths, listed⟩
      · simp at this
  · have := stale entry (List.mem_toArray.mpr mem)
    split at this
    · rename_i found
      simp only [Bool.and_eq_true, List.contains_iff_mem, Array.any_eq_true,
        beq_iff_eq] at found
      obtain ⟨audit, i, bound, same⟩ := found
      exact ⟨audit, starts[i], Array.getElem_mem bound, same.1, same.2⟩
    · simp at this

end Regula.Qualification.ProcessStarts
