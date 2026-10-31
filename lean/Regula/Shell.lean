/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Regula.Reader
public import Regula.Rules

/-!
# The shell of the checker

The checker's whole run as a program over the closed operations of `Regula.Effect`, which the `lint`
executable interprets (`Regula.LintMain`), Lake's lint driver for a project that sets
`lintDriver := "regula/lint"`. It performs nothing itself, and every decision it holds is pure code
about what a response holds, so that `specification/RegulaSpecification/Proofs/Shell.lean` states what it does
for every response.

A run with one profile gives the proof verdict, that of `Regula.Closed.decision`: `pass` (exit 0) when
the input has the closed form and no rule reports a subject, `fail` (exit 1) when a rule reports one, and
`incomplete` (exit 2) when the build cannot be loaded or the input does not have the closed form (RG2001).
It promises nothing about what ran during the build.

A run with the profile, `full` and a directory is the full gate (`Regula.Language.gate`) on the project
there: the language check, which copies what it reads to a tree of the checker's own, then, for an admitted
project, the build and its replay in that tree and the same rules on it. Only that run can print a full
verdict, because only there the check came first, and only from a checker that the project's Lake did not start
(`Regula.Reader.startedOutside`). A project with a dependency or with Mathlib in its imports gets no build from
it: it says that only a proof verdict is possible and exits with 3.

Each line but the last starts with two spaces (`Regula.Reader.say`). The last is a function of the verdict
alone (`Regula.Closed.Verdict.proofLine`, `Regula.Language.Report.label`), and so is the exit code.
-/

public section

namespace Regula.Shell

open Lean (Name)
open System (FilePath)
open Regula.Closed
open Regula.Effect
open Regula.Reader

variable {L E : Type}

/-- Whether this is the one Lean release that this revision of Regula reads. -/
def supportsLean (version commit : String) : Bool :=
  (version, commit) == pinnedLean

/-- The line of one finding. -/
def line (f : Finding) : String :=
  let place := if f.module == f.subject then "" else s!" (module {f.module})"
  s!"{f.rule.spelling} {f.subject}{place}: {f.detail}"

/-- What a report says beside its verdict: each finding, and how many there are or why it is incomplete. -/
def details : Report → List String
  | .pass => []
  | .fail first rest =>
    (first :: rest).map line ++ [s!"{rest.length + 1} findings"]
  | .incomplete why => [s!"RG2001: {why}"]

/-- What a run read. -/
def coverage (i : Input) : String :=
  s!"regula: read {i.modules.length} claimed modules and {i.claimedDecls.length} of their constants"

/-- The spellings of the profiles, for a refusal. -/
def profileSpellings : String :=
  ", ".intercalate (Profile.all.map (·.spelling))

/-- The profile of a run of the Lean release `version` at `commit` with the arguments `args`, or why
the run is `incomplete`: any other release, and any argument list other than one profile. -/
def profileOfRun (version commit : String) (args : List String) : Except String Profile :=
  if !supportsLean version commit then
    .error s!"this revision of Regula reads only Lean 4.35.0, and this is Lean {version} ({commit})"
  else
    match args with
    | [text] =>
      match Profile.ofSpelling? text with
      | some profile => .ok profile
      | none => .error s!"{text} is no profile: {profileSpellings}"
    | _ =>
      .error s!"state one profile in `lintDriverArgs`: {profileSpellings}, or, from a checkout of \
        Regula, a profile, `full` and the project's directory"

/-- Each of the modules `names`, in that order, with where Lean finds its `.olean` on Lake's search
path. The result carries that it is these modules and what each place decides. -/
def readModules (toolchainDir rootDir : FilePath) : (names : List Name) →
    Attempt L E { ms : List Regula.Load.LoadedModule // ms.map (·.name) = names ∧
      ∀ m ∈ ms, m = Regula.Load.LoadedModule.ofPlace toolchainDir rootDir m.name m.olean }
  | [] => pure ⟨[], rfl, by simp⟩
  | n :: rest => do
    let olean ← attempt (Prog.call (.findOLean n))
    let ⟨ms, hn, hp⟩ ← readModules toolchainDir rootDir rest
    pure ⟨Regula.Load.LoadedModule.ofPlace toolchainDir rootDir n olean :: ms,
      by simp [Regula.Load.LoadedModule.ofPlace_name, hn],
      by
        intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact Regula.Load.LoadedModule.ofPlace_self ..
        · exact hp m hm⟩

/-- The facts of `env`, from where the `.olean` of each of its modules lies. -/
def factsOf (env : Lean.Environment) (toolchainDir rootDir : FilePath) : Attempt L E Regula.Load.Facts := do
  let ⟨ms, hn, hp⟩ ← readModules toolchainDir rootDir env.header.moduleNames.toList
  pure { env, toolchainDir, rootDir, modules := ms.toArray, names := by simpa using hn,
         placed := by simpa using hp }

/-- The closed input of the finished build that the load `root` describes. -/
def inputOf (root : Root L) (profile : Profile) : Attempt L E Input := do
  let modules ← defaultModules root root.defaultTargets
  let roots := modules.map (·.1)
  ExceptT.lift (Prog.call (.setSearchPath root.leanPath))
  let env ← attempt (Prog.call (.importForRules roots.toArray))
  let f ← factsOf env root.leanLib root.rootLib
  ExceptT.mk (pure (f.input roots profile))

/-- The closed input of the finished build of the workspace that Lake dispatched from the current directory.
-/
def loadPlain (profile : Profile) : Attempt L E Input := do
  let sysroot ← requireEnv "LEAN_SYSROOT"
    "LEAN_SYSROOT is not set, so the toolchain of the build is not known: run the checker with \
      `lake lint` or `lake exe lint`, which set it"
  let dir ← realPath "."
  let root ← ExceptT.mk (Prog.bind (Prog.call (.loadWorkspace sysroot dir)) fun r =>
    pure (loaded "the workspace" r))
  let (_, lakeLib) ← (ExceptT.lift (Prog.call (.lakeInstall sysroot)) :
    Attempt L E (FilePath × FilePath))
  let received ← requireEnv "LEAN_PATH"
    "LEAN_PATH is not set, so the workspace that Lake dispatched is not known: run the checker with \
      `lake lint` or `lake exe lint`, which set it"
  if Regula.Load.dispatchedFrom root.rootLib.toString lakeLib.toString
      ((System.SearchPath.parse received).map toString) then
    inputOf root profile
  else
    throw "the current directory is not the workspace Lake dispatched; run `lake lint` from that \
      workspace's directory"

/-- The closed input of the finished build in the checker's tree, through the root package's load alone. The
full gate asks this only after the check admitted the project, so each `globs` entry is a single module and it
lists no directory. -/
def loadTree (sysroot : String) (tree : FilePath) (profile : Profile) : Attempt L E Input := do
  let dir ← realPath tree
  let root ← ExceptT.mk (Prog.bind (Prog.call (.loadRoot sysroot dir)) fun r =>
    pure (loaded "the configuration" r))
  inputOf root profile

/-- The rules on the finished build: prints what they found, and gives their verdict. -/
def rules (load : Attempt L E Input) : Prog L E Verdict := do
  let result ← load.run
  if let .ok input := result then say (coverage input)
  let r := decision result
  sayAll (details r)
  pure r.verdict

/-- What the language check says of a reading, printed. -/
def check (sysroot : String) (dir tree : FilePath) : Prog L E Language.Outcome := do
  match ← (read sysroot dir tree).run with
  | .error e =>
    say s!"RG2001: {e}"
    pure .incomplete
  | .ok (reading, lines) =>
    sayAll lines
    say s!"regula: the language check read {reading.files.length} files"
    pure (Language.decision reading)

/-- One Lake command in the checker's tree: whether it ended with 0. A command that could not start did not
end with 0. -/
def lake (program tree : FilePath) (args : List String) : Prog L E Bool := do
  say s!"regula: lake {" ".intercalate args}"
  let _ ← Prog.call (.flush)
  match ← (Prog.call (.runLake program tree args) : Prog L E (Except IO.Error UInt32)) with
  | .ok code => pure (code == 0)
  | .error e =>
    say s!"regula: lake could not start: {e}"
    pure false

/-- `lake build --wfail` and `lake check` in the checker's tree, with the Lake installed beside this Lean, so
that no `lean-toolchain` chooses anything. -/
def buildAndReplay (sysroot : String) (tree : FilePath) : Prog L E Bool := do
  let (program, _) ← (Prog.call (.lakeInstall sysroot) : Prog L E (FilePath × FilePath))
  if ← lake program tree ["build", "--wfail"] then
    lake program tree
      (if System.Platform.isOSX then ["check", "--inadvisably-no-sandbox"] else ["check"])
  else
    pure false

/-- The full gate in the tree, up to its report. -/
def gateIn (profile : Profile) (dir tree : FilePath) : Prog L E Language.Report := do
  match ← (Prog.call (.getEnv "LEAN_SYSROOT") : Prog L E (Option String)) with
  | none =>
    say "RG2001: LEAN_SYSROOT is not set, so the toolchain is not known"
    pure .incomplete
  | some sysroot =>
    Language.gate (check sysroot dir tree) (buildAndReplay sysroot tree)
      (rules (loadTree sysroot tree profile))

/-- The last line of a run, and its exit code. -/
def finish (text : String) (code : UInt32) : Prog L E UInt32 := do
  let _ ← Prog.call (.println text)
  pure code

/-- The end of a run of the full gate. -/
def finishFull (report : Language.Report) : Prog L E UInt32 :=
  finish report.label report.exitCode

/-- The end of a run of the proof verdict. -/
def finishProof (report : Report) : Prog L E UInt32 := do
  sayAll (details report)
  finish report.verdict.proofLine report.verdict.exitCode

/-- The full gate on the project at `dir`, in a new directory of the checker's own. It removes that directory
before it prints the last line, whatever the gate gave, and the verdict does not depend on the removal. Each run
makes a new directory, so one left by a crash or a failed removal can affect nothing later. -/
def runFull (profile : Profile) (dir : FilePath) : Prog L E UInt32 := do
  match ← (Prog.call .createTempDir : Prog L E (Except IO.Error FilePath)) with
  | .error e =>
    say s!"RG2001: the checker could not make its tree: {e}"
    finishFull .incomplete
  | .ok tree =>
    let report ← gateIn profile dir tree
    match ← (Prog.call (.removeDirAll tree) : Prog L E (Except IO.Error Unit)) with
    | .ok _ => finishFull report
    | .error e =>
      say s!"regula: the checker could not remove its tree {tree}: {e}"
      finishFull report

/-- A run of the proof verdict on the workspace that Lake dispatched. -/
def runPlain (profile : Profile) : Prog L E UInt32 := do
  let result ← (loadPlain profile).run
  if let .ok input := result then say (coverage input)
  finishProof (decision result)

/-- The checker with the arguments of `lake lint` (`profileOfRun`), giving the verdict of `decision`; or, with a
profile, `full` and a directory, the full gate on the project there. -/
def run (args : List String) : Prog L E UInt32 := do
  let (version, commit) ← (Prog.call .leanVersion : Prog L E (String × String))
  let (profileArgs, project) := match args with
    | [text, "full", dir] => ([text], some dir)
    | _ => (args, none)
  match profileOfRun version commit profileArgs, project with
  | .error why, _ => finishProof (.incomplete why)
  | .ok profile, some dir => runFull profile (FilePath.mk dir)
  | .ok profile, none => runPlain profile

end Regula.Shell
