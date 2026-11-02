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

A run with one profile and the variable `REGULA_FULL` set (`fullVariable`) is the full gate (`Regula.Language.gate`) on the
project at the directory the variable names: the language check, which writes the configuration to a tree of the checker's own and, once it has admitted the
project, what it judged of each file, then, for
an admitted project, the build and its replay in that tree and the same rules on it. Only that run can print a full
verdict, because only there the check came first. Starting the checker from its own package is a precondition of that verdict, which it does not test. A project with a dependency or with Mathlib in its imports gets no build from
it: it says that only a proof verdict is possible and exits with 3.

The arguments select no directory, because a project's Lake configuration sets them (`lintDriverArgs`), and `lakefile.toml`
has no key that sets a variable. So a project's `lake lint` gives a proof verdict about that project or a refusal, unless whoever ran it set the
variable, whose value then says what they asked about.

Each line but the last starts with two spaces (`Regula.Reader.say`). The exit code is a function of the verdict alone, and
so is the last line (`Regula.Closed.Verdict.proofLineOn`, `Regula.Language.Report.labelOn`), but for the path that a pass
names at its end.
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

/-- The variable that names the project of the full gate; `Regula.DiagnosticsGate` sets it for one step. A project's `lakefile.toml`
sets the arguments of its lint driver, and has no key that sets a variable: Lake gives a program what it inherited, with the fixed list of `Workspace.augmentedEnvVars`
(`Lake/Config/Workspace.lean:417-433`) over it. So this is what whoever started the run asked about. -/
abbrev fullVariable : String := "REGULA_FULL"

/-- The profile of a run of the Lean release `version` at `commit` with the arguments `args`, or why
the run is `incomplete`: any other release, and any argument list other than one profile. So no argument names a directory. -/
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
      .error s!"state one profile in `lintDriverArgs`: {profileSpellings}. No argument names a project: for a full \
        verdict, from a checkout of Regula, run `{fullVariable}=DIR lake exe lint PROFILE`"

/-- Each of the modules `names`, in that order, with where Lean finds its `.olean` on the search
path `path`. The result carries that it is these modules and what each place decides. -/
def readModules (path : List FilePath) (toolchainDir rootDir : FilePath) : (names : List Name) →
    Attempt L E { ms : List Regula.Load.LoadedModule // ms.map (·.name) = names ∧
      ∀ m ∈ ms, m = Regula.Load.LoadedModule.ofPlace toolchainDir rootDir m.name m.olean }
  | [] => pure ⟨[], rfl, by simp⟩
  | n :: rest => do
    let olean ← attempt (Prog.call (.findOLean path n))
    let ⟨ms, hn, hp⟩ ← readModules path toolchainDir rootDir rest
    pure ⟨Regula.Load.LoadedModule.ofPlace toolchainDir rootDir n olean :: ms,
      by simp [Regula.Load.LoadedModule.ofPlace_name, hn],
      by
        intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact Regula.Load.LoadedModule.ofPlace_self ..
        · exact hp m hm⟩

/-- The facts of `env`, from where the `.olean` of each of its modules lies. -/
def factsOf (env : Lean.Environment) (path : List FilePath) (toolchainDir rootDir : FilePath) : Attempt L E Regula.Load.Facts := do
  let ⟨ms, hn, hp⟩ ← readModules path toolchainDir rootDir env.header.moduleNames.toList
  pure { env, toolchainDir, rootDir, modules := ms.toArray, names := by simpa using hn,
         placed := by simpa using hp }

/-- The closed input of the finished build that the load `root` describes. -/
def inputOf (root : Root L) (profile : Profile) : Attempt L E Input := do
  let modules ← defaultModules root root.defaultTargets
  let roots := modules.map (·.1)
  let env ← attempt (Prog.call (.importForRules root.leanPath roots.toArray))
  let f ← factsOf env root.leanPath root.leanLib root.rootLib
  ExceptT.mk (pure (f.input roots profile))

/-- The closed input of the finished build of the workspace that Lake dispatched from the current directory, with that
directory.
-/
def loadPlain (profile : Profile) : Attempt L E (FilePath × Input) := do
  let sysroot ← requireEnv "LEAN_SYSROOT"
    "LEAN_SYSROOT is not set, so the toolchain of the build is not known: run the checker with \
      `lake lint` or `lake exe lint`, which set it"
  let dir ← realPath "."
  let root ← ExceptT.mk (Prog.bind (Prog.call (.loadWorkspace sysroot dir)) fun r =>
    pure (loaded "the workspace" r))
  let received ← requireEnv "LEAN_PATH"
    "LEAN_PATH is not set, so the workspace that Lake dispatched is not known: run the checker with \
      `lake lint` or `lake exe lint`, which set it"
  if Regula.Load.dispatchedFrom (root.leanPath.map toString) ((System.SearchPath.parse received).map toString) then
    let input ← inputOf root profile
    pure (dir, input)
  else
    throw "Lake's search path does not start with that of the workspace in the current directory, so this may be another workspace: run \
      `lake lint` from the directory of the workspace to check"

/-- The closed input of the finished build in the checker's tree, through the root package's load alone. The
full gate asks this only after the check admitted the project, so each `globs` entry is a single module and it
lists no directory. -/
def loadTree (sysroot : String) (tree : FilePath) (profile : Profile) : Attempt L E Input := do
  let dir ← realPath tree
  let root ← ExceptT.mk (Prog.bind (Prog.call (.loadRoot sysroot dir)) fun r =>
    pure (loaded "the configuration" r))
  inputOf root profile

/-- What a load read, printed. -/
def sayCoverage : Except String Input → Prog L E Unit
  | .ok input => say (coverage input)
  | .error _ => pure ()

/-- The rules on the finished build: prints what they found, and gives their verdict. -/
def rules (load : Attempt L E Input) : Prog L E Verdict := do
  let result ← load.run
  sayCoverage result
  sayAll (details (decision result))
  pure (decision result).verdict

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

/-- The end of a run of the full gate on the project at `dir`. -/
def finishFull (dir : FilePath) (report : Language.Report) : Prog L E UInt32 :=
  finish (report.labelOn dir.toString) report.exitCode

/-- The end of a run of the proof verdict that has no subject to name. -/
def finishProof (report : Report) : Prog L E UInt32 := do
  sayAll (details report)
  finish report.verdict.proofLine report.verdict.exitCode

/-- The end of a run of the proof verdict on the workspace at `subject`. -/
def finishPlain (subject : FilePath) (report : Report) : Prog L E UInt32 := do
  sayAll (details report)
  finish (report.verdict.proofLineOn subject.toString) report.verdict.exitCode

/-- The full gate on the project at `dir`, in a new directory of the checker's own. It removes that directory
before it prints the last line, whatever the gate gave, and the verdict does not depend on the removal. Each run
makes a new directory, so one left by a crash or a failed removal can affect nothing later. -/
def runFull (profile : Profile) (dir : FilePath) : Prog L E UInt32 := do
  match ← (Prog.call .createTempDir : Prog L E (Except IO.Error FilePath)) with
  | .error e =>
    say s!"RG2001: the checker could not make its tree: {e}"
    finishFull dir .incomplete
  | .ok tree =>
    let report ← gateIn profile dir tree
    match ← (Prog.call (.removeDirAll tree) : Prog L E (Except IO.Error Unit)) with
    | .ok _ => finishFull dir report
    | .error e =>
      say s!"regula: the checker could not remove its tree {tree}: {e}"
      finishFull dir report

/-- The directory that a load gave. A load that gave no input names none, and its verdict is no pass. -/
def subjectOf : Except String (FilePath × Input) → FilePath
  | .ok x => x.1
  | .error _ => "."

/-- A run of the proof verdict on the workspace that Lake dispatched. -/
def runPlain (profile : Profile) : Prog L E UInt32 := do
  let result ← (loadPlain profile).run
  let input := result.map (·.2)
  sayCoverage input
  finishPlain (subjectOf result) (decision input)

/-- What a run does on this Lean with these arguments: the profile, or a refusal, and then the variable says which run. -/
def dispatch (version commit : String) (args : List String) : Prog L E UInt32 :=
  match profileOfRun version commit args with
  | .error why => finishProof (.incomplete why)
  | .ok profile =>
    Prog.bind (Prog.call (.getEnv fullVariable)) fun project =>
      match project with
      | some dir => runFull profile (FilePath.mk dir)
      | none => runPlain profile

/-- The checker with the arguments of `lake lint` (`profileOfRun`), giving the verdict of `decision`; or, with `fullVariable`
set, the full gate on the project it names. -/
def run (args : List String) : Prog L E UInt32 :=
  Prog.bind (Prog.call .leanVersion : Prog L E (String × String)) fun v =>
    dispatch v.1 v.2 args

end Regula.Shell
