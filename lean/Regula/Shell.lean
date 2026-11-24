module

public import Regula.Reader
public import Regula.Rules

public section

namespace Regula.Shell

open Lean (Name)
open System (FilePath)
open Regula.Closed
open Regula.Effect
open Regula.Reader

variable {L E : Type}

def supportsLean (version commit : String) : Bool :=
  (version, commit) == pinnedLean

def line (f : Finding) : String :=
  match f.subject with
  | .constant name m => s!"{f.rule} {name} (module {m}): {f.detail}"
  | .module name => s!"{f.rule} {name}: {f.detail}"

def guidanceLine (f : Finding) : String :=
  "fix: " ++ f.guidance.text

def findingLines (f : Finding) : List String :=
  [line f, guidanceLine f]

def details : Report → List String
  | .pass => []
  | .fail first rest =>
    (first :: rest).flatMap findingLines ++ [s!"{rest.length + 1} findings"]
  | .incomplete why => [s!"RG2001: {why}"]

def coverage (i : Input) : String :=
  s!"regula: read {i.modules.length} claimed modules and {i.claimedDecls.length} of their constants"

def profileSpellings : String :=
  ", ".intercalate (Profile.all.map (·.spelling))

abbrev fullVariable : String := "REGULA_FULL"

abbrev proofVariable : String := "REGULA_PROOF"

def profileOfRun (version commit : String) (args : List String) : Except String Profile :=
  if !supportsLean version commit then
    .error s!"this revision of Regula reads only Lean 4.36.0, and this is Lean {version} ({commit})"
  else
    match args with
    | [text] =>
      match Profile.ofSpelling? text with
      | some profile => .ok profile
      | none => .error s!"{text} is no profile: {profileSpellings}"
    | _ =>
      .error s!"state one profile in `lintDriverArgs`: {profileSpellings}. No argument names a project: for a full \
        verdict, from a checkout of Regula, run `{fullVariable}=DIR lake exe lint PROFILE`, or for a proof verdict \
        on a zero-dependency `lakefile.toml` package, `{proofVariable}=DIR lake exe lint PROFILE`"

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

def factsOf (env : Lean.Environment) (path : List FilePath) (toolchainDir rootDir : FilePath) : Attempt L E Regula.Load.Facts := do
  let ⟨ms, hn, hp⟩ ← readModules path toolchainDir rootDir env.header.moduleNames.toList
  pure { env, toolchainDir, rootDir, modules := ms.toArray, names := by simpa using hn,
         placed := by simpa using hp }

def replayed (f : Regula.Load.Facts) (p : Prepared) : Attempt L E Prepared :=
  ExceptT.mk do
    match ← (Prog.call (.kernelReplay (f.replayConstants p.input)) : Prog L E (Except IO.Error Unit)) with
    | .ok _ => pure (.ok p)
    | .error e => pure (.error s!"Lean's kernel did not accept the replay of the claim's cone: {e}")

def inputOf (root : Root L) (profile : Profile) : Attempt L E Prepared := do
  let modules ← defaultModules root root.defaultTargets
  let roots := modules.map (·.1)
  let env ← attempt (Prog.call (.importForRules root.leanPath roots.toArray))
  let f ← factsOf env root.leanPath root.leanLib root.rootLib
  let p ← ExceptT.mk (pure (f.prepare roots profile))
  replayed f p

def loadPlain (profile : Profile) : Attempt L E (FilePath × Prepared) := do
  let sysroot ← requireEnv "LEAN_SYSROOT"
    "LEAN_SYSROOT is not set, so the toolchain of the build is not known: run the checker with \
      `lake lint` or `lake exe lint`, which set it"
  let dir ← realPath "."
  let root ← ExceptT.mk (Prog.bind (Prog.call (.loadWorkspace sysroot dir)) fun r =>
    pure (loaded "the workspace" r))
  let received ← requireEnv "LEAN_PATH"
    "LEAN_PATH is not set, so this run did not get Lake's search path: run the checker with \
      `lake lint` or `lake exe lint`, which set it"
  if Regula.Load.startsSearchPath (root.leanPath.map toString) ((System.SearchPath.parse received).map toString) then
    let prepared ← inputOf root profile
    pure (dir, prepared)
  else
    throw "Lake's search path does not start with that of the workspace in the current directory, so this may be another workspace: run \
      `lake lint` from the directory of the workspace to check"

def loadTree (sysroot : String) (tree : FilePath) (profile : Profile) : Attempt L E Prepared := do
  let dir ← realPath tree
  let root ← ExceptT.mk (Prog.bind (Prog.call (.loadRoot sysroot dir)) fun r =>
    pure (loaded "the configuration" r))
  inputOf root profile

def loadProof (target : FilePath) (profile : Profile) : Attempt L E (FilePath × Prepared) := do
  if target.toString.isEmpty then
    throw s!"{proofVariable} is empty, so no project directory was named"
  else
    let sysroot ← requireEnv "LEAN_SYSROOT"
      "LEAN_SYSROOT is not set, so the toolchain of the build is not known: run the checker with \
        `lake lint` or `lake exe lint`, which set it"
    let dir ← realPath target
    let shadowed ← existsByName (dir / "lakefile.lean")
    if shadowed then
      throw "something answers to `lakefile.lean` in the target directory, and out-of-tree proof mode reads only \
        `lakefile.toml`: remove `lakefile.lean` or run `lake lint` from that directory"
    else
      let root ← ExceptT.mk (Prog.bind (Prog.call (.loadRoot sysroot dir)) fun r =>
        pure (loaded "the configuration" r))
      if root.defaultTargets.isEmpty then
        throw "the package has no default library target to audit"
      else
        match root.defaultTargets.find? (fun target => (root.findLib target).isNone) with
        | some target =>
          throw s!"default target {target} is not a library: out-of-tree proof mode checks only library targets"
        | none =>
          let prepared ← inputOf root profile
          pure (dir, prepared)

def sayCoverage : Except String Prepared → Prog L E Unit
  | .ok prepared => say (coverage prepared.input)
  | .error _ => pure ()

def rules (load : Attempt L E Prepared) : Prog L E Verdict := do
  let result ← load.run
  sayCoverage result
  let report := decisionPrepared result
  sayAll (details report)
  pure report.verdict

def check (sysroot : String) (dir tree : FilePath) : Prog L E Language.Outcome := do
  match ← (read sysroot dir tree).run with
  | .error e =>
    say s!"RG2001: {e}"
    pure .incomplete
  | .ok (reading, lines) =>
    sayAll lines
    say s!"regula: the language check read {reading.files.length} files"
    pure (Language.decision reading)

def lake (program tree : FilePath) (args : List String) : Prog L E Bool := do
  say s!"regula: lake {" ".intercalate args}"
  let _ ← Prog.call (.flush)
  match ← (Prog.call (.runLake program tree args) : Prog L E (Except IO.Error UInt32)) with
  | .ok code => pure (code == 0)
  | .error e =>
    say s!"regula: lake could not start: {e}"
    pure false

def build (sysroot : String) (tree : FilePath) : Prog L E Bool := do
  let (program, _) ← (Prog.call (.lakeInstall sysroot) : Prog L E (FilePath × FilePath))
  lake program tree ["build", "--wfail"]

def gateIn (profile : Profile) (dir tree : FilePath) : Prog L E Language.Report := do
  match ← (Prog.call (.getEnv "LEAN_SYSROOT") : Prog L E (Option String)) with
  | none =>
    say "RG2001: LEAN_SYSROOT is not set, so the toolchain is not known"
    pure .incomplete
  | some sysroot =>
    Language.gate (check sysroot dir tree) (build sysroot tree)
      (rules (loadTree sysroot tree profile))

def finish (text : String) (code : UInt32) : Prog L E UInt32 := do
  let _ ← Prog.call (.println text)
  pure code

def finishFull (dir : FilePath) (report : Language.Report) : Prog L E UInt32 :=
  finish (report.labelOn dir.toString) report.exitCode

def finishProof (report : Report) : Prog L E UInt32 := do
  sayAll (details report)
  finish report.verdict.proofLine report.verdict.exitCode

def finishPlain (subject : FilePath) (report : Report) : Prog L E UInt32 := do
  sayAll (details report)
  finish (report.verdict.proofLineOn subject.toString) report.verdict.exitCode

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

def reportProof (load : Attempt L E (FilePath × Prepared)) : Prog L E UInt32 := do
  match ← load.run with
  | .error why => finishProof (decisionPrepared (.error why))
  | .ok (dir, prepared) =>
    say (coverage prepared.input)
    finishPlain dir (decisionPrepared (.ok prepared))

def runPlain (profile : Profile) : Prog L E UInt32 :=
  reportProof (loadPlain profile)

def runProof (profile : Profile) (target : FilePath) : Prog L E UInt32 :=
  reportProof (loadProof target profile)

def dispatch (version commit : String) (args : List String) : Prog L E UInt32 :=
  match profileOfRun version commit args with
  | .error why => finishProof (.incomplete why)
  | .ok profile =>
    Prog.bind (Prog.call (.getEnv fullVariable)) fun fullProject =>
      Prog.bind (Prog.call (.getEnv proofVariable)) fun proofProject =>
        match fullProject, proofProject with
        | some _, some _ =>
          finishProof (.incomplete s!"both {fullVariable} and {proofVariable} are set; set at most one")
        | some dir, none => runFull profile (FilePath.mk dir)
        | none, some dir => runProof profile (FilePath.mk dir)
        | none, none => runPlain profile

def run (args : List String) : Prog L E UInt32 :=
  Prog.bind (Prog.call .leanVersion : Prog L E (String × String)) fun v =>
    dispatch v.1 v.2 args

end Regula.Shell
