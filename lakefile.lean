import Lake

-- A copy of `findSysroot` from `lean/Regula/CompilerObservation.lean`, which finds the toolchain as
-- `Lean.findSysroot` does but reads the prefix that `lean --print-prefix` prints exactly, where
-- `Lean.findSysroot` removes the whitespace at its ends. This file cannot import Regula, so the
-- copy has the same names. `Regula.PrintedPathControls.lakefileCopies` elaborates this part of the
-- file again and fails unless the kernel admits that each function equals Regula's by `rfl`. It
-- must stay first in the file.
namespace Regula.CompilerObservation

/-- `Regula.CompilerObservation.printedLine?`. -/
def printedLine? (text : String) : Option String :=
  match text.toList.reverse with
  | '\n' :: reversed =>
    if reversed ≠ [] ∧ ∀ c ∈ reversed, c ≠ '\n' ∧ c ≠ '\r' ∧ c ≠ '\x00' then
      some (String.ofList reversed.reverse)
    else none
  | _ => none

/-- `Regula.CompilerObservation.printedPrefix?`. -/
def printedPrefix? (text : String) : Option System.FilePath :=
  match printedLine? text with
  | some line => if (System.FilePath.mk line).isAbsolute then some ⟨line⟩ else none
  | none => none

/-- `Regula.CompilerObservation.printedSysroot`. -/
def printedSysroot (lean : String) : IO System.FilePath := do
  let out ← IO.Process.run { cmd := lean, args := #["--print-prefix"] }
  let some root := printedPrefix? out
    | throw <| IO.userError s!"{lean} --print-prefix printed {out.quote}, not one absolute path"
  return root

/-- `Regula.CompilerObservation.findSysroot`. -/
def findSysroot : IO System.FilePath := do
  if let some root ← IO.getEnv "LEAN_SYSROOT" then return root
  printedSysroot "lean"

end Regula.CompilerObservation

open Lake DSL

-- Execute the same source guard used by compiled policy. A fresh dependency has no Regula
-- artifacts yet, so a child `lean` elaborates the policy source, which imports only Init, checks
-- that child's own identity and, asked by `REGULA_COMPILER_GUARD`, prints it. `LEAN_SYSROOT` or
-- `PATH` selects the child, so the guard passes only when the child accepts itself and reports
-- the version and commit of the Lean elaborating this file. Any other child is refused.
run_cmd do
  let running := s!"{Lean.versionString}\n{Lean.githash}\n"
  let refusal : IO (Option String) := do
    let lean := ((← Regula.CompilerObservation.findSysroot) / "bin" / "lean").toString
    let child ← IO.Process.output {
      cmd := lean, args := #[(__dir__ / "lean/RegulaPolicy/Compiler.lean").toString]
      env := #[("REGULA_COMPILER_GUARD", some "1"), ("GHCR_TOKEN", none)] }
    if child.exitCode != 0 then
      return some s!"Regula's compiler guard stopped: Lake is running Lean \
        {Lean.versionString} ({Lean.githash}), and `{lean}`, which LEAN_SYSROOT or PATH selects, \
        refused Regula's compiler policy or could not compile it. Use a Lean release this \
        Regula revision supports, or a Regula revision qualified for this exact compiler: \
        https://github.com/rbeauchamp/regula/blob/main/docs/guides/adoption.md\
        #when-your-lean-release-has-no-regula-release\n{child.stdout}{child.stderr}"
    if child.stdout.replace "\r" "" == running then return none
    return some s!"Regula's compiler guard stopped: `{lean}`, which LEAN_SYSROOT or PATH \
      selects, is not the Lean running Lake, {Lean.versionString} ({Lean.githash}), so Regula's \
      compiler policy was not checked on that Lean. Run Lake without the LEAN_SYSROOT or PATH \
      of another toolchain. It reports:\n{child.stdout}{child.stderr}"
  match ← refusal.toBaseIO with
  | .ok none => pure ()
  | .ok (some refused) => Lean.logError refused
  | .error error => Lean.logError s!"Regula's compiler guard stopped: it cannot run the `lean` \
      that LEAN_SYSROOT or PATH selects to check the Lean running Lake, {Lean.versionString} \
      ({Lean.githash}): {error}"

-- The package adopters require: the checker, lint driver, `regula` CLI, rule registry and
-- editor linter, with no dependency beyond the Lean toolchain. The standard's example library is
-- the separate `regula_audit` package in `audit/`, which also imports only Lean's core libraries;
-- everything that imports Mathlib is the Mathlib integration package in `integration/mathlib/`.
package «regula» where
  -- Regula's semantic version: the latest release's, which only the release pull request
  -- changes and CI checks against `Regula.releases` (docs/guides/contributing.md#release). Each
  -- release is tagged `v<version>`. The first release, tagged `v4.34.0` for its Lean release,
  -- declares no version, which Lake reads as this `0.0.0`.
  version := v!"0.11.1"
  -- Reservoir (https://reservoir.lean-lang.org) lists these, and each release tag with the version
  -- its lakefile declares.
  description := "A strict linter for Lean. Regula refuses proof holes, project axioms and proofs \
    that trust the compiler. Each finding gives a fix."
  keywords := #["linter", "devtool", "cli", "formal-verification", "software-verification"]
  homepage := "https://rbeauchamp.github.io/regula/"
  license := "MIT AND Apache-2.0"
  licenseFiles := #["LICENSE", "LICENSES/Apache-2.0.txt"]
  lintDriver := "regula/lint"
  srcDir := "lean"
  -- The verification toolset for Regula (see docs/).
  -- Code here exists to machine-check claims, patterns, and examples from the standard.
  -- Build warnings are failures. No automatic implicits: every binder of an elaborated
  -- statement is written in its source (standard §7.1, RG2006). Every public definition has a
  -- docstring (standard §6.7, RG2006).
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩, ⟨`linter.missingDocs, true⟩]

-- Every target of this package but the observer's own library loads Regula's elaboration
-- observer (the `RegulaObserver` library below) into the elaboration of its modules through Lake's
-- own `plugins` setting, which Lake's `presetup` facet fetches, passes to `lean --plugin` and mixes
-- into each module's trace. `@/` names this package whether it is the root or a dependency, so an
-- adopter that requires it builds its modules as this checkout does. Each target also lists the
-- same key in `needs`: Lake v4.34.1 can build a `plugins` key several times at once in a fresh
-- build (`Lake/Build/Target/Fetch.lean` lines 54 to 66), and it builds a target's `needs` before
-- its modules fetch their plugins (`Lake/Build/Module.lean` lines 546 to 557, lean4#13598), so the
-- observer is built once, and mixes the trace of the `needs` into each module's trace whatever the
-- target's `platformIndependent`, so a replayed module was elaborated with the observer the build
-- has. An adopter's claimed targets load the observer the same way, as
-- `@regula/RegulaObserver:shared` in both settings; RG2006 requires both entries.
@[default_target]
lean_lib «AuditApp» where
  plugins := #[`@/RegulaObserver:shared]
  needs := #[`@/RegulaObserver:shared]
  -- The complete-application dogfooding surface: a bounded-slot limiter whose
  -- admission, update, and composition contracts are proved about the same
  -- computable definitions the `auditApp` executable runs. Core-only.
  globs := #[.andSubmodules `AuditApp]

lean_lib «Fixtures» where
  plugins := #[`@/RegulaObserver:shared]
  needs := #[`@/RegulaObserver:shared]
  -- Queryable exact inventory for isolated controls and mutations. This is
  -- deliberately not a default target: many modules are meant not to build.
  globs := #[.submodules `Fixtures]
  -- Unclaimed controls whose source is their test input: documenting them would change the
  -- inputs, so only this library turns the package's docstring linter off.
  leanOptions := #[⟨`linter.missingDocs, false⟩]

@[default_target]
lean_lib «RegulaPolicy» where
  plugins := #[`@/RegulaObserver:shared]
  needs := #[`@/RegulaObserver:shared]
  globs := #[.andSubmodules `RegulaPolicy]

-- The two standalone programs run with `lean --run` before the package is built
-- (`scripts/verify.sh` and `scripts/provision.sh`), so each root module imports only the toolchain. Each library has a second module,
-- `Decisions`, which imports its program with `Regula.Contract` and `Regula.Decision` and
-- registers the program's decisions (RG1008); no program imports it.
@[default_target]
lean_lib «RegulaVerification» where
  plugins := #[`@/RegulaObserver:shared]
  needs := #[`@/copyConstructionSource, `@/RegulaObserver:shared]
  globs := #[.andSubmodules `RegulaVerification]

-- Dependency setup.
@[default_target]
lean_lib «RegulaProvision» where
  plugins := #[`@/RegulaObserver:shared]
  needs := #[`@/copyConstructionSource, `@/RegulaObserver:shared]
  globs := #[.andSubmodules `RegulaProvision]

@[default_target]
lean_lib «RegulaQualification» where
  plugins := #[`@/RegulaObserver:shared]
  needs := #[`@/RegulaObserver:shared]
  -- Pure, proof-backed observation contracts; no process or filesystem drivers.
  globs := #[.submodules `RegulaQualification]

-- The checked rule-example corpus. `RegulaCore.Rule` embeds each rule's compliant and
-- noncompliant example files, so `RegulaCore` needs this directory as a traced input.
input_dir ruleExampleSources where
  path := "examples/rules"
  text := true

-- The standalone compiler probe embeds this source with include_str.
input_file compilerObservationSource where
  path := "lean/Regula/CompilerObservation.lean"
  text := true

-- Cold drivers interpret this shared source before package artifacts exist.
input_file copyConstructionSource where
  path := "lean/RegulaCore/CopyProgram.lean"
  text := true

-- `Regula.AbsenceControls` embeds this fixture with include_str and runs it.
input_file absenceReadsFixture where
  path := "examples/fixtures/absence-reads/AbsenceReads/Refused.lean"
  text := true

@[default_target]
lean_lib «RegulaCore» where
  plugins := #[`@/RegulaObserver:shared]
  -- The rule registry and the pure checker projections of policy decisions that the
  -- operational checker executes; claimed, so the gate audits their declarations.
  globs := #[.submodules `RegulaCore]
  needs := #[`@/ruleExampleSources, `@/RegulaObserver:shared]

lean_lib «Regula» where
  plugins := #[`@/RegulaObserver:shared]
  -- Lean-only checker implementation. Operational checker modules are
  -- separately qualified; they are not part of the conforming proof surface.
  globs := #[.submodules `Regula]
  -- The observer's shared library, listed as in every target here, is also the one that
  -- `axiomGate --file` loads as a plugin into its standalone compilation.
  needs := #[`@/compilerObservationSource, `@/RegulaObserver:shared, `@/absenceReadsFixture]

lean_exe «axiomGate» where
  plugins := #[`@/RegulaObserver:shared]
  needs := #[`@/RegulaObserver:shared]
  root := `Regula.Checker.AxiomGateMain
  supportInterpreter := true

lean_exe «lint» where
  plugins := #[`@/RegulaObserver:shared]
  needs := #[`@/RegulaObserver:shared]
  -- Lake lint driver: `lintDriver = "regula/lint"` in an adopting package and in this one.
  root := `Regula.Checker.LintMain
  supportInterpreter := true

lean_exe «docFenceAudit» where
  plugins := #[`@/RegulaObserver:shared]
  needs := #[`@/RegulaObserver:shared]
  root := `Regula.Checker.DocFenceAudit
  supportInterpreter := true

lean_exe «freshChecker» where
  plugins := #[`@/RegulaObserver:shared]
  needs := #[`@/RegulaObserver:shared]
  root := `Regula.Checker.FreshChecker
  supportInterpreter := true

lean_exe «checkerSelftest» where
  plugins := #[`@/RegulaObserver:shared]
  needs := #[`@/RegulaObserver:shared]
  root := `Regula.Checker.CheckerSelftest
  supportInterpreter := true

lean_exe «qualify» where
  plugins := #[`@/RegulaObserver:shared]
  needs := #[`@/RegulaObserver:shared]
  root := `Regula.Qualification.Main
  supportInterpreter := true

lean_exe «ruleExamples» where
  plugins := #[`@/RegulaObserver:shared]
  needs := #[`@/RegulaObserver:shared]
  root := `Regula.Checker.RuleExamples
  supportInterpreter := true

lean_exe «ruleExampleQualification» where
  plugins := #[`@/RegulaObserver:shared]
  needs := #[`@/RegulaObserver:shared]
  root := `Regula.Checker.RuleExampleQualificationMain

lean_exe «regula» where
  plugins := #[`@/RegulaObserver:shared]
  needs := #[`@/RegulaObserver:shared]
  -- Project setup (`init`, `doctor`) and offline rule guidance (`explain <RULE-ID>`, `rules`,
  -- `agent-guide`, `skill`). Loading an adopter's `lakefile.lean` needs the interpreter.
  root := `Regula.Cli.Main
  supportInterpreter := true

lean_exe «site» where
  plugins := #[`@/RegulaObserver:shared]
  needs := #[`@/RegulaObserver:shared]
  -- Rule-reference site builder: generates, renders, assembles and checks the Pages artifact.
  root := `Regula.Site.Main
  supportInterpreter := true

lean_exe «auditApp» where
  plugins := #[`@/RegulaObserver:shared]
  needs := #[`@/RegulaObserver:shared]
  root := `Main
  supportInterpreter := true

-- Regula's weak-arguments record. Lake's module trace omits a library's `weakLeanArgs`, so a
-- module replayed from a build under weak arguments since removed would reproduce messages of
-- that build. The facet below wraps Lake's own `extraDep` facet and, for libraries of the root
-- package and of the package that declares it (Lake's own identity of each: `Package.isRoot`, and
-- the package key `__name__` that Lake gives this file in the workspace), mixes into the trace a
-- caption that records the library's identity and its `weakLeanArgs`. A change of those arguments
-- then rebuilds the library's modules, and the audit decides a replayed module from the record of
-- its own library (`Regula.Checker.Lake.traceRecords_ownRecord_iff`). Regula's own modules get
-- the record whether Regula is the root or a dependency, so the two share one build. Other
-- dependencies' traces stay unchanged. A dependency resolved after this package that declares an
-- `extraDep` facet replaces this one: Lake resolves a package's `require` lines from the last to
-- the first, then their dependencies. The audit counts no record when a dependency declares
-- a library or module facet.

/-- The record of the weak arguments `args` of the library `libraryName` of the package
`packageName`, each name written by its components, so that distinct names give distinct records.
This file cannot import Regula's modules, since Lake loads the configuration of a fresh dependency
before it builds any of its modules, so this is a copy of `Regula.Checker.Lake.weakArgsRecordJson`,
whose records are proved injective, and must equal it. Acceptance has the kernel admit this
compiled declaration as equal to it (`Regula.Checker.Lake.lakefileEncoderAgrees`). -/
def weakLeanArgsRecord (packageName libraryName : Lean.Name) (args : Array String) : Lean.Json :=
  let component := fun (component : Lean.Name) =>
    if component.isNum then Lean.Json.arr #[.str (component.toString (escape := false))]
    else Lean.Json.str component.getString!
  let name := fun (name : Lean.Name) => Lean.Json.arr (name.components.map component).toArray
  Lean.Json.arr #[.str "weakLeanArgs", name packageName, name libraryName,
    .arr (args.map .str)]

@[«library_facet»] def weakLeanArgsTrace : LibraryFacetDecl :=
  .mk LeanLib.extraDepFacet <| mkFacetJobConfig fun library => do
    let job ← LeanLib.extraDepFacetConfig.run library
    unless library.pkg.isRoot || library.pkg.keyName == __name__ do return job
    let record :=
      (weakLeanArgsRecord library.pkg.baseName library.name library.weakLeanArgs).compress
    return job.mix <| Job.ofTask <| .pure <| .ok () {
      trace := BuildTrace.ofHash (pureHash record) record }

-- End of Regula's weak-arguments record.

-- Regula's elaboration observer: a Lean plugin that records in each module's `.olean` what a
-- build's messages do not show (the options its source set, `#guard_msgs` and `#guard_panic`,
-- silent messages), from which the audit decides RG2003 and RG2006. Its one root module and the
-- default library name make it a plugin that Lean can load (`LeanLib.isPlugin`). It imports only
-- Lean, so no module of it is elaborated with it.
lean_lib «RegulaObserver» where
  globs := #[.andSubmodules `RegulaObserver]
