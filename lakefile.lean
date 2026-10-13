import Lake
import Lean.Elab.Frontend
open Lake DSL

namespace RegulaBootstrap
run_cmd do
  let input := Lean.Parser.mkInputContext (include_str "lean/Regula/ProcessSource.inc") "Regula/ProcessSource.inc"
  let result ← Lean.Elab.IO.processCommands input {} (← get)
  set result.commandState
end RegulaBootstrap

-- A fresh dependency has no Regula artifacts. The shared typed observer selects an installed
-- compiler without PATH and checks its identity, then that compiler elaborates the policy source
-- and reports its identity. Both the selected child and the Lean elaborating this file must agree.
run_cmd do
  let running := s!"{Lean.versionString}\n{Lean.githash}\n"
  let refusal : IO (Option String) := do
    let lean := (← RegulaBootstrap.toolPath .lean).toString
    let child ← RegulaBootstrap.output (.toolchain .lean) {
      cmd := lean, args := #[(__dir__ / "lean/RegulaPolicy/Compiler.lean").toString]
      env := #[("GHCR_TOKEN", none)] }
    if child.exitCode != 0 then
      return some s!"Regula's compiler guard stopped: Lake is running Lean \
        {Lean.versionString} ({Lean.githash}), and the selected installed `{lean}` \
        refused Regula's compiler policy or could not compile it. Use a Lean release this \
        Regula revision supports, or a Regula revision qualified for this exact compiler: \
        https://github.com/rbeauchamp/regula/blob/main/docs/guides/adoption.md\
        #when-your-lean-release-has-no-regula-release\n{child.stdout}{child.stderr}"
    if child.stdout.replace "\r" "" == running then return none
    return some s!"Regula's compiler guard stopped: the selected installed `{lean}` \
      is not the Lean running Lake, {Lean.versionString} ({Lean.githash}), so Regula's \
      compiler policy was not checked on that Lean. Select this compiler's installation with \
      LEAN_SYSROOT or ELAN_TOOLCHAIN. It reports:\n{child.stdout}{child.stderr}"
  match ← refusal.toBaseIO with
  | .ok none => pure ()
  | .ok (some refused) => Lean.logError refused
  | .error error => Lean.logError s!"Regula's compiler guard stopped: it cannot run the `lean` \
      selected from the installation to check the Lean running Lake, {Lean.versionString} \
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

@[default_target]
lean_lib «AuditApp» where
  -- The complete-application dogfooding surface: a bounded-slot limiter whose
  -- admission, update, and composition contracts are proved about the same
  -- computable definitions the `auditApp` executable runs. Core-only.
  globs := #[.andSubmodules `AuditApp]

lean_lib «Fixtures» where
  -- Queryable exact inventory for isolated controls and mutations. This is
  -- deliberately not a default target: many modules are meant not to build.
  globs := #[.submodules `Fixtures]
  -- Unclaimed controls whose source is their test input: documenting them would change the
  -- inputs, so only this library turns the package's docstring linter off.
  leanOptions := #[⟨`linter.missingDocs, false⟩]

@[default_target]
lean_lib «RegulaPolicy» where
  globs := #[.andSubmodules `RegulaPolicy]

-- The two standalone programs run with `lean --run` before the package is built
-- (`scripts/verify.sh` and `scripts/provision.sh`), so each root module imports only the toolchain. Each library has a second module,
-- `Decisions`, which imports its program with `Regula.Contract` and `Regula.Decision` and
-- registers the program's decisions (RG1008); no program imports it.
@[default_target]
lean_lib «RegulaVerification» where
  globs := #[.andSubmodules `RegulaVerification]
  needs := #[`@/processSource]

-- Dependency setup.
@[default_target]
lean_lib «RegulaProvision» where
  globs := #[.andSubmodules `RegulaProvision]
  needs := #[`@/processSource]

@[default_target]
lean_lib «RegulaQualification» where
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

-- Cold drivers and the installed observer elaborate the same policy source with Lean's frontend.
input_file processSource where
  path := "lean/Regula/ProcessSource.inc"
  text := true

-- The cold website build and compiled renderer include one selector admission implementation.
input_file rendererSelectionSource where
  path := "lean/Regula/RendererSelection.inc"
  text := true

input_file lakeBuildConfigSource where
  path := "lean/Regula/LakeBuildConfig.inc"
  text := true

-- External-boundary controls are committed Lean sources, embedded without generated layout.
input_dir processFixtureSources where
  path := "examples/process-controls"
  text := true

@[default_target]
lean_lib «RegulaCore» where
  -- The rule registry and the pure checker projections of policy decisions that the
  -- operational checker executes; claimed, so the gate audits their declarations.
  globs := #[.submodules `RegulaCore]
  needs := #[`@/ruleExampleSources]

lean_lib «Regula» where
  -- Lean-only checker implementation. Operational checker modules are
  -- separately qualified; they are not part of the conforming proof surface.
  globs := #[.submodules `Regula]
  needs := #[`@/compilerObservationSource, `@/processSource, `@/processFixtureSources,
    `@/rendererSelectionSource, `@/lakeBuildConfigSource]

lean_exe «axiomGate» where
  root := `Regula.Checker.AxiomGateMain
  supportInterpreter := true

lean_exe «lint» where
  -- Lake lint driver: `lintDriver = "regula/lint"` in an adopting package and in this one.
  root := `Regula.Checker.LintMain
  supportInterpreter := true

lean_exe «docFenceAudit» where
  root := `Regula.Checker.DocFenceAudit
  supportInterpreter := true

lean_exe «freshChecker» where
  root := `Regula.Checker.FreshChecker
  supportInterpreter := true

lean_exe «checkerSelftest» where
  root := `Regula.Checker.CheckerSelftest
  supportInterpreter := true

lean_exe «qualify» where
  root := `Regula.Qualification.Main
  supportInterpreter := true

lean_exe «ruleExamples» where
  root := `Regula.Checker.RuleExamples
  supportInterpreter := true

lean_exe «ruleExampleQualification» where
  root := `Regula.Checker.RuleExampleQualificationMain

lean_exe «regula» where
  -- Project setup (`init`, `doctor`) and offline rule guidance (`explain <RULE-ID>`, `rules`,
  -- `agent-guide`, `skill`). Loading an adopter's `lakefile.lean` needs the interpreter.
  root := `Regula.Cli.Main
  supportInterpreter := true

lean_exe «site» where
  -- Rule-reference site builder: generates, renders, assembles and checks the Pages artifact.
  root := `Regula.Site.Main
  supportInterpreter := true

lean_exe «auditApp» where
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
-- another library facet.

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
