import Lake
open Lake DSL

-- Execute the same source guard used by compiled policy. A fresh dependency has no Regula
-- artifacts yet; this module imports only Init and checks the running compiler's full identity.
run_cmd do
  let checked ← IO.Process.output {
    cmd := ((← Lean.findSysroot) / "bin" / "lean").toString
    args := #[(__dir__ / "lean/RegulaPolicy/Compiler.lean").toString] }
  unless checked.exitCode == 0 do
    Lean.logError m!"{checked.stdout}{checked.stderr}"

-- The package adopters require: the checker, lint driver, `regula` CLI, rule registry and
-- editor linter, with no dependency beyond the Lean toolchain. Everything that imports Mathlib
-- (the standard's Mathlib examples) is the separate `regula_audit` package in `audit/`.
package «regula» where
  -- Dependency planning builds its own tool before setup, without warming acceptance builds.
  buildDir := if (get_config? dependencyPlanner).isSome then
    ".lake/dependency-planner" else ".lake/build"
  -- Regula's semantic version: the latest release's, which only the release pull request
  -- changes and CI checks against `Regula.releases` (docs/guides/contributing.md#release). Each
  -- release is tagged `v<version>`. The first release, tagged `v4.34.0` for its Lean release,
  -- declares no version, which Lake reads as this `0.0.0`.
  version := v!"0.4.2"
  -- Reservoir (https://reservoir.lean-lang.org) lists these, and each release tag with the version
  -- its lakefile declares.
  description := "A strict linter for Lean: no holes, no hidden axioms, no unstated trust, and a \
    fix for every finding."
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

@[default_target]
lean_lib «RegulaVerification»

-- Toolchain-only local provisioning of the shared, read-only Mathlib; `scripts/provision.sh`
-- runs it with `lean --run` (`scripts/verify.sh` before its deadline), so it imports no
-- root-package module.
@[default_target]
lean_lib «RegulaProvision»

@[default_target]
lean_lib «RegulaCompiler»

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
  needs := #[`@/compilerObservationSource]

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

lean_exe «toolchain» where
  root := `Regula.Toolchain
  needs := #[`@/compilerObservationSource]

lean_exe «dependencyScope» where
  root := `Regula.DependencyScope
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
