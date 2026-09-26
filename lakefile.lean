import Lake
open Lake DSL

package «regula» where
  lintDriver := "regula/lint"
  srcDir := "lean"
  -- The verification toolset for Regula (see docs/).
  -- Code here exists to machine-check claims, patterns, and examples from the standard.
  leanOptions := #[⟨`warningAsError, true⟩]  -- Build warnings are failures

@[default_target]
lean_lib «Audit» where
  -- The claimed surface is every module at or below `Audit`, not only the
  -- transitive imports of the umbrella module. Lake's elaborated module
  -- inventory is the semantic inventory consumed by the declaration gate.
  globs := #[.andSubmodules `Audit]

@[default_target]
lean_lib «AuditApp» where
  -- The complete-application dogfooding surface: a bounded-slot limiter whose
  -- admission, update, and composition contracts are proved about the same
  -- computable definitions the `auditApp` executable runs.
  globs := #[.andSubmodules `AuditApp]

lean_lib «Fixtures» where
  -- Queryable exact inventory for isolated controls and mutations. This is
  -- deliberately not a default target: many modules are meant not to build.
  globs := #[.submodules `Fixtures]

@[default_target]
lean_lib «RegulaPolicy» where
  globs := #[.andSubmodules `RegulaPolicy]

@[default_target]
lean_lib «RegulaVerification»

-- Toolchain-only local provisioning of the shared, read-only Mathlib; `scripts/verify.sh`
-- runs it with `lean --run` before its deadline, so it imports no root-package module.
@[default_target]
lean_lib «RegulaProvision»

@[default_target]
lean_lib «RegulaQualification» where
  -- Pure, proof-backed observation contracts; no process or filesystem drivers.
  globs := #[.submodules `RegulaQualification]

-- The checked rule-example corpus. `RegulaCore.Rule` embeds each rule's compliant and
-- noncompliant example files, so `RegulaCore` needs this directory as a traced input.
input_dir ruleExampleSources where
  path := "examples/rules"
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

lean_exe «intentScreen» where
  -- Opt-in probabilistic intent screen (docs/guides/intent-screening.md). Never part of
  -- offline acceptance; it calls a network service only when explicitly run.
  root := `Regula.Screen.Main
  supportInterpreter := true

lean_exe «regula» where
  -- Offline rule guidance: `explain <RULE-ID>`, `rules`, `agent-guide`, `skill`.
  root := `Regula.Cli.Main

lean_exe «site» where
  -- Rule-reference site builder: generates, renders, assembles and checks the Pages artifact.
  root := `Regula.Site.Main
  supportInterpreter := true

lean_exe «auditApp» where
  root := `Main
  supportInterpreter := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "5ed2965256430c3649e86755f9576b54eca72435"
