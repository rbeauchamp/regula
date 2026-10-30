import Lake
open Lake DSL

-- Execute the same source guard used by compiled policy. A fresh dependency has no Regula
-- artifacts yet, so a child `lean` elaborates the policy source, which imports only Init, checks
-- that child's own identity and, asked by `REGULA_COMPILER_GUARD`, prints it. `LEAN_SYSROOT` or
-- `PATH` selects the child, so the guard passes only when the child accepts itself and reports
-- the version and commit of the Lean elaborating this file. Any other child is refused.
--
-- When `LEAN_SYSROOT` is not set, the child's path comes from `Lean.findSysroot`, which removes the
-- whitespace at the ends of the prefix that `lean --print-prefix` prints
-- (`Lean/Util/Path.lean:180-187` of Lean v4.35.0). For an installation directory whose name ends
-- in a space, it names another directory. That cannot cause a wrong acceptance. The guard accepts
-- only a child that exits with 0, which the policy source does only after
-- `RegulaPolicy.Compiler.checkCurrent` accepts the child's own version and commit. It also
-- requires the child to print exactly the version and commit of the Lean running Lake. So whatever
-- program that path names, an acceptance means that the Lean running Lake has the supported
-- identity, on the child's report of its own identity, which the guard trusts at any path.
run_cmd do
  let running := s!"{Lean.versionString}\n{Lean.githash}\n"
  let refusal : IO (Option String) := do
    let lean := ((← Lean.findSysroot) / "bin" / "lean").toString
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
    that trust the compiler. Each finding links to its rule page, which gives the fix."
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

@[default_target]
lean_lib «RegulaPolicy» where
  globs := #[.submodules `RegulaPolicy]

-- The two standalone programs run with `lean --run` before the package is built
-- (`scripts/verify.sh` and `scripts/provision.sh`), so each root module imports only the toolchain. Each library has a second module,
-- `Decisions`, which imports its program with `Regula.Contract` and `Regula.Decision` and
-- registers the program's decisions (RG1008); no program imports it.
@[default_target]
lean_lib «RegulaVerification» where
  needs := #[`@/copyConstructionSource]
  globs := #[.andSubmodules `RegulaVerification]

-- Dependency setup.
@[default_target]
lean_lib «RegulaProvision» where
  needs := #[`@/copyConstructionSource]
  globs := #[.andSubmodules `RegulaProvision]

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
  -- The rule registry and the pure checker projections of policy decisions that the
  -- operational checker executes; claimed, so the gate audits their declarations.
  globs := #[.submodules `RegulaCore]
  needs := #[`@/ruleExampleSources]

-- The published checker interfaces that claimed modules and adopters import: executable
-- contracts (`Regula.Contract`), decision registration (`Regula.Decision`), material claims
-- (`Regula.MaterialClaim`) and assumptions (`Regula.Assumption`). They are claimed, so a claimed
-- module that imports them imports no module of an excluded target (RG2004).
@[default_target]
lean_lib «RegulaInterface» where
  globs := #[.one `Regula.Contract, .one `Regula.Decision, .one `Regula.MaterialClaim,
    .one `Regula.Assumption]

lean_lib «Regula» where
  -- Regula's checker (the closed input, its loader, the rules and the shell), its manifest reader,
  -- the `regula` command, the site builder and the repository's own programs. The interfaces are
  -- the library `RegulaInterface`, so each module is in exactly one library (RG2004).
  globs := #[.submodules `Regula.Checker, .submodules `Regula.Cli, .submodules `Regula.Site,
    .one `Regula.AbsenceControls, .one `Regula.CompilerObservation, .one `Regula.CompilerProbe,
    .one `Regula.CopyControls, .one `Regula.Destination, .one `Regula.DiagnosticsGate,
    .one `Regula.Filesystem, .one `Regula.GitIsolation, .one `Regula.Input, .one `Regula.LintMain,
    .one `Regula.Load, .one `Regula.PrintedPathControls, .one `Regula.ProvisionControls,
    .one `Regula.RegistryChecks, .one `Regula.Release, .one `Regula.Removal,
    .one `Regula.RemovalControls, .one `Regula.Rules, .one `Regula.Scratch, .one `Regula.Shell,
    .one `Regula.TaskManager, .one `Regula.TaskManagerCheck, .one `Regula.TestListing,
    .one `Regula.ProgramCheck.DiagnosticsGate, .one `Regula.ProgramCheck.Provision,
    .one `Regula.ProgramCheck.RegistryChecks, .one `Regula.ProgramCheck.Release,
    .one `Regula.ProgramCheck.SiteDeployment, .one `Regula.ProgramCheck.TestListing,
    .one `Regula.ProgramCheck.Verification]
  needs := #[`@/compilerObservationSource, `@/absenceReadsFixture]

lean_exe «lint» where
  -- Lake lint driver: `lintDriver = "regula/lint"` in an adopting package and in this one.
  root := `Regula.LintMain
  supportInterpreter := true

lean_exe «regula» where
  -- Project setup (`init`, `doctor`) and offline rule guidance (`explain <RULE-ID>`, `rules`,
  -- `agent-guide`, `skill`). Loading an adopter's `lakefile.lean` needs the interpreter.
  root := `Regula.Cli.Main
  supportInterpreter := true

lean_exe «site» where
  -- Rule-reference site builder: generates, renders, assembles and checks the Pages artifact.
  root := `Regula.Site.Main
  supportInterpreter := true

@[default_target]
lean_exe «auditApp» where
  root := `Main
  supportInterpreter := true
