import Lake
open Lake DSL

package build_lint_adopter where
  -- `lake lint` runs the Regula driver over every manifested surface.
  lintDriver := "regula/lint"
  -- The community linters of standard §6.7 and the options of §7.1. A library that
  -- imports Mathlib also enables Mathlib's standard set, as the adoption guide shows.
  leanOptions := #[⟨`linter.missingDocs, true⟩, ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

require regula from "../.."

lean_lib Widget where
  -- Regula's elaboration observer records the options the source sets and the messages a build
  -- does not show (RG2003, RG2006); every claimed target loads it, and lists it in `needs` so that
  -- a fresh build builds it once.
  plugins := #[`@regula/RegulaObserver:shared]
  needs := #[`@regula/RegulaObserver:shared]
  globs := #[.andSubmodules `Widget]

/-- The sole default target: build the tool, then build and inspect every
manifested surface. The job deliberately has no cached success artifact. -/
@[default_target]
target policy pkg : Unit := do
  let some checkerPackage ← findPackageByName? `regula
    | error "build policy: missing regula dependency"
  let some checker := checkerPackage.findLeanExe? `axiomGate
    | error "build policy: missing axiomGate executable"
  let binary ← checker.fetch
  binary.mapM fun path => do
    let result ← IO.Process.output {
      cmd := path.toString
      args := #["--build-lint", "--project", pkg.dir.toString]
      cwd := some pkg.dir }
    if result.exitCode != 0 then error s!"{result.stdout}{result.stderr}"
    logInfo result.stdout
