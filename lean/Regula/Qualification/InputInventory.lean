import Regula.Qualification.DependencySnapshot

/-! # Input inventory fault injection

Root and Markdown inventory controls whose faults the checker's own in-process build injects:
the scratch project's claimed library has a Lake library facet as its only default facet, and
that facet changes an input when the build of the library begins. -/
namespace Regula.Qualification.InputInventory
open Lean System DependencySnapshot

/-- The scratch project's configuration. The library `Example`'s only default facet is
`inventoryFault`, which builds the library's Lean artifacts (`leanArts`, Lake's default facet) as
the default build does. When `INVENTORY_FAULT` names a fault and the file `INVENTORY_RECORD` is
absent, the facet first injects the fault: it writes the text of the file `INVENTORY_SOURCE` to
`INVENTORY_TARGET`, or removes `INVENTORY_TARGET` when `INVENTORY_SOURCE` is unset, and then
writes the record with the fault's name. Once the library's Lean artifacts are built, it writes
the record again with `buildSucceeded` and whether `Example.New` was built (`addedBuilt`).

Assumes:
- Lake `v4.34.1` fetches a library's default facets in their order
  (`LeanLib.recBuildDefaultFacets`, `src/lean/lake/Lake/Build/Library.lean:177`), and a facet's
  `FetchM` action runs when it is fetched, before the fetch returns its job (`ensureJob`,
  `src/lean/lake/Lake/Build/Job/Register.lean:47`), so the fault is on disk before the facet
  fetches `leanArts`.
- Lake `v4.34.1` collects a library's modules from its globs when that library's `modules` facet
  is fetched (`LeanLib.recCollectLocalModules`, `src/lean/lake/Lake/Build/Library.lean:36`),
  which `leanArts` fetches first (`LeanLib.recBuildLean`, line 67), so a module the fault adds is
  collected and built by the same build.
- The checker builds a claimed library through its default facet (`Regula.Checker.Lake.Build.run`,
  `surfaceRequest`), in its own process, with this process's environment. -/
def lakefile : String := "\n".intercalate [
  "import Lake",
  "open Lake DSL",
  "package inventory_control where",
  "  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩,",
  "    ⟨`linter.missingDocs, true⟩]",
  "",
  "/-- The input-inventory campaign's fault, injected when a build of the library begins. -/",
  "library_facet inventoryFault (lib : LeanLib) : Unit := do",
  "  let record : System.FilePath := (← IO.getEnv \"INVENTORY_RECORD\").getD \"\"",
  "  let fault := (← IO.getEnv \"INVENTORY_FAULT\").getD \"\"",
  "  let active := !fault.isEmpty && !record.toString.isEmpty && !(← record.pathExists)",
  "  if active then",
  "    let some changed ← IO.getEnv \"INVENTORY_TARGET\" | error \"missing INVENTORY_TARGET\"",
  "    match ← IO.getEnv \"INVENTORY_SOURCE\" with",
  "    | some text => IO.FS.writeFile changed (← IO.FS.readFile text)",
  "    | none => IO.FS.removeFile changed",
  "    IO.FS.writeFile record (Lean.Json.mkObj [(\"fault\", Lean.toJson fault)]).compress",
  "  let job ← lib.leanArts.fetch",
  "  if !active then return job",
  "  job.mapM fun _ => do",
  "    let added ← (lib.pkg.leanLibDir / \"Example\" / \"New.olean\").pathExists",
  "    IO.FS.writeFile record (Lean.Json.mkObj [(\"fault\", Lean.toJson fault),",
  "      (\"buildSucceeded\", Lean.toJson true), (\"addedBuilt\", Lean.toJson added)]).compress",
  "",
  "lean_lib Example where",
  "  globs := #[.andSubmodules `Example]",
  "  defaultFacets := #[LeanLib.facetKind ++ `inventoryFault]",
  ""]

/-- The record the facet of `lakefile` writes for a fault that it injected and after which the
library's Lean artifacts built: the fault's name, `buildSucceeded`, and whether `Example.New` was
built (`addedBuilt`). -/
def injected (fault : String) (added : Bool) : Json :=
  Json.mkObj [("fault", toJson fault), ("buildSucceeded", toJson true),
    ("addedBuilt", toJson added)]

/-- Input-inventory fault controls in a scratch project whose claimed library's default facet
injects the fault when the checker's own build of the library begins (`lakefile`). Root
inventory, under `--incremental` and `--build-lint`: a module added under `Example` after root
discovery must be built and then refused with "root inventory changed:", incomplete status and no
acceptance. Markdown inventory, through `docFenceAudit` and `ruleExamples`: replacing a failing
`docs/` fence with a passing one, or removing its file, during the build must be refused with no
documentation acceptance. Each faulted run must leave the facet's record of the injected fault and
of the library's completed build, and the injected change on disk; each unfaulted run (positive and
restored) must be accepted and leave no record. Any failed check throws. -/
def check : IO Unit := do
  let root ← rootDirectory
  withScratch root "input-inventory" fun scratch => do
    let project := scratch / "project"
    IO.FS.createDirAll (project / "Example")
    toolchain root project
    IO.FS.writeFile (project / "Example.lean") "/-! Empty declared surface. -/\n"
    IO.FS.writeFile (project / "lakefile.lean") lakefile
    manifest project "kernel-only"
    success (← runLake project #["update"] cleanEnv)
    let record := scratch / "build.json"
    let addedSource := scratch / "New.lean"
    IO.FS.writeFile addedSource
      "/-! Added after root discovery. -/\n/-- Documented, so the added module builds \
        without a warning. -/\naxiom escaped : False\n"
    let added := project / "Example/New.lean"
    let env := cleanEnv ++ #[("INVENTORY_RECORD", some record.toString)]
    for (mode, flag) in #[("incremental", "--incremental"), ("build-lint", "--build-lint")] do
      for phase in #["positive", "root-add", "restored"] do
        let fault := phase == "root-add"
        removeFile added
        if !fault then clearBuild project
        requireChecks [⟨"added module starts absent",
          !(← (project / ".lake/build/lib/lean/Example/New.olean").pathExists)⟩]
        removeFile record
        let output := scratch / s!"{mode}-{phase}.json"
        let result ← run project (root / ".lake/build/bin/axiomGate").toString
          #["--project", project.toString, flag, "--json-out", output.toString]
          (env ++ #[("INVENTORY_FAULT", if fault then some phase else none),
            ("INVENTORY_TARGET", some added.toString),
            ("INVENTORY_SOURCE", some addedSource.toString)])
        let packet ← readJson output
        let log := result.stdout ++ result.stderr
        if fault then
          let observation ← readJson record
          requireChecks [⟨s!"added root actually built: {observation.compress}",
              Regula.JsonAgreement.conforms observation (injected phase true)⟩,
            ⟨"added root present", ← added.pathExists⟩,
            ⟨s!"root inventory refusal: {log}\n{packet.compress}", result.exitCode != 0 &&
                log.contains "root inventory changed:" &&
              !log.contains "accepted " &&
              (packet.getObjValAs? String "status").toOption == some "incomplete" &&
              (packet.getObjVal? "acceptance").toOption.isNone⟩]
        else
          success result
          requireChecks [⟨"root positive", accepted packet⟩,
            ⟨"no fault injected", !(← record.pathExists)⟩]
        IO.println s!"root inventory {mode}/{phase}: PASS"
    removeFile added
    let docs := project / "docs"
    IO.FS.createDirAll docs
    let passing := "```lean\nexample : True := True.intro\n```\n"
    IO.FS.writeFile (docs / "control.md") passing
    let passingSource := scratch / "passing.md"
    IO.FS.writeFile passingSource passing
    let target := docs / "target.md"
    for route in #["docFenceAudit", "ruleExamples"] do
      let phases := #["positive", "docs-edit", "restored", "docs-remove", "restored"]
      for index in [:phases.size] do
        let phase := phases[index]!
        removeFile record
        let bad := phase.startsWith "docs-"
        IO.FS.writeFile target (if bad then "```lean\nexample : False := True.intro\n```\n"
          else passing)
        clearBuild project
        let output := scratch / s!"{route}-{index}.json"
        let args := if route == "docFenceAudit" then #["--project", project.toString, "--jobs", "1"]
          else #["--documentation", project.toString, docs.toString, output.toString]
        let result ← run project (root / ".lake/build/bin" / route).toString args
          (env ++ #[("INVENTORY_FAULT", if bad then some phase else none),
            ("INVENTORY_TARGET", some target.toString),
            ("INVENTORY_SOURCE", if phase == "docs-remove" then none
              else some passingSource.toString)])
        let log := result.stdout ++ result.stderr
        if bad then
          let observation ← readJson record
          let reason := if phase == "docs-remove" then "documentation inventory changed" else
                                                        "documentation source changed"
          let present ← if phase == "docs-remove" then pure !(← target.pathExists)
            else pure ((← IO.FS.readFile target) == passing)
          requireChecks
              [⟨s!"fault injected and prerequisite build succeeded: {observation.compress}",
                  Regula.JsonAgreement.conforms observation (injected phase false)⟩,
                ⟨"injected documentation change present", present⟩,
            ⟨s!"Markdown inventory refused: {log}", result.exitCode != 0 && log.contains reason &&
              !log.contains "accepted "⟩]
          if ← output.pathExists then
            requireChecks
                [⟨"no documentation acceptance",
                    ((← readJson output).getObjVal? "acceptance").toOption.isNone⟩]
        else
          success result
          requireChecks [⟨"no fault injected", !(← record.pathExists)⟩]
        IO.println s!"Markdown inventory {route}/{phase}: PASS"
end Regula.Qualification.InputInventory
