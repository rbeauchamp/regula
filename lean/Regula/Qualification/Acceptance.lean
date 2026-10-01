import Regula.Qualification.InputInventory

/-! # Acceptance control qualification

Native retention of raw-worker acceptance and documentation-dependency controls.
The coordinator is the actual checker; only a copied native child proxy mutates
completed fence-compilation packets. Project and documentation acceptance run in one
process with no serialized evidence between them, so no project packet exists to
mutate. IO/process observations remain trusted boundaries. -/
namespace Regula.Qualification.Acceptance
open Lean System DependencySnapshot InputInventory

private def array (j : Json) (key : String) : IO (Array Json) := IO.ofExcept
    (j.getObjValAs? (Array Json) key)
private def first (xs : Array Json) : IO Json := do
  let some x := xs[0]? | throw <| IO.userError "mutation requires a nonempty array"
  return x

/-- Test-only native proxy; invoked before the dispatcher's outer deadline wrapper. -/
def worker (args : List String) : IO UInt32 := do
  let mode := (← IO.getEnv "REGULA_PACKET_FAULT").getD ""
  let compilation := args.head? == some "--compile-batch-worker"
  let some parent := (← IO.appPath).parent | throw <| IO.userError "missing proxy directory"
  let child ← IO.Process.spawn {
    cmd := (parent / "axiomGate-real").toString, args := args.toArray,
    stdin := .inherit, stdout := .inherit, stderr := .inherit }
  let code ← child.wait
  if code != 0 then return code
  if compilation && #["fence-missing", "fence-duplicate", "fence-misindexed"].contains mode then
    let some path := args[2]? | throw <| IO.userError "missing compilation output"
    let packet ← readJson ⟨path⟩
    let mut payload ← array packet "payload"
    if mode == "fence-missing" then payload := payload.pop
    else if mode == "fence-duplicate" then payload := payload.push (← first payload)
    else
      let entry ← IO.ofExcept ((← first payload).getArr?)
      payload := payload.set! 0 (toJson (entry.set! 0 (toJson (999999 : Nat))))
    writeJson ⟨path⟩ (packet.setObjVal! "payload" (toJson payload))
  return 0

private def faults : String → Array (String × String)
  | "fences" =>
      #[("fence-missing", "missing required key"), ("fence-duplicate", "duplicateResult"),
          ("fence-misindexed", "unknownKey")]
  | _ => #[]

private def save (path : FilePath) (receipt : Json) : IO Unit := do
  let suffix ← IO.getRandomBytes 12
  let temporary := FilePath.mk
      (path.toString ++ "." ++ suffix.foldl (fun s b => s ++ s!"{b.toNat}-") "")
  try
    writeJson temporary receipt
    IO.FS.rename temporary path
  finally
    removeFile temporary

private def qualify (group : String) (evidence : FilePath) (receipt : IO.Ref Json) : IO Unit := do
  let root ← rootDirectory
  let update (key : String) (value : Json) := do
    receipt.modify (·.setObjVal! key value)
    save evidence (← receipt.get)
  let executable := root / ".lake/build/bin/axiomGate"
  let head ← run root "git" #["rev-parse", "HEAD"]
  success head
  update "inputs" (Json.mkObj [("head", toJson head.stdout.trimAscii.toString)])
  let digest ← run root "shasum" #["-a", "256", executable.toString]
  success digest
  update "inputs" (Json.mkObj [("head", toJson head.stdout.trimAscii.toString),
    ("binarySha256", toJson (digest.stdout.splitOn " ").head!)])
  withScratch root "acceptance-controls" fun scratch => do
    let project := scratch / "project"
    IO.FS.createDirAll (project / "docs")
    prepareProject root project "acceptance_control" "standard-logical"
        "Exact accepted-result transport controls."
    manifest project "standard-logical"
    IO.FS.writeFile (project / "Example.lean") "import Regula.Contract\n/-! Public acceptance \
      transport control. -/\n/-- The accepted value. -/\ndef value : Nat := 7\n"
    IO.FS.writeFile (project / "docs/control.md")
      "```lean\ntheorem documented : True := True.intro\n```\n\n<!-- lean-fail: Type mismatch \
        -->\n```lean\nexample : False := True.intro\n```\n"
    let bin := scratch / "tool/bin"
    IO.FS.createDirAll bin
    IO.FS.createDirAll (scratch / "tool/lib")
    success
        (← run root "ln"
            #["-s", (root / ".lake/build/lib/lean").toString, (scratch / "tool/lib/lean").toString])
    copyExecutable executable (bin / "axiomGate-real")
    copyExecutable (← IO.appPath) (bin / "axiomGate")
    let mut sources : List (String × Json) := []
    for name in
        #["lean-toolchain", "lakefile.lean", "lake-manifest.json", "foundation_manifest.json",
            "Example.lean", "docs/control.md"] do
      if ← (project / name).pathExists then sources := sources ++
                                             [(name, toJson (← IO.FS.readFile (project / name)))]
    update "sources" (Json.mkObj sources)
    let mut records : Array Json := #[]
    let mut cases := #[("positive", "", "")]
    for (fault, reason) in faults group do
      cases := cases.push ("mutation", fault, reason) |>.push ("restored", "", "")
    for (phase, fault, reason) in cases do
      let output := scratch / s!"result-{records.size}.json"
      let args := #["--project", project.toString, "--with-docs", "--json-out", output.toString]
      update "activeCase" (Json.mkObj [("phase", toJson phase), ("fault", toJson fault),
        ("command", toJson (#[ (bin / "axiomGate").toString ] ++ args))])
      let env := cleanEnv ++ #[("REGULA_QUALIFICATION_WRAPPER", some "acceptance"),
        ("REGULA_PACKET_FAULT", some fault)]
      let start ← IO.monoMsNow
      -- Every case inherits only the public 420-second deadline.
      let result ← IO.Process.output {
        cmd := (bin / "axiomGate").toString, args,
        cwd := some project, env }
      let elapsed := (← IO.monoMsNow) - start
      -- Persist the raw result and its location before any parsing. A missing file
      -- is explicitly null, never fabricated.
      let mut active := (← receipt.get).getObjVal? "activeCase" |>.toOption.getD Json.null
      active := (active.setObjVal! "exitCode" (toJson result.exitCode.toNat)).setObjVal!
        "log" (toJson (result.stdout ++ result.stderr))
      update "activeCase" active
      let resultEvidence := evidence.addExtension s!"result-{records.size}.json"
      let resultFile ← if ← output.pathExists then do
        IO.FS.rename output resultEvidence
        pure (toJson resultEvidence.toString)
        else pure Json.null
      active := active.setObjVal! "resultFile" resultFile
      update "activeCase" active
      let value ← if resultFile != Json.null then readJson resultEvidence else pure Json.null
      let log := result.stdout ++ result.stderr
      let status := (value.getObjValAs? String "status").toOption
      let hasAcceptance := (value.getObjVal? "acceptance").toOption.isSome
      let hasDocs := (value.getObjVal? "documentationAcceptance").toOption.isSome
      let passed := if fault.isEmpty then result.exitCode == 0 && status == some "completed" &&
                                           hasAcceptance && hasDocs
        else result.exitCode != 0 && status == some "incomplete" && !hasAcceptance && !hasDocs &&
          (reason.isEmpty || log.toLower.contains reason.toLower)
      let record := Json.mkObj [("phase", toJson phase), ("fault", toJson fault),
        ("command", toJson (#[ (bin / "axiomGate").toString ] ++ args)),
        ("milliseconds", toJson elapsed), ("exitCode", toJson result.exitCode.toNat),
        ("expectedReason", toJson reason), ("status", toJson status), ("pass", toJson passed),
        ("log", toJson log), ("resultFile", resultFile)]
      records := records.push record
      update "records" (toJson records)
      update "activeCase" Json.null
      requireChecks [⟨s!"acceptance {phase}/{fault}: {log}", passed⟩]
      IO.println s!"acceptance transport {phase}/{fault}: PASS"

/-- Invalidate old evidence before setup. SIGKILL leaves a current incomplete receipt;
ordinary exceptions retain failure and the active case. Filesystem atomicity is trusted. -/
def beginAttempt (group : String) (evidence : FilePath) (attempt : String) : IO Json := do
  if let some parent := evidence.parent then IO.FS.createDirAll parent
  let receipt := Json.mkObj [("attemptId", toJson attempt),
    ("status", toJson "incomplete"), ("group", toJson group), ("inputs", Json.mkObj []),
    ("records", toJson (#[] : Array Json))]
  save evidence receipt
  return receipt

/-- The outer wrapper supplies its original attempt; direct timed dispatch creates
one before setup. Neither path can reuse a previous completed receipt. -/
def check (group : String) (evidence : FilePath) (attempt : Option String := none) : IO Unit := do
  let attempt ← attempt.map pure |>.getD freshAttempt
  let receipt ← IO.mkRef (← beginAttempt group evidence attempt)
  try
    requireChecks [⟨"known transport group", !(faults group).isEmpty⟩]
    qualify group evidence receipt
  catch error =>
    receipt.modify
        (fun r => (r.setObjVal! "status" (toJson "failed")).setObjVal! "error"
                   (toJson error.toString))
    save evidence (← receipt.get)
    throw error
  receipt.modify (·.setObjVal! "status" (toJson "completed"))
  save evidence (← receipt.get)

/-- Documentation dependency-freeze control, run in a scratch project that requires a local
`dep` package. Through both `docFenceAudit` and `ruleExamples` it checks that a fence over
`Dep` passes when the dependency is unchanged, is refused with "dependency snapshot changed:"
and no acceptance when the build itself rewrites `Dep.lean`, and passes again once restored;
then a combined `--with-docs` run must accept both code and documentation on one snapshot.
Any failed check throws. -/
def documentationDependencies : IO Unit := do
  let root ← rootDirectory
  withScratch root "documentation-dependency" fun scratch => do
    let dependency := scratch / "dependency"
    IO.FS.createDirAll dependency
    IO.FS.writeFile (dependency / "lakefile.toml") "name = \"dep\"\n[[lean_lib]]\nname = \"Dep\"\n"
    toolchain root dependency
    let original := "namespace Dep\ndef n : Nat := 1\nend Dep\n"
    let changed := "namespace Dep\ndef n : Nat := 2\nend Dep\n"
    let dependencySource := dependency / "Dep.lean"
    IO.FS.writeFile dependencySource original
    let project := scratch / "project"
    IO.FS.createDirAll (project / "docs")
    toolchain root project
    IO.FS.writeFile (project / "lakefile.toml")
      "name = \"documentation_dependency\"\n[leanOptions]\nautoImplicit = \
        false\nrelaxedAutoImplicit = false\nlinter.missingDocs = true\n[[require]]\nname = \
        \"dep\"\npath = \"../dependency\"\n[[lean_lib]]\nname = \"Example\"\n"
    manifest project "kernel-only"
    let source := "import Lean\nimport Dep\n/-! Documentation prerequisite. -/\ntheorem value : \
      Dep.n = 1 := rfl\n"
    IO.FS.writeFile (project / "Example.lean") source
    IO.FS.writeFile
        (project / "docs/control.md") "```lean\nimport Dep\nexample : Dep.n = 1 := rfl\n```\n"
    success (← run project "lake" #["update"] cleanEnv)
    for route in #["docFenceAudit", "ruleExamples"] do
      for phase in #["positive", "changed-during-build", "restored"] do
        if phase != "changed-during-build" then
          clearBuild project
          clearBuild dependency
        IO.FS.writeFile dependencySource original
        let bad := phase == "changed-during-build"
        let mutation := if bad then s!"run_cmd do\n  \
          IO.FS.writeFil\
          e {toJson dependencySource.toString |>.compress} {toJson changed |>.compress}\n" else ""
        IO.FS.writeFile (project / "Example.lean") (source ++ mutation)
        let output := scratch / s!"{route}-{phase}.json"
        let args := if route == "docFenceAudit" then #["--project", project.toString, "--jobs", "1"]
          else #["--documentation", project.toString, (project / "docs").toString, output.toString]
        let result ← run project (root / ".lake/build/bin" / route).toString args cleanEnv
        let log := result.stdout ++ result.stderr
        if bad then
          requireChecks
              [⟨"dependency mutation occurred", (← IO.FS.readFile dependencySource) == changed⟩,
            ⟨s!"frozen dependency refused: {log}", result.exitCode != 0 &&
                log.contains "dependency snapshot changed:" &&
              !log.contains "accepted "⟩]
          if ← output.pathExists then
            requireChecks
                [⟨"no acceptance", ((← readJson output).getObjVal? "acceptance").toOption.isNone⟩]
        else
          success result
          requireChecks
              [⟨"checked positive fence", result.stdout.contains "conforming-positive-pass=1/1"⟩]
          if route == "ruleExamples" then requireChecks
                                           [⟨"documentation accepted", accepted
                                               (← readJson output)⟩]
        IO.println s!"documentation dependency {route}/{phase}: PASS"
    let (result, packet) ← observeProject root project (scratch / "combined.json") #["--with-docs"]
    success result
    requireChecks [⟨"same-snapshot combined acceptance", accepted packet &&
      (packet.getObjVal? "documentationAcceptance").toOption.isSome⟩]
end Regula.Qualification.Acceptance
