import Regula.Qualification.Project
import Regula.Checker.Snapshot

/-! # Dependency snapshot qualification

Native retention of dependency snapshot and RG3001 history controls. These
observations qualify trusted Lake/filesystem boundaries, not universal IO behavior. -/
namespace Regula.Qualification.DependencySnapshot
open Lean System

/-- Throws, labelled with the process's combined output, unless it exited with code 0. -/
def success (result : IO.Process.Output) : IO Unit :=
  requireChecks [⟨result.stdout ++ result.stderr, result.exitCode == 0⟩]

/-- Removes the file at `path` when it exists; a missing file is not an error. -/
def removeFile (path : FilePath) : IO Unit := do
  if ← path.pathExists then IO.FS.removeFile path

/-- Copies the Regula root's `lean-toolchain` file into the directory `target`. -/
def toolchain (root target : FilePath) : IO Unit := do
  IO.FS.writeBinFile (target / "lean-toolchain") (← IO.FS.readBinFile (root / "lean-toolchain"))

/-- Writes `project`'s `foundation_manifest.json` (schema 2): one surface, the `Example`
library with foundation claim `claim` and execution mode `report`, and no exclusions. -/
def manifest (project : FilePath) (claim : String) : IO Unit :=
  writeJson (project / "foundation_manifest.json") (Json.mkObj [
    ("schema-version", toJson (2 : Nat)), ("surfaces", toJson #[Json.mkObj [
      ("library", toJson "Example"), ("claim", toJson claim), ("execution", toJson "report"),
      ("rationale", toJson "Exact frozen-input qualification.")]]),
    ("excluded-libraries", toJson (#[] : Array Json)),
    ("excluded-executables", toJson (#[] : Array Json))])

/-- A checker result packet counts as accepted when its `status` is `"completed"` and it has
an `acceptance` field. -/
def accepted (result : Json) : Bool :=
  (result.getObjValAs? String "status").toOption == some "completed" &&
    (result.getObjVal? "acceptance").toOption.isSome

private def control (project dependency : FilePath) : IO Unit := do
  let inventory ← Regula.Checker.Lake.surfaceInventory project
  let before ← Regula.Checker.Snapshot.dependencies inventory
  let some observed := before.find? (·.package == "dep")
    | throw <| IO.userError "dependency missing"
  requireChecks [⟨"ignored imported module", observed.sourcePaths.any (·.1 == `Dep.Generated)⟩,
    ⟨"buildable unimported module", observed.sourcePaths.any (·.1 == `Dep.Unimported)⟩]
  let unchanged := Regula.Checker.Snapshot.inputsUnchanged inventory before
  unchanged
  let snapshot ← IO.ofExcept <| Regula.Checker.Snapshot.make inventory.root #[] #[] before
  let marker := "R4_SYNTHETIC_UNRELATED"
  let encoded := (toJson (marker.toUTF8.toList.map UInt8.toNat)).compress
  requireChecks [⟨"unrelated bytes excluded", !snapshot.val.configuration.source.contains marker &&
    !snapshot.val.configuration.source.contains encoded⟩]
  for name in #[".env", "unrelated.txt"] do
    IO.FS.writeFile (dependency / name) "R4_SYNTHETIC_CHANGED"
  unchanged
  let built ← Regula.Checker.Lake.buildTargets project #["Example"]
  requireChecks [⟨built.output, built.succeeded⟩,
    ⟨"custom dependency build directory", ← (dependency / "build/lib/lean/Dep.olean").pathExists⟩]
  unchanged
  for name in #["Dep/Generated.lean", "lean-toolchain", "Dep/New.lean"] do
    let path := dependency / name
    let original ← if ← path.pathExists then pure (some (← IO.FS.readFile path)) else pure none
    IO.FS.writeFile path (original.getD "" ++
      if name == "lean-toolchain" then "\n" else "\ndef added : Nat := 9\n")
    let changed ← unchanged.toBaseIO
    match original with
    | some text => IO.FS.writeFile path text
    | none => IO.FS.removeFile path
    match changed with
    | .ok _ => throw <| IO.userError s!"accepted changed dependency input: {name}"
    | .error error =>
        requireChecks
            [⟨"intended dependency refusal",
                error.toString.contains "dependency snapshot changed:"⟩]
    unchanged

/-- The retired dirty decision, kept only as this control's oracle: non-empty output
of one literal-pathspec status over the declared inputs. -/
private def retiredDirty (root : FilePath) (paths : Array FilePath) : IO String := do
  let status ← run root "git" (#["--literal-pathspecs", "status", "--porcelain=v1", "-z",
    "--untracked-files=all", "--ignored=matching", "--"] ++ paths.map (·.toString))
  return if status.exitCode != 0 then "refused" else if status.stdout.isEmpty then
                                                      "clean" else "dirty"

/-- The executed decision, through the public Git-facts observation. -/
private def currentDirty (root : FilePath) (paths : Array FilePath) : IO String := do
  match ← (Regula.Checker.Snapshot.observeGitFacts "control" root #[] paths).toBaseIO with
  | .ok (some _, dirty) => return if dirty then "dirty" else "clean"
  | .ok (none, _) => return "no revision"
  | .error error => return if error.toString == "dependency input status unavailable" then "refused"
      else s!"unexpected refusal: {error}"

private def unrestrictedStatus (root : FilePath) : IO String := do
  return (← run root "git" #["status", "--porcelain=v1", "-z", "--untracked-files=all",
    "--ignored=matching"]).stdout

/-- Git-semantics controls for the unrestricted-status membership decision. Each case
states the retired pathspec result and the current result; they are equal except for
an input inside an untracked nested repository, which the retired status omits. -/
private def gitStatusControls (root : FilePath) : IO Unit :=
  withScratch root "git-status" fun scratch => do
    let repository := scratch / "repository"
    IO.FS.createDirAll (repository / "A")
    IO.FS.createDirAll (repository / "ig")
    IO.FS.writeFile (repository / ".gitignore") "ig/\nig2/\n*.gen\n"
    IO.FS.writeFile
        (repository / "A/a.lean") "def a : Nat := 1\ndef b : Nat := 2\ndef c : Nat := 3\n"
    IO.FS.writeFile (repository / "ig/tracked.lean") "def tracked : Nat := 1\n"
    for args in #[#["init", "-q"], #["add", "-f", ".gitignore", "A/a.lean", "ig/tracked.lean"],
        #["-c", "user.name=Status Control", "-c", "user.email=status@example.invalid", "-c",
          "commit.gpgsign=false", "commit", "-qm", "status control"]] do
      success (← run repository "git" args)
    let repository ← IO.FS.realPath repository
    let base := #[repository / "A/a.lean", repository / "ig/tracked.lean"]
    let expectCase (name : String) (paths : Array FilePath) (retired current : String)
        (shape : String → Bool := fun _ => true) : IO Unit := do
      let observedRetired ← retiredDirty repository paths
      let observedCurrent ← currentDirty repository paths
      requireChecks [⟨s!"git-status {name}: status shape", shape (← unrestrictedStatus repository)⟩,
        ⟨s!"git-status {name}: retired {observedRetired}, expected {retired}",
            observedRetired == retired⟩,
        ⟨s!"git-status {name}: current {observedCurrent}, expected {current}",
            observedCurrent == current⟩]
      success (← run repository "git" #["reset", "-q", "--hard", "HEAD"])
      success (← run repository "git" #["clean", "-qffdx"])
      requireChecks [⟨s!"git-status {name}: restored", (← currentDirty repository base) == "clean"⟩]
      IO.println s!"git-status {name}: PASS (retired {observedRetired}, current {observedCurrent})"
    expectCase "clean" base "clean" "clean"
    IO.FS.writeFile (repository / "ig/other.lean") "unrelated\n"
    IO.FS.writeFile (repository / "x.gen") "unrelated\n"
    IO.FS.createDirAll (repository / "U")
    IO.FS.writeFile (repository / "U/u.lean") "unrelated\n"
    IO.FS.writeFile (repository / "sp ä\nx.lean") "unrelated\n"
    expectCase "unrelated ignored, untracked and NUL-framed siblings" base "clean" "clean"
      (·.contains "!! ig/other.lean")
    IO.FS.writeFile (repository / "ig/new.lean") "new\n"
    expectCase "untracked input under an ignored directory with tracked files"
      #[repository / "ig/new.lean"] "dirty" "dirty" (·.contains "!! ig/new.lean")
    IO.FS.writeFile (repository / "ig/tracked.lean") "def tracked : Nat := 2\n"
    expectCase "modified tracked input under an ignored directory" base "dirty" "dirty"
    IO.FS.createDirAll (repository / "ig2")
    IO.FS.writeFile (repository / "ig2/q.lean") "ignored\n"
    expectCase "input under a collapsed ignored directory" #[repository / "ig2/q.lean"]
      "dirty" "dirty" (·.contains "!! ig2/\x00")
    IO.FS.createDirAll (repository / "N")
    IO.FS.writeFile (repository / "N/n.lean") "untracked\n"
    expectCase "input under an untracked directory" #[repository / "N/n.lean"] "dirty" "dirty"
      (·.contains "?? N/n.lean")
    success (← run repository "git" #["mv", "A/a.lean", "B.lean"])
    expectCase "staged rename with the original declared" #[repository / "A/a.lean"]
      "dirty" "dirty" (·.startsWith "R  B.lean\x00A/a.lean\x00")
    IO.FS.rename (repository / "A/a.lean") (repository / "C.lean")
    success (← run repository "git" #["add", "-N", "C.lean"])
    expectCase "worktree rename with the original declared" #[repository / "A/a.lean"]
      "dirty" "dirty" (·.startsWith " R C.lean\x00A/a.lean\x00")
    IO.FS.removeFile (repository / "A/a.lean")
    expectCase "deleted tracked input" base "dirty" "dirty"
    IO.FS.writeFile (repository / "sp ä\nx.lean") "untracked\n"
    expectCase "NUL-framed input name" #[repository / "sp ä\nx.lean"] "dirty" "dirty"
    IO.FS.createDirAll (repository / "nest")
    success (← run (repository / "nest") "git" #["init", "-q"])
    IO.FS.writeFile (repository / "nest/q.lean") "nested\n"
    expectCase "input inside an untracked nested repository" #[repository / "nest/q.lean"]
      "clean" "dirty" (·.contains "?? nest/\x00")
    let link := scratch / "link"
    success (← run scratch "ln" #["-s", repository.toString, link.toString])
    expectCase "input spelled through a symlinked root" #[link / "A/a.lean"] "clean" "clean"
    IO.FS.writeFile (repository / "A/a.lean") "def a : Nat := 4\n"
    expectCase "modified input spelled through a symlinked root"
        #[link / "A/a.lean"] "dirty" "dirty"
    IO.FS.writeFile (repository / "A/a.lean") "def a : Nat := 4\n"
    expectCase "modified relative input" #[FilePath.mk "A/a.lean"] "dirty" "dirty"
    IO.FS.writeFile (scratch / "outside.lean") "outside\n"
    expectCase "input outside the root" #[scratch / "outside.lean"] "refused" "refused"

/-- Runs the snapshot control group `group`: `git-status` (Git status controls only),
`dependencies` (dependency snapshot retention on a Git and a non-Git local dependency),
`history` (RG3001 history controls in fresh, incremental and build-lint modes), or `all`.
Any other group, and any failed check, throws. -/
def check (group : String) : IO Unit := do
  requireChecks [⟨"known snapshot group",
    #["all", "dependencies", "history", "git-status"].contains group⟩]
  let root ← rootDirectory
  if group == "all" || group == "git-status" then gitStatusControls root
  if group == "git-status" then return
  withScratch root "snapshot-history" fun scratch => do
    let dependency := scratch / "dependency"
    IO.FS.createDirAll (dependency / "Dep")
    IO.FS.writeFile (dependency / "lakefile.toml")
      "name = \"dep\"\nbuildDir = \"build\"\n[[lean_lib]]\nname = \"Dep\"\nglobs = [\"Dep\"]\n"
    IO.FS.writeFile (dependency / "Dep.lean") "import Dep.Generated\n"
    IO.FS.writeFile (dependency / "Dep/Generated.lean") "def generated : Nat := 3\n"
    IO.FS.writeFile (dependency / "Dep/Unimported.lean") "def unimported : Nat := 4\n"
    toolchain root dependency
    IO.FS.writeFile
        (dependency / ".gitignore")
            "Dep/Generated.lean\nDep/Unimported.lean\nDep/New.lean\nlean-toolchain\n.lake/\n"
    IO.FS.writeFile (dependency / ".env") "R4_SYNTHETIC_UNRELATED"
    for args in #[#["init", "-q"], #["add", "."], #["-c", "user.name=Snapshot Control", "-c",
        "user.email=snapshot@example.invalid", "-c", "commit.gpgsign=false", "commit", "-qm",
            "dependency control"]] do
      success (← run dependency "git" args)
    IO.FS.writeFile (dependency / "unrelated.txt") "R4_SYNTHETIC_UNRELATED"
    let project := scratch / "project"
    IO.FS.createDirAll project
    toolchain root project
    IO.FS.writeFile (project / "lakefile.toml")
      "name = \"snapshot_control\"\n[leanOptions]\nautoImplicit = false\nrelaxedAutoImplicit = \
        false\nlinter.missingDocs = true\n[[require]]\nname = \"dep\"\npath = \
        \"../dependency\"\n[[lean_lib]]\nname = \"Example\"\n"
    IO.FS.writeFile (project / "Example.lean") "import Dep\n/-! Snapshot control. -/\n"
    success (← run project "lake" #["update"] cleanEnv)
    if group != "history" then
      manifest project "standard-logical"
      for kind in #["git", "non-git"] do
        if kind == "non-git" then IO.FS.removeDirAll (dependency / ".git")
        for path in #[dependency / "build", project / ".lake/build"] do
          if ← path.pathExists then IO.FS.removeDirAll path
        for name in #[".env", "unrelated.txt"] do
          IO.FS.writeFile (dependency / name) "R4_SYNTHETIC_UNRELATED"
        control project dependency
        IO.FS.removeDirAll (dependency / "build")
        let output := scratch / s!"scope-{kind}.json"
        let (result, packet) ← observeProject root project output #[]
        success result
        let encoded := packet.compress
        requireChecks [⟨"accepted dependency scope", accepted packet⟩,
          ⟨"unrelated filenames excluded", !encoded.contains ".env" &&
              !encoded.contains "unrelated.txt"⟩]
        for marker in #["R4_SYNTHETIC_UNRELATED", "R4_SYNTHETIC_CHANGED"] do
          requireChecks [⟨"unrelated content excluded", !encoded.contains marker &&
            !encoded.contains (toJson (marker.toUTF8.toList.map UInt8.toNat)).compress⟩]
        IO.println s!"dependency snapshot {kind}: PASS"
    if group == "dependencies" then return
    IO.FS.writeFile (project / "lakefile.toml") "name = \
      \"history_control\"\n[leanOptions]\nautoImplicit = false\nrelaxedAutoImplicit = \
      false\nlinter.missingDocs = true\n[[lean_lib]]\nname = \"Example\"\n"
    removeFile (project / "lake-manifest.json")
    success (← run project "lake" #["update"] cleanEnv)
    manifest project "standard-logical"
    for (mode, flags) in
        #[("fresh", #[]), ("incremental", #["--incremental"]), ("build-lint", #["--build-lint"])] do
      for (phase, fixture) in
          #[("positive", "Fixed.lean"), ("negative", "Violation.lean"),
              ("restored", "Fixed.lean")] do
        IO.FS.writeBinFile (project / "Example.lean")
            (← IO.FS.readBinFile (root / "examples/rules/RG3001" / fixture))
        if phase != "negative" then clearBuild project
        let (result, packet) ← observeProject root project (scratch / s!"{mode}-{phase}.json") flags
        if phase != "negative" then
          success result
          requireChecks [⟨"accepted history", accepted packet⟩]
        else
          let findings ← IO.ofExcept (packet.getObjValAs? (Array Json) "diagnostics")
          let historyFindings := findings.filter
              (fun d => (d.getObjValAs? String "id").toOption == some "RG3001")
          requireChecks [⟨"history incomplete", result.exitCode != 0 &&
            (packet.getObjValAs? String "status").toOption == some "incomplete" &&
            (packet.getObjVal? "acceptance").toOption.isNone⟩,
            ⟨"not setup failure", !findings.any
                (fun d => (d.getObjValAs? String "id").toOption == some "RG2001")⟩,
            ⟨"history diagnostic present", !historyFindings.isEmpty⟩,
            ⟨"identity root", historyFindings.any (fun d => (do
              let args ← d.getObjVal? "arguments"
              args.getObjVal? "root").toOption == some (.str "identity"))⟩,
            ⟨"exact source location", historyFindings.all (fun d => (do
              let loc ← d.getObjVal? "location"
              pure ((← loc.getObjValAs? String "kind") == "source" &&
                (← loc.getObjValAs? String "uri").endsWith "Example.lean")).toOption == some true)⟩,
            ⟨"unresolved history", (result.stdout ++ result.stderr).contains
                "execution-unresolved"⟩]
        IO.println s!"snapshot history {mode}/{phase}: PASS"
end Regula.Qualification.DependencySnapshot
