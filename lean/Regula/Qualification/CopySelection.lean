import Regula.Qualification.SourceEvidence
import Regula.Checker.Documentation

/-! # Consumer-domain construction controls

Native compiler, filesystem and Lake observations for the source-selection contracts. The public
fresh audit must consume the original Markdown census. These controls aid counterexample
discovery at trusted boundaries; the universal selection and construction claims are theorems.
-/

namespace Regula.Qualification.CopySelection

open Lean System Regula.Filesystem RegulaQualification.Evidence
open Regula.Qualification.SourceEvidence

/-- Require the intended construction refusal, never an unrelated failure. -/
private def refused (reason : String) (action : IO Unit) : IO Unit := do
  match ← action.toBaseIO with
  | .ok _ => throw <| IO.userError "selected-domain control unexpectedly succeeded"
  | .error error =>
    unless error.toString.contains reason do
      throw <| IO.userError s!"wrong selected-domain refusal: {error}"

/-- Make a deliberate source link through Git's indexed-link checkout. No copy implementation
uses this operation. Git and native link creation are trusted fixture mechanisms. -/
private def sourceLink (project : FilePath) (relative target : String) : IO Unit := do
  let git (args : Array String) : IO String := do
    let result ← Regula.Process.output (.stated "git" "Git creates the deliberate indexed-link input")
      (← Construction.gitProcessArgs {
      cmd := "git", args := #["-C", project.toString] ++ args })
    unless result.exitCode == 0 do throw <| IO.userError result.stderr
    return result.stdout.trimAscii.toString
  discard <| git #["init", "--quiet"]
  IO.FS.writeFile (project / "link-target") target
  let object ← git #["hash-object", "-w", "link-target"]
  discard <| git #["update-index", "--add", "--cacheinfo", "120000," ++ object ++ "," ++ relative]
  discard <| git #["-c", "core.symlinks=true", "checkout-index", "--force", "--", relative]
  unless (← Construction.observeMetadata (project / relative)).type == .symlink do
    throw <| IO.userError "Git fixture did not create the intended source link"

/-- Exercise original-document preservation, cold construction, file-only artifact filtering,
selected aliases, and source-link refusals. `base` is an empty private directory whose caller
owns cleanup. `root` supplies the pinned toolchain and the built public audit executable. -/
def checkAt (root base : FilePath) : IO Unit := do
  let toolchain ← Construction.capture (root / "lean-toolchain") ["lean-toolchain"]
  let source := "/-! Reflexivity. -/\n/-- Reflexivity. -/\ntheorem reflexive (n : Nat) : n = n := rfl\n"
  let positive := "# Valid example\n\n```lean\n" ++ source ++ "```\n"
  let negative := "# Invalid positive example\n\n```lean\nexample : False := True.intro\n```\n"
  let policy := "{\"schema-version\":2,\"surfaces\":[{\"library\":\"Solo\",\"claim\":\"kernel-only\",\"rationale\":\"Reflexivity\"}],\"excluded-libraries\":[],\"excluded-executables\":[]}\n"
  for (label, packages, hidden) in [
      ("artifact-directory", ".lake/packages", "docs/lowering.ir/guide.md"),
      ("documentation-packages", "docs/vendor", "docs/vendor/guide.md")] do
    let project := base / label
    -- `Solo` loads Regula's elaboration observer, which it requires from `root` by path, so that
    -- RG2003 is decided and each audit reaches the documentation stage these phases exercise.
    let lakefile := "import Lake\nopen Lake DSL\npackage copy_selection where\n" ++
      "  packagesDir := \"" ++ packages ++ "\"\n" ++
      "  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, " ++
      "⟨`linter.missingDocs, true⟩]\n" ++ Regula.Checker.observerPluginLean ++
      "require regula from " ++ (toJson root.toString).compress ++ "\nlean_lib Solo where\n" ++
      Regula.Checker.observerNeedLean
    let manifest := (Json.mkObj [
      ("version", toJson "1.1.0"), ("name", toJson "copy_selection"),
      ("lakeDir", toJson ".lake"), ("packagesDir", toJson packages),
      ("packages", toJson #[Regula.Checker.regulaManifestEntry root])]).pretty ++ "\n"
    construct project (Construction.layout (toolchain ++ [
      ⟨["lakefile.lean"], .file lakefile.toUTF8⟩,
      ⟨["lake-manifest.json"], .file manifest.toUTF8⟩,
      ⟨["Solo.lean"], .file source.toUTF8⟩,
      ⟨["foundation_manifest.json"], .file policy.toUTF8⟩,
      ⟨["docs", "ok.md"], .file positive.toUTF8⟩,
      ⟨(FilePath.mk hidden).components, .file positive.toUTF8⟩,
      ⟨["docs", "stale.ir"], .file "old artifact".toUTF8⟩]))
    for phase in ["positive", "negative", "restored"] do
      let bad := phase == "negative"
      IO.FS.writeFile (project / hidden) (if bad then negative else positive)
      let (_, report) ← observe root project phase "axiomGate" #["--with-docs"] {
        failure := bad, mode := some "freshProject",
        status := if bad then "rejected" else "completed",
        ids := if bad then ["RG4002"] else [],
        reason := if bad then "did not elaborate verbatim" else "",
        positiveText := "conforming-positive-pass=2/2" }
      if bad then
        let some report := report | throw <| IO.userError "missing public refusal result"
        let [diagnostic] := (← IO.ofExcept (array report "diagnostics")).toList
          | throw <| IO.userError "expected the single positive-fence refusal"
        let subject ← IO.ofExcept do text (← field diagnostic "arguments") "subject"
        unless subject == "/".intercalate ((FilePath.mk hidden).components.drop 1) ++ ":3" do
          throw <| IO.userError "the refusal did not identify the originally selected document"
      IO.println s!"copy selection {label}/{phase}: PASS"
    if ← (project / "LAKE-MANIFEST.JSON").pathExists then
      replacePath (project / "lake-manifest.json") (project / "manifest-renaming")
      replacePath (project / "manifest-renaming") (project / "LAKE-MANIFEST.JSON")
      let target := base / (label ++ "-selected-manifest")
      let copied ← Regula.Checker.Lake.copyProject project target target
        (selectedFiles := [project / "LAKE-MANIFEST.JSON"])
      unless (← Regula.Filesystem.Construction.listDirectory copied.project).any
          (·.fileName == "LAKE-MANIFEST.JSON") &&
          (← readFile (copied.project / "lake-manifest.json")) == manifest do
        throw <| IO.userError "selected loaded manifest lost its stored source spelling or bytes"
      discard <| observe root project "manifest-alias" "axiomGate" #["--with-docs"] {
        positiveText := "conforming-positive-pass=2/2" }
      IO.println s!"copy selection {label}/selected-manifest-alias: PASS"
    let documents ← Regula.Checker.Documentation.captureMarkdown (project / "docs")
    let target := base / (label ++ "-copy")
    let copied ← Regula.Checker.Lake.copyProject project target target
      (selectedFiles := documents.toList.map (FilePath.mk ·.uri))
    unless (← readFile (copied.project / hidden)) == positive &&
        !(← (copied.project / "docs/stale.ir").pathExists) do
      throw <| IO.userError "kind-aware selection lost documentation or retained a module artifact"
    let cold := base / (label ++ "-cold")
    discard <| Construction.sourceMain ["project", project.toString, cold.toString]
    unless (← readFile (cold / hidden)) == positive do
      throw <| IO.userError "cold construction lost an original Markdown input"
    let alias := project / hidden.toUpper
    if ← alias.pathExists then
      let target := base / (label ++ "-alias")
      let copied ← Regula.Checker.Lake.copyProject project target target (selectedFiles := [alias])
      unless (← readFile (copied.project / hidden)) == positive do
        throw <| IO.userError "selected document alias lost its stored source spelling"
    sourceLink project "docs/selected-link.md" "ok.md"
    discard <| observe root project "source-link" "axiomGate" #["--with-docs"] {
      failure := true, status := "incomplete", ids := ["RG2001"],
      reason := "selected entry is not a regular file" }
    refused "selected entry is not a regular file" <|
      discard <| Construction.sourceMain
        ["project", project.toString, (base / (label ++ "-cold-link")).toString]
    removeOwn .link (project / "docs/selected-link.md")
    sourceLink project "docs/linked.ir" ((FilePath.mk hidden).components[1]!)
    discard <| observe root project "ancestor-link" "axiomGate" #["--with-docs"] {
      failure := true, status := "incomplete", ids := ["RG2001"],
      reason := "selected ancestor is not a directory" }
    removeOwn .link (project / "docs/linked.ir")
    sourceLink project "docs/cycle" "."
    discard <| observe root project "directory-cycle" "axiomGate" #["--with-docs"] {
      failure := true, status := "incomplete", ids := ["RG2001"],
      reason := "selected ancestor is not a directory" }
    refused "selected ancestor is not a directory" <|
      discard <| Construction.sourceMain
        ["project", project.toString, (base / (label ++ "-cold-cycle")).toString]
    removeOwn .link (project / "docs/cycle")
    IO.println s!"copy selection {label}: kinds, cold domain, aliases and links PASS"
  let missing := base / "missing-domain"
  refused "omit a selected source file" <|
    Construction.constructSelectedWith Construction.observer missing [["omitted.md"]] []
  unless !(← missing.pathExists) do
    throw <| IO.userError "missing-domain refusal wrote a destination"
  let occupied := base / "occupied"
  construct occupied [⟨["entry"], .file "original".toUTF8⟩]
  refused "occupied" <|
    Construction.constructSelectedWith Construction.observer occupied [["entry"]]
      [⟨["entry"], .file "replacement".toUTF8⟩]
  unless (← readFile (occupied / "entry")) == "original" do
    throw <| IO.userError "selected construction changed an occupied destination"
  let casing := base / "casing"
  construct casing [⟨[".LaKe"], .directory⟩]
  if ← (casing / ".lake").isDir then
    let attempt ← (Construction.constructSelectedWith Construction.observer
      (base / "alias-collision") [[".LaKe", "entry"]]
      [⟨[".LaKe"], .directory⟩, ⟨[".lake"], .directory⟩,
       ⟨[".LaKe", "entry"], .file "selected".toUTF8⟩]).toBaseIO
    unless attempt matches .error _ do
      throw <| IO.userError "selected construction accepted colliding directory aliases"
  IO.println "copy selection: original domain, exclusive destinations and alias collision PASS"

/-- Run native selection qualification inside one scratch directory owned by this campaign. -/
def check : IO Unit := do
  let root ← rootDirectory
  withScratch root "copy-selection" (checkAt root)

end Regula.Qualification.CopySelection
