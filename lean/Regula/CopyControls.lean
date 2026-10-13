import Regula.Checker.Lake
import Regula.Checker.RuleExampleQualification
import Regula.Qualification.Slot
import Lean.Elab.Command

/-! # Construction boundary controls

These controls exercise the native filesystem and Lake boundaries that the construction theorem
takes as hypotheses. They are counterexample aids, not proofs of those external mechanisms.
The acceptance build elaborates the refusal controls. `qualify combined` runs the loaded-workspace
control natively, as the product loads workspaces. No executable runs the deliberate link/FIFO
fixtures, and no workspace containing such a fixture is passed to Lake after a successful copy.
-/

namespace Regula.CopyControls

open Lean System
open Regula.Filesystem

/-- Require an external fixture-maker to succeed. The link and FIFO creation below is deliberate
negative input, never the implementation of an accepted copy. -/
private def fixture (command : String) (args : Array String) : IO Unit := do
  let out ← IO.Process.output (← Construction.gitProcessArgs {cmd := command, args})
  unless out.exitCode == 0 do throw <| IO.userError s!"fixture failed: {out.stderr}"

/-- Refuse an operation for its construction reason. A failure elsewhere does not qualify it. -/
private def refused (label needle : String) (action : IO Unit) : IO Unit := do
  match ← action.toBaseIO with
  | .ok _ => throw <| IO.userError s!"{label}: construction unexpectedly succeeded"
  | .error error =>
    unless error.toString.contains needle do
      throw <| IO.userError s!"{label}: wrong refusal: {error}"

-- POSIX no-follow and exclusive-creation boundary controls. Windows has no supported observer.
run_cmd do
  unless System.Platform.isWindows do
    withOwnTempDir fun base => do
      IO.eprintln "construction controls: source refusals"
      let source := base / "source"
      construct source [⟨["plain"], .file "source bytes".toUTF8⟩]
      let positive ← copy source (base / "positive")
      unless positive.length == 2 &&
          (← IO.FS.readFile (base / "positive/plain")) == "source bytes" do
        throw <| IO.userError "plain copy lost its source receipt or bytes"
      let policies := base / "policies"
      let selected := [".lake/policy.json", "tmp/policy.json", ".cache/policy.json", "policy.olean"]
      construct policies (Construction.layout (
        selected.map (fun path => ⟨(FilePath.mk path).components, .file "policy".toUTF8⟩) ++
        [⟨[".lake", "stale"], .file "stale".toUTF8⟩,
         ⟨[".cache", "stale"], .file "stale".toUTF8⟩,
         ⟨["tmp", "stale"], .file "stale".toUTF8⟩,
         ⟨["plain"], .file "ordinary".toUTF8⟩]))
      let selectedCopy := base / "selected-copy"
      discard <| Construction.sourceMain (["project", policies.toString, selectedCopy.toString] ++ selected)
      for path in selected do
        unless (← readFile (selectedCopy / path)) == "policy" do
          throw <| IO.userError "cold project copy lost selected policy bytes"
      unless (← readFile (selectedCopy / "plain")) == "ordinary" do
        throw <| IO.userError "cold project copy lost ordinary source bytes"
      for directory in [".lake", ".cache", "tmp"] do
        unless !(← (selectedCopy / directory / "stale").pathExists) do
          throw <| IO.userError "cold project selection included an unselected pruned sibling"
      fixture "ln" #["-s", "../plain", (policies / ".cache/link").toString]
      refused "selected policy link" "selected entry is not a regular file" <|
        discard <| Construction.sourceMain
          ["project", policies.toString, (base / "selected-link-output").toString, ".cache/link"]
      fixture "ln" #["-s", "..", (policies / ".cache/ancestor").toString]
      refused "selected policy ancestor link" "selected ancestor is not a directory" <|
        discard <| Construction.sourceMain
          ["project", policies.toString, (base / "selected-ancestor-output").toString, ".cache/ancestor/plain"]
      if ← (policies / ".CACHE/POLICY.json").pathExists then
        let foldedCopy := base / "folded-policy-copy"
        discard <| Construction.sourceMain
          ["project", policies.toString, foldedCopy.toString, ".CACHE/POLICY.json"]
        unless (← readFile (foldedCopy / ".CACHE/POLICY.json")) == "policy" do
          throw <| IO.userError "cold project copy lost a selected policy's stored spelling"
      refused "removed all domain" "unknown construction domain" <|
        discard <| Construction.sourceMain ["all", source.toString, (base / "all-output").toString]
      let slot := base / "conflicting-slot"
      construct slot []
      refused "conflicting source occurrences" "conflicting captured bytes" <|
        discard <| Regula.Qualification.Slot.prepareSlot source ⟨slot⟩
          #[(source / "plain", "source bytes".toUTF8), (source / "plain", "different".toUTF8)] #[] #[]
      let alias := base / "source-alias"
      fixture "ln" #["-s", source.toString, alias.toString]
      refused "slot linked source" "not a directory or" <|
        discard <| Regula.Qualification.Slot.copyTree alias (base / "slot-link-output")
      let gitAlias := base / "git-alias"
      fixture "ln" #["-s", (source / "plain").toString, gitAlias.toString]
      refused "slot linked Git pointer" "not a directory or" <|
        Regula.Qualification.Slot.materializeGit (base / "git-output") gitAlias
      fixture "ln" #["-s", "plain", (source / "link").toString]
      refused "source link" "not a directory or" (discard <| copy source (base / "link-output"))
      removeOwn .link (source / "link")
      IO.eprintln "construction controls: FIFO"
      fixture "mkfifo" #[(source / "pipe").toString]
      refused "source FIFO" "not a directory or" (discard <| copy source (base / "pipe-output"))
      refused "slot Git FIFO" "not a directory or" <|
        Regula.Qualification.Slot.materializeGit (base / "fifo-git-output") (source / "pipe")
      -- The observer intentionally has no removal kind for a FIFO. It stays in this fixture's
      -- private root, which withOwnTempDir removes as a whole after the control.
      let occupied := base / "occupied"
      IO.eprintln "construction controls: occupied destination"
      construct occupied [⟨["vendor"], .directory⟩]
      refused "occupied packages place" "occupied" (discard <| copy (base / "positive") occupied)
      let parent := base / "exclusive"
      IO.eprintln "construction controls: exclusive final link"
      construct parent []
      fixture "ln" #["-s", (base / "absent").toString, (parent / "vendor").toString]
      let output ← (Construction.emitWith Construction.observer parent
        [⟨["vendor"], .file "never follows the link".toUTF8⟩]).toBaseIO
      unless output matches .error _ do
        throw <| IO.userError "exclusive creation followed an occupied final link"
      unless !(← (base / "absent").pathExists) do
        throw <| IO.userError "exclusive creation wrote through a dangling link"
      -- Case aliases must collide at exclusive creation on a folding filesystem. Distinct
      -- spellings remain valid distinct entries on a case-sensitive filesystem.
      let probe := base / "case-probe"
      IO.eprintln "construction controls: case aliases"
      construct probe [⟨[".LaKe"], .directory⟩]
      if (← Construction.kindWith Construction.observer (probe / ".lake")) == some .dir then
        let result ← (construct (base / "case-output")
          [⟨[".LaKe"], .directory⟩, ⟨[".lake"], .directory⟩]).toBaseIO
        unless result matches .error _ do
          throw <| IO.userError "case-folded destination alias was not refused exclusively"

-- Git's external index/blob/config boundary: the copy has the complete indexed worktree,
-- and every tracked link is the native Git target-text regular-file representation.
run_cmd do
  unless System.Platform.isWindows do
    withOwnTempDir fun base => do
      IO.eprintln "construction controls: Git target-text representation"
      let source := base / "git-source"
      construct source (Construction.layout [
        ⟨["plain"], .file "tracked file\n".toUTF8⟩,
        ⟨[".gitignore"], .file ".lake/\n".toUTF8⟩,
        ⟨[".lake", "build", "lib", "Cached.olean"], .file "reusable build output".toUTF8⟩,
        ⟨[".lake", "cache"], .file "unselected cache".toUTF8⟩,
        ⟨["untracked"], .file "unselected source".toUTF8⟩])
      fixture "git" #["-C", source.toString, "init", "--quiet"]
      fixture "ln" #["-s", "plain", (source / "tracked-link").toString]
      fixture "git" #["-C", source.toString, "-c", "core.symlinks=true", "add", "plain", "tracked-link", ".gitignore"]
      fixture "git" #["-C", source.toString, "-c", "user.name=Construction Control",
        "-c", "user.email=construction@example.invalid", "-c", "commit.gpgsign=false",
        "commit", "--quiet", "-m", "controlled index"]
      let target := base / "git-target"
      discard <| Construction.copyGit source target
      unless (← readFile (target / ".lake/build/lib/Cached.olean")) == "reusable build output" &&
          !(← (target / ".lake/cache").pathExists) && !(← (target / "untracked").pathExists) do
        throw <| IO.userError "Git copy did not retain exactly its reusable untracked build outputs"
      unless (← observeMetadata (target / "tracked-link")).type == .file &&
          (← readBytes (target / "tracked-link")) == "plain".toUTF8 do
        throw <| IO.userError "tracked Git link was not its target-text regular representation"
      let status ← Construction.gitOutput target
        #["-c", "core.fileMode=true", "status", "--porcelain", "--untracked-files=all"]
      unless status.exitCode == 0 && status.stdout.isEmpty do
        throw <| IO.userError s!"target-text Git checkout is not clean: {status.stdout}{status.stderr}"
      -- A self-pointing common instruction is unnecessary after source-location equality and
      -- must not redirect the clone to its source. Stored case is an external filesystem boundary.
      Construction.appendFileWith Construction.observer (source / ".git") "commondir"
        ((source / ".git").toString ++ "\n").toUTF8
      let selfCommon := base / "self-common-output"
      discard <| Construction.copyGit source selfCommon
      unless (← Construction.gitPath selfCommon
          #["rev-parse", "--path-format=absolute", "--git-common-dir"]) ==
          (← observeRealPath (selfCommon / ".git")) &&
          (← Construction.kindWith Construction.observer (selfCommon / ".git/commondir")).isNone do
        throw <| IO.userError "copied self-pointing common instruction selects its source"
      if (← Construction.kindWith Construction.observer (source / ".git/COMMONDIR")).isSome then
        IO.FS.rename (source / ".git/commondir") (source / ".git/temporary-spelling")
        IO.FS.rename (source / ".git/temporary-spelling") (source / ".git/COMMONDIR")
        let foldedCommon := base / "folded-common-output"
        discard <| Construction.copyGit source foldedCommon
        unless (← Construction.gitPath foldedCommon
            #["rev-parse", "--path-format=absolute", "--git-common-dir"]) ==
            (← observeRealPath (foldedCommon / ".git")) &&
            (← Construction.kindWith Construction.observer (foldedCommon / ".git/commondir")).isNone do
          throw <| IO.userError "copied folded common instruction selects its source"
        removeOwn .file (source / ".git/COMMONDIR")
      else removeOwn .file (source / ".git/commondir")
      -- Configuration scope, repository selectors, stored index spellings and alternate stores
      -- are external Git/filesystem boundaries. Each control targets one closed-domain refusal.
      fixture "git" #["-C", source.toString, "config", "extensions.worktreeConfig", "true"]
      Construction.appendFileWith Construction.observer (source / ".git") "config.worktree"
        "[core]\n\tsymlinks = true\n".toUTF8
      refused "Git worktree extension" "outside the closed case" <|
        discard <| Construction.copyGit source (base / "extension-output")
      fixture "git" #["-C", source.toString, "config", "--unset", "extensions.worktreeConfig"]
      removeOwn .file (source / ".git/config.worktree")
      let other := base / "other"
      construct other [⟨["plain"], .file "another repository".toUTF8⟩]
      fixture "git" #["-C", other.toString, "init", "--quiet"]
      fixture "ln" #["-s", "other-target", (other / "tracked-link").toString]
      fixture "git" #["-C", other.toString, "-c", "core.symlinks=true", "add", "plain", "tracked-link"]
      construct (base / "worker") [⟨["source.lean"], .file
        ((include_str "../RegulaCore/CopyProgram.lean") ++
          "\n/-- Controlled cold copy. -/\ndef main := Regula.Filesystem.Construction.sourceMain\n").toUTF8⟩]
      let isolated := base / "isolated-output"
      let out ← IO.Process.output {
        cmd := ((← Lean.getBuildDir) / "bin/lean").toString
        args := #["--run", (base / "worker/source.lean").toString, "git", source.toString, isolated.toString]
        env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none),
          ("GIT_DIR", some (other / ".git").toString), ("GIT_WORK_TREE", some other.toString),
          ("GIT_COMMON_DIR", some (other / ".git").toString),
          ("GIT_INDEX_FILE", some (other / ".git/index").toString),
          ("GIT_OBJECT_DIRECTORY", some (other / ".git/objects").toString),
          ("GIT_CONFIG_COUNT", some "not-a-number"), ("GIT_CONFIG_KEY_0", some "core.symlinks"),
          ("GIT_CONFIG_VALUE_0", some "true"), ("GIT_CONFIG_PARAMETERS", some "'malformed")] }
      unless out.exitCode == 0 && (← readBytes (isolated / "tracked-link")) == "plain".toUTF8 do
        throw <| IO.userError s!"copy inherited Git repository/config selectors: {out.stdout}{out.stderr}"
      let refresh ← Construction.gitOutput isolated #["update-index", "-q", "--refresh"]
      let diff ← Construction.gitOutput isolated #["diff", "--exit-code", "HEAD"]
      unless refresh.exitCode == 0 && diff.exitCode == 0 do
        throw <| IO.userError "isolated Git refresh and diff disagree with its source index"
      if (← Construction.kindWith Construction.observer (source / "TRACKED-LINK")) == some .symlink then
        -- A deliberate fixture rename changes only the stored spelling; Git's index stays fixed.
        IO.FS.rename (source / "tracked-link") (source / "temporary-spelling")
        IO.FS.rename (source / "temporary-spelling") (source / "TRACKED-LINK")
        refused "Git link index spelling" "index spelling differs" <|
          discard <| Construction.copyGit source (base / "link-spelling-output")
        IO.FS.rename (source / "TRACKED-LINK") (source / "tracked-link")
        IO.FS.rename (source / "plain") (source / "temporary-spelling")
        IO.FS.rename (source / "temporary-spelling") (source / "PLAIN")
        refused "Git file index spelling" "index spelling differs" <|
          discard <| Construction.copyGit source (base / "file-spelling-output")
        IO.FS.rename (source / "PLAIN") (source / "plain")
      -- A relative linked-worktree pointer exercises Git's own resolution, without administering
      -- any Git worktree. These are ordinary fixture metadata instructions in a private root.
      let leaf := source / ".git/worktrees/control"
      let head ← Construction.capture (source / ".git/HEAD") ["HEAD"]
      let index ← Construction.capture (source / ".git/index") ["index"]
      Construction.ensureDirectory 4096 (source / ".git/worktrees")
      construct leaf (head ++ index ++ [⟨["commondir"], .file "../..\n".toUTF8⟩])
      let linked := base / "linked"
      construct linked [⟨[".git"], .file "gitdir: ../git-source/.git/worktrees/control\n".toUTF8⟩]
      let slot := base / "linked-slot"
      construct slot []
      Regula.Qualification.Slot.materializeGit (slot / ".git") (linked / ".git")
      let copiedHead ← Construction.gitOutput slot #["cat-file", "-e", "HEAD^{commit}"]
      unless copiedHead.exitCode == 0 do
        throw <| IO.userError s!"Git-resolved slot common metadata lost its objects: {copiedHead.stderr}"
      construct (source / ".git/cache") []
      construct (source / ".git/objects/cache") []
      Construction.appendFileWith Construction.observer (source / ".git/objects/info") "alternates"
        "cache\n".toUTF8
      refused "Git clone alternates" "alternates are outside" <|
        discard <| Construction.copyGit source (base / "alternate-copy-output")
      refused "Git slot common alternates" "alternates are outside" <|
        Regula.Qualification.Slot.materializeGit (base / "alternate-slot-output") (linked / ".git")
      removeOwn .file (source / ".git/objects/info/alternates")
      fixture "ln" #["-s", "../../../plain", (source / ".lake/build/untracked-link").toString]
      refused "untracked Git build link" "not a directory or" <|
        discard <| Construction.copyGit source (base / "untracked-build-output")
      removeOwn .link (source / ".lake/build/untracked-link")
      fixture "ln" #["-s", "plain", (source / "untracked-link").toString]
      refused "untracked Git source link" "not a directory or" <|
        discard <| Construction.copyGit source (base / "untracked-output")
      IO.eprintln "construction controls: tracked Git link regular and clean; untracked link refused"

/-- Loaded-workspace control: the lakefile sets packagesDir, while its loaded default manifest
omits that field. The source vendor entry is build state, not a directory to copy or link into.
Run in the native qualification executable because Lake's loader needs its initialized native
state; source elaboration tests the independent directory/file refusals above. -/
def checkWorkspace : IO Unit := do
  unless System.Platform.isWindows do
    withOwnTempDir fun base => do
      IO.eprintln "construction controls: loaded packages directory"
      let source := base / "project"
      let toolchain ← Construction.capture "lean-toolchain" ["lean-toolchain"]
      let lakefile := "import Lake\nopen Lake DSL\npackage construction_control where\n" ++
        "  packagesDir := \"vendor\"\n" ++
        "  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, " ++
        "⟨`linter.missingDocs, true⟩]\n" ++
        "lean_lib Solo\n"
      let manifest := "{\"version\":\"1.1.0\",\"name\":\"construction_control\"," ++
        "\"lakeDir\":\".lake\",\"packages\":[]}\n"
      construct source (Construction.layout (toolchain ++ [
        ⟨["lakefile.lean"], .file lakefile.toUTF8⟩,
        ⟨["Solo.lean"], .file ("/-! Plain source control. -/\n" ++
          "/-- Natural equality is reflexive. -/\ntheorem reflexive (n : Nat) : n = n := rfl\n").toUTF8⟩,
        ⟨["lake-manifest.json"], .file manifest.toUTF8⟩,
        ⟨["vendor", "stale"], .file "must not be copied as project source".toUTF8⟩]))
      let target := base / "copied"
      let result ← Regula.Checker.Lake.copyProject source target target
      unless !(← (result.project / "vendor/stale").pathExists) &&
          (← IO.FS.readFile (result.project / "lake-manifest.json")) == manifest do
        throw <| IO.userError "copy used a manifest/default packages directory instead of Lake's workspace"
      unless !(← (result.project / ".lake/package-overrides.json").pathExists) do
        throw <| IO.userError "empty dependency graph changed captured configuration presence"
      Regula.Checker.Workspace.withRootWorkspace result.project fun ws => do
        unless ws.relPkgsDir == "vendor" &&
            ws.manifestFile == result.project / "lake-manifest.json" do
          throw <| IO.userError "ordinary copied load lost the loaded workspace configuration"
      -- The public audit and its serialized configuration account are an external compiler/CLI
      -- boundary. This selected policy is deliberately outside the project, and is not relocated.
      let policy := (Json.mkObj [("schema-version", toJson (2 : Nat)),
        ("surfaces", toJson #[Json.mkObj [("library", .str "Solo"), ("claim", .str "kernel-only"),
          ("rationale", .str "The same reflexivity theorem with no logical axioms.")]]),
        ("excluded-libraries", toJson (#[] : Array Json)),
        ("excluded-executables", toJson (#[] : Array Json))]).pretty ++ "\n"
      let external := source / "../selected-policy.json"
      Construction.appendFileWith Construction.observer base "selected-policy.json" policy.toUTF8
      let binary ← IO.FS.realPath ((← IO.currentDir) / ".lake/build/bin/axiomGate")
      let output := base / "external-manifest-result.json"
      let audit ← IO.Process.output {
        cmd := binary.toString, cwd := some source
        args := #["--project", source.toString, "--manifest", external.toString,
          "--incremental", "--json-out", output.toString]
        env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none)] }
      unless audit.exitCode == 0 do
        throw <| IO.userError s!"selected external manifest audit failed: {audit.stdout}{audit.stderr}"
      let account ← IO.ofExcept (Json.parse (← readFile output))
      let effective ← IO.ofExcept (account.getObjVal? "effective")
      let origins ← IO.ofExcept (effective.getObjVal? "configurationOrigins")
      let captured : Regula.CopyConfiguration.Files ← IO.ofExcept (origins.getObjValAs? _ "captured")
      unless captured.contains (external.toString, some policy) do
        throw <| IO.userError "selected external manifest lost its exact path or text in the account"
      IO.println "construction external manifest: incremental audit and exact external account PASS"
      -- A fresh audit relocates a project-contained absolute selection. Qualification consumes
      -- the actual public result and request, rather than a duplicated expected-account model.
      let policies := ["foundation_manifest.json", ".lake/policy.json", "tmp/policy.json",
          ".cache/policy.json", ".regula-scratch/policy.json", "nested/.cache/policy.json",
          ".git/policy.json", "policy.olean"]
      for selected in policies do
        let path := source / selected
        Construction.appendFileWith Construction.observer (path.parent.getD source)
          (path.fileName.getD "policy.json") policy.toUTF8
      let policies := if ← (source / ".CACHE/POLICY.json").pathExists then
          policies ++ [".CACHE/POLICY.json", ".LAKE/policy.json"]
        else policies
      for selected in policies do
        let path := source / selected
        let freshOutput := base / "fresh-manifest-result.json"
        let fresh ← IO.Process.output {
          cmd := binary.toString, cwd := some source,
          args := #["--project", source.toString, "--manifest", path.toString,
            "--json-out", freshOutput.toString],
          env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none)] }
        unless fresh.exitCode == 0 do
          throw <| IO.userError s!"selected fresh manifest {selected} audit failed: {fresh.stdout}{fresh.stderr}"
        let freshResult ← Regula.Checker.ResultProtocol.readDocument freshOutput
        let request : Regula.Website.ExampleRequest ← IO.ofExcept
          (fromJson? (← IO.ofExcept (freshResult.getObjVal? "request")))
        if selected == "foundation_manifest.json" then
          IO.ofExcept (Regula.Checker.RuleExampleQualification.effectiveAccount freshResult request)
        let effective ← IO.ofExcept (freshResult.getObjVal? "effective")
        let root : String ← IO.ofExcept (effective.getObjValAs? _ "root")
        let configuration : Regula.CopyConfiguration.Files ← IO.ofExcept
          (effective.getObjValAs? _ "configuration")
        let actual ← IO.ofExcept (Regula.Checker.Lake.configurationAccount root configuration)
        let requested ← IO.ofExcept
          (Regula.Checker.Lake.configurationAccount request.project request.configuration)
        let expected ← match request.copyConfiguration with
          | none => pure requested
          | some inputs =>
            IO.ofExcept (Regula.Checker.Lake.expectedConfiguration inputs (FilePath.mk root) requested)
        IO.ofExcept (Regula.CopyConfiguration.check (expected, actual))
        unless requested.contains (selected, some policy) && actual.contains (selected, some policy) do
          throw <| IO.userError s!"selected policy {selected} lost its requested path or bytes"
      IO.println "construction selected manifest: fresh audits and exact configuration accounts PASS"
      if ← (source / "VENDOR").isDir then
        -- A deliberate configuration mutation exercises Lake's stored-spelling boundary.
        IO.FS.writeFile (source / "lakefile.lean") (lakefile.replace "vendor" "VENDOR")
        -- Two admitted moves change the stored spelling without treating the case alias as
        -- an independently occupied destination of the observer's replacement operation.
        replacePath (source / "lake-manifest.json") (source / "manifest-renaming")
        replacePath (source / "manifest-renaming") (source / "LAKE-MANIFEST.JSON")
        let folded ← Regula.Checker.Lake.copyProject source (base / "folded") (base / "folded")
        unless !(← (folded.project / "vendor/stale").pathExists) &&
            (← Regula.Filesystem.readFile (folded.project / "lake-manifest.json")) == manifest do
          throw <| IO.userError "case-folded packages or manifest location was not retained correctly"
      IO.println "construction workspace: configured packagesDir and captured manifest PASS"
      for packages in ["vendor", ".lake/packages"] do
        let source := base / (if packages == "vendor" then "owned-vendor" else "owned-default")
        let dependency := (FilePath.mk packages).components ++ ["dep"]
        let lakefile := lakefile.replace "vendor" packages |>.replace "lean_lib Solo"
          ("require dep from \"" ++ packages ++ "/dep\"\nlean_lib Solo")
        let manifest := (Json.mkObj [
          ("version", toJson "1.1.0"), ("name", toJson "construction_control"),
          ("lakeDir", toJson ".lake"), ("packagesDir", toJson packages),
          ("packages", toJson #[Json.mkObj [
            ("name", toJson "dep"), ("scope", toJson ""), ("inherited", toJson false),
            ("configFile", toJson "lakefile.toml"), ("manifestFile", toJson "lake-manifest.json"),
            ("type", toJson "path"), ("dir", toJson (packages ++ "/dep"))]])]).pretty ++ "\n"
        construct source (Construction.layout (toolchain ++ [
          ⟨["lakefile.lean"], .file lakefile.toUTF8⟩,
          ⟨["lake-manifest.json"], .file manifest.toUTF8⟩,
          ⟨["Solo.lean"], .file "/-! Owned layout control. -/\n".toUTF8⟩,
          ⟨dependency ++ ["lakefile.toml"], .file
            "name = \"dep\"\n[[lean_lib]]\nname = \"Dep\"\n".toUTF8⟩,
          ⟨dependency ++ ["Dep.lean"], .file "/-! Owned dependency. -/\n".toUTF8⟩,
          ⟨dependency ++ [".lake", "policy.json"], .file policy.toUTF8⟩,
          ⟨(FilePath.mk packages).components ++ ["stale"], .file "unselected".toUTF8⟩]))
        fixture "git" #["-C", source.toString, "init", "--quiet"]
        let target := source / ".lake/copied"
        let selected := source / packages / "dep/.lake/policy.json"
        let result ← Regula.Checker.Lake.copyProject source target target (policy := some selected)
        let copiedPolicy := Regula.Checker.Lake.relocateConfigurationPath source result.project selected
        unless result.selection.dependencies.any (fun dependency =>
            dependency.package == "dep" && dependency.owned &&
            dependency.dir == result.project / packages / "dep") &&
            (← readFile (result.project / packages / "dep/Dep.lean")) == "/-! Owned dependency. -/\n" &&
            (← readFile copiedPolicy) == policy &&
            !(← (result.project / packages / "stale").pathExists) do
          throw <| IO.userError "owned package copy lost its selected policy or retained stale package state"
        let inventory ← Regula.Checker.Lake.surfaceInventory result.project
        discard <| Regula.Checker.Lake.checkCopiedWorkspace result.root (some result.selection) inventory
      IO.println "construction owned packages: configured and default package layouts PASS"

end Regula.CopyControls
