import Regula.Site.Support
import RegulaCore.SiteDocs
import RegulaCore.SiteTheme
import Regula.Filesystem
import Lake.Load.Manifest

/-! # Rule-reference site builder

Operational builder of the published rule reference. It generates the Verso sources from the
registry (`RegulaCore.Rule`), with each rule's example pair, and the rule explanations
(`RegulaCore.Guide`), renders them with the pinned Verso
package in `website/`, assembles the GitHub Pages artifact with the permanent edition of every
release and checks it.

## Main declarations

- `remoteTags`, `tagState`, `downloadRelease`, `extractRelease`: the observations the release
  decisions (`labelAdmitted`, `releaseSource`, `publishable`) take: which commit, if any, a
  release tag names, whether a release's GitHub asset exists, and the permanent copy it holds.
- `build`: generation, Verso rendering, assembly and `checkArtifact`.

## Boundaries

Process, filesystem, Git, network and Verso observations are trusted operational inputs. The pure
decisions (editions, releases and routes, escaping, filters, diffs, links, page structure, colour
contrast) are proved in `RegulaCore.Edition`, `RegulaCore.Site`, `RegulaCore.SitePage`,
`RegulaCore.SiteDocs` and `RegulaCore.SiteTheme`.
The builder removes nothing: it refuses when an earlier build's output is present
(`Regula.Site.Build.requireFresh`), so a symbolic link at a path that it would write stays as it is.
-/

namespace Regula.Site.Build

open Lean System Regula.Site

/-- The pinned Verso revision of the website package: the commit of the last Git entry named
`verso` among the entries of its manifest and then those of its package overrides file, each read
by Lake's own reader, from which Lake's load of the website's workspace materializes `verso`
(`Lake/Load/Resolve.lean:598-616` at v4.35.0). A website without a manifest, or one that
materializes `verso` from no Git entry, is refused. -/
def versoRevision (root : FilePath) : IO String := do
  let dir := root / "website"
  let some manifest ← Lake.Manifest.load? (dir / "lake-manifest.json")
    | throw <| IO.userError s!"website: {dir}/lake-manifest.json is absent"
  let overrides ← Lake.Manifest.tryLoadEntries (dir / ".lake" / "package-overrides.json")
  match ((manifest.packages ++ overrides).findRev? (·.name == `verso)).map (·.src) with
  | some (Lake.PackageEntrySrc.git _ rev _ _) => return rev
  | _ => throw <| IO.userError s!"website: {dir} materializes no Git package verso"

/-- Whether the object `j` has the field `key` with the value `expected`. -/
private def has (j : Json) (key : String) (expected : Json) : Bool :=
  (j.getObjVal? key).toOption == some expected

private def git (root : FilePath) (args : Array String) : IO String := do
  let result ← run root "git" args
  requireChecks [⟨s!"git {args}: {result.stderr}", result.exitCode == 0⟩]
  return result.stdout

/-- Build identity: the checked-out commit, whether the worktree is modified, the toolchain
and Regula's version (`Regula.installed`). -/
def identity (root : FilePath) : IO Identity := do
  let head := (← git root #["rev-parse", "HEAD"]).trimAscii.toString
  let some revision := Commit.parse? head | throw <|
                                             IO.userError s!"not a commit identifier: {head}"
  let dirty := !(← git root #["status", "--porcelain", "--untracked-files=normal"]).isEmpty
  return { revision, dirty, toolchain := Lean.versionString, producerVersion := installed.spelling,
           versoRevision := ← versoRevision root }

private def writeModule (dir : FilePath) (name : String) (content : String) : IO Unit := do
  let path := dir / (System.FilePath.mk ((name.replace "." "/") ++ ".lean"))
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path content

/-- Exact relative file names and bytes of a tree. -/
def snapshotTree (root : FilePath) : IO (List (String × ByteArray)) := do
  let root ← IO.FS.realPath root
  let mut files := []
  for path in ← Regula.Filesystem.Construction.walkDirectory root do
    if !(← Regula.Filesystem.isDirectory path) then
      let relative := String.intercalate "/" (path.components.drop root.components.length)
      files := (relative, ← IO.FS.readBinFile path) :: files
  return files.mergeSort (fun a b => a.1 ≤ b.1)

/-- Write each relative file name and its bytes under `destination`, creating parent
directories; files already there that are not listed are left in place. -/
def writeTree (destination : FilePath) (files : List (String × ByteArray)) : IO Unit := do
  for (relative, bytes) in files do
    let path := destination / relative
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile path bytes

/-- The name of the GitHub release asset that holds the permanent copy of release `v`'s edition:
a gzip-compressed tar archive of that edition's files, paths relative to its root. -/
def releaseAsset (v : ReleaseVersion) : String := "regula-site-" ++ v.spelling ++ ".tar.gz"

/-- The download URL of `releaseAsset v`, attached to the release tagged `v<version>`. -/
def releaseAssetUrl (v : ReleaseVersion) : String :=
  repository ++ "/releases/download/v" ++ v.spelling ++ "/" ++ releaseAsset v

/-- The scratch directory of a build: what it renders, the release copies that it fetches and the
artifact before its check. A build refuses when it is present and leaves it behind. -/
def siteScratch (root : FilePath) : FilePath := root / "tmp/site-build"

/-- Scratch directory of the fetched release copies; `<version>/` holds each extracted edition. -/
def releaseDirectory (root : FilePath) : FilePath := siteScratch root / "releases"

/-- The commit that tag reference `ref` names in `git ls-remote` output: its peeled `^{}` line
when the tag is annotated, otherwise its own line. -/
def taggedCommit (listing ref : String) : Option String :=
  let entries := (listing.splitOn "\n").filterMap fun line => match line.splitOn "\t" with
    | [commit, name] => some (name, commit)
    | _ => none
  entries.lookup (ref ++ "^{}") <|> entries.lookup ref

/-- The repository's tags as `git ls-remote` lists them. They are read from the repository,
because CI checkouts are shallow and have no tags; a failed read refuses. -/
def remoteTags (root : FilePath) : IO String := git root #["ls-remote", "--tags", repository]

/-- The state of tag `v<version>` in `listing` (`remoteTags`) relative to `head`: absent, naming
`head`, or naming another commit. -/
def tagState (listing : String) (v : ReleaseVersion) (head : Commit) : TagState :=
  match taggedCommit listing ("refs/tags/v" ++ v.spelling) with
  | none => .absent
  | some commit => if commit == head.val then .head else .other

/-- Download release `v`'s asset into `releaseDirectory` and return whether it exists: HTTP 200
is present and 404 absent; any other answer or a failed transfer refuses. -/
def downloadRelease (root : FilePath) (v : ReleaseVersion) : IO Bool := do
  IO.FS.createDirAll (releaseDirectory root)
  let archive := releaseDirectory root / releaseAsset v
  let fetched ← run root "curl" #["--silent", "--show-error", "--location", "--max-time", "120",
    "--output", archive.toString, "--write-out", "%{http_code}", releaseAssetUrl v]
  requireChecks [⟨s!"release {v.spelling}: {releaseAssetUrl v}\n{fetched.stderr}",
    fetched.exitCode == 0⟩]
  match fetched.stdout.trimAscii.toString with
  | "200" => return true
  | "404" => return false
  | status => throw <| IO.userError s!"release {v.spelling}: {releaseAssetUrl v} answered HTTP \
      {status}"

/-- Extract the downloaded permanent copy of release `v`'s edition and return its files. Refuses
an unreadable archive, a symbolic link, a copy without a home page, and a copy whose `build.json`
does not record a clean build of `v` for this site. -/
def extractRelease (root : FilePath) (v : ReleaseVersion) : IO (List (String × ByteArray)) := do
  let dir := releaseDirectory root / v.spelling
  IO.FS.createDirAll dir
  let archive := releaseDirectory root / releaseAsset v
  let extracted ← run root "tar" #["-xzf", archive.toString, "-C", dir.toString]
  requireChecks [⟨s!"release {v.spelling}: extract {releaseAsset v}\n{extracted.stderr}",
    extracted.exitCode == 0⟩]
  for path in ← Regula.Filesystem.Construction.walkDirectory dir do
    requireChecks [⟨s!"release {v.spelling}: {path} is a symbolic link",
      (← path.symlinkMetadata).type != .symlink⟩]
  let files ← snapshotTree dir
  let some (_, recorded) := files.find? (·.1 == "build.json")
    | throw <| IO.userError s!"release {v.spelling}: the copy has no build.json"
  let build ← IO.ofExcept (Json.parse (← IO.ofExcept
    ((String.fromUTF8? recorded).elim (.error "build.json is not UTF-8") .ok)))
  requireChecks [
    ⟨s!"release {v.spelling}: build.json records Regula {v.spelling}",
      has build "producerVersion" (.str v.spelling)⟩,
    ⟨s!"release {v.spelling}: build.json records a clean build", has build "dirty" (.bool false)⟩,
    ⟨s!"release {v.spelling}: build.json records this site", has build "site" (.str siteBase)⟩,
    ⟨s!"release {v.spelling}: the copy has a home page", files.any (·.1 == "index.html")⟩]
  return files

/-- Generate every Verso module of the manual into `website/Generated`, with the site
stylesheet (`Regula.Site.stylesheet`) as `website/Generated/regula.css`, which the website
package copies to each edition's root. -/
def generate (root : FilePath) (ident : Identity) : IO Unit := do
  let out := root / "website/Generated"
  let top := root / "website/Generated.lean"
  IO.FS.writeFile top (← IO.ofExcept (homePage ident))
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "regula.css") stylesheet
  let dir := root / "website"
  writeModule dir "Generated.Rules" (← IO.ofExcept (indexPage ident))
  writeModule dir "Generated.Enforcement" (← IO.ofExcept (enforcementPage ident))
  writeModule dir "Generated.Coverage" (← IO.ofExcept (coveragePage ident))
  writeModule dir "Generated.Versions" (← IO.ofExcept (versionsPage ident))
  writeModule dir "Generated.Credits" (← IO.ofExcept (creditsPage ident))
  for id in RuleId.all do
    for p in (guide id).repositoryPaths do
      requireChecks
          [⟨s!"{id.spelling}: cited repository path exists: {p}",
            ← Regula.Filesystem.isPresent (root / p)⟩]
    -- Each cited section of the standard, on its page in the same edition (`Clause.route` is
    -- relative to the edition root, like every generated link); the artifact link check
    -- requires the anchor to exist.
    let clauses := (descriptor id).normativeClauses.map fun c =>
      ({ label := c.label, url := c.route } : Regula.Site.Clause)
    writeModule dir (ruleModule id) (← IO.ofExcept (rulePage ident id clauses))

end Regula.Site.Build
