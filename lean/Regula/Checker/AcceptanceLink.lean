import Regula.Checker.Snapshot
import Regula.Checker.SourceBinding
import RegulaCore.Account
import RegulaCore.BuildReuse

/-! # Two-step acceptance identity link

Link between the two required verification steps: ordinary project acceptance and
the separately timed documentation-fence audit. Each step computes one location-independent
content identity from its own fresh captures of the root sources, configuration,
dependency inputs, Markdown documents and, when given, a Verso documentation library with its
package's inputs (`Documentation.Sources.captureLinked`). Ordinary acceptance records the identity
only
after its accepted success has passed every freshness recheck with exit code 0; the
documentation step refuses unless its own identity is
equal. The SHA-256 digest is computed by the trusted external `shasum` tool; equality
establishes identical captured inputs, not authenticity of the tool or the filesystem.

The verification driver adds a `build` field to the record of its own gate before it promotes it,
when the first step gave its build output to a checkout that had none: the targets of its build,
the digests of every file of its copy and of the build output it moved
(`RegulaVerification.Copy.recordBuild`). The documentation step places the part of that build
output that its claimed build compiles in its copy only as `BuildReuse.reuse` decides
(`placeRetained`). -/
namespace Regula.Checker.AcceptanceLink
open Lean System

/-- Root-relative display of a path inside an isolated copy or the documentation root: `.` for the
root itself. -/
def relative (root : FilePath) (path : String) : String :=
  let stem := root.toString ++ "/"
  if path == root.toString then "."
  else if path.startsWith stem then (path.drop stem.length).toString else path

/-- The captured inputs, with every copy-root or documentation-root path made relative
so that two isolated copies of the same checkout have equal identities: a path below the copied
project `projectRoot` relative to it, and any other path below the real directory of the copy
`copyRoot` (`Lake.ProjectCopy.root`) relative to that, such as a source of an owned path dependency
that holds the project. The copy's `.lake/package-overrides.json` names such a dependency by its
directory in the copy, so that file's text has `copyRoot` replaced by `.`. -/
def identityJson (projectRoot copyRoot docsRoot : FilePath)
    (sources : Array ProducerReport.SourceBinding)
    (configuration : Array (FilePath × Option String))
    (dependencies : Array Snapshot.DependencyObservation)
    (documents : Array RegulaPolicy.SourceSnapshot) : Json :=
  let rel (path : String) : String :=
    let below := relative projectRoot path
    if below != path then below else relative copyRoot path
  Json.mkObj [
    ("toolchain", toJson (Lean.versionString, Lean.githash)),
    ("sources", toJson (sources.map fun source =>
      (source.moduleName.toString, rel source.path, source.content))),
    -- The copy writes its own `.lake/package-overrides.json` (`Lake.relocateDependencies`), whose
    -- entries name the copied owned dependencies by their directories in the copy.
    ("configuration", toJson (configuration.map fun (path, text) =>
      let shown := rel path.toString
      (shown, if shown == ".lake/package-overrides.json" then
        text.map (String.replace · copyRoot.toString ".") else text))),
    ("dependencies", toJson (dependencies.map fun dependency => Json.mkObj [
      ("package", toJson dependency.package), ("root", toJson (rel dependency.root.toString)),
      ("revision", toJson dependency.revision), ("dirty", toJson dependency.dirty),
      ("owned", toJson dependency.owned),
      ("sources", toJson (dependency.sourceCaptures.map fun (name, path, canonical, text) =>
        (name.toString, rel path, rel canonical, text))),
      ("configuration", toJson (dependency.configurationCaptures.map fun (path, entry) =>
        (rel path, entry.map fun ((canonical, bytes) : String × ByteArray) =>
          (rel canonical, bytes.data.toList.map UInt8.toNat))))])),
    -- Markdown by its path below `docsRoot`; any other document (a Verso source) by its path
    -- below the repository, the parent of `docsRoot`.
    ("documents", toJson (documents.map fun document =>
      let below := relative docsRoot document.uri
      (if below != document.uri then below else relative
                                                 (docsRoot.parent.getD docsRoot) document.uri,
        document.source)))]

/-- SHA-256 of the compact identity bytes, computed by the external `shasum` tool. -/
def identity (scratch projectRoot copyRoot docsRoot : FilePath)
    (sources : Array ProducerReport.SourceBinding)
    (configuration : Array (FilePath × Option String))
    (dependencies : Array Snapshot.DependencyObservation)
    (documents : Array RegulaPolicy.SourceSnapshot) : IO String := do
  let path := scratch / "acceptance-link-identity.json"
  IO.FS.writeFile path
    (identityJson projectRoot copyRoot docsRoot sources configuration dependencies
      documents).compress
  try sha256File scratch path finally Regula.Filesystem.removePath .file path

/-- Replace any earlier record before the ordinary audit starts. A run that stops before its audit
records why as `reason` (`AxiomGate.refuseWithoutTaskManager`). -/
def invalidate (path : FilePath) (reason : Option String := none) : IO Unit :=
  writeJson path <| Json.mkObj <|
    [("schemaVersion", toJson (1 : Nat)), ("status", .str "incomplete")] ++
      (reason.map fun reason => [("reason", Json.str reason)]).getD []

/-- The identity of one accepted run's captured inputs, computed before its success line
and held, unrecorded, until the run's outer freshness recheck has passed. -/
structure Pending where
  /-- The lowercase hexadecimal SHA-256 of the run's input identity, from `identity`. -/
  digest : String
  /-- The run's account, whose accepted jobs `record` writes beside the digest. -/
  account : Account
  /-- Where the build output that the run inspected came from: `isolatedCopy` for a copy the
  audit made, `driverCopy` for a copy that the verification driver made
  (`AxiomGate.Origin.spelling`). -/
  origin : String

/-- Written only after accepted ordinary success. It cannot be called without a `Pending`, whose
`Account` is a projection of some `AcceptedRun`; that it is this run's account, and that
`digest` matches it, is the caller's binding. -/
def record (path : FilePath) (pending : Pending) : IO Unit :=
  writeJson path (Json.mkObj [("schemaVersion", toJson (1 : Nat)), ("status", .str "accepted"),
      ("identity", .str pending.digest), ("acceptedJobs", toJson pending.account.val.jobs),
      ("origin", .str pending.origin)])

/-- Refuse unless ordinary acceptance recorded an accepted success over equal inputs.
The `status: accepted` record lives in a writable `tmp/` file and is trusted as written
by ordinary acceptance, like the `shasum` and filesystem observations behind its
identity; a process that forges it is outside the assurance boundary (standard §7). -/
def require (path : FilePath) (digest : String) : IO Unit := do
  unless ← path.pathExists do
    throw <| IO.userError s!"acceptance link missing: run ordinary acceptance first ({path})"
  let value ← readJson path
  unless (value.getObjValAs? Nat "schemaVersion").toOption == some 1 &&
      (value.getObjValAs? String "status").toOption == some "accepted" do
    throw <| IO.userError s!"acceptance link is not an accepted ordinary result: {path}"
  unless (value.getObjValAs? String "identity").toOption == some digest do
    throw <| IO.userError "acceptance link identity differs: documentation inputs are not the \
      accepted ordinary inputs"

/-! ## Reuse of the first step's build

The documentation step's side of `Regula.Checker.BuildReuse`: it reads the record of the first
step's build from the acceptance link, takes the digests the decision compares, and places the
first step's build output in its copy only when `BuildReuse.reuse` accepts. -/

/-- Whether `text` is a SHA-256 digest as `shasum` prints it: 64 lowercase hexadecimal digits. -/
def hexDigest (text : String) : Bool :=
  text.length == 64 && text.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- The SHA-256 of each of `paths`, each relative to `dir` and written with `/`, by the external
`shasum -a 256` run in `dir` on at most 200 paths at a time. Each path is given as `./` and the
path, since `shasum` reads standard input for the operand `-`, and a path below `dir` stays the same
file with that prefix. For each file `shasum` prints the digest, two spaces and the operand; any other
line in a path's place fails, so a path that `shasum` would escape fails. The record keeps the path
without the prefix. The verification driver writes this a second time
(`RegulaVerification.digests`), since it imports only the toolchain.

Assumes: `shasum -a 256` (the Perl `Digest::SHA` script on macOS and Linux) prints, in text mode,
one line per file, in the order of its arguments: the lowercase digest, two spaces and the name as
given, with a leading backslash when the name holds a backslash or a newline, and that it reads
standard input only for an operand that is `-` exactly. Trusted. -/
def digests (dir : FilePath) (paths : List String) : IO (List BuildReuse.Digest) := do
  let batches := paths.foldl (fun (batches : Array (Array String)) path =>
    match batches.back? with
    | some last => if last.size < 200 then batches.pop.push (last.push path)
        else batches.push #[path]
    | none => #[#[path]]) #[]
  let mut result := #[]
  for batch in batches do
    let run ← runProcess dir "shasum" (#["-a", "256", "--"] ++ batch.map ("./" ++ ·))
    let lines := (run.stdout.splitOn "\n").filter (!·.isEmpty)
    unless run.succeeded && lines.length == batch.size do
      throw <| IO.userError s!"shasum gave no digest of each file: {run.output}"
    for (path, line) in batch.toList.zip lines do
      let digest := (line.take 64).toString
      unless hexDigest digest && line == digest ++ "  ./" ++ path do
        throw <| IO.userError s!"shasum gave an unexpected line for {path}: {line}"
      result := result.push (path, digest)
  return result.toList

/-- Every regular file below `root`, outside every directory named `.lake` below `root`, by its
path relative to `root` written with `/`. Only the relative path is tested for `.lake`: `root`
itself lies below a `.lake` when it is a copy in a scratch directory. -/
def treeFiles (root : FilePath) : IO (List String) := do
  let prefixLength := root.normalize.components.length
  let enter (path : FilePath) : IO Bool := pure (path.fileName != some ".lake")
  let mut files := #[]
  for path in ← root.walkDir enter do
    let relative := path.normalize.components.drop prefixLength
    if relative.contains ".lake" then continue
    if (← path.symlinkMetadata).type == .file then
      files := files.push ("/".intercalate relative)
  return files.toList

/-- The parts of an acceptance link that `BuildReuse.reuse` reads. A `build` field that does not
have the shape the driver writes reads as no build. -/
def reuseLink (value : Json) : BuildReuse.Link :=
  let text (key : String) := (value.getObjValAs? String key).toOption.getD ""
  { accepted := (value.getObjValAs? Nat "schemaVersion").toOption == some 1 &&
      text "status" == "accepted"
    identity := text "identity"
    origin := text "origin"
    build := (value.getObjVal? "build").toOption.bind fun build => Except.toOption do
      return { targets := ← build.getObjValAs? (List String) "targets"
               tree := ← build.getObjValAs? (List BuildReuse.Digest) "tree"
               artifacts := ← build.getObjValAs? (List BuildReuse.Digest) "artifacts" } }

/-- The path of the module `name` below a build directory's `lib/lean` or `ir`, without extension and
written with `/`: its components in order, as `Lean.modToFilePath` joins them. -/
def modulePath (name : Name) : String :=
  "/".intercalate (name.components.map (·.toString (escape := false)))

/-- Why `BuildReuse.reuse` refused, for the step's output; the decision itself is `reuse`. -/
def refusal (link : BuildReuse.Link) (run : BuildReuse.Run) : String :=
  match link.build with
  | none => "the acceptance link records no build of the first acceptance step"
  | some build =>
    if !(link.accepted && link.identity == run.identity && link.origin == "driverCopy") then
      "the acceptance link is not an accepted record of the first acceptance step's own copy"
    else if !run.targets.all build.targets.contains then
      "the first acceptance step's build does not name every claimed target"
    else if !build.artifacts.all (BuildReuse.below ·.1) then
      "a recorded artifact path leaves .lake/build"
    else if !run.modules.all BuildReuse.plain then
      "a module name of the root package has a component that holds a dot"
    else if !build.tree.isPerm run.tree then
      "a file of this copy differs from the first acceptance step's copy"
    else "the checkout's .lake/build does not hold the recorded files of the claimed build's \
      modules with their recorded digests"

/-- Place the first step's build output of the modules of `closure` in the documentation step's
`copy`, which has no build output, when `BuildReuse.reuse` accepts, and return how many files it
placed; otherwise return why not, with the copy as it was. `modules` is the module path
(`modulePath`) of every module of the root package, and `closure` that of each root-package module
the claimed build compiles. The step calls it only after `require` admitted `link`. The recorded
artifacts of `closure`'s modules (`BuildReuse.selected`) are copied from `repo`'s `.lake/build` into a new staging directory in
`scratch`, outside the copy, and the digests compared are those of the staged files and of the
copy's own files outside `.lake`. Only after the decision is each staged file moved to its place in
the copy's `.lake/build`, which must not exist, through the filesystem observer
(`Regula.Filesystem.replacePath`). Both are in the scratch directory of the run, so each move is
within one file system. Any failure on the way is a refusal, and a move that fails first removes
the copy's `.lake/build` through the observer (`Regula.Filesystem.removePath`): the step then
builds as without a link. -/
def placeRetained (repo copy scratch link : FilePath) (identity : String)
    (targets modules closure : List String) : IO (Except String Nat) := do
  let attempt : IO (Except String Nat) := do
    let record := reuseLink (← readJson link)
    let tree ← digests copy (← treeFiles copy)
    let staging := scratch / "retained-build"
    let staged ← match record.build with
      | some build =>
        if build.artifacts.all (BuildReuse.below ·.1) then
          let mut present := #[]
          for (path, _) in BuildReuse.selected closure build.artifacts do
            let source := repo / ".lake" / "build" / path
            let regular ← match ← source.symlinkMetadata.toBaseIO with
              | .ok metadata => pure (metadata.type == .file)
              | .error _ => pure false
            unless regular do continue
            let target := staging / path
            Regula.Filesystem.copyFile source target
            present := present.push path
          digests staging present.toList
        else pure []
      | none => pure []
    let run : BuildReuse.Run := { identity, targets, modules, closure, tree, staged }
    unless BuildReuse.reuse record run do return .error (refusal record run)
    let target := copy / ".lake" / "build"
    unless (← (target.symlinkMetadata.toBaseIO)) matches .error _ do
      return .error s!"{target} already exists"
    try
      for (path, _) in staged do
        let destination := target / path
        if let some parent := destination.parent then IO.FS.createDirAll parent
        Regula.Filesystem.replacePath (staging / path) destination
    catch error =>
      Regula.Filesystem.removePath .directory target
      throw error
    return .ok staged.length
  match ← attempt.toBaseIO with
  | .ok outcome => return outcome
  | .error error => return .error s!"the first acceptance step's build could not be placed: {error}"

end Regula.Checker.AcceptanceLink
