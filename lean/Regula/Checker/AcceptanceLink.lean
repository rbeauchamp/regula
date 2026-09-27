import Regula.Checker.Snapshot
import Regula.Checker.SourceBinding
import RegulaCore.Account

/-! # Two-step acceptance identity link

Link between the two required verification steps: ordinary project acceptance and
the separately timed documentation-fence audit. Each step computes one location-independent
content identity from its own fresh captures of the root sources, configuration,
dependency inputs, Markdown documents and, when given, a Verso documentation library with its
package's inputs (`Documentation.Sources.captureLinked`). Ordinary acceptance records the identity only
after its accepted success has passed every freshness recheck with exit code 0; the
documentation step refuses unless its own identity is
equal. The SHA-256 digest is computed by the trusted external `shasum` tool; equality
establishes identical captured inputs, not authenticity of the tool or the filesystem. -/
namespace Regula.Checker.AcceptanceLink
open Lean System

/-- Root-relative display of a path inside an isolated copy or the documentation root. -/
def relative (root : FilePath) (path : String) : String :=
  let stem := root.toString ++ "/"
  if path.startsWith stem then (path.drop stem.length).toString else path

/-- The captured inputs, with every copy-root or documentation-root path made relative
so that two isolated copies of the same checkout have equal identities. -/
def identityJson (projectRoot docsRoot : FilePath)
    (sources : Array ProducerReport.SourceBinding)
    (configuration : Array (FilePath × Option String))
    (dependencies : Array Snapshot.DependencyObservation)
    (documents : Array RegulaPolicy.SourceSnapshot) : Json :=
  let rel := relative projectRoot
  Json.mkObj [
    ("toolchain", toJson (Lean.versionString, Lean.githash)),
    ("sources", toJson (sources.map fun source =>
      (source.moduleName.toString, rel source.path, source.content))),
    ("configuration", toJson (configuration.map fun (path, text) => (rel path.toString, text))),
    ("dependencies", toJson (dependencies.map fun dependency => Json.mkObj [
      ("package", toJson dependency.package), ("root", toJson (rel dependency.root.toString)),
      ("revision", toJson dependency.revision), ("dirty", toJson dependency.dirty),
      ("sources", toJson (dependency.sourceCaptures.map fun (name, path, canonical, text) =>
        (name.toString, rel path, rel canonical, text))),
      ("configuration", toJson (dependency.configurationCaptures.map fun (path, entry) =>
        (rel path, entry.map fun ((canonical, bytes) : String × ByteArray) =>
          (rel canonical, bytes.data.toList.map UInt8.toNat))))])),
    -- Markdown by its path below `docsRoot`; any other document (a Verso source) by its path
    -- below the repository, the parent of `docsRoot`.
    ("documents", toJson (documents.map fun document =>
      let below := relative docsRoot document.uri
      (if below != document.uri then below else relative (docsRoot.parent.getD docsRoot) document.uri,
        document.source)))]

/-- SHA-256 of the compact identity bytes, computed by the external `shasum` tool. -/
def identity (scratch projectRoot docsRoot : FilePath)
    (sources : Array ProducerReport.SourceBinding)
    (configuration : Array (FilePath × Option String))
    (dependencies : Array Snapshot.DependencyObservation)
    (documents : Array RegulaPolicy.SourceSnapshot) : IO String := do
  let path := scratch / "acceptance-link-identity.json"
  IO.FS.writeFile path
    (identityJson projectRoot docsRoot sources configuration dependencies documents).compress
  let result ← runProcess scratch "shasum" #["-a", "256", path.toString]
  IO.FS.removeFile path
  let digest := (result.stdout.splitOn " ").head!
  unless result.succeeded && digest.length == 64 &&
      digest.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
    throw <| IO.userError s!"acceptance link digest unavailable: {result.output}"
  return digest

/-- Replace any earlier record before the ordinary audit starts. -/
def invalidate (path : FilePath) : IO Unit :=
  writeJson path (Json.mkObj [("schemaVersion", toJson (1 : Nat)), ("status", .str "incomplete")])

/-- The identity of one accepted run's captured inputs, computed before its success line
and held, unrecorded, until the run's outer freshness recheck has passed. -/
structure Pending where
  /-- The lowercase hexadecimal SHA-256 of the run's input identity, from `identity`. -/
  digest : String
  /-- The run's account, whose accepted jobs `record` writes beside the digest. -/
  account : Account

/-- Written only after accepted ordinary success. It cannot be called without a `Pending`, whose
`Account` is a projection of some `AcceptedRun`; that it is this run's account, and that
`digest` matches it, is the caller's binding. -/
def record (path : FilePath) (pending : Pending) : IO Unit :=
  writeJson path (Json.mkObj [("schemaVersion", toJson (1 : Nat)), ("status", .str "accepted"),
    ("identity", .str pending.digest), ("acceptedJobs", toJson pending.account.val.jobs)])

/-- Refuse unless ordinary acceptance recorded an accepted success over equal inputs.
The `status: accepted` record lives in a writable `tmp/` file and is trusted as written
by ordinary acceptance, like the `shasum` and filesystem observations behind its
identity; a process that forges it is outside the assurance boundary (standard §8). -/
def require (path : FilePath) (digest : String) : IO Unit := do
  unless ← path.pathExists do
    throw <| IO.userError s!"acceptance link missing: run ordinary acceptance first ({path})"
  let value ← readJson path
  unless (value.getObjValAs? Nat "schemaVersion").toOption == some 1 &&
      (value.getObjValAs? String "status").toOption == some "accepted" do
    throw <| IO.userError s!"acceptance link is not an accepted ordinary result: {path}"
  unless (value.getObjValAs? String "identity").toOption == some digest do
    throw <| IO.userError "acceptance link identity differs: documentation inputs are not the accepted ordinary inputs"

end Regula.Checker.AcceptanceLink
