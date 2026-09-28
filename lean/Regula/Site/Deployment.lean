import Lean

/-! # Deployment gate and deployed rule-reference verification

Gates and verifies publication of the artifact the CI `site` job validated. It imports only
Lean's core so the deployment jobs can run it with the pinned toolchain alone:

```text
lean --run lean/Regula/Site/Deployment.lean gate ARTIFACT_DIR    # before uploading for Pages
lean --run lean/Regula/Site/Deployment.lean verify ARTIFACT_DIR  # after deploying
```

`gate` requires the artifact to be a clean build of `GITHUB_SHA`, so a build from uncommitted
changes or of another commit is never published, and requires the recorded `publishable` to be
`true`: the site build computes it with the proved `Regula.publishable` from how it obtained each
release edition (every one from its release asset, none rendered from source), and its artifact
check requires `build.json` to be exactly that record. The privileged deploy job separately refuses
unless `main` is still at `GITHUB_SHA`, so a re-run of an older run cannot publish over a newer
revision.

`verify` requires `REGULA_PAGE_URL` to be the artifact's recorded site, the live `build.json`
to equal the artifact's bytes (retrying while the deployment propagates), the site root
`index.html`, the home page of every edition listed in `build.json`, every rule page of the
development edition and the `build.json` of every release edition to be served with the
artifact's exact bytes, and an unpublished route to be answered with HTTP 404 and the artifact's
`404.html`. It compares only those files.

## Boundaries

These are observations at one time through `curl`, not proofs: GitHub, Pages, its CDN and the
network are external. Requests carry a per-attempt query string so that a cached copy is
unlikely to satisfy the comparison; whether the CDN keys on it is not established.
-/

namespace Regula.Site.Deployment
open Lean System

private def fail {α : Type} (message : String) : IO α := throw <|
    IO.userError s!"deployment verification: {message}"

/-- Fetch `url` into `path`; returns the HTTP status (0 when no response). -/
def fetch (url : String) (path : FilePath) : IO Nat := do
  let out ← IO.Process.output
      { cmd := "curl", args := #["--silent", "--show-error", "--max-time", "60",
    "--output", path.toString, "--write-out", "%{http_code}", url] }
  return out.stdout.trimAscii.toString.toNat?.getD 0

private def field (j : Json) (key : String) : IO Json := IO.ofExcept (j.getObjVal? key)
private def str (j : Json) (key : String) : IO String := do IO.ofExcept (← field j key).getStr?

private def env (name : String) : IO String := do
  match ← IO.getEnv name with
  | some v => if v.isEmpty then fail s!"{name} is empty" else pure v
  | none => fail s!"{name} is not set"

/-- Refuse to publish unless the artifact is a clean build of `GITHUB_SHA` whose recorded
`publishable` (the site build's value of `Regula.publishable`) is `true`. -/
def gate (artifact : FilePath) : IO Unit := do
  let build ← IO.ofExcept (Json.parse (← IO.FS.readFile (artifact / "build.json")))
  let sha ← env "GITHUB_SHA"
  unless (← field build "dirty") == .bool false do
      fail "the artifact was built from uncommitted changes"
  unless (← str build "revision") == sha do
      fail s!"the artifact is for {← str build "revision"}, not {sha}"
  unless (← field build "publishable") == .bool true do
      fail "a release edition was rendered from source instead of taken from its release asset"
  IO.println s!"deployment gate: PASS (clean artifact of {sha})"

/-- Post-deployment observation of the site at `pageUrl`: the artifact must be a clean build
for that site; its `build.json` must be served live (polled up to 20 times, 15 seconds
apart); the site root `index.html`, the home page of every edition, every rule page of the
development edition and the `build.json` of every release edition must be served with the
artifact's bytes; and an unpublished route must return 404 with the artifact's `404.html`. Any
difference fails. -/
def run (artifact : FilePath) (pageUrl : String) : IO Unit := do
  let recorded ← IO.FS.readBinFile (artifact / "build.json")
  let build ← IO.ofExcept (Json.parse (← IO.FS.readFile (artifact / "build.json")))
  let site ← str build "site"
  let revision ← str build "revision"
  let pageUrl := if pageUrl.endsWith "/" then pageUrl else pageUrl ++ "/"
  unless pageUrl == site do fail s!"deployed at {pageUrl}, but the artifact is for {site}"
  unless (← field build "dirty") == .bool false do
      fail "the artifact was built from uncommitted changes"
  let scratch := artifact.parent.getD "." / "deployment-check"
  IO.FS.createDirAll scratch
  let probe := s!"?regula-deployment={revision}"
  -- The deployment is atomic; wait until the live identity is this artifact's.
  let mut matched := false
  for attempt in [1:21] do
    let status ← fetch (site ++ "build.json" ++ probe ++ s!"-{attempt}") (scratch / "build.json")
    if status == 200 then
      if (← IO.FS.readBinFile (scratch / "build.json")) == recorded then
        matched := true
        break
    IO.println s!"attempt {attempt}: live build.json is not this artifact yet (HTTP {status}); \
      waiting"
    IO.sleep 15000
  unless matched do fail s!"the live site does not serve the artifact of {revision}"
  let editions ← (← IO.ofExcept ((← field build "editions").getArr?)).toList.mapM fun e =>
    IO.ofExcept e.getStr?
  let rules ← IO.ofExcept ((← field build "rules").getArr?)
  let routes ← rules.toList.mapM fun rule => str rule "route"
  let files := "index.html" :: editions.map (· ++ "index.html") ++
    routes.map ("dev/" ++ · ++ "index.html") ++
    (editions.filter (· != "dev/")).map (· ++ "build.json")
  for file in files do
    let status ← fetch (site ++ file ++ probe) (scratch / "file")
    unless status == 200 do fail s!"{file}: HTTP {status}"
    unless (← IO.FS.readBinFile (scratch / "file")) == (← IO.FS.readBinFile (artifact / file)) do
      fail s!"{file}: live bytes differ from the validated artifact"
  let status ← fetch (site ++ "v/0.0.0-unpublished/rules/RG1001/" ++ probe)
      (scratch / "missing.html")
  unless status == 404 do fail s!"unpublished route answered HTTP {status}, expected 404"
  unless (← IO.FS.readBinFile (scratch / "missing.html")) ==
      (← IO.FS.readBinFile (artifact / "404.html")) do
    fail "unpublished route did not serve the artifact's not-available page"
  IO.FS.removeDirAll scratch
  IO.println s!"deployment verification: PASS ({site} serves the artifact of {revision}: \
    build.json and {files.length} pages and edition records of {editions}, not-available page); \
    an observation at this time, not a guarantee of availability"

end Regula.Site.Deployment

/-- Command line of `lean --run lean/Regula/Site/Deployment.lean`: `gate ARTIFACT_DIR` runs the
deployment gate; `verify ARTIFACT_DIR` checks the live site at `REGULA_PAGE_URL`. Returns 2 on a
usage error or a missing `REGULA_PAGE_URL`. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["gate", artifact] => Regula.Site.Deployment.gate artifact; return 0
  | ["verify", artifact] =>
    let some pageUrl ← IO.getEnv "REGULA_PAGE_URL" | IO.eprintln
                                                      "REGULA_PAGE_URL is not set"; return 2
    Regula.Site.Deployment.run artifact pageUrl; return 0
  | _ => IO.eprintln "usage: lean --run lean/Regula/Site/Deployment.lean (gate ARTIFACT_DIR | \
    verify ARTIFACT_DIR)"; return 2
