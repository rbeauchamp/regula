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
release edition (every one from its release asset, none rendered from source and none a preview
of a release not yet published), and its artifact check requires `build.json` to be exactly that
record. The privileged deploy job separately refuses
unless `main` is still at `GITHUB_SHA`, so a re-run of an older run cannot publish over a newer
revision.

`verify` requires `REGULA_PAGE_URL` to be the artifact's recorded site, the live `build.json`
to equal the artifact's bytes (retrying while the deployment propagates), the site root
`index.html`, the home page of every edition listed in `build.json`, every rule page of the
development edition, the `build.json` of every release edition and the page of every stable
route listed in `build.json` to be served with the
artifact's exact bytes, and an unpublished route to be answered with HTTP 404 and the artifact's
`404.html`. It compares only those files.

## Boundaries

These are observations at one time through `curl`, not proofs: GitHub, Pages, its CDN and the
network are external. Requests carry a per-attempt query string so that a cached copy is
unlikely to satisfy the comparison; whether the CDN keys on it is not established.

`verify` reads each fetched page from `curl`'s standard output, so it writes and removes no
file, under the assumption that `fetch` states.
-/

namespace Regula.Site.Deployment
open Lean System

private def fail {α : Type} (message : String) : IO α := throw <|
    IO.userError s!"deployment verification: {message}"

/-- The variables of this process that `fetch` passes to curl when they are set. -/
def curlEnvironment : Array String :=
  #["PATH", "HTTPS_PROXY", "https_proxy", "HTTP_PROXY", "http_proxy", "ALL_PROXY", "all_proxy",
    "NO_PROXY", "no_proxy", "SSL_CERT_FILE", "SSL_CERT_DIR", "CURL_CA_BUNDLE"]

/-- Fetch `url`: return the HTTP status (0 when no response) and the bytes of the body. curl
writes the body and then the three digits of the status to its standard output, which this
process reads from a pipe. curl starts with an environment that has only the variables of
`curlEnvironment` that are set in this process: it runs as the utility of `env -i NAME=VALUE ...`,
which by POSIX `env` (`-i`) gets exactly the environment its assignments give. The child is not
spawned with `inheritEnv := false`, under which the Lean 4.34.1 runtime on macOS crashes the child
(exit 139) before it runs curl. The variables are `PATH`, by which the child finds curl, the proxy
variables `HTTPS_PROXY`, `HTTP_PROXY`, `ALL_PROXY`, `NO_PROXY` and their lowercase forms, and the
certificate variables `SSL_CERT_FILE`, `SSL_CERT_DIR` and `CURL_CA_BUNDLE`. Assumes: by the curl
manual (its ENVIRONMENT section and the `--cacert` and `--capath` descriptions), these select only
the proxy curl connects through and the certificates it reads, and none makes it write a file. No
other variable of this process reaches curl, so for example `SSLKEYLOGFILE` cannot make it write a
file. Assumes: with `--disable` as its first argument, curl reads no `.curlrc` (curl manual,
`-q, --disable`: "If used as the first parameter on the command line, the curlrc config file is
not read or used"), so no configuration file can make it write the body to a file. `url` is the value of `--url`, so a `url` that starts with `-`,
such as `-K/tmp/x`, is a URL and not an option. With the other arguments and no other variable
curl writes no file. -/
def fetch (url : String) : IO (Nat × ByteArray) := do
  let assignments ← curlEnvironment.filterMapM fun name => do
    return (← IO.getEnv name).map fun value => s!"{name}={value}"
  let child ← IO.Process.spawn
      { cmd := "env", args := #["-i"] ++ assignments ++ #["curl", "--disable", "--silent",
          "--show-error", "--max-time", "60", "--write-out", "%{http_code}", "--url", url]
        stdin := .null, stdout := .piped, stderr := .inherit }
  let out ← child.stdout.readBinToEnd
  let _ ← child.wait
  let body := out.extract 0 (out.size - 3)
  let status := (String.fromUTF8? (out.extract (out.size - 3) out.size)).bind (·.toNat?)
  return (status.getD 0, body)

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
  unless (← field build "dirty") matches .bool false do
      fail "the artifact was built from uncommitted changes"
  unless (← str build "revision") == sha do
      fail s!"the artifact is for {← str build "revision"}, not {sha}"
  unless (← field build "publishable") matches .bool true do
      fail "a release edition is not its release asset: the release commit rendered it from \
        source, or an unreleased commit previewed a release that is not published yet"
  IO.println s!"deployment gate: PASS (clean artifact of {sha})"

/-- Post-deployment observation of the site at `pageUrl`: the artifact must be a clean build
for that site; its `build.json` must be served live (polled up to 20 times, 15 seconds
apart); the site root `index.html`, the home page of every edition, every rule page of the
development edition, the `build.json` of every release edition and the page of every stable
route must be served with the
artifact's bytes; and an unpublished route must return 404 with the artifact's `404.html`. Any
difference fails. -/
def run (artifact : FilePath) (pageUrl : String) : IO Unit := do
  let recorded ← IO.FS.readBinFile (artifact / "build.json")
  let build ← IO.ofExcept (Json.parse (← IO.FS.readFile (artifact / "build.json")))
  let site ← str build "site"
  let revision ← str build "revision"
  let pageUrl := if pageUrl.endsWith "/" then pageUrl else pageUrl ++ "/"
  unless pageUrl == site do fail s!"deployed at {pageUrl}, but the artifact is for {site}"
  unless (← field build "dirty") matches .bool false do
      fail "the artifact was built from uncommitted changes"
  let probe := s!"?regula-deployment={revision}"
  -- The deployment is atomic; wait until the live identity is this artifact's.
  let mut matched := false
  for attempt in [1:21] do
    let (status, live) ← fetch (site ++ "build.json" ++ probe ++ s!"-{attempt}")
    if status == 200 then
      if live == recorded then
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
  let stable ← (← IO.ofExcept ((← field build "stableRoutes").getArr?)).toList.mapM fun file =>
    IO.ofExcept file.getStr?
  let files := "index.html" :: editions.map (· ++ "index.html") ++
    routes.map ("dev/" ++ · ++ "index.html") ++
    (editions.filter (· != "dev/")).map (· ++ "build.json") ++ stable
  for file in files do
    let (status, live) ← fetch (site ++ file ++ probe)
    unless status == 200 do fail s!"{file}: HTTP {status}"
    unless live == (← IO.FS.readBinFile (artifact / file)) do
      fail s!"{file}: live bytes differ from the validated artifact"
  let (status, missing) ← fetch (site ++ "v/0.0.0-unpublished/rules/RG1001/" ++ probe)
  unless status == 404 do fail s!"unpublished route answered HTTP {status}, expected 404"
  unless missing == (← IO.FS.readBinFile (artifact / "404.html")) do
    fail "unpublished route did not serve the artifact's not-available page"
  IO.println s!"deployment verification: PASS ({site} serves the artifact of {revision}: \
    build.json and {files.length} pages and edition records of {editions}, {stable.length} of \
    them stable routes, not-available page); \
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
