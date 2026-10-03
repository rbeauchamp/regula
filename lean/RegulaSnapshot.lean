import Lean.Data.Json

/-! # Prepare and restore compiled dependency snapshots

A preparation builds the selected compiler and pinned dependencies from source.
Restoration acquires an immutable GHCR artifact and admits its complete input and
package census before activating it. Acquisition does not change source origin.
The pure contracts govern decoded admission and build plans. Git, compiler reports,
native ABI compatibility, ORAS, SHA-256, tar, subprocesses and filesystem effects are
trusted boundaries. Successful transport is not checker qualification.
-/
namespace RegulaSnapshot
open Lean System

/-- How a source-built snapshot reaches this copy. -/
inductive Acquisition where
  /-- Compile the frozen sources in the dedicated preparation workflow. -/
  | prepare
  /-- Acquire an already prepared immutable artifact. -/
  | restore
  deriving DecidableEq, Repr

/-- Native environments admitted by the snapshot factory and consumer. -/
inductive Platform where
  /-- Ubuntu 24.04 with the system x86-64 C ABI. -/
  | linuxX64
  /-- macOS 15 or later on arm64 with the system C ABI and Homebrew library paths. -/
  | macARM64
  deriving DecidableEq, Repr, FromJson, ToJson

/-- Stable external names of the two supported native environments. -/
def Platform.name : Platform → String
  | .linuxX64 => "ubuntu24.04-x86_64"
  | .macARM64 => "macos-arm64-min15"

/-- The exact runtime requirements attached to a target, separate from acquisition. -/
def Platform.runtime : Platform → Array String
  | .linuxX64 => #["Ubuntu 24.04 x86_64", "system cc and glibc 2.39 ABI",
      "GMP >=6.3.0 libgmp.so.10", "libuv >=1.48.0 libuv.so.1",
      "OpenSSL >=3.0.0 libssl.so.3 and libcrypto.so.3", "libstdc++.so.6"]
  | .macARM64 => #["macOS >=15.0 arm64", "system cc with active Command Line Tools",
      "/opt/homebrew/opt/gmp/lib/libgmp.10.dylib GMP >=6.3.0",
      "/opt/homebrew/opt/libuv/lib/libuv.1.dylib libuv >=1.48.0",
      "/opt/homebrew/opt/openssl@3/lib/libssl.3.dylib and libcrypto.3.dylib OpenSSL >=3.0.0",
      "system libc++.1.dylib"]

/-- A dependency checkout required by the committed Lake manifests. -/
structure Pin where
  /-- Lake package name. -/
  name : String
  /-- Full pinned Git revision. -/
  revision : String
  deriving DecidableEq, Repr, FromJson, ToJson

/-- One exact build configuration input. -/
structure Input where
  /-- Repository-relative configuration path. -/
  path : String
  /-- Complete contents, compared without reformatting. -/
  contents : String
  deriving DecidableEq, Repr, FromJson, ToJson

/-- The compiler selected for one immutable preparation. -/
structure Compiler where
  /-- Elan selector shared by all Regula packages and distinct for each input set. -/
  selector : String
  /-- Full compiler Git revision. -/
  revision : String
  /-- Exact reported Lean version. -/
  version : String
  deriving DecidableEq, Repr, FromJson, ToJson

/-- Exact preparation inputs, including the compiler recipe and native platform. -/
structure Identity where
  /-- Preparation policy, including cache-disabled native build requirements. -/
  recipe : Nat
  /-- Selected compiler identity. -/
  compiler : Compiler
  /-- Native target and declared runtime compatibility boundary. -/
  platform : Platform
  /-- Exact declared native environment, enforced before executing the restored compiler. -/
  runtime : Array String
  /-- Exact manifests, configuration and preparation program contents. -/
  inputs : Array Input
  /-- Complete sorted dependency package census. -/
  packages : Array Pin
  /-- Dependency library facets built before publication. -/
  targets : Array String
  deriving DecidableEq, Repr, FromJson, ToJson

/-- The complete preparation receipt carried inside the artifact. -/
structure Receipt where
  /-- Receipt format version. -/
  schema : Nat
  /-- Source preparation is recorded independently of subsequent acquisition. -/
  sourceBuilt : Bool
  /-- Frozen build inputs. -/
  identity : Identity
  /-- Independently observed compiler identity. -/
  compiler : Compiler
  /-- Independently observed package census. -/
  packages : Array Pin
  /-- Build commands whose completion preceded this receipt. -/
  completedTargets : Array String
  deriving DecidableEq, Repr, FromJson, ToJson

/-- Admission requires complete equality, including every requested package and facet. -/
def admits (expected : Identity) (receipt : Receipt) : Bool :=
  receipt.schema == 1 && receipt.sourceBuilt && receipt.identity == expected &&
    receipt.compiler == expected.compiler && receipt.packages == expected.packages &&
    receipt.completedTargets == expected.targets

/--
Admission fixes the complete identity, source origin, compiler, package census and plan.

## Intent
An empty or partial census cannot satisfy a nonempty request. This theorem compares
supplied observations; it does not prove the external compiler or build commands sound.
-/
theorem admits_iff (expected : Identity) (receipt : Receipt) :
    admits expected receipt = true ↔
      receipt.schema = 1 ∧ receipt.sourceBuilt = true ∧ receipt.identity = expected ∧
      receipt.compiler = expected.compiler ∧ receipt.packages = expected.packages ∧
      receipt.completedTargets = expected.targets := by
  simp [admits, and_assoc]

/-- A receipt carrying the admission predicate required before activation. -/
abbrev Admitted (expected : Identity) := {receipt : Receipt // admits expected receipt = true}

/-- Admit decoded data without a permissive restoration path. -/
def admit? (expected : Identity) (receipt : Receipt) : Option (Admitted expected) :=
  if h : admits expected receipt then some ⟨receipt, h⟩ else none

/-- The actual admission constructor retains exactly its checked receipt. -/
theorem admit?_sound (expected : Identity) (receipt : Receipt) (accepted : Admitted expected)
    (h : admit? expected receipt = some accepted) :
    accepted.val = receipt ∧ admits expected receipt = true := by
  unfold admit? at h
  split at h
  · rename_i valid
    cases Option.some.inj h
    exact ⟨rfl, valid⟩
  · simp at h

/-- Source-build operations interpreted by the acquisition runner. -/
inductive BuildStep where
  /-- Prepare the exact compiler before building its dependencies. -/
  | compiler
  /-- Build the requested facets in one pinned Lake workspace. -/
  | dependencies (directory : String) (targets : Array String)

/-- Only explicit preparation schedules compiler and dependency compilation. -/
def buildPlan : Acquisition → Array BuildStep
  | .prepare => #[
      .compiler,
      .dependencies "audit"
        #["mathlib/Mathlib", "mathlib/Mathlib:static.export", "mathlib/Mathlib:shared"],
      .dependencies "website" #["verso/VersoManual", "verso/VersoManual:static.export",
        "verso/VersoManual:shared"]]
  | .restore => #[]

/-- The acquisition runner's restoration plan contains no source-build operation. -/
theorem restore_plan : buildPlan .restore = #[] := rfl

/-- Closed set of native targets supported by the preparation workflow. -/
def platformName : IO Platform := do
  let arch ← IO.Process.output {
    cmd := "uname", args := #["-m"], env := #[("GHCR_TOKEN", none)], stdin := .null}
  unless arch.exitCode == 0 do throw <| IO.userError "snapshot: cannot observe architecture"
  let arch := arch.stdout.trimAscii.toString
  if System.Platform.isOSX && arch == "arm64" then
    let os ← IO.Process.output {
      cmd := "sw_vers", args := #["-productVersion"], env := #[("GHCR_TOKEN", none)], stdin := .null}
    let major := ((os.stdout.trimAscii.toString.splitOn ".").headD "").toNat?
    unless os.exitCode == 0 && (major.any (· ≥ 15)) do
      throw <| IO.userError "snapshot: macOS arm64 requires macOS 15 or later"
    return .macARM64
  if System.Platform.isLinux && arch == "x86_64" then
    let os ← IO.FS.readFile "/etc/os-release"
    unless (os.splitOn "\n").contains "ID=ubuntu" &&
        (os.splitOn "\n").contains "VERSION_ID=\"24.04\"" do
      throw <| IO.userError "snapshot: Linux native artifacts require Ubuntu 24.04 x86_64"
    return .linuxX64
  throw <| IO.userError "snapshot: unsupported native platform"

private def run (cwd : FilePath) (cmd : String) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO String := do
  let result ← IO.Process.output {
    cmd, args, cwd := some cwd, env := env.push ("GHCR_TOKEN", none), stdin := .null}
  unless result.exitCode == 0 do
    throw <| IO.userError s!"snapshot: {cmd} failed ({result.exitCode}): {result.stderr}"
  return result.stdout.trimAscii.toString

private def stream (cwd : FilePath) (cmd : String) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO Unit := do
  let child ← IO.Process.spawn {
    cmd, args, cwd := some cwd, env := env.push ("GHCR_TOKEN", none),
    stdin := .null, stdout := .inherit, stderr := .inherit}
  let code ← child.wait
  unless code == 0 do throw <| IO.userError s!"snapshot: {cmd} failed ({code})"

private def diskSpace (root : FilePath) (phase : String) : IO Nat := do
  let report ← run root "df" #["-Pk", root.toString]
  let line := (report.splitOn "\n").getLast!
  let fields := (line.splitOn " ").filter (!·.isEmpty)
  let some available := (fields[3]?).bind String.toNat?
    | throw <| IO.userError "snapshot: cannot observe available disk space"
  IO.println s!"snapshot: {phase}: {available} KiB available on the preparation filesystem"
  return available

private def readJson (path : FilePath) : IO Json := do
  IO.ofExcept <| Json.parse (← IO.FS.readFile path)

private def decode {α : Type} [FromJson α] (path : FilePath) : IO α := do
  IO.ofExcept <| fromJson? (← readJson path)

private def component (text : String) : Bool :=
  !text.isEmpty && !text.startsWith "." && !text.startsWith "-" &&
    text.all fun c => c.isAlphanum || c == '-' || c == '_' || c == '.'

private def objectName (text : String) : Bool :=
  text.length == 40 && text.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

private def objectDigest (text : String) : Bool :=
  text.length == 64 && text.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- The two disjoint payload roots; archives cannot choose another extraction directory. -/
inductive ArchiveTarget where
  /-- The complete compiler prefix. -/
  | compiler
  /-- The complete pinned package directory. -/
  | packages
  deriving DecidableEq, Repr, FromJson, ToJson

/-- Fixed archive roots used by both preparation and restoration. -/
def ArchiveTarget.name : ArchiveTarget → String
  | .compiler => "compiler"
  | .packages => "packages"

/-- One bounded OCI layer carrying part of a compressed archive. -/
structure Chunk where
  /-- A single archive filename, never a path chosen by a registry response. -/
  name : String
  /-- SHA-256 of exactly these compressed bytes. -/
  sha256 : String
  deriving Repr, FromJson, ToJson

/-- Ordered layers of one archive and its closed extraction target. -/
structure Archive where
  /-- One of the two owned payload roots. -/
  target : ArchiveTarget
  /-- Layers in the exact compressed-stream order. -/
  chunks : Array Chunk
  deriving Repr, FromJson, ToJson

/-- A transport descriptor carried in the same immutable OCI manifest as its layers. -/
structure Archives where
  /-- Transport descriptor version. -/
  schema : Nat
  /-- The admitted source preparation, before any activation. -/
  receipt : Receipt
  /-- Exactly one complete archive for each payload root. -/
  archives : Array Archive
  deriving Repr, FromJson, ToJson

/-- Validate every decoded extraction target, layer name and digest before writing payloads. -/
def Archives.valid (description : Archives) : Bool :=
  description.schema == 1 &&
    description.archives.map (·.target) == #[.compiler, .packages] &&
    description.archives.all fun archive => !archive.chunks.isEmpty &&
      archive.chunks.all fun chunk => component chunk.name && objectDigest chunk.sha256

/--
Transport admission requires both distinct roots and every layer's safe name and digest.

## Intent
Apply the predicate used by the extractor to the complete decoded archive census.
SHA-256, OCI transport and tar's interpretation remain trusted effects.
-/
theorem Archives.valid_iff (description : Archives) :
    description.valid = true ↔ description.schema = 1 ∧
      description.archives.map (·.target) = #[.compiler, .packages] ∧
      (∀ archive ∈ description.archives, archive.chunks.isEmpty = false ∧
        ∀ chunk ∈ archive.chunks, component chunk.name = true ∧ objectDigest chunk.sha256 = true) := by
  simp [Archives.valid, Array.all_eq_true', -Array.all_eq_true, and_assoc]

private def pins (root : FilePath) : IO (Array Pin) := do
  let mut found : Array Pin := #[]
  for file in #["audit/lake-manifest.json", "website/lake-manifest.json"] do
    let entries ← IO.ofExcept <| (← readJson (root / file)).getObjValAs? (Array Json) "packages"
    for entry in entries do
      let type ← IO.ofExcept <| entry.getObjValAs? String "type"
      if type == "git" then
        let name ← IO.ofExcept <| entry.getObjValAs? String "name"
        let revision ← IO.ofExcept <| entry.getObjValAs? String "rev"
        unless component name && objectName revision do
          throw <| IO.userError "snapshot: malformed dependency pin"
        if let some old := found.find? (·.name == name) then
          unless old.revision == revision do
            throw <| IO.userError s!"snapshot: manifests disagree on {name}"
        else found := found.push ⟨name, revision⟩
      else if type != "path" then
        throw <| IO.userError s!"snapshot: unsupported package origin {type}"
  unless !found.isEmpty do throw <| IO.userError "snapshot: empty dependency census"
  return found.qsort fun left right => left.name < right.name

private def identity (root : FilePath) : IO Identity := do
  let compiler : Compiler ← decode (root / ".github/snapshot-compiler.json")
  unless component compiler.selector do
    throw <| IO.userError "snapshot: malformed compiler selector"
  unless objectName compiler.revision && !compiler.version.isEmpty do
    throw <| IO.userError "snapshot: malformed compiler identity"
  let mut inputs := #[]
  for file in #["lean-toolchain", "dependency-build-mode", "lakefile.lean", "lake-manifest.json",
      "audit/lean-toolchain", "audit/lakefile.lean", "audit/lake-manifest.json",
      "website/lean-toolchain", "website/lakefile.toml", "website/lake-manifest.json",
      "examples/build-lint/lean-toolchain", "examples/lake-lint-toml/lean-toolchain",
      "lean/RegulaCompiler.lean", "lean/RegulaSnapshot.lean"] do
    inputs := inputs.push ⟨file, ← IO.FS.readFile (root / file)⟩
  if ← (root / ".github/compiler-source.json").pathExists then
    inputs := inputs.push ⟨".github/compiler-source.json",
      ← IO.FS.readFile (root / ".github/compiler-source.json")⟩
  unless (← IO.FS.readFile (root / "dependency-build-mode")).trimAscii == "source" do
    throw <| IO.userError "snapshot: preparation and restoration require source origin"
  for file in #["lean-toolchain", "audit/lean-toolchain", "website/lean-toolchain",
      "examples/build-lint/lean-toolchain", "examples/lake-lint-toml/lean-toolchain"] do
    unless (← IO.FS.readFile (root / file)).trimAscii == compiler.selector do
      throw <| IO.userError s!"snapshot: {file} selects another compiler"
  let targets := (buildPlan .prepare).flatMap fun step => match step with
    | .compiler => #[]
    | .dependencies dir targets => targets.map fun target => s!"{dir}:{target}"
  let platform ← platformName
  return {
    recipe := 1, compiler, platform, runtime := platform.runtime,
    inputs, packages := ← pins root, targets}

private def requireRuntime (root : FilePath) (platform : Platform) : IO Unit := do
  let _ ← run root "cc" #["--version"]
  let libraries := match platform with
    | .linuxX64 => #["/usr/lib/x86_64-linux-gnu/libgmp.so.10",
        "/usr/lib/x86_64-linux-gnu/libuv.so.1", "/usr/lib/x86_64-linux-gnu/libssl.so.3",
        "/usr/lib/x86_64-linux-gnu/libcrypto.so.3", "/usr/lib/x86_64-linux-gnu/libstdc++.so.6"]
    | .macARM64 => #["/opt/homebrew/opt/gmp/lib/libgmp.10.dylib",
        "/opt/homebrew/opt/libuv/lib/libuv.1.dylib", "/opt/homebrew/opt/openssl@3/lib/libssl.3.dylib",
        "/opt/homebrew/opt/openssl@3/lib/libcrypto.3.dylib"]
  for path in libraries do
    unless ← (FilePath.mk path).pathExists do
      throw <| IO.userError s!"snapshot: required native runtime library is absent: {path}"
  if platform == .macARM64 then
    let _ ← run root "xcrun" #["--find", "clang"]
  let env := if platform == .macARM64 then
    #[("PKG_CONFIG_PATH", some ("/opt/homebrew/opt/gmp/lib/pkgconfig:" ++
      "/opt/homebrew/opt/libuv/lib/pkgconfig:/opt/homebrew/opt/openssl@3/lib/pkgconfig"))] else #[]
  for (package, version) in #[("gmp", "6.3.0"), ("libuv", "1.48.0"), ("openssl", "3.0.0")] do
    let _ ← run root "pkg-config" #[s!"--atleast-version={version}", package] env

private def observeCompiler (root compilerRoot : FilePath) (expected : Compiler) : IO Compiler := do
  let lean := (compilerRoot / "bin/lean").toString
  let revision ← run root lean #["--githash"]
  let library ← run root lean #["--run", (root / "lean/RegulaCompiler.lean").toString, "identity"]
  let reported ← run root lean #["--version"]
  unless revision == expected.revision && library == expected.revision &&
      reported.startsWith s!"Lean (version {expected.version}," do
    throw <| IO.userError s!"snapshot: compiler reports do not match {expected.revision}"
  return {expected with revision}

/-- Execute only the selected acquisition's compiler and dependency build operations. -/
private def runBuildPlan (root : FilePath) (expected : Identity)
    (acquisition : Acquisition) : IO Unit := do
  for step in buildPlan acquisition do
    match step with
    | .compiler =>
      stream root "elan" #["run", "leanprover/lean4:v4.34.0", "lean", "--run",
        "lean/RegulaCompiler.lean", "prepare"]
      let _ ← diskSpace root "after compiler preparation"
      let compilerRoot ← run root "elan" #["run", expected.compiler.selector, "lean", "--print-prefix"]
      let _ ← observeCompiler root (FilePath.mk compilerRoot) expected.compiler
    | .dependencies dir targets =>
      let cache := root / ".lake/snapshot-artifact-cache"
      IO.FS.createDirAll cache
      let env := #[("LAKE_NO_CACHE", some "true"), ("MATHLIB_NO_CACHE_ON_UPDATE", some "1"),
        ("LAKE_ARTIFACT_CACHE", some "false"), ("LAKE_CACHE_DIR", some cache.toString),
        ("LAKE_RESTORE_ARTIFACTS", some "true"), ("MACOSX_DEPLOYMENT_TARGET", some "15.0")]
      stream root "elan" (#["run", expected.compiler.selector, "lake", "--no-cache",
        "--keep-toolchain", "-d", dir, "build"] ++ targets) env

/-- The executed restoration runner performs no build-plan IO for any root or identity. -/
private theorem runBuildPlan_restore (root : FilePath) (expected : Identity) :
    runBuildPlan root expected .restore = pure () := by
  simp [runBuildPlan, restore_plan]
  rfl

private def observePackages (packages : FilePath) : IO (Array Pin) := do
  let mut observed := #[]
  for entry in ← packages.readDir do
    unless component entry.fileName && (← entry.path.isDir) &&
        (← (entry.path / ".git").symlinkMetadata).type == .dir do
      throw <| IO.userError s!"snapshot: unexpected package entry {entry.path}"
    unless (← run entry.path "git" #["status", "--porcelain", "--untracked-files=all"]).isEmpty do
      throw <| IO.userError s!"snapshot: package has local changes: {entry.fileName}"
    observed := observed.push ⟨entry.fileName, ← run entry.path "git" #["rev-parse", "HEAD"]⟩
  return observed.qsort fun left right => left.name < right.name

private def readAdmitted (root payload : FilePath) (expected : Identity) : IO (Admitted expected) := do
  let receipt : Receipt ← decode (payload / "receipt.json")
  let some accepted := admit? expected receipt
    | throw <| IO.userError "snapshot: receipt does not admit the complete requested inputs"
  requireRuntime root expected.platform
  unless (← observePackages (payload / "packages")) == accepted.val.packages do
    throw <| IO.userError "snapshot: unpacked package census differs from the admitted receipt"
  let _ ← observeCompiler root (payload / "compiler") accepted.val.compiler
  return accepted

private def nonce : IO String := do
  let bytes ← IO.getRandomBytes 8
  return toString <| bytes.foldl (fun total byte => total * 256 + byte.toNat) 0

private def digest (root path : FilePath) : IO String := do
  let result ← if System.Platform.isOSX then run root "shasum" #["-a", "256", path.toString]
    else run root "sha256sum" #[path.toString]
  let value := (result.splitOn " ").headD ""
  unless objectDigest value do
    throw <| IO.userError "snapshot: invalid SHA-256 observation"
  return value

private def packArchive (prepared source : FilePath) (target : ArchiveTarget) : IO Archive := do
  let child ← IO.Process.spawn {
    cmd := "tar", args := #["-czf", "-", "."], cwd := some source,
    env := #[("GHCR_TOKEN", none)], stdin := .null, stdout := .piped, stderr := .inherit}
  let chunks ← try
    let mut chunks := #[]
    let mut finished := false
    while !finished do
      let first ← child.stdout.read (1024 * 1024)
      if first.isEmpty then break
      let name := s!"{target.name}.part-{chunks.size}"
      let file := prepared / name
      let output ← IO.FS.Handle.mk file .write
      output.write first
      let mut size := first.size
      while size < 1024 * 1024 * 1024 do
        let bytes ← child.stdout.read ((min (1024 * 1024) (1024 * 1024 * 1024 - size)).toUSize)
        if bytes.isEmpty then
          finished := true
          break
        output.write bytes
        size := size + bytes.size
      output.flush
      chunks := chunks.push ⟨name, ← digest prepared file⟩
    pure chunks
  catch error =>
    if (← child.tryWait).isNone then
      child.kill
      let _ ← child.wait
    throw error
  let code ← child.wait
  unless code == 0 && !chunks.isEmpty do
    throw <| IO.userError s!"snapshot: {target.name} archive preparation failed ({code})"
  return ⟨target, chunks⟩

private def extractArchive (staging payload : FilePath) (archive : Archive) : IO Unit := do
  let destination := payload / archive.target.name
  IO.FS.createDir destination
  let child ← do
    let (input, child) ← (← IO.Process.spawn {
      cmd := "tar", args := #["-xzf", "-", "-C", destination.toString], cwd := some staging,
      env := #[("GHCR_TOKEN", none)], stdin := .piped,
      stdout := .inherit, stderr := .inherit}).takeStdin
    try
      for chunk in archive.chunks do
        let source ← IO.FS.Handle.mk (staging / chunk.name) .read
        repeat
          let bytes ← source.read (1024 * 1024)
          if bytes.isEmpty then break
          input.write bytes
      input.flush
      pure child
    catch error =>
      child.kill
      let _ ← child.wait
      throw error
  let code ← child.wait
  unless code == 0 do throw <| IO.userError s!"snapshot: {archive.target.name} extraction failed ({code})"

private def registryLogin (root : FilePath) (tool : String) : IO Unit := do
  let some token ← IO.getEnv "GHCR_TOKEN" | throw <| IO.userError "snapshot: package token is unset"
  unless (← IO.getEnv "GITHUB_ACTIONS") == some "true" &&
      (← IO.getEnv "GITHUB_REPOSITORY") == some "rbeauchamp/regula" do
    throw <| IO.userError "snapshot: package credentials are confined to Regula Actions"
  let some actor ← IO.getEnv "GITHUB_ACTOR" | throw <| IO.userError "snapshot: actor is unset"
  let result ← IO.Process.output {
    cmd := tool, args := #["login", "ghcr.io", "--username", actor, "--password-stdin"],
    cwd := some root, env := #[("GHCR_TOKEN", none)]} (some (token ++ "\n"))
  unless result.exitCode == 0 do throw <| IO.userError "snapshot: package login failed"

private def oras (root : FilePath) : IO String := do
  let platform ← platformName
  let (target, expectedDigest) := match platform with
    | .linuxX64 => ("linux_amd64", "6cdc692f929100feb08aa8de584d02f7bcc30ec7d88bc2adc2054d782db57c64")
    | .macARM64 => ("darwin_arm64", "e10c6552c02d5a7c7eaf7170d3b6f7f094b675a98a1e0edf4d4478a909447245")
  let dir := root / ".lake/snapshot-tools/oras-1.3.0" / target
  IO.FS.createDirAll dir
  let exe := dir / "oras"
  unless ← exe.pathExists do
    let archive := s!"oras_1.3.0_{target}.tar.gz"
    let base := "https://github.com/oras-project/oras/releases/download/v1.3.0"
    stream dir "curl" #["--fail", "--location", "--retry", "3", s!"{base}/{archive}",
      "--output", archive]
    let actual ← digest dir (dir / archive)
    unless actual == expectedDigest do
      throw <| IO.userError "snapshot: ORAS archive differs from its pinned digest"
    stream dir "tar" #["-xzf", archive, "oras"]
  let _ ← run dir exe.toString #["version"]
  return exe.toString

/-- One immutable OCI reference for a supported native target. -/
structure Location where
  /-- Target named by `platformName`. -/
  platform : String
  /-- Complete manifest digest, with no mutable tag or alternate registry. -/
  reference : String
  deriving FromJson, ToJson, Repr

/-- A location names exactly the requested platform and an immutable Regula manifest. -/
def Location.valid (platform : Platform) (selected : Location) : Bool :=
  let referencePrefix := "ghcr.io/rbeauchamp/regula-compiled@sha256:"
  selected.platform == platform.name && selected.reference.startsWith referencePrefix &&
    objectDigest (selected.reference.drop referencePrefix.length).toString

/--
Location admission fixes the native target, registry and complete manifest digest.

## Intent
Use the same predicate for committed locations and a preparation's qualification input.
The artifact's receipt must separately admit the complete build identity.
-/
theorem Location.valid_iff (platform : Platform) (selected : Location) :
    selected.valid platform = true ↔ selected.platform = platform.name ∧
      selected.reference.startsWith "ghcr.io/rbeauchamp/regula-compiled@sha256:" = true ∧
      objectDigest (selected.reference.drop
        "ghcr.io/rbeauchamp/regula-compiled@sha256:".length).toString = true := by
  simp [Location.valid, and_assoc]

private def location (root : FilePath) (expected : Identity) : IO Location := do
  let locations : Array Location ← decode (root / ".github/compiler-snapshot.json")
  let candidates := locations.filter (·.platform == expected.platform.name)
  unless candidates.size == 1 do
    throw <| IO.userError s!"snapshot: expected one location for {expected.platform.name}; prepare it first"
  let some selected := candidates[0]?
    | throw <| IO.userError "snapshot: absent platform after exact location count"
  unless selected.valid expected.platform do
    throw <| IO.userError "snapshot: reference must be an immutable Regula GHCR digest"
  return selected

/-- Select a preparation's exact digest only in the fresh hosted qualification checkout. -/
def selectForQualification (root input : FilePath) : IO Unit := do
  unless (← IO.getEnv "GITHUB_ACTIONS") == some "true" &&
      (← IO.getEnv "GITHUB_REPOSITORY") == some "rbeauchamp/regula" do
    throw <| IO.userError "snapshot: qualification selection is confined to Regula Actions"
  let expected ← identity root
  let selected : Location ← decode input
  unless selected.valid expected.platform do
    throw <| IO.userError "snapshot: preparation location has another platform or invalid digest"
  IO.FS.writeFile (root / ".github/compiler-snapshot.json")
    ((toJson #[selected]).pretty ++ "\n")

private def requireActivation (root payload : FilePath) (expected : Identity) : IO Bool := do
  let packages := root / ".lake/packages"
  for directory in #[root / ".lake", packages] do
    match ← directory.symlinkMetadata.toBaseIO with
    | .ok _ =>
      unless ← directory.isDir do
        throw <| IO.userError s!"snapshot: preserving existing non-directory {directory}; use a fresh copy"
    | .error (.noFileOrDirectory ..) => pure ()
    | .error error => throw error
  for pin in expected.packages do
    let target := payload / "packages" / pin.name
    let path := packages / pin.name
    match ← path.symlinkMetadata.toBaseIO with
    | .ok metadata =>
      unless metadata.type == .symlink && (← target.pathExists) do
        throw <| IO.userError s!"snapshot: preserving existing package path {path}; use a fresh copy"
      unless (← IO.FS.realPath path) == (← IO.FS.realPath target) do
        throw <| IO.userError s!"snapshot: preserving existing package path {path}; use a fresh copy"
    | .error (.noFileOrDirectory ..) => pure ()
    | .error error => throw error
  let listing ← run root "elan" #["toolchain", "list"]
  let installed := (listing.splitOn "\n").any fun line =>
    (line.splitOn " ").head? == some expected.compiler.selector
  if installed then
    let compilerRoot ← run root "elan" #["run", expected.compiler.selector, "lean", "--print-prefix"]
    unless ← (payload / "compiler").pathExists do
      throw <| IO.userError "snapshot: preserving an existing alias before its snapshot is available; \
        choose a distinct alias and prepare that input set"
    unless (← IO.FS.realPath (FilePath.mk compilerRoot)) ==
        (← IO.FS.realPath (payload / "compiler")) do
      throw <| IO.userError "snapshot: preserving an existing alias linked to another compiler root; \
        choose a distinct alias in the compiler specifications and all five toolchain files, \
        then prepare and qualify that input set"
    let _ ← observeCompiler root (FilePath.mk compilerRoot) expected.compiler
  return installed

private def activate (root payload : FilePath) (expected : Identity)
    (_accepted : Admitted expected) : IO Unit := do
  let installed ← requireActivation root payload expected
  let packages := root / ".lake/packages"
  IO.FS.createDirAll packages
  unless installed do
    stream root "elan" #["toolchain", "link", expected.compiler.selector,
      (payload / "compiler").toString]
  for pin in expected.packages do
    let path := packages / pin.name
    unless ← path.pathExists do
      stream root "ln" #["-s", (payload / "packages" / pin.name).toString, path.toString]
  IO.println s!"snapshot: restored source-built {expected.compiler.revision} ({expected.platform.name})"

/-- Restore and admit the committed OCI digest; a miss never compiles dependencies. -/
def restore (root : FilePath) : IO Unit := do
  let expected ← identity root
  runBuildPlan root expected .restore
  let selected ← location root expected
  requireRuntime root expected.platform
  let some home ← IO.getEnv "HOME" | throw <| IO.userError "snapshot: HOME is unset"
  let parent := FilePath.mk home / ".cache/regula-snapshots"
  IO.FS.createDirAll parent
  let lock ← IO.FS.Handle.mk (parent / "restore.lock") .append
  lock.lock
  try
    let key := ((selected.reference.splitOn "@sha256:").getLast!).trimAscii.toString
    let final := parent / key
    let _ ← requireActivation root (final / "payload") expected
    unless ← final.pathExists do
      let staging := parent / s!"{key}.staging-{← nonce}"
      IO.FS.createDir staging
      IO.println s!"snapshot: restoring {selected.reference}; interrupted content stays in {staging}"
      let tool ← oras root
      stream staging tool #["pull", selected.reference, "--output", staging.toString]
      let description : Archives ← decode (staging / "archive.json")
      unless description.valid && admits expected description.receipt do
        throw <| IO.userError "snapshot: archive descriptor does not admit the complete request"
      for archive in description.archives do
        for chunk in archive.chunks do
          unless (← digest staging (staging / chunk.name)) == chunk.sha256 do
            throw <| IO.userError s!"snapshot: layer hash differs from its descriptor: {chunk.name}"
      let payload := staging / "payload"
      IO.FS.createDir payload
      IO.FS.writeFile (payload / "receipt.json") ((toJson description.receipt).pretty ++ "\n")
      for archive in description.archives do
        extractArchive staging payload archive
        for chunk in archive.chunks do IO.FS.removeFile (staging / chunk.name)
      let _ ← readAdmitted root payload expected
      stream staging "chmod" #["-R", "a-w", payload.toString]
      IO.FS.rename staging final
    let accepted ← readAdmitted root (final / "payload") expected
    activate root (final / "payload") expected accepted
  finally lock.unlock

/-- Prepare source-built native artifacts; publication is a separate explicit command. -/
def prepare (root : FilePath) : IO Unit := do
  let expected ← identity root
  unless (← IO.getEnv "GITHUB_ACTIONS") == some "true" &&
      (← IO.getEnv "GITHUB_REPOSITORY") == some "rbeauchamp/regula" do
    throw <| IO.userError "snapshot: preparation runs only in the dedicated Regula Actions workflow"
  unless (← run root "git" #["status", "--porcelain", "--untracked-files=all"]).isEmpty do
    throw <| IO.userError "snapshot: preparation requires a clean frozen checkout"
  unless ← (root / ".github/compiler-source.json").pathExists do
    throw <| IO.userError "snapshot: preparation requires an explicit compiler source recipe"
  let source ← readJson (root / ".github/compiler-source.json")
  unless (← IO.ofExcept <| source.getObjValAs? String "revision") == expected.compiler.revision do
    throw <| IO.userError "snapshot: compiler source recipe selects another revision"
  unless !(← (root / ".lake/packages").pathExists) do
    throw <| IO.userError "snapshot: preserving existing dependency artifacts; use a fresh factory runner"
  let some home ← IO.getEnv "HOME" | throw <| IO.userError "snapshot: HOME is unset"
  unless !(← (FilePath.mk home / ".cache/regula-compilers").pathExists) do
    throw <| IO.userError "snapshot: preserving an existing compiler store; use a fresh factory runner"
  let listing ← run root "elan" #["toolchain", "list"]
  unless !(listing.splitOn "\n").any (fun line =>
      (line.splitOn " ").head? == some expected.compiler.selector) do
    throw <| IO.userError "snapshot: source preparation cannot reuse an installed compiler alias"
  let available ← diskSpace root "before source preparation"
  unless available ≥ 32 * 1024 * 1024 do
    throw <| IO.userError "snapshot: source preparation requires at least 32 GiB initially free; \
      hosted capacity is not inferred from the runner label"
  runBuildPlan root expected .prepare
  let _ ← diskSpace root "after dependency preparation"
  let compilerRoot ← run root "elan" #["run", expected.compiler.selector, "lean", "--print-prefix"]
  let compiler ← observeCompiler root (FilePath.mk compilerRoot) expected.compiler
  let prepared := root / "tmp/compiled-snapshot"
  unless !(← prepared.pathExists) do
    throw <| IO.userError "snapshot: preserving an existing preparation directory"
  IO.FS.createDirAll prepared
  let payload := prepared / "payload"
  IO.FS.createDir payload
  stream root "ln" #["-s", compilerRoot, (payload / "compiler").toString]
  stream root "ln" #["-s", (root / ".lake/packages").toString, (payload / "packages").toString]
  let packages ← observePackages (payload / "packages")
  let receipt : Receipt := {
    schema := 1, sourceBuilt := true, identity := expected,
    compiler, packages, completedTargets := expected.targets}
  IO.FS.writeFile (payload / "receipt.json") ((toJson receipt).pretty ++ "\n")
  let _ ← readAdmitted root payload expected
  let archives := #[← packArchive prepared (FilePath.mk compilerRoot) .compiler,
    ← packArchive prepared (root / ".lake/packages") .packages]
  let description : Archives := ⟨1, receipt, archives⟩
  unless description.valid do throw <| IO.userError "snapshot: generated archive descriptor is invalid"
  IO.FS.writeFile (prepared / "archive.json") ((toJson description).pretty ++ "\n")
  let _ ← diskSpace root "after streamed packaging"
  IO.println s!"snapshot: prepared source-built {compiler.revision} for {expected.platform.name}"

/-- Publish only an admitted preparation to the Regula OCI package. -/
def publish (root : FilePath) : IO Unit := do
  let expected ← identity root
  let prepared := root / "tmp/compiled-snapshot"
  let _ ← readAdmitted root (prepared / "payload") expected
  unless (← IO.getEnv "GITHUB_ACTIONS") == some "true" &&
      (← IO.getEnv "GITHUB_REPOSITORY") == some "rbeauchamp/regula" do
    throw <| IO.userError "snapshot: publication is confined to the Regula preparation workflow"
  let tool ← oras root
  registryLogin prepared tool
  let description : Archives ← decode (prepared / "archive.json")
  unless description.valid && admits expected description.receipt do
    throw <| IO.userError "snapshot: refusing an invalid publication descriptor"
  let chunks := description.archives.flatMap (·.chunks)
  for chunk in chunks do
    unless (← digest prepared (prepared / chunk.name)) == chunk.sha256 do
      throw <| IO.userError s!"snapshot: publication layer changed: {chunk.name}"
  let tag := s!"ghcr.io/rbeauchamp/regula-compiled:{expected.compiler.revision}-{expected.platform.name}"
  let result ← run prepared tool (#["push", tag, "--format", "json", "--artifact-type",
    "application/vnd.regula.compiled-snapshot.v1", "--annotation",
    "org.opencontainers.image.source=https://github.com/rbeauchamp/regula",
    "archive.json:application/json"] ++ chunks.map (·.name ++ ":application/octet-stream"))
  let result ← IO.ofExcept <| Json.parse result
  let hash ← IO.ofExcept <| result.getObjValAs? String "digest"
  let reference := s!"ghcr.io/rbeauchamp/regula-compiled@{hash}"
  IO.FS.writeFile (prepared / "location.json")
    ((toJson (Location.mk expected.platform.name reference)).pretty ++ "\n")
  IO.println s!"snapshot: prepared package {reference}; qualification remains required"

end RegulaSnapshot

/-- Standalone preparation, publication, qualification selection and restoration. -/
def main (args : List String) : IO Unit := do
  let root ← IO.FS.realPath (← IO.currentDir)
  match args with
  | ["prepare"] => RegulaSnapshot.prepare root
  | ["publish"] => RegulaSnapshot.publish root
  | ["restore"] => RegulaSnapshot.restore root
  | ["select-for-qualification", input] =>
    RegulaSnapshot.selectForQualification root (System.FilePath.mk input)
  | _ => throw <| IO.userError "usage: lean --run lean/RegulaSnapshot.lean \
      prepare|publish|restore|select-for-qualification LOCATION"
