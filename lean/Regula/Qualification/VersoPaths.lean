import Regula.Qualification.Support
import Regula.Checker.Documentation

/-! # The Lake selection of a Verso package's local packages

The control of `qualify verso-recorded-paths`. Two documentation checks read the Lake inputs of the
packages that the Verso package's workspace loads from a path entry
(`LakeSelection.pathPackages`). `Documentation.sharedPinMismatch` compares the Git pins of the
Verso workspace with those of the workspace that each such package roots
(`LakeSelection.pinMismatch`, `LakeSelection.rootEntries`), and
`Documentation.captureVersoPackage` binds the configuration files, manifests, package overrides
files and toolchain files of those packages (`LakeSelection.lakeInputs`). The control runs both on
a copy of `examples/fixtures/verso-recorded-paths`, a Verso package that requires the package
`recorded` by path. The manifest entry of `recorded` records the configuration file
`package.toml` and the manifest `pins.json`, which pins the Git package `shared` at another revision
than the Verso package and `recorded`'s own `lake-manifest.json` do. `recorded` also has a
`lakefile.toml`, which Lake does not load for it. The control writes the files and the further
manifest entries it needs into the copy, and undoes each before the next step. Lake's load of the
copy, the files it reads and the copy itself are trusted IO that the control observes, not
proves. -/

namespace Regula.Qualification.VersoPaths
open Lean System RegulaQualification
open Regula.Checker

/-- The revision at which the Verso package and `recorded`'s own manifest pin `shared`. -/
private def pinned : String := "1111111111111111111111111111111111111111"

/-- Another revision of `shared`: the one that `pins.json` pins, and the one that a mutation
writes elsewhere. -/
private def other : String := "2222222222222222222222222222222222222222"

/-- A Lean configuration of `recorded`, which the control writes beside `package.toml`. -/
private def leanConfiguration : String := "import Lake\nopen Lake DSL\n\npackage recorded\n"

/-- Run `action` with `path` changed by `change`, then write its text back. The changed text must
differ from the original, so a mutation cannot leave the file as it was. -/
private def withChanged {α : Type} (path : FilePath) (change : String → String) (action : IO α) :
    IO α := do
  let saved ← IO.FS.readFile path
  let changed := change saved
  requireChecks [⟨s!"the mutation changes {path}", changed != saved⟩]
  IO.FS.writeFile path changed
  try
    action
  finally
    IO.FS.writeFile path saved

/-- Run `action` with the package entries of the manifest at `path` replaced by `change` of them.
A manifest that is not a JSON object with a `packages` array is left as it is, which `withChanged`
refuses. -/
private def withEntries {α : Type} (path : FilePath) (change : Array Json → Array Json)
    (action : IO α) : IO α :=
  withChanged path (fun text => match Json.parse text with
    | .ok json => match json.getObjValAs? (Array Json) "packages" with
      | .ok entries => (json.setObjVal! "packages" (toJson (change entries))).pretty
      | .error _ => text
    | .error _ => text) action

/-- Run `action` with the file `path`, which must not exist yet, written with `text`, then remove
it. -/
private def withWritten {α : Type} (path : FilePath) (text : String) (action : IO α) : IO α := do
  requireChecks
    [⟨s!"{path} does not exist before the control writes it", !(← path.pathExists)⟩]
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path text
  try
    action
  finally
    Regula.Filesystem.removePath .file path

/-- Run `action` with the file `path` written as a package overrides file of `entries`
(`withWritten`). -/
private def withOverrides {α : Type} (path : FilePath) (entries : Array Json) (action : IO α) :
    IO α :=
  withWritten path (Json.mkObj [("version", "1.2.0"), ("packages", toJson entries)]).pretty action

/-- Run `action` with the file `path` removed, then write its contents back. -/
private def withRemoved {α : Type} (path : FilePath) (action : IO α) : IO α := do
  let saved ← IO.FS.readBinFile path
  Regula.Filesystem.removePath .file path
  try
    action
  finally
    IO.FS.writeBinFile path saved

/-- What `action` gives, or the message of the error that it raises. -/
private def outcome {α : Type} (action : IO α) : IO (Except String α) := do
  try return .ok (← action) catch error => return .error (toString error)

/-- A Git entry for `name` at the revision `rev`. -/
private def gitEntry (name rev : String) : Json :=
  Json.mkObj [("url", s!"https://example.invalid/{name}"), ("type", "git"), ("subDir", Json.null),
    ("scope", ""), ("rev", rev), ("name", name), ("manifestFile", "lake-manifest.json"),
    ("inputRev", Json.null), ("inherited", false), ("configFile", "lakefile.toml")]

/-- A path entry for `name` in the directory `dir`, with the manifest file that the fixture's
entry for `recorded` records and the configuration name `configFile`. -/
private def pathEntry (name dir : String) (configFile := "package.toml") : Json :=
  Json.mkObj [("type", "path"), ("scope", ""), ("name", name), ("manifestFile", "pins.json"),
    ("inherited", false), ("dir", dir), ("configFile", configFile)]

/-- The paths of the captured snapshots, relative to the Verso package's directory as given. -/
private def capturedPaths (dir : FilePath) (snapshots : Array RegulaPolicy.SourceSnapshot) :
    List String :=
  snapshots.toList.map fun snapshot => (snapshot.uri.dropPrefix (dir.toString ++ "/")).toString

/-- The control. In a copy of the fixture, `sharedPinMismatch` finds no mismatch, though
`pins.json` pins `shared` at another revision, and `captureVersoPackage` binds the configuration
file that the entry of `recorded` records, `pins.json` and `recorded`'s own `lake-manifest.json`,
and not its `lakefile.toml`. Then, one at a time:
- `shared` at another revision in `recorded`'s own manifest is reported, and a change of
  `pins.json` changes the capture.
- `shared` at another revision in the package overrides file of `recorded`'s own workspace, or of
  the Verso package's, is reported, and the capture binds that file.
- Without its own manifest, `recorded`'s workspace reads no overrides file, and nothing is
  reported. The Verso package without one is refused by both checks before Lake's load.
- Of two entries for `shared` in `recorded`'s own manifest, the last decides.
- A path entry that the Verso package does not require is neither read nor captured.
- A selection whose entry for `recorded` names a configuration that Lake did not load is refused
  (`LakeSelection.checkSelection`), and the selection of the load is not.
- A Git entry for `recorded` that the Verso package's overrides file replaces by the path entry is
  a local package to both checks.
- With `recorded` as the accepted project, its Lake inputs are still captured, except the package
  overrides file of its own workspace, which a copy of the project writes anew.
- A change of `package.toml` changes the capture, and a change of `lakefile.toml` does not.
- A `package.lean` beside `package.toml` leaves the capture as it was. For the configuration name
  `package`, which has no extension, the capture binds both files.
Each mutation is undone before the next one, and the restored copy captures as before. -/
def check : IO Unit := do
  let root ← rootDirectory
  withScratch root "verso-recorded-paths" fun scratch => do
    copyFixture (root / "examples" / "fixtures" / "verso-recorded-paths") scratch
    let dir := scratch / "verso"
    let recorded := scratch / "recorded"
    let verso : Documentation.VersoPackage := ⟨dir, `Doc, "render"⟩
    let capture := Documentation.captureVersoPackage scratch verso
    let mismatch := Documentation.sharedPinMismatch dir
    let reported := some "shared (against ../recorded)"
    let positive ← capture
    let paths := capturedPaths dir positive
    requireChecks [
      ⟨"no mismatch in the fixture, though pins.json pins shared at another revision",
        (← mismatch).isNone⟩,
      ⟨s!"the capture binds the recorded configuration and both manifests: {paths}",
        ["../recorded/package.toml", "../recorded/pins.json", "../recorded/lake-manifest.json",
          "lakefile.toml", "lake-manifest.json", "Doc.lean", "Render.lean"].all paths.contains⟩,
      ⟨s!"the capture binds no configuration Lake does not load: {paths}",
        !paths.contains "../recorded/lakefile.toml"⟩]
    IO.println "verso recorded paths positive: PASS"
    let own ← withChanged (recorded / "lake-manifest.json") (·.replace pinned other) mismatch
    requireChecks [⟨s!"a pin of recorded's own manifest that differs is reported: {own}",
      own == reported⟩]
    IO.println "verso recorded paths own manifest: PASS"
    let recordedManifest ← withChanged (recorded / "pins.json") (·.replace other pinned) capture
    requireChecks [⟨"a change of the recorded manifest changes the capture",
      recordedManifest != positive⟩]
    IO.println "verso recorded paths recorded manifest: PASS"
    for (anchor, file, name) in
        [(recorded, "../recorded/.lake/package-overrides.json", "recorded's"),
          (dir, ".lake/package-overrides.json", "the Verso package's")] do
      let overrides := anchor / ".lake" / "package-overrides.json"
      let (found, overridden) ← withOverrides overrides #[gitEntry "shared" other] do
        return (← mismatch, capturedPaths dir (← capture))
      requireChecks [⟨s!"a pin of {name} overrides file that differs is reported: {found}",
          found == reported⟩,
        ⟨s!"the capture binds {name} overrides file: {overridden}", overridden.contains file⟩]
      IO.println s!"verso recorded paths overrides of {name} workspace: PASS"
      -- Without its own manifest, a build of `recorded` would resolve its requirements anew and
      -- would not read the overrides file, so its pins are unknown. The Verso package without one
      -- is refused before Lake's load, which would write a manifest. `withRemoved` writes the
      -- original back.
      let manifest := anchor / "lake-manifest.json"
      let (pins, captured, written) ← withRemoved manifest <|
        withOverrides overrides #[gitEntry "shared" other] do
          return (← outcome mismatch, ← outcome (discard capture), ← manifest.pathExists)
      let refused := fun (found : Except String Unit) => match found with
        | .error message => (message.splitOn "no file records").length > 1
        | .ok _ => false
      requireChecks (if anchor == recorded then
          [⟨s!"without its own manifest, recorded's overrides file is not read: {pins.toOption}",
            pins matches .ok none⟩]
        else
          [⟨"the Verso package without a manifest is refused by the pin check",
              refused (pins.map fun _ => ())⟩,
            ⟨"the Verso package without a manifest is refused by the capture", refused captured⟩,
            ⟨"the refusal comes before Lake's load writes a manifest", !written⟩])
      IO.println s!"verso recorded paths overrides of {name} workspace without a manifest: PASS"
    for (entries, expected, order) in [(#[gitEntry "shared" other, gitEntry "shared" pinned], none,
        "an equal pin last"), (#[gitEntry "shared" pinned, gitEntry "shared" other], reported,
        "a different pin last")] do
      let found ← withEntries (recorded / "lake-manifest.json") (fun _ => entries) mismatch
      requireChecks [⟨s!"with {order}, recorded's own manifest gives {found}", found == expected⟩]
      IO.println s!"verso recorded paths last entry, {order}: PASS"
    let (leftover, leftoverPaths) ←
      withEntries (dir / "lake-manifest.json") (·.push (pathEntry "leftover" "../leftover")) do
        return (← mismatch, capturedPaths dir (← capture))
    requireChecks [⟨s!"a path entry Lake does not load is not compared: {leftover}",
        leftover.isNone⟩,
      ⟨s!"a path entry Lake does not load is not captured: {leftoverPaths}",
        !leftoverPaths.any (·.startsWith "../leftover")⟩]
    IO.println "verso recorded paths unloaded path entry: PASS"
    -- A selection that Lake's load does not corroborate: the entry of `recorded` with a
    -- configuration file that Lake did not load for it.
    let (given, altered) ← LakeSelection.withRootSelection dir fun ws selection => do
      let altered : LakeSelection.RootSelection := { selection with
        entries := selection.entries.map fun entry =>
          if entry.name == `recorded then { entry with configFile := "lakefile.toml" } else entry }
      return (← outcome (LakeSelection.checkSelection ws selection),
        ← outcome (LakeSelection.checkSelection ws altered))
    requireChecks [⟨"the selection of the load is corroborated", given matches .ok _⟩,
      ⟨"a selection that names a configuration Lake did not load is refused",
        altered matches .error _⟩]
    IO.println "verso recorded paths selection the load does not corroborate: PASS"
    let replaced := fun (entry : String → Json) (entries : Array Json) => entries.map fun old =>
      if old.getObjValAs? String "name" matches .ok "recorded" then entry "recorded" else old
    -- The Verso package requires `recorded` by Git, its manifest pins it by Git, and its overrides
    -- file replaces that entry by the path entry, so Lake loads `recorded` from its directory.
    let byGit := s!"git = \"https://example.invalid/recorded\"\nrev = \"{other}\""
    let (viaOverride, overridePaths) ←
      withChanged (dir / "lakefile.toml") (·.replace "path = \"../recorded\"" byGit) <|
        withEntries (dir / "lake-manifest.json") (replaced (gitEntry · other)) <|
          withOverrides (dir / ".lake" / "package-overrides.json")
            #[pathEntry "recorded" "../recorded"] <|
            withChanged (recorded / "lake-manifest.json") (·.replace pinned other) do
              return (← mismatch, capturedPaths dir (← capture))
    requireChecks [⟨s!"a Git entry overridden by a path is a local package: {viaOverride}",
        viaOverride == reported⟩,
      ⟨s!"the capture binds the overridden package's configuration: {overridePaths}",
        overridePaths.contains "../recorded/package.toml"⟩]
    IO.println "verso recorded paths Git entry overridden by a path: PASS"
    let accepted ← withOverrides (recorded / ".lake" / "package-overrides.json")
        #[gitEntry "shared" other] do
      return capturedPaths dir (← Documentation.captureVersoPackage recorded verso)
    requireChecks [⟨s!"the accepted project's Lake inputs are captured: {accepted}",
        ["../recorded/package.toml", "../recorded/pins.json",
          "../recorded/lake-manifest.json"].all accepted.contains⟩,
      ⟨s!"the capture leaves out the accepted project's own overrides file: {accepted}",
        !accepted.contains "../recorded/.lake/package-overrides.json"⟩]
    IO.println "verso recorded paths accepted project: PASS"
    let changed ← withChanged (recorded / "package.toml") (· ++ "# changed\n") capture
    requireChecks [⟨"a change of the recorded configuration changes the capture",
      changed != positive⟩]
    IO.println "verso recorded paths recorded configuration: PASS"
    let unloaded ← withChanged (recorded / "lakefile.toml") (· ++ "# changed\n") capture
    requireChecks [⟨"a change of a configuration Lake does not load leaves the capture",
      unloaded == positive⟩]
    IO.println "verso recorded paths default configuration: PASS"
    let sameStem ← withWritten (recorded / "package.lean") leanConfiguration capture
    requireChecks [⟨"a configuration of the recorded stem with another extension is not captured",
      sameStem == positive⟩]
    IO.println "verso recorded paths unread configuration of the same stem: PASS"
    let stemPaths ← withEntries (dir / "lake-manifest.json")
        (replaced (pathEntry · "../recorded" "package")) <|
      withWritten (recorded / "package.lean") leanConfiguration do
        return capturedPaths dir (← capture)
    requireChecks [⟨s!"for a name without an extension, the capture binds each candidate: \
        {stemPaths}",
      ["../recorded/package.lean", "../recorded/package.toml"].all stemPaths.contains⟩]
    IO.println "verso recorded paths configuration name without an extension: PASS"
    requireChecks [⟨"the restored fixture captures as before", (← capture) == positive⟩]
    IO.println "verso recorded paths restored: PASS"

end Regula.Qualification.VersoPaths
