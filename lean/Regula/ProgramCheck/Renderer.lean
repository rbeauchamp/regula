import Regula.Removal
import Regula.Checker.Workspace
import Lake.Load.Manifest

/-! # The renderer's pinned library origin

The renderer admits its third-party library only from Lake's resolved package and Lean's loaded
artifact records. The manifest pin is checked before loading, and its bytes must stay unchanged.
Package loading, import records and file contents remain trusted external observations. -/

namespace Regula.ProgramCheck.Renderer

open Lean System

/-- Resolve the renderer's one sourced library through Lake's package model, after its manifest
names the reviewed upstream revision. This does not authenticate a package from a name prefix.
Assumes: Lake v4.34.1 `Lake/Load/Manifest.lean:192-200,244-273` decodes the manifest and
`Lake/Load/Workspace.lean:57-65` resolves its packages. The pinned checkout and import/build
mechanisms stay trusted, as the renderer's own Verso dependency does. -/
def pinnedPackage (directory : FilePath) : IO _root_.Lake.Package := do
  let manifestFile := directory / _root_.Lake.defaultManifestFile
  let before ← IO.FS.readFile manifestFile
  let some manifest ← _root_.Lake.Manifest.load? manifestFile
    | throw <| IO.userError "renderer library origin: missing Lake manifest"
  let entries := manifest.packages.filter (·.name == `verso)
  let #[entry] := entries
    | throw <| IO.userError "renderer library origin: expected exactly one Verso dependency"
  match entry.src with
  | .git url revision _ _ =>
    unless url == "https://github.com/leanprover/verso" &&
        revision == "cad4b633e75ea769b851f12f9ca3b4f0dfcc625f" do
      throw <| IO.userError "renderer library origin: unreviewed Verso source"
  | .path _ => throw <| IO.userError "renderer library origin: a local Verso cannot borrow the exemption"
  let searchPath ← Lean.searchPathRef.get
  let package ← try
    Regula.Checker.Workspace.withRootWorkspace directory fun workspace => do
      let packages := workspace.packages.filter (·.baseName == entry.name)
      let #[package] := packages
        | throw <| IO.userError "renderer library origin: unresolved or ambiguous Verso package"
      return package
    finally Lean.searchPathRef.set searchPath
  unless (← IO.FS.readFile manifestFile) == before do
    throw <| IO.userError "renderer library origin: manifest changed during resolution"
  return package

/-- Check the renderer using the common reach/admission decision, with its one pinned package
supplied only as Lake resolved it. Artifact equality is established by Removal.libraryOrigins.
Assumes: Lean v4.34.1 `Lean/Elab/Command.lean:323-326` reports this command's source filename;
relative filenames use the compiler's working directory. Source location and directory stability
remain trusted compiler/filesystem observations. -/
def check : Elab.Command.CommandElabM Unit := do
  let directory := (FilePath.mk (← getFileName)).parent.getD "."
  let package ← Elab.Command.liftIO <| pinnedPackage directory
  Regula.Removal.checkProgram (packages := #[package])

end Regula.ProgramCheck.Renderer
