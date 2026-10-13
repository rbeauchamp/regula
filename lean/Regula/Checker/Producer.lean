import Lean
import Regula.RegistryCodec
import RegulaCore.CopyProgram
import RegulaCore.Presence

/-! # Producer build identity

Build identity shared by operational result and raw worker transports. -/
namespace Regula.Checker.Producer
open Lean Regula
/-- Captured when this module is elaborated, not from an adopter's working directory. -/
elab "regula_build_revision" : term => do
  let source := System.FilePath.mk (← getFileName)
  let some root := source.parent >>= (·.parent) >>= (·.parent) >>= (·.parent)
    | throwError "cannot identify checker package source directory"
  let root ← IO.FS.realPath root
  unless ← Regula.Filesystem.isPresent (root / "lakefile.lean") do
      throwError "checker package configuration unavailable"
  let head ← Regula.Filesystem.Construction.gitOutput root #["rev-parse", "HEAD"]
  unless head.exitCode == 0 do throwError "cannot identify checker source revision"
  let state ← Regula.Filesystem.Construction.gitOutput root
    #["status", "--porcelain", "--untracked-files=normal"]
  unless state.exitCode == 0 do throwError "cannot identify checker source state"
  let suffix := if state.stdout.isEmpty then "" else ":unreleased-worktree"
  return mkStrLit (head.stdout.trimAscii.toString ++ suffix)

/-- This checker build's producer identity in reports and worker packets: its version
(`Regula.installed`: the release, or `unreleased`), the Lean version string, and the Git
revision of the checker source captured when this module was elaborated, suffixed
`:unreleased-worktree` when that worktree had changes. -/
def identity : RegistryCodec.ProducerIdentity := {
  producerVersion := installed.spelling
  toolchain := Lean.versionString
  sourceRevision := regula_build_revision }

end Regula.Checker.Producer
