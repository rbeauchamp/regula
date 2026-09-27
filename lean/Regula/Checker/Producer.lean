import Lean
import Regula.RegistryCodec

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
  unless ← (root / "lakefile.lean").pathExists do throwError "checker package configuration unavailable"
  let head ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "rev-parse", "HEAD"] }
  unless head.exitCode == 0 do throwError "cannot identify checker source revision"
  let state ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "status", "--porcelain", "--untracked-files=normal"] }
  unless state.exitCode == 0 do throwError "cannot identify checker source state"
  let suffix := if state.stdout.isEmpty then "" else ":unreleased-worktree"
  return mkStrLit (head.stdout.trimAscii.toString ++ suffix)

/-- This checker build's producer identity in reports and worker packets: version
`unreleased`, the Lean version string, and the Git revision of the checker source captured
when this module was elaborated, suffixed `:unreleased-worktree` when that worktree had
changes. -/
def identity : RegistryCodec.ProducerIdentity := {
  producerVersion := "unreleased"
  toolchain := Lean.versionString
  sourceRevision := regula_build_revision }

end Regula.Checker.Producer
