import Regula.Removal
import Regula.TaskManagerCheck
import Regula.Site.Artifact

/-! # Site builder entry point

Command-line entrypoint of the rule-reference site builder (`lake exe site`). -/

open System

/-- The build that an argument list names, `site build --out DIR --evidence SHARD...`: its output
directory and evidence shards. -/
def parseSiteBuild : List String → Option (FilePath × List FilePath)
  | "build" :: "--out" :: out :: "--evidence" :: evidence@(_ :: _) =>
    some (out, evidence.map FilePath.mk)
  | _ => none

/-- The output directory that an argument list names from its leading arguments,
`build --out DIR`, so that one the parser refuses for a later argument still has its directory
recognized. -/
def siteOutputNamed : List String → Option FilePath
  | "build" :: "--out" :: out :: _ => some out
  | _ => none

/-- On an argument list that the parser accepts, the directory named by its leading arguments is
the build's own. -/
theorem siteOutputNamed_of_parse {args : List String} {out : FilePath} {evidence : List FilePath}
    (h : parseSiteBuild args = some (out, evidence)) : siteOutputNamed args = some out := by
  unfold parseSiteBuild at h
  split at h
  · cases h; rfl
  · cases h

/-- `site build --out DIR --evidence SHARD...` builds and checks the Pages artifact. -/
def siteMain (args : List String) : IO UInt32 := do
  match parseSiteBuild args with
  | some (out, evidence) =>
    Regula.Site.Build.build evidence out
    return 0
  | none =>
    IO.eprintln "usage: lake exe site build --out DIR --evidence SHARD.json [SHARD.json ...]"
    return 2

/-- The refusal of the build in a process without Lean's task manager
(`Regula.TaskManager.guard`): it invalidates the artifact of the directory that the arguments name
(`siteOutputNamed`) as a build does before its first step (`Regula.Site.Build.invalidateArtifact`),
printing a line when it cannot, and returns 1. Arguments that name no directory invalidate
nothing. -/
def refuseSiteBuild (_reason : String) (args : List String) : IO UInt32 := do
  if let some out := siteOutputNamed args then
    try discard <| Regula.Site.Build.invalidateArtifact out
    catch error => IO.eprintln s!"site: could not invalidate the artifact at {out}: {error}"
  return 1

/-- `siteMain` on the command-line arguments. A process without Lean's task manager is refused
before the build starts, with exit code 1 (`Regula.TaskManager.guard`). -/
def main : List String → IO UInt32 :=
  Regula.TaskManager.guard "site" refuseSiteBuild siteMain

-- The removals that the compiled code of `main`, and of the initializers of the modules it links,
-- reaches are the filesystem observer's and those that `Regula.Removal.libraryRemovals` lists: the
-- build of this module fails otherwise (`Regula.Removal.checkProgram`).
run_cmd Regula.Removal.checkProgram

-- A program that needs Lean's task manager starts through its guard (`Regula.TaskManager.guard`),
-- and its refusal needs none: the build of this module fails otherwise
-- (`Regula.TaskManagerCheck.checkProgram`).
run_cmd Regula.TaskManagerCheck.checkProgram
