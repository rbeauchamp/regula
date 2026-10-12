import Regula.Removal
import Regula.Site.Artifact

/-! # Site builder entry point

Command-line entrypoint of the rule-reference site builder (`lake exe site`). -/

open System

/-- `site build --out DIR --evidence SHARD...` builds and checks the Pages artifact. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | "build" :: "--out" :: out :: "--evidence" :: evidence@(_ :: _) =>
    Regula.Site.Build.build (evidence.map FilePath.mk) out
    return 0
  | _ =>
    IO.eprintln "usage: lake exe site build --out DIR --evidence SHARD.json [SHARD.json ...]"
    return 2

-- The removals that the compiled code of `main`, and of the initializers of the modules it links,
-- reaches are the filesystem observer's and those that `Regula.Removal.libraryRemovals` lists: the
-- build of this module fails otherwise (`Regula.Removal.checkProgram`).
run_cmd Regula.Removal.checkProgram
