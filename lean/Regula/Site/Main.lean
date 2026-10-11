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

-- Each removal of a directory or file that the compiled code of `main` and of the initializers of
-- the linked modules reaches is in `Regula.Removal.removeDecided`, which removes only what the
-- decision `Regula.Removal.removal` decided to remove (`removal_remove_iff`), or is one of the
-- single-file removals of Lean's library that `Regula.Removal.libraryRemovals` lists. The check
-- follows every compiled declaration, of this package and of the libraries, and the build of this
-- module fails when it finds another call of a removal primitive or a declaration whose compiled
-- code it cannot read.
run_cmd do
  let (raw, unknown) := Regula.Removal.rawRemovals (← Lean.getEnv) ``main
  unless raw.isEmpty do
    Lean.throwError m!"the site executable removes without `Regula.Removal.removal`: \
      {raw.toList.map fun (caller, primitive) => m!"{caller} calls {primitive}"}"
  unless unknown.isEmpty do
    Lean.throwError m!"the site executable reaches declarations whose compiled code is not \
      available, so their removals are unknown: {unknown.toList}"
