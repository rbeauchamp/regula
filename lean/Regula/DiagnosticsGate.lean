/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

/-! # The local gate

The gate of a change, which the validation pipeline runs on each commit it validates
(`commands.test` in `.no-mistakes.yaml`). It needs the pinned toolchain alone and no build before it
starts:

```text
lean --run lean/Regula/DiagnosticsGate.lean local
```

It copies the checker's sources to a directory of its own, runs `localSteps` one after another in the
checkout, and stops at the first whose exit code is not 0, which fails it (`runSteps`, `runSteps_eq_none_iff`). It sets no time limit, so a slow or
sleeping machine does not fail it; a step killed by a signal ends with a code other than 0.

`lake build --wfail` and `lake check` are Lean's own commands, and the gate adds no claim of its own
about what they decide.

## Boundaries

`runSteps` is the decision the program executes, and its theorems are checked by the kernel each
time `lean --run` elaborates this file. `specification/RegulaSpecification/Proofs/Gate.lean` proves, at `IO`, that `runLocal`
gives 0 only when it copied each file that `checkerFiles` lists, read from the checkout and written with the same
bytes to the copy, and then each step gave 0, with that copy as the checker and the working directory as the
project. Which files exist is what `System.FilePath.walkDir` lists, which is Lean's. Starting a step, its exit code and what the step does are
trusted effects of the operating system and of Lake. `lake` is the program that `PATH` selects. Each
step sees the checkout as the step before it left it: the gate assumes that no other process changes
the build between its steps. -/

public section

namespace Regula.DiagnosticsGate

/-- One step of the local gate: `lake ARGUMENTS` in the directory `dir` of the checkout, relative to
its root. -/
structure Step where
  /-- The arguments of `lake`. -/
  arguments : List String
  /-- The directory, relative to the root of the checkout. -/
  dir : String
  deriving DecidableEq, Repr

/-- The steps of the gate, in order.

- `lake clean` in the specification's workspace, which holds both packages (`Workspace.clean`,
  `Lake/CLI/Main.lean:1160-1172` at v4.35.0), so that no step reads an output of an earlier build: a
  module of a library that the configuration no longer names would still satisfy an import.
- The checker, built in a separate copy of the program at `checker`.
- The full gate on this checkout (`root`), started from that copy: the language check, then, in a tree of the
  checker's own, the build of the default targets with warnings as errors, Lean's replay of them, and the
  rules. Its exit code is 0 only for a pass of the full verdict. It writes nothing in this checkout.
- The root package's default targets in this checkout, which the proof verdict below reads, and the programs
  of the root package outside the default targets, which only call Lake or are the
  repository's own, and Regula's checker on its own build.
- The specification, with warnings as errors, Lean's replay of it, and Regula's checker on it, the
  path that a project that requires Regula takes. So each theorem of the specification depends on no
  axiom beyond `propext`, `Quot.sound` and `Classical.choice`, on the run of the checker. -/
def localSteps (checker root : String) : List Step :=
  [⟨["clean"], "specification"⟩,
    ⟨["build", "lint"], checker⟩,
    ⟨["exe", "lint", "standard-logical", "full", root], checker⟩,
    ⟨["build", "--wfail"], "."⟩,
    ⟨["build", "--wfail", "Regula", "lint"], "."⟩,
    ⟨["lint"], "."⟩,
    ⟨["build", "--wfail"], "specification"⟩,
    ⟨["check", "--inadvisably-no-sandbox"], "specification"⟩,
    ⟨["lint"], "specification"⟩]

/-- Run `steps` in order with `run`, which runs a step and gives its exit code, and stop at the
first step whose code is not 0: that step with its code, or none when every step ended with 0. -/
def runSteps {m : Type → Type} [Monad m] (run : Step → m UInt32) :
    List Step → m (Option (Step × UInt32))
  | [] => pure none
  | step :: rest => do
    let code ← run step
    if code == 0 then runSteps run rest else pure (some (step, code))

/-- One step of `runSteps`, for steps whose codes `code` gives: the rest runs only after a step
whose code is 0. -/
theorem runSteps_cons (code : Step → UInt32) (step : Step) (rest : List Step) :
    runSteps (m := Id) (fun s => pure (code s)) (step :: rest) =
      if code step == 0 then runSteps (m := Id) (fun s => pure (code s)) rest
      else some (step, code step) := by
  rfl

/-- The decision of `runSteps`, for steps whose codes `code` gives: no step is reported exactly
when every step's code is 0. -/
theorem runSteps_eq_none_iff (code : Step → UInt32) (steps : List Step) :
    runSteps (m := Id) (fun s => pure (code s)) steps = none ↔ ∀ s ∈ steps, code s = 0 := by
  induction steps with
  | nil => exact ⟨(fun _ _ m => nomatch m), fun _ => rfl⟩
  | cons step rest ih =>
    rw [runSteps_cons]
    by_cases h : code step = 0
    · simp [h, ih]
    · simp [h]

/-- What the gate exits with, by what `runSteps` gave: 0 only when no step is reported. -/
def exitOf : Option (Step × UInt32) → UInt32
  | some _ => 1
  | none => 0

/-- Only a run in which no step is reported exits with 0. -/
theorem exitOf_eq_zero_iff (r : Option (Step × UInt32)) : exitOf r = 0 ↔ r = none := by
  cases r <;> simp [exitOf]

/-- Run `step`, with the standard streams of this process, and give its exit code. The inherited
Lean search paths are removed, so a Lake command resolves modules only through the workspace it runs
in. Lake's artifact cache is off: a module that Lake restores from that cache replays no warning, so
`lake build --wfail` would not see it. -/
def runStep (step : Step) : IO UInt32 := do
  IO.println s!"local gate: lake {" ".intercalate step.arguments} (in {step.dir})"
  (← IO.getStdout).flush
  let child ← IO.Process.spawn
    { cmd := "lake", args := step.arguments.toArray, cwd := some (System.FilePath.mk step.dir),
      stdin := .null,
      env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none),
        ("LAKE_ARTIFACT_CACHE", some "false")] }
  child.wait

/-- Each path of `paths` that is no directory, in their order. -/
def regularFiles : List System.FilePath → IO (List System.FilePath)
  | [] => pure []
  | p :: rest => do
    let dir ← p.isDir
    let others ← regularFiles rest
    pure (if dir then others else p :: others)

/-- What the checker's copy needs: its Lake configuration, its pin and its sources. -/
def checkerFiles : IO (List System.FilePath) := do
  let sources ← System.FilePath.walkDir "lean"
  let files ← regularFiles sources.toList
  pure (["lakefile.toml", "lake-manifest.json", "lean-toolchain"].map System.FilePath.mk ++ files)

/-- Copy one file to the same relative path below `target`, with the directories above it. -/
def copyFile (target file : System.FilePath) : IO Unit := do
  let to := target / file
  if let some dir := to.parent then IO.FS.createDirAll dir
  IO.FS.writeBinFile to (← IO.FS.readBinFile file)

/-- Copy each of `files` to `target`. -/
def copyAll (target : System.FilePath) : List System.FilePath → IO Unit
  | [] => pure ()
  | file :: rest => do
    copyFile target file
    copyAll target rest

/-- Copy the checker's files to `target`. -/
def copyChecker (target : System.FilePath) : IO Unit := do
  copyAll target (← checkerFiles)

/-- What `runSteps` gave, said on the standard streams. -/
def sayResult (steps : List Step) : Option (Step × UInt32) → IO Unit
  | some (step, code) =>
    IO.eprintln s!"local gate: lake {" ".intercalate step.arguments} (in {step.dir}) ended with \
      exit code {code}, so the local gate refuses the change"
  | none => IO.println s!"local gate: each of its {steps.length} steps ended with exit code 0"

/-- The steps, then what they gave. `specification/RegulaSpecification/Proofs/Gate.lean` proves of this definition, at `IO`,
that it gives 0 only when each step gave 0. -/
def runIn (target root : String) : IO UInt32 := do
  let steps := localSteps target root
  let result ← runSteps runStep steps
  sayResult steps result
  return exitOf result

/-- Run the steps of the gate, and give 0 only when each ended with exit code 0. The checker's copy
lies in a directory of its own outside the checkout, removed at the end. -/
def runLocal : IO UInt32 := do
  let target ← IO.FS.createTempDir
  try
    copyChecker target
    runIn target.toString (← IO.currentDir).toString
  finally
    IO.FS.removeDirAll target

end Regula.DiagnosticsGate

/-- Command line of `lean --run lean/Regula/DiagnosticsGate.lean`: `local`; returns 2 on a usage
error. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["local"] => Regula.DiagnosticsGate.runLocal
  | _ =>
    IO.eprintln "usage: lean --run lean/Regula/DiagnosticsGate.lean local"
    return 2
