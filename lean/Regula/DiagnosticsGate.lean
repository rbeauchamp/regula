import Lean

/-! # The local gate

The gate of a change is the local gate (`localSteps`), which the no-mistakes validation pipeline
runs on each commit it validates (its `commands.test` in `.no-mistakes.yaml`). It runs, one after
another in the checkout, the steps of the CI workflow's jobs that check a change, after the
provisioning those jobs make: the release checks, the two acceptance steps (the first of which runs
Regula's checker on Regula's own build, the self-check), the Mathlib integration check, and the
builds of the site's tools and of the example library. It runs with the pinned toolchain alone, so
it needs no build before it starts:

```text
lean --run lean/Regula/DiagnosticsGate.lean local    # run every step of the local gate in order
```

The step `local` refuses an empty list, runs the steps one after another and stops at the first
whose exit code is not 0, which fails it (`runSteps`, `runSteps_eq_none_iff`). Each `verify.sh`
invocation keeps its own 420-second deadline, and the gate adds none: it waits for each step to
end. A step killed by a signal ends with a code other than 0. The earlier build outputs that a step
reuses are those that Lake's own traces admit in the checkout; the first acceptance step builds in
a new copy with no artifact cache, as it does by hand.

The gate leaves out `./scripts/verify.sh site`, which reads the repository's tags with
`git ls-remote` without credentials (`Regula.Site.Build.remoteTags`) and so fails while the
repository is private, in CI as well, whose `site` job checks out without credentials.

## Boundaries

`runSteps` is the decision the step executes; its theorems are checked by the kernel each time
`lean --run` elaborates this file. Running a step, its exit code and what it prints are trusted
effects of the operating system and of the step's own program.
-/

namespace Regula.DiagnosticsGate

private def fail {α : Type} (message : String) : IO α :=
  throw <| IO.userError s!"local gate: {message}"

/-- One step of the local gate. -/
inductive Step where
  /-- `./scripts/verify.sh ARGUMENTS`, in the root of the checkout. -/
  | verify (arguments : List String)
  /-- `PROGRAM ARGUMENTS`, with `PROGRAM` found on `PATH` as a workflow step finds it, in the
  directory `dir` of the checkout, relative to its root. -/
  | run (program : String) (arguments : List String) (dir : String)
  deriving DecidableEq, Repr

/-- The program a step starts, its arguments and the directory it runs in. -/
def Step.command : Step → String × List String × String
  | .verify arguments => ("./scripts/verify.sh", arguments, ".")
  | .run program arguments dir => (program, arguments, dir)

/-- The steps of the local gate, in order: CI's `verify` job, which provisions pinned Verso for
the documentation step, runs the release checks and the two acceptance steps; its `mathlib` job,
which provisions the pinned Mathlib and runs the integration check; and the builds of its `site`
job before the site's check, which the gate leaves out. -/
def localSteps : List Step :=
  let program (file : String) (arguments : List String) : Step :=
    .run "lean" ("--run" :: file :: arguments) "."
  [program "lean/RegulaProvision.lean" ["verso"],
    program "lean/Regula/Release.lean" ["unreleased"],
    program "lean/Regula/Release.lean" ["agree"],
    .verify [], .verify ["docs"],
    program "lean/RegulaProvision.lean" ["mathlib"], .verify ["mathlib"],
    .run "lake" ["build", "site", "AuditApp"] ".",
    .run "lake" ["build", "Audit"] "audit"]

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
      else some (step, code step) := rfl

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

/-- A step that `runSteps` reports is one of the steps, and its code is its own and not 0. -/
theorem runSteps_eq_some (code : Step → UInt32) (steps : List Step) (s : Step) (c : UInt32)
    (h : runSteps (m := Id) (fun s => pure (code s)) steps = some (s, c)) :
    s ∈ steps ∧ c = code s ∧ c ≠ 0 := by
  induction steps with
  | nil =>
    have none_eq : (none : Option (Step × UInt32)) = some (s, c) := h
    cases none_eq
  | cons step rest ih =>
    rw [runSteps_cons] at h
    by_cases hc : code step = 0
    · simp only [hc, beq_self_eq_true, ite_true] at h
      obtain ⟨m, e, ne⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ m, e, ne⟩
    · have skip : (code step == 0) = false := by simpa using hc
      simp only [skip, Bool.false_eq_true, ite_false] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨List.mem_cons_self, rfl, hc⟩

/-! ## Steps -/

/-- Run `step` in the checkout, with the standard streams of this process, and give its exit
code. -/
private def runStep (step : Step) : IO UInt32 := do
  let (program, arguments, dir) := step.command
  IO.println s!"local gate: {" ".intercalate (program :: arguments)} (in {dir})"
  (← IO.getStdout).flush
  let child ← IO.Process.spawn
    { cmd := program, args := arguments.toArray, cwd := some (System.FilePath.mk dir),
      stdin := .null }
  child.wait

/-- The `local` step: run the steps of the local gate in order (`runSteps`), and refuse at the
first whose exit code is not 0, or when it has no step. -/
def runLocal : IO Unit := do
  if localSteps.isEmpty then fail "the local gate has no step, so it checks nothing"
  if let some (step, code) ← runSteps runStep localSteps then
    let (program, arguments, dir) := step.command
    fail s!"{" ".intercalate (program :: arguments)} (in {dir}) ended with exit code \
      {code}, so the local gate refuses the change"
  IO.println s!"local gate: each of its {localSteps.length} steps ended with exit code 0"

end Regula.DiagnosticsGate

/-- Command line of `lean --run lean/Regula/DiagnosticsGate.lean`: `local`; returns 2 on a usage
error. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["local"] => Regula.DiagnosticsGate.runLocal; return 0
  | _ =>
    IO.eprintln "usage: lean --run lean/Regula/DiagnosticsGate.lean local"
    return 2
