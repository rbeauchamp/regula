import Lean

/-! # The local gate

The gate of a change is the local gate (`localSteps`), which the no-mistakes validation pipeline
runs on each commit it validates (its `commands.test` in `.no-mistakes.yaml`). It runs, one after
another in the checkout, the steps of the CI workflow's jobs that check a change, after the
provisioning those jobs make: the release checks, the two acceptance steps (the first of which runs
Regula's checker on Regula's own build, the self-check), the builds of the site's tools and of the
example library, and the site check. It runs with the pinned toolchain alone, so it needs no build
before it starts:

```text
lean --run lean/Regula/DiagnosticsGate.lean local    # run every step of the local gate in order
```

The step `local` refuses an empty list, runs the steps one after another and stops at the first
whose exit code is not 0, which fails it (`runSteps`, `runSteps_eq_none_iff`). Each `verify.sh`
invocation keeps its own 420-second deadline, and the gate adds none: it waits for each step to
end. A step killed by a signal ends with a code other than 0. The earlier build outputs that a step
reuses are those that Lake's own traces admit in the checkout; the first acceptance step builds in
a new copy with no artifact cache, as it does by hand.

## The site check

`./scripts/verify.sh site` (`siteCheck`) renders the site from the commit and checks the artifact,
which a change can fail. Before it does, it reads two things that a change cannot alter: the
repository's tags, with `git ls-remote` (`Regula.Site.Build.remoteTags`), and the release asset of
each listed release, with `curl` (`Regula.Site.Build.downloadRelease`). Each read uses no
credentials, and a failed read refuses. It reads neither the deployed site nor any external link.

So, after every other step has passed, the gate makes the same kinds of read itself (`siteReads`).
When one does not answer HTTP status 200, the check does not run and the gate names each such answer
and passes on the other steps (`Outcome.siteNotRun`, `runGate_siteNotRun_iff`): an outage of GitHub
says nothing about the change, and a blocked gate costs more than one run without this check, which
a later run of the gate makes. When both answer, the check runs and its exit code decides
(`runGate_passed_iff`, `runGate_site_failure`), so a read of the check that fails after the gate's
own reads fails the gate, with the check's message, until a new run. The gate's reads use its own
address rather than the check's, because a change can break the check's: `Regula.Site.repository`
set to a wrong address fails the check here, and it does not read as an outage. The deployed site
lagging `main` cannot fail the check, which does not read it.

The site build refuses what an earlier build left (`Regula.Site.Build.requireFresh`) and removes
nothing, and the gate can run again in one checkout, so the gate first removes those paths
(`siteOutputs`). It removes what is at one of them only when the path's parent, fully resolved, is
that same parent under the canonical root of the checkout and the entry is not a symbolic link
(`removal`, `removal_ne_leave_iff`). So it leaves a symbolic link at one of them, and a path reached
through a symbolic link, with the target untouched, and the build refuses that path by name when
the check runs.

## Boundaries

`runSteps`, `runGate` and `removal` are the decisions the step executes; their theorems are checked
by the kernel each time `lean --run` elaborates this file. Running a step, its exit code, what it
prints, what `curl` reports and what `realPath`, `symlinkMetadata` and the removals do are trusted
effects of the operating system, of the step's own program and of the network. Two gate runs at one
time in one checkout are not a supported use. Accepted risk, because these are generated outputs in
the owner's own checkout: another process that replaces a path with a link between the gate's check
and its removal defeats the check.
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

/-- The steps of the local gate before the site check, in order: CI's `verify` job, which provisions
pinned Verso for the documentation step, runs the release checks and the two acceptance steps; and
the builds of its `site` job before the site's check (`siteCheck`). -/
def localSteps : List Step :=
  let program (file : String) (arguments : List String) : Step :=
    .run "lean" ("--run" :: file :: arguments) "."
  [program "lean/RegulaProvision.lean" ["verso"],
    program "lean/Regula/Release.lean" ["unreleased"],
    program "lean/Regula/Release.lean" ["agree"],
    .verify [], .verify ["docs"],
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

/-! ## The site check -/

/-- The check of the site, which the gate runs after `localSteps`. -/
def siteCheck : Step := .verify ["site"]

/-- The gate's reads before the site check. The first is the request with which `git ls-remote`
starts over HTTP (observed with `GIT_CURL_VERBOSE` on Git 2.54.0), for the read of
`Regula.Site.Build.remoteTags`. The second is the asset of a published release, for the reads of
`Regula.Site.Build.downloadRelease`; a published release keeps its asset
(docs/guides/website.md#versions-and-routes), so this address does not change. -/
def siteReads : List String :=
  let repository := "https://github.com/rbeauchamp/regula"
  [repository ++ "/info/refs?service=git-upload-pack",
    repository ++ "/releases/download/v0.11.1/regula-site-0.11.1.tar.gz"]

/-- The paths, relative to the root of the checkout, that the site build refuses when an earlier
build left them (`Regula.Site.Build.outputs`). -/
def siteOutputs : List String :=
  ["_site", "tmp/site-build", "website/Generated", "website/Generated.lean", "tmp/site-release"]

/-- What one of `siteReads` answered: `curl`'s exit code, the HTTP status it wrote and its standard
error. -/
structure Answer where
  /-- The address that was read. -/
  url : String
  /-- The exit code of `curl`. -/
  exitCode : UInt32
  /-- The HTTP status that `curl` wrote, `000` when it got none. -/
  status : String
  /-- What `curl` wrote to its standard error. -/
  message : String
  deriving DecidableEq, Repr

/-- The transfer completed with the HTTP status that the site check's reads take as present. -/
def Answer.available (a : Answer) : Bool := a.exitCode == 0 && a.status == "200"

/-- An answer that is not `Answer.available`. -/
abbrev Refusal := { a : Answer // a.available = false }

/-- The answers that are not `Answer.available`, in order, each with its proof. -/
def refusals : List Answer → List Refusal
  | [] => []
  | a :: rest =>
    if h : a.available = false then ⟨a, h⟩ :: refusals rest else refusals rest

/-- `refusals` keeps exactly the answers that are not available. -/
theorem mem_refusals (answers : List Answer) (r : Refusal) :
    r ∈ refusals answers ↔ r.val ∈ answers := by
  induction answers with
  | nil => simp [refusals]
  | cons a rest ih =>
    by_cases h : a.available = false
    · simp only [refusals, h, ↓reduceDIte, List.mem_cons, ih, Subtype.ext_iff]
    · have ne : r.val ≠ a := fun e => h (e ▸ r.property)
      simp [refusals, h, ih, ne]

/-- There is no refusal exactly when each answer is available. -/
theorem refusals_eq_nil_iff (answers : List Answer) :
    refusals answers = [] ↔ ∀ a ∈ answers, a.available = true := by
  constructor
  · intro h a m
    by_cases av : a.available = false
    · have := (mem_refusals answers ⟨a, av⟩).mpr m
      simp [h] at this
    · simpa using av
  · intro h
    cases e : refusals answers with
    | nil => rfl
    | cons r rest =>
      have m := (mem_refusals answers r).mp (e ▸ List.mem_cons_self)
      have := h _ m
      have := r.property
      simp_all

/-- How a run of the gate ended. No constructor passes without the site check's result except
`siteNotRun`, which cannot be built without an answer that names why. -/
inductive Outcome where
  /-- A step ended with this exit code, which is not 0. -/
  | failed (step : Step) (code : UInt32)
  /-- Each step of the gate ended with exit code 0, the site check among them. -/
  | passed
  /-- Each step before the site check ended with exit code 0, and the check did not run, because
  of these answers to `siteReads`. -/
  | siteNotRun (first : Refusal) (rest : List Refusal)

/-- Run `steps`; when each ended with 0, `read` the answers to `siteReads`; when each is available,
run `siteCheck`, whose exit code then decides. -/
def runGate {m : Type → Type} [Monad m] (run : Step → m UInt32) (read : m (List Answer))
    (steps : List Step) : m Outcome := do
  match ← runSteps run steps with
  | some (step, code) => return .failed step code
  | none =>
    match refusals (← read) with
    | first :: rest => return .siteNotRun first rest
    | [] =>
      let code ← run siteCheck
      return if code == 0 then .passed else .failed siteCheck code

/-- `runGate` for steps whose codes `code` gives and reads that gave `answers`. -/
abbrev gateOf (code : Step → UInt32) (answers : List Answer) (steps : List Step) : Outcome :=
  runGate (m := Id) (fun s => pure (code s)) (pure answers) steps

/-- The gate passes with the check exactly when each step, each read and the check itself passed:
a run in which the check did not run or did not end with 0 is not `Outcome.passed`. -/
theorem runGate_passed_iff (code : Step → UInt32) (answers : List Answer) (steps : List Step) :
    gateOf code answers steps = .passed ↔
      (∀ s ∈ steps, code s = 0) ∧ (∀ a ∈ answers, a.available = true) ∧ code siteCheck = 0 := by
  rw [← runSteps_eq_none_iff, ← refusals_eq_nil_iff]
  show (match runSteps (m := Id) (fun s => pure (code s)) steps with
    | some (step, c) => Outcome.failed step c
    | none => match refusals answers with
      | first :: rest => Outcome.siteNotRun first rest
      | [] => if code siteCheck == 0 then Outcome.passed else .failed siteCheck (code siteCheck))
    = .passed ↔ _
  cases runSteps (m := Id) (fun s => pure (code s)) steps with
  | some p => simp
  | none =>
    cases refusals answers with
    | cons r rest => simp
    | nil =>
      by_cases h : code siteCheck = 0
      · simp [h]
      · simp [h]

/-- The gate reports the check as not run exactly when each step passed and a read was refused,
and it names each refused answer. So it never leaves the check out for another reason. -/
theorem runGate_siteNotRun_iff (code : Step → UInt32) (answers : List Answer) (steps : List Step)
    (first : Refusal) (rest : List Refusal) :
    gateOf code answers steps = .siteNotRun first rest ↔
      (∀ s ∈ steps, code s = 0) ∧ refusals answers = first :: rest := by
  rw [← runSteps_eq_none_iff]
  show (match runSteps (m := Id) (fun s => pure (code s)) steps with
    | some (step, c) => Outcome.failed step c
    | none => match refusals answers with
      | first :: rest => Outcome.siteNotRun first rest
      | [] => if code siteCheck == 0 then Outcome.passed else .failed siteCheck (code siteCheck))
    = .siteNotRun first rest ↔ _
  cases runSteps (m := Id) (fun s => pure (code s)) steps with
  | some p => simp
  | none =>
    cases refusals answers with
    | cons r more => simp
    | nil =>
      by_cases h : code siteCheck = 0
      · simp [h]
      · simp [h]

/-- When each step passed and each read was available, an exit code of the check other than 0 fails
the gate: the failure of a change that the check finds is never a pass. -/
theorem runGate_site_failure (code : Step → UInt32) (answers : List Answer) (steps : List Step)
    (hs : ∀ s ∈ steps, code s = 0) (ha : ∀ a ∈ answers, a.available = true)
    (hc : code siteCheck ≠ 0) :
    gateOf code answers steps = .failed siteCheck (code siteCheck) := by
  have h1 := (runSteps_eq_none_iff code steps).mpr hs
  have h2 := (refusals_eq_nil_iff answers).mpr ha
  show (match runSteps (m := Id) (fun s => pure (code s)) steps with
    | some (step, c) => Outcome.failed step c
    | none => match refusals answers with
      | first :: rest => Outcome.siteNotRun first rest
      | [] => if code siteCheck == 0 then Outcome.passed else .failed siteCheck (code siteCheck))
    = _
  rw [h1, h2]
  simp [hc]

/-! ## Removing the outputs of an earlier build -/

/-- What the gate does with an entry that is present at one of `siteOutputs`. -/
inductive Removal where
  /-- Leave the entry where it is. -/
  | leave
  /-- Remove the directory and what is below it. -/
  | removeDir
  /-- Remove the entry, which is not a directory. -/
  | removeFile
  deriving DecidableEq, Repr

/-- The decision for an entry of type `type`, where `parentResolves` says that the path's parent,
fully resolved, is that same parent under the canonical root of the checkout. -/
def removal (parentResolves : Bool) (type : IO.FS.FileType) : Removal :=
  match parentResolves, type with
  | false, _ | true, .symlink => .leave
  | true, .dir => .removeDir
  | true, .file | true, .other => .removeFile

/-- The gate removes an entry exactly when its parent resolves to itself and the entry is not a
symbolic link: it removes nothing through a linked ancestor, and each present entry that is not a
link under a parent that resolves. -/
theorem removal_ne_leave_iff (parentResolves : Bool) (type : IO.FS.FileType) :
    removal parentResolves type ≠ .leave ↔ parentResolves = true ∧ type ≠ .symlink := by
  cases parentResolves <;> cases type <;> simp [removal]

/-- The gate removes recursively exactly a directory under a parent that resolves to itself. -/
theorem removal_eq_removeDir_iff (parentResolves : Bool) (type : IO.FS.FileType) :
    removal parentResolves type = .removeDir ↔ parentResolves = true ∧ type = .dir := by
  cases parentResolves <;> cases type <;> simp [removal]

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

/-- Make one of `siteReads`, with the options of `Regula.Site.Build.downloadRelease` and its time
limit, so a read that does not answer ends. -/
private def readSite (url : String) : IO Answer := do
  let out ← IO.Process.output
    { cmd := "curl", stdin := .null,
      args := #["--silent", "--show-error", "--location", "--max-time", "120", "--output",
        "/dev/null", "--write-out", "%{http_code}", url] }
  return { url, exitCode := out.exitCode, status := out.stdout.trimAscii.toString,
           message := out.stderr.trimAscii.toString }

/-- Remove what is at `path`, a path under the canonical root of the checkout, from an earlier site
build, as `removal` decides. The final entry is read by a read that follows no link, so an absent
path is left absent, and `realPath` only reads a parent that exists. A symbolic link at `path`, and
a path whose parent does not resolve to itself, stay, and their targets are not touched.
`IO.FS.removeDirAll` follows no link below the directory (`Init/System/IO.lean:1335-1342` at
v4.35.0). -/
private def removeOutput (path : System.FilePath) : IO Unit := do
  let type ← try
      pure (some (← path.symlinkMetadata).type)
    catch e => match e with
      | .noFileOrDirectory .. => pure none
      | _ => throw e
  match type with
  | none => pure ()
  | some type =>
    let parentResolves ← match path.parent with
      | some parent => pure ((← IO.FS.realPath parent) == parent)
      | none => pure false
    match removal parentResolves type with
    | .leave => pure ()
    | .removeDir => IO.FS.removeDirAll path
    | .removeFile => IO.FS.removeFile path

/-- The `local` step: remove the outputs of an earlier site build (`siteOutputs`) under the
canonical root of the checkout, run the steps of the local gate in order (`runGate`), and refuse at
the first whose exit code is not 0, or when it has no step. An output left because it is a symbolic
link or is reached through one is refused by the site build, when the check runs. A run in which
the site check could not run passes on its other steps, and its last lines name each answer that
kept the check from running. -/
def runLocal : IO Unit := do
  if localSteps.isEmpty then fail "the local gate has no step, so it checks nothing"
  let root ← IO.FS.realPath "."
  for path in siteOutputs do removeOutput (root / path)
  match ← runGate runStep (siteReads.mapM readSite) localSteps with
  | .failed step code =>
    let (program, arguments, dir) := step.command
    fail s!"{" ".intercalate (program :: arguments)} (in {dir}) ended with exit code \
      {code}, so the local gate refuses the change"
  | .passed =>
    IO.println s!"local gate: each of its {localSteps.length + 1} steps ended with exit code 0, \
      the site check among them"
  | .siteNotRun first rest =>
    IO.println s!"local gate: the site check DID NOT RUN, so this pass does not cover it; each \
      of the other {localSteps.length} steps ended with exit code 0. The gate's reads of GitHub \
      answered:"
    for r in first :: rest do
      IO.println s!"local gate:   {r.val.url}: curl exit code {r.val.exitCode}, HTTP status \
        {r.val.status}: {r.val.message}"

end Regula.DiagnosticsGate

/-- Command line of `lean --run lean/Regula/DiagnosticsGate.lean`: `local`; returns 2 on a usage
error. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["local"] => Regula.DiagnosticsGate.runLocal; return 0
  | _ =>
    IO.eprintln "usage: lean --run lean/Regula/DiagnosticsGate.lean local"
    return 2
