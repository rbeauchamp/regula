import Lean

/-! # The diagnostics gate

The `Diagnostics` workflow (`.github/workflows/diagnostics.yml`) runs on every pull request, every
push to `main`, nightly and on dispatch. Its first job, `compiler`, prepares the selected compiler.
The next, `applies`, needs it and has no `if:`, so it runs only once `compiler` succeeded; it
decides which of its partition jobs apply to the run, and each partition job runs only when it
applies. Its last job,
`diagnostics`, runs once every other job has finished, whatever their results, and passes exactly
when `applies` succeeded and each partition job passed and applies, or was skipped and does not
apply. It is the check that the ruleset of `main` requires, so it reports on every pull request.
Both steps run with the pinned toolchain alone, so they need no build:

```text
lean --run lean/Regula/DiagnosticsGate.lean applies  # decide which partition jobs apply
lean --run lean/Regula/DiagnosticsGate.lean gate     # refuse unless each passed as it applies
```

## Which jobs apply

`inputs` is the one statement of the paths the campaigns depend on: the checker, the rules and
their examples, the adopter fixtures, the application and fixture sources the structural and
execution controls mutate, Lake configuration and manifests, `scripts/verify.sh`, the provisioning
and compiler-installation programs, the snapshot controller, the dependency mode, the declared
compiler source and snapshot selections, the workflow, both preparation workflows and the
provisioning action. `decisions` decides each
partition job by its job id: the campaigns (`campaign`) on every run other than a pull request's
(`campaign_of_ne`), and on a pull request's exactly when one of its changed paths is an input
(`campaign_pullRequest_iff`); the nightly rule-example shards (`rule-examples-nightly`) on the
schedule alone. A pull request whose every changed path lies in `docs/` or `website/`, or is
`README.md` or `AGENTS.md`, runs no campaign (`campaign_documentation`). A pull request's changed
paths are those at which the checked-out commit, the merge commit GitHub creates and tests,
differs from its first parent, the head of the base branch: every path added, deleted or modified
there, a rename as both of its paths.

## The gate

`verdict` is the gate's decision over what the workflow's `needs` context reports: the job
`applies` succeeded, it decided every other job the gate needs and no job the gate does not need,
and each of those jobs passed when it was decided to apply and was skipped when it was decided not
to (`verdict_iff`, with `admits_iff`). A failed or cancelled job is refused, so is a job that ran
out of time, which GitHub reports as one of the two, and so is a job decided to apply that was
skipped, as the jobs that had not started are when a run is cancelled. A job the gate needs that
`applies` did not decide, and a job `applies` decided that the gate does not need, fail the gate;
that every partition job of the workflow is in the gate's `needs` is the workflow's wiring, which
no step here observes.

## Boundaries

`verdict`, `admits` and `decisions` are the decisions the steps execute; their theorems are checked
by the kernel each time `lean --run` elaborates this file. GitHub (the event, the merge commit it
creates for a pull request, the `needs` context, a job's `if:` that reads the decision, the
implicit `success()` that runs `applies` only once `compiler` succeeded, its results, timeouts and
cancellation, and the ruleset that requires the check) and `git` (the
commits it fetched and the paths `diff-tree` lists) are trusted and observed, not proved.
-/

namespace Regula.DiagnosticsGate

open Lean

private def fail {α : Type} (message : String) : IO α :=
  throw <| IO.userError s!"diagnostics gate: {message}"

/-! ## Which jobs apply -/

/-- An input of the diagnostics campaigns, as the components of its path from the repository
root. -/
inductive Input where
  /-- One file. -/
  | file (path : List String)
  /-- Every file below a directory. -/
  | tree (dir : List String)

/-- The components of the input's path. -/
def Input.path : Input → List String
  | .file path => path
  | .tree dir => dir

/-- Whether the changed path `p`, as its components, is the input or lies below it. -/
def Input.covers : Input → List String → Bool
  | .file path, p => p == path
  | .tree dir, p => dir.isPrefixOf p

/-- The paths the campaigns depend on, and the only statement of them: the checker, the rules and
their examples, the adopter fixtures in `examples/lake-lint-toml` and `examples/build-lint`, the
application and fixture sources the structural and execution controls mutate, Lake configuration
and manifests, `scripts/verify.sh`, the provisioning and compiler-installation programs, the
snapshot controller, the dependency mode, the declared compiler source and snapshot selections,
the workflow, both preparation workflows and the provisioning action. This module is an input,
below `lean/Regula`. -/
def inputs : List Input := [
  .tree ["lean", "Regula"],
  .tree ["lean", "RegulaPolicy"],
  .file ["lean", "RegulaPolicy.lean"],
  .tree ["lean", "RegulaCore"],
  .tree ["lean", "RegulaQualification"],
  .file ["lean", "RegulaVerification.lean"],
  .file ["lean", "RegulaProvision.lean"],
  .file ["lean", "RegulaCompiler.lean"],
  .file ["lean", "RegulaSnapshot.lean"],
  .file ["dependency-build-mode"],
  .file [".github", "compiler-source.json"],
  .file [".github", "snapshot-compiler.json"],
  .file [".github", "compiler-snapshot.json"],
  .tree ["lean", "AuditApp"],
  .file ["lean", "AuditApp.lean"],
  .file ["lean", "Main.lean"],
  .tree ["lean", "Fixtures"],
  .file ["audit", "lakefile.lean"],
  .file ["audit", "lake-manifest.json"],
  .file ["audit", "foundation_manifest.json"],
  .tree ["examples", "rules"],
  .tree ["examples", "lake-lint-toml"],
  .tree ["examples", "build-lint"],
  .file ["lakefile.lean"],
  .file ["lake-manifest.json"],
  .file ["lean-toolchain"],
  .file ["foundation_manifest.json"],
  .file ["scripts", "verify.sh"],
  .file [".github", "workflows", "diagnostics.yml"],
  .file [".github", "workflows", "compiler.yml"],
  .file [".github", "workflows", "snapshot.yml"],
  .tree [".github", "actions", "provision"]]

/-- Whether some input covers the changed path `p`. -/
def isInput (p : List String) : Bool := inputs.any (·.covers p)

/-- The event that started the run, as `GITHUB_EVENT_NAME` names it. -/
inductive Event where
  /-- A pull request was opened, reopened or pushed to. -/
  | pullRequest
  /-- A push to `main`. -/
  | push
  /-- The nightly schedule. -/
  | schedule
  /-- A dispatch, such as the Release workflow's on the branch of its pull request. -/
  | workflowDispatch
  deriving DecidableEq, Repr

/-- The event `GITHUB_EVENT_NAME` names, if the workflow runs on it. -/
def Event.parse : String → Option Event
  | "pull_request" => some .pullRequest
  | "push" => some .push
  | "schedule" => some .schedule
  | "workflow_dispatch" => some .workflowDispatch
  | _ => none

/-- Whether the campaigns apply to a run of `event` whose changed paths are `changed`: on a pull
request, exactly when a changed path is an input; on every other run. -/
def campaignApplies : Event → List (List String) → Bool
  | .pullRequest, changed => changed.any isInput
  | _, _ => true

/-- Whether the nightly rule-example shards apply to a run of `event`: on the schedule alone. -/
def nightlyApplies : Event → Bool
  | .schedule => true
  | _ => false

/-- Which partition jobs apply to a run of `event` whose changed paths are `changed`, by job id:
the decision `applies` writes and each partition job's `if:` reads. -/
def decisions (event : Event) (changed : List (List String)) : List (String × Bool) :=
  [("campaign", campaignApplies event changed), ("rule-examples-nightly", nightlyApplies event)]

/-- On a pull request, the campaigns apply exactly when some input covers a changed path. -/
theorem campaign_pullRequest_iff (changed : List (List String)) :
    campaignApplies .pullRequest changed = true ↔
      ∃ p ∈ changed, ∃ i ∈ inputs, i.covers p = true := by
  simp [campaignApplies, isInput]

/-- On every run other than a pull request's, the campaigns apply. -/
theorem campaign_of_ne {event : Event} (h : event ≠ .pullRequest) (changed : List (List String)) :
    campaignApplies event changed = true := by
  cases event <;> simp_all [campaignApplies]

/-- A path an input covers starts with the input's first component. -/
theorem Input.covers_head {i : Input} {p : List String} (hi : i.path ≠ [])
    (h : i.covers p = true) :
    p.head? = i.path.head? := by
  cases i with
  | file path => simp_all [covers, Input.path]
  | tree dir =>
    simp only [covers, List.isPrefixOf_iff_prefix] at h
    obtain ⟨rest, rfl⟩ := h
    cases dir with
    | nil => simp [path] at hi
    | cons a dir => simp [path]

/-- On a pull request, the campaigns apply only when a changed path starts with the first component
of an input. -/
theorem campaign_head {changed : List (List String)}
    (h : campaignApplies .pullRequest changed = true) :
    ∃ p ∈ changed, ∃ i ∈ inputs, p.head? = i.path.head? := by
  obtain ⟨p, hp, i, hi, hc⟩ := (campaign_pullRequest_iff changed).mp h
  have hne : i.path ≠ [] := by
    simp only [inputs, List.mem_cons, List.not_mem_nil] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      h <;> simp_all [Input.path]
  exact ⟨p, hp, i, hi, Input.covers_head hne hc⟩

/-- A pull request whose every changed path lies in `docs/` (the guides) or `website/` (the
standard and the site), or is `README.md` or `AGENTS.md`, runs no campaign. -/
theorem campaign_documentation (changed : List (List String))
    (h : ∀ p ∈ changed, p.head? = some "docs" ∨ p.head? = some "website" ∨
      p = ["README.md"] ∨ p = ["AGENTS.md"]) :
    campaignApplies .pullRequest changed = false := by
  cases hc : campaignApplies .pullRequest changed with
  | false => rfl
  | true =>
    obtain ⟨p, hp, i, hi, hh⟩ := campaign_head hc
    simp only [inputs, List.mem_cons, List.not_mem_nil] at hi
    rcases h p hp with h | h | rfl | rfl <;>
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        hi <;> simp_all [Input.path]

/-! ## The gate -/

/-- A job's result as the `needs` context reports it. -/
inductive Result where
  /-- Every step passed. -/
  | success
  /-- A step failed. -/
  | failure
  /-- The job was cancelled, or ran out of time. -/
  | cancelled
  /-- The job did not run. -/
  | skipped
  deriving DecidableEq, Repr

/-- The result `needs.<job>.result` names. -/
def Result.parse : String → Option Result
  | "success" => some .success
  | "failure" => some .failure
  | "cancelled" => some .cancelled
  | "skipped" => some .skipped
  | _ => none

/-- The name `needs.<job>.result` gives the result. -/
def Result.spelling : Result → String
  | .success => "success"
  | .failure => "failure"
  | .cancelled => "cancelled"
  | .skipped => "skipped"

/-- The gate reads back every name it prints. -/
theorem Result.parse_spelling (r : Result) : Result.parse r.spelling = some r := by
  cases r <;> rfl

/-- Whether a partition job decided to apply (`applies`) passes the gate with result `r`: it passed
and applies, or it was skipped and does not apply. -/
def admits : Bool → Result → Bool
  | true, .success => true
  | false, .skipped => true
  | _, _ => false

/-- `admits` exactly: a job that applies passes only by passing, and a job that does not apply only
by being skipped. -/
theorem admits_iff (applies : Bool) (r : Result) :
    admits applies r = true ↔
      (applies = true ∧ r = .success) ∨ (applies = false ∧ r = .skipped) := by
  cases applies <;> cases r <;> simp [admits]

/-- The gate's decision over the `needs` context: `decided` is the result of the job `applies`,
`decisions` its decisions by job id, and `jobs` every other job the gate needs, with its result. -/
def verdict (decided : Result) (decisions : List (String × Bool))
    (jobs : List (String × Result)) : Bool :=
  decided == .success &&
  decisions.all (fun d => jobs.any (·.1 == d.1)) &&
  jobs.all fun j => match decisions.lookup j.1 with
    | some applies => admits applies j.2
    | none => false

/-- The gate passes exactly when `applies` succeeded, every job it decided is one the gate needs,
and every job the gate needs passed when it was decided to apply and was skipped when it was
decided not to. -/
theorem verdict_iff (decided : Result) (decisions : List (String × Bool))
    (jobs : List (String × Result)) :
    verdict decided decisions jobs = true ↔
      decided = .success ∧ (∀ d ∈ decisions, ∃ r, (d.1, r) ∈ jobs) ∧
      ∀ j ∈ jobs, (decisions.lookup j.1 = some true ∧ j.2 = .success) ∨
        (decisions.lookup j.1 = some false ∧ j.2 = .skipped) := by
  simp only [verdict, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true, and_assoc]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · refine forall_congr' fun d => imp_congr_right fun _ => ?_
    constructor
    · rintro ⟨⟨k, r⟩, hj, hk⟩
      exact ⟨r, hk ▸ hj⟩
    · rintro ⟨r, hj⟩
      exact ⟨(d.1, r), hj, rfl⟩
  · refine forall_congr' fun j => imp_congr_right fun _ => ?_
    cases decisions.lookup j.1 with
    | none => simp
    | some applies => cases applies <;> simp [admits_iff]

/-! ## Steps -/

private def env (name : String) : IO String := do
  match ← IO.getEnv name with
  | some v => if v.isEmpty then fail s!"{name} is empty" else pure v
  | none => fail s!"{name} is not set"

/-- Run `git` with `args` in the checkout; its standard output as it is, or a failure with its
standard error. -/
private def git (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := "git", args }
  unless out.exitCode == 0 do fail s!"git {args}: {out.stderr}"
  return out.stdout

/-- The paths at which the checked-out commit, the merge commit GitHub creates and tests for a pull
request, differs from its first parent, the head of the base branch, each as its components: every
path added, deleted or modified there, a rename as both of its paths (`diff-tree` detects no
renames, and `--no-renames` says so). Refused unless the commit has exactly two parents. -/
private def changedPaths : IO (List (List String)) := do
  let line := (← git #["rev-list", "--parents", "-n", "1", "HEAD"]).trimAscii.toString
  match line.splitOn " " with
  | [_, base, _] =>
    let listed ← git #["diff-tree", "-r", "-z", "--no-renames", "--name-only", base, "HEAD"]
    return (listed.splitOn "\x00").filter (!·.isEmpty) |>.map (·.splitOn "/")
  | _ => fail s!"the checked-out commit is not a merge commit with two parents: {line}"

/-- Append `key=value` to the step outputs file `GITHUB_OUTPUT`. -/
private def output (key value : String) : IO Unit := do
  let path ← env "GITHUB_OUTPUT"
  let handle ← IO.FS.Handle.mk path .append
  handle.putStrLn s!"{key}={value}"

/-- The `applies` step: decide which partition jobs apply to this run (`decisions`) and write the
decision as the step output `decisions`, a JSON object from job id to whether it applies. -/
def writeDecisions : IO Unit := do
  let name ← env "GITHUB_EVENT_NAME"
  let some event := Event.parse name | fail s!"the workflow does not run on the event {name}"
  let changed ← if event == .pullRequest then changedPaths else pure []
  if event == .pullRequest then
    match changed.find? isInput with
    | some p => IO.println s!"{"/".intercalate p} is an input of the campaigns"
    | none => IO.println s!"none of the {changed.length} changed paths is an input of the campaigns"
  let decided := decisions event changed
  for (job, applies) in decided do
    IO.println s!"{job}: {if applies then "applies" else "does not apply"} to this {name} run"
  output "decisions" (Json.mkObj (decided.map fun (job, applies) => (job, toJson applies))).compress

/-- The result `needs.<job>.result` reports, from that job's entry of the `needs` context. -/
private def resultOf (job : String) (entry : Json) : IO Result := do
  let name ← IO.ofExcept (entry.getObjValAs? String "result")
  match Result.parse name with
  | some r => pure r
  | none => fail s!"the job {job} has the result {name}, which the gate does not know"

/-- The decisions the job `applies` wrote, from its entry of the `needs` context. -/
private def decisionsOf (entry : Json) : IO (List (String × Bool)) := do
  let outputs ← IO.ofExcept (entry.getObjVal? "outputs")
  let text ← IO.ofExcept (outputs.getObjValAs? String "decisions")
  let decided ← IO.ofExcept ((← IO.ofExcept (Json.parse text)).getObj?)
  decided.toList.mapM fun (job, applies) => return (job, ← IO.ofExcept applies.getBool?)

/-- The `gate` step: read the `needs` context from `NEEDS` and refuse unless `verdict` passes. -/
def checkGate : IO Unit := do
  let needs ← IO.ofExcept ((← IO.ofExcept (Json.parse (← env "NEEDS"))).getObj?)
  let entries := needs.toList
  let some decision := entries.lookup "applies" | fail "the gate does not need the job applies"
  let decided ← resultOf "applies" decision
  let decisions ← if decided == .success then decisionsOf decision else pure []
  let jobs ← (entries.filter (·.1 != "applies")).mapM fun (job, entry) =>
    return (job, ← resultOf job entry)
  IO.println s!"applies: {decided.spelling}"
  for (job, r) in jobs do
    let decision := match decisions.lookup job with
      | some true => "applies"
      | some false => "does not apply"
      | none => "was not decided"
    IO.println s!"{job}: {decision}, {r.spelling}"
  for (job, _) in decisions do
    unless jobs.any (·.1 == job) do
      IO.println s!"{job}: decided, but the gate does not need it"
  unless verdict decided decisions jobs do
    fail "a diagnostics job that applies did not pass, or the decision of which apply did not \
      succeed or does not match the jobs the gate needs"
  IO.println "every diagnostics job that applies passed, and every other one was skipped"

end Regula.DiagnosticsGate

/-- Command line of `lean --run lean/Regula/DiagnosticsGate.lean`: `applies` or `gate`; returns 2
on a usage error. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["applies"] => Regula.DiagnosticsGate.writeDecisions; return 0
  | ["gate"] => Regula.DiagnosticsGate.checkGate; return 0
  | _ =>
    IO.eprintln "usage: lean --run lean/Regula/DiagnosticsGate.lean (applies | gate)"
    return 2
