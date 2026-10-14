import Regula.Qualification.SourceEvidence
import RegulaQualification.History

/-! # Project history qualification

Actual project/file history qualification. Every control runs in its own fresh
workspace with its own output path, so no restored rerun repeats an earlier positive
control (standard §7.8).

Each control is kept for a genuinely external boundary: it observes what the real
`axiomGate` process, Lean elaborator and collector emit for one source. What the pure
checkers conclude from such an output is proved instead, for every input:
`ProducerReport.validate_sound` for transport admission and
`RegulaQualification.History.validate_importedRootExecuted` /
`validate_unsupported_unresolved` for this oracle. -/
namespace Regula.Qualification.History
open Lean

private def source := "import Lean\nimport Regula.Contract\n/-! Two callers preserve an earlier \
  implementation overwritten after compilation. -/\n/-- The identity, as `n + 0`. -/\ndef earlier \
  (n : Nat) : Nat := n + 0\n/-- The identity. -/\ndef target (n : Nat) : Nat := n\n/-- The \
  identity, first implemented by `earlier`. -/\n@[implemented_by earlier] def reference (n : Nat) \
  : Nat := n\n/-- `reference`, compiled while `earlier` implements it. -/\ndef first (n : Nat) : \
  Nat := reference n\nattribute [implemented_by target] reference\n/-- `reference`, compiled while \
  `target` implements it. -/\ndef second (n : Nat) : Nat := reference n\n/-- The sum of a list. \
  -/\ndef recursiveSum : List Nat → Nat\n  | [] => 0\n  | x :: xs => x + recursiveSum xs\nprivate \
  def unused (xs : List Nat) : Nat := recursiveSum xs\nprivate def unregistered (xs : List Nat) : \
  Nat := recursiveSum xs\ntheorem privateContract : Regula.ExecutableContract unused\n    (fun f \
  => ∀ xs, f xs = recursiveSum xs) := ⟨by intro xs; rfl⟩\ntheorem importedContract : \
  Regula.ExecutableContract Nat.add\n    (fun f => ∀ n m, f n m = n + m) := ⟨by intros; rfl⟩\n-- \
  evaluator control\n"

/-- The history source mutated for `phase`. -/
private def mutated (phase : String) : String :=
  let mutation := if phase == "unsupported" then "run_cmd pure ()"
    else if phase == "admission" then SourceEvidence.unchecked
    else if phase == "source-change" then "run_cmd do\n  let path ← Lean.getFileName\n  let \
      content ← IO.FS.readFile path\n  IO.FS.writeFile path (content ++ \"\\n\")\n"
    else "-- evaluator control"
  source.replace "-- evaluator control" mutation

/-- One control: the public invocation `invocation` with `flags` on the history source mutated
for `phase`, in a fresh workspace of its own below `scratch`, and the checks of its oracle. -/
private def control (root scratch : System.FilePath)
    (invocation : String) (flags : Array String) (mode : String) (index : Nat) (phase : String) :
    IO Unit := do
  let source := mutated phase
  let project := scratch / s!"{invocation}-{phase}"
  IO.FS.createDir project
  prepareProject root project "history_adopter" "standard-logical"
    "All three implementations compute the identity."
  IO.FS.writeFile (project / "Example.lean") source
  let output := project / s!"{invocation}-{index}-{phase}.json"
  let (result, report) ← observeProject root project output flags
  if phase == "admission" || phase == "source-change" then
    let reason := if phase == "admission" then "kernel-admission" else
                                                "producer-source: source snapshot changed"
    IO.ofExcept (RegulaQualification.Evidence.checked_validation.run {
      failure := true, mode := some mode, status := "incomplete", ids := ["RG2005"], reason,
      impact := some "incomplete", diagnosticMode := some mode }
      result.exitCode.toNat (result.stdout ++ result.stderr) (some report))
    requireChecks [⟨"exact history evidence exit", result.exitCode == 3⟩]
    if phase == "admission" then
      let ds ← readMember output (RegulaQualification.Member.array report "diagnostics")
      for d in ds do
        requireChecks
            [⟨"intended unchecked theorem",
                (← IO.ofExcept (RegulaQualification.Evidence.detail d)).contains
                    "admissionFalse"⟩]
    IO.println s!"source {invocation}/{phase}: exact RG2005 incomplete PASS"
    return
  IO.ofExcept (RegulaQualification.History.checked_validation.run report result.exitCode.toNat
    mode source (invocation == "file") (phase == "unsupported"))
  -- `report` is the document the reader rebuilt (`readResult`). The file itself holds the
  -- account in the shared form, every root as an entry its account is derived from: that
  -- the collector's accounts have the form the reader derives is not proved, so it is
  -- observed here on the real collector's output.
  let file ← readJson output
  let written ← IO.ofExcept do
    (← RegulaQualification.History.account file (invocation == "file")).getObjVal? "execution"
  requireChecks [⟨"execution account stored once, every root derived",
    Regula.SharedExecution.derivedOnly written⟩]
  if invocation == "file" && phase == "positive" then
    let scope ← readMember output (RegulaQualification.Member.field report "scope")
    let account ← readMember output (RegulaQualification.Member.field scope "report")
    let execution ← readMember output (RegulaQualification.Member.array account "execution")
    let importedName := nameJson "Nat.add"
    let imported := execution.filter
        (fun entry => (entry.getObjVal? "name").toOption.any
          (Regula.JsonAgreement.conforms · importedName))
    requireChecks
        [⟨"one imported control with existing ownership", imported.size == 1 && imported.all
      (fun entry => (entry.getObjVal? "module").toOption.isSome)⟩]
  requireChecks
      [⟨"history source unchanged", (← IO.FS.readFile (project / "Example.lean")) == source⟩]
  IO.println s!"history {invocation}/{phase}: exact requests/source/outcome PASS"

/-- Ten real public invocations retain exact requests, source binding, outcomes and
both replacement targets. No control reads another's workspace, so they run on `jobs` workers
(`mapWorkQueue`). Before they start, the guard refuses when a module of the root package that
their sources import needs a build (`requireRootImportsBuilt`); the producers campaign runs the
guard's control. `mapWorkQueue` joins every worker before it reports a failure, and the error it
reports is the first failing worker's. A worker that fails runs no further control, so once
`jobs` controls have failed, the controls still queued do not run. -/
def check (jobs : Nat := 4) : IO Unit := do
  let root ← rootDirectory
  withScratch root "history-controls" fun scratch => do
    let controls := #[
        ("project", #[], "freshProject"), ("incremental", #["--incremental"], "incrementalProject"),
        ("file",
            #["--file", "Example.lean", "--claim", "standard-logical", "--execution", "checked"],
                "freshFile")].flatMap fun (invocation, flags, mode) =>
      let phases := #["positive", "unsupported"] ++
        (if invocation == "incremental" then #[] else #["admission", "source-change"])
      phases.mapIdx fun index phase => (invocation, flags, mode, index, phase)
    requireRootImportsBuilt root (controls.map (mutated ·.2.2.2.2))
    let _ ← Regula.Checker.mapWorkQueue jobs controls fun (invocation, flags, mode, index, phase) =>
      control root scratch invocation flags mode index phase

end Regula.Qualification.History
