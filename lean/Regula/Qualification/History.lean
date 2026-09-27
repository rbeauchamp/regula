import Regula.Qualification.SourceEvidence
import RegulaQualification.History

/-! # Project history qualification

Actual project/file history qualification. Every control runs in its own fresh
workspace with its own output path, so no restored rerun repeats an earlier positive
control (standard §8.8).

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

/-- Ten real public invocations retain exact requests, source binding, outcomes and
both replacement targets. -/
def check : IO Unit := do
  let root ← rootDirectory
  withScratch root "history-controls" fun scratch => do
    for (invocation, flags, mode) in #[
        ("project", #[], "freshProject"), ("incremental", #["--incremental"], "incrementalProject"),
        ("file",
            #["--file", "Example.lean", "--claim", "standard-logical", "--execution", "checked"],
                "freshFile")] do
      let phases := #["positive", "unsupported"] ++
        (if invocation == "incremental" then #[] else #["admission", "source-change"])
      for index in [:phases.size] do
        let phase := phases[index]!
        let mutation := if phase == "unsupported" then "run_cmd pure ()"
          else if phase == "admission" then SourceEvidence.unchecked
          else if phase == "source-change" then "run_cmd do\n  let path ← Lean.getFileName\n  let \
            content ← IO.FS.readFile path\n  IO.FS.writeFile path (content ++ \"\\n\")\n"
          else "-- evaluator control"
        let source := source.replace "-- evaluator control" mutation
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
          requireChecks [⟨"exact history evidence exit", result.exitCode == 1⟩]
          if phase == "admission" then
            let ds ← IO.ofExcept (report.getObjValAs? (Array Json) "diagnostics")
            for d in ds do
              requireChecks
                  [⟨"intended unchecked theorem",
                      (← IO.ofExcept (RegulaQualification.Evidence.detail d)).contains
                          "admissionFalse"⟩]
          IO.println s!"source {invocation}/{phase}: exact RG2005 incomplete PASS"
          continue
        IO.ofExcept (RegulaQualification.History.checked_validation.run report result.exitCode.toNat
          mode source (invocation == "file") (phase == "unsupported"))
        if invocation == "file" && phase == "positive" then
          let scope ← IO.ofExcept (report.getObjVal? "scope")
          let account ← IO.ofExcept (scope.getObjVal? "report")
          let execution ← IO.ofExcept (account.getObjValAs? (Array Json) "execution")
          let importedName := toJson #[#["str", "add"], #["str", "Nat"]]
          let imported := execution.filter
              (fun entry => (entry.getObjVal? "name").toOption == some importedName)
          requireChecks
              [⟨"one imported control with existing ownership", imported.size == 1 && imported.all
            (fun entry => (entry.getObjVal? "module").toOption.isSome)⟩]
        requireChecks
            [⟨"history source unchanged", (← IO.FS.readFile (project / "Example.lean")) == source⟩]
        IO.println s!"history {invocation}/{phase}: exact requests/source/outcome PASS"

end Regula.Qualification.History
