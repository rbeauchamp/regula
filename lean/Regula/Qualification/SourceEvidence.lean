import Regula.Qualification.Project
import RegulaQualification.Evidence

/-! # Source and evidence campaigns

Operational source/evidence campaigns. Every mutation stays in a unique disposable
adopter. These exercise actual checker commands; the supplied-observation oracle is
proof-backed, while process, filesystem and compiler effects remain trusted. -/
namespace Regula.Qualification.SourceEvidence
open Lean System RegulaQualification
open RegulaQualification.Evidence

/-- Valid kernel proposition shared by otherwise-independent controls. -/
def good : String :=
    "import Lean\n/-! Unchanged proposition and proof. -/\ntheorem valid : True := True.intro\n"
/-- Invalid direct API admission, confined to generated negative fixtures. -/
def unchecked : String := "open Lean Elab Command\nrun_cmd do\n  let d := Declaration.thmDecl \
  {\n    name := `admissionFalse\n    levelParams := [], type := mkConst ``False, value := mkConst \
  ``True.intro }\n  match (← getEnv).addDeclCore 200000 1000 d none false with\n  | .ok env => \
  setEnv env\n  | .error _ => throwError \"construction failed\"\n"
/-- Identical theorem with either genuine or independently corrupted source coordinates. -/
def rangeSource (bad : Bool) : String :=
  "import Lean\n/-! The same proved proposition with supplied range metadata. -/\ntheorem \
    rangeClaim : True := True.intro\nopen Lean Elab Command in\nrun_cmd do\n  let some ranges ← \
    findDeclarationRangesCore? ``rangeClaim\n    | throwError \"missing control range\"\n  let \
    supplied := " ++
    (if bad then "{ ranges.range with pos := ⟨0, 0⟩, endPos := ⟨0, 1⟩ }" else "ranges.range") ++
    "\n  addDeclarationRanges ``rangeClaim { range := supplied, selectionRange := supplied }\n"

/-- Write a positive Markdown fence verbatim, with no instrumentation wrapper. -/
def writeFence (project : FilePath) (source : String) : IO Unit :=
  IO.FS.writeFile (project / "docs/control.md") ("```lean\n" ++ source ++ "```\n")

/-- Observe the selected public command in `env`, requiring a fresh output for JSON commands. -/
def observe (root project : FilePath) (label binary : String) (flags : Array String)
    (expected : Expected) (env : Array (String × Option String) := cleanEnv) :
    IO (IO.Process.Output × Option Json) := do
  let output := project / s!"{label}.json"
  requireChecks [⟨"fresh evidence output", !(← output.pathExists)⟩]
  let jsonCommand := binary == "axiomGate"
  let result ← run project (root / ".lake/build/bin" / binary).toString
    (#["--project", project.toString] ++ flags ++
      if jsonCommand then #["--json-out", output.toString] else #[]) env
  let report ← if jsonCommand then pure (some (← readResult output)) else pure none
  IO.ofExcept
      (checked_validation.run expected result.exitCode.toNat
          (result.stdout ++ result.stderr) report)
  return (result, report)

/-- Public closure/range controls: reflexive candidate is retained, active replacement
cycle refuses, ordinary recursive IR self-edge stays present and resolved. -/
def closure : IO Unit := do
  let root ← rootDirectory
  withScratch root "closure-evidence" fun project => do
    prepareCoreProject root project "evidence_adopter" "standard-logical"
    writeFence project "import Example\ntheorem fenceClaim : True := True.intro\n"
    for kind in #["cycle", "range"] do
      for (invocation, flags, mode) in #[
          ("project", #[], "freshProject"),
          ("incremental", #["--incremental"], "incrementalProject"),
          ("file", #["--file", "Example.lean", "--claim", "standard-logical"], "freshFile"),
          ("combined", #["--with-docs"], "freshProject")] do
        if kind == "cycle" && #["file", "combined"].contains invocation then continue
        for phase in #["positive", "negative", "restored"] do
          let bad := phase == "negative"
          let source := if kind == "range" then rangeSource bad else
            "import Lean\n/-! Reflexive simplification and ordinary recursion have separate \
              meanings. -/\n/-- The identity. -/\ndef f (n : Nat) : Nat := n\n/-- The sum of a \
              list. -/\ndef recursiveSum : List Nat → Nat\n  | [] \
              => 0\n  | x :: xs => x + recursiveSum xs\n" ++
            (if bad then "@[csimp] " else "") ++ "theorem same : f = f := rfl\n"
          IO.FS.writeFile (project / "Example.lean") source
          clearBuild project
          let reason := if !bad then "" else if kind == "cycle" then "replacement-only cycle"
            else "producer-source: source coverage or coordinates mismatch"
          let (_, some report) ← observe root project s!"{kind}-{invocation}-{phase}"
              "axiomGate" flags {
              failure := bad, mode := some mode, status := if bad then "incomplete" else
                                                                        "completed",
              ids := if bad then [if kind == "cycle" then "RG3001" else "RG2005"] else [],
              reason, impact := some "incomplete" }
            | throw <| IO.userError "missing closure result"
          if bad then
            let ds ← IO.ofExcept (array report "diagnostics")
            for d in ds do
              requireChecks
                  [⟨"typed closure refusal reason", (← IO.ofExcept (detail d)).contains reason⟩]
          if kind == "cycle" then
            let roots ← IO.ofExcept do
              let surfaces ← array (← field report "scope") "surfaces"
              let some surface := surfaces[0]? | throw "missing surface"
              array (← field surface "report") "execution"
            for (name, recursion) in #[("f", false), ("recursiveSum", true)] do
              let some entry := roots.find?
                  (fun entry => (entry.getObjVal? "name").toOption == some (nameJson name))
                | throw <| IO.userError s!"missing {name} execution"
              let closure ← IO.ofExcept (field entry "closure")
              let edge := toJson #[nameJson name, nameJson name]
              let edges ← IO.ofExcept
                  (if recursion then array entry "compilerEdges" else
                                      array closure "candidateEdges")
              let unresolved ← IO.ofExcept (array entry "unresolved")
              requireChecks [⟨"retained self edge", edges.contains edge⟩,
                ⟨"exact unresolved state", (!unresolved.isEmpty) == (bad && !recursion)⟩]
              if !recursion then
                requireChecks [⟨"active self simplification iff mutated",
                  (← IO.ofExcept (array closure "activeSimplificationEdges")).contains edge == bad⟩]
          IO.println s!"closure evidence {kind}/{invocation}/{phase}: PASS"

/-- Initial configuration-read IO failure must produce one exact typed incomplete
result, not an exception without evidence or a stale successful request account: its
request records no configuration and it has no effective configuration. -/
def configuration : IO Unit := do
  let root ← rootDirectory
  withScratch root "configuration-capture" fun project => do
    prepareCoreProject root project "configuration_adopter" "kernel-only"
    let source := "/-! Fixed proposition. -/\ntheorem valid : True := True.intro\n"
    IO.FS.writeFile (project / "Example.lean") source
    let manifest := project / "foundation_manifest.json"
    let saved ← IO.FS.readFile manifest
    -- What this runtime reports for reading a directory in a file's place.
    let directory ← readFailure (project / "docs")
    for (mode, flags) in #[("freshProject", #[]),
        ("freshFile", #["--file", (project / "Example.lean").toString, "--claim", "kernel-only"])]
            do
      for phase in #["positive", "directory", "restored"] do
        if phase == "directory" then IO.FS.removeFile manifest; IO.FS.createDir manifest
        if phase == "restored" then IO.FS.removeDir manifest; IO.FS.writeFile manifest saved
        clearBuild project
        let bad := phase == "directory"
        let (process, some result) ← observe root project s!"{mode}-{phase}" "axiomGate"
            (#["--manifest", manifest.toString] ++ flags) {
              failure := bad, mode := some mode, status := if bad then "incomplete" else
                                                                        "completed",
              ids := if bad then ["RG2001"] else [], impact := some "incomplete" }
          | throw <| IO.userError "missing configuration result"
        let checks ← IO.ofExcept do
          if bad then
            let ds ← array result "diagnostics"
            let some d := ds[0]? | throw "missing diagnostic"
            let why ← detail d
            return [
              Check.mk "configuration IO detail"
                  (why.contains directory && process.stderr.contains why),
              ⟨"exact configuration location", (← field d "location") == Json.mkObj [
                ("kind", .str "project"), ("identity", .str project.toString)]⟩,
              ⟨"exact unresolved IO failure", (← array result "unresolved") == #[.str why]⟩,
              ⟨"no source invented", (← array result "sourceAccount").isEmpty⟩,
              ⟨"request without configuration read",
                ((← field result "request").getObjVal? "configuration").toOption == some
                (.arr #[]) &&
                  (field result "effective").toOption == some .null⟩]
          else
            let effective ← text (← field result "effective") "root"
            let sources ← array result "sourceAccount"
            return [⟨"actual source account", sources.any fun item =>
              (text item "path").toOption == some (effective ++ "/Example.lean") &&
              (text item "sourceText").toOption == some source⟩]
        requireChecks checks
        IO.println s!"configuration capture {mode}/{phase}: PASS"

/-- Independent range, replay, policy and compiler defects originating in positive
fences, through both documentation public entrypoints, each followed by restoration. -/
def fences : IO Unit := do
  let root ← rootDirectory
  withScratch root "fence-evidence" fun project => do
    prepareCoreProject root project "fence_adopter" "standard-logical"
    IO.FS.writeFile (project / "Example.lean") good
    let positive := rangeSource false
    let mut phases := #[("positive", positive, ([] : List String), "")]
    -- The result lists findings in run order (`Regula.sortFindings`): two findings of the same
    -- fence are ordered by rule ID, and a fence's finding precedes a source-located one.
    for (label, source, ids, reason) in #[
        ("range", rangeSource true, ["RG2005", "RG4002"],
            "producer-source: source coverage or coordinates mismatch"),
        ("replay", "import Lean\n" ++ unchecked, ["RG2005", "RG4002"], "kernel-admission"),
        ("policy", "axiom forbidden : True\n", ["RG4002", "RG1001"], "project-axiom"),
        ("compiler", "def bad : Nat := \"wrong\"\n", ["RG4002"], "")] do
      phases := phases.push (label, source, ids, reason) |>.push
          (label ++ "-restored", positive, [], "")
    for (binary, flags) in
        #[("docFenceAudit", #["--jobs", "1", "--verbose"]), ("axiomGate", #["--with-docs"])] do
      for (phase, source, ids, reason) in phases do
        writeFence project source
        clearBuild project
        let incomplete := ids.contains "RG2005"
        let (process, _) ← observe root project s!"{binary}-{phase}" binary flags {
          failure := !ids.isEmpty, mode := some "freshProject",
          status := if incomplete then "incomplete" else if ids.isEmpty then "completed" else
                                                                              "rejected",
          ids, reason, grouped := phase != "compiler", positiveText :=
              s!"{RegulaPolicy.Compiler.positiveSummary RegulaPolicy.Compiler.candidate}=1/1",
          impact := some (if incomplete then "incomplete" else "violation"),
          diagnosticMode := some "documentationExample", evidenceSubject := some "control.md:1" }
        if phase == "replay" then
          requireChecks
              [⟨"replay failed at intended declaration", (process.stdout ++ process.stderr).contains
                  "admissionFalse"⟩]
        IO.println s!"fence evidence {binary}/{phase}: PASS"
end Regula.Qualification.SourceEvidence
