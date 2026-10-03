import Regula.Qualification.Launcher
import Regula.Checker.Common
import RegulaQualification.Native
import RegulaCore.Edition

/-! # Native linter linkage qualification

Operational controls for native collector/logger/metadata linkage. Intentionally
invalid source is only written to disposable paths. The pure diagnostic oracle lives
in `RegulaQualification.Native`; actual compiler behavior is observed, not proved. -/

namespace Regula.Qualification.NativeLinter
open Lean System

/-- The registered claim's docstring, with the nonempty Intent section RG5003 requires. -/
private def claimDoc :=
    "/-- A registered material claim.\n\n# Intent\nQualify the native Intent-section observer. -/\n"

private def base := "import Regula.Linter\n/-! Collector qualification control. -/\n" ++ claimDoc ++
    "@[regula_material] theorem documented : True := .intro\nprivate def privateValue : Nat := \
      1\ninductive Branch where\n  | node : List Branch → Branch\n"

/-- One native control's invocation options and expected diagnostic contract. -/
structure Control where
  /-- The control's name, also the file stem of its scratch source `label.lean`. -/
  label : String
  /-- The Lean source compiled for this control. -/
  source : String
  /-- Rule IDs of the native diagnostics expected, with multiplicity and in any order; each
  `id` is matched as the message kind `Regula.<id>._namedError`. -/
  ids : List String := []
  /-- Whether the compiler process is expected to exit with a nonzero code. -/
  errors : Bool := false
  /-- Extra `lean` arguments, placed before the output flag and the source path. -/
  options : Array String := #[]
  /-- Whether `lean` also writes an `.olean` beside the source (`-o`). -/
  output : Bool := false
  /-- The non-native compiler messages expected, in order, each by severity and a substring
  of its text. -/
  compiler : List RegulaQualification.Native.CompilerMessage := []
  /-- A substring that at least one native diagnostic's text must contain, when given. -/
  detail : Option String := none
  /-- The severity every native diagnostic must have; by default `error` when `options`
  contains `-DwarningAsError=true` and `warning` otherwise. -/
  nativeSeverity : Option String := none

/-- Decode required message fields without silently defaulting malformed values. Lean's
JSON protocol serializes every message's `kind`, `[anonymous]` when it has no tag. -/
def decode (value : Json) : Except String RegulaQualification.Native.Message := do
  return {
    kind := (← value.getObjValAs? String "kind"),
    severity := (← value.getObjValAs? String "severity"),
    data := (← value.getObjValAs? String "data"), fileName :=
        (← value.getObjValAs? String "fileName") }

private def check (root scratch : FilePath) (launcher : Launcher.State) (control : Control)
    (env : Array (String × Option String) := #[]) : IO (List Json) := do
  let path := scratch / s!"{control.label}.lean"
  IO.FS.writeFile path control.source
  let args := #["--json", "--root", scratch.toString] ++ control.options ++
    (if control.output then #["-o", (path.withExtension "olean").toString] else #[]) ++
        #[path.toString]
  let result ← Launcher.runLean root launcher args env
  let messages ← (result.stdout.splitOn "\n").filterMapM fun line => do
    if line.trimAscii.isEmpty then return none
    return some (← IO.ofExcept (Json.parse line))
  let decoded ← IO.ofExcept (messages.mapM decode)
  let expected : RegulaQualification.Native.Expected := {
    kinds := control.ids.map (fun id => s!"Regula.{id}._namedError"),
    fileName := path.toString, errors := control.errors, compiler := control.compiler,
    helpPrefix := Regula.installed.edition.url "rules/",
    detail := control.detail, severity := control.nativeSeverity.getD
      (if control.options.contains "-DwarningAsError=true" then "error" else "warning") }
  match RegulaQualification.Native.checked_validation.run expected result.exitCode.toNat
      result.stderr decoded with
  | .ok () => pure ()
  | .error detail =>
      throw <| IO.userError s!"{control.label}: {detail}\n{result.stdout}{result.stderr}"
  return messages

private def position (messages : List Json) (id : String) : IO Json := do
  let some message := messages.find? (fun message =>
    (message.getObjValAs? String "kind").toOption == some s!"Regula.{id}._namedError")
    | throw <| IO.userError s!"missing {id} diagnostic"
  IO.ofExcept (message.getObjVal? "pos")

/-- Preserve all native source controls, including imported-artifact and restored
controls. Search-path augmentation is child-local rather than a global mutation. Every
control is its own compiler process with its own source path, so controls run `jobs` at a
time in three waves that keep each order the checks depend on: `Control` first; then every
control that reads no other control's output; then the controls that import wave-one
artifacts and the `Restored` controls, which follow every malformed control. -/
def checkAt (root scratch : FilePath) (launcher : Launcher.State) (jobs : Nat := 4) : IO Unit := do
    let check := check root scratch launcher
    let _ ← check { label := "Control", source := base, output := true }
    let retired : Array (String × String) := match RegulaPolicy.Compiler.legacyCompilerTrust with
      | .present => #[]
      | .absent => #[
          ("RetiredTrustCompiler", "Lean.trustCompiler"),
          ("RetiredOfReduceBool", "Lean.ofReduceBool"),
          ("RetiredOfReduceNat", "Lean.ofReduceNat")]
    let _ ← Regula.Checker.mapWorkQueue jobs retired fun (label, name) =>
      check { label, source := "import Regula.Linter\n/-! Retired compiler-name dependency. -/\n" ++
        s!"axiom {name} : True\n", ids := ["RG1001"], output := true }
    let axiomSource := base ++ "\naxiom forbidden : False\n"
    let missing := base.replace "/-! Collector qualification control. -/\n" ""
        |>.replace claimDoc ""
    let compilerTrust : Control := match RegulaPolicy.Compiler.legacyCompilerTrust with
      | .present =>
        { label := "CompilerTrust", source := base ++
            "theorem trustedCompiler : True := Lean.trustCompiler\n", ids := ["RG1004"],
          compiler := [⟨"warning", "`Lean.trustCompiler` has been deprecated: in-kernel native \
            reduction is deprecated; assert native evaluations with axioms instead"⟩] }
      | .absent =>
        { label := "RetiredCompilerName", source := base ++
            "axiom Lean.trustCompiler : True\n", ids := ["RG1001"] }
    let controls : List Control := [
      { label := "PromotedMissing", source := missing, ids := ["RG5001", "RG5002"], errors := true,
        options := #["-DwarningAsError=true"] },
      { label := "MissingIntent", source :=
          base.replace claimDoc "/-- A registered material claim. -/\n",
        ids := ["RG5003"] },
      { label := "Disabled", source := base.replace "/-!" "set_option linter.regula false\n/-!" ++
        "axiom forbidden : False\n" },
      { label := "Narrow", source := base ++
          "set_option regula.localFoundation \"kernel-only\"\n" ++
        "theorem classicalClaim (p : Prop) : p ∨ ¬p := Classical.em p\n", ids := ["RG1005"] },
      { label := "EmptyBadRequest", source :=
          "import Regula.Linter\n/-! Configuration control. -/\n" ++
        "set_option regula.localFoundation \"unsupported\"\n", ids := ["RG2002"] },
      { label := "TrailingBadRequest", source := base ++
          "set_option regula.localFoundation \"unsupported\"\n", ids := ["RG2002"] },
      { label := "InitialBadRequest", source := "import Regula.Linter\n", ids := ["RG2002"],
        options := #["-Dregula.localFoundation=unsupported"] },
      { label := "ScopedBadRequest", source := base ++
          "set_option regula.localFoundation \"unsupported\" in\n" ++
        "def selected : Nat := 1\n", ids := ["RG2002"] },
      { label := "ScopedNarrow", source := base ++
          "set_option regula.localFoundation \"kernel-only\" in\n" ++
        "theorem classicalClaim (p : Prop) : p ∨ ¬p := Classical.em p\n", ids := ["RG1005"] },
      { label := "ScopedDisabled", source := base ++
          "set_option linter.regula false in\naxiom forbidden : False\n" },
      -- The audit-build marker (`Lake.auditLeanOptions`) silences the `Axiom` control's
      -- finding even where the source turns `linter.regula` back on.
      { label := "AuditBuild", source := base ++
          "set_option linter.regula true\naxiom forbidden : False\n" ++
        "set_option linter.regula true in\naxiom scopedForbidden : False\n", options :=
            #["-Dweak.regula.auditBuild=true"] },
      { label := "ScopedPromoted", source := base ++
          "set_option warningAsError true in\naxiom forbidden : False\n",
        ids := ["RG1001"], errors := true, nativeSeverity := some "error" },
      { label := "Hole", source := base ++ "theorem unfinished : True := by sorry\n", ids :=
          ["RG1002"],
        compiler := [⟨"warning", "declaration uses `sorry`"⟩] },
      { label := "RecoveredError", source := base ++
          "theorem broken : True := by exact missingProof\n",
        ids := ["RG1002"], errors := true, compiler :=
            [⟨"error", "Unknown identifier `missingProof`"⟩] },
      { label := "Synchronous", source := axiomSource, ids := ["RG1001"], options :=
          #["-DElab.async=false"] },
      { label := "UnknownAxiom", source := base ++
          "private axiom assumed : False\ntheorem dependent : False := assumed\n",
        ids := ["RG1001", "RG1003"] },
      compilerTrust,
      { label := "Escape", source := base ++ "unsafe def escape : Nat := 0\n", ids := ["RG1006"] },
      { label := "Contract", source := base ++ "def implementation (n : Nat) : Nat := n\n" ++
        "theorem unsupported (n : Nat) : Regula.ExecutableContract (implementation n) (fun value \
          => value = n) := ⟨rfl⟩\n",
        ids := ["RG1007"] },
      { label := "Pending", source := base ++
          "theorem nativeTruth : (2 + 2 : Nat) = 4 := by native_decide\n",
        ids := ["RG2005"], detail := some "fresh generated-role evidence remains required" },
      -- `decide +native` and `bv_decide` name their `nativeEqTrue` axioms after their own
      -- tactic; the editor defers them like `native_decide` rather than reporting RG1001.
      { label := "PendingDecideNative", source := base ++
          "theorem decideNativeTruth : (2 + 2 : Nat) = 4 := by decide +native\n",
        ids := ["RG2005"], detail := some "fresh generated-role evidence remains required" },
      { label := "PendingBvDecide", source := base.replace "import Regula.Linter"
          "import Regula.Linter\nimport Std.Tactic.BVDecide" ++
          "theorem bvTruth (x y : BitVec 8) : x * y = y * x := by bv_decide\n",
        ids := ["RG2005"], detail := some "fresh generated-role evidence remains required" }]
    let malformed := base ++ "open Lean Elab Command in\nelab \"bad_range \" name:ident : command \
      => do\n  elabCommand (← `(axiom $name:ident : False))\n  let some ranges ← \
      findDeclarationRangesCore? name.getId | throwError \"missing control range\"\n  let invalid \
      := { ranges.range with pos := ⟨9999, 0⟩, endPos := ⟨9999, 1⟩ }\n  addDeclarationRanges \
      name.getId { range := invalid, selectionRange := invalid }\nbad_range corrupted\n"
    let restored := malformed.replace "{ ranges.range with pos := ⟨9999, 0⟩, endPos := ⟨9999, 1⟩ }"
        "ranges.range"
    -- A Verso module docstring takes the community's `set_option … in` form, which RG5001 reads
    -- as the first command after the imports; later docstrings use a module-wide option.
    let verso := base.replace "/-! Collector qualification control. -/\n"
      ("set_option doc.verso true in\nset_option doc.verso.module true in\n" ++
        "/-! Collector qualification control. -/\nset_option doc.verso true\n")
    let moduleStyle := base.replace "import Regula.Linter" "module\nimport Regula.Linter" |>.replace
      "@[regula_material] theorem" "@[regula_material] public theorem"
    let inspect := base ++ "run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.axiomDecl {\n  \
      name := `hiddenAxiom, levelParams := [], type := Lean.mkSort .zero, isUnsafe := false \
      })\nrun_cmd do\n  let env ← Lean.getEnv\n  let ds ← Regula.Collect.currentModule\n  unless \
      ds.any (fun d => d.name == `hiddenAxiom && d.kind == .«axiom») do\n    throwError \
      \"binder-less declaration missing\"\n  unless ds.any (fun d => d.private) do throwError \
      \"private declaration missing\"\n  unless ds.any (fun d => d.name == `Branch.rec) do \
      throwError \"generated declaration missing\"\n  unless ds.all (fun d => d.module == \
      env.mainModule) do throwError \"wrong local ownership\"\n  let a ← \
      Regula.Collect.declaration `documented .snapshot\n  let b ← Regula.Collect.declaration \
      `documented .replayCandidate\n  unless a == b do throwError \"stage changed ordinary \
      canonical record\"\n  unless (Regula.Collect.moduleOf env \
      `unknownDeclaration).toOption.isNone do\n    throwError \"invented unknown ownership\"\n  if \
      env.header.modules.any (fun m => m.module.getRoot == `Mathlib) then\n    throwError \"public \
      import required Mathlib\"\n"
    let independent : Array Control := #[
      { label := "Axiom", source := axiomSource, ids := ["RG1001"] },
      { label := "PromotedAxiom", source := axiomSource, ids := ["RG1001"],
        errors := true, options := #["-DwarningAsError=true"] },
      { label := "Missing", source := missing, ids := ["RG5001", "RG5002"], output := true },
      { label := "BadRequest", source := base ++
        "set_option regula.localFoundation \"unsupported\"\ndef selected : Nat := 1\n", ids :=
            ["RG2002", "RG2002"] }] ++
      controls.toArray ++ #[
      { label := "ValidRange", source := restored, ids := ["RG1001"] },
      { label := "InvalidRange", source := malformed, ids := ["RG2005"],
        detail := some "reported source coordinates disagree with the snapshot" },
      { label := "Verso", source := verso, output := true },
      { label := "Inherited", source := base ++ "/-- Reused documentation.\n\n# Intent\nInherited \
        by the registered child. -/\ndef parent : Nat := 1\n@[inherit_doc parent, regula_material] \
        def child : Nat := 1\n@[regula_material] private def privateMaterial : Nat := 1\n" },
      { label := "ModuleSystem", source := moduleStyle ++
          "@[regula_material] theorem privateMaterial : True := .intro\n" },
      { label := "ModuleAxiom", source := moduleStyle ++ "public axiom forbidden : False\n", ids :=
          ["RG1001"] },
      { label := "ModuleMissing", source :=
          (moduleStyle.replace "/-! Collector qualification control. -/\n" "").replace
          claimDoc "", ids := ["RG5001", "RG5002"] },
      { label := "Collect", source := inspect },
      -- RG5001 beyond presence: a command before the module docstring, and a repeated import.
      { label := "MisplacedDoc", source :=
          base.replace "/-! Collector" "set_option pp.all false\n/-! Collector",
        ids := ["RG5001"] },
      { label := "RepeatedImport", source := "import Regula.Linter\n" ++ base, ids := ["RG5001"] }]
    let messages ← Regula.Checker.mapWorkQueue jobs independent check
    let some axiomMessages := messages[0]? | throw <| IO.userError "missing Axiom control"
    let some missingMessages := messages[2]? | throw <| IO.userError "missing Missing control"
    let some config := messages[3]? | throw <| IO.userError "missing BadRequest control"
    requireChecks [⟨"axiom diagnostic selection position", (← position axiomMessages "RG1001") ==
      Json.mkObj [("line", toJson (12 : Nat)), ("column", toJson (6 : Nat))]⟩]
    requireChecks
        [⟨"missing module documentation position", (← position missingMessages "RG5001") ==
      Json.mkObj [("line", toJson (missing.splitOn "\n").length), ("column", toJson (0 : Nat))]⟩]
    let lines ← IO.ofExcept (config.mapM fun value => do
      (← value.getObjVal? "pos").getObjValAs? Nat "line")
    requireChecks [⟨"configuration diagnostic ordering/positions", lines == [11, 12]⟩]
    let observer := "import Control\n/-! Imported observation control. -/\nrun_cmd do\n  let env ← \
      Lean.getEnv\n  for moduleName in #[`Control] do\n    unless \
      (Regula.Linter.Documentation.modulePresent env moduleName).toOption == some true do\n      \
      throwError \"imported module documentation absent\"\n  unless \
      Regula.Linter.Documentation.selected env `documented do\n    throwError \"imported \
      registration missing\"\n  unless (← Regula.Linter.Documentation.declarationFailure env \
      `documented).isNone == true do\n    throwError \"imported declaration documentation \
      mismatch\"\n  let d ← Regula.Collect.declaration `documented .snapshot\n  unless d.module == \
      `Control do throwError \"wrong imported ownership\"\n  unless \
      (Regula.Linter.Documentation.modulePresent env `Unknown).toOption.isNone do\n    throwError \
      \"unknown module treated as absent\"\n"
    let search := SearchPath.parse (← Launcher.leanPath root launcher)
    let env := #[("LEAN_PATH", some (SearchPath.toString (search ++ [scratch])))]
    -- One environment capture for the imported controls, before they run concurrently.
    let _ ← Launcher.environment root launcher env
    let dependent : Array (Control × Array (String × Option String)) := #[
      ({ label := "ConstructorIndexObserver", source :=
          "import Regula.Collect\nimport Regula.Report\nimport RegulaPolicy.Decision\n" ++
          (← IO.FS.readFile (root / "lean/Fixtures/Positive/ConstructorIndex.lean")) ++ "\n" ++
          (← IO.FS.readFile (root / "examples/qualification/ConstructorIndex.lean")) }, env),
      ({ label := "Imported", source := observer }, env),
      ({ label := "ImportedVerso", source := observer.replace "Control" "Verso" }, env),
      ({ label := "ImportedMissing", source := ((observer.replace "Control" "Missing").replace
        "== true" "== false").replace "some true" "some false" }, env),
      ({ label := "RestoredRange", source := restored, ids := ["RG1001"] }, #[]),
      ({ label := "Restored", source := base }, #[])] ++ retired.map fun (label, name) =>
      ({ label := label ++ "Importer", source := s!"import {label}\n" ++
          "/-! An imported retired compiler name remains an unknown axiom. -/\n" ++
          s!"theorem retiredDependency : True := {name}\n", ids := ["RG1003"] }, env)
    let _ ← Regula.Checker.mapWorkQueue jobs dependent fun (control, env) =>
      NativeLinter.check root scratch launcher control env
    IO.println s!"native bridge qualification: PASS ({1 + retired.size + independent.size + dependent.size} \
      actual Lean source controls)"

/-- Normal acceptance uses the cached actual Lake environment, never a cached verdict. -/
def checkAll : IO Unit := do
  let root ← rootDirectory
  withScratch root "native-controls" fun scratch => do checkAt root scratch (← Launcher.create)

/-- Paired baseline-first diagnostic with the same scratch path, source, argv, observed
outputs, environment and executable. Measurements describe only these actual runs. -/
def paired : IO Unit := do
  let root ← rootDirectory
  let output := root / "tmp/native-launcher-diagnostic.json"
  IO.FS.createDirAll (root / "tmp")
  if ← output.pathExists then IO.FS.removeFile output
  let started ← IO.monoMsNow
  let report ← IO.mkRef (Json.mkObj [("outcome", .str "INCOMPLETE"), ("equivalent", .bool false)])
  try
    withScratch root "launcher-pair" fun scratch => do
      let controls := scratch / "controls"
      let mut observations := #[]
      let mut runs := #[]
      for legacy in #[true, false] do
        IO.FS.createDir controls
        let launcher ← Launcher.create legacy
        let start ← IO.monoMsNow
        -- One control at a time keeps both runs' record order identical for the comparison.
        try checkAt root controls launcher (jobs := 1) finally IO.FS.removeDirAll controls
        let elapsed := (← IO.monoMsNow) - start
        let records ← launcher.records.get
        observations := observations.push records
        -- Environment values intentionally never leave memory.
        let encoded := records.map fun r => Json.mkObj [
          ("label", toJson r.label), ("args", toJson r.args), ("source", toJson r.source),
          ("returncode", toJson r.exitCode), ("stdout", toJson r.stdout),
          ("stderr", toJson r.stderr)]
        runs := runs.push (Json.mkObj [("legacy", .bool legacy), ("millis", toJson elapsed),
          ("captureMillis", toJson (← launcher.captureMillis.get)),
          ("controlMillis", toJson (← launcher.timings.get)),
          ("controls", toJson encoded)])
        report.modify (·.setObjVal! "runs" (toJson runs))
      let some before := observations[0]? | throw <| IO.userError "missing baseline"
      let some after := observations[1]? | throw <| IO.userError "missing candidate"
      requireChecks
          [⟨s!"{before.size} exact paired controls",
            RegulaQualification.Launcher.checked_equivalence.run before after⟩]
      report.modify fun value => (value.setObjVal! "equivalent" (.bool true)).setObjVal! "outcome"
                                  (.str "PASS")
      IO.println s!"launcher diagnostic: PASS ({before.size} exact paired controls; timing is an \
        observation only)"
  catch e =>
    report.modify (·.setObjVal! "outcome" (.str "FAIL"))
    throw e
  finally
    writeJson output ((← report.get).setObjVal! "totalMillis" (toJson ((← IO.monoMsNow) - started)))

end Regula.Qualification.NativeLinter
