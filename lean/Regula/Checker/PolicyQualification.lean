import Regula.Checker.SourceAudit

/-! # Policy transport qualification

Focused operational qualification of policy transport and public admission.
Universal value/collection laws live in RegulaPolicy. These controls exercise
JSON text, process packets, source elaboration and the actual CLI, whose linkage
is an operational boundary. Every public mutation has a fresh restored control. -/
universe u

namespace Regula.Checker.PolicyQualification
open Lean System
open Regula.Checker
open scoped Regula.Report

private def expectError {α : Type u} (label expected : String) (result : Except String α) : Array String :=
  match result with
  | .ok _ => #[s!"{label}: invalid input was accepted"]
  | .error error => if error.contains expected then #[]
    else #[s!"{label}: wrong refusal: {error}"]

private def expectOk {α : Type u} (label : String) (result : Except String α) : Array String :=
  match result with
  | .ok _ => #[]
  | .error error => #[s!"{label}: valid input refused: {error}"]

/-- Qualify the actual operational parser/decoder functions, not a second model. -/
def transport : Array String := Id.run do
  let mut failures := #[]
  let validText := "{\"x\":1,\"nested\":[{\"y\":true}]}"
  failures := failures ++ expectOk "parser-positive" (PolicyCodec.parse validText)
  for (label, input) in #[("duplicate", "{\"x\":1,\"x\":2}"),
      ("escaped-duplicate", "{\"x\":1,\"\\u0078\":1}"),
      ("nested-duplicate", "{\"a\":[{\"x\":1,\"x\":1}]}")] do
    failures := failures ++ expectError label "duplicate JSON field" (PolicyCodec.parse input)
  failures := failures ++ expectOk "parser-restored" (PolicyCodec.parse validText)
  let boundary : Regula.Report.ExecutionBoundary := {
    occurrence := 0, name := `sample, «module» := `PublicApi, boundary := .external
    account := .trusted none (), owned := true, replacement := none }
  let encoded := toJson boundary
  let decode (j : Json) := (fromJson? j : Except String Regula.Report.ExecutionBoundary)
  failures := failures ++ expectOk "boundary-positive" (decode encoded)
  for (label, field, value, expected) in #[("unknown-category", "boundary", .str "unknown", "unknown BoundaryKind"),
      -- A deliberate homoglyph: `trusted` with the Cyrillic letter U+0435 in place of `e`.
      ("typo-category", "correspondence", .str "trust\u0435d", "unknown Correspondence"),
      ("malformed-name", "name", .str "sample", "array expected"),
      ("extra-field", "extra", .bool true, "unknown or missing JSON object fields")] do
    failures := failures ++ expectError label expected (decode (encoded.setObjVal! field value))
  let .ok nativeOrigin := RegulaPolicy.admitNativeOrigin `Init
      "/toolchain/Init.olean" "/toolchain/Init.olean"
    | return failures.push "native-origin positive admission failed"
  let origin := toJson nativeOrigin
  failures := failures ++ expectError "discarded-origin" "boundary evidence contains incompatible fields"
    (decode (encoded.setObjVal! "nativeOrigin" origin))
  failures := failures ++ expectError "missing-category" "unknown or missing JSON object fields"
    (decode (Json.mkObj ((encoded.getObj?.toOption.map (·.toList)).getD [] |>.filter (·.1 != "boundary"))))
  failures := failures ++ expectOk "boundary-restored" (decode encoded)
  let root : Regula.Report.ExecutionRoot := {
    name := `sample, «module» := `PublicApi, boundaries := #[boundary], unresolved := #[], compilerEdges := #[]
    closure := {
      nodes := #[`sample]
      visits := #[{ name := `sample, moduleName := some `PublicApi, parent := none }] } }
  failures := failures ++ expectOk "execution-inventory-positive" (RegulaPolicy.admitExecution #[root])
  failures := failures ++ expectError "duplicate-root" "invalid execution inventory"
    (RegulaPolicy.admitExecution #[root, root])
  failures := failures ++ expectError "duplicate-boundary-occurrence" "invalid execution inventory"
    (RegulaPolicy.admitExecution #[{root with boundaries := #[boundary, boundary]}])
  failures := failures ++ expectOk "execution-inventory-restored" (RegulaPolicy.admitExecution #[root])
  let request := sourceWorkerRequest "transcript" `PublicApi "PublicApi.lean" "theorem t : True := .intro\n"
  let packet := workerPacket request (.str "result")
  failures := failures ++ expectOk "packet-positive" (readWorkerPacket request packet)
  failures := failures ++ expectError "request-mismatch" "request binding mismatch"
    (readWorkerPacket (.str "different request") packet)
  failures := failures ++ expectError "producer-mismatch" "producer or toolchain mismatch"
    (readWorkerPacket request (packet.setObjVal! "producer" .null))
  failures := failures ++ expectError "schema-mismatch" "unsupported worker schema"
    (readWorkerPacket request (packet.setObjVal! "schema" (toJson (2 : Nat))))
  failures := failures ++ expectOk "packet-restored" (readWorkerPacket request packet)
  let batch (values : Array (Nat × Nat)) :=
    admitIndexedWorkerResults 2 (fun key value : Nat => value == key + 10) (toJson values)
  let good := #[(0, 10), (1, 11)]
  failures := failures ++ expectOk "indexed-positive" (batch good)
  for (label, values, expected) in #[("duplicate-result", #[(0,10), (0,10), (1,11)], "duplicateResult"),
      ("conflicting-result", #[(0,10), (0,99), (1,11)], "duplicateResult"),
      ("unknown-result", #[(0,10), (1,11), (2,12)], "unknownKey"),
      ("wrong-result-binding", #[(0,11), (1,11)], "invalidBinding"),
      ("missing-result", #[(0,10)], "missing required key")] do
    failures := failures ++ expectError label expected (batch values)
  failures := failures ++ expectOk "indexed-restored" (batch good)
  let spec : SourceAudit.SourceSpec := { «module» := "PublicApi", source := "" }
  let compilation : SourceAudit.Compilation := {
    spec, sourcePath := "PublicApi.lean", oleanPath := "PublicApi.olean", ileanPath := "PublicApi.ilean"
    process := {exitCode := 0, stdout := "", stderr := ""} }
  let compiled := toJson compilation
  let decodeCompilation (j : Json) := (fromJson? j : Except String SourceAudit.Compilation)
  failures := failures ++ expectOk "process-positive" (decodeCompilation compiled)
  let overflow := Json.mkObj [("exitCode", toJson (2^32 : Nat)), ("stdout", .str ""), ("stderr", .str "")]
  failures := failures ++ expectError "process-overflow" "invalid process exit code"
    (decodeCompilation (compiled.setObjVal! "process" overflow))
  failures := failures ++ expectOk "process-restored" (decodeCompilation compiled)
  return failures

private def source : String :=
  "import Regula.Diagnostic\nimport Regula.StructuralName\nimport Lean\n" ++
  "/-! Public name-codec proof and compiler-root classification controls. -/\n" ++
  "inductive Branch where\n  | node : List Branch → Branch\n" ++
  "theorem publicNameRoundtrip (n : Lean.Name) :\n" ++
  "    Regula.RegistryCodec.parseName (Regula.RegistryCodec.nameJson n) = .ok n :=\n" ++
  "  Regula.RegistryCodec.name_roundtrip n\n" ++
  "abbrev Pretend.brecOn.go : PProd Nat Nat := ⟨0, 0⟩\n" ++
  "abbrev Pretend.brecOn : Nat := Pretend.brecOn.go.1\n" ++
  "run_cmd Lean.modifyEnv fun env => Lean.markAuxRecursor env `Pretend.brecOn\n" ++
  "def ordinaryUnused : Nat := 0\n" ++
  "def auxUnused : Nat := 0\n" ++
  "def confusionUnused : Nat := 0\n" ++
  "def match_unused : Nat := 0\n" ++
  "run_cmd Lean.modifyEnv fun env => Lean.markAuxRecursor env `auxUnused\n" ++
  "run_cmd Lean.modifyEnv fun env => Lean.markNoConfusion env `confusionUnused (.regular 0 0 0)\n" ++
  "run_cmd Lean.Meta.Match.addMatcherInfo `match_unused default\n" ++
  "run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.defnDecl { name := `auxUncompiled, levelParams := [], type := Lean.mkConst ``Nat, value := Lean.mkNatLit 0, hints := .abbrev, safety := .safe })\n" ++
  "run_cmd Lean.modifyEnv fun env => Lean.markAuxRecursor env `auxUncompiled\n"

private def setup (repo adopter : FilePath) : IO Unit := do
  IO.FS.createDirAll adopter
  IO.FS.writeFile (adopter / "lean-toolchain") (← IO.FS.readFile (repo / "lean-toolchain"))
  IO.FS.writeFile (adopter / "lakefile.lean") <|
    "import Lake\nopen Lake DSL\npackage policy_adopter\nrequire regula from " ++
      (toJson repo.toString).compress ++ "\n@[default_target] lean_lib PublicApi\n"
  IO.FS.writeFile (adopter / "foundation_manifest.json") <| Json.compress <| Json.mkObj [
    ("schema-version", toJson (2 : Nat)), ("surfaces", toJson #[Json.mkObj [
      ("library", .str "PublicApi"), ("claim", .str "standard-logical"),
      ("execution", .str "checked"), ("rationale", .str "Public policy admission control")]]),
    ("excluded-libraries", toJson (#[] : Array Json)), ("excluded-executables", toJson (#[] : Array Json))]
  let base ← readJson (repo / "lake-manifest.json")
  let packages : Array Json ← IO.ofExcept <| base.getObjValAs? (Array Json) "packages"
  let dependency := Json.mkObj [("name", .str "regula"), ("scope", .str ""),
    ("configFile", .str "lakefile.lean"), ("manifestFile", .str "lake-manifest.json"),
    ("inherited", .bool false), ("type", .str "path"), ("dir", .str repo.toString)]
  writeJson (adopter / "lake-manifest.json") <| base.setObjVal! "packages" <|
    toJson (#[dependency] ++ packages.map (·.setObjVal! "inherited" (.bool true)))
  IO.FS.createDirAll (adopter / ".lake")
  let linked ← runProcess adopter "ln" #["-s", (repo / ".lake" / "packages").toString,
    (adopter / ".lake" / "packages").toString]
  unless linked.succeeded do throw <| IO.userError linked.output

/-- Actual external adopter, single-fault mutations, and fresh source restoration.
No mutation executes the fabricated extern body. -/
def publicPaths (repo scratch : FilePath) : IO (Array String) := do
  let adopter := scratch / "adopter"
  setup repo adopter
  let binary := repo / ".lake" / "build" / "bin" / "axiomGate"
  let invoke := runProcess adopter binary.toString #["--project", adopter.toString] scrubbedLeanPathEnv
  let mut failures := #[]
  let cases := #[("forbidden-report", "import Regula.Report\n" ++ source, #["probe", "Regula.Report"]),
    ("forbidden-probe", "import Regula.Probe\n" ++ source, #["probe", "Regula.Probe"]),
    ("forged-helper", source.replace "abbrev Pretend.brecOn.go"
      "@[extern \"policy_forgery\"] abbrev Pretend.brecOn.go", #["execution-trusted-boundary", "Pretend.brecOn.go"]),
    ("generated-helper-runtime-change", source ++ "attribute [extern \"policy_recursion\"] Branch.brecOn.go\n",
      #["execution-trusted-boundary", "Branch.brecOn.go"]),
    ("tagged-root-placeholder", source ++
      "run_cmd Lean.modifyEnv fun env => Lean.IR.declMapExt.addEntry env (.extern `auxUncompiled #[] .object default)\n",
      #["execution-unresolved", "auxUncompiled", "opaque export placeholder"])] ++
    #["ordinaryUnused", "auxUnused", "confusionUnused", "match_unused"].map (fun name =>
      (s!"unused-root-{name}", source.replace s!"def {name} : Nat" s!"@[extern \"unused_root_boundary\"] def {name} : Nat",
        #["execution-trusted-boundary", name]))
  IO.FS.writeFile (adopter / "PublicApi.lean") source
  let positive ← invoke
  unless positive.succeeded do
    return #[s!"public-policy-positive: {positive.output}"]
  IO.println "policy public adopter positive: PASS"
  (← IO.getStdout).flush
  for (label, mutated, expected) in cases do
    IO.FS.writeFile (adopter / "PublicApi.lean") mutated
    let rejected ← invoke
    if rejected.succeeded || !expected.all (fun value => rejected.output.contains value) then
      failures := failures.push s!"{label}: expected refusal {expected}; got {rejected.exitCode}\n{rejected.output}"
    else IO.println s!"policy {label}: intended refusal"
    (← IO.getStdout).flush
    IO.FS.writeFile (adopter / "PublicApi.lean") source
    let restored ← invoke
    unless restored.succeeded do failures := failures.push s!"{label}-restored: {restored.output}"
  let file := adopter / "Warning.lean"
  let positiveFile := "import Lean\ntheorem clean : True := .intro\n"
  let invokeFile := runProcess adopter binary.toString #["--file", file.toString,
    "--claim", "standard-logical"] scrubbedLeanPathEnv
  IO.FS.writeFile file positiveFile
  let before ← invokeFile
  unless before.succeeded do failures := failures.push s!"warning-positive: {before.output}"
  IO.FS.writeFile file (positiveFile ++
    "set_option warningAsError false\nrun_cmd Lean.logWarning \"policy-domain warning control\"\n")
  let warning ← invokeFile
  if warning.succeeded || !warning.output.contains "policy-domain warning control" then
    failures := failures.push s!"warning-negative: {warning.output}"
  IO.FS.writeFile file positiveFile
  let restored ← invokeFile
  unless restored.succeeded do failures := failures.push s!"warning-restored: {restored.output}"
  return failures
/-- Qualify the actual production import through the unchanged public project gate.
The preceding domain campaign owns forbidden-import and execution mutations. -/
def nativeImport (repo scratch : FilePath) : IO (Array String) := do
  let adopter := scratch / "adopter"
  setup repo adopter
  let nativeSource := "import Regula.Linter\n" ++ source.replace "import Lean\n"
    "import Lean\n/-! Native linter adopter with retained execution controls. -/\n"
  IO.FS.writeFile (adopter / "PublicApi.lean") nativeSource
  let result ← runProcess adopter (repo / ".lake" / "build" / "bin" / "axiomGate").toString
    #["--project", adopter.toString] scrubbedLeanPathEnv
  if result.succeeded then
    IO.println "native public adopter: PASS"
    return #[]
  return #[s!"native public adopter: {result.output}"]

end Regula.Checker.PolicyQualification
