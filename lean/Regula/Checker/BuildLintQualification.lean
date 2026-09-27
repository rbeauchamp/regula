import Regula.Checker.Common

/-!
# Build-policy path qualification

Qualification of the opt-in ordinary-Lake-build policy path. Every case uses
the shipped adopter's actual default target, one independent mutation, and a
fresh restored build. These are diagnostics of the checker, not correctness
proofs for the programs or the linter.
-/

namespace Regula.Checker.BuildLintQualification

open Lean System

private def manifest (claim : String := "kernel-only") (execution : String := "checked") : String :=
  Json.compress <| Json.mkObj [
    ("schema-version", toJson (2 : Nat)),
    ("surfaces", toJson #[Json.mkObj [
      ("library", toJson "Widget"), ("claim", toJson claim),
      ("execution", toJson execution), ("rationale", toJson "build control")]]),
    ("excluded-libraries", toJson (#[] : Array Json)),
    ("excluded-executables", toJson (#[] : Array Json))]

private def proofSource (proof : String) : String :=
  s!"theorem truth : True := {proof}\n"

private def classicalProof := "Classical.choice (show Nonempty True from ⟨True.intro⟩)"

private def witnessSource : String :=
  "import Regula.Contract\n" ++
  "/-- A control witness. -/\n" ++
  "def witness : {n : Nat // n = 1} := ⟨1, rfl⟩\n" ++
  "theorem witnessContract : Regula.ExecutableContract witness " ++
  "(fun n => n.val = 1) := ⟨witness.property⟩\n"

private def identitySource (beforeDefinition : String := "") : String :=
  "import Regula.Contract\n" ++ "/-- A control definition. -/\n" ++ beforeDefinition ++
  "def identity (n : Nat) := n\n" ++
  "theorem identityContract : Regula.ExecutableContract identity " ++
  "(fun f => ∀ n, f n = n) := ⟨fun _ => rfl⟩\n"

private structure Case where
  name : String
  /-- Alternative initial files in the disposable adopter. -/
  files : Array (String × String) := #[]
  support : Option String := none
  path : String := "Widget.lean"
  before : String
  after : String
  expected : Array String
  repeatCachedFailure : Bool := false

private def cases : Array Case := #[
  { name := "direct-choice"
    files := #[("Widget.lean", proofSource "True.intro"),
      ("foundation_manifest.json", manifest "choice-free")]
    before := "True.intro", after := classicalProof
    expected := #["label-exceeds-claim", "truth", "Classical.choice", "choice-free"]
    repeatCachedFailure := true },
  { name := "cached-profile-change"
    files := #[("Widget.lean", proofSource classicalProof),
      ("foundation_manifest.json", manifest "standard-logical")]
    path := "foundation_manifest.json"
    before := "standard-logical", after := "choice-free"
    expected := #["label-exceeds-claim", "Classical.choice"] },
  { name := "choice-free-positive"
    files := #[("Widget.lean", "theorem ext : (True ∧ True) = True := propext ⟨And.left, fun h => ⟨h, h⟩⟩\n"),
      ("foundation_manifest.json", manifest "choice-free")]
    path := "foundation_manifest.json"
    before := "choice-free", after := "kernel-only"
    expected := #["label-exceeds-claim", "propext", "kernel-only"] },
  { name := "erased-classical-contract"
    files := #[("Widget.lean", identitySource |>.replace "⟨fun _ => rfl⟩"
      "⟨Classical.byContradiction (fun h => h (fun _ => rfl))⟩"),
      ("foundation_manifest.json", manifest "standard-logical")]
    path := "foundation_manifest.json"
    before := "standard-logical", after := "choice-free"
    expected := #["label-exceeds-claim", "identityContract", "Classical.choice"] },
  { name := "unused-private-axiom"
    before := "namespace Widget", after := "private axiom unusedAssumption : True\nnamespace Widget"
    expected := #["project-axiom", "unusedAssumption"] },
  { name := "unimported-configured-module"
    path := "Widget/Additional.lean"
    before := "namespace Widget.Additional", after := "/-- A control assumption. -/\naxiom unimported : True\nnamespace Widget.Additional"
    expected := #["project-axiom", "unimported"] },
  { name := "missing-evidence"
    before := ":=\n  ⟨fun _ => rfl⟩", after := "where"
    expected := #["build-failed", "Fields missing", "evidence"] },
  { name := "weakened-evidence"
    before := "⟨fun _ => rfl⟩", after := "⟨fun (n : Nat) (_ : n = 0) => rfl⟩"
    expected := #["build-failed", "Application type mismatch", "n = 0", "SuccessorSpec successor"] },
  { name := "unrelated-evidence"
    before := "⟨fun _ => rfl⟩", after := "⟨True.intro⟩"
    expected := #["build-failed", "Application type mismatch", "True", "SuccessorSpec"] },
  { name := "deleted-evidence"
    before := "theorem identityContract", after := "theorem discardedContract"
    files := #[("Widget.lean", identitySource ++ "/-- A control use of the contract. -/\ndef use := identityContract.run\n")]
    expected := #["build-failed", "Unknown identifier"] },
  { name := "existence-is-not-witness-evidence"
    before := "⟨fun _ => rfl⟩"
    after := "(show ∀ n : Nat, ∃ m : Nat, m = n + 1 from fun n => ⟨n + 1, rfl⟩)"
    expected := #["build-failed", "Type mismatch", "ExecutableContract"] },
  { name := "noncomputable-witness"
    files := #[("Widget.lean", witnessSource),
      ("foundation_manifest.json", manifest "standard-logical")]
    before := "def witness : {n : Nat // n = 1} := ⟨1, rfl⟩"
    after := "noncomputable def witness : {n : Nat // n = 1} := Classical.choice ⟨⟨1, rfl⟩⟩"
    expected := #["executable-contract", "witnessContract", "noncomputable"] },
  { name := "noncomputable-marking"
    files := #[("Widget.lean", witnessSource)]
    before := "def witness", after := "noncomputable def witness"
    expected := #["executable-contract", "noncomputable"] },
  { name := "unsupported-parameterized-registration"
    files := #[("Widget.lean", identitySource)]
    before := "theorem identityContract :", after := "theorem identityContract (_n : Nat) :"
    expected := #["executable-contract", "registration must be closed"] },
  { name := "unsupported-partial-application"
    files := #[("Widget.lean", identitySource)]
    before := "identity (fun f => ∀ n, f n = n) := ⟨fun _ => rfl⟩"
    after := "(identity 0) (fun n => n = 0) := ⟨rfl⟩"
    expected := #["executable-contract", "named constant"] },
  { name := "type-producing-root-alias"
    files := #[("Widget.lean", "import Regula.Contract\n" ++
      "/-- A control alias. -/\n@[irreducible] def ResultAlias := Nat\n/-- A control root. -/\n@[macro_inline] def root : ResultAlias := by unfold ResultAlias; exact 0\n" ++
      "theorem contract : Regula.ExecutableContract root (fun _ => True) := ⟨True.intro⟩\n")]
    before := "@[irreducible] def ResultAlias := Nat\n/-- A control root. -/\n@[macro_inline] def root : ResultAlias := by unfold ResultAlias; exact 0"
    after := "@[irreducible] def ResultAlias := Type\n/-- A control root. -/\n@[macro_inline] def root : ResultAlias := by unfold ResultAlias; exact Nat"
    expected := #["executable-contract", "contract", "returns a type"] },
  { name := "aliased-contract-registration"
    files := #[("Widget.lean", "import Regula.Contract\n" ++
      "/-- A control root. -/\ndef root (n : Nat) := n\n" ++
      "/-- A control requirement. -/\n@[irreducible] def Required : Prop := Regula.ExecutableContract root (fun _ => True)\n" ++
      "theorem contract : Required := by unfold Required; exact ⟨True.intro⟩\n")]
    before := "def root", after := "noncomputable def root"
    expected := #["executable-contract", "contract", "noncomputable"] },
  { name := "private-executable-boundary"
    files := #[("Widget.lean", identitySource "private ")]
    before := "private def identity", after := "@[extern \"lps_private_external\"] private def identity"
    expected := #["execution-trusted-boundary", "identity", "external"] },
  { name := "replacement-boundary"
    files := #[("Widget.lean", identitySource "def replacement (n : Nat) := n\n/-- A control definition. -/\n@[implemented_by replacement] ")]
    before := "def replacement (n : Nat) := n", after := "def replacement (n : Nat) := n + 1"
    expected := #["execution-trusted-boundary", "identity", "runtime-replacement"] },
  { name := "cached-execution-policy"
    files := #[("Widget.lean", identitySource "@[extern \"lps_external\"] "),
      ("foundation_manifest.json", manifest "kernel-only" "report")]
    path := "foundation_manifest.json"
    before := "report", after := "checked"
    expected := #["execution-trusted-boundary", "external"] },
  { name := "invalid-profile"
    path := "foundation_manifest.json", before := "kernel-only", after := "unknown"
    expected := #["manifest", "claim"] },
  { name := "unclassified-library"
    files := #[("Extra.lean", "theorem extra : True := True.intro\n")]
    path := "lakefile.lean", before := "lean_lib Widget", after := "lean_lib Extra\n\nlean_lib Widget"
    expected := #["manifest-incomplete", "Extra"] },
  { name := "late-warning-suppression"
    before := "namespace Widget"
    after := "set_option warningAsError false\ndef emitsWarning (unused : Nat) := 0\nnamespace Widget"
    expected := #["build-failed", "warning"]
    repeatCachedFailure := true },
  { name := "imported-cached-choice"
    files := #[("Widget.lean", "import Support\ntheorem dependent : True := Support.truth\n"),
      ("foundation_manifest.json", manifest "choice-free")]
    support := some ("namespace Support\n" ++ proofSource "True.intro" ++ "end Support\n")
    path := "support/Support.lean", before := "True.intro", after := classicalProof
    expected := #["label-exceeds-claim", "dependent", "Classical.choice"] },
  { name := "imported-cached-csimp"
    files := #[("Widget.lean", "import Support\nimport Regula.Contract\n" ++
      "theorem importedContract : Regula.ExecutableContract Support.entry " ++
      "(fun f => ∀ n, f n = n) := ⟨fun _ => rfl⟩\n")]
    support := some ("namespace Support\ndef target (n : Nat) := n\n" ++
      "def reference (n : Nat) := n\n@[csimp] theorem optimize : reference = target := rfl\n" ++
      "def entry (n : Nat) := reference n\nend Support\n")
    path := "support/Support.lean", before := "def target"
    after := "@[extern \"lps_imported_external\"] def target"
    expected := #["execution-trusted-boundary", "Support.target", "external"] },
  { name := "imported-unsafe-replacement"
    files := #[("Widget.lean", "import Support\nimport Regula.Contract\n" ++
      "theorem importedContract : Regula.ExecutableContract Support.reference " ++
      "(fun f => ∀ n, f n = n) := ⟨fun _ => rfl⟩\n")]
    support := some ("namespace Support\nunsafe def dangerous (n : Nat) := n\n" ++
      "def target (n : Nat) := n\n@[implemented_by target] def reference (n : Nat) := n\nend Support\n")
    path := "support/Support.lean", before := "implemented_by target"
    after := "implemented_by dangerous"
    expected := #["execution-trusted-boundary", "unsafe-computation"] }
]

/-- Use the checked-in public recipe verbatim apart from the local dependency
path. Dependencies are inherited exactly as Lake resolves the pinned package;
only their already-built checkouts are shared across isolated controls. -/
def setup (repo adopter : FilePath) (exampleDir : String := "build-lint")
    (sources : Array String := #["Widget.lean", "Widget/Additional.lean"])
    (lakefileName : String := "lakefile.lean") : IO Unit := do
  let template := repo / "examples" / exampleDir
  for name in sources ++ #["lean-toolchain", "foundation_manifest.json"] do
    if let some parent := (adopter / name).parent then IO.FS.createDirAll parent
    IO.FS.writeFile (adopter / name) (← IO.FS.readFile (template / name))
  let lakefile ← IO.FS.readFile (template / lakefileName)
  IO.FS.writeFile (adopter / lakefileName)
    (lakefile.replace "\"../..\"" (Json.compress (toJson repo.toString)))
  let base ← readJson (repo / "lake-manifest.json")
  let packages : Array Json ← IO.ofExcept <| base.getObjValAs? (Array Json) "packages"
  let dependency := Json.mkObj [
    ("name", toJson "regula"), ("scope", toJson ""),
    ("configFile", toJson "lakefile.lean"), ("manifestFile", toJson "lake-manifest.json"),
    ("inherited", toJson false), ("type", toJson "path"), ("dir", toJson repo.toString)]
  writeJson (adopter / "lake-manifest.json") <| base.setObjVal! "packages" <|
    toJson (#[dependency] ++ packages.map (·.setObjVal! "inherited" (toJson true)))
  IO.FS.createDirAll (adopter / ".lake")
  let linked ← runProcess adopter "ln" #["-s", (repo / ".lake" / "packages").toString,
    (adopter / ".lake" / "packages").toString]
  if !linked.succeeded then throw <| IO.userError linked.output

private def build (adopter : FilePath) : IO ProcessResult :=
  runProcess adopter "lake" #["build"] scrubbedLeanPathEnv

private def positive (name : String) (result : ProcessResult) : Array String :=
  if result.succeeded && result.output.contains "build policy linter: PASS" then #[]
  else #[s!"build-lint/{name}: enabled positive failed:\n{result.output}"]

private def negative (test : Case) (result : ProcessResult) : Array String :=
  if result.succeeded then #[s!"build-lint/{test.name}: mutation passed"]
  else if let some missing := test.expected.find? (!result.output.contains ·) then
    #[s!"build-lint/{test.name}: missing intended diagnostic {missing}:\n{result.output}"]
  else #[]

private def addSupport (adopter : FilePath) (source : String) : IO Unit := do
  let support := adopter / "support"
  IO.FS.createDirAll support
  IO.FS.writeFile (support / "Support.lean") source
  IO.FS.writeFile (support / "lean-toolchain") (← IO.FS.readFile (adopter / "lean-toolchain"))
  IO.FS.writeFile (support / "lakefile.toml")
    "name = \"build_lint_support\"\n[[lean_lib]]\nname = \"Support\"\n"
  let path := adopter / "lakefile.lean"
  IO.FS.writeFile path ((← IO.FS.readFile path) ++ "\nrequire build_lint_support from \"support\"\n")
  let path := adopter / "lake-manifest.json"
  let value ← readJson path
  let packages : Array Json ← IO.ofExcept <| value.getObjValAs? (Array Json) "packages"
  let dependency := Json.mkObj [
    ("name", toJson "build_lint_support"), ("scope", toJson ""),
    ("configFile", toJson "lakefile.toml"), ("manifestFile", toJson "lake-manifest.json"),
    ("inherited", toJson false), ("type", toJson "path"), ("dir", toJson support.toString)]
  writeJson path <| value.setObjVal! "packages" (toJson (packages.push dependency))

private def runCase (repo adopter : FilePath) (test : Case) : IO (Array String) := do
  setup repo adopter
  if let some source := test.support then addSupport adopter source
  for (path, source) in test.files do
    -- A control's intended defect is independent of module-doc presence.
    let source := if (FilePath.mk path).extension == some "lean" then
        source ++ s!"\n/-! Build integration control for {test.name}. -/\n"
      else source
    IO.FS.writeFile (adopter / path) source
  let mut failures := positive s!"{test.name}/positive" (← build adopter)
  if !failures.isEmpty then return failures
  let path := adopter / test.path
  let original ← IO.FS.readFile path
  if (original.splitOn test.before).length != 2 then
    return #[s!"build-lint/{test.name}: expected exactly one mutation anchor {test.before}"]
  IO.FS.writeFile path (original.replace test.before test.after)
  failures := failures ++ negative test (← build adopter)
  if test.repeatCachedFailure then failures := failures ++ negative test (← build adopter)
  IO.FS.writeFile path original
  IO.FS.removeDirAll (adopter / ".lake" / "build")
  if test.support.isSome then IO.FS.removeDirAll (adopter / "support" / ".lake" / "build")
  failures := failures ++ positive s!"{test.name}/fresh-restored" (← build adopter)
  IO.println s!"build-lint control {test.name}: completed (positive/mutation/fresh restoration)"
  (← IO.getStdout).flush
  return failures

/-- Disabling the default policy target removes foundation enforcement, while
reenabling it rejects the very same cached axiom. Typed evidence obligations
remain ordinary Lean obligations in either mode. -/
private def disabledControl (repo adopter : FilePath) : IO (Array String) := do
  setup repo adopter
  let path := adopter / "lakefile.lean"
  let enabled ← IO.FS.readFile path
  let disabled := enabled.replace "@[default_target]\n" ""
    |>.replace "lean_lib Widget" "@[default_target]\nlean_lib Widget"
  IO.FS.writeFile path disabled
  let source := adopter / "Widget.lean"
  let original ← IO.FS.readFile source
  IO.FS.writeFile source "/-! Cached axiom used to qualify disabling and reenabling policy. -/\n/-- A control assumption. -/\naxiom disabledAssumption : True\n"
  let result ← build adopter
  let mut failures := if result.succeeded && !result.output.contains "build policy linter:" then #[]
    else #[s!"build-lint/disabled: ordinary build did not remain disabled:\n{result.output}"]
  IO.FS.writeFile path enabled
  failures := failures ++ negative {
    name := "reenabled-cached-axiom", before := "", after := "",
    expected := #["project-axiom", "disabledAssumption"] } (← build adopter)
  IO.FS.writeFile source original
  IO.FS.removeDirAll (adopter / ".lake" / "build")
  failures := failures ++ positive "reenabled/fresh-restored" (← build adopter)
  return failures

/-- Independently mutated standalone adopters, each using only `lake build`.
The existing compiler-path suite separately qualifies the shared policy's
unchanged replacement-history and correspondence machinery. -/
def qualify (repo scratch : FilePath) (jobs : Nat) : IO (Array String) := do
  let results ← mapConcurrent jobs cases fun test => do
    withScratch scratch test.name fun adopter => runCase repo adopter test
  let disabled ← withScratch scratch "disabled" fun adopter => disabledControl repo adopter
  return results.foldl (· ++ ·) disabled

end Regula.Checker.BuildLintQualification
