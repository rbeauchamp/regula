module

public import RegulaPolicy.Compiler

/-! # Development compiler qualification decisions

The driver executes these recipes and this completion decision. Completion means that
all named commands met their exact exit and output requirements for unchanged observed inputs. It grants no admission
authority and proves nothing about the processes, compiler executable, or filesystem. -/

@[expose] public section

namespace Regula.Toolchain

/-- A compiler's identity and the observed capability used by declaration policy. -/
structure Identity where
  /-- The complete version string, including a prerelease suffix. -/
  version : String
  /-- The full forty-character Git commit. -/
  commit : String
  /-- Whether the compiler's origin-checked Core declares the legacy compiler-trust family. -/
  legacyCompilerTrust : RegulaPolicy.Compiler.LegacyCompilerTrust
  deriving BEq, DecidableEq, Repr

/-- A nonempty version and a complete lowercase hexadecimal source commit. -/
def Identity.valid (i : Identity) : Bool :=
  !i.version.isEmpty && i.commit.length == 40 &&
    i.commit.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

/-- Admit the compiler probe's exact three-line output, including its final newline. -/
def parseIdentity (output : String) : Except String Identity :=
  match output.splitOn "\n" with
  | [v, h, capability, ""] =>
    match RegulaPolicy.Compiler.LegacyCompilerTrust.parse? capability with
    | none => .error "compiler capability is unknown"
    | some capability =>
      let i := Identity.mk v h capability
      if i.valid then .ok i else .error "compiler identity is incomplete"
  | _ => .error "compiler probe did not return exactly a version, full commit and capability"

/-- Parsing cannot replace a malformed or incomplete identity with a default. -/
theorem parseIdentity_valid {output : String} {i : Identity}
    (h : parseIdentity output = .ok i) : i.valid = true := by
  unfold parseIdentity at h
  split at h
  · split at h
    · cases h
    · dsimp only at h
      split at h
      · cases h; assumption
      · cases h
  · cases h

/-- The toolchains `elan toolchain list` printed, one name on each line, without the
` (default)` marker Elan 3 appends to the default toolchain. A remaining line with a space,
such as Elan's notice that none is installed, names no toolchain. -/
def listedToolchains (output : String) : List String :=
  (output.splitOn "\n").map (·.trimAscii.toString.dropSuffix " (default)" |>.toString) |>.filter
    (fun line => !line.isEmpty && !line.contains ' ')

/-- The listed toolchain `selector` names: the selector itself, exactly as listed (a linked
toolchain or a full name). It resolves no channel, completes no shorter spelling and installs
nothing: a channel such as `stable` resolves only when the listing names a toolchain spelled
exactly so. -/
def installedName? (listed : List String) (selector : String) : Option String :=
  listed.find? (· == selector)

/-- A selector resolves only to itself, and only when it is listed. -/
theorem installedName?_spec {listed : List String} {selector name : String}
    (h : installedName? listed selector = some name) :
    name ∈ listed ∧ name = selector := by
  unfold installedName? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- One existing build or detector campaign, in dependency order. -/
structure Campaign where
  /-- A stable receipt/log name. -/
  name : String
  /-- Arguments to the selected toolchain's Lake executable. -/
  args : List String
  /-- Whether this command explicitly requests candidate diagnostic observations. -/
  diagnostic : Bool := true
  /-- The required process exit, including a refusal control's nonzero exit. -/
  expectedExit : UInt32 := 0
  /-- A required public output fragment; empty when the exit is the whole observation. -/
  requiredText : String := ""
  deriving BEq, DecidableEq, Repr

/-- Core checker qualification; Mathlib, Verso and the website corpus are separate claims. -/
def campaigns : List Campaign := [
  { name := "build", args := ["build", "Regula", "axiomGate", "checkerSelftest", "qualify", "lint", "regula"] },
  { name := "candidate-refusal", args := ["exe", "axiomGate", "--help", "--json-out",
      ".lake/regula-toolchain/ordinary-refusal.json"], diagnostic := false, expectedExit := 3,
      requiredText := "unsupported compiler/checker combination" },
  { name := "fixtures", args := ["exe", "checkerSelftest", "--build-bound", "--partition", "fixtures"] },
  { name := "producers", args := ["exe", "qualify", "--under-deadline", "producers"] },
  { name := "history", args := ["exe", "qualify", "--under-deadline", "history"] },
  { name := "structural", args := ["exe", "checkerSelftest", "--build-bound", "--partition", "structural"] },
  { name := "execution", args := ["exe", "checkerSelftest", "--build-bound", "--partition", "execution"] },
  { name := "lint-driver", args := ["exe", "checkerSelftest", "--build-bound", "--partition", "lint-driver"] },
  { name := "self-audit", args := ["exe", "qualify", "--under-deadline", "self-audit"] }]

/-- One process observation, before classification. Output is retained in the campaign log. -/
structure Observation where
  /-- The exact recipe executed. -/
  campaign : Campaign
  /-- The observed exit code. -/
  exitCode : UInt32
  /-- The observed standard output followed by standard error. -/
  output : String

/-- The required exit and public output fragment, without interpreting an error as success. -/
def Observation.meets (o : Observation) : Bool :=
  o.exitCode == o.campaign.expectedExit &&
    (o.campaign.requiredText.isEmpty || o.output.contains o.campaign.requiredText)

/-- Recorded exit observations in the exact required order, without omitted commands. -/
def complete (results : List Observation) : Bool :=
  decide (results.map Observation.campaign = campaigns) && results.all Observation.meets

/-- Completion requires every exact recipe, in order, and each required observation. -/
theorem complete_iff (results : List Observation) : complete results = true ↔
    results.map Observation.campaign = campaigns ∧ ∀ r ∈ results, r.meets = true := by
  simp [complete, List.all_eq_true]

end Regula.Toolchain
