module

public import Init

/-! # Exact compiler support

Each checker source revision names one compiler identity. Version strings alone do not
identify development builds. The compiler's reported identity and the integrity of its
executable remain trusted observations; these contracts compare the supplied strings. -/

@[expose] public section

namespace RegulaPolicy.Compiler

/-- Whether the selected compiler's origin-checked Core declares the legacy compiler axioms.
Native proof axioms have their separate per-invocation authentication. -/
inductive LegacyCompilerTrust where
  /-- Core declares the complete legacy compiler-trust family. -/
  | present
  /-- Core declares none of the legacy compiler-trust family. -/
  | absent
  deriving BEq, DecidableEq, Repr

/-- Canonical transport spelling of the observed capability. -/
def LegacyCompilerTrust.spelling : LegacyCompilerTrust → String
  | .present => "present"
  | .absent => "absent"

/-- Unknown and missing capability spellings cannot supply a default. -/
def LegacyCompilerTrust.parse? : String → Option LegacyCompilerTrust
  | "present" => some .present
  | "absent" => some .absent
  | _ => none

@[simp] theorem LegacyCompilerTrust.roundtrip (c : LegacyCompilerTrust) :
    parse? c.spelling = some c := by cases c <;> rfl

/-- The capability declared by this source revision and re-observed before policy admission. -/
def legacyCompilerTrust : LegacyCompilerTrust := .present

/-- An observed capability equal to the one used by this compiled policy.
Its proof concerns the supplied observation; compiler installation and extraction are trusted. -/
structure Capability where
  /-- The actual observation retained at admission. -/
  legacy : LegacyCompilerTrust
  /-- Observation and compiled classification policy agree. -/
  agrees : legacy = legacyCompilerTrust
  deriving DecidableEq, Repr

/-- Admit precisely the capability this compiled policy expects. -/
def admitCapability (observed : LegacyCompilerTrust) : Except String Capability :=
  if h : observed = legacyCompilerTrust then .ok ⟨observed, h⟩
  else .error "compiler capability differs from this Regula build"

/-- Capability admission succeeds exactly when the observation matches this compiled policy. -/
theorem admitCapability_iff (observed : LegacyCompilerTrust) :
    (∃ c, admitCapability observed = .ok c) ↔ observed = legacyCompilerTrust := by
  simp only [admitCapability]
  split <;> simp_all

/-- The compiler version declared by this source revision. Publication requires qualification. -/
def version : String := "4.34.0"

/-- The full compiler commit declared by this source revision. -/
def commit : String := "293d5d0c0c3f3dded4688b3ccd6a33939ac5102b"

/-- Prepared revisions are candidates until reviewed qualification permits promotion. -/
def candidate : Bool := false

/-- The entrypoints that call this decision (`axiomGate`, so also the `lake lint` audit,
`docFenceAudit` and `freshChecker`) refuse candidates. Explicit diagnostics may observe them. -/
def mayRun (isCandidate diagnostic : Bool) : Bool := !isCandidate || diagnostic

/-- A candidate can run only with an explicit diagnostic purpose. -/
theorem candidate_mayRun_iff (diagnostic : Bool) :
    mayRun true diagnostic = true ↔ diagnostic = true := by
  simp [mayRun]

/-- Public output keeps candidate observations distinct from supported audit evidence. -/
inductive Publication (α : Type) where
  /-- Output of a revision whose compiler support has been qualified. -/
  | audit (value : α)
  /-- Development observations, which confer no support or conformance. -/
  | diagnostic (value : α)

/-- The classifier executed by result writers. -/
def publication {α : Type} (isCandidate : Bool) (value : α) : Publication α :=
  if isCandidate then .diagnostic value else .audit value

/-- Candidate observations cannot be classified as supported audit output. -/
theorem candidate_not_audit {α : Type} (value other : α) :
    publication true value ≠ .audit other := by
  simp [publication]

/-- Successful candidate observations retain their diagnostic purpose in public text. -/
def successLabel (isCandidate : Bool) (supported observed : String) : String :=
  if isCandidate then s!"DIAGNOSTIC {observed} (unqualified compiler)" else supported

/-- Candidate labels never use the supplied supported verdict. -/
theorem candidate_successLabel (supported observed : String) :
    successLabel true supported observed = s!"DIAGNOSTIC {observed} (unqualified compiler)" := rfl

/-- The public acceptance label. -/
def verdict (isCandidate : Bool) : String := successLabel isCandidate "PASS" "ACCEPTED"

/-- Exact public text classification for a candidate. -/
theorem candidate_verdict : verdict true = "DIAGNOSTIC ACCEPTED (unqualified compiler)" := rfl

/-- The positive documentation count label, shared by writers and qualification readers. -/
def positiveSummary (isCandidate : Bool) : String :=
  if isCandidate then "diagnostic-positive-observed" else "conforming-positive-pass"

/-- Candidate counts describe observations without a conformance claim. -/
theorem candidate_positiveSummary : positiveSummary true = "diagnostic-positive-observed" := rfl

/-- The exact identity relation used by inventory and plan admission. -/
def Supports (observedVersion observedCommit : String) : Prop :=
  observedVersion = version ∧ observedCommit = commit

instance (v h : String) : Decidable (Supports v h) :=
  inferInstanceAs (Decidable (v = version ∧ h = commit))

/-- Executable support decision used at compiler and probe boundaries. -/
def accepts (observedVersion observedCommit : String) : Bool :=
  decide (Supports observedVersion observedCommit)

/-- The executable guard accepts exactly the identity required by admission. -/
theorem accepts_iff (v h : String) : accepts v h = true ↔ Supports v h := by
  simp [accepts]

/-- Matching version strings cannot admit a different compiler commit. -/
theorem refuses_other_commit (v h : String) (different : h ≠ commit) :
    accepts v h = false := by
  simp [accepts, Supports, different]

/-- Any two identities admitted by this source revision are equal in both fields. -/
theorem unique {v₁ h₁ v₂ h₂ : String} (a : Supports v₁ h₁) (b : Supports v₂ h₂) :
    v₁ = v₂ ∧ h₁ = h₂ :=
  ⟨a.1.trans b.1.symm, a.2.trans b.2.symm⟩

/-- The refusal of a compiler this source revision does not support, with the adopter's remedy. -/
def refusal (observedVersion observedCommit : String) : String :=
  s!"unsupported Regula compiler: expected Lean {version} ({commit}), observed Lean \
    {observedVersion} ({observedCommit}). Move the project, and Mathlib if it uses it, to the \
    supported Lean release (its lean-toolchain, then `lake update`), or require a Regula \
    revision qualified for this exact compiler: \
    https://github.com/rbeauchamp/regula/blob/main/docs/guides/adoption.md\
    #when-your-lean-release-has-no-regula-release. For release candidates, nightlies and \
    source-built compilers see \
    https://github.com/rbeauchamp/regula/blob/main/docs/guides/toolchains.md."

/-- Cold Lake configuration and compilation run this guard from this source file.
It needs no package artifacts or dependency resolution. After accepting the compiler that
elaborates it, it prints that compiler's version and commit when `REGULA_COMPILER_GUARD` is `1`:
the cold guard requires them to be those of the Lean running Lake. -/
def checkCurrent : IO Unit := do
  unless accepts Lean.versionString Lean.githash do
    throw <| IO.userError (refusal Lean.versionString Lean.githash)
  if (← IO.getEnv "REGULA_COMPILER_GUARD") == some "1" then
    IO.println Lean.versionString
    IO.println Lean.githash

end RegulaPolicy.Compiler

#eval RegulaPolicy.Compiler.checkCurrent
