module

public import Init

/-! # Exact compiler support

Each source revision of Regula names one compiler identity. Version strings alone do not
identify development builds. The compiler's reported identity and the integrity of its
executable remain trusted observations; these contracts compare the supplied strings. -/

@[expose] public section

namespace RegulaPolicy.Compiler

/-- The one compiler release supported by this source revision. -/
def version : String := "4.35.0"

/-- The full compiler commit declared by this source revision. -/
def commit : String := "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"

/-- The exact identity relation that the guard below and `regula doctor` decide. -/
def Supports (observedVersion observedCommit : String) : Prop :=
  observedVersion = version ∧ observedCommit = commit

instance (v h : String) : Decidable (Supports v h) :=
  inferInstanceAs (Decidable (v = version ∧ h = commit))

/-- The support decision of the compiler guard (`checkCurrent`) and `regula doctor`. -/
def accepts (observedVersion observedCommit : String) : Bool :=
  decide (Supports observedVersion observedCommit)

/-- The decision accepts exactly the identity this source revision supports. -/
theorem accepts_iff (v h : String) : accepts v h = true ↔ Supports v h := by
  simp [accepts]

/-- Matching version strings cannot admit a different compiler commit. -/
theorem refuses_other_commit (v h : String) (different : h ≠ commit) :
    accepts v h = false := by
  simp [accepts, Supports, different]

/-- Any two identities this source revision supports are equal in both fields. -/
theorem unique {v₁ h₁ v₂ h₂ : String} (a : Supports v₁ h₁) (b : Supports v₂ h₂) :
    v₁ = v₂ ∧ h₁ = h₂ :=
  ⟨a.1.trans b.1.symm, a.2.trans b.2.symm⟩

/-- The refusal of a compiler this source revision does not support, with the adopter's remedy. -/
def refusal (observedVersion observedCommit : String) : String :=
  s!"unsupported Regula compiler: expected Lean {version} ({commit}), observed Lean \
    {observedVersion} ({observedCommit}). Move the project, and Mathlib if it uses it, to \
    the supported Lean release (its lean-toolchain, then `lake update`). Other compilers require \
    a separately reviewed port; see \
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
