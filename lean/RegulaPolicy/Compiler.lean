module

public import Init

/-! # Exact compiler support

Each checker source revision names one compiler identity. Version strings alone do not
identify development builds. The compiler's reported identity and the integrity of its
executable remain trusted observations; these contracts compare the supplied strings. -/

@[expose] public section

namespace RegulaPolicy.Compiler

/-- The compiler version declared by this source revision. Publication requires qualification. -/
def version : String := "4.34.0"

/-- The full compiler commit declared by this source revision. -/
def commit : String := "293d5d0c0c3f3dded4688b3ccd6a33939ac5102b"

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

/-- Cold Lake configuration and compilation run this guard from this source file.
It needs no package artifacts or dependency resolution. -/
def checkCurrent : IO Unit := do
  unless accepts Lean.versionString Lean.githash do
    throw <| IO.userError s!"unsupported Regula compiler: expected Lean {version} ({commit}), \
      observed Lean {Lean.versionString} ({Lean.githash}). Select a Regula revision qualified \
      for this exact compiler; see docs/guides/toolchains.md."

end RegulaPolicy.Compiler

#eval RegulaPolicy.Compiler.checkCurrent
