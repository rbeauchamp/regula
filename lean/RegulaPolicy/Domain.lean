module

public import RegulaPolicy.Compiler
public import Regula.Contract
public import Lean.Expr
public import Regula.Decision

/-! # Policy vocabulary

The closed vocabulary that the manifest reader and the effect check of a program read: a surface's
execution mode (`ExecutionClaim`) and the roots of the toolchain's own modules (`ToolchainRoot`). The module also
registers the compiler support decision (`Compiler.accepts`), whose own module imports nothing
beyond `Init`, since the compiler guard of `lakefile.lean` elaborates it before any artifact of the
package exists. `Regula.Decision` is imported for the type `RegisteredDecision`. -/

@[expose] public section

namespace RegulaPolicy

/-- The execution mode that a surface of the manifest claims, which the loader gives the checker as
`Regula.Closed.Execution`; parsing cannot manufacture an unknown constructor. -/
inductive ExecutionClaim where
  /-- Execution boundaries are not checked. -/
  | «report»
  /-- Each reachable execution boundary needs an admitted correspondence (RG3002). -/
  | «checked»
  deriving Repr, DecidableEq

/-- The claim's text in manifests and reports (`report` or `checked`); `parse?` reads it back
(`ExecutionClaim.roundtrip`). -/
def ExecutionClaim.spelling : ExecutionClaim → String
  | .«report» => "report"
  | .«checked» => "checked"

/-- The claim a text names; `none` for any text that is not a `spelling`
(`ExecutionClaim.canonical`). -/
def ExecutionClaim.parse? : String → Option ExecutionClaim
  | "report" => some .«report»
  | "checked" => some .«checked»
  | _ => none

theorem ExecutionClaim.parse?_registered : Regula.RegisteredDecision @ExecutionClaim.parse? := ⟨⟩

/-- Every value survives its actual spelling parser. -/
@[simp] theorem ExecutionClaim.roundtrip (x : ExecutionClaim) : parse? x.spelling = some x := by
  cases x <;> rfl

/-- The parser accepts only the canonical spelling of its result. -/
theorem ExecutionClaim.canonical (s : String) (x : ExecutionClaim) (h : parse? s = some x) :
    x.spelling = s := by
  unfold parse? at h
  split at h <;> cases h <;> rfl

/-- The roots of the library packages the Lean toolchain ships as its own code: `Init`, `Std`,
`Lean`, `Lake` and `LeanExport`. The effect check of a program (`Regula.Effects.check`) reads the
name alone, under the hypothesis that the workspace gives no module under these roots, which is
assumed, not checked.

Assumes: the Lean 4.35.0 release installs the compiled modules of these five packages in its
library directory `lib/lean`, beside only the root modules of its executables (`LakeMain`,
`LeanChecker`, `LeanIR` and `Leanc`), as a listing of that directory shows (Lake's sources are
`src/lake/Lake` of the release), so a module whose loaded `.olean` is its own file there is the
toolchain's. Lean 4.35.0 adds `LeanExport`, whose modules Lake's own modules import
(`src/lake/Lake/CLI/Main.lean:29`, `src/lake/Lake/Check/Axioms.lean:9`). -/
def ToolchainRoot (root : Lean.Name) : Prop :=
  root = `Init ∨ root = `Std ∨ root = `Lean ∨ root = `Lake ∨ root = `LeanExport

instance : DecidablePred ToolchainRoot := fun _ => by unfold ToolchainRoot; infer_instance

/-- `ExecutionClaim.parse?` accepts exactly the spellings. -/
theorem ExecutionClaim.checked_parse : Regula.ExecutableContract ExecutionClaim.parse?
    (Regula.Decides (·.isSome = true) fun text => ∃ x : ExecutionClaim, text = x.spelling) :=
  ⟨.of_roundtrip roundtrip canonical .«report» (unwritten := "") rfl⟩

/-- `Compiler.accepts`, the support decision of `regula doctor`, accepts
exactly the version and commit this revision declares (`Compiler.accepts_iff`): it accepts that
pair and refuses the empty pair. That the pair is the running compiler's is the caller's
observation. -/
theorem checked_compilerAccepts : Regula.ExecutableContract Compiler.accepts (fun accepts =>
    Regula.Decides (· = true)
      (fun input : String × String => Compiler.Supports input.1 input.2)
      (Function.uncurry accepts)) :=
  ⟨.of_iff (fun input => Compiler.accepts_iff input.1 input.2)
    ⟨(Compiler.version, Compiler.commit),
      (Compiler.accepts_iff Compiler.version Compiler.commit).mpr ⟨rfl, rfl⟩⟩
    ⟨("", ""), fun accepted =>
      absurd ((Compiler.accepts_iff "" "").mp accepted).1 (by decide)⟩⟩

theorem Compiler.accepts_registered : Regula.RegisteredDecision @Compiler.accepts := ⟨⟩

end RegulaPolicy
