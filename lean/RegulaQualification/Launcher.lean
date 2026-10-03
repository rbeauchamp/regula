import RegulaQualification.Json

/-! # Launcher capture admission

Pure capture admission and paired-launcher equivalence. Environment values stay
in memory, never in the exported diagnostic. No theorem authenticates OS environment
capture or establishes that a future run will be faster. -/
namespace RegulaQualification.Launcher
open Lean

/-- Exactly the captured name/value mapping required for direct compiler launches. -/
abbrev Environment := Array (String × String)

/-- A capture has unique nonempty names and both required search paths. -/
def Valid (env : Environment) : Prop :=
  (env.toList.map Prod.fst).Nodup ∧ (env.toList.all (fun p => !p.1.isEmpty)) = true ∧
    (env.any (fun p => p.1 == "PATH")) = true ∧ (env.any (fun p => p.1 == "LEAN_PATH")) = true
instance (env : Environment) : Decidable (Valid env) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Parse NUL-delimited OS capture; '=' is split only at its first occurrence. -/
def decode (raw : String) : Except String Environment := do
  unless raw.endsWith "\x00" do throw "unterminated environment capture"
  let entries := (raw.dropEnd 1).toString.splitOn "\x00"
  let env ← entries.toArray.mapM fun entry => do
    let parts := entry.splitOn "="
    let name :: value :: rest := parts | throw "invalid environment entry"
    return (name, String.intercalate "=" (value :: rest))
  return env

/-- The operational caller cannot obtain an admitted mapping without its invariant. -/
def admit (raw : String) : Except String {env : Environment // Valid env} := do
  let env ← decode raw
  if h : Valid env then return ⟨env, h⟩ else throw "invalid or incomplete environment capture"

/-- Every admitted environment has exactly the invariant consumed by the launcher. -/
theorem admit_sound (raw : String) (env : {e : Environment // Valid e})
    (_ : admit raw = .ok env) : Valid env.val := env.property

/-- Every successfully decoded valid mapping is admitted, not only a selected subset. -/
theorem admit_complete (raw : String) (env : Environment) (h : decode raw = .ok env)
    (valid : Valid env) : admit raw = .ok ⟨env, valid⟩ := by
  simp only [admit, h]
  change (if h : Valid env then Except.ok (⟨env, h⟩ : {e : Environment // Valid e})
    else Except.error "invalid or incomplete environment capture") = _
  simp [valid]

/-- Full in-memory identity of one real compiler control, excluding measured duration. -/
structure Observation where
  /-- The control's name: the stem of the compiled source file's path. -/
  label : String
  /-- The compiler's arguments, the source path last. -/
  args : Array String
  /-- The text of the compiled source file. -/
  source : String
  /-- The compiler's exit code. -/
  exitCode : Nat
  /-- The compiler's standard output. -/
  stdout : String
  /-- The compiler's standard error. -/
  stderr : String
  /-- The captured environment, which the direct launch uses. -/
  environment : Environment
  /-- The resolved path of the `lean` executable, which the direct launch uses. -/
  executable : String
  deriving BEq, DecidableEq

/-- Exact full-sequence comparison also preserves order, multiplicity and all 42
controls. Equality includes the environment and resolved compiler path. -/
def equivalent (before after : Array Observation) : Bool :=
  decide (before.size = 42 ∧ before = after)

/-- The paired diagnostic consumes this proof-linked predicate; timing is separate. It is a
two-way decision that refuses two empty sequences; the accepted witness is forty-two copies of
one observation, compared with themselves. -/
theorem checked_equivalence : Regula.ExecutableContract equivalent (fun run =>
    Regula.Decides (· = true)
      (fun input : Array Observation × Array Observation =>
        input.1.size = 42 ∧ input.1 = input.2)
      (Function.uncurry run)) :=
  let observations : Array Observation := Array.replicate 42 ⟨"", #[], "", 0, "", "", #[], ""⟩
  ⟨.of_iff (fun input => by simp [Function.uncurry, equivalent])
    ⟨(observations, observations), by simp [Function.uncurry, equivalent, observations]⟩
    ⟨(#[], #[]), by simp [Function.uncurry, equivalent]⟩⟩
end RegulaQualification.Launcher
