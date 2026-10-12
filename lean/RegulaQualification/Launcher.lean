import RegulaQualification.Json
import Regula.Decision

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

/-- The environment modifications of one direct launch: a variable set to `some` value, or unset
by `none`. -/
abbrev Launch := Array (String × Option String)

/-- The modifications that give a child of this process exactly the variables `captured`, where
`inherited` names the variables the child would otherwise inherit: every captured variable set,
and every other inherited name unset. A child inherits its parent's environment and then applies
the modifications, so an inherited variable the capture omits, such as one an override or Lake
unset, would otherwise reach the child. -/
def launchEnvironment (captured : Environment) (inherited : Array String) : Launch :=
  captured.map (fun (name, value) => (name, some value)) ++
    (inherited.filter fun name => !captured.any (·.1 == name)).map (·, none)

/-- The variables a launch sets are exactly the captured mapping, in its order. -/
theorem launchEnvironment_set (captured : Environment) (inherited : Array String) :
    (launchEnvironment captured inherited).filterMap
        (fun (name, value) => value.map (name, ·)) = captured := by
  apply Array.ext'
  simp [launchEnvironment, List.filterMap_map, Function.comp_def]

/-- A launch unsets a name exactly when the child would inherit it and the capture omits it. -/
theorem launchEnvironment_unset_iff (captured : Environment) (inherited : Array String)
    (name : String) :
    (name, none) ∈ launchEnvironment captured inherited ↔
      name ∈ inherited ∧ captured.any (·.1 == name) = false := by
  simp [launchEnvironment]

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
  /-- The environment modifications the launch used (`launchEnvironment`), whose set variables
  are the captured environment (`launchEnvironment_set`). -/
  environment : Launch
  /-- The resolved path of the `lean` executable, which the direct launch uses. -/
  executable : String
  deriving BEq, DecidableEq

/-- Exact full-sequence comparison also preserves order, multiplicity and all 42
controls. Equality includes the environment and resolved compiler path. -/
@[regula_decision]
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
