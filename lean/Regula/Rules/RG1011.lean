module

public import Regula.Rule

/-!
# RG1011: replaced compiled code

A constant of a claimed module has `@[implemented_by]` or `@[extern]`, or is a definition for which
`@[init]` or `@[builtin_init]` names an initialization function, so a compiled program runs other code
in its place than the definition that its proofs are about; or a claimed module has an exported
(`global` or `scoped`) `@[csimp]` entry whose theorem is not declared in any claimed module's
`.olean` data, so that theorem can escape the claim's kernel replay cone and axiom/safety checks.
The loader reads the first three with `Lean.Compiler.getImplementedBy?`, `Lean.isExtern` and
`Lean.getInitFnNameFor?`, the queries by which Lean's compiler decides what it compiles for a constant
(`shouldGenerateCode`, `Lean/Compiler/LCNF/Main.lean:34` and `:40`, and `toDecl`,
`Lean/Compiler/LCNF/ToDecl.lean:72`, at v4.35.0), and reads claimed modules' exported `@[csimp]` entries
with `Lean.Compiler.CSimp.ext.ext.getModuleEntries` (`Lean/Compiler/CSimpAttr.lean:18-38`,
`Lean/ScopedEnvExtension.lean:17-19,96-112`, `Lean/Environment.lean:1672-1678,2377` at v4.35.0).
`specification/RegulaSpecification/Rules/RG1011.lean` states the rule and proves this check against it.
-/

public section

namespace Regula.Rules.RG1011

open Regula.Closed

/-- Whether `d` is a definition for which `@[init]` or `@[builtin_init]` names an initialization
function. An opaque constant with one, which `initialize` declares, is not read: Lean's logic states
nothing of its value. -/
def initialized (d : Decl) : Bool := d.kind == .definition && d.initFn.isSome

/-- What runs in place of the definition of `d`, when its check reports it. -/
def replacement (d : Decl) : String :=
  " and ".intercalate
    ((d.implementedBy.map fun impl => s!"@[implemented_by {impl}]").toList ++
      (if d.isExtern then ["@[extern]"] else []) ++
      (if d.kind == .definition then
        (d.initFn.map fun fn => s!"the initialization function {fn} of @[init] or @[builtin_init]").toList
      else []))

/-- Fix guidance for an exported claimed-module `@[csimp]` entry targeting a foreign theorem. -/
def foreignCSimpGuidance : Guidance :=
  { text := "remove @[csimp] on the foreign theorem, or under the proof verdict define a claimed \
      @[csimp] theorem or one-line claimed alias (@[csimp] public theorem alias : @f = @g := Dep.thm) \
      in a claimed module (RG1010 refuses @[csimp] in the full gate)"
    nonblank := by simp [Char.isWhitespace] }

/-- Fix guidance for `@[implemented_by]`. -/
def implementedByGuidance : Guidance :=
  { text := "remove @[implemented_by] and simplify the definition so compiled code matches the proved \
      definition, or under the proof verdict use a proved claimed @[csimp] theorem (@f = @g) (RG1010 \
      refuses @[csimp] in the full gate)"
    nonblank := by simp [Char.isWhitespace] }

/-- Fix guidance for `@[extern]`. -/
def externGuidance : Guidance :=
  { text := "remove @[extern] and implement the definition in pure Lean so proofs cover compiled code, \
      or isolate foreign bindings outside claimed modules"
    nonblank := by simp [Char.isWhitespace] }

/-- Fix guidance for `@[init]`/`@[builtin_init]` naming an initialization function on a `def`. -/
def initDefGuidance : Guidance :=
  { text := "remove @[init]/@[builtin_init] from the def (pass state explicitly, or under the proof \
      verdict declare runtime-initialized state with initialize/opaque; RG1010 refuses initialize and \
      opaque in the full gate)"
    nonblank := by simp [Char.isWhitespace] }

/-- Fix guidance when a declaration combines multiple replacement attributes. -/
def combinedReplacementGuidance : Guidance :=
  { text := "remove @[implemented_by], @[extern], and @[init]/@[builtin_init] from the declaration so \
      compiled code matches the proved definition (under the proof verdict, use a proved claimed \
      @[csimp] theorem for optimizations or initialize/opaque for runtime state; RG1010 refuses both \
      in the full gate)"
    nonblank := by simp [Char.isWhitespace] }

/-- Fix guidance for a replaced declaration `d`, tailored to which replacement attributes are present. -/
def replacementGuidance (d : Decl) : Guidance :=
  match d.implementedBy.isSome, d.isExtern, initialized d with
  | true, false, false => implementedByGuidance
  | false, true, false => externGuidance
  | false, false, true => initDefGuidance
  | _, _, _ => combinedReplacementGuidance

/-- The exported (`global` or `scoped`) `@[csimp]` entries of claimed modules whose theorem is not
declared in any claimed module's `.olean` data. With no entry it builds no hash set, and with entries
its two sets hold the claimed modules and each owned entry target (`Input.claimedConstants`). -/
def foreignCSimps (i : Input) : List Violation :=
  if i.csimps.isEmpty then []
  else
    let claimedMods := setOf i.modules
    let claimedConsts := setOf i.claimedConstants
    i.csimps.filterMap fun e =>
      if claimedMods.contains e.module && !claimedConsts.contains e.thm then
        some { subject := .constant e.thm e.module,
               detail := "registered as @[csimp] in this module, but not declared in any claimed module",
               guidance := foreignCSimpGuidance }
      else none

/-- The constants of claimed modules that have `@[implemented_by]` or `@[extern]`, and the definitions
of claimed modules that have an initialization function. -/
def replaced {i : Input} (t : Tables i) : List Violation :=
  t.claimed.filterMap fun d =>
    if d.implementedBy.isSome || d.isExtern || initialized d then
      some (violation d s!"has {replacement d}, so compiled code runs in place of its definition"
        (replacementGuidance d))
    else none

/-- The exported `@[csimp]` entries of claimed modules whose theorem is not declared in any claimed
module, together with what `replaced` reports. Returns `replaced t` directly without traversing it
when no foreign `@[csimp]` entry is reported, and prepends `extra` otherwise. -/
def check {i : Input} (t : Tables i) : List Violation :=
  let extra := foreignCSimps i
  if extra.isEmpty then replaced t else extra ++ replaced t

/-- RG1011, for the registry. Its body is exposed so that the registry reads its spelling (`Regula.Closed.spellings_nodup`). -/
@[expose] def rule : Rule := { spelling := "RG1011", check := check }

end Regula.Rules.RG1011
