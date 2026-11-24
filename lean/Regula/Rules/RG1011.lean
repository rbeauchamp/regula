module

public import Regula.Rule

public section

namespace Regula.Rules.RG1011

open Regula.Closed

def initialized (d : Decl) : Bool := d.kind == .definition && d.initFn.isSome

def replacement (d : Decl) : String :=
  " and ".intercalate
    ((d.implementedBy.map fun impl => s!"@[implemented_by {impl}]").toList ++
      (if d.isExtern then ["@[extern]"] else []) ++
      (if d.kind == .definition then
        (d.initFn.map fun fn => s!"the initialization function {fn} of @[init] or @[builtin_init]").toList
      else []))

def foreignCSimpGuidance : Guidance :=
  { text := "remove the @[csimp] registration on the foreign theorem, or replace it under the proof \
      verdict with a claimed @[csimp] theorem or one-line claimed alias (@[csimp] public theorem \
      alias : @f = @g := Dep.thm) in a claimed module when the dependency proof is safe and fits \
      the project's profile (RG1010 refuses @[csimp] in the full gate)"
    nonblank := by simp [Char.isWhitespace] }

def implementedByGuidance : Guidance :=
  { text := "remove @[implemented_by] and simplify the definition so compiled code matches the proved \
      definition, or replace it under the proof verdict with a proved claimed @[csimp] theorem \
      (@f = @g) (RG1010 refuses @[csimp] in the full gate)"
    nonblank := by simp [Char.isWhitespace] }

def externGuidance : Guidance :=
  { text := "remove @[extern] and implement the definition in pure Lean so proofs cover compiled code, \
      or isolate foreign bindings outside claimed modules"
    nonblank := by simp [Char.isWhitespace] }

def initDefGuidance : Guidance :=
  { text := "remove @[init]/@[builtin_init] from the def and pass state explicitly, or replace the \
      def under the proof verdict with initialize (which declares an opaque constant with a named \
      initializer; RG1010 refuses initialize in the full gate)"
    nonblank := by simp [Char.isWhitespace] }

def combinedReplacementGuidance : Guidance :=
  { text := "remove @[implemented_by], @[extern], and @[init]/@[builtin_init] from the declaration so \
      compiled code matches the proved definition (or isolate foreign bindings outside claimed \
      modules; under the proof verdict, replace @[implemented_by] with a proved claimed @[csimp] \
      theorem or replace an @[init]/@[builtin_init] def with initialize, which declares an opaque \
      constant with a named initializer; RG1010 refuses @[csimp] and initialize in the full gate)"
    nonblank := by simp [Char.isWhitespace] }

def replacementGuidance (d : Decl) : Guidance :=
  match d.implementedBy.isSome, d.isExtern, initialized d with
  | true, false, false => implementedByGuidance
  | false, true, false => externGuidance
  | false, false, true => initDefGuidance
  | _, _, _ => combinedReplacementGuidance

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

def replaced {i : Input} (t : Tables i) : List Violation :=
  t.claimed.filterMap fun d =>
    if (d.implementedBy.isSome && !t.ctorIdxDef d) || d.isExtern || initialized d then
      some (violation d s!"has {replacement d}, so compiled code runs in place of its definition"
        (replacementGuidance d))
    else none

def check {i : Input} (t : Tables i) : List Violation :=
  let extra := foreignCSimps i
  if extra.isEmpty then replaced t else extra ++ replaced t

@[expose] def rule : Rule := { spelling := "RG1011", check := check }

end Regula.Rules.RG1011
