import Regula.Checker.ProducerReport
import Lean.Replay
import Regula.Probe

/-!
# Checked logical admission

Checked logical admission before report construction. The replay base contains
only imported modules outside the owned inventory. Unsafe and partial entries
remain subject to generated-role policy; they cannot supply logical evidence.
-/

namespace Regula.Checker.Admission

open Lean

/-- Replay the completed owned logical declarations against trusted imports.
The original environment is retained for compiler metadata only after replay
succeeds. This is not a fresh replay of the imported dependency graph. -/
unsafe def validate (env : Environment) (ownedModules : Array Name) :
    IO (Except ProducerReport.AdmissionFailure ProducerReport.AdmissionReceipt) := do
  let mut replayModules := ownedModules
  -- The force-loaded reporter now depends on the positive policy library.
  -- Replay these exact checker implementation modules too; importing them into
  -- the base would reintroduce unchecked owned policy declarations. They do not
  -- become claimed surfaces, and arbitrary reverse imports remain forbidden.
  let reporterModules := #[`Regula.Probe, `Regula.Report,
    `Regula.Checker.PolicyCodec, `Regula.StructuralName]
  for _ in [:reporterModules.size] do
    for (name, data) in env.header.moduleNames.zip env.header.moduleData do
      if reporterModules.contains name && !replayModules.contains name &&
          data.imports.any (fun imp => replayModules.contains imp.module) then
        replayModules := replayModules.push name
  let owned := replayModules.foldl (fun names name => names.insert name) ({} : NameSet)
  let mut declarations : Std.HashMap Name ConstantInfo := {}
  let own := Regula.Probe.ownedConstants env replayModules.toList
  let mut required := #[]
  for (name, info) in own do
    declarations := declarations.insert name info
    if !info.isUnsafe && !info.isPartial then
      let some idx := env.getModuleIdxFor? name
        | return .error ⟨s!"[VIOLATION[kernel-admission]] missing owner for {name}"⟩
      required := required.push (env.header.modules[(idx : Nat)]!.module, name)
  let mut imports : Array Import := #[]
  for (name, data) in env.header.moduleNames.zip env.header.moduleData do
    if owned.contains name then continue
    -- Importing such a module would put unchecked owned declarations back in
    -- the trusted base. Ownership must be expanded or the claim rejected.
    if data.imports.any (fun imp => owned.contains imp.module) then
      return .error
          ⟨s!"[VIOLATION[kernel-admission]] unowned module {name} imports an owned module"⟩
    imports := imports.push { module := name, importAll := true }
  let base ← importModules imports {} 0 (loadExts := false) (level := .private)
  try
    for (name, _) in declarations do
      if (base.toKernelEnv.find? name).isSome then
        throw <| IO.userError s!"owned declaration {name} already exists in replay base"
    let checked ← Lean.Kernel.Environment.replay declarations base.toKernelEnv
    let mut admitted := #[]
    for key in required do
      let name := key.2
      if (checked.find? name).isNone then
        throw <| IO.userError s!"missing replayed declaration {name}"
      admitted := admitted.push key
    return .ok { modules := RegulaPolicy.canonicalNames replayModules, required, admitted }
  catch error =>
    return .error ⟨s!"[VIOLATION[kernel-admission]] {error}"⟩
  finally
    -- No replay environment escapes this function. Release its separately
    -- imported regions, as Lean's bundled replay checker does.
    base.freeRegions

end Regula.Checker.Admission
