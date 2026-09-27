import Regula.Checker.Snapshot
import Regula.Checker.Lake
import Regula.Qualification.Slot
import Regula.Qualification.Support

/-! # Producer slot preparation qualification

Preparation-only qualification (harness): the full normal
copy/authentication/preparation path for the shared producer slot on fresh
owned scratch, with per-phase wall timings. No detector, no corpus and no
shared writes (callers run this with `GIT_OPTIONAL_LOCKS=0`). Scratch cleanup
is verified after the owned scratch is removed. This exercises exactly the
preparation work the corpus campaign performs before its producer pool. -/
namespace Regula.Qualification.Preparation
open Lean System

/-- Prepares one shared producer slot and a `rule_examples` slot project in owned scratch,
printing the wall time of each phase: surface inventory, dependency capture, input capture,
slot and project preparation. Throws unless the scratch directory is gone afterwards; prints
`preparation measure: PASS` on success. -/
def check : IO Unit := do
  let root ← Regula.Qualification.rootDirectory
  let scratchRef ← IO.mkRef (none : Option FilePath)
  try
    Regula.Qualification.withScratch root "prep-measure" fun scratch => do
      scratchRef.set (some scratch)
      let inventoryStart ← IO.monoMsNow
      let inventory ← Regula.Checker.Lake.surfaceInventory root
      IO.println s!"prep phase: surfaceInventory: {(← IO.monoMsNow) - inventoryStart}ms"
      let modulePaths := inventory.moduleSources.map Prod.snd
      let captureStart ← IO.monoMsNow
      let deps ← Regula.Checker.Snapshot.dependencies inventory
      IO.println s!"prep phase: dependency captures: {(← IO.monoMsNow) - captureStart}ms"
      let configNames ← (#[ "lean-toolchain", "lakefile.lean", "lake-manifest.json",
        "foundation_manifest.json"] : Array String).filterM
          (fun (name : String) => (root / name).pathExists)
      let rootConfigs ← configNames.mapM (fun (name : String) => do
        pure (root / name, ← IO.FS.readBinFile (root / name)))
      let rootSources ← modulePaths.mapM (fun path => do
        pure (path, ← IO.FS.readBinFile path))
      IO.println s!"prep phase: input capture: root sources={rootSources.size} configs={rootConfigs.size} deps={deps.size}"
      let totalStart ← IO.monoMsNow
      let slot : Slot.ProducerSlot := ⟨scratch / "slot"⟩
      IO.FS.createDirAll slot.root
      let _ ← Slot.prepareSlot root slot rootSources rootConfigs deps
      let projectStart ← IO.monoMsNow
      IO.FS.createDirAll (scratch / "project")
      Slot.prepareSlotProject slot (scratch / "project")
        "rule_examples" "kernel-only" "The fixture's exact mathematical claim and scope."
      IO.println s!"prep phase: prepareSlotProject: {(← IO.monoMsNow) - projectStart}ms"
      IO.println s!"prep phase: TOTAL preparation (shared slot): {(← IO.monoMsNow) - totalStart}ms"
  finally
    match ← scratchRef.get with
    | some scratch =>
      if ← scratch.pathExists then
        throw <| IO.userError s!"preparation cleanup failed: {scratch} still exists"
      else
        IO.println "prep phase: cleanup verified (scratch removed)"
    | none => throw <| IO.userError "preparation scratch never captured"
  IO.println "preparation measure: PASS"

end Regula.Qualification.Preparation
