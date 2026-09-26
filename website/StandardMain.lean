import VersoManual
import RegulaStandard

/-! Renders the standard alone. Rendering resolves every cross-reference and checklist-row
anchor, so a successful run is the standard's cross-reference check; the published copy is
rendered with the rest of the site by `regula-site`. -/

open Verso.Genre Manual

def main := manualMain (%doc RegulaStandard) (config := {
  emitTeX := false, emitHtmlSingle := .no, emitHtmlMulti := .immediately, htmlDepth := 1 })
