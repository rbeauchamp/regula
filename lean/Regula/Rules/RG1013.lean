module

public import Regula.Rule

/-!
# RG1013: files that are not `module` files

The file of a claimed module is not a `module` file. `specification/RegulaSpecification/Rules/RG1013.lean` states
the rule and proves this check against it. Its subject is a module and no constant, so a finding of it names the
module alone.
-/

public section

namespace Regula.Rules.RG1013

open Regula.Closed

/-- Fix guidance for RG1013 findings. -/
def fixGuidance : Guidance :=
  { text := "add a `module` header (use `public section` / `@[expose]` for bodies downstream proofs \
      unfold, or `import all` in a downstream proof package under the proof verdict; RG1010 refuses \
      `import all` in the full gate) and ensure imported files are `module` files"
    nonblank := by simp [Char.isWhitespace] }

/-- The claimed modules that are not among the loaded modules that are `module` files. -/
def check {i : Input} (_ : Tables i) : List Violation :=
  let modFiles := setOf i.moduleFiles
  i.modules.filterMap fun m =>
    if !modFiles.contains m then
      some { subject := .module m, detail := "the file is not a `module` file", guidance := fixGuidance }
    else none

/-- RG1013, for the registry. Its body is exposed so that the registry reads its spelling (`Regula.Closed.spellings_nodup`). -/
@[expose] def rule : Rule := { spelling := "RG1013", check := check }

end Regula.Rules.RG1013
