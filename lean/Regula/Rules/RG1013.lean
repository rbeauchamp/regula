module

public import Regula.Rule

public section

namespace Regula.Rules.RG1013

open Regula.Closed

def fixGuidance : Guidance :=
  { text := "add a `module` header (make declarations `public`—for example in a `public section`—and \
      mark bodies `@[expose]` when downstream proofs unfold them, or use `import all` in a downstream \
      proof package under the proof verdict; RG1010 refuses `import all` in the full gate) and ensure \
      imported files are `module` files"
    nonblank := by simp [Char.isWhitespace] }

def check {i : Input} (_ : Tables i) : List Violation :=
  let modFiles := setOf i.moduleFiles
  i.modules.filterMap fun m =>
    if !modFiles.contains m then
      some { subject := .module m, detail := "the file is not a `module` file", guidance := fixGuidance }
    else none

@[expose] def rule : Rule := { spelling := "RG1013", check := check }

end Regula.Rules.RG1013
