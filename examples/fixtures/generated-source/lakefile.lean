import Lake
open Lake DSL

/-! # Overridden source generator

An external Lake/filesystem refusal control, copied verbatim into the qualification workspace.
The harness supplies its `other-regula` sibling; `Generated.lean` is intentionally absent.
The generator receives its runtime directory through Lake's library argument, not source edits.
-/

package build_lint_adopter where
  leanOptions := #[⟨`linter.missingDocs, true⟩, ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

require checker from "../other-regula"

lean_lib Widget where
  globs := #[.one `Generated]

/-- Create the explicit source if this root prerequisite facet runs. This control exercises
Lake's configuration loader and filesystem boundary, not a universal claim about build order. -/
@[«library_facet»] def generateSource : LibraryFacetDecl :=
  .mk LeanLib.extraDepFacet <| mkFacetJobConfig fun (library : LeanLib) => do
    liftM <| IO.FS.writeFile (library.pkg.dir / "Generated.lean")
      "/-- A generated value. -/\ndef generated : Nat := 0\n"
    pure (Job.nil "generate source")
