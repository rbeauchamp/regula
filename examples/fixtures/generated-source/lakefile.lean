import Lake
open Lake DSL

/-! # Overridden source generator

An external Lake/filesystem refusal control, copied verbatim into the qualification workspace.
The harness supplies its `other-regula` sibling; the `Generated` directory is intentionally absent.
The generator receives its runtime directory through Lake's library argument, not source edits.
A second control replaces the explicit module with a glob over that directory.
-/

package build_lint_adopter where
  leanOptions := #[⟨`linter.missingDocs, true⟩, ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

require checker from "../other-regula"

lean_lib Widget where
  globs := #[.one `Generated.Value]

/-- Create the generated directory and its source if this root prerequisite facet runs. This
control exercises Lake's configuration loader and filesystem boundary, not a universal claim about
build order. -/
@[«library_facet»] def generateSource : LibraryFacetDecl :=
  .mk LeanLib.extraDepFacet <| mkFacetJobConfig fun (library : LeanLib) => do
    liftM <| IO.FS.createDirAll (library.pkg.dir / "Generated")
    liftM <| IO.FS.writeFile (library.pkg.dir / "Generated" / "Value.lean")
      "/-- A generated value. -/\ndef generated : Nat := 0\n"
    pure (Job.nil "generate source")
