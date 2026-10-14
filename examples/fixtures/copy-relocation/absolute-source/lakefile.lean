import Lake
open Lake DSL

/-! A project of the `qualify copy-relocation` control whose library `AbsoluteSource` sets its
source directory to the package's `src` directory as an absolute path. Lake joins that path as it
stands, so a copy would still read the original's sources, and must refuse that setting by name. -/

package absolute_source

lean_lib AbsoluteSource where
  srcDir := __dir__ / "src"
