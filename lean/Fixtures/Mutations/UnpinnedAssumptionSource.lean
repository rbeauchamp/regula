/-
Intended failure: two assumptions that cite a document about Lean without its release. The first
cites a file of the Lean 4 repository by its URL, as a document about the filesystem; the second
names Lean as the system its document is about. `@[regula_assumption]` refuses each where it is
written (`RegulaPolicy.External.Source.unpinned`), so a fact about Lean or Lake is cited with a
`lean` source, which carries its release.
-/
import Regula.Assumption

namespace Fixtures.UnpinnedAssumptionSource

@[regula_assumption filesystem (document filesystem
  "https://github.com/leanprover/lean4/blob/v4.33.0/src/Init/System/IO.lean#L1330-L1342")]
def RemovesByUrl : Prop := True

@[regula_assumption filesystem (document lean "Lean's reference for IO.FS.removeDirAll")]
def RemovesByLean : Prop := True

end Fixtures.UnpinnedAssumptionSource
