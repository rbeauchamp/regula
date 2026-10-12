/-
Mutation: a project axiom with a generated native-proof name whose prefix names a
declaration of another module, and a statement that native replay confirms. It is authored,
so it is a project axiom here; `ImportedNativeForeignParent` imports it.

-/
import Fixtures.Mutations.NativeProof

axiom fixtures_native_proof._native.native_decide.ax_7 : decide (1 = 1) = true
