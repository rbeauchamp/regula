module

/-!
Mutation: a `native_decide` proof of a public theorem in a `module` file. The proof is
elaborated without exporting, so the generated axiom's prefix is the module-private form of the
theorem's name. It must be reported as compiler-trusting.
-/

public theorem fixtures_module_native_proof : (List.range 101).sum = 5050 := by
  native_decide
