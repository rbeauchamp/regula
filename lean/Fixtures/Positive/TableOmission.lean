/-
Positive control: the identity on `Float`. Lean's axiom table records no axiom for `Float`,
though its constructor's type reaches `propext` and `Quot.sound`, so `collectAxioms` reports none
for this definition either. The audit labels the definition by the axioms it reaches in the
replayed kernel, Choice-Free, and reports what `collectAxioms` omits without failing the claim.
-/
def fixtures_float_id (x : Float) : Float := x
