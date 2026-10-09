/-
Positive control: a definition over `Float`. Lean's axiom table records no axiom for `Float`,
though its constructor's type reaches `propext` and `Quot.sound`, so `collectAxioms` reports none
for this definition either. The audit labels the definition by the axioms it reaches in the
replayed kernel, Choice-Free, and reports what `collectAxioms` omits without failing the claim.
-/
def fixtures_float_double (x : Float) : Float := x + x
