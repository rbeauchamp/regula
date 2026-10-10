/-
Mutation: an unsafe constructor-index helper spelled `T.ctorIdx._impl` and installed as the
runtime implementation of Lean's generated `T.ctorIdx`, the shape a compiler that generates such
helpers produces. No constructor-index helper is a generated role (the exception was removed
until a port to such a compiler), so the helper is an escape hatch whatever its name and link.
-/
inductive FixturesCtorForge where
  | left
  | right

unsafe def FixturesCtorForge.ctorIdx._impl : FixturesCtorForge → Nat
  | .left => 0
  | .right => 1

attribute [implemented_by FixturesCtorForge.ctorIdx._impl] FixturesCtorForge.ctorIdx
