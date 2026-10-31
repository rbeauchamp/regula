module

/-! # Decision registration

Explicit selection of the functions a project declares to be decisions: a parser, decoder,
validator or admission function whose result accepts or refuses its input.
Registration identifies the RG1008 obligation: the function is the implementation of a decision
contract of a claimed module (an `ExecutableContract` whose requirement is a
`Regula.DecidesSoundly`, `Regula.DecidesCompletely` or `Regula.Decides`), or its result type is
`Decidable _`. A registration adds that requirement and waives nothing. It does not certify that
every function that acts as a checker is registered, or that a registered contract's specification
is the intended one.

A registration is a declaration of the type `RegisteredDecision`, in a module that imports the
function:

```

theorem positive_registered : Regula.RegisteredDecision @positive := ⟨⟩
```

It is an ordinary constant, so it adds no code that Lean runs while it elaborates, and RG2007 admits
it in a claimed module. The checker reads the type of each constant of a claimed module
(`Regula.Load.registrationOf`), and decides the RG1008 requirement only for a registered function
of a claimed module (`Regula.Closed.Tables.rg1008`); it reports nothing for a registration
of another function. A file that is a `module` imports this one with `public import`, because the
statement of a public registration names `RegisteredDecision`. -/

public section

universe u

namespace Regula

/-- A declaration of this type registers `f` as a decision function (RG1008). The type has one
inhabitant and states nothing about `f`: the registration is the declaration's existence, which the
checker reads from its type. -/
structure RegisteredDecision {α : Sort u} (f : α) : Prop where
  /-- Registers `f`. -/
  mk ::

end Regula
