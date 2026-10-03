module

public import Lean.Attributes

/-! # Decision registration

Explicit selection of the functions a project declares to be decisions: a parser, decoder,
validator or admission function whose result accepts or refuses its input.
Registration identifies the RG1008 obligation: the function is the implementation of a decision
contract of its inventory (an `ExecutableContract` whose requirement is a `Regula.DecidesSoundly`,
`Regula.DecidesCompletely` or `Regula.Decides`), or its result type is `Decidable _`.
A registration adds that requirement and waives nothing. It does not certify that every function
that acts as a checker is registered, or that a registered contract's specification is the
intended one.

A file that is not a `module` imports this module with `import Regula.Decision`. A `module`
imports it with `meta import Regula.Decision`: the attribute is needed only while the file is
elaborated, and under that import Lean refuses a definition of the file that would run this
module's imports. The attribute is an ordinary definition, not a `meta` one, so the collector
reads the registration with it (`Regula.Collect.declaration`). -/

public section

namespace Regula

/-- Lean's persistent tag attribute retains selection across normal module imports, and applies
only in the module that declares the function, so the registration is present wherever the
function is. -/
initialize decisionAttribute : Lean.TagAttribute ←
  Lean.registerTagAttribute `regula_decision
      "Marks a function as a decision that must state which direction it proves."

end Regula
