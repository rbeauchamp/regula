module

public meta import Lean.Attributes

/-! # Material claim registration

Explicit selection of public declarations that state material normative claims.
Registration selects the declarations to which the written guidance of the retired rules RG5002
and RG5003 applies: a docstring with a nonempty Intent section (standard §5.1 and §5.2). No check
reads the registration; review does.
It does not certify that all material claims have been registered, or that their
documentation or stated intent is adequate. -/

public meta section

namespace Regula

/-- Lean's persistent tag attribute retains selection across normal module imports. -/
initialize materialClaimAttribute : Lean.TagAttribute ←
  Lean.registerTagAttribute `regula_material
      "Marks a declaration as evidence for a material normative claim."

end Regula
