module

public meta import Lean.Attributes

/-! Explicit selection of public declarations that state material normative claims.
Registration identifies the RG5002 docstring and RG5003 Intent-section presence obligations.
It does not certify that all material claims have been registered, or that their
documentation or stated intent is adequate. -/

public meta section

namespace Regula

/-- Lean's persistent tag attribute retains selection across normal module imports. -/
initialize materialClaimAttribute : Lean.TagAttribute ←
  Lean.registerTagAttribute `regula_material "Marks a declaration as evidence for a material normative claim."

end Regula
