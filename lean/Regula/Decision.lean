/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

/-! # Decision registration

Explicit selection of the functions a project declares to be decisions: a parser, decoder, validator
or admission function whose result accepts or refuses its input. This module is a library and gives
no verdict: no check of Regula reads a registration.

A registration is a declaration of the type `RegisteredDecision`, in a module that imports the
function:

```

theorem positive_registered : Regula.RegisteredDecision @positive := ⟨⟩
```

A file that is a `module` imports this one with `public import`, because the statement of a public
registration names `RegisteredDecision`. -/

public section

universe u

namespace Regula

/-- A declaration of this type registers `f` as a decision function. The type has one inhabitant and
states nothing about `f`: the registration is the declaration's existence. -/
structure RegisteredDecision {α : Sort u} (f : α) : Prop where
  /-- Registers `f`. -/
  mk ::

end Regula
