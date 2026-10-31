/-! A configured module deliberately absent from the umbrella's imports.
Lake and the checker find it through the library's glob. -/

namespace Widget.Additional

/-- A separate closed, kernel-only claim included in the library surface. -/
theorem reflexive (n : Nat) : n = n := rfl

end Widget.Additional
