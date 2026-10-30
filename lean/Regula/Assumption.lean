module

public import RegulaPolicy.External
public import RegulaPolicy.Compiler

/-! # Assumptions about external systems

An assumption is a predicate over a model of a system outside Lean's logic, which the theorems that
rest on the property take as a hypothesis (`RegulaPolicy.External`). A declaration of the type
`Assumed p` records which system the predicate `p` is about and where the fact is stated:

```
def ReadsBytes_assumed : Regula.Assumption.Assumed ReadsBytes where
  system := .filesystem
  sources := [.lean "v4.35.0" "Init/System/IO.lean#L1211-L1221",
    .trusted "reading bytes preserves the modeled filesystem state"]
  stated := rfl
  pinned := by decide +kernel
```

A source is a file below `src` of the Lean 4 repository at a release tag, a document about a
system, or a reason that the fact is trusted. A `lean` source must be pinned to the release that
Regula supports, `v` and `RegulaPolicy.Compiler.version`: after a toolchain upgrade, each assumption
whose source was read at the earlier release fails to elaborate until its source is read again at
the new one (`RegulaPolicy.External.Source.stale`). A document about Lean or Lake, or one whose
reference names a place of the Lean 4 repository or of Lean's documentation, is refused
(`RegulaPolicy.External.Source.unpinned`), so a fact about Lean or Lake carries its release.

The declaration is an ordinary constant, so it adds no code that Lean runs while it elaborates, and
RG2007 admits it in a claimed module. Each declaration proves its two checks itself: a default of
the form `:= by tactic` is a `meta` declaration of the module that states it, which RG2007 refuses. It records what is written and decides nothing else. -/

public section

universe u

namespace Regula.Assumption

open RegulaPolicy.External

/-- The release tag that a `lean` source must name: `v` and the release Regula supports. -/
def currentTag : String := "v" ++ RegulaPolicy.Compiler.version

/-- A declaration of this type records the system that the assumption `p` is about, and the sources
that state it. At least one source is required, and each is pinned to the supported release. -/
structure Assumed {α : Sort u} (p : α) where
  /-- The system the assumption is about. -/
  system : System
  /-- The sources that state the fact. -/
  sources : List Source
  /-- At least one source states the fact. -/
  stated : sources.isEmpty = false
  /-- No `lean` source is stale, and no document escapes the pin. -/
  pinned : sources.all (fun s => !s.stale currentTag && !s.unpinned) = true

end Regula.Assumption
