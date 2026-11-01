/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Effects

/-!
# Filesystem meaning of a successful copy

A filesystem view may give two different path keys the same file's contents. No injectivity of paths is assumed.
The primitive laws below concern Lean's exclusive open, handle write, flush and read, not Regula's writer.
-/

namespace RegulaSpecification.Effects

open System (FilePath)
open Regula.Effect

/-- The state token of Lean's IO definitions. -/
abbrev World := Void IO.RealWorld

/-- The filesystem view of the copied input paths, indexed by components; aliases may have equal observations.
Unrelated files need not be represented, so changes to the source project or Lake's outputs impose no preservation law. -/
abbrev Contents := List String → Option String

/-- Every text already present remains present with the same contents. -/
def Preserves (before after : Contents) : Prop :=
  ∀ q text, before q = some text → after q = some text

/-- The requested text is present and every earlier file's contents are preserved. -/
def Installed (path : FilePath) (text : String) (before after : Contents) : Prop :=
  after (parts path) = some text ∧ Preserves before after

/-- Laws of Lean's filesystem primitives on the private tree, in the absence of another writer. Exclusive creation
cannot replace an existing file, including through an alias. A successful write and flush to that fresh handle installs
the string. A failed exclusive open preserves existing contents; a successful read returns the contents and preserves them.
These are primitive interface assumptions, not assumptions about Regula's decisions. -/
structure FilePrimitives (contents : World → Contents) (paths : FilePath → Prop) : Prop where
  /-- Opening a new file, writing its fresh handle and flushing installs the text without replacing any old file. -/
  fresh : ∀ path text w h w₁ w₂ w₃, paths path →
    IO.FS.Handle.mk path .writeNew w = .ok h w₁ →
    h.putStr text w₁ = .ok () w₂ → h.flush w₂ = .ok () w₃ →
    Installed path text (contents w) (contents w₃)
  /-- Failed exclusive creation never truncates an existing file. -/
  failedOpen : ∀ path w error w', paths path →
    IO.FS.Handle.mk path .writeNew w = .error error w' → Preserves (contents w) (contents w')
  /-- A successful read reports the file's text and preserves existing contents. -/
  read : ∀ path w text w', paths path → IO.FS.readFile path w = .ok text w' →
    Installed path text (contents w) (contents w')

/-- The actual table answers every event at the world left by the preceding event. -/
inductive Execution {L E : Type} (table : (o : Op L E) → BaseIO (Resp o)) :
    World → List (Event L E) → World → Prop where
  /-- An empty segment leaves the world unchanged. -/
  | nil (w) : Execution table w [] w
  /-- One table answer, followed by the remaining execution. -/
  | step {w w₁ w₂ o r rest} : table o w = ⟨r, w₁⟩ → Execution table w₁ rest w₂ →
      Execution table w (⟨o, r⟩ :: rest) w₂

end RegulaSpecification.Effects
