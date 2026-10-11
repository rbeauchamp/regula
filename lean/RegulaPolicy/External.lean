module

public import Regula.Contract
meta import Regula.Decision

/-! # External systems, their assumptions and their observers

Regula's code observes and acts on systems outside Lean's logic: the filesystem, processes, the
process environment, Lake, Lean's elaborator and compiler, the operating system's file locks and
Git. A theorem about a decision holds for the values the decision is given. That an observation
reports the system truthfully, or that an action changes only what it should, is a fact about the
system, outside the logic.

Each such fact is a declaration (`Role.assumption`): a predicate over a model of the system, which
the theorems that rest on the fact take as a hypothesis, never an `axiom`. Such a predicate is
the contract of one operation of the model, a `Std.Do` triple whose postcondition is the property,
or states that the operations that run correspond to the model.
Each assumption names its sources (`Source`): a file of the Lean 4 repository at a release
tag, a document, or the reason it is trusted when no source states it. A property that the
observer tests on each result it gets, refusing the result when the test fails, is not an
assumption but a checked operation (`Role.checked`), whose contract is a theorem. The IO code that
supplies the real system is its observer (`Role.observer`): code written over a model's
operations reaches the system only through it. Other code of Regula still calls the primitive
operations directly, and no check finds those calls yet.

This module holds the vocabulary of those declarations; `Regula.Assumption` holds the attributes
that make them, and `RegulaPolicy.Assumptions` the reading of a claim's assumptions from the
constants it uses. -/

@[expose] public section

namespace RegulaPolicy.External

/-- A system outside Lean's logic that Regula's code observes or acts on. -/
inductive System where
  /-- Files, directories and symbolic links, through Lean's `IO.FS` and `System.FilePath`. -/
  | filesystem
  /-- Child processes, through Lean's `IO.Process`. -/
  | process
  /-- The process environment: variables, the working directory and the executable's path. -/
  | environment
  /-- Lake: its workspace, its configuration and its module lookup. -/
  | lake
  /-- Lean's elaborator, compiler and environment, as a program observes them. -/
  | lean
  /-- The operating system's file locks, through Lean's `IO.FS.Handle.lock`. -/
  | locking
  /-- Git and GitHub. -/
  | git
  deriving Repr, DecidableEq, Inhabited, Hashable

/-- Every system, each once. -/
def System.all : List System :=
  [.filesystem, .process, .environment, .lake, .lean, .locking, .git]

/-- `System.all` holds every system. -/
theorem System.mem_all (system : System) : system ∈ System.all := by
  cases system <;> simp [System.all]

/-- The name of a system in an attribute and in a report. -/
def System.spelling : System → String
  | .filesystem => "filesystem"
  | .process => "process"
  | .environment => "environment"
  | .lake => "lake"
  | .lean => "lean"
  | .locking => "locking"
  | .git => "git"

/-- The system a name spells, if any. -/
@[regula_decision]
def System.parse? : String → Option System
  | "filesystem" => some .filesystem
  | "process" => some .process
  | "environment" => some .environment
  | "lake" => some .lake
  | "lean" => some .lean
  | "locking" => some .locking
  | "git" => some .git
  | _ => none

/-- `parse?` reads every system's name back as that system. -/
theorem System.parse_spelling (system : System) : System.parse? system.spelling = some system := by
  cases system <;> rfl

/-- `parse?` accepts only the name of a system. -/
theorem System.spelling_of_parse {text : String} {system : System}
    (read : System.parse? text = some system) : system.spelling = text := by
  unfold System.parse? at read
  split at read <;> first | (cases read; rfl) | cases read

/-- `parse?` accepts exactly the names of the systems (`parse_spelling`, `spelling_of_parse`). -/
theorem System.checked_parse : Regula.ExecutableContract System.parse?
    (Regula.Decides (·.isSome = true) fun text => ∃ system : System, text = system.spelling) :=
  ⟨.of_roundtrip System.parse_spelling (fun _ _ read => System.spelling_of_parse read)
    .filesystem (unwritten := "") rfl⟩

/-- Where a fact about an external system is stated. -/
inductive Source where
  /-- A file of the Lean 4 repository at the release tag `version`, such as `v4.34.1`, with its
  lines: `location` is a path below the repository's `src` directory and a line range, such as
  `Init/System/IO.lean#L1330-L1342` or `runtime/io.cpp#L1351-L1364`. A toolchain installs the
  Lean files below its own `src/lean` directory. -/
  | lean (version : String) (location : String)
  /-- A document about `system` that states the fact and identifies its own version, such as a
  standard. A fact about Lean or Lake is stated by a `lean` source, which carries its release, so
  `Source.unpinned` refuses a document about either. -/
  | document (system : System) (reference : String)
  /-- No source states the fact: it is trusted for the given reason. -/
  | trusted (reason : String)
  deriving Repr, DecidableEq, Inhabited

/-- What a declaration is to the check of external systems. -/
inductive Role where
  /-- A property of `system` that the theorems resting on it take as a hypothesis: a predicate
  over a model of the system. -/
  | assumption (system : System) (sources : List Source)
  /-- An operation that runs an operation of `system`, tests the postcondition of that operation on
  its result and fails when the test fails. `contract` is the theorem that states that
  postcondition. -/
  | checked (system : System) (contract : Lean.Name) (sources : List Source)
  /-- IO code that supplies the real `system`: a place where its primitive operations may be
  called. -/
  | observer (system : System)
  deriving Repr, DecidableEq, Inhabited

/-- The system a declaration's role is about. -/
def Role.system : Role → System
  | .assumption system _ => system
  | .checked system _ _ => system
  | .observer system => system

/-- The sources a role names; an observer names none. -/
def Role.sources : Role → List Source
  | .assumption _ sources => sources
  | .checked _ _ sources => sources
  | .observer _ => []

/-! ## The version a source is pinned to -/

/-- A source pinned to a toolchain release other than `tag`: a `lean` source whose version is not
`tag`. A document or a trusted reason names no toolchain release, so it is never stale. -/
@[regula_decision]
def Source.stale (tag : String) : Source → Bool
  | .lean version _ => version != tag
  | .document .. | .trusted _ => false

/-- A source is stale exactly when it is a `lean` source of another version. -/
theorem Source.stale_iff (tag : String) (source : Source) :
    source.stale tag = true ↔
      ∃ version location, source = .lean version location ∧ version ≠ tag := by
  cases source <;> simp [Source.stale]

/-- `stale` holds exactly for the sources pinned to another toolchain release (`stale_iff`): it
holds for a source of another release and not for one of the current release, read as a decision on
the pair of the tag and the source. -/
theorem Source.checked_stale : Regula.ExecutableContract Source.stale
    (fun stale => Regula.Decides (· = true)
      (fun input : String × Source => ∃ version location,
        input.2 = .lean version location ∧ version ≠ input.1)
      (Function.uncurry stale)) :=
  ⟨.of_iff (fun input => Source.stale_iff input.1 input.2)
    ⟨("v4.34.1", .lean "v4.33.0" "Init/Prelude.lean#L1"), by decide⟩
    ⟨("v4.34.1", .lean "v4.34.1" "Init/Prelude.lean#L1"), by decide⟩⟩

/-! ## A document that would escape the pin -/

/-- The texts that identify a place in the Lean 4 repository or in Lean's documentation: the
repository's GitHub path `leanprover/lean4`, which a URL of `github.com` or of
`raw.githubusercontent.com` contains, and the documentation sites `lean-lang.org` and
`leanprover.github.io`. A reference that names that place by other text is not recognized. -/
def leanLocators : List String := ["leanprover/lean4", "lean-lang.org", "leanprover.github.io"]

/-- A source that states a fact about Lean or Lake without its release: a document about Lean or
Lake, or a document whose reference, in lower case, contains one of `leanLocators`. Such a fact
belongs in a `lean` source, which `stale` compares with the release that elaborates it. -/
@[regula_decision]
def Source.unpinned : Source → Bool
  | .document system reference =>
    system == .lean || system == .lake ||
      leanLocators.any fun locator => decide (locator.toList <:+: reference.toLower.toList)
  | .lean .. | .trusted _ => false

/-- A source is unpinned exactly when it is a document about Lean or Lake, or a document whose
reference in lower case is some text, then a Lean locator, then some text. -/
theorem Source.unpinned_iff (source : Source) :
    source.unpinned = true ↔ ∃ system reference, source = .document system reference ∧
      (system = .lean ∨ system = .lake ∨ ∃ locator ∈ leanLocators, ∃ before after : List Char,
        before ++ locator.toList ++ after = reference.toLower.toList) := by
  cases source with
  | lean version location => simp [Source.unpinned]
  | trusted reason => simp [Source.unpinned]
  | document system reference =>
    simp only [Source.unpinned, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, decide_eq_true_eq,
      Source.document.injEq]
    simp only [List.IsInfix, or_assoc]
    constructor
    · intro h; exact ⟨system, reference, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, h⟩; exact h

/-- `unpinned` holds exactly for a document about Lean or Lake or one that names a place of the
Lean 4 repository or of Lean's documentation (`unpinned_iff`). -/
theorem Source.checked_unpinned : Regula.ExecutableContract Source.unpinned
    (Regula.Decides (· = true) fun source => ∃ system reference,
      source = .document system reference ∧
        (system = .lean ∨ system = .lake ∨ ∃ locator ∈ leanLocators, ∃ before after : List Char,
          before ++ locator.toList ++ after = reference.toLower.toList)) :=
  ⟨.of_iff Source.unpinned_iff ⟨.document .lean "", by decide⟩ ⟨.trusted "", by decide⟩⟩

end RegulaPolicy.External
