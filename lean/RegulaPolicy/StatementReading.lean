module

public import RegulaPolicy.Domain
public import RegulaPolicy.KernelAxioms
public import Regula.Contract
meta import Regula.Decision

/-! # The reading of a statement

The pure decision of what the search for shared functions (RG1009) reads of the specification of
a decision registration and of its acceptance predicate: from each constant that such a term
reaches, which of the constants that the constant mentions the search follows (`reads`), and the
constants that the term reaches by that reading (`reading`).

The rule of a statement (`Observed.references`) follows the type of each constant, the value of a
definition whose value a statement depends on (`RegulaPolicy.ResultForm.ValueRead`), and the
declaration of an inductive type, a constructor and a recursor. The reading is that rule with one
exception: it does not enter the declaration of the input type of the kind from the input. A kind
compares `accepts (f x)` with `spec x` for each input `x : α`, and the specification is
`fun x : α => b`. The reading starts at the constants of `b`, not at those of `α`, and from a
field's projection function of a structure that occurs in `α` it does not follow the edge back to
that structure. The acceptance predicate is read in the same way, with the result type in the
place of the input type. Everything else is followed as before: the arguments of each application,
the types of opaque constants and axioms, and the declaration of a constant of `α` that `b` names in
any other way, as the binder of `∀ y : α`, as an argument of a function or through a constructor.

A test `T` that the rule reaches only through the declaration of a constant of `α` that `b` does
not name is not a part of `spec x` for any `x`: a change of `T` changes which values `α` has, the
same set on the two sides of the kind, and the comparison at each input is the one that it was
(rbeauchamp/regula#270). `through_input` states the property that this argument needs of the
reading: a constant that the rule reaches and the reading does not is reached from a constant of
the input type that the reading does not reach at all.

`Observed` is what the observing pass (`Regula.Collect`) reads of one constant: its kind, the form
of its result type, the constants that each part of it mentions, and the structure of a field's
projection function, read from its kernel-checked value. `reads` decides which of those constants
the search follows; it is registered with the kind `checked_reads` against `Read`. `reading`
closes the reading and the rule from the constants of a term (`reading_some`,
`read_subset_withTypes`), and `sharedConstants` gives the shared constants of each
(`no_shared_test`, `accepted_throughTypes`). The record of a registration names each function with
a result of `Bool` or `BEq` that the two sides share by the rule and not by the reading
(`RegulaPolicy.SharedNames.throughTypes`).

**Not claimed.** That the constants of each part are those that the part mentions is the pass's:
it reads them with `Lean.Expr.getUsedConstants`, a function of Lean's library. That a test reached
only through the declaration of the input type is no part of the specification is the argument
above, stated in the standard; it is not a theorem about Lean's semantics. -/

@[expose] public section

namespace RegulaPolicy.StatementReading
open Lean

/-! ## The reading of one constant -/

/-- The kind of a constant of the declaration of an inductive type: the inductive type, a
constructor or a recursor. The rule of a statement reads the declaration of such a constant: a
statement about a value of an inductive type is about what its constructors hold, the proof
fields among them. -/
def Declares (kind : DeclarationKind) : Prop :=
  kind = .«inductive» ∨ kind = .«constructor» ∨ kind = .«recursor»

instance (kind : DeclarationKind) : Decidable (Declares kind) := by
  unfold Declares; infer_instance

/-- What the observing pass reads of a constant outside Lean's own library that a specification
or an acceptance predicate reaches. Each list holds the constants that one part of the constant
mentions, as `Lean.Expr.getUsedConstants` gives them. -/
structure Observed where
  /-- The kind of its `ConstantInfo`. -/
  kind : DeclarationKind
  /-- The form of its result type (`RegulaPolicy.ResultForm`). -/
  result : ResultForm
  /-- The constants that its type mentions. -/
  type : Array Name
  /-- For a definition: the constants that its value mentions. Empty for every other
  constant. -/
  value : Array Name
  /-- For an inductive type: its constructors. For a recursor: the constructor and the constants
  of the right side of each of its rules. Empty for every other constant. -/
  declaration : Array Name
  /-- For a field's projection function: its structure, read from its kernel-checked value, which
  is the primitive projection of its last argument under its binders. `none` for every other
  constant. -/
  projection : Option Name
  deriving Repr, DecidableEq, Inhabited

/-- The constants that the rule of a statement follows from the constant: its type, the
declaration of a constant of the declaration of an inductive type, and the value of a definition
whose value the rule reads (`RegulaPolicy.ResultForm.ValueRead`). The rule reads no value of a
proof or of a `Decidable` definition, and no value of a theorem, an opaque constant or an
axiom. -/
def Observed.references (observed : Observed) : Array Name :=
  observed.type ++
    (if Declares observed.kind then observed.declaration
     else if observed.kind = .«definition» ∧ observed.result.ValueRead true then observed.value
     else #[])

/-- A constant that a constant mentions, with what the pass read of the constant that mentions
it, and the constants of the input type of the kind (the result type, for an acceptance
predicate). -/
structure Mention where
  /-- What the pass read of the constant that mentions `target`. -/
  source : Observed
  /-- The constant that is mentioned. -/
  target : Name
  /-- The constants of the input type of the kind, or of its result type. -/
  domain : Array Name
  deriving Repr, DecidableEq, Inhabited

/-- The search follows the mention: the rule of a statement follows it, and it is not the edge
from a field's projection function back to its structure, where that structure is a constant of
the input type. Two cases:

* `other`: the constant is no projection function of a structure of the input type.
* `field`: the constant is a projection function, and the target is not its structure: the type
  of the field, or a type of a parameter. -/
inductive Read (mention : Mention) : Prop where
  /-- The rule follows the target from a constant that is no projection function of a
  structure of the input type. -/
  | other (referenced : mention.target ∈ mention.source.references)
      (outside : ∀ structure_, mention.source.projection = some structure_ →
        structure_ ∉ mention.domain)
  /-- The rule follows the target from a projection function, and the target is not its
  structure. -/
  | field (referenced : mention.target ∈ mention.source.references) (structure_ : Name)
      (projection : mention.source.projection = some structure_)
      (different : mention.target ≠ structure_)

/-- The decision of the reading of a statement: whether the search follows the mention
(`reads_iff`). -/
@[regula_decision]
def reads (mention : Mention) : Bool :=
  mention.source.references.contains mention.target &&
    match mention.source.projection with
    | some structure_ => structure_ != mention.target || !mention.domain.contains structure_
    | none => true

/-- `reads` decides `Read` exactly. -/
theorem reads_iff (mention : Mention) : reads mention = true ↔ Read mention := by
  obtain ⟨source, target, domain⟩ := mention
  unfold reads
  cases found : source.projection with
  | none =>
    simp only [Bool.and_true, Array.contains_iff_mem]
    constructor
    · intro referenced
      exact .other referenced fun _ projection => by simp [found] at projection
    · intro read
      cases read with
      | other referenced _ => exact referenced
      | field referenced _ projection _ => simp [found] at projection
  | some structure_ =>
    simp only [Bool.and_eq_true, Array.contains_iff_mem, Bool.or_eq_true, bne_iff_ne, ne_eq,
      Bool.not_eq_true', Bool.eq_false_iff]
    constructor
    · rintro ⟨referenced, different | outside⟩
      · exact .field referenced structure_ found (Ne.symm different)
      · exact .other referenced fun other projection => by
          simp only [found, Option.some.injEq] at projection
          exact projection ▸ outside
    · intro read
      cases read with
      | other referenced outside => exact ⟨referenced, .inr (outside structure_ found)⟩
      | field referenced other projection different =>
        simp only [found, Option.some.injEq] at projection
        exact ⟨referenced, .inl (projection ▸ Ne.symm different)⟩

/-- `reads` decides `Read` (`reads_iff`): it follows a projection function of the input type to
the type of its field, and it does not follow it back to the input type. -/
theorem checked_reads : Regula.ExecutableContract reads (Regula.Decides (· = true) Read) :=
  ⟨.of_iff reads_iff
    ⟨⟨⟨.«definition», .other, #[`Input, `Nat], #[`Input], #[], some `Input⟩, `Nat, #[`Input]⟩,
      (reads_iff _).mpr (.field (by simp [Observed.references, Declares]) `Input rfl (by simp))⟩
    ⟨⟨⟨.«definition», .other, #[`Input, `Nat], #[`Input], #[], some `Input⟩, `Input, #[`Input]⟩,
      fun accepted => by
        cases (reads_iff _).mp accepted with
        | other _ outside => exact outside `Input rfl (by simp)
        | field _ _ projection different =>
          simp only [Option.some.injEq] at projection
          exact different projection⟩⟩

/-- The constants that the search follows from the constant (`reads`), for the constants of the
input type `domain`. -/
def Observed.read (observed : Observed) (domain : Array Name) : Array Name :=
  observed.references.filter fun target => reads ⟨observed, target, domain⟩

/-- **The constants that the search follows from a constant are exactly those of `Read`.** -/
theorem mem_read (observed : Observed) (domain : Array Name) (target : Name) :
    target ∈ observed.read domain ↔ Read ⟨observed, target, domain⟩ := by
  unfold Observed.read
  rw [Array.mem_filter, reads_iff]
  refine ⟨And.right, fun read => ⟨?_, read⟩⟩
  cases read with
  | other referenced _ => exact referenced
  | field referenced _ _ _ => exact referenced

/-- The reading follows only what the rule follows. -/
theorem read_references {observed : Observed} {domain : Array Name} {target : Name}
    (read : target ∈ observed.read domain) : target ∈ observed.references :=
  (Array.mem_filter.mp read).1

/-- A constant that the rule follows and the reading does not is the structure of a projection
function, and a constant of the input type. -/
theorem dropped {observed : Observed} {domain : Array Name} {target : Name}
    (referenced : target ∈ observed.references) (unread : target ∉ observed.read domain) :
    observed.projection = some target ∧ target ∈ domain := by
  rw [mem_read] at unread
  cases found : observed.projection with
  | none => exact absurd (.other referenced fun _ projection => by simp [found] at projection) unread
  | some structure_ =>
    by_cases same : target = structure_
    · subst same
      by_cases inside : target ∈ domain
      · exact ⟨rfl, inside⟩
      · exact absurd (.other referenced fun other projection => by
          simp only [found, Option.some.injEq] at projection
          exact projection ▸ inside) unread
    · exact absurd (.field referenced structure_ found same) unread

/-! ## The reading of a term -/

/-- What `reading` reads: the record of each constant outside Lean's own library that the term
reaches by the rule of a statement, the constants of the input type, and the constants of the
body of the term under the variable of the input. A constant with no record is not followed: a
constant of Lean's own library, or one that the environment does not have. -/
structure Request where
  /-- What the pass read of each constant that it read. -/
  records : Std.HashMap Name Observed
  /-- The constants of the input type of the kind (the result type, for an acceptance
  predicate): those of the type of the variable of the term. -/
  domain : Array Name
  /-- The constants of the body of the term under the variable of the input. -/
  body : Array Name

/-- The constants that the reading follows from `name`: those of its record (`Observed.read`),
or none without a record. -/
def Request.readNext (request : Request) (name : Name) : Array Name :=
  match request.records[name]? with
  | some observed => observed.read request.domain
  | none => #[]

/-- The constants that the rule of a statement follows from `name`. -/
def Request.withTypesNext (request : Request) (name : Name) : Array Name :=
  match request.records[name]? with
  | some observed => observed.references
  | none => #[]

/-- The bound of the steps of a search over the records: one more than the number of constants
that the term and all records list. A search expands each constant one time. -/
def Request.fuel (request : Request) : Nat :=
  request.records.fold (fun total _ observed => total + observed.references.size)
    (request.domain.size + request.body.size + 1)

/-- The constants with a record that a term reaches: by the reading from its body (`read`), and
by the rule of a statement from the whole term, its input type included (`withTypes`). -/
structure Reading where
  /-- The constants with a record that the body of the term reaches by `Request.readNext`. -/
  read : Array Name
  /-- The constants with a record that the term reaches by `Request.withTypesNext`, the rule of
  a statement, from the constants of its input type and of its body. -/
  withTypes : Array Name

/-- The two readings of the term, or `none` when a search runs out of its bound of steps
(`reading_some`). -/
def reading (request : Request) : Option Reading := do
  let read ← KernelAxioms.search request.readNext request.fuel request.body.toList
  let withTypes ← KernelAxioms.search request.withTypesNext request.fuel
    (request.domain ++ request.body).toList
  let recorded (names : Std.HashSet Name) : Array Name :=
    (names.toList.filter request.records.contains).toArray
  return { read := recorded read, withTypes := recorded withTypes }

/-- **The two readings of a term.** A constant is in `read` exactly when it has a record and
the body of the term reaches it by the reading, and in `withTypes` exactly when it has a record and
the term, its input type included, reaches it by the rule of a statement. -/
theorem reading_some {request : Request} {result : Reading}
    (returned : reading request = some result) :
    (∀ name, name ∈ result.read ↔ request.records.contains name = true ∧
      ∃ start ∈ request.body, KernelAxioms.Reach request.readNext start name) ∧
    (∀ name, name ∈ result.withTypes ↔ request.records.contains name = true ∧
      ∃ start ∈ request.domain ++ request.body,
        KernelAxioms.Reach request.withTypesNext start name) := by
  unfold reading at returned
  cases readSearch : KernelAxioms.search request.readNext request.fuel request.body.toList with
  | none => simp [readSearch] at returned
  | some read =>
    cases withTypesSearch : KernelAxioms.search request.withTypesNext request.fuel
        (request.domain ++ request.body).toList with
    | none =>
      simp only [readSearch, withTypesSearch, Option.bind_eq_bind, Option.bind_some,
        Option.bind_none, reduceCtorEq] at returned
    | some withTypes =>
      simp only [readSearch, withTypesSearch, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, Option.some.injEq] at returned
      subst returned
      obtain ⟨readComplete, readSound⟩ := KernelAxioms.search_some readSearch
      obtain ⟨withComplete, withSound⟩ := KernelAxioms.search_some withTypesSearch
      refine ⟨fun name => ?_, fun name => ?_⟩
      · simp only [List.mem_toArray, List.mem_filter, Std.HashSet.mem_toList]
        constructor
        · rintro ⟨member, recorded⟩
          obtain ⟨start, starts, reach⟩ := readSound name member
          exact ⟨recorded, start, Array.mem_toList_iff.mp starts, reach⟩
        · rintro ⟨recorded, start, starts, reach⟩
          exact ⟨readComplete start (Array.mem_toList_iff.mpr starts) name reach, recorded⟩
      · simp only [List.mem_toArray, List.mem_filter, Std.HashSet.mem_toList]
        constructor
        · rintro ⟨member, recorded⟩
          obtain ⟨start, starts, reach⟩ := withSound name member
          exact ⟨recorded, start, Array.mem_toList_iff.mp starts, reach⟩
        · rintro ⟨recorded, start, starts, reach⟩
          exact ⟨withComplete start (Array.mem_toList_iff.mpr starts) name reach, recorded⟩

/-- Each step of the reading is a step of the rule. -/
theorem readNext_withTypesNext {request : Request} {source target : Name}
    (step : target ∈ request.readNext source) : target ∈ request.withTypesNext source := by
  unfold Request.readNext at step
  unfold Request.withTypesNext
  cases found : request.records[source]? with
  | none => simp [found] at step
  | some observed =>
    simp only [found] at step ⊢
    exact read_references step

/-- **The reading reaches only what the rule reaches.** So a registration that the search refuses
for a function that the reading reaches, it refuses also by the rule: the reading refuses no
registration that the rule accepts. -/
theorem read_subset_withTypes {request : Request} {result : Reading}
    (returned : reading request = some result) {name : Name} (member : name ∈ result.read) :
    name ∈ result.withTypes := by
  obtain ⟨read, withTypes⟩ := reading_some returned
  obtain ⟨recorded, start, starts, reach⟩ := (read name).mp member
  exact (withTypes name).mpr ⟨recorded, start, Array.mem_append_right _ starts,
    reach.mono fun _ _ step => readNext_withTypesNext step⟩

/-- The body of the term reaches the constant by the reading. -/
def Request.Reads (request : Request) (name : Name) : Prop :=
  ∃ start ∈ request.body, KernelAxioms.Reach request.readNext start name

/-- A rule path from a constant that the reading reaches, or from a constant of the input type
that it does not reach, to a constant that it does not reach, passes through a constant of the
input type that the reading does not reach. -/
private theorem through_input_from {request : Request} {source name : Name}
    (reach : KernelAxioms.Reach request.withTypesNext source name)
    (unread : ¬ request.Reads name)
    (from_ : request.Reads source ∨ (source ∈ request.domain ∧ ¬ request.Reads source)) :
    ∃ constant ∈ request.domain, ¬ request.Reads constant ∧
      KernelAxioms.Reach request.withTypesNext constant name := by
  induction reach with
  | refl source =>
    rcases from_ with read | ⟨inside, unreadSource⟩
    · exact absurd read unread
    · exact ⟨source, inside, unreadSource, .refl source⟩
  | @step source middle name step rest next =>
    rcases from_ with ⟨start, starts, readSource⟩ | ⟨inside, unreadSource⟩
    · by_cases readStep : middle ∈ request.readNext source
      · exact next unread (.inl ⟨start, starts, readSource.tail readStep⟩)
      · unfold Request.withTypesNext at step
        unfold Request.readNext at readStep
        cases found : request.records[source]? with
        | none => simp [found] at step
        | some observed =>
          simp only [found] at step readStep
          obtain ⟨-, inside⟩ := dropped step readStep
          by_cases readMiddle : request.Reads middle
          · exact next unread (.inl readMiddle)
          · exact next unread (.inr ⟨inside, readMiddle⟩)
    · exact ⟨source, inside, unreadSource, .step step rest⟩

/-- **What the reading leaves out is reached only through the input type.** A constant that the
term reaches by the rule of a statement and not by the reading is reached by the rule from a
constant of the input type that the reading does not reach: the body of the term names that
constant in no way but through a projection of a field. -/
theorem through_input {request : Request} {result : Reading}
    (returned : reading request = some result) {name : Name}
    (rule : name ∈ result.withTypes) (unread : name ∉ result.read) :
    ∃ constant ∈ request.domain, ¬ request.Reads constant ∧
      KernelAxioms.Reach request.withTypesNext constant name := by
  obtain ⟨read, withTypes⟩ := reading_some returned
  obtain ⟨recorded, start, starts, reach⟩ := (withTypes name).mp rule
  have notRead : ¬ request.Reads name := fun reads => unread ((read name).mpr ⟨recorded, reads⟩)
  rcases Array.mem_append.mp starts with inside | body
  · by_cases readStart : request.Reads start
    · exact through_input_from reach notRead (.inl readStart)
    · exact through_input_from reach notRead (.inr ⟨inside, readStart⟩)
  · exact through_input_from reach notRead (.inl ⟨start, body, .refl start⟩)

/-! ## The shared functions of a registration -/

/-- The shared constants of a decision registration by one reading: each constant that
`specification` holds and that the other side holds too, the implementation (`implementation`)
or `acceptance`, with what the collector read of it (`definitions`). `widen` selects the rule of a
statement (`Reading.withTypes`) over the reading (`Reading.read`), on the two terms. A constant
that `definitions` has no entry for is left out. -/
def sharedConstants (widen : Bool) (specification acceptance : Reading)
    (implementation : Name → Bool) (definitions : Name → Option SharedDefinition) :
    List SharedDefinition :=
  let side (reading : Reading) := if widen then reading.withTypes else reading.read
  (side specification).toList.filterMap fun name =>
    if implementation name || (side acceptance).contains name then definitions name else none

/-- A constant is a shared constant of a reading exactly when the specification holds it by that
reading, the implementation or the acceptance predicate holds it by the same reading, and the
collector read it. -/
theorem mem_sharedConstants {widen : Bool} {specification acceptance : Reading}
    {implementation : Name → Bool} {definitions : Name → Option SharedDefinition}
    {definition : SharedDefinition} :
    definition ∈ sharedConstants widen specification acceptance implementation definitions ↔
      ∃ name, name ∈ (if widen then specification.withTypes else specification.read) ∧
        (implementation name = true ∨
          name ∈ (if widen then acceptance.withTypes else acceptance.read)) ∧
        definitions name = some definition := by
  unfold sharedConstants
  simp only [List.mem_filterMap, Array.mem_toList_iff, Option.ite_none_right_eq_some,
    Bool.or_eq_true, Array.contains_iff_mem]

/-- **A registration that the reading accepts has no test that its specification reads and its
implementation reaches.** When the record names no function of the class `boolean` from the
reading (`RegulaPolicy.sharedTestFailure` then refuses nothing), no constant that the reading of
the specification reaches and that the implementation reaches is of that class. This is the
reason of the rule (RG1009) at the level of the readings: what the specification states shares
no test with the implementation. That the reading of the body is what the specification states
is the argument of this module. -/
theorem no_shared_test {first : List SharedDefinition} {specification acceptance : Reading}
    {implementation : Name → Bool} {definitions : Name → Option SharedDefinition}
    (accepted : (sharedNames first
      (sharedConstants false specification acceptance implementation definitions)
      (sharedConstants true specification acceptance implementation definitions)).booleans = #[])
    {name : Name} {definition : SharedDefinition} (read : name ∈ specification.read)
    (reached : implementation name = true) (found : definitions name = some definition) :
    definition.class ≠ .boolean := by
  rw [sharedNames_booleans_eq_empty_iff] at accepted
  exact accepted definition (mem_sharedConstants.mpr ⟨name, read, .inl reached, found⟩)

/-- **The reading refuses no registration that the rule of a statement accepts.** Each shared
constant of the reading is a shared constant of the rule of a statement, when each reading
reaches at most what the rule of a statement reaches (`read_subset_withTypes`), so a function
of the class `boolean` that the record names is one that the rule of a statement shares
too. -/
theorem sharedConstants_read_subset {specification acceptance : Reading}
    {implementation : Name → Bool} {definitions : Name → Option SharedDefinition}
    (specificationWithin : ∀ name, name ∈ specification.read → name ∈ specification.withTypes)
    (acceptanceWithin : ∀ name, name ∈ acceptance.read → name ∈ acceptance.withTypes)
    {definition : SharedDefinition}
    (shared : definition ∈ sharedConstants false specification acceptance implementation
      definitions) :
    definition ∈ sharedConstants true specification acceptance implementation definitions := by
  obtain ⟨name, held, other, found⟩ := mem_sharedConstants.mp shared
  simp only [Bool.false_eq_true, ↓reduceIte] at held other
  refine mem_sharedConstants.mpr ⟨name, ?_, ?_, found⟩
  · simpa using specificationWithin name held
  · simpa using other.imp id (acceptanceWithin name)

/-- **What the change accepts.** A registration that the reading accepts and that the rule of a
statement refuses has each of the functions of the class `boolean` that the rule shares in
`throughTypes`, and the implementation does not reach any of them through what the specification
reads: for each such function, the specification does not read it, or the implementation does
not reach it and the acceptance predicate does not read it. -/
theorem accepted_throughTypes {first : List SharedDefinition} {specification acceptance : Reading}
    {implementation : Name → Bool} {definitions : Name → Option SharedDefinition}
    (accepted : (sharedNames first
      (sharedConstants false specification acceptance implementation definitions)
      (sharedConstants true specification acceptance implementation definitions)).booleans = #[])
    {definition : SharedDefinition}
    (shared : definition ∈ sharedConstants true specification acceptance implementation
      definitions)
    (boolean : definition.class = .boolean) :
    definition.name ∈ (sharedNames first
      (sharedConstants false specification acceptance implementation definitions)
      (sharedConstants true specification acceptance implementation definitions)).throughTypes ∧
    ∀ name, definitions name = some definition →
      name ∉ specification.read ∨ (implementation name = false ∧ name ∉ acceptance.read) := by
  have none := (sharedNames_booleans_eq_empty_iff _ _ _).mp accepted
  refine ⟨(mem_sharedNames_throughTypes _ _ _ _).mpr ⟨⟨definition, shared, boolean, rfl⟩,
    fun ⟨other, member, otherBoolean, _⟩ => none other member otherBoolean⟩, ?_⟩
  intro name found
  by_cases read : name ∈ specification.read
  · refine .inr ⟨?_, fun acceptanceRead => ?_⟩
    · cases reached : implementation name
      · rfl
      · exact absurd boolean (no_shared_test accepted read reached found)
    · exact none definition (mem_sharedConstants.mpr ⟨name, read, .inr acceptanceRead, found⟩)
        boolean
  · exact .inl read

end RegulaPolicy.StatementReading
