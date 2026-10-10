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

A kind compares `accepts (f x)` with `spec x` for each input `x`. The search reads `spec` and
`accepts` for what the truth of `spec x` and of `accepts r` depends on at a given `x` and a given
`r`. Three parts of a term name only the types of values that are given, and the search does not
follow them:

* **The types of the leading variables of a function.** A term `fun (x₁ : T₁) … (xₙ : Tₙ) => b`
  has the value of `b` at each argument, and `Tᵢ` is the domain: which arguments there are. A
  change of the declaration of `Tᵢ`, such as an invariant of a structure in a proof field,
  changes which values `Tᵢ` has, and not the value of the function at an argument. So the search
  reads `b` and not `Tᵢ`. The specification itself is `fun x : α => b`, so the search does not
  read the declaration of the input type through its variable, and the acceptance predicate is
  `fun r : ρ => b`, so it does not read the declaration of the result type through its
  variable.
* **The parameters of an application of a field's projection function.** A projection function
  applied to the parameters of its structure and to a value of the structure gives the field of
  that value. The parameters, such as the element type of an array in `xs[i]` or the predicate of
  a subtype in `x.val`, say which structure type the value has; the search reads the value and
  the arguments after it, and not the parameters (`readStep`). The structure that a primitive
  projection `e.i` names is not read either: the projection is the field of the value `e`.
* **The type of a constant whose value the search reads.** The value of a definition determines
  the definition, and its type is the type of that value. So the search reads the body of the
  value and not the type. A field's projection function is such a definition: its value is the
  field of its argument, so a specification that reads a field of its input, at any depth, does
  not lead to the declaration of the structure.

A term that quantifies over a type, or that builds or takes apart its values, names the type
outside these parts: as the binder of `∀`, as an argument of `Exists`, `Eq` or another constant
that is no projection function, or through a constructor or a recursor, whose declaration the
search reads. So does a term that names a definition of a proposition: the search reads the value
of that definition.

`Observed` is what the observing pass (`Regula.Collect`) reads of one constant: its kind, the form
of its result type, and the constants that each part of it mentions. `reads` decides which of
those constants the search follows; it is registered with the kind `checked_reads` against
`Read`. `Observed.withTypes` is the reading that also follows the three parts above, the reading
of the search before it left them out (`read_withTypes`). `reading` closes the two readings from
the constants of a term (`reading_some`); a constant that the reading with the types reaches and
the reading does not is reached only through a type that the search does not follow
(`read_subset_withTypes`), and the record of the registration names such a function with a result
of `Bool` or `BEq` (`RegulaPolicy.SharedNames.throughTypes`). `sharedConstants` gives the shared
constants of each reading: a registration that the reading accepts has no test that the reading
of its specification and its implementation reach (`no_shared_test`), and one that the reading
accepts and the reading with the types refuses has each such test in `throughTypes`
(`accepted_throughTypes`).

**Not claimed.** That the constants of each part are those that the part mentions is the pass's:
it reads them with `Lean.Expr.getUsedConstants`, and those of a body with `Lean.Expr.forEach'` and
`readStep`, functions of Lean's library and of this module. That a statement does not depend on what the three parts name is the
argument above, stated in the standard; it is not a theorem about Lean's semantics. -/

@[expose] public section

namespace RegulaPolicy.StatementReading
open Lean

/-! ## The parts of a term -/

/-- The leading function abstractions of `e`, each with its binder name, the type of its
variable and its binder information, and the body under them: `e` is
`fun (x₁ : T₁) … (xₙ : Tₙ) => b` with `b` no function abstraction. -/
def lambdaParts : Expr → List (Name × Expr × BinderInfo) × Expr
  | .lam name type body info =>
    let (binders, inner) := lambdaParts body
    ((name, type, info) :: binders, inner)
  | e => ([], e)

/-- The term with the function abstractions `binders` around `body`. -/
def abstract (binders : List (Name × Expr × BinderInfo)) (body : Expr) : Expr :=
  binders.foldr (fun binder inner => .lam binder.1 binder.2.1 inner binder.2.2) body

/-- The parts of a term are the term: the types of the leading variables and the body hold every
subterm of it, so a constant that the term mentions is in a type of a leading variable or in the
body. -/
theorem abstract_lambdaParts (e : Expr) : abstract (lambdaParts e).1 (lambdaParts e).2 = e := by
  induction e with
  | lam name type body info _ ih =>
    simp only [lambdaParts, abstract, List.foldr_cons] at ih ⊢
    rw [ih]
  | _ => rfl

/-- The body of `lambdaParts e` is no function abstraction. -/
theorem lambdaParts_body (e : Expr) (name : Name) (type body : Expr) (info : BinderInfo) :
    (lambdaParts e).2 ≠ .lam name type body info := by
  induction e with
  | lam _ _ _ _ _ ih => simpa only [lambdaParts] using ih
  | _ => simp [lambdaParts]

/-- What the reading takes of one subterm `e` of a body, for `Lean.Expr.forEach'`, which takes
each subterm from the outside in and goes into its children only when asked: the constant that
the reading reads at `e`, and whether it goes on into the children of `e`.

* A constant is read.
* An application of a field's projection function to at most the parameters of its structure,
  where `parameters` gives the number of parameters of the structure of each projection function,
  reads the function and not its arguments. In `p a₁ … aₖ b₁ … bₘ` with `k` parameters, the
  reading goes into the function `p a₁ … aₖ` and the arguments `b₁ … bₘ`, and reads `p` there.
* Every other subterm reads nothing itself, and the reading goes into its children. The children
  of a primitive projection `e.i` are `e` alone: the name of its structure is no subterm, so the
  reading does not read it. -/
def readStep (parameters : Name → Option Nat) (e : Expr) : Option Name × Bool :=
  match e with
  | .const name _ => (some name, false)
  | .app .. =>
    match e.getAppFn with
    | .const name _ =>
      match parameters name with
      | some count => if e.getAppNumArgs ≤ count then (some name, false) else (none, true)
      | none => (none, true)
    | _ => (none, true)
  | _ => (none, true)

/-- The reading leaves out the children of a subterm only at a constant, which has none, and at
an application of a projection function to at most the parameters of its structure, where it
reads the function (`readStep`). -/
theorem readStep_skips {parameters : Name → Option Nat} {e : Expr}
    (skips : (readStep parameters e).2 = false) :
    (∃ name levels, e = .const name levels ∧ (readStep parameters e).1 = some name) ∨
      ∃ name levels count, e.getAppFn = .const name levels ∧ parameters name = some count ∧
        e.getAppNumArgs ≤ count ∧ (readStep parameters e).1 = some name := by
  unfold readStep at skips ⊢
  split
  · next name levels => exact .inl ⟨name, levels, rfl, rfl⟩
  · split
    · next name levels head =>
      split
      · next count found =>
        split
        · next within => exact .inr ⟨name, levels, count, head, found, within, rfl⟩
        · next => simp_all
      · next => simp_all
    · next => simp_all
  · next => simp_all

/-! ## The reading of one constant -/

/-- The kind of a constant of the declaration of an inductive type: the inductive type, a
constructor or a recursor. The search reads the declaration of such a constant: a statement about
a value of an inductive type is about what its constructors hold, the proof fields among them. -/
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
  /-- For a definition: the constants that the body of its value under its leading variables
  mentions (`lambdaParts`), with the parameters of each application of a projection function
  and the structures of primitive projections left out (`readStep`). Empty for every other
  constant. -/
  body : Array Name
  /-- For an inductive type: its constructors. For a recursor: the constructor and the constants
  of the right side of each of its rules. Empty for every other constant. -/
  declaration : Array Name
  deriving Repr, DecidableEq, Inhabited

/-- A constant that a constant mentions, with what the pass read of the constant that mentions
it. -/
structure Mention where
  /-- What the pass read of the constant that mentions `target`. -/
  source : Observed
  /-- The constant that is mentioned. -/
  target : Name
  deriving Repr, DecidableEq, Inhabited

/-- The search follows the mention by the rule of a statement. One case for each part of a
constant that the rule reads:

* `declaration`: the constant is of the declaration of an inductive type, and the target is in
  its type or its declaration.
* `body`: the constant is a definition whose value the rule reads
  (`RegulaPolicy.ResultForm.ValueRead`), and the target is in the body of that value.
* `type`: the constant is of no declaration of an inductive type, the rule does not read its
  value, and the target is in its type: the statement of a proof, the proposition of a
  `Decidable` value.

The rule reads no other part. It does not read the types of the leading variables of a value,
the parameters of an application of a projection function in it, the structure that a primitive
projection in it names, or the type of a constant whose value it reads. It reads nothing of an
opaque constant or of an axiom whose value it would read, since there is no value that a
statement can depend on. -/
inductive Read (mention : Mention) : Prop where
  /-- The target is in the type or the declaration of a constant of the declaration of an
  inductive type. -/
  | declaration (declares : Declares mention.source.kind)
      (named : mention.target ∈ mention.source.type ∨ mention.target ∈ mention.source.declaration)
  /-- The target is in the body of the value of a definition whose value the rule reads. -/
  | body (definition : mention.source.kind = .«definition»)
      (read : mention.source.result.ValueRead true) (named : mention.target ∈ mention.source.body)
  /-- The target is in the type of a constant whose value the rule does not read. -/
  | type (declares : ¬ Declares mention.source.kind)
      (unread : ¬ mention.source.result.ValueRead true) (named : mention.target ∈ mention.source.type)

/-- The decision of the reading of a statement: whether the search follows the mention
(`reads_iff`). -/
@[regula_decision]
def reads (mention : Mention) : Bool :=
  match mention.source.kind with
  | .«inductive» | .«constructor» | .«recursor» =>
    mention.source.type.contains mention.target ||
      mention.source.declaration.contains mention.target
  | .«definition» =>
    if mention.source.result.ValueRead true then mention.source.body.contains mention.target
    else mention.source.type.contains mention.target
  | .«axiom» | .«theorem» | .«opaque» | .«quotient» =>
    !decide (mention.source.result.ValueRead true) &&
      mention.source.type.contains mention.target

/-- `reads` decides `Read` exactly. -/
theorem reads_iff (mention : Mention) : reads mention = true ↔ Read mention := by
  obtain ⟨⟨kind, result, type, value, body, declaration⟩, target⟩ := mention
  constructor
  · intro accepted
    cases kind <;> simp only [reads] at accepted
    case «inductive» | «constructor» | «recursor» =>
      exact .declaration (by simp [Declares])
        (by simpa only [Bool.or_eq_true, Array.contains_iff_mem] using accepted)
    case «definition» =>
      by_cases read : result.ValueRead true
      · simp only [read, ↓reduceIte, Array.contains_iff_mem] at accepted
        exact .body rfl read accepted
      · simp only [read, ↓reduceIte, Array.contains_iff_mem] at accepted
        exact .type (by simp [Declares]) read accepted
    all_goals
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Array.contains_iff_mem] at accepted
      exact .type (by simp [Declares]) accepted.1 accepted.2
  · intro read
    cases read with
    | declaration declares named =>
      simp only [Declares] at declares
      rcases declares with same | same | same <;> subst same <;>
        simpa only [reads, Bool.or_eq_true, Array.contains_iff_mem] using named
    | body definition read named =>
      subst definition
      simpa only [reads, read, ↓reduceIte, Array.contains_iff_mem] using named
    | type declares unread named =>
      simp only [Declares, not_or] at declares
      obtain ⟨notInductive, notConstructor, notRecursor⟩ := declares
      cases kind <;> simp_all [reads]

/-- `reads` decides `Read` (`reads_iff`): it follows the constant in the body of a definition
whose value the rule reads, and it does not follow the input type in the type of the leading
variable of that value. -/
theorem checked_reads : Regula.ExecutableContract reads (Regula.Decides (· = true) Read) :=
  ⟨.of_iff reads_iff
    ⟨⟨⟨.«definition», .other, #[], #[`Input], #[`test], #[]⟩, `test⟩,
      (reads_iff _).mpr (.body rfl (by decide) (by simp))⟩
    ⟨⟨⟨.«definition», .other, #[], #[`Input], #[`test], #[]⟩, `Input⟩, fun accepted => by
      cases (reads_iff _).mp accepted with
      | declaration declares _ => simp [Declares] at declares
      | body _ _ named => simp at named
      | type _ unread _ => exact unread (by decide)⟩⟩

/-! ## The two readings of one constant -/

/-- The constants that the search follows from the constant by the rule of a statement with the
types that `Read` leaves out: its type, the declaration of a constant of the declaration of an
inductive type, and the whole value of a definition whose value the rule reads, with the body
that `Read` reads. This is the reading of the search before it left those types out: the pass
reads the body from the value, so the body adds no constant to it. -/
def Observed.withTypes (observed : Observed) : Array Name :=
  observed.type ++
    (if Declares observed.kind then observed.declaration
     else if observed.kind = .«definition» ∧ observed.result.ValueRead true then
       observed.value ++ observed.body
     else #[])

/-- The constants that the search follows from the constant (`reads`). -/
def Observed.read (observed : Observed) : Array Name :=
  observed.withTypes.filter fun target => reads ⟨observed, target⟩

/-- The reading follows only what the reading with the types follows. -/
theorem withTypes_of_read {mention : Mention} (read : Read mention) :
    mention.target ∈ mention.source.withTypes := by
  unfold Observed.withTypes
  cases read with
  | declaration declares named =>
    rcases named with named | named
    · exact Array.mem_append_left _ named
    · refine Array.mem_append_right _ ?_
      rw [ite_eq_left_of_eq_true _ _ (eq_true declares)]
      exact named
  | body definition read named =>
    refine Array.mem_append_right _ ?_
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [Declares, definition])),
      ite_eq_left_of_eq_true _ _ (eq_true ⟨definition, read⟩)]
    exact Array.mem_append_right _ named
  | type _ _ named => exact Array.mem_append_left _ named

/-- **The constants that the search follows from a constant are exactly those of `Read`.** -/
theorem mem_read (observed : Observed) (target : Name) :
    target ∈ observed.read ↔ Read ⟨observed, target⟩ := by
  unfold Observed.read
  rw [Array.mem_filter, reads_iff]
  exact ⟨And.right, fun read => ⟨withTypes_of_read read, read⟩⟩

/-- The reading follows only what the reading with the types follows. -/
theorem read_withTypes {observed : Observed} {target : Name} (read : target ∈ observed.read) :
    target ∈ observed.withTypes :=
  withTypes_of_read ((mem_read observed target).mp read)

/-! ## The reading of a term -/

/-- What `reading` reads: the record of each constant outside Lean's own library that the term
reaches by the reading with the types, the constants of the term, and those of its body that the
reading reads (`lambdaParts`, `readStep`). A constant with no record is not followed: a
constant of Lean's own library, or one that the environment does not have. -/
structure Request where
  /-- What the pass read of each constant that it read. -/
  records : Std.HashMap Name Observed
  /-- The constants that the term mentions. -/
  term : Array Name
  /-- The constants that the body of the term under its leading variables mentions, with the
  parameters of each application of a projection function and the structures of primitive
  projections left out (`readStep`). -/
  body : Array Name

/-- The constants that the reading follows from `name`: those of its record (`Observed.read`),
or none without a record. -/
def Request.readNext (request : Request) (name : Name) : Array Name :=
  match request.records[name]? with
  | some observed => observed.read
  | none => #[]

/-- The constants that the reading with the types follows from `name`. -/
def Request.withTypesNext (request : Request) (name : Name) : Array Name :=
  match request.records[name]? with
  | some observed => observed.withTypes
  | none => #[]

/-- The bound of the steps of a search over the records: one more than the number of constants
that the term and all records list. A search expands each constant one time. -/
def Request.fuel (request : Request) : Nat :=
  request.records.fold (fun total _ observed => total + observed.withTypes.size)
    (request.term.size + request.body.size + 1)

/-- The constants with a record that a term reaches: those that the search reads (`read`), and
those that it reaches by the reading with the types (`withTypes`). -/
structure Reading where
  /-- The constants with a record that the body of the term reaches by `Request.readNext`. -/
  read : Array Name
  /-- The constants with a record that the term reaches by `Request.withTypesNext`. -/
  withTypes : Array Name

/-- The two readings of the term, or `none` when a search runs out of its bound of steps
(`reading_some`). -/
def reading (request : Request) : Option Reading := do
  let read ← KernelAxioms.search request.readNext request.fuel request.body.toList
  let withTypes ← KernelAxioms.search request.withTypesNext request.fuel
    (request.term ++ request.body).toList
  let recorded (names : Std.HashSet Name) : Array Name :=
    (names.toList.filter request.records.contains).toArray
  return { read := recorded read, withTypes := recorded withTypes }

/-- **The two readings of a term.** A constant is in `read` exactly when it has a record and
the body of the term reaches it by the reading (`Read`, through `Request.readNext`), and in
`withTypes` exactly when it has a record and the term reaches it by the reading with the types.
A constant of `withTypes` that is not in `read` is reached only through a part of the term that
the reading does not read, a type of a leading variable or a parameter of a projection, or
through a step that `Read` does not take. -/
theorem reading_some {request : Request} {result : Reading}
    (returned : reading request = some result) :
    (∀ name, name ∈ result.read ↔ request.records.contains name = true ∧
      ∃ start ∈ request.body, KernelAxioms.Reach request.readNext start name) ∧
    (∀ name, name ∈ result.withTypes ↔ request.records.contains name = true ∧
      ∃ start ∈ request.term ++ request.body,
        KernelAxioms.Reach request.withTypesNext start name) := by
  unfold reading at returned
  cases readSearch : KernelAxioms.search request.readNext request.fuel request.body.toList with
  | none => simp [readSearch] at returned
  | some read =>
    cases withTypesSearch : KernelAxioms.search request.withTypesNext request.fuel
        (request.term ++ request.body).toList with
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

/-- **The reading reaches only what the reading with the types reaches.** So a registration that
the search refuses for a function that the reading reaches, it refuses also by the reading with
the types: the reading refuses no registration that the reading with the types accepts. -/
theorem read_subset_withTypes {request : Request} {result : Reading}
    (returned : reading request = some result) {name : Name} (member : name ∈ result.read) :
    name ∈ result.withTypes := by
  obtain ⟨read, withTypes⟩ := reading_some returned
  obtain ⟨recorded, start, starts, reach⟩ := (read name).mp member
  refine (withTypes name).mpr ⟨recorded, start, Array.mem_append_right _ starts, ?_⟩
  refine reach.mono fun source target step => ?_
  unfold Request.readNext at step
  unfold Request.withTypesNext
  cases found : request.records[source]? with
  | none => simp [found] at step
  | some observed =>
    simp only [found] at step ⊢
    exact read_withTypes step


/-! ## The shared functions of a registration -/

/-- The shared constants of a decision registration by one reading: each constant that
`specification` holds and that the other side holds too, the implementation (`implementation`)
or `acceptance`, with what the collector read of it (`definitions`). `widen` selects the reading
with the types (`Reading.withTypes`) over the reading (`Reading.read`), on the two terms. A
constant that `definitions` has no entry for is left out. -/
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

/-- **The reading refuses no registration that the reading with the types accepts.** Each shared
constant of the reading is a shared constant of the reading with the types, when each reading
reaches at most what the reading with the types reaches (`read_subset_withTypes`), so a function
of the class `boolean` that the record names is one that the reading with the types shares
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

/-- **What the change accepts.** A registration that the reading accepts and that the reading
with the types refuses has each of the functions of the class `boolean` that the reading with
the types shares in `throughTypes`, and the implementation does not reach any of them through
what the specification reads: for each such function, the specification does not read it, or
the implementation does not reach it and the acceptance predicate does not read it. -/
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
