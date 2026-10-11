module

public import Regula.Contract
meta import Regula.Decision

/-! # Decision evidence of a registration

What a registration whose requirement is one of the four decision structures of
`Regula.Contract` establishes, as the checker reports it: the structure (`Carrier`), the laws and
outcomes it establishes (`Carrier.facts`, proved sound and exact in `Carrier.facts_sound` and
`Carrier.facts_exact`), and whether the function it states them about is the registered
implementation (`Linkage`). Each expression and proposition is recorded as its exact term
(`Term`), beside Lean's display of it, which is of another type (`Shown`). The report is an
observation in a record part that no part a rule's decision takes includes
(`RegulaPolicy.Declaration.Reported`). The roles and the name-keyed decision give the same result
whatever the records report (`RegulaPolicy.authorize_withEvidence`,
`RegulaPolicy.policyForName_withEvidence`), and so does the decision on a member when the
inventory's reports and the member's are replaced together (`RegulaPolicy.policyFor_withEvidence`).
The exception is the admission boundary of a supplied record
(`RegulaPolicy.recordFailure`): it compares whole records, so it refuses a supplied record whose
report differs from the inventory's.
Which carriers discharge a `@[regula_decision]` registration is RG1008's decision, which reads the
kind of the recorded contract (`RegulaPolicy.DecisionKind`) and not this report;
`RegulaPolicy.Carrier.kind?_ofStructureName?` states that the law `Regula.DecisionEquivalence`
has no kind. -/

@[expose] public section

namespace RegulaPolicy

universe u v

/-- The structure of `Regula.Contract` to which a registration's requirement reduces, among the
four that state laws of a decision: the three kinds and the law `Regula.DecisionEquivalence`
(`Carrier.structureName`); parsing cannot manufacture an unknown constructor. -/
inductive Carrier where
  /-- `Regula.DecidesSoundly`. -/
  | «sound»
  /-- `Regula.DecidesCompletely`. -/
  | «complete»
  /-- `Regula.Decides`. -/
  | «soundAndComplete»
  /-- `Regula.DecisionEquivalence`: both directions, no witness. -/
  | «equivalence»
  deriving Repr, DecidableEq, Inhabited

/-- The carrier's text in reports (`sound`, `complete`, `sound-and-complete` or `equivalence`);
`parse?` reads it back (`Carrier.roundtrip`). -/
def Carrier.spelling : Carrier → String
  | .«sound» => "sound"
  | .«complete» => "complete"
  | .«soundAndComplete» => "sound-and-complete"
  | .«equivalence» => "equivalence"

/-- The carrier a text names; `none` for any text that is not a `spelling`
(`Carrier.canonical`). -/
@[regula_decision]
def Carrier.parse? : String → Option Carrier
  | "sound" => some .«sound»
  | "complete" => some .«complete»
  | "sound-and-complete" => some .«soundAndComplete»
  | "equivalence" => some .«equivalence»
  | _ => none

instance : ToString Carrier := ⟨Carrier.spelling⟩

/-- Every value survives its actual spelling parser. -/
@[simp] theorem Carrier.roundtrip (x : Carrier) : parse? x.spelling = some x := by
  cases x <;> rfl

/-- The parser accepts only the canonical spelling of its result. -/
theorem Carrier.canonical (s : String) (x : Carrier) (h : parse? s = some x) :
    x.spelling = s := by
  unfold parse? at h
  split at h <;> cases h <;> rfl

/-- The structure of `Regula.Contract` whose proof a registration with each carrier requires. -/
def Carrier.structureName : Carrier → Lean.Name
  | .«sound» => ``Regula.DecidesSoundly
  | .«complete» => ``Regula.DecidesCompletely
  | .«soundAndComplete» => ``Regula.Decides
  | .«equivalence» => ``Regula.DecisionEquivalence

/-- The carrier whose structure `name` is; `none` for every other name
(`Carrier.ofStructureName?_eq_some_iff`). The collector applies it to the head constant of a
registration's reduced requirement. -/
@[regula_decision]
def Carrier.ofStructureName? : Lean.Name → Option Carrier
  | .str (.str .anonymous "Regula") "DecidesSoundly" => some .«sound»
  | .str (.str .anonymous "Regula") "DecidesCompletely" => some .«complete»
  | .str (.str .anonymous "Regula") "Decides" => some .«soundAndComplete»
  | .str (.str .anonymous "Regula") "DecisionEquivalence" => some .«equivalence»
  | _ => none

/-- A name is read as a carrier exactly when it is that carrier's structure. -/
theorem Carrier.ofStructureName?_eq_some_iff (name : Lean.Name) (carrier : Carrier) :
    ofStructureName? name = some carrier ↔ name = carrier.structureName := by
  constructor
  · intro h
    unfold ofStructureName? at h
    split at h <;> cases h <;> rfl
  · rintro rfl
    cases carrier <;> rfl

/-- Every carrier (`Carrier.mem_all`). -/
def Carrier.all : Array Carrier := #[.«sound», .«complete», .«soundAndComplete», .«equivalence»]

/-- Each carrier is listed. A new carrier is a new constructor, and this theorem fails until
`all` lists it. -/
theorem Carrier.mem_all (carrier : Carrier) : carrier ∈ all := by
  cases carrier <;> simp [all]

/-- The structure of each carrier, the constants to which a registration's requirement reduces
when it states one (`Carrier.mem_structureNames_iff`). -/
def Carrier.structureNames : Array Lean.Name := all.map structureName

/-- A name is listed exactly when it is read as a carrier (`ofStructureName?`). -/
theorem Carrier.mem_structureNames_iff (name : Lean.Name) :
    name ∈ structureNames ↔ (ofStructureName? name).isSome := by
  simp only [structureNames, Array.mem_map, Option.isSome_iff_exists,
    ofStructureName?_eq_some_iff]
  constructor
  · rintro ⟨carrier, -, rfl⟩
    exact ⟨carrier, rfl⟩
  · rintro ⟨carrier, rfl⟩
    exact ⟨carrier, mem_all carrier, rfl⟩

/-- `Carrier.parse?` accepts exactly the spellings. -/
theorem Carrier.checked_parse : Regula.ExecutableContract Carrier.parse?
    (Regula.Decides (·.isSome = true) fun text => ∃ x : Carrier, text = x.spelling) :=
  ⟨.of_roundtrip roundtrip canonical .«sound» (unwritten := "") rfl⟩

/-- `Carrier.ofStructureName?` accepts exactly the four structures' names
(`Carrier.ofStructureName?_eq_some_iff`): the collector reads a registration's carrier with it. -/
theorem Carrier.checked_ofStructureName :
    Regula.ExecutableContract Carrier.ofStructureName?
      (Regula.Decides (·.isSome = true) fun name =>
        ∃ carrier : Carrier, name = carrier.structureName) :=
  ⟨.of_roundtrip (fun carrier => (ofStructureName?_eq_some_iff _ carrier).mpr rfl)
    (fun name carrier read => ((ofStructureName?_eq_some_iff name carrier).mp read).symm)
    .«equivalence» (unwritten := .anonymous) rfl⟩

/-- The proposition that a registration with the carrier proves of `accepts`, `spec` and `f`:
the carrier's structure applied to them. -/
def Carrier.Holds {α : Sort u} {ρ : Sort v} :
    Carrier → (ρ → Prop) → (α → Prop) → (α → ρ) → Prop
  | .«sound», accepts, spec, f => Regula.DecidesSoundly accepts spec f
  | .«complete», accepts, spec, f => Regula.DecidesCompletely accepts spec f
  | .«soundAndComplete», accepts, spec, f => Regula.Decides accepts spec f
  | .«equivalence», accepts, spec, f => Regula.DecisionEquivalence accepts spec f

/-- A statement that a carrier can establish of `accepts`, `spec` and `f`: one of the two
directional laws, which quantify over every input, or one of the four outcomes, each the
existence of an input (`Fact.Holds`). An outcome is a proposition in `Prop`: it names no input
that a program could compute. -/
inductive Fact where
  /-- The law of soundness: every input `f` accepts satisfies the specification. -/
  | «sound»
  /-- The law of completeness: `f` accepts every input that satisfies the specification. -/
  | «complete»
  /-- `f` accepts some input. -/
  | «accepted»
  /-- `f` refuses some input. -/
  | «refused»
  /-- Some input satisfies the specification. -/
  | «satisfiable»
  /-- Some input does not satisfy the specification. -/
  | «refutable»
  deriving Repr, DecidableEq, Inhabited

/-- The fact's text in reports. -/
def Fact.spelling : Fact → String
  | .«sound» => "sound"
  | .«complete» => "complete"
  | .«accepted» => "accepted"
  | .«refused» => "refused"
  | .«satisfiable» => "satisfiable"
  | .«refutable» => "refutable"

/-- The fact is a law, a statement about every input, and not an outcome. -/
def Fact.law : Fact → Bool
  | .«sound» | .«complete» => true
  | .«accepted» | .«refused» | .«satisfiable» | .«refutable» => false

/-- The proposition the fact states of `accepts`, `spec` and `f`. -/
def Fact.Holds {α : Sort u} {ρ : Sort v} :
    Fact → (ρ → Prop) → (α → Prop) → (α → ρ) → Prop
  | .«sound», accepts, spec, f => ∀ x, accepts (f x) → spec x
  | .«complete», accepts, spec, f => ∀ x, spec x → accepts (f x)
  | .«accepted», accepts, _, f => ∃ x, accepts (f x)
  | .«refused», accepts, _, f => ∃ x, ¬ accepts (f x)
  | .«satisfiable», _, spec, _ => ∃ x, spec x
  | .«refutable», _, spec, _ => ∃ x, ¬ spec x

/-- The facts a registration with the carrier establishes, laws first: the sound kind its law,
the input it accepts and, through that input, a satisfying input; the complete kind its law, the
input it refuses and, through that input, an input that fails the specification; the two-way kind
all six; and the law `Regula.DecisionEquivalence` its two laws and no outcome. Each listed fact
holds of every registration with the carrier (`Carrier.facts_sound`), and each other fact fails
for some (`Carrier.facts_exact`). -/
def Carrier.facts : Carrier → List Fact
  | .«sound» => [.«sound», .«accepted», .«satisfiable»]
  | .«complete» => [.«complete», .«refused», .«refutable»]
  | .«soundAndComplete» =>
      [.«sound», .«complete», .«accepted», .«refused», .«satisfiable», .«refutable»]
  | .«equivalence» => [.«sound», .«complete»]

/-- Every fact that `Carrier.facts` lists for a carrier holds of every `accepts`, `spec` and `f`
of which the carrier holds. The outcomes come from the witness fields and from
`Regula.DecidesSoundly.satisfiable` and `Regula.DecidesCompletely.refutable`, the laws from the
direction fields and from `Regula.DecisionEquivalence.sound` and `complete`. -/
theorem Carrier.facts_sound {α : Sort u} {ρ : Sort v} {accepts : ρ → Prop} {spec : α → Prop}
    {f : α → ρ} (carrier : Carrier) (holds : carrier.Holds accepts spec f) :
    ∀ fact ∈ carrier.facts, fact.Holds accepts spec f := by
  cases carrier <;> simp only [facts, List.mem_cons, List.not_mem_nil, or_false] <;>
    rintro fact (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [Holds] at holds
  all_goals first
    | exact holds.sound | exact holds.complete | exact holds.accepted | exact holds.refused
    | exact holds.satisfiable | exact holds.refutable
    | exact holds.toDecidesSoundly.satisfiable | exact holds.toDecidesCompletely.refutable

/-- No fact that `Carrier.facts` leaves out of a carrier's list follows from the carrier: for each
such fact, some `accepts`, `spec` and `f` satisfy the carrier and not the fact. So the list is
exactly what a registration with the carrier establishes in general; in particular the law
`Regula.DecisionEquivalence` establishes no outcome. -/
theorem Carrier.facts_exact (carrier : Carrier) (fact : Fact) (absent : fact ∉ carrier.facts) :
    ∃ (α ρ : Type) (accepts : ρ → Prop) (spec : α → Prop) (f : α → ρ),
      carrier.Holds accepts spec f ∧ ¬ fact.Holds accepts spec f := by
  cases carrier <;> cases fact <;> simp [facts] at absent
  -- The sound kind on `Bool`, accepting `true` for a specification that every input satisfies:
  -- `false` is refused although it satisfies the specification.
  · exact ⟨Bool, Bool, (· = true), fun _ => True, id,
      ⟨fun _ _ => trivial, ⟨true, rfl⟩⟩, fun law => Bool.false_ne_true (law false trivial)⟩
  -- The sound kind on `Unit`, accepting every input of a specification every input satisfies.
  · exact ⟨Unit, Unit, fun _ => True, fun _ => True, id,
      ⟨fun _ _ => trivial, ⟨(), trivial⟩⟩, fun ⟨_, refused⟩ => refused trivial⟩
  · exact ⟨Unit, Unit, fun _ => True, fun _ => True, id,
      ⟨fun _ _ => trivial, ⟨(), trivial⟩⟩, fun ⟨_, fails⟩ => fails trivial⟩
  -- The complete kind on `Bool`, accepting `true` for a specification no input satisfies:
  -- `true` is accepted although it does not satisfy the specification.
  · exact ⟨Bool, Bool, (· = true), fun _ => False, id,
      ⟨fun _ holds => holds.elim, ⟨false, Bool.false_ne_true⟩⟩, fun law => law true rfl⟩
  -- The complete kind on `Unit`, refusing every input of a specification no input satisfies.
  · exact ⟨Unit, Unit, fun _ => False, fun _ => False, id,
      ⟨fun _ holds => holds, ⟨(), id⟩⟩, fun ⟨_, accepted⟩ => accepted⟩
  · exact ⟨Unit, Unit, fun _ => False, fun _ => False, id,
      ⟨fun _ holds => holds, ⟨(), id⟩⟩, fun ⟨_, holds⟩ => holds⟩
  -- The law on the empty domain, where no input exists (`Regula.DecisionEquivalence.of_empty`).
  all_goals exact ⟨Empty, Unit, fun _ => True, fun _ => True, Empty.elim,
    ⟨fun x => x.elim⟩, fun ⟨x, _⟩ => x.elim⟩

/-- Why the law observer draws no linkage conclusion from a registration. Either keeps the
registration's exact relation in its report; neither refuses the registration. -/
inductive Unlinked where
  /-- The function the requirement states its laws about is not of the one form the observer
  reads: a constant under applications of `Function.uncurry`, whose result is not a function.
  A field application or an erasure of `Regula.Contract` is not read, although the kinds admit
  them; the reason names the form. -/
  | unsupported (reason : String)
  /-- The function is of that form, but its constant is not the registered implementation, or
  it is the implementation at universe levels other than those at which the registration names it,
  or those levels are not the registration's own universe parameters. -/
  | mismatch (reason : String)
  deriving Repr, DecidableEq

/-- The reason's text. -/
def Unlinked.reason : Unlinked → String
  | .unsupported reason | .mismatch reason => reason

/-- What the law observer reads, from the kernel-checked requirement, of the function a carrier
states its laws about. -/
structure DecidedObservation where
  /-- The applications of `Function.uncurry`, at its three implicit arguments, around the core. -/
  uncurries : Nat
  /-- The constant at the core under those applications; `none` when the core is not a
  constant. -/
  core : Option Lean.Name
  /-- The core names its constant at exactly the universe levels at which the registration names
  its implementation. -/
  sameLevels : Bool
  /-- Those levels are universe parameters of the registration, no two the same, so a law about
  the constant at them holds of every universe instance of the constant. -/
  ownParameters : Bool
  /-- The number of arguments that a result of the function takes: the leading binders of the
  carrier's result type, with every definition unfolded. -/
  unsupplied : Nat
  deriving Repr, DecidableEq

/-- The function is the registered implementation `implementation` on every argument, at the
registration's own universe parameters: its core is that constant at those levels, under some
applications of `Function.uncurry`, which is a bijection between the curried and the uncurried
function (`Function.curry_uncurry`), and its result takes no argument. -/
def DecidedObservation.Linked (implementation : Lean.Name) (o : DecidedObservation) : Prop :=
  o.core = some implementation ∧ o.sameLevels = true ∧ o.ownParameters = true ∧ o.unsupplied = 0

/-- Why the observation does not link the function to `implementation`, or `none` when it does
(`DecidedObservation.unlinked?_eq_none_iff`). -/
@[regula_decision]
def DecidedObservation.unlinked? (implementation : Lean.Name) (o : DecidedObservation) :
    Option Unlinked :=
  match o.core with
  | none => some (.unsupported "the function is not a constant under `Function.uncurry`; a \
      field application, an erasure or another form is not read")
  | some core =>
    if core ≠ implementation then
      some (.mismatch s!"the function is `{core}`, not the implementation `{implementation}`")
    else if !o.sameLevels then
      some (.mismatch s!"the function names `{core}` at universe levels other than those of the \
        registered implementation")
    else if !o.ownParameters then
      some (.mismatch s!"the function names `{core}` at universe levels that are not the \
        registration's own parameters")
    else if o.unsupplied != 0 then
      some (.unsupported s!"the result of the function takes {o.unsupplied} more argument(s)")
    else none

/-- The observer links exactly the observations that `DecidedObservation.Linked` describes. -/
theorem DecidedObservation.unlinked?_eq_none_iff (implementation : Lean.Name)
    (o : DecidedObservation) : o.unlinked? implementation = none ↔ o.Linked implementation := by
  cases o with
  | mk uncurries core sameLevels ownParameters unsupplied =>
    cases core with
    | none => simp [unlinked?, Linked]
    | some core =>
      by_cases same : core = implementation
      · subst same
        cases sameLevels <;> cases ownParameters <;> by_cases zero : unsupplied = 0 <;>
          simp [unlinked?, Linked, zero]
      · simp [unlinked?, Linked, same]

/-- The observer's linkage is exact (`DecidedObservation.unlinked?_eq_none_iff`): it links the
implementation's constant itself, and refuses an observation whose core is not a constant. -/
theorem DecidedObservation.checked_unlinked :
    Regula.ExecutableContract DecidedObservation.unlinked? (fun observe =>
      Regula.Decides (· = none)
        (fun input : Lean.Name × DecidedObservation => input.2.Linked input.1)
        (Function.uncurry observe)) :=
  ⟨.of_iff (fun input => unlinked?_eq_none_iff input.1 input.2)
    ⟨(`f, ⟨0, some `f, true, true, 0⟩), (unlinked?_eq_none_iff _ _).mpr ⟨rfl, rfl, rfl, rfl⟩⟩
    ⟨(`f, ⟨0, none, true, true, 0⟩), fun linked =>
      nomatch ((unlinked?_eq_none_iff _ _).mp linked).1⟩⟩

/-- A universe level of a `Term`, as one entry of its table of levels: each argument that is a
level is the position of an earlier entry of the same table. -/
inductive LevelNode where
  /-- `Level.zero`. -/
  | zero
  /-- `Level.succ` of the entry at `of`. -/
  | succ (of : Nat)
  /-- `Level.max` of two entries. -/
  | max (left right : Nat)
  /-- `Level.imax` of two entries. -/
  | imax (left right : Nat)
  /-- A universe parameter. -/
  | param (name : Lean.Name)
  /-- A universe metavariable. -/
  | mvar (name : Lean.Name)
  deriving Repr, DecidableEq, Inhabited

/-- How a binder of a `Term` binds its variable: Lean's `BinderInfo`, which does not derive
`DecidableEq`. -/
inductive Binding where
  /-- An explicit binder. -/
  | «default»
  /-- An implicit binder. -/
  | implicit
  /-- A strict implicit binder. -/
  | strictImplicit
  /-- An instance-implicit binder. -/
  | instImplicit
  deriving Repr, DecidableEq, Hashable, Inhabited

/-- A subterm of a `Term`, as one entry of its table of subterms: each argument that is a subterm
is the position of an earlier entry of the same table, and each argument that is a level is a
position in the table of levels. The constructors are those of Lean's `Expr` except metadata
(`Expr.mdata`), which is no part of the term that Lean's kernel checks: a subterm with metadata
is recorded as the subterm under it. -/
inductive TermNode where
  /-- A bound variable, by its de Bruijn index. -/
  | bvar (index : Nat)
  /-- A free variable, by the name of its identifier. -/
  | fvar (name : Lean.Name)
  /-- A metavariable, by the name of its identifier. -/
  | mvar (name : Lean.Name)
  /-- A sort at a level. -/
  | sort (level : Nat)
  /-- A constant at its universe levels. -/
  | const (name : Lean.Name) (levels : List Nat)
  /-- An application of a function to one argument. -/
  | app (function argument : Nat)
  /-- A function abstraction. -/
  | lam (binder : Lean.Name) (type body : Nat) (binding : Binding)
  /-- A dependent function type. -/
  | forallE (binder : Lean.Name) (type body : Nat) (binding : Binding)
  /-- A local definition. -/
  | letE (binder : Lean.Name) (type value body : Nat) (nondep : Bool)
  /-- A natural-number literal. -/
  | natLit (value : Nat)
  /-- A string literal. -/
  | strLit (value : String)
  /-- A projection of a structure value. -/
  | proj (typeName : Lean.Name) (index : Nat) (value : Nat)
  deriving Repr, DecidableEq, Hashable, Inhabited

/-- An elaborated Lean term, node by node: the table of its universe levels and the table of its
subterms, in which each subterm comes after the subterms it contains and the last entry is the
term. A subterm that occurs several times has one entry, so the table grows with the number of
distinct subterms. No limit of a printer applies to it, and it keeps every implicit argument and
every universe level that the term has. -/
structure Term where
  /-- The universe levels, each after the levels it contains. -/
  levels : Array LevelNode
  /-- The subterms, each after the subterms it contains; the last is the term. -/
  nodes : Array TermNode
  deriving Repr, DecidableEq, Inhabited

/-- An expression of a report: the exact term, and Lean's display of it for a reader. The display
is pretty-printed with the notations in force, which can leave out subterms (`⋯`), implicit
arguments and universe levels, so it is never the exact value: that is `exact`, of another
type. -/
structure Shown where
  /-- The elaborated term, every node of it but its metadata. -/
  exact : Term
  /-- Lean's display of the term, for a reader only. -/
  display : String
  deriving Repr, DecidableEq, Inhabited

/-- A linkage conclusion for a carrier: the applications of `Function.uncurry` around the
implementation, and one proposition for each fact of the carrier, in the order of
`Carrier.facts`, at the registration's acceptance predicate, specification and decided function,
each as its exact term with Lean's display. The number of propositions is part of the type. -/
structure Linked (carrier : Carrier) where
  /-- The applications of `Function.uncurry` around the implementation. -/
  uncurries : Nat
  /-- The proposition of each fact of the carrier (`Fact.Holds`), in order. -/
  statements : Array Shown
  /-- There is one proposition for each fact of the carrier. -/
  exact : statements.size = carrier.facts.length
  deriving Repr, DecidableEq

/-- What the law observer concludes of a registration with the carrier. Only `linked` carries
facts, so an observation that is unsupported or does not match supplies no linkage conclusion
and no fact: there is no field to hold one. -/
inductive Linkage (carrier : Carrier) where
  /-- The decided function is the registered implementation on every argument
  (`DecidedObservation.Linked`), and these are the facts. -/
  | linked (conclusion : Linked carrier)
  /-- No conclusion, and why. -/
  | unlinked (why : Unlinked)
  deriving Repr, DecidableEq

/-- Admit the propositions of a linkage conclusion: them when there is one for each fact of the
carrier, and an error otherwise. -/
@[regula_decision]
def admitStatements (carrier : Carrier) (statements : Array Shown) :
    Except String { s : Array Shown // s.size = carrier.facts.length } :=
  if exact : statements.size = carrier.facts.length then .ok ⟨statements, exact⟩
  else .error s!"linkage of a {carrier.spelling} carrier has {statements.size} proposition(s), \
    not {carrier.facts.length}"

/-- The propositions are admitted exactly when there is one for each fact. -/
theorem admitStatements_isOk_iff (input : Carrier × Array Shown) :
    Regula.Dependent.isOk (fun input : Carrier × Array Shown => admitStatements input.1 input.2)
        input = true ↔ input.2.size = input.1.facts.length := by
  unfold Regula.Dependent.isOk admitStatements
  by_cases exact : input.2.size = input.1.facts.length <;> simp [exact, Except.isOk, Except.toBool]

/-- `admitStatements` accepts exactly the propositions of the right number
(`admitStatements_isOk_iff`): it accepts two for the law and refuses none for it. -/
theorem checked_admitStatements :
    Regula.ExecutableContract admitStatements (fun admit =>
      Regula.Decides (· = true)
        (fun input : Carrier × Array Shown => input.2.size = input.1.facts.length)
        (Regula.Dependent.isOk (fun input : Carrier × Array Shown => admit input.1 input.2))) :=
  ⟨.of_iff admitStatements_isOk_iff
    ⟨(.«equivalence», #[default, default]), by decide⟩
    ⟨(.«equivalence», #[]), by decide⟩⟩

/-- The checker's report of one registration whose requirement reduces to a carrier: the exact
relation, each part as its exact term with Lean's display of it (`Shown`), and the law observer's
linkage conclusion. It is an observation of the registration it belongs to. What the decisions do
with it is stated by `RegulaPolicy.policyFor_withEvidence` and its companions, and the admission
boundary of a supplied record (`RegulaPolicy.recordFailure`) compares it as part of the whole
record. -/
structure ContractEvidence where
  /-- The structure the requirement reduces to. -/
  carrier : Carrier
  /-- The registration's implementation expression, with its universe levels. -/
  implementation : Shown
  /-- The registration's universe parameters. -/
  universes : Array Lean.Name
  /-- The registration's requirement applied to its implementation, before any reduction. -/
  requirement : Shown
  /-- The domain of the decided function: the carrier's first type argument. -/
  domain : Shown
  /-- The result type of the decided function: the carrier's second type argument. -/
  result : Shown
  /-- The acceptance predicate. -/
  accepts : Shown
  /-- The specification. -/
  spec : Shown
  /-- The function the requirement states its laws about. -/
  decided : Shown
  /-- The linkage conclusion, with the facts, or why there is none. -/
  linkage : Linkage carrier
  deriving Repr, DecidableEq

/-- The facts of the evidence with their propositions, in the order of `Carrier.facts`: those of
its carrier when it is linked, and none otherwise. -/
def ContractEvidence.facts (e : ContractEvidence) : List (Fact × Shown) :=
  match e.linkage with
  | .linked conclusion => e.carrier.facts.zip conclusion.statements.toList
  | .unlinked _ => []

/-- Linked evidence reports each fact of its carrier, each once and in order. -/
theorem ContractEvidence.facts_linked (e : ContractEvidence) (conclusion : Linked e.carrier)
    (linked : e.linkage = .linked conclusion) :
    (e.facts.map (·.1)) = e.carrier.facts := by
  simp only [facts, linked]
  apply List.map_fst_zip
  simp [conclusion.exact]

/-- Evidence that is not linked reports no fact. -/
theorem ContractEvidence.facts_unlinked (e : ContractEvidence) (why : Unlinked)
    (unlinked : e.linkage = .unlinked why) : e.facts = [] := by
  simp only [facts, unlinked]

/-- The evidence as the `--verbose` line of its declaration shows it: the carrier, the decided
function, and the linkage with each fact and its proposition, or the state and the reason of no
linkage. Each expression is shown by its display, which a reader of the line takes as a display:
the exact terms are in the JSON record. -/
def ContractEvidence.text (e : ContractEvidence) : String :=
  s!"contract-evidence={e.carrier.spelling} decided={e.decided.display} " ++
    match e.linkage with
    | .linked conclusion =>
      s!"linked uncurries={conclusion.uncurries} facts=[" ++
        "; ".intercalate (e.facts.map fun (fact, statement) =>
          s!"{fact.spelling}: {statement.display}") ++
        "]"
    | .unlinked (.unsupported reason) => s!"unsupported: {reason}"
    | .unlinked (.mismatch reason) => s!"mismatch: {reason}"

end RegulaPolicy
