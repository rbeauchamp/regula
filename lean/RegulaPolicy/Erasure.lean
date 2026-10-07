module

public import Lean.Expr
public import Regula.Contract
meta import Regula.Decision

/-! # Equality up to compilation erasure

The pure decision of the recursion-helper comparison (RG1006):
whether each definition that Lean's recursion compiler regenerated from a helper is, up to what
compilation erases, the observed definition of its name.

The comparison is split in two. An observing pass (`Regula.Collect.observeEqual`) runs in
`MetaM` and records, for the terms it is asked about, `Observations`: whether a term is a proof or
a type, the variable a binder's body is read with, and a decomposition of a `match` application
whose threading law Lean's kernel checked. `reproduces` is the decision. It is a pure, total
function of the regenerated and the observed values, of those observations and of whether the
pass finished, and of nothing else: no environment, no attribute, no reducibility status and no
name the audited project can write is among its arguments. What selects a regeneration (a
termination argument, a status assignment, matcher metadata) is therefore not an argument of the
decision.

`EqualWithin` is the relation the decision is proved against: one constructor for each rule the
comparison applies. `equalWithin_iff` proves that the executed comparison answers `true` exactly
for the related terms, for every pair of terms and every observation, and `checked_reproduces`
registers the kind.

**Not claimed.** The theorem starts from the observations: that an observation is what Lean
answers for the term is the observing pass's, and is not proved. That two related terms compile
to code that computes the same is the adequacy of the relation, which is argued in
`docs/guides/proofs-and-boundaries.md` and is not a theorem. `Expr` equality, free-variable
tests, instantiation and the equality of names, universe levels and literals are Lean's own
functions, which the relation names as the comparison runs them. -/

@[expose] public section

namespace RegulaPolicy.Erasure
open Lean (Expr FVarId Name Level)

/-- One of the two terms compared. In `reproduces` the left one is a regenerated value and the
right one the observed value of its name. -/
inductive Side where
  /-- The first term. -/
  | left
  /-- The second term. -/
  | right
  deriving Repr, DecidableEq, Inhabited

/-- The other side. -/
def Side.other : Side → Side
  | .left => .right
  | .right => .left

/-- The pairs under which the variables of the two terms are read: `(x, y)` says that `x` in the
left term and `y` in the right term are the same variable. -/
abbrev Pairs := Array (FVarId × FVarId)

/-- A decomposition of the arguments of a `match` application `M ps motive ds alts v rest…`: how
many parameters `ps` come before the motive, how many discriminants `ds` after it, and for each
alternative how many pattern variables it binds. The observing pass records one for an
application only where Lean's kernel checked the threading law of that application for exactly
this decomposition (`Observations.threading`). -/
structure Threading where
  /-- The parameters before the motive. -/
  params : Nat
  /-- The discriminants after the motive. -/
  discriminants : Nat
  /-- For each alternative, in order, the pattern variables it binds. -/
  alternatives : Array Nat
  /-- The position of the motive's universe level among the levels of the constant, if it has
  one. -/
  motiveLevel : Option Nat
  deriving Repr, DecidableEq, Inhabited

/-- The arguments before the alternatives: the parameters, the motive and the discriminants. -/
def Threading.head (shape : Threading) : Nat := shape.params + 1 + shape.discriminants

/-- Whether the levels `us` and `vs` of the constant agree apart from the motive's level, which
the binder a threaded `match` adds to its motive changes. -/
def Threading.sameLevels (shape : Threading) (us vs : List Level) : Bool :=
  match shape.motiveLevel with
  | some position =>
    us.toArray.eraseIdxIfInBounds position == vs.toArray.eraseIdxIfInBounds position
  | none => us.toArray == vs.toArray

/-- The levels `us` and `vs` of the constant agree apart from the motive's level, as a
proposition stated with Lean's own comparison of levels (`==`). `Threading.sameLevels` decides
it (`Threading.sameLevels_iff`). -/
def Threading.SameLevels (shape : Threading) (us vs : List Level) : Prop :=
  match shape.motiveLevel with
  | some position =>
    (us.toArray.eraseIdxIfInBounds position == vs.toArray.eraseIdxIfInBounds position) = true
  | none => (us.toArray == vs.toArray) = true

/-- The executed test accepts exactly the levels that agree apart from the motive's. -/
theorem Threading.sameLevels_iff (shape : Threading) (us vs : List Level) :
    shape.sameLevels us vs = true ↔ shape.SameLevels us vs := by
  unfold Threading.sameLevels Threading.SameLevels
  split <;> exact Iff.rfl

/-- What the observing pass shows of the terms of one side. Each field answers for a term as it
stands under the variables the pass bound, and `none` says that the pass was not asked about it.
`erased` and `threading` are toolchain observations: what Lean answers, or what its kernel
checked, at inspection. Both depend on state the audited project writes. Lean's answer for `erased`
reads reducibility statuses. For `threading`, what Lean records about the applied constant gives
the decomposition, and what the pass records is that the kernel checked the threading law for
it. `bound` is the pass's own choice of a variable, and the comparison does not rely on it: it
refuses a variable that a pair holds (`newVariables`), and a pair holds every variable it read a
body with on the path to the term (`unpaired_push`, `alternative_holds`, `Reached.holds`).

A regenerated or observed value is closed, and the comparison reads a body only with the variable
`bound` gives its binder, so a term with a free variable names the binders it is under. -/
structure Observations where
  /-- Whether the term is a proof or a type in its own local context: what Lean's code generator
  erases (`Meta.isProof` or `Meta.isType`). -/
  erased : Expr → Option Bool
  /-- For a binder (`fun`, `∀` or `let`): the variable its body is read with. The pass declares it
  with the binder's own type, and for a `let` its value. -/
  bound : Expr → Option FVarId
  /-- For an application: `some none` where the pass found no decomposition whose threading law
  the kernel checked, and `some (some shape)` where Lean's kernel checked, with no axiom outside
  Standard-Logical, the threading law of the application for `shape`: with `M` the applied
  constant, `ps` its first `shape.params` arguments and the next one the motive
  `fun ds => A ds → R ds`,

  `∀ ds alts (w : A ds), M ps (fun ds => A ds → R ds) ds alts w = M ps R ds (fun xs => altsᵢ xs w)`

  where alternative `i` binds `shape.alternatives[i]` pattern variables `xs`. What Lean records
  about `M` only proposes the decomposition; the kernel's check is what is recorded. -/
  threading : Expr → Option (Option Threading)

/-- An observation the comparison needs and was not given. -/
inductive Need where
  /-- Whether `term`, of `side`, is erased. -/
  | erased (side : Side) (term : Expr)
  /-- The variable of `binder`, of `side`. -/
  | bound (side : Side) (binder : Expr)
  /-- The checked decomposition of `application`, of `side`. -/
  | threading (side : Side) (application : Expr)

/-- Two terms to compare, with the pairs their variables are read under. -/
structure Part where
  /-- The pairs of variables. -/
  pairs : Pairs
  /-- The left term. -/
  left : Expr
  /-- The right term. -/
  right : Expr

/-- Why a step does not reduce comparing two terms to comparing parts. -/
inductive Refusal where
  /-- The terms are not equal up to erasure. -/
  | different
  /-- The step needs an observation it was not given. Without it the terms are not accepted. -/
  | unobserved (need : Need)

/-- What comparing two terms comes to in one step: the parts whose terms must all be equal for
the two terms to be equal up to erasure (none, where the step itself settles that they are), or
the refusal. -/
abbrev Step := Except Refusal (List Part)

/-- The part that compares `threaded`, a term of `side`, with `direct`, a term of the other
side. -/
def Side.orient (side : Side) (pairs : Pairs) (threaded direct : Expr) : Part :=
  match side with
  | .left => ⟨pairs, threaded, direct⟩
  | .right => ⟨pairs, direct, threaded⟩

/-- `Side.orient` keeps the pairs it was given. -/
theorem Side.orient_pairs (side : Side) (pairs : Pairs) (threaded direct : Expr) :
    (side.orient pairs threaded direct).pairs = pairs := by
  cases side <;> rfl

/-- The pair that reads `x`, a variable of `side`, and `y`, a variable of the other side, as the
same variable. -/
def Side.pair (side : Side) (x y : FVarId) : FVarId × FVarId :=
  match side with
  | .left => (x, y)
  | .right => (y, x)

/-- The parts that compare the terms of `xs` and `ys` position by position, each under `pairs`. -/
def paired (pairs : Pairs) (xs ys : Array Expr) : List Part :=
  (xs.toList.zip ys.toList).map fun (x, y) => ⟨pairs, x, y⟩

/-- A part that `paired` yields has the pairs it was given. -/
theorem pairs_of_mem_paired {pairs : Pairs} {xs ys : Array Expr} {part : Part}
    (member : part ∈ paired pairs xs ys) : part.pairs = pairs := by
  obtain ⟨⟨x, y⟩, _, rfl⟩ := List.mem_map.mp member
  rfl

/-- Whether no pair of `pairs` holds the variable `x`, on either side (`unpaired_eq_true_iff`).
Two variables are compared by their names, which is all a variable is, so that a theorem can
state that a pair holds a variable. -/
def unpaired (pairs : Pairs) (x : FVarId) : Bool :=
  pairs.all fun pair => pair.1.name != x.name && pair.2.name != x.name

/-- Whether the variables `introduced` are new: no pair of `pairs` holds one of them, on either
side, and no two of them are the same (`newVariables_eq_true_iff`). Two variables are compared by
their names, as in `unpaired`. The comparison reads a body only with new variables, and
the part for that body holds each of them in a pair (`unpaired_push`, `alternative_holds`). So a
later binder on the path is refused that variable (`Reached.newVariables_eq_false`). -/
def newVariables (pairs : Pairs) : List FVarId → Bool
  | [] => true
  | x :: rest =>
    unpaired pairs x && rest.all (fun y => y.name != x.name) && newVariables pairs rest

/-- `unpaired` reads the pairs of two arrays one array after the other: no pair of the two holds
a variable exactly where no pair of either holds it. -/
theorem unpaired_append (pairs more : Pairs) (x : FVarId) :
    unpaired (pairs ++ more) x = (unpaired pairs x && unpaired more x) := by
  simp [unpaired]

/-- A variable that a pair of `pairs` holds, on either side, is not unpaired. -/
theorem unpaired_eq_false_of_mem {pairs : Pairs} {pair : FVarId × FVarId} {x : FVarId}
    (member : pair ∈ pairs) (holds : pair.1 = x ∨ pair.2 = x) : unpaired pairs x = false := by
  cases free : unpaired pairs x with
  | false => rfl
  | true =>
    have each := Array.all_eq_true'.mp free pair member
    rcases holds with rfl | rfl <;> simp at each

/-- `unpaired` answers `true` exactly where no pair holds the variable, on either side. -/
theorem unpaired_eq_true_iff (pairs : Pairs) (x : FVarId) :
    unpaired pairs x = true ↔ ∀ pair ∈ pairs, pair.1 ≠ x ∧ pair.2 ≠ x := by
  have named : ∀ y : FVarId, (y.name != x.name) = true ↔ y ≠ x := by
    intro y
    cases x
    cases y
    simp
  simp only [unpaired, Array.all_eq_true', Bool.and_eq_true, named]

/-- The variables are new exactly where no pair holds one of them, on either side, and no two of
them are the same. -/
theorem newVariables_eq_true_iff (pairs : Pairs) :
    ∀ variables : List FVarId,
      newVariables pairs variables = true ↔
        (∀ x ∈ variables, unpaired pairs x = true) ∧ variables.Nodup
  | [] => by simp [newVariables]
  | x :: rest => by
    have named : ∀ y : FVarId, (y.name != x.name) = true ↔ y ≠ x := by
      intro y
      cases x
      cases y
      simp
    have differs : (rest.all fun y => y.name != x.name) = true ↔ x ∉ rest := by
      simp only [List.all_eq_true, named]
      exact ⟨fun each member => each x member rfl, fun absent y member same =>
        absent (same ▸ member)⟩
    simp only [newVariables, Bool.and_eq_true, differs, newVariables_eq_true_iff pairs rest,
      List.mem_cons, forall_eq_or_imp, List.nodup_cons]
    constructor
    · rintro ⟨⟨free, absent⟩, others, distinct⟩
      exact ⟨⟨free, others⟩, absent, distinct⟩
    · rintro ⟨⟨free, others⟩, absent, distinct⟩
      exact ⟨⟨free, absent⟩, others, distinct⟩

/-- A variable that a pair holds is not new: `newVariables` refuses every list that has it. -/
theorem newVariables_eq_false_of_held {pairs : Pairs} {x : FVarId}
    (held : unpaired pairs x = false) :
    ∀ {variables : List FVarId}, x ∈ variables → newVariables pairs variables = false
  | [], member => by cases member
  | y :: rest, member => by
    rcases List.mem_cons.mp member with rfl | later
    · simp [newVariables, held]
    · simp [newVariables, newVariables_eq_false_of_held held later]

/-- The variables are new, as a proposition: no pair of `pairs` holds one of them, on either
side, and no two of them are the same. `newVariables` decides it (`newVariables_iff`). -/
def NewVariables (pairs : Pairs) (variables : List FVarId) : Prop :=
  (∀ x ∈ variables, ∀ pair ∈ pairs, pair.1 ≠ x ∧ pair.2 ≠ x) ∧ variables.Nodup

/-- The executed test accepts exactly the lists of new variables. -/
theorem newVariables_iff (pairs : Pairs) (variables : List FVarId) :
    newVariables pairs variables = true ↔ NewVariables pairs variables := by
  rw [newVariables_eq_true_iff]
  simp only [NewVariables, unpaired_eq_true_iff]

/-- The arguments of a well-founded fixpoint application that carry its computation: for
`WellFounded.fix α C r hwf F x…` and `WellFounded.Nat.fix α motive h F x…` (the two combinators
Lean 4.34.0's well-founded recursion uses) the domain, the motive, the functional and the
remaining arguments, without the relation `r`, its well-foundedness proof or the measure `h`. -/
def fixpointArguments? (e : Expr) : Option (Array Expr) :=
  let args := e.getAppArgs
  if e.isAppOf ``WellFounded.fix && args.size ≥ 5 then
    some (#[args[0]!, args[1]!, args[4]!] ++ args.extract 5 args.size)
  else if e.isAppOf ``WellFounded.Nat.fix && args.size ≥ 4 then
    some (#[args[0]!, args[1]!, args[3]!] ++ args.extract 4 args.size)
  else none

/-- `arguments` are the arguments of the well-founded fixpoint application `e` that carry its
computation. This states, without `fixpointArguments?`, which arguments the `fixpoint` rule
compares: the domain, the motive, the functional and the arguments after it, and not the relation,
its well-foundedness proof or the measure. `fixpointArguments?_eq_some_iff` proves that the
executed selection is this one. -/
inductive Fixpoint : Expr → Array Expr → Prop where
  /-- `WellFounded.fix α C r hwf F x…`: without the relation `r` and its proof `hwf`. -/
  | wellFounded {e : Expr} :
      e.isAppOf ``WellFounded.fix = true → 5 ≤ e.getAppArgs.size →
      Fixpoint e (#[e.getAppArgs[0]!, e.getAppArgs[1]!, e.getAppArgs[4]!] ++
        e.getAppArgs.extract 5 e.getAppArgs.size)
  /-- `WellFounded.Nat.fix α motive h F x…`, where the first form does not apply: without the
  measure `h`. -/
  | natural {e : Expr} :
      ¬ (e.isAppOf ``WellFounded.fix = true ∧ 5 ≤ e.getAppArgs.size) →
      e.isAppOf ``WellFounded.Nat.fix = true → 4 ≤ e.getAppArgs.size →
      Fixpoint e (#[e.getAppArgs[0]!, e.getAppArgs[1]!, e.getAppArgs[3]!] ++
        e.getAppArgs.extract 4 e.getAppArgs.size)

/-- The executed selection of a fixpoint's arguments is exactly `Fixpoint`. -/
theorem fixpointArguments?_eq_some_iff (e : Expr) (arguments : Array Expr) :
    fixpointArguments? e = some arguments ↔ Fixpoint e arguments := by
  by_cases first : e.isAppOf ``WellFounded.fix = true ∧ 5 ≤ e.getAppArgs.size
  · have selected : fixpointArguments? e =
        some (#[e.getAppArgs[0]!, e.getAppArgs[1]!, e.getAppArgs[4]!] ++
          e.getAppArgs.extract 5 e.getAppArgs.size) := by
      simp [fixpointArguments?, first.1, first.2]
    constructor
    · intro found
      rw [selected] at found
      cases found
      exact .wellFounded first.1 first.2
    · intro fixpoint
      cases fixpoint with
      | wellFounded _ _ => exact selected
      | natural notFirst _ _ => exact absurd first notFirst
  · have skipped : ¬ ((e.isAppOf ``WellFounded.fix && decide (e.getAppArgs.size ≥ 5)) = true) := by
      simpa using first
    by_cases second : e.isAppOf ``WellFounded.Nat.fix = true ∧ 4 ≤ e.getAppArgs.size
    · have selected : fixpointArguments? e =
          some (#[e.getAppArgs[0]!, e.getAppArgs[1]!, e.getAppArgs[3]!] ++
            e.getAppArgs.extract 4 e.getAppArgs.size) := by
        simp [fixpointArguments?, skipped, second.1, second.2]
      constructor
      · intro found
        rw [selected] at found
        cases found
        exact .natural first second.1 second.2
      · intro fixpoint
        cases fixpoint with
        | wellFounded applies enough => exact absurd ⟨applies, enough⟩ first
        | natural _ _ _ => exact selected
    · have unselected : ¬ ((e.isAppOf ``WellFounded.Nat.fix && decide (e.getAppArgs.size ≥ 4)) =
          true) := by simpa using second
      have selected : fixpointArguments? e = none := by
        simp [fixpointArguments?, skipped, unselected]
      constructor
      · intro found
        rw [selected] at found
        cases found
      · intro fixpoint
        cases fixpoint with
        | wellFounded applies enough => exact absurd ⟨applies, enough⟩ first
        | natural _ applies enough => exact absurd ⟨applies, enough⟩ second

/-- No fixpoint arguments are selected exactly where `Fixpoint` gives none. -/
theorem fixpointArguments?_eq_none_iff (e : Expr) :
    fixpointArguments? e = none ↔ ∀ arguments, ¬ Fixpoint e arguments := by
  constructor
  · intro none arguments fixpoint
    rw [(fixpointArguments?_eq_some_iff e arguments).mpr fixpoint] at none
    cases none
  · intro none
    cases found : fixpointArguments? e with
    | none => rfl
    | some arguments =>
      exact absurd ((fixpointArguments?_eq_some_iff e arguments).mp found) (none _)

/-- The pairs under which `bound`, a variable the threaded side has just bound, stands for
`passed`, a variable of the same side: `bound` with every variable of the other side that `passed`
is paired with. `side` is the threaded side. -/
def standingFor (side : Side) (pairs : Pairs) (passed bound : FVarId) : Pairs :=
  pairs.filterMap fun (x, y) =>
    match side with
    | .left => if x.name == passed.name then some (bound, y) else none
    | .right => if y.name == passed.name then some (x, bound) else none

/-- With the threaded side on the left, `standingFor` pairs `bound` alone, and with exactly the
variables `passed` is paired with: it relates no two variables that `pairs` does not, other than
through `bound`. This states nothing about the comparison that uses the pairs. -/
theorem mem_standingFor_left (pairs : Pairs) (passed bound x y : FVarId) :
    (x, y) ∈ standingFor .left pairs passed bound ↔ x = bound ∧ (passed, y) ∈ pairs := by
  cases passed
  simp only [standingFor, Array.mem_filterMap, Prod.exists]
  constructor
  · rintro ⟨⟨a⟩, b, member, selected⟩
    split at selected <;> simp_all
  · rintro ⟨rfl, member⟩
    exact ⟨_, _, member, by simp⟩

/-- `mem_standingFor_left` with the threaded side on the right. -/
theorem mem_standingFor_right (pairs : Pairs) (passed bound x y : FVarId) :
    (x, y) ∈ standingFor .right pairs passed bound ↔ y = bound ∧ (x, passed) ∈ pairs := by
  cases passed
  simp only [standingFor, Array.mem_filterMap, Prod.exists]
  constructor
  · rintro ⟨a, ⟨b⟩, member, selected⟩
    split at selected <;> simp_all
  · rintro ⟨rfl, member⟩
    exact ⟨_, _, member, by simp⟩

/-- A term with its leading `fun` binders opened. -/
inductive Opened where
  /-- The pass gave no variable for `binder`. -/
  | unobserved (binder : Expr)
  /-- The variables of the binders opened, in order, and the term under them. -/
  | opened (variables : Array FVarId) (body : Expr)

/-- `e` with at most `count` leading `fun` binders opened, each body read with the variable
`bound` gives its binder, after the variables `xs` already opened. Only a term that is a `fun` as
it stands is opened: nothing is reduced, as in Lean's `Meta.lambdaBoundedTelescope`. -/
def openLambdas (bound : Expr → Option FVarId) : Nat → Expr → Array FVarId → Opened
  | count + 1, e@(.lam _ _ body _), xs =>
    match bound e with
    | some x => openLambdas bound count (body.instantiate1 (.fvar x)) (xs.push x)
    | none => .unobserved e
  | _, e, xs => .opened xs e

/-- The part that compares one alternative of a threaded `match` with the same alternative of the
direct one. `threaded` binds `binders` pattern variables and then one more, which stands for the
variable `passed`; `direct` binds the same pattern variables. The two bodies are compared with the
pattern variables paired in order and the further variable standing for `passed`
(`standingFor`). The variables must be new (`newVariables`): the pattern variables of both
alternatives and the further variable. A pair must hold `passed` on the threaded side, so that
`standingFor` gives the further variable a pair, and a later binder is refused that variable as
it is refused each other one. An error is the refusal the comparison comes to instead: a variable
the pass did not give, an alternative that does not bind those variables, a variable that is not
new, or a passed variable that no pair holds. `seen` holds the observations of the threaded side,
`side`, and `other` those of the direct side. -/
def alternative (side : Side) (seen other : Observations) (pairs : Pairs) (passed : FVarId)
    (binders : Nat) (threaded direct : Expr) : Except Refusal Part :=
  match openLambdas seen.bound binders threaded #[] with
  | .unobserved binder => .error (.unobserved (.bound side binder))
  | .opened xs body =>
    match openLambdas other.bound binders direct #[] with
    | .unobserved binder => .error (.unobserved (.bound side.other binder))
    | .opened ys body' =>
      if xs.size = binders ∧ ys.size = binders then
        match body with
        | .lam _ _ inner _ =>
          match seen.bound body with
          | none => .error (.unobserved (.bound side body))
          | some further =>
            if newVariables pairs (xs.toList ++ ys.toList ++ [further]) &&
                !(standingFor side pairs passed further).isEmpty then
              .ok (side.orient
                (pairs ++ (xs.zip ys).map (fun (x, y) => side.pair x y) ++
                  standingFor side pairs passed further)
                (inner.instantiate1 (.fvar further)) body')
            else .error .different
        | _ => .error .different
      else .error .different

/-- The parts that compare a threaded `match` application with the direct one, given the
arguments `targs` of the threaded application, of `side`, and `dargs` of the direct one: the
parameters, the motive, the discriminants and the arguments after the variable passed, position by
position, and then each alternative (`alternative`). The alternatives themselves and the variable
passed are not among the arguments compared position by position. An error is the refusal the
comparison comes to instead. -/
def threadedParts (side : Side) (seen other : Observations) (pairs : Pairs) (shape : Threading)
    (passed : FVarId) (targs dargs : Array Expr) : Step :=
  let count := shape.alternatives.size
  let kept := targs.extract 0 shape.head ++ targs.extract (shape.head + count + 1)
  let direct := dargs.extract 0 shape.head ++ dargs.extract (shape.head + count)
  if kept.size = direct.size then
    let outer := (kept.toList.zip direct.toList).map fun (t, d) => side.orient pairs t d
    let alternatives := shape.alternatives.toList.zipIdx.mapM fun (binders, index) =>
      match targs[shape.head + index]?, dargs[shape.head + index]? with
      | some t, some d => alternative side seen other pairs passed binders t d
      | _, _ => .error .different
    alternatives.map (outer ++ ·)
  else .error .different

/-- `threaded`, an application of `side`, is the threaded form of the `match` that `direct`
applies, under the decomposition `shape` and with the variable `passed`: it has one more argument,
both apply the same constant at levels that agree apart from the motive's, the pass recorded that
the kernel checked the threading law of `threaded` for `shape`, and the argument after the
alternatives is the variable `passed`. `seen` holds the observations of `side`. -/
structure Threads (seen : Observations) (threaded direct : Expr) (shape : Threading)
    (passed : FVarId) : Prop where
  /-- `threaded` has one more argument than `direct`. -/
  more : threaded.getAppArgs.size = direct.getAppArgs.size + 1
  /-- Both apply the same constant, at levels that agree apart from the motive's. -/
  same : ∃ name us name' vs, threaded.getAppFn = .const name us ∧
    direct.getAppFn = .const name' vs ∧ (name == name') = true ∧ shape.SameLevels us vs
  /-- The kernel checked the threading law of `threaded` for `shape`. -/
  law : seen.threading threaded = some (some shape)
  /-- The argument after the alternatives is the variable `passed`. -/
  passes : threaded.getAppArgs[shape.head + shape.alternatives.size]? = some (.fvar passed)

/-- The step that compares `threaded`, an application of `side`, as the threaded form of the
`match` that `direct` applies; `none` where it is not that form (`Threads`). Where the pass was not
asked for the decomposition, the step is the refusal that names that need. -/
def threaded (side : Side) (seen other : Observations) (pairs : Pairs) (threaded direct : Expr) :
    Option Step :=
  if threaded.getAppArgs.size = direct.getAppArgs.size + 1 then
    match threaded.getAppFn, direct.getAppFn with
    | .const name us, .const name' vs =>
      if name == name' then
        match seen.threading threaded with
        | none => some (.error (.unobserved (.threading side threaded)))
        | some none => none
        | some (some shape) =>
          if shape.sameLevels us vs then
            match threaded.getAppArgs[shape.head + shape.alternatives.size]? with
            | some (.fvar passed) =>
              some (threadedParts side seen other pairs shape passed threaded.getAppArgs
                direct.getAppArgs)
            | _ => none
          else none
      else none
    | _, _ => none
  else none

/-- The step that compares two applications: two well-founded fixpoints by the arguments that
carry their computation (`fixpointArguments?`), a threaded `match` with the direct one
(`threaded`), on either side, and any other two by their heads and their arguments. -/
def application (left right : Observations) (pairs : Pairs) (a b : Expr) : Step :=
  match fixpointArguments? a, fixpointArguments? b with
  | some xs, some ys => if xs.size = ys.size then .ok (paired pairs xs ys) else .error .different
  | none, none =>
    match threaded .left left right pairs a b with
    | some result => result
    | none =>
      match threaded .right right left pairs b a with
      | some result => result
      | none =>
        if a.getAppArgs.size = b.getAppArgs.size then
          .ok (⟨pairs, a.getAppFn, b.getAppFn⟩ :: paired pairs a.getAppArgs b.getAppArgs)
        else .error .different
  | _, _ => .error .different

/-- The step that compares the bodies of two binders `a` and `b` after the parts `before`: each
body is read with the variable the pass gave its binder, and the two variables are paired. The two
variables must be new (`newVariables`): a variable that a pair already holds, or one variable for
both binders, is refused, whatever the pass gave. -/
def under (left right : Observations) (pairs : Pairs) (a b : Expr) (before : List Part)
    (body body' : Expr) : Step :=
  match left.bound a with
  | none => .error (.unobserved (.bound .left a))
  | some x =>
    match right.bound b with
    | none => .error (.unobserved (.bound .right b))
    | some y =>
      if newVariables pairs [x, y] then
        .ok (before ++
          [⟨pairs.push (x, y), body.instantiate1 (.fvar x), body'.instantiate1 (.fvar y)⟩])
      else .error .different

/-- The step that compares two terms by their structure, which the comparison takes where
compilation keeps both of them. -/
def structural (left right : Observations) (pairs : Pairs) (a b : Expr) : Step :=
  match a, b with
  | .mdata _ a', _ => .ok [⟨pairs, a', b⟩]
  | _, .mdata _ b' => .ok [⟨pairs, a, b'⟩]
  | .fvar x, .fvar y => if x == y || pairs.contains (x, y) then .ok [] else .error .different
  | .const n us, .const m vs => if n == m && us == vs then .ok [] else .error .different
  | .lit l, .lit l' => if l == l' then .ok [] else .error .different
  | .sort u, .sort v => if u == v then .ok [] else .error .different
  | .proj s i e, .proj s' i' e' =>
    if s == s' && i == i' then .ok [⟨pairs, e, e'⟩] else .error .different
  | .app .., .app .. => application left right pairs a b
  | .lam _ t body _, .lam _ t' body' _ => under left right pairs a b [⟨pairs, t, t'⟩] body body'
  | .forallE _ t body _, .forallE _ t' body' _ =>
    under left right pairs a b [⟨pairs, t, t'⟩] body body'
  | .letE _ t v body _, .letE _ t' v' body' _ =>
    under left right pairs a b [⟨pairs, t, t'⟩, ⟨pairs, v, v'⟩] body body'
  | _, _ => .error .different

/-- One step of the comparison of `a` with `b`. Two terms that Lean's expression equality
identifies and that have no free variable are equal. Otherwise the erasure of each is read: two
erased terms are equal, two terms that compilation keeps are compared by their structure
(`structural`), and an erased term is different from a kept one. -/
def step (left right : Observations) (pairs : Pairs) (a b : Expr) : Step :=
  if a == b && !a.hasFVar && !b.hasFVar then .ok []
  else
    match left.erased a, right.erased b with
    | none, _ => .error (.unobserved (.erased .left a))
    | some _, none => .error (.unobserved (.erased .right b))
    | some true, some true => .ok []
    | some false, some false => structural left right pairs a b
    | some _, some _ => .error .different

/-- Whether `a` and `b` are equal up to compilation erasure, to depth `fuel`: the steps of `step`,
each part compared in turn. A step that needs an observation it was not given answers `false`, and
so does exhausted `fuel`. -/
def equalWithin (left right : Observations) : Nat → Pairs → Expr → Expr → Bool
  | 0, _, _, _ => false
  | fuel + 1, pairs, a, b =>
    match step left right pairs a b with
    | .ok all => all.all fun part => equalWithin left right fuel part.pairs part.left part.right
    | .error _ => false

/-- Compilation keeps both `a` and `b`: each is observed not to be erased. A term whose erasure
the pass was not asked about is not kept, and neither is a pair of which exactly one term is
erased, so no structural rule relates an erased term to a kept one. -/
def Kept (left right : Observations) (a b : Expr) : Prop :=
  left.erased a = some false ∧ right.erased b = some false

/-- `a` and `b` are equal up to compilation erasure, by a derivation of depth at most the index:
one constructor for each rule the comparison applies. `left` and `right` hold the observations of
the two sides. A pair `(x, y)` of `pairs` reads `x` on the left and `y` on the right as the same
variable.

Every rule but `closed` and `erased` compares two terms by their structure, and applies only where
compilation keeps both of them (`Kept`). So the two terms are the same once every proof and every
type of each, decided in its own context, is erased: an erased term is related to an erased term
(`erased`), and no rule but `closed` relates it to a kept one. `closed` is the exception because
it reads no observation. It relates only two terms that Lean's expression equality identifies and
that have no free variable, and for two such terms the erasure of one is the erasure of the other
when the observations are truthful. That is argued, not proved: `equalWithin_iff` holds for every
pair of observations, also for a pair that answers differently for such a term. The equalities of
names, universe levels, literals and variables are stated as the Boolean tests the comparison
runs, because Lean's equality of universe levels and of expressions has no specification to state
them by.

A binder rule (`lam`, `forallE`, `letE`) and each alternative of a threaded `match` reads a body
only with new variables (`newVariables`), and the part for that body holds each of them in a pair
(`unpaired_push`, `alternative_holds`). Every later part keeps that pair (`step_keeps_pairs`). So
no answer of `Observations.bound` makes one variable stand for two binders on one path
(`Reached.newVariables_eq_false`). That is about the binders the comparison opens, not about a
free variable of the two terms it starts from: `reproduces` starts with no pairs, and a
regenerated or observed value has no free variable.

What the relation shares with the comparison. The relation is stated with definitions the
comparison runs, so a change inside one of them changes the relation and the comparison together.
A constructor states when its rule applies and that every part is related. Which parts those
are, and which variables are new, is what the shared definitions compute. The two rules for a
threaded `match` take their parts from `threadedParts`, which uses `alternative`, `openLambdas`,
`standingFor`, `Side.orient`, `Side.pair` and `Threading.head`. `Threads` reads a decomposition
with `Threading.head` and `Threading.sameLevels`. Every rule that pairs arguments position by
position uses `paired`, and every rule that reads a body uses `newVariables` with `unpaired`.

Theorems state these of them exactly, so a change fails a theorem: when `threadedParts` and
`alternative` yield parts and which (`threadedParts_eq_ok_iff`, `alternative_eq_ok_iff`), the
pairs of `standingFor` (`mem_standingFor_left`, `mem_standingFor_right`), and the test of
`newVariables` and of `unpaired` (`newVariables_eq_true_iff`, `unpaired_eq_true_iff`). Of
`Side.orient` and `paired` a theorem states only the pairs of their parts (`Side.orient_pairs`,
`pairs_of_mem_paired`), not which term is on which side or which terms are paired. No theorem
states what `openLambdas`, `Side.pair`, `Threading.head` and `Threading.sameLevels` compute: the
theorems name them, and the relation means what they are written to compute. `Side.other` only
names the side in a refusal, and no rule reads it. A change inside a shared definition, in a part
that no theorem states, is a matter for review, not a failed proof. The `fixpoint` rule states
its parts by `Fixpoint`, which `fixpointArguments?_eq_some_iff` ties to the executed selection. -/
inductive EqualWithin (left right : Observations) : Nat → Pairs → Expr → Expr → Prop where
  /-- Two terms that Lean's expression equality identifies, neither with a free variable. -/
  | closed {depth : Nat} {pairs : Pairs} {a b : Expr} :
      (a == b && !a.hasFVar && !b.hasFVar) = true → EqualWithin left right (depth + 1) pairs a b
  /-- Two terms that compilation erases: each a proof or a type in its own context. -/
  | erased {depth : Nat} {pairs : Pairs} {a b : Expr} :
      left.erased a = some true → right.erased b = some true →
      EqualWithin left right (depth + 1) pairs a b
  /-- Metadata around the left term is passed over. -/
  | mdataLeft {depth : Nat} {pairs : Pairs} {data : Lean.MData} {a b : Expr} :
      Kept left right (.mdata data a) b → EqualWithin left right depth pairs a b →
      EqualWithin left right (depth + 1) pairs (.mdata data a) b
  /-- Metadata around the right term is passed over, where the left term has none. -/
  | mdataRight {depth : Nat} {pairs : Pairs} {data : Lean.MData} {a b : Expr} :
      Kept left right a (.mdata data b) → (∀ data' a', a ≠ .mdata data' a') →
      EqualWithin left right depth pairs a b →
      EqualWithin left right (depth + 1) pairs a (.mdata data b)
  /-- Two variables that are the same variable or are paired. -/
  | fvar {depth : Nat} {pairs : Pairs} {x y : FVarId} :
      Kept left right (.fvar x) (.fvar y) → (x == y || pairs.contains (x, y)) = true →
      EqualWithin left right (depth + 1) pairs (.fvar x) (.fvar y)
  /-- The same constant at the same universe levels. -/
  | const {depth : Nat} {pairs : Pairs} {n m : Name} {us vs : List Level} :
      Kept left right (.const n us) (.const m vs) → (n == m && us == vs) = true →
      EqualWithin left right (depth + 1) pairs (.const n us) (.const m vs)
  /-- The same literal. -/
  | lit {depth : Nat} {pairs : Pairs} {l l' : Lean.Literal} :
      Kept left right (.lit l) (.lit l') → (l == l') = true →
      EqualWithin left right (depth + 1) pairs (.lit l) (.lit l')
  /-- The same sort. -/
  | sort {depth : Nat} {pairs : Pairs} {u v : Level} :
      Kept left right (.sort u) (.sort v) → (u == v) = true →
      EqualWithin left right (depth + 1) pairs (.sort u) (.sort v)
  /-- The same projection of equal structures. -/
  | proj {depth : Nat} {pairs : Pairs} {s s' : Name} {i i' : Nat} {e e' : Expr} :
      Kept left right (.proj s i e) (.proj s' i' e') → (s == s' && i == i') = true →
      EqualWithin left right depth pairs e e' →
      EqualWithin left right (depth + 1) pairs (.proj s i e) (.proj s' i' e')
  /-- Two well-founded fixpoints whose arguments that carry the computation (`Fixpoint`: the
  domain, the motive, the functional and the arguments after it) are as many and are equal one by
  one. Their relations, measures and well-foundedness proofs are not compared, and neither is the
  combinator or its universe levels: an application of `WellFounded.fix` is related to one of
  `WellFounded.Nat.fix` with equal such arguments. -/
  | fixpoint {depth : Nat} {pairs : Pairs} {f x g y : Expr} {xs ys : Array Expr} :
      Kept left right (.app f x) (.app g y) →
      Fixpoint (.app f x) xs → Fixpoint (.app g y) ys →
      xs.size = ys.size →
      (∀ part ∈ paired pairs xs ys, EqualWithin left right depth part.pairs part.left part.right) →
      EqualWithin left right (depth + 1) pairs (.app f x) (.app g y)
  /-- A `match` on the left that passes a variable through, against the `match` on the right that
  uses the variable directly (`Threads`), neither a well-founded fixpoint: every part of
  `threadedParts` is equal. The rule applies only where the pass recorded that Lean's kernel
  checked the threading law of the left application (`Threads.law`). -/
  | threadedLeft {depth : Nat} {pairs : Pairs} {f x g y : Expr} {shape : Threading}
      {passed : FVarId} {parts : List Part} :
      Kept left right (.app f x) (.app g y) →
      (∀ arguments, ¬ Fixpoint (.app f x) arguments) →
      (∀ arguments, ¬ Fixpoint (.app g y) arguments) →
      Threads left (.app f x) (.app g y) shape passed →
      threadedParts .left left right pairs shape passed (Expr.app f x).getAppArgs
        (Expr.app g y).getAppArgs = .ok parts →
      (∀ part ∈ parts, EqualWithin left right depth part.pairs part.left part.right) →
      EqualWithin left right (depth + 1) pairs (.app f x) (.app g y)
  /-- `threadedLeft` with the `match` that passes the variable through on the right. -/
  | threadedRight {depth : Nat} {pairs : Pairs} {f x g y : Expr} {shape : Threading}
      {passed : FVarId} {parts : List Part} :
      Kept left right (.app f x) (.app g y) →
      (∀ arguments, ¬ Fixpoint (.app f x) arguments) →
      (∀ arguments, ¬ Fixpoint (.app g y) arguments) →
      Threads right (.app g y) (.app f x) shape passed →
      threadedParts .right right left pairs shape passed (Expr.app g y).getAppArgs
        (Expr.app f x).getAppArgs = .ok parts →
      (∀ part ∈ parts, EqualWithin left right depth part.pairs part.left part.right) →
      EqualWithin left right (depth + 1) pairs (.app f x) (.app g y)
  /-- Two applications, neither a well-founded fixpoint, with equal heads and with arguments that
  are as many and are equal one by one. -/
  | app {depth : Nat} {pairs : Pairs} {f x g y : Expr} :
      Kept left right (.app f x) (.app g y) →
      (∀ arguments, ¬ Fixpoint (.app f x) arguments) →
      (∀ arguments, ¬ Fixpoint (.app g y) arguments) →
      (Expr.app f x).getAppArgs.size = (Expr.app g y).getAppArgs.size →
      EqualWithin left right depth pairs (Expr.app f x).getAppFn (Expr.app g y).getAppFn →
      (∀ part ∈ paired pairs (Expr.app f x).getAppArgs (Expr.app g y).getAppArgs,
        EqualWithin left right depth part.pairs part.left part.right) →
      EqualWithin left right (depth + 1) pairs (.app f x) (.app g y)
  /-- Two functions with equal binder types and with bodies that are equal when each is read
  with its own variable and the two variables are paired. The two variables are new
  (`NewVariables`). -/
  | lam {depth : Nat} {pairs : Pairs} {n n' : Name} {t t' body body' : Expr}
      {bi bi' : Lean.BinderInfo} {x y : FVarId} :
      Kept left right (.lam n t body bi) (.lam n' t' body' bi') →
      left.bound (.lam n t body bi) = some x → right.bound (.lam n' t' body' bi') = some y →
      NewVariables pairs [x, y] →
      EqualWithin left right depth pairs t t' →
      EqualWithin left right depth (pairs.push (x, y)) (body.instantiate1 (.fvar x))
        (body'.instantiate1 (.fvar y)) →
      EqualWithin left right (depth + 1) pairs (.lam n t body bi) (.lam n' t' body' bi')
  /-- Two function types, compared as two functions are. -/
  | forallE {depth : Nat} {pairs : Pairs} {n n' : Name} {t t' body body' : Expr}
      {bi bi' : Lean.BinderInfo} {x y : FVarId} :
      Kept left right (.forallE n t body bi) (.forallE n' t' body' bi') →
      left.bound (.forallE n t body bi) = some x →
      right.bound (.forallE n' t' body' bi') = some y →
      NewVariables pairs [x, y] →
      EqualWithin left right depth pairs t t' →
      EqualWithin left right depth (pairs.push (x, y)) (body.instantiate1 (.fvar x))
        (body'.instantiate1 (.fvar y)) →
      EqualWithin left right (depth + 1) pairs (.forallE n t body bi) (.forallE n' t' body' bi')
  /-- Two `let` terms with equal types and values and with bodies that are equal when each is
  read with its own variable and the two variables are paired. -/
  | letE {depth : Nat} {pairs : Pairs} {n n' : Name} {t t' v v' body body' : Expr}
      {nondep nondep' : Bool} {x y : FVarId} :
      Kept left right (.letE n t v body nondep) (.letE n' t' v' body' nondep') →
      left.bound (.letE n t v body nondep) = some x →
      right.bound (.letE n' t' v' body' nondep') = some y →
      NewVariables pairs [x, y] →
      EqualWithin left right depth pairs t t' → EqualWithin left right depth pairs v v' →
      EqualWithin left right depth (pairs.push (x, y)) (body.instantiate1 (.fvar x))
        (body'.instantiate1 (.fvar y)) →
      EqualWithin left right (depth + 1) pairs (.letE n t v body nondep)
        (.letE n' t' v' body' nondep')


/-- `under` reduces to parts exactly where the pass gave each of the two binders a variable and
the two variables are new: the parts before, and then the two bodies read with those variables,
paired. -/
theorem under_eq_ok_iff (left right : Observations) (pairs : Pairs) (a b : Expr)
    (before : List Part) (body body' : Expr) (parts : List Part) :
    under left right pairs a b before body body' = .ok parts ↔
      ∃ x y, left.bound a = some x ∧ right.bound b = some y ∧ newVariables pairs [x, y] = true ∧
        parts = before ++
          [⟨pairs.push (x, y), body.instantiate1 (.fvar x), body'.instantiate1 (.fvar y)⟩] := by
  unfold under
  cases onLeft : left.bound a with
  | none => simp
  | some x =>
    cases onRight : right.bound b with
    | none => simp
    | some y =>
      by_cases new : newVariables pairs [x, y] = true
      · constructor
        · intro found
          simp only [new, ↓reduceIte] at found
          exact ⟨x, y, rfl, rfl, new, (Except.ok.inj found).symm⟩
        · rintro ⟨x', y', same, same', _, rfl⟩
          cases same
          cases same'
          simp only [new, ↓reduceIte]
      · constructor
        · intro found
          simp [new] at found
        · rintro ⟨x', y', same, same', new', _⟩
          cases same
          cases same'
          exact absurd new' new

/-- A binder whose variable is not new is refused, whatever the pass gave: a variable that a pair
already holds, on either side, or one variable for both binders. This is the test of one rule
against the pairs it is given; `Reached.newVariables_eq_false` states what follows for a path. -/
theorem under_eq_error_of_reused (left right : Observations) (pairs : Pairs) (a b : Expr)
    (before : List Part) (body body' : Expr) {x y : FVarId} (bound : left.bound a = some x)
    (bound' : right.bound b = some y) (reused : newVariables pairs [x, y] = false) :
    under left right pairs a b before body body' = .error .different := by
  simp [under, bound, bound', reused]

/-- The pairs with which a binder rule reads the two bodies hold both of its variables. -/
theorem unpaired_push (pairs : Pairs) (x y : FVarId) :
    unpaired (pairs.push (x, y)) x = false ∧ unpaired (pairs.push (x, y)) y = false :=
  ⟨unpaired_eq_false_of_mem (pair := (x, y)) (by simp) (.inl rfl),
    unpaired_eq_false_of_mem (pair := (x, y)) (by simp) (.inr rfl)⟩

/-- `alternative` yields a part exactly where both alternatives open to `binders` pattern
variables, the threaded one then binds one more variable, those variables are new (the pattern
variables of both and the further one), a pair holds the passed variable on the threaded side, and
the part compares the two bodies under them. So an alternative is compared only with new
variables, whatever the pass gave. -/
theorem alternative_eq_ok_iff (side : Side) (seen other : Observations) (pairs : Pairs)
    (passed : FVarId) (binders : Nat) (threaded direct : Expr) (part : Part) :
    alternative side seen other pairs passed binders threaded direct = .ok part ↔
      ∃ xs ys name type inner info body' further,
        openLambdas seen.bound binders threaded #[] = .opened xs (.lam name type inner info) ∧
        openLambdas other.bound binders direct #[] = .opened ys body' ∧
        (xs.size = binders ∧ ys.size = binders) ∧
        seen.bound (.lam name type inner info) = some further ∧
        newVariables pairs (xs.toList ++ ys.toList ++ [further]) = true ∧
        (standingFor side pairs passed further).isEmpty = false ∧
        part = side.orient
          (pairs ++ (xs.zip ys).map (fun (x, y) => side.pair x y) ++
            standingFor side pairs passed further)
          (inner.instantiate1 (.fvar further)) body' := by
  constructor
  · intro found
    unfold alternative at found
    split at found <;> try cases found
    rename_i xs body opened
    split at found <;> try cases found
    rename_i ys body' opened'
    split at found <;> try cases found
    rename_i sizes
    split at found <;> try cases found
    rename_i name type inner info
    split at found <;> try cases found
    rename_i further bound
    split at found <;> try cases found
    rename_i accepted
    rw [Bool.and_eq_true, Bool.not_eq_true'] at accepted
    exact ⟨xs, ys, name, type, inner, info, body', further, opened, opened', sizes, bound,
      accepted.1, accepted.2, rfl⟩
  · rintro ⟨xs, ys, name, type, inner, info, body', further, opened, opened', sizes, bound, new,
      standing, rfl⟩
    simp only [alternative, opened, opened', sizes, and_self, ↓reduceIte, bound, new, standing,
      Bool.not_false, Bool.and_self]

/-- An alternative one of whose variables is not new is refused, whatever the pass gave: a
pattern variable or the further variable that a pair already holds, on either side, or two of
them that are the same. -/
theorem alternative_eq_error_of_reused (side : Side) (seen other : Observations) (pairs : Pairs)
    (passed : FVarId) (binders : Nat) (threaded direct : Expr) {xs ys : Array FVarId}
    {name : Name} {type inner body' : Expr} {info : Lean.BinderInfo} {further : FVarId}
    (opened : openLambdas seen.bound binders threaded #[] =
      .opened xs (.lam name type inner info))
    (opened' : openLambdas other.bound binders direct #[] = .opened ys body')
    (sizes : xs.size = binders ∧ ys.size = binders)
    (bound : seen.bound (.lam name type inner info) = some further)
    (reused : newVariables pairs (xs.toList ++ ys.toList ++ [further]) = false) :
    alternative side seen other pairs passed binders threaded direct = .error .different := by
  simp only [alternative, opened, opened', sizes, and_self, ↓reduceIte, bound, reused,
    Bool.false_and, Bool.false_eq_true]

/-- An alternative whose passed variable no pair holds on the threaded side is refused, whatever
the pass gave: `standingFor` then gives the further variable no pair. -/
theorem alternative_eq_error_of_unpaired (side : Side) (seen other : Observations) (pairs : Pairs)
    (passed : FVarId) (binders : Nat) (threaded direct : Expr) {xs ys : Array FVarId}
    {name : Name} {type inner body' : Expr} {info : Lean.BinderInfo} {further : FVarId}
    (opened : openLambdas seen.bound binders threaded #[] =
      .opened xs (.lam name type inner info))
    (opened' : openLambdas other.bound binders direct #[] = .opened ys body')
    (sizes : xs.size = binders ∧ ys.size = binders)
    (bound : seen.bound (.lam name type inner info) = some further)
    (unpaired : (standingFor side pairs passed further).isEmpty = true) :
    alternative side seen other pairs passed binders threaded direct = .error .different := by
  simp only [alternative, opened, opened', sizes, and_self, ↓reduceIte, bound, unpaired,
    Bool.not_true, Bool.and_false, Bool.false_eq_true]

/-- The pairs with which the two bodies of an alternative are compared hold every variable the
bodies are read with: the pattern variables of both alternatives and the further variable. -/
theorem alternative_holds (side : Side) (seen other : Observations) (pairs : Pairs)
    (passed : FVarId) (binders : Nat) (threaded direct : Expr) {xs ys : Array FVarId}
    {name : Name} {type inner body' : Expr} {info : Lean.BinderInfo} {further : FVarId}
    {part : Part}
    (opened : openLambdas seen.bound binders threaded #[] =
      .opened xs (.lam name type inner info))
    (opened' : openLambdas other.bound binders direct #[] = .opened ys body')
    (bound : seen.bound (.lam name type inner info) = some further)
    (found : alternative side seen other pairs passed binders threaded direct = .ok part)
    {v : FVarId} (member : v ∈ xs.toList ++ ys.toList ++ [further]) :
    unpaired part.pairs v = false := by
  obtain ⟨xs', ys', name', type', inner', info', body'', further', opened₁, opened₂, sizes, bound₁,
    _, standing, rfl⟩ := (alternative_eq_ok_iff ..).mp found
  cases opened.symm.trans opened₁
  cases opened'.symm.trans opened₂
  cases bound.symm.trans bound₁
  rw [Side.orient_pairs, unpaired_append, unpaired_append]
  simp only [List.mem_append, List.mem_singleton, Array.mem_toList_iff] at member
  rcases member with (onThreaded | onDirect) | rfl
  · obtain ⟨i, bounds, rfl⟩ := Array.mem_iff_getElem.mp onThreaded
    have held : unpaired ((xs.zip ys).map fun (x, y) => side.pair x y) xs[i] = false :=
      unpaired_eq_false_of_mem (pair := side.pair xs[i] (ys[i]'(by omega)))
        (Array.mem_map.mpr ⟨(xs[i], ys[i]'(by omega)),
          Array.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩, rfl⟩)
        (by cases side <;> simp [Side.pair])
    simp [held]
  · obtain ⟨i, bounds, rfl⟩ := Array.mem_iff_getElem.mp onDirect
    have held : unpaired ((xs.zip ys).map fun (x, y) => side.pair x y) ys[i] = false :=
      unpaired_eq_false_of_mem (pair := side.pair (xs[i]'(by omega)) ys[i])
        (Array.mem_map.mpr ⟨(xs[i]'(by omega), ys[i]),
          Array.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩, rfl⟩)
        (by cases side <;> simp [Side.pair])
    simp [held]
  · obtain ⟨⟨x, y⟩, standingMember⟩ := Array.isEmpty_eq_false_iff_exists_mem.mp standing
    have held : unpaired (standingFor side pairs passed v) v = false :=
      unpaired_eq_false_of_mem standingMember (by
        cases side
        · exact .inl ((mem_standingFor_left ..).mp standingMember).1
        · exact .inr ((mem_standingFor_right ..).mp standingMember).1)
    simp [held]

/-- Two lists are as long, and `related` holds of their members position by position. -/
inductive Positionwise {α β : Type} (related : α → β → Prop) : List α → List β → Prop where
  /-- Two empty lists. -/
  | nil : Positionwise related [] []
  /-- Two related heads before two lists that are related position by position. -/
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      related a b → Positionwise related as bs → Positionwise related (a :: as) (b :: bs)

/-- A relation that holds position by position is kept by a weaker relation. -/
theorem Positionwise.imp {α β : Type} {related weaker : α → β → Prop}
    (implies : ∀ a b, related a b → weaker a b) {as : List α} {bs : List β}
    (holds : Positionwise related as bs) : Positionwise weaker as bs := by
  induction holds with
  | nil => exact .nil
  | cons head _ tail => exact .cons (implies _ _ head) tail

/-- A member of the second of two lists that are related position by position is related to a
member of the first. -/
theorem Positionwise.exists_of_mem {α β : Type} {related : α → β → Prop} {as : List α}
    {bs : List β} (holds : Positionwise related as bs) {b : β} (member : b ∈ bs) :
    ∃ a, related a b := by
  induction holds with
  | nil => cases member
  | cons head _ tail =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨_, head⟩
    · exact tail later

/-- A list mapped in `Except` succeeds exactly where every element does, with the results in
the order of the elements. -/
theorem mapM_eq_ok_iff {α β ε : Type} (f : α → Except ε β) :
    ∀ (elements : List α) (results : List β),
      elements.mapM f = .ok results ↔
        Positionwise (fun element result => f element = .ok result) elements results
  | [], results => by
    constructor
    · intro mapped
      cases mapped
      exact .nil
    · intro related
      cases related
      rfl
  | element :: rest, results => by
    rw [List.mapM_cons]
    constructor
    · intro mapped
      cases first : f element with
      | error refusal => rw [first] at mapped; cases mapped
      | ok result =>
        rw [first] at mapped
        cases others : rest.mapM f with
        | error refusal => rw [others] at mapped; cases mapped
        | ok tail =>
          rw [others] at mapped
          cases mapped
          exact .cons first ((mapM_eq_ok_iff f rest tail).mp others)
    · intro related
      cases related with
      | cons first others =>
        rw [first, (mapM_eq_ok_iff f rest _).mpr others]
        rfl

/-- `threadedParts` yields parts exactly where the arguments other than the alternatives and the
variable passed are as many on both sides, every alternative yields its part (`alternative`), and
the parts are those arguments position by position and then the alternatives' parts in order. So
every part of a threaded `match` that comes from an alternative is a part `alternative` yields,
which reads its bodies only with new variables (`alternative_eq_ok_iff`), and no alternative is
left out. A change of the selection inside `threadedParts` fails this theorem. -/
theorem threadedParts_eq_ok_iff (side : Side) (seen other : Observations) (pairs : Pairs)
    (shape : Threading) (passed : FVarId) (targs dargs : Array Expr) (parts : List Part) :
    threadedParts side seen other pairs shape passed targs dargs = .ok parts ↔
      (targs.extract 0 shape.head ++
          targs.extract (shape.head + shape.alternatives.size + 1)).size =
        (dargs.extract 0 shape.head ++ dargs.extract (shape.head + shape.alternatives.size)).size ∧
      ∃ alternatives : List Part,
        Positionwise
          (fun (entry : Nat × Nat) (part : Part) =>
            ∃ t d, targs[shape.head + entry.2]? = some t ∧ dargs[shape.head + entry.2]? = some d ∧
              alternative side seen other pairs passed entry.1 t d = .ok part)
          shape.alternatives.toList.zipIdx alternatives ∧
        parts =
          ((targs.extract 0 shape.head ++
              targs.extract (shape.head + shape.alternatives.size + 1)).toList.zip
            (dargs.extract 0 shape.head ++
              dargs.extract (shape.head + shape.alternatives.size)).toList).map
            (fun (t, d) => side.orient pairs t d) ++ alternatives := by
  have each : ∀ (entry : Nat × Nat) (part : Part),
      (match targs[shape.head + entry.2]?, dargs[shape.head + entry.2]? with
        | some t, some d => alternative side seen other pairs passed entry.1 t d
        | _, _ => Except.error Refusal.different) = .ok part ↔
      ∃ t d, targs[shape.head + entry.2]? = some t ∧ dargs[shape.head + entry.2]? = some d ∧
        alternative side seen other pairs passed entry.1 t d = .ok part := by
    intro entry part
    constructor
    · intro found
      split at found
      · rename_i t d onThreaded onDirect
        exact ⟨t, d, onThreaded, onDirect, found⟩
      · cases found
    · rintro ⟨t, d, onThreaded, onDirect, found⟩
      simp only [onThreaded, onDirect, found]
  unfold threadedParts
  simp only
  split
  · rename_i sizes
    generalize mapped :
      List.mapM (m := Except Refusal) (β := Part) _ shape.alternatives.toList.zipIdx = result
    cases result with
    | error refusal =>
      constructor
      · intro found
        cases found
      · rintro ⟨_, alternatives, related, _⟩
        have accepted := (mapM_eq_ok_iff _ _ _).mpr
          (Positionwise.imp (fun entry part found => (each entry part).mpr found) related)
        cases mapped.symm.trans accepted
    | ok alternatives =>
      have related := (mapM_eq_ok_iff _ _ _).mp mapped
      constructor
      · intro found
        have same : Except.ok (_ ++ alternatives) = Except.ok parts := found
        exact ⟨sizes, alternatives,
          Positionwise.imp (fun entry part found => (each entry part).mp found) related,
          (Except.ok.inj same).symm⟩
      · rintro ⟨_, alternatives', related', rfl⟩
        have accepted := (mapM_eq_ok_iff _ _ _).mpr
          (Positionwise.imp (fun entry part found => (each entry part).mpr found) related')
        cases mapped.symm.trans accepted
        rfl
  · rename_i sizes
    constructor
    · intro found
      cases found
    · rintro ⟨same, _⟩
      exact absurd same sizes

/-- `threaded` reduces to parts exactly where `threaded` is the threaded form of the `match` that
`direct` applies (`Threads`), and then to the parts of `threadedParts`. -/
theorem threaded_eq_some_ok_iff (side : Side) (seen other : Observations) (pairs : Pairs)
    (t d : Expr) (parts : List Part) :
    threaded side seen other pairs t d = some (.ok parts) ↔
      ∃ shape passed, Threads seen t d shape passed ∧
        threadedParts side seen other pairs shape passed t.getAppArgs d.getAppArgs =
          .ok parts := by
  constructor
  · intro found
    unfold threaded at found
    split at found <;> try cases found
    rename_i more
    split at found <;> try cases found
    rename_i name us name' vs function function'
    split at found <;> try cases found
    rename_i named
    split at found <;> try cases found
    rename_i shape law
    split at found <;> try cases found
    rename_i levels
    split at found <;> try cases found
    rename_i passed passes
    exact ⟨shape, passed, ⟨more, ⟨name, us, name', vs, function, function', named,
      (Threading.sameLevels_iff ..).mp levels⟩, law, passes⟩, Option.some.inj found⟩
  · rintro ⟨shape, passed, ⟨more, ⟨name, us, name', vs, function, function', named, agree⟩, law,
      passes⟩, found⟩
    have levels := (Threading.sameLevels_iff ..).mpr agree
    simp [threaded, more, function, function', named, law, levels, passes, found]

/-- `threaded` does not apply where `threaded` does not have exactly one more argument than
`direct`. -/
theorem threaded_eq_none (side : Side) (seen other : Observations) (pairs : Pairs) (t d : Expr)
    (sizes : t.getAppArgs.size ≠ d.getAppArgs.size + 1) :
    threaded side seen other pairs t d = none := by
  simp [threaded, sizes]

/-- `application` reduces to parts by exactly one of its four rules: two well-founded fixpoints,
a threaded `match` on the left, one on the right, or two other applications with as many
arguments. -/
theorem application_eq_ok_iff (left right : Observations) (pairs : Pairs) (a b : Expr)
    (parts : List Part) :
    application left right pairs a b = .ok parts ↔
      (∃ xs ys, fixpointArguments? a = some xs ∧ fixpointArguments? b = some ys ∧
        xs.size = ys.size ∧ parts = paired pairs xs ys) ∨
      (fixpointArguments? a = none ∧ fixpointArguments? b = none ∧
        ((∃ shape passed, Threads left a b shape passed ∧
            threadedParts .left left right pairs shape passed a.getAppArgs b.getAppArgs =
              .ok parts) ∨
          (∃ shape passed, Threads right b a shape passed ∧
            threadedParts .right right left pairs shape passed b.getAppArgs a.getAppArgs =
              .ok parts) ∨
          (a.getAppArgs.size = b.getAppArgs.size ∧
            parts =
              ⟨pairs, a.getAppFn, b.getAppFn⟩ :: paired pairs a.getAppArgs b.getAppArgs))) := by
  constructor
  · intro found
    unfold application at found
    split at found
    · rename_i xs ys fixed fixed'
      split at found
      · rename_i sizes
        exact .inl ⟨xs, ys, fixed, fixed', sizes, (Except.ok.inj found).symm⟩
      · cases found
    · rename_i fixed fixed'
      refine .inr ⟨fixed, fixed', ?_⟩
      split at found
      · rename_i result onLeft
        subst found
        exact .inl ((threaded_eq_some_ok_iff ..).mp onLeft)
      · split at found
        · rename_i result onRight
          subst found
          exact .inr (.inl ((threaded_eq_some_ok_iff ..).mp onRight))
        · split at found
          · rename_i sizes
            exact .inr (.inr ⟨sizes, (Except.ok.inj found).symm⟩)
          · cases found
    · cases found
  · rintro (⟨xs, ys, fixed, fixed', sizes, rfl⟩ | ⟨fixed, fixed', onLeft | onRight | ⟨sizes, rfl⟩⟩)
    · simp [application, fixed, fixed', sizes]
    · obtain ⟨shape, passed, threads, found⟩ := onLeft
      simp [application, fixed, fixed',
        (threaded_eq_some_ok_iff ..).mpr ⟨shape, passed, threads, found⟩]
    · obtain ⟨shape, passed, threads, found⟩ := onRight
      have notLeft := threaded_eq_none .left left right pairs a b
        (by have := threads.more; omega)
      simp [application, fixed, fixed', notLeft,
        (threaded_eq_some_ok_iff ..).mpr ⟨shape, passed, threads, found⟩]
    · have notLeft := threaded_eq_none .left left right pairs a b (by omega)
      have notRight := threaded_eq_none .right right left pairs b a (by omega)
      simp [application, fixed, fixed', notLeft, notRight, sizes]

/-- Every part of a threaded `match` keeps the pairs of the step, and has its further pairs after
them. -/
theorem threadedParts_keeps_pairs {side : Side} {seen other : Observations} {pairs : Pairs}
    {shape : Threading} {passed : FVarId} {targs dargs : Array Expr} {parts : List Part}
    (found : threadedParts side seen other pairs shape passed targs dargs = .ok parts)
    {part : Part} (member : part ∈ parts) : ∃ added : Pairs, part.pairs = pairs ++ added := by
  obtain ⟨_, alternatives, related, rfl⟩ := (threadedParts_eq_ok_iff ..).mp found
  rcases List.mem_append.mp member with outer | inner
  · obtain ⟨⟨t, d⟩, _, rfl⟩ := List.mem_map.mp outer
    exact ⟨#[], by simp [Side.orient_pairs]⟩
  · obtain ⟨entry, t, d, _, _, accepted⟩ := related.exists_of_mem inner
    obtain ⟨xs, ys, name, type, body, info, body', further, _, _, _, _, _, _, rfl⟩ :=
      (alternative_eq_ok_iff ..).mp accepted
    exact ⟨_, by rw [Side.orient_pairs, Array.append_assoc]⟩

/-- Every part of a structural step keeps the pairs of the step, and has its further pairs after
them. -/
theorem structural_keeps_pairs {left right : Observations} {pairs : Pairs} {a b : Expr}
    {parts : List Part} (found : structural left right pairs a b = .ok parts) {part : Part}
    (member : part ∈ parts) : ∃ added : Pairs, part.pairs = pairs ++ added := by
  have same : ∀ {part : Part}, part.pairs = pairs → ∃ added : Pairs, part.pairs = pairs ++ added :=
    fun kept => ⟨#[], by simp [kept]⟩
  unfold structural at found
  split at found
  · cases found
    cases List.mem_singleton.mp member
    exact same rfl
  · cases found
    cases List.mem_singleton.mp member
    exact same rfl
  · split at found
    · cases found
      cases member
    · cases found
  · split at found
    · cases found
      cases member
    · cases found
  · split at found
    · cases found
      cases member
    · cases found
  · split at found
    · cases found
      cases member
    · cases found
  · split at found
    · cases found
      cases List.mem_singleton.mp member
      exact same rfl
    · cases found
  · rcases (application_eq_ok_iff ..).mp found with
      ⟨xs, ys, _, _, _, rfl⟩ |
      ⟨_, _, ⟨shape, passed, _, threadedFound⟩ | ⟨shape, passed, _, threadedFound⟩ | ⟨_, rfl⟩⟩
    · exact same (pairs_of_mem_paired member)
    · exact threadedParts_keeps_pairs threadedFound member
    · exact threadedParts_keeps_pairs threadedFound member
    · rcases List.mem_cons.mp member with rfl | argument
      · exact same rfl
      · exact same (pairs_of_mem_paired argument)
  · obtain ⟨x, y, _, _, _, rfl⟩ := (under_eq_ok_iff ..).mp found
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl
    · exact same rfl
    · exact ⟨#[(x, y)], by simp⟩
  · obtain ⟨x, y, _, _, _, rfl⟩ := (under_eq_ok_iff ..).mp found
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl
    · exact same rfl
    · exact ⟨#[(x, y)], by simp⟩
  · obtain ⟨x, y, _, _, _, rfl⟩ := (under_eq_ok_iff ..).mp found
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl
    · exact same rfl
    · exact same rfl
    · exact ⟨#[(x, y)], by simp⟩
  · cases found

/-- Every part of a step keeps the pairs of the step, and has its further pairs after them: no
rule of the comparison removes or replaces a pair. -/
theorem step_keeps_pairs {left right : Observations} {pairs : Pairs} {a b : Expr}
    {parts : List Part} (found : step left right pairs a b = .ok parts) {part : Part}
    (member : part ∈ parts) : ∃ added : Pairs, part.pairs = pairs ++ added := by
  unfold step at found
  split at found
  · cases found
    cases member
  · split at found
    · cases found
    · cases found
    · cases found
      cases member
    · exact structural_keeps_pairs found member
    · cases found

/-- The parts the comparison comes to from the part `start`: `start` itself, and each part of a
step (`step`) from a part it comes to. `equalWithin` compares only such parts: `start`, then
parts of its step, then parts of theirs. -/
inductive Reached (left right : Observations) (start : Part) : Part → Prop where
  /-- The part the comparison starts from. -/
  | start : Reached left right start start
  /-- A part of the step from a part the comparison comes to. -/
  | part {whole part : Part} {parts : List Part} :
      Reached left right start whole →
      step left right whole.pairs whole.left whole.right = .ok parts → part ∈ parts →
      Reached left right start part

/-- A variable that a pair holds at `start` is held by a pair at every part the comparison comes
to from `start`. -/
theorem Reached.holds {left right : Observations} {start part : Part}
    (reached : Reached left right start part) {v : FVarId}
    (held : unpaired start.pairs v = false) : unpaired part.pairs v = false := by
  induction reached with
  | start => exact held
  | part _ found member kept =>
    obtain ⟨added, same⟩ := step_keeps_pairs found member
    rw [same, unpaired_append, kept, Bool.false_and]

/-- One variable does not stand for two binders on one path, whatever the pass gave: a variable
`v` that a pair holds at `start` is not new at any part the comparison comes to from `start`. So
a binder rule there refuses `v` (`under_eq_error_of_reused`), and so does an alternative
(`alternative_eq_error_of_reused`). A rule that reads a body with a variable starts such a path:
the part for the body holds the variable (`unpaired_push`, `alternative_holds`). -/
theorem Reached.newVariables_eq_false {left right : Observations} {start part : Part}
    (reached : Reached left right start part) {v : FVarId}
    (held : unpaired start.pairs v = false) {variables : List FVarId} (member : v ∈ variables) :
    newVariables part.pairs variables = false :=
  newVariables_eq_false_of_held (reached.holds held) member

/-- Where compilation keeps both of two terms and their structure reduces the comparison to parts
that are all related, the two terms are related: each rule of `structural` is a constructor of
`EqualWithin`. -/
theorem EqualWithin.of_structural {left right : Observations} {depth : Nat} {pairs : Pairs}
    {a b : Expr} {parts : List Part} (kept : Kept left right a b)
    (found : structural left right pairs a b = .ok parts)
    (related : ∀ part ∈ parts, EqualWithin left right depth part.pairs part.left part.right) :
    EqualWithin left right (depth + 1) pairs a b := by
  unfold structural at found
  split at found
  · cases found
    exact .mdataLeft kept (related _ (List.mem_singleton.mpr rfl))
  · rename_i notMData
    cases found
    exact .mdataRight kept (fun data' a' same => notMData data' a' same)
      (related _ (List.mem_singleton.mpr rfl))
  · split at found
    · exact .fvar kept ‹_›
    · cases found
  · split at found
    · exact .const kept ‹_›
    · cases found
  · split at found
    · exact .lit kept ‹_›
    · cases found
  · split at found
    · exact .sort kept ‹_›
    · cases found
  · split at found
    · cases found
      exact .proj kept ‹_› (related _ (List.mem_singleton.mpr rfl))
    · cases found
  · rcases (application_eq_ok_iff ..).mp found with
      ⟨xs, ys, fixed, fixed', sizes, rfl⟩ |
      ⟨fixed, fixed', ⟨shape, passed, threads, threadedFound⟩ |
        ⟨shape, passed, threads, threadedFound⟩ | ⟨sizes, rfl⟩⟩
    · exact .fixpoint kept ((fixpointArguments?_eq_some_iff ..).mp fixed)
        ((fixpointArguments?_eq_some_iff ..).mp fixed') sizes related
    · exact .threadedLeft kept ((fixpointArguments?_eq_none_iff _).mp fixed)
        ((fixpointArguments?_eq_none_iff _).mp fixed') threads threadedFound related
    · exact .threadedRight kept ((fixpointArguments?_eq_none_iff _).mp fixed)
        ((fixpointArguments?_eq_none_iff _).mp fixed') threads threadedFound related
    · simp only [List.mem_cons, forall_eq_or_imp] at related
      exact .app kept ((fixpointArguments?_eq_none_iff _).mp fixed)
        ((fixpointArguments?_eq_none_iff _).mp fixed') sizes related.1 related.2
  · obtain ⟨x, y, bound, bound', new, rfl⟩ := (under_eq_ok_iff ..).mp found
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at related
    exact .lam kept bound bound' ((newVariables_iff ..).mp new) related.1 related.2
  · obtain ⟨x, y, bound, bound', new, rfl⟩ := (under_eq_ok_iff ..).mp found
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at related
    exact .forallE kept bound bound' ((newVariables_iff ..).mp new) related.1 related.2
  · obtain ⟨x, y, bound, bound', new, rfl⟩ := (under_eq_ok_iff ..).mp found
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at related
    exact .letE kept bound bound' ((newVariables_iff ..).mp new) related.1 related.2.1 related.2.2
  · cases found

/-- Where a step reduces the comparison to parts that are all related, the two terms are
related. -/
theorem EqualWithin.of_step {left right : Observations} {depth : Nat} {pairs : Pairs}
    {a b : Expr} {parts : List Part} (found : step left right pairs a b = .ok parts)
    (related : ∀ part ∈ parts, EqualWithin left right depth part.pairs part.left part.right) :
    EqualWithin left right (depth + 1) pairs a b := by
  unfold step at found
  split at found
  · exact .closed ‹_›
  · split at found
    · cases found
    · cases found
    · exact .erased ‹_› ‹_›
    · exact .of_structural ⟨‹_›, ‹_›⟩ found related
    · cases found

/-- Soundness of the executed comparison: two terms it accepts are related. -/
theorem EqualWithin.of_equalWithin {left right : Observations} :
    ∀ (fuel : Nat) (pairs : Pairs) (a b : Expr),
      equalWithin left right fuel pairs a b = true → EqualWithin left right fuel pairs a b
  | 0, _, _, _, accepted => by simp [equalWithin] at accepted
  | fuel + 1, pairs, a, b, accepted => by
    simp only [equalWithin] at accepted
    split at accepted
    · rename_i all found
      exact .of_step found fun part member =>
        EqualWithin.of_equalWithin fuel part.pairs part.left part.right
          (List.all_eq_true.mp accepted part member)
    · cases accepted

/-- Where compilation keeps both of two terms and their structure reduces the comparison to parts
that the comparison accepts, it accepts the two terms. -/
theorem equalWithin_of_structural {left right : Observations} {fuel : Nat} {pairs : Pairs}
    {a b : Expr} {parts : List Part} (kept : Kept left right a b)
    (found : structural left right pairs a b = .ok parts)
    (accepted : ∀ part ∈ parts,
      equalWithin left right fuel part.pairs part.left part.right = true) :
    equalWithin left right (fuel + 1) pairs a b = true := by
  by_cases closed : (a == b && !a.hasFVar && !b.hasFVar) = true
  · simp [equalWithin, step, closed]
  · obtain ⟨keptLeft, keptRight⟩ := kept
    simpa [equalWithin, step, closed, keptLeft, keptRight, found] using accepted

/-- Completeness of the executed comparison: it accepts every two related terms. -/
theorem equalWithin_of_related {left right : Observations} {fuel : Nat} {pairs : Pairs}
    {a b : Expr} (related : EqualWithin left right fuel pairs a b) :
    equalWithin left right fuel pairs a b = true := by
  induction related with
  | closed closed => simp [equalWithin, step, closed]
  | @erased depth pairs a b erasedLeft erasedRight =>
    by_cases closed : (a == b && !a.hasFVar && !b.hasFVar) = true
    · simp [equalWithin, step, closed]
    · simp [equalWithin, step, closed, erasedLeft, erasedRight]
  | mdataLeft kept _ accepted =>
    exact equalWithin_of_structural kept (parts := [⟨_, _, _⟩]) rfl (by simpa using accepted)
  | @mdataRight depth pairs data a b kept notMData _ accepted =>
    refine equalWithin_of_structural kept (parts := [⟨pairs, a, b⟩]) ?_ (by simpa using accepted)
    cases a with
    | mdata data' a' => exact absurd rfl (notMData data' a')
    | _ => rfl
  | fvar kept same =>
    exact equalWithin_of_structural kept (parts := []) (by simp [structural, same]) (by simp)
  | const kept same =>
    exact equalWithin_of_structural kept (parts := []) (by simp [structural, same]) (by simp)
  | lit kept same =>
    exact equalWithin_of_structural kept (parts := []) (by simp [structural, same]) (by simp)
  | sort kept same =>
    exact equalWithin_of_structural kept (parts := []) (by simp [structural, same]) (by simp)
  | @proj depth pairs s s' i i' e e' kept same _ accepted =>
    exact equalWithin_of_structural kept (parts := [⟨pairs, e, e'⟩]) (by simp [structural, same])
      (by simpa using accepted)
  | fixpoint kept fixed fixed' sizes _ accepted =>
    exact equalWithin_of_structural kept
      ((application_eq_ok_iff ..).mpr (.inl ⟨_, _, (fixpointArguments?_eq_some_iff ..).mpr fixed,
        (fixpointArguments?_eq_some_iff ..).mpr fixed', sizes, rfl⟩)) accepted
  | threadedLeft kept fixed fixed' threads found _ accepted =>
    exact equalWithin_of_structural kept
      ((application_eq_ok_iff ..).mpr (.inr ⟨(fixpointArguments?_eq_none_iff _).mpr fixed,
        (fixpointArguments?_eq_none_iff _).mpr fixed', .inl ⟨_, _, threads, found⟩⟩))
      accepted
  | threadedRight kept fixed fixed' threads found _ accepted =>
    exact equalWithin_of_structural kept
      ((application_eq_ok_iff ..).mpr
        (.inr ⟨(fixpointArguments?_eq_none_iff _).mpr fixed,
          (fixpointArguments?_eq_none_iff _).mpr fixed', .inr (.inl ⟨_, _, threads, found⟩)⟩))
      accepted
  | app kept fixed fixed' sizes _ _ acceptedHead acceptedArguments =>
    refine equalWithin_of_structural kept
      ((application_eq_ok_iff ..).mpr (.inr ⟨(fixpointArguments?_eq_none_iff _).mpr fixed,
        (fixpointArguments?_eq_none_iff _).mpr fixed', .inr (.inr ⟨sizes, rfl⟩)⟩)) ?_
    intro part member
    rcases List.mem_cons.mp member with rfl | member
    · exact acceptedHead
    · exact acceptedArguments part member
  | lam kept bound bound' new _ _ acceptedType acceptedBody =>
    refine equalWithin_of_structural kept
      ((under_eq_ok_iff ..).mpr ⟨_, _, bound, bound', (newVariables_iff ..).mpr new, rfl⟩) ?_
    intro part member
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl
    · exact acceptedType
    · exact acceptedBody
  | forallE kept bound bound' new _ _ acceptedType acceptedBody =>
    refine equalWithin_of_structural kept
      ((under_eq_ok_iff ..).mpr ⟨_, _, bound, bound', (newVariables_iff ..).mpr new, rfl⟩) ?_
    intro part member
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl
    · exact acceptedType
    · exact acceptedBody
  | letE kept bound bound' new _ _ _ acceptedType acceptedValue acceptedBody =>
    refine equalWithin_of_structural kept
      ((under_eq_ok_iff ..).mpr ⟨_, _, bound, bound', (newVariables_iff ..).mpr new, rfl⟩) ?_
    intro part member
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl
    · exact acceptedType
    · exact acceptedValue
    · exact acceptedBody

/-- The executed comparison answers `true` exactly for the terms `EqualWithin` relates, for every
observation, depth, pairing and pair of terms. The theorem is about `equalWithin` itself, the
function `reproduces` runs. It starts from the observations: it does not say that an observation
is what Lean answers, or that related terms compile to code that computes the same. -/
theorem equalWithin_iff (left right : Observations) (fuel : Nat) (pairs : Pairs) (a b : Expr) :
    equalWithin left right fuel pairs a b = true ↔ EqualWithin left right fuel pairs a b :=
  ⟨EqualWithin.of_equalWithin fuel pairs a b, equalWithin_of_related⟩

/-- An erased term is refused against a kept one, at every depth and under every pairing, unless
the two are terms that Lean's expression equality identifies and that have no free variable. -/
theorem equalWithin_erased_kept (left right : Observations) (fuel : Nat) (pairs : Pairs)
    (a b : Expr) (erased : left.erased a = some true) (kept : right.erased b = some false)
    (open_ : (a == b && !a.hasFVar && !b.hasFVar) = false) :
    equalWithin left right fuel pairs a b = false := by
  cases fuel <;> simp [equalWithin, step, erased, kept, open_]

/-- `equalWithin_erased_kept` with the erased term on the right. -/
theorem equalWithin_kept_erased (left right : Observations) (fuel : Nat) (pairs : Pairs)
    (a b : Expr) (kept : left.erased a = some false) (erased : right.erased b = some true)
    (open_ : (a == b && !a.hasFVar && !b.hasFVar) = false) :
    equalWithin left right fuel pairs a b = false := by
  cases fuel <;> simp [equalWithin, step, erased, kept, open_]

/-- A left term whose erasure the pass did not record is refused, unless the two terms are ones
that Lean's expression equality identifies and that have no free variable. -/
theorem equalWithin_unobserved_left (left right : Observations) (fuel : Nat) (pairs : Pairs)
    (a b : Expr) (unobserved : left.erased a = none)
    (open_ : (a == b && !a.hasFVar && !b.hasFVar) = false) :
    equalWithin left right fuel pairs a b = false := by
  cases fuel <;> simp [equalWithin, step, unobserved, open_]

/-- `equalWithin_unobserved_left` for the right term, where the erasure of the left one is
recorded. -/
theorem equalWithin_unobserved_right (left right : Observations) (fuel : Nat) (pairs : Pairs)
    (a b : Expr) {recorded : Bool} (observed : left.erased a = some recorded)
    (unobserved : right.erased b = none)
    (open_ : (a == b && !a.hasFVar && !b.hasFVar) = false) :
    equalWithin left right fuel pairs a b = false := by
  cases fuel <;> simp [equalWithin, step, observed, unobserved, open_]

/-- The depth to which the comparison reads two values. Two values that differ only below it are
not accepted. -/
def depthLimit : Nat := 100000

/-- The definitions one regeneration added, each with the observed definition of its name, and
what the observing pass shows of the terms of each side. This is all the decision reads. -/
structure Regeneration where
  /-- The observations of the terms of the regenerated values. -/
  regenerated : Observations
  /-- The observations of the terms of the observed values. -/
  observed : Observations
  /-- Each regenerated value with the value of the observed definition of its name, and `none`
  where the inspected environment holds no definition of that name. -/
  definitions : List (Expr × Option Expr)
  /-- What the observing pass reports of its own run: `true` only where it took the comparison of
  every definition to its end, and `false` where it stopped, at a part the comparison refuses, at
  exhausted depth, or at its bound on the observations one step may ask for. It is an observation
  of the pass, like the others: nothing proves that the pass reports its run truthfully. -/
  finished : Bool

/-- Whether a regeneration reproduces the observed definitions: the observing pass finished, the
regeneration added at least one definition, and each one's value equals, up to compilation
erasure, the value of the observed definition of its name (`equalWithin`, to `depthLimit`, with no
variables paired). A regenerated definition with no observed definition of its name is not
reproduced, and neither is anything after a pass that stopped
(`reproduces_eq_false_of_unfinished`). -/
@[regula_decision]
def reproduces (regeneration : Regeneration) : Bool :=
  regeneration.finished && !regeneration.definitions.isEmpty &&
    regeneration.definitions.all fun definition =>
      match definition.2 with
      | some observed =>
        equalWithin regeneration.regenerated regeneration.observed depthLimit #[] definition.1
          observed
      | none => false

/-- The observing pass finished, the regeneration added at least one definition, and each one's
value is related by `EqualWithin`, within `depthLimit`, to the value of the observed definition of
its name. -/
def Reproduction (regeneration : Regeneration) : Prop :=
  regeneration.finished = true ∧ regeneration.definitions ≠ [] ∧
    ∀ definition ∈ regeneration.definitions,
      ∃ observed, definition.2 = some observed ∧
        EqualWithin regeneration.regenerated regeneration.observed depthLimit #[] definition.1
          observed

/-- `reproduces` answers `true` exactly for a regeneration that is a `Reproduction`. -/
theorem reproduces_iff (regeneration : Regeneration) :
    reproduces regeneration = true ↔ Reproduction regeneration := by
  simp only [reproduces, Reproduction, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.isEmpty_eq_false_iff, List.all_eq_true, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun definition _ => ?_
  cases observed : definition.2 with
  | none => simp
  | some value => simp [equalWithin_iff]

/-- `reproduces` accepts exactly the regenerations that reproduce the observed definitions
(`reproduces_iff`): it accepts one definition whose two values are erased, after a pass that
finished, and refuses a regeneration that added no definition. The decision reads the two values,
the observations and whether the pass finished, and nothing else. That each observation is what
Lean answers is the observing pass's, and that related values compile to the same code is argued;
neither is part of this kind. -/
theorem checked_reproduces :
    Regula.ExecutableContract reproduces (Regula.Decides (· = true) Reproduction) :=
  let erased : Observations :=
    { erased := fun _ => some true, bound := fun _ => none, threading := fun _ => none }
  ⟨.of_iff reproduces_iff
    ⟨⟨erased, erased, [(.sort .zero, some (.sort .zero))], true⟩,
      (reproduces_iff _).mpr ⟨rfl, by simp, fun definition member => by
        obtain rfl := List.mem_singleton.mp member
        exact ⟨_, rfl, .erased (depth := 99999) rfl rfl⟩⟩⟩
    ⟨⟨erased, erased, [], true⟩, by simp [reproduces]⟩⟩

/-- A regeneration whose observing pass did not finish is refused, whatever the pass recorded.
So a pass that stops at its bound on the observations of one step, at exhausted depth or at a
refused part cannot be followed by an acceptance: the refusal is part of the decision, not a
property of the pass. -/
theorem reproduces_eq_false_of_unfinished (regeneration : Regeneration)
    (stopped : regeneration.finished = false) : reproduces regeneration = false := by
  simp [reproduces, stopped]

end RegulaPolicy.Erasure
