module

public import Lean.Expr
public import RegulaPolicy.NativeAxiom
public import Regula.Contract
import all Lean.Expr
meta import Regula.Decision

/-! # The statement of a generated native-proof axiom

The pure decision of the native-axiom replay (RG1004,
https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG1004/): whether the type of an axiom is the
statement that its native tactic asserts, and which Boolean expression that statement asserts to
be `true`.

The producer is split in three. `nativeAxiomOrigin?` reads the owning prefix and the tactic from
the axiom's name. `recognize?` is the decision of this module. It is a pure, total function of
that origin and of the axiom's kernel-checked type, and of nothing else: no environment, no
attribute and no name that the audited project can write beside the declaration itself is among
its arguments. The observing pass (`Regula.Collect.replayNative`) then evaluates the expression
that the decision returned with compiled code. The pass takes a `Recognition` of the candidate,
which holds the expression with the proof that the decision returns it for that candidate. Each
value of that type is the result of the decision (`recognize?_eq_some`), so the pass cannot be
given the expression of a different candidate or a different expression.

`Statement` is the relation the decision is proved against: one constructor for each tactic.
`asserted?_sound` proves, with no hypothesis, that an accepted type is related, and
`asserted?_complete` that a related type is accepted. For `bv_decide` the second needs
`RuntimeStringAppend`, because the names of the tactic's auxiliary definitions are regenerated
with the logically opaque `String.Internal.append`. `checked_recognize` registers the sound kind.

**Not claimed.** That the evaluation of the expression returns what the pass records, and that
compiled code computes what the expression means, are the observing pass's and the compiler's.
That `generatedName` is the name Lean's generator gives is read from Lean's source, as in
`RegulaPolicy.NativeAxiom`. The universe levels of the constants of a statement are not
compared: the kernel checked the type. -/

@[expose] public section

namespace RegulaPolicy.NativeStatement
open Lean

/-- `Std.Tactic.BVDecide.Reflect.verifyBVExpr`, the check `bv_decide` evaluates natively. -/
def verifyBVExprName : Name := `Std.Tactic.BVDecide.Reflect.verifyBVExpr

/-- What the decision reads of an axiom: the tactic and the owning prefix that
`nativeAxiomOrigin?` recovers from the axiom's name, and the axiom's kernel-checked type. -/
structure Candidate where
  /-- The native tactic of the axiom's name. -/
  tactic : NativeTactic
  /-- The prefix under which Lean's generator made the axiom's name. -/
  parent : Name
  /-- The axiom's type. -/
  type : Expr

/-- The Boolean expression `e` of a type `e = true`. -/
def assertedBool? (type : Expr) : Option Expr := do
  let args := type.getAppArgs
  guard <| type.getAppFn.isConstOf ``Eq
  guard <| args.size == 3
  guard <| args[0]!.isConstOf ``Bool
  guard <| args[2]!.isConstOf ``Bool.true
  return args[1]!

/-- The asserted Boolean expression of a generated native-proof axiom, when its type has the
exact shape its tactic produces: `Decidable.decide p inst` (`elabNativeDecideCore`), or
`verifyBVExpr expr cert` over the same run's `_expr_def` and `_cert_def` definitions
(`LratCert.toReflectionProof`). -/
def asserted? (candidate : Candidate) : Option Expr := do
  let asserted ← assertedBool? candidate.type
  match candidate.tactic with
  | .nativeDecide | .decideNative => guard <| asserted.isAppOfArity ``Decidable.decide 2
  | .bvDecide =>
      guard <| asserted.isAppOfArity verifyBVExprName 2
      guard <| ([asserted.appFn!.appArg!, asserted.appArg!].zip
          candidate.tactic.auxiliaryInfixes).all
        fun (argument, kind) => argument.isConst &&
          generatedAuxParent? kind argument.constName! == some candidate.parent
  return asserted

/-! ## The relation -/

/-- `type` is the statement `e = true` over `Bool`: the constant `Eq` applied to the constant
`Bool`, to `e` and to the constant `Bool.true`. The universe levels of the three constants are
not part of the relation. -/
inductive AssertsTrue : Expr → Expr → Prop where
  /-- The application `Eq Bool e Bool.true`, at any universe levels. -/
  | intro (eqLevels boolLevels trueLevels : List Level) (e : Expr) :
      AssertsTrue
        (.app (.app (.app (.const ``Eq eqLevels) (.const ``Bool boolLevels)) e)
          (.const ``Bool.true trueLevels)) e

/-- `type` is the statement of an axiom that the native tactic `tactic` adds under the prefix
`parent`, and `asserted` is the Boolean expression that it asserts to be `true`. One constructor
for each tactic. -/
inductive Statement (parent : Name) : NativeTactic → Expr → Expr → Prop where
  /-- `native_decide` asserts `Decidable.decide p inst = true`. -/
  | nativeDecide {type : Expr} (levels : List Level) (p inst : Expr) :
      AssertsTrue type (.app (.app (.const ``Decidable.decide levels) p) inst) →
      Statement parent .nativeDecide type (.app (.app (.const ``Decidable.decide levels) p) inst)
  /-- `decide +native` asserts `Decidable.decide p inst = true`. -/
  | decideNative {type : Expr} (levels : List Level) (p inst : Expr) :
      AssertsTrue type (.app (.app (.const ``Decidable.decide levels) p) inst) →
      Statement parent .decideNative type (.app (.app (.const ``Decidable.decide levels) p) inst)
  /-- `bv_decide` asserts `verifyBVExpr expr cert = true`, where `expr` and `cert` are the
  constants of the `_expr_def` and `_cert_def` definitions that the generator made under the
  same prefix. -/
  | bvDecide {type : Expr} (levels exprLevels certLevels : List Level) (expr cert : Name) :
      AssertsTrue type
        (.app (.app (.const verifyBVExprName levels) (.const expr exprLevels))
          (.const cert certLevels)) →
      GeneratedAux "_expr_def" parent expr → GeneratedAux "_cert_def" parent cert →
      Statement parent .bvDecide type
        (.app (.app (.const verifyBVExprName levels) (.const expr exprLevels))
          (.const cert certLevels))

/-- A statement asserts its expression. -/
theorem Statement.asserts {parent : Name} {tactic : NativeTactic} {type asserted : Expr}
    (statement : Statement parent tactic type asserted) : AssertsTrue type asserted := by
  cases statement <;> assumption

/-- A type asserts one expression at most. -/
theorem AssertsTrue.unique {type first second : Expr} (left : AssertsTrue type first)
    (right : AssertsTrue type second) : first = second := by
  cases left
  cases right
  rfl

/-- A type is the statement of one expression at most, whatever the tactic and the prefix. -/
theorem Statement.unique {parent other : Name} {tactic otherTactic : NativeTactic}
    {type first second : Expr} (left : Statement parent tactic type first)
    (right : Statement other otherTactic type second) : first = second :=
  left.asserts.unique right.asserts

/-! ## Lean's functions on an application -/

/-- `Expr.isConstOf` answers `true` exactly for the constant of that name, at any levels. -/
theorem isConstOf_iff (e : Expr) (name : Name) :
    e.isConstOf name = true ↔ ∃ levels, e = .const name levels := by
  cases e <;> simp [Expr.isConstOf]

/-- `Expr.isConst` answers `true` exactly for a constant. -/
theorem isConst_iff (e : Expr) : e.isConst = true ↔ ∃ name levels, e = .const name levels := by
  cases e <;> simp [Expr.isConst]

/-- `Expr.isAppOfArity` at arity 2 answers `true` exactly for the constant of that name, at any
levels, applied to two arguments. -/
theorem isAppOfArity_two_iff (e : Expr) (name : Name) :
    e.isAppOfArity name 2 = true ↔ ∃ levels a b, e = .app (.app (.const name levels) a) b := by
  cases e with
  | app f b =>
    cases f with
    | app g a => cases g <;> simp [Expr.isAppOfArity]
    | _ => simp [Expr.isAppOfArity]
  | _ => simp [Expr.isAppOfArity]

private theorem getAppNumArgsAux_le (e : Expr) (n : Nat) : n ≤ Expr.getAppNumArgsAux e n := by
  induction e generalizing n with
  | app f a ihf _ => exact Nat.le_trans (Nat.le_succ n) (ihf (n + 1))
  | _ => simp [Expr.getAppNumArgsAux]

private theorem size_getAppArgsAux (e : Expr) (as : Array Expr) (i : Nat) :
    (Expr.getAppArgsAux e as i).size = as.size := by
  induction e generalizing as i with
  | app f a ihf _ => simp [Expr.getAppArgsAux, ihf]
  | _ => simp [Expr.getAppArgsAux]

/-- The number of the arguments `Expr.getAppArgs` returns is `Expr.getAppNumArgs`. -/
theorem size_getAppArgs (e : Expr) : e.getAppArgs.size = e.getAppNumArgs := by
  simp [Expr.getAppArgs, size_getAppArgsAux]

/-- A term with three arguments is a head that is no application, applied three times. -/
theorem eq_app_of_getAppNumArgs_three {e : Expr} (three : e.getAppNumArgs = 3) :
    ∃ head a b c, e = .app (.app (.app head a) b) c ∧ head.isApp = false := by
  unfold Expr.getAppNumArgs at three
  cases e with
  | app f c =>
    cases f with
    | app g b =>
      cases g with
      | app head a =>
        cases head with
        | app deeper d =>
          have := getAppNumArgsAux_le deeper 4
          simp [Expr.getAppNumArgsAux] at three
          omega
        | _ => exact ⟨_, a, b, c, rfl, rfl⟩
      | _ => simp [Expr.getAppNumArgsAux] at three
    | _ => simp [Expr.getAppNumArgsAux] at three
  | _ => simp [Expr.getAppNumArgsAux] at three

/-- The head and the arguments that Lean's functions give for a head that is no application,
applied three times. -/
theorem getApp_three {head a b c : Expr} (noApp : head.isApp = false) :
    (Expr.app (.app (.app head a) b) c).getAppFn = head ∧
      (Expr.app (.app (.app head a) b) c).getAppArgs = #[a, b, c] := by
  cases head <;> first
    | (simp [Expr.isApp] at noApp; done)
    | simp [Expr.getAppFn, Expr.getAppArgs, Expr.getAppNumArgs, Expr.getAppNumArgsAux,
        Expr.getAppArgsAux, Array.replicate]

/-- `assertedBool?` returns `e` exactly for a type that asserts `e`. -/
theorem assertedBool?_eq_some_iff (type e : Expr) :
    assertedBool? type = some e ↔ AssertsTrue type e := by
  constructor
  · intro accepted
    simp [assertedBool?, Option.bind_eq_some_iff, guard] at accepted
    obtain ⟨isEq, size, isBool, isTrue, rfl⟩ := accepted
    obtain ⟨head, a, b, c, rfl, noApp⟩ :=
      eq_app_of_getAppNumArgs_three ((size_getAppArgs type).symm.trans size)
    obtain ⟨fn, args⟩ := getApp_three (a := a) (b := b) (c := c) noApp
    rw [fn] at isEq
    rw [args] at isBool isTrue ⊢
    simp only [List.getElem!_toArray, List.getElem!_cons_zero, List.getElem!_cons_succ]
      at isBool isTrue ⊢
    obtain ⟨eqLevels, rfl⟩ := (isConstOf_iff _ _).mp isEq
    obtain ⟨boolLevels, rfl⟩ := (isConstOf_iff _ _).mp isBool
    obtain ⟨trueLevels, rfl⟩ := (isConstOf_iff _ _).mp isTrue
    exact .intro eqLevels boolLevels trueLevels b
  · rintro ⟨eqLevels, boolLevels, trueLevels, e⟩
    obtain ⟨fn, args⟩ := getApp_three (head := .const ``Eq eqLevels)
      (a := .const ``Bool boolLevels) (b := e) (c := .const ``Bool.true trueLevels) rfl
    simp [assertedBool?, guard, fn, args, Expr.isConstOf]

/-! ## The decision against the relation -/

/-- A guard before the rest of a computation in `Option`: the result is a value exactly when the
condition holds and the rest gives that value. -/
private theorem guard_bind_eq_some {condition : Prop} [Decidable condition] {α : Type}
    {rest : Unit → Option α} {value : α} :
    ((if condition then some () else failure : Option Unit).bind rest) = some value ↔
      condition ∧ rest () = some value := by
  by_cases holds : condition <;> simp [holds, failure]

/-- An accepted type is the statement of its tactic under its prefix, and the returned
expression is the one that the statement asserts. No hypothesis. -/
theorem asserted?_sound {candidate : Candidate} {asserted : Expr}
    (accepted : asserted? candidate = some asserted) :
    Statement candidate.parent candidate.tactic candidate.type asserted := by
  obtain ⟨tactic, parent, type⟩ := candidate
  simp only [asserted?, Option.bind_eq_bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨e, asserts, rest⟩ := accepted
  have asserts := (assertedBool?_eq_some_iff type e).mp asserts
  cases tactic <;>
    simp only [guard, Option.pure_def, guard_bind_eq_some, Option.some.injEq] at rest
  · obtain ⟨shape, rfl⟩ := rest
    obtain ⟨levels, p, inst, rfl⟩ := (isAppOfArity_two_iff _ _).mp shape
    exact .nativeDecide levels p inst asserts
  · obtain ⟨shape, rfl⟩ := rest
    obtain ⟨levels, p, inst, rfl⟩ := (isAppOfArity_two_iff _ _).mp shape
    exact .decideNative levels p inst asserts
  · obtain ⟨shape, names, rfl⟩ := rest
    obtain ⟨levels, expr, cert, rfl⟩ := (isAppOfArity_two_iff _ _).mp shape
    simp only [Expr.appFn!, Expr.appArg!, NativeTactic.auxiliaryInfixes, List.zip_cons_cons,
      List.zip_nil_right, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      beq_iff_eq] at names
    obtain ⟨⟨exprConst, exprParent⟩, certConst, certParent⟩ := names
    obtain ⟨exprName, exprLevels, rfl⟩ := (isConst_iff expr).mp exprConst
    obtain ⟨certName, certLevels, rfl⟩ := (isConst_iff cert).mp certConst
    exact .bvDecide levels exprLevels certLevels exprName certName asserts
      (generatedAuxParent?_sound exprParent) (generatedAuxParent?_sound certParent)

/-- A type that is the statement of its tactic under its prefix is accepted, with the
expression that the statement asserts. For `bv_decide` this needs `RuntimeStringAppend`: the
decision regenerates the names of the two auxiliary definitions with
`String.Internal.append`. For the two `decide` tactics it needs no hypothesis. -/
theorem asserted?_complete {candidate : Candidate} {asserted : Expr}
    (hAppend : candidate.tactic = .bvDecide → RuntimeStringAppend)
    (statement : Statement candidate.parent candidate.tactic candidate.type asserted) :
    asserted? candidate = some asserted := by
  obtain ⟨tactic, parent, type⟩ := candidate
  dsimp only at statement hAppend
  cases statement with
  | nativeDecide levels p inst asserts =>
    simp [asserted?, (assertedBool?_eq_some_iff _ _).mpr asserts, guard, Expr.isAppOfArity]
  | decideNative levels p inst asserts =>
    simp [asserted?, (assertedBool?_eq_some_iff _ _).mpr asserts, guard, Expr.isAppOfArity]
  | bvDecide levels exprLevels certLevels expr cert asserts exprAux certAux =>
    have append := hAppend rfl
    simp [asserted?, (assertedBool?_eq_some_iff _ _).mpr asserts, guard, Expr.isAppOfArity,
      Expr.appFn!, Expr.appArg!, NativeTactic.auxiliaryInfixes, Expr.isConst, Expr.constName!,
      generatedAuxParent?_of_generatedAux append (by simp) exprAux,
      generatedAuxParent?_of_generatedAux append (by simp) certAux]

/-- Under `RuntimeStringAppend`, the decision returns an expression exactly for a type that is
the statement of that expression. -/
theorem asserted?_eq_some_iff (hAppend : RuntimeStringAppend) (candidate : Candidate)
    (asserted : Expr) :
    asserted? candidate = some asserted ↔
      Statement candidate.parent candidate.tactic candidate.type asserted :=
  ⟨asserted?_sound, asserted?_complete fun _ => hAppend⟩

/-! ## The registered decision -/

/-- The recognition of a candidate: the Boolean expression that the decision returns for it, with
the proof that `asserted?` returns that expression for that candidate. So a value of this type
exists only for a candidate that the decision accepts, and it holds the expression of the
decision (`recognize?_eq_some`): a caller cannot build one for a different tactic, prefix, type
or expression. The observing pass takes this record. -/
structure Recognition (candidate : Candidate) where
  /-- The Boolean expression that the candidate's type asserts to be `true`. -/
  asserted : Expr
  /-- The decision returns that expression for the candidate. -/
  accepted : asserted? candidate = some asserted

/-- The candidate's type is the statement of the recognized expression, for the candidate's
tactic and prefix. -/
theorem Recognition.statement {candidate : Candidate} (recognition : Recognition candidate) :
    Statement candidate.parent candidate.tactic candidate.type recognition.asserted :=
  asserted?_sound recognition.accepted

/-- The recognition of a candidate, when its type is the statement of its tactic under its prefix
(`asserted?`). The function reads the tactic, the prefix and the type, and nothing else. -/
@[regula_decision]
def recognize? (candidate : Candidate) : Option (Recognition candidate) :=
  match accepted : asserted? candidate with
  | some asserted => some ⟨asserted, accepted⟩
  | none => none

/-- Each recognition of a candidate is the one that the decision gives for that candidate. So
the type of the result links what the pass evaluates to the candidate: no value of
`Recognition candidate` is anything but the result of `recognize? candidate`. -/
theorem recognize?_eq_some {candidate : Candidate} (recognition : Recognition candidate) :
    recognize? candidate = some recognition := by
  obtain ⟨asserted, accepted⟩ := recognition
  unfold recognize?
  split
  · rename_i found returned
    obtain rfl : found = asserted := Option.some.inj (returned.symm.trans accepted)
    rfl
  · rename_i refused
    rw [refused] at accepted
    cases accepted

/-- A candidate that the decision refuses has no recognition. -/
theorem Recognition.not_refused {candidate : Candidate} (recognition : Recognition candidate) :
    recognize? candidate ≠ none := by
  rw [recognize?_eq_some recognition]
  exact Option.some_ne_none recognition

/-- `recognize?` gives a recognition exactly where `asserted?` gives an expression. -/
theorem isSome_recognize? (candidate : Candidate) :
    (recognize? candidate).isSome = (asserted? candidate).isSome := by
  unfold recognize?
  split <;> simp [*]

/-- The candidate's type is the statement of its tactic under its prefix, for some
expression. -/
def Stated (candidate : Candidate) : Prop :=
  ∃ asserted, Statement candidate.parent candidate.tactic candidate.type asserted

/-- The type of the statement `decide True = true`, which `native_decide` asserts for the
proposition `True`. -/
def decideTrue : Expr :=
  .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool []))
    (.app (.app (.const ``Decidable.decide []) (.const ``True []))
      (.const ``instDecidableTrue []))) (.const ``Bool.true [])

/-- `recognize?` is a sound decision of the statements of the native tactics: it gives a
recognition only for a type that is the statement of the candidate's tactic under the
candidate's prefix (`asserted?_sound`, with no hypothesis), and it accepts the statement
`decide True = true` of `native_decide`. Its result type depends on the candidate, since a
recognition holds the proof about that candidate, so the decision is of whether a recognition is
given (`Regula.Dependent.isSome`).

The kind is one-way for a reason the logic gives. A related type is accepted where the names of
the auxiliary definitions of `bv_decide` are regenerated by concatenation
(`asserted?_complete`, under `RuntimeStringAppend` for that tactic and with no hypothesis for
the two `decide` tactics), and a two-way kind has no hypothesis. A refusal fails closed: an
axiom with no recognized statement is not authenticated. -/
theorem checked_recognize : Regula.ExecutableContract recognize? (fun decision =>
    Regula.DecidesSoundly (· = true) Stated (Regula.Dependent.isSome decision)) :=
  ⟨{ sound := fun candidate accepted => by
       rw [Regula.Dependent.isSome, isSome_recognize?] at accepted
       obtain ⟨asserted, found⟩ := Option.isSome_iff_exists.mp accepted
       exact ⟨asserted, asserted?_sound found⟩
     accepted := ⟨⟨.nativeDecide, .anonymous, decideTrue⟩, by
       rw [Regula.Dependent.isSome, isSome_recognize?,
         asserted?_complete (candidate := ⟨.nativeDecide, .anonymous, decideTrue⟩)
           (fun bv => by cases bv) (.nativeDecide _ _ _ (.intro _ _ _ _))]
       rfl⟩ }⟩

/-- A type that asserts no expression is refused, whatever the tactic and the prefix. -/
theorem asserted?_eq_none_of_not_asserts {candidate : Candidate}
    (refuted : ∀ asserted, ¬ AssertsTrue candidate.type asserted) :
    asserted? candidate = none := by
  cases found : asserted? candidate with
  | none => rfl
  | some asserted => exact absurd (asserted?_sound found).asserts (refuted asserted)

end RegulaPolicy.NativeStatement
