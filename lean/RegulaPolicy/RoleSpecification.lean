module

public import RegulaPolicy.Foundation

/-! # Generated-role relations

Generated-role relations over the complete observation inventory. Each component
states exact metadata, value/equation observations, ordered attribution, and uniqueness.
These finite decidable relations do not attest that a compiler observation is truthful. -/

@[expose] public section

namespace RegulaPolicy
open Lean (Name)
open Frontend

/-- The declaration a generated `native_decide` axiom name belongs to: for
`parent._native.native_decide.ax_N…` with a nonanonymous `parent` and a suffix of `ax_` then
`_`-separated nonempty digit runs, `some parent`; otherwise `none`. -/
def nativeParent? : Name → Option Name
  | .str (.str (.str parent "_native") "native_decide") suffix => do
      guard (parent != .anonymous && suffix.startsWith "ax_")
      let numbers := (suffix.drop 3).toString.splitOn "_"
      guard (!numbers.isEmpty && numbers.all fun n => !n.isEmpty && n.toList.all Char.isDigit)
      return parent
  | _ => none

/-- Only declaration kinds that could receive a generated-role exception need
the extra fresh frontend transcript. This core works over primitive fields so
a batched harness can apply the identical predicate to raw environment
constant records before paying any environment load. -/
def declarationNeedsTranscript (isUnsafe isPartial : Bool) (kind : DeclarationKind) (name : Name) : Bool :=
  isUnsafe || isPartial || (kind == .«axiom» && (nativeParent? name).isSome)

/-- Only declaration kinds that could receive a generated-role exception need
the extra fresh frontend transcript. -/
def needsFrontendTranscript (decls : Array Declaration) : Bool :=
  decls.any fun decl =>
    declarationNeedsTranscript decl.isUnsafe decl.isPartial decl.kind decl.name

/-- Lean's command elaborator for a declaration command. -/
def declarationElaborator := `Lean.Elab.Command.elabDeclaration
/-- Lean's macro that expands a declaration with a namespaced name into a `namespace` block. -/
def namespacedDeclarationElaborator :=
  `Lean.Elab.Command.expandNamespacedDeclaration
/-- The syntax kind of a declaration command. -/
def declarationKind := `Lean.Parser.Command.declaration
/-- Lean's tactic elaborator for `native_decide`. -/
def nativeDecideElaborator := `Lean.Elab.Tactic.evalNativeDecide
/-- The syntax kind of the `native_decide` tactic. -/
def nativeDecideKind := `Lean.Parser.Tactic.nativeDecide

/-- The part of an evaluator observation that identifies it in an evaluator chain. -/
structure EvaluatorKey where
  /-- Whether the evaluator elaborated a command, a tactic or a term. -/
  role : EvaluatorRole
  /-- The elaborator's declaration name (anonymous when none was recorded). -/
  elaborator : Name
  /-- The syntax kind the evaluator elaborated. -/
  kind : Name
  deriving Repr, DecidableEq

/-- The role, elaborator and syntax kind of an evaluator observation. -/
def key (value : Evaluator) : EvaluatorKey :=
  { role := value.role, elaborator := value.elaborator, kind := value.kind }

/-- The only non-term evaluator sequence `NativeCommand` accepts: the declaration command,
then its `by` block and tactic sequence, then `native_decide`, in that order. -/
def nativeDecideChain : Array EvaluatorKey := #[
  ⟨.command, declarationElaborator, declarationKind⟩,
  ⟨.tactic, .anonymous, `Lean.Parser.Term.byTactic⟩,
  ⟨.tactic, .anonymous, `by⟩,
  ⟨.tactic, `Lean.Elab.Tactic.evalTacticSeq, `Lean.Parser.Tactic.tacticSeq⟩,
  ⟨.tactic, `Lean.Elab.Tactic.evalTacticSeq1Indented,
    `Lean.Parser.Tactic.tacticSeq1Indented⟩,
  ⟨.tactic, nativeDecideElaborator, nativeDecideKind⟩
]


/-- Source containment uses the lexicographic codepoint position order. -/
def PositionLE (a b : Position) : Prop :=
  a.line < b.line ∨ (a.line = b.line ∧ a.column ≤ b.column)
instance (a b : Position) : Decidable (PositionLE a b) := by unfold PositionLE; infer_instance

/-- The start and end of a declaration's full recorded range, when Lean recorded one. -/
def declarationRange? (d : Declaration) : Option SyntaxRange :=
  d.ranges.map fun r => ⟨r.range.start, r.range.end⟩

/-- Preserve command occurrence order and multiplicity, including duplicate observations. -/
def moduleCommands (ts : Array Transcript) (m : Name) : Array Command :=
  (ts.filter (fun t => t.module == m)).flatMap (·.commands)

/-- Exactly one occurrence introduces this declaration; identical duplicates are ambiguous. -/
def IntroducingCommand (ts : Array Transcript) (m n : Name) (c : Command) : Prop :=
  (moduleCommands ts m).filter (fun c => c.added.contains n) = #[c]
instance (ts : Array Transcript) (m n : Name) (c : Command) :
    Decidable (IntroducingCommand ts m n c) := by unfold IntroducingCommand; infer_instance

/-- The native observation must match exactly one added axiom in exactly one command. -/
def NativeIntroducingCommand (ts : Array Transcript) (a : Declaration) (parent : Name)
    (c : Command) : Prop :=
  (moduleCommands ts a.module).filter (fun cmd =>
    (cmd.addedDeclarations.filter (fun d => nativeParent? d.name == some parent &&
      d.kind == .«axiom» && d.type == a.type)).size == 1) = #[c]
instance (ts : Array Transcript) (a : Declaration) (p : Name) (c : Command) :
    Decidable (NativeIntroducingCommand ts a p c) := by unfold NativeIntroducingCommand; infer_instance

/-- Literal declaration origin, including the exact built-in dotted-name expansion. -/
def LiteralDeclaration (c : Command) (r : SyntaxRange) : Prop :=
  c.commandKind = declarationKind ∧ c.commandRange = some r ∧
  (c.commandElaborator = declarationElaborator ∨
    (c.commandElaborator = namespacedDeclarationElaborator ∧
      (c.evaluators.filter (fun e => e.role == .command &&
        e.elaborator == declarationElaborator && e.kind == declarationKind &&
        e.range == some r)).size = 1))
instance (c : Command) (r : SyntaxRange) : Decidable (LiteralDeclaration c r) := by
  unfold LiteralDeclaration; infer_instance

/-- Every recorded evaluator is pinned and excludes audited-source metaprogram execution. -/
def PinnedEvaluator (e : Evaluator) : Prop :=
  e.pinned = true ∧ e.elaborator ≠ `Lean.Elab.Tactic.evalRunTac ∧
    e.elaborator ≠ `Lean.Elab.Term.elabRunElab
instance (e : Evaluator) : Decidable (PinnedEvaluator e) := by unfold PinnedEvaluator; infer_instance

/-- Nested binders require exact selection attribution as well as source containment. -/
def RecursiveCommand (c : Command) (base : Declaration) (r : SyntaxRange) : Prop :=
  (LiteralDeclaration c r ∨
    ∃ outer ∈ c.commandRange, ∃ ranges ∈ base.ranges,
      LiteralDeclaration c outer ∧ PositionLE outer.start r.start ∧ PositionLE r.end outer.end ∧
      ∃ b ∈ c.bindings, b.name = base.name ∧
        b.range = some ⟨ranges.selectionRange.start, ranges.selectionRange.end⟩) ∧
  ∀ e ∈ c.evaluators, PinnedEvaluator e
instance (c : Command) (b : Declaration) (r : SyntaxRange) : Decidable (RecursiveCommand c b r) := by
  unfold RecursiveCommand; infer_instance

/-- Native teaching permits exactly the pinned complete non-term evaluator sequence. -/
def NativeCommand (c : Command) (r : SyntaxRange) : Prop :=
  LiteralDeclaration c r ∧ (∀ e ∈ c.evaluators, PinnedEvaluator e) ∧
  (c.evaluators.filter (·.role != .term)).map key = nativeDecideChain
instance (c : Command) (r : SyntaxRange) : Decidable (NativeCommand c r) := by
  unfold NativeCommand; infer_instance

/-- Native axiom shape and successful independent replay observations. -/
def NativeAxiomShape (a : Declaration) : Prop :=
  a.kind = .«axiom» ∧ a.internal = true ∧ a.isProp = true ∧
  a.isUnsafe = false ∧ a.isPartial = false ∧ a.implementedBy = none ∧ a.extern = false ∧
  a.nativeBoolShape = true ∧ a.nativeReplay = some true ∧ a.name ∈ a.axioms ∧
  ∀ n ∈ a.axioms, n = a.name ∨ Permitted .standardLogical n
instance (a : Declaration) : Decidable (NativeAxiomShape a) := by unfold NativeAxiomShape; infer_instance

/-- Exact supported parent and recorded use shape, with no safety/runtime escape. -/
def NativeParentShape (a p : Declaration) : Prop :=
  p.isProp = true ∧ p.kind ∈ #[DeclarationKind.theorem, .opaque, .definition] ∧
  p.module = a.module ∧ a.name ∈ p.axioms ∧ a.nativeUseParents = #[p.name] ∧
  p.isUnsafe = false ∧ p.isPartial = false ∧ p.implementedBy = none ∧ p.extern = false
instance (a p : Declaration) : Decidable (NativeParentShape a p) := by unfold NativeParentShape; infer_instance

/-- All native teaching requirements jointly hold, including unique use and introduction.
Names locate a candidate; the remaining relations supply the required data-level evidence. -/
def NativeTeachingOK (ds : Array Declaration) (ts : Array Transcript) (a : Declaration) : Prop :=
  NativeAxiomShape a ∧ a ∈ ds ∧ ∃ p ∈ ds,
    nativeParent? a.name = some p.name ∧ NativeParentShape a p ∧
    (ds.filter (fun d => d.valueConstants.contains a.name)) = #[p] ∧
    ∃ pr ∈ declarationRange? p, ∃ ar ∈ declarationRange? a,
      PositionLE pr.start ar.start ∧ PositionLE ar.end pr.end ∧
      ExactlyOne ((moduleCommands ts p.module).filter (fun c => c.added.contains p.name)) (fun c =>
        NativeIntroducingCommand ts a p.name c ∧ NativeCommand c pr ∧ p.name ∈ c.added ∧
        ExactlyOne (c.evaluators.filter (fun e => e.role == .tactic &&
          e.elaborator == nativeDecideElaborator && e.kind == nativeDecideKind)) (fun e =>
          e.range = some ar))
instance (ds : Array Declaration) (ts : Array Transcript) (a : Declaration) :
    Decidable (NativeTeachingOK ds ts a) := by unfold NativeTeachingOK; infer_instance

/-- Range-less generated partial helper with all value and equation checks retained. -/
def RecursiveHelperShape (h : Declaration) : Prop :=
  h.kind = .definition ∧ h.internal = true ∧ h.ranges = none ∧ h.isPartial = true ∧
  h.isUnsafe = false ∧ h.hints = some .opaque ∧ h.implementedBy = none ∧ h.extern = false ∧
  h.unsafeRecValueOrigin.isSome = true ∧ h.unsafeRecValueExact = some true ∧
  h.unsafeRecValueDefeq = some true ∧ h.unsafeRecEquationExact = some true ∧
  h.unsafeRecEquationDefeq = some true
instance (h : Declaration) : Decidable (RecursiveHelperShape h) := by unfold RecursiveHelperShape; infer_instance

/-- Safe recursive base, exact type/universes, and bounded helper/equation dependencies. -/
def RecursiveBaseShape (h b : Declaration) : Prop :=
  b.kind = .definition ∧ h.module = b.module ∧ b.isPartial = false ∧ b.isUnsafe = false ∧
  b.hints = some .regular ∧ b.recursive = true ∧ b.implementedBy = none ∧ b.extern = false ∧
  h.type = b.type ∧ h.levelParams = b.levelParams ∧ (∀ n ∈ h.axioms, n ∈ b.axioms) ∧
  ∃ eqAxioms ∈ h.unsafeRecEquationAxioms,
    ∀ n ∈ eqAxioms, Permitted .standardLogical n ∨ n ∈ b.axioms
instance (h b : Declaration) : Decidable (RecursiveBaseShape h b) := by unfold RecursiveBaseShape; infer_instance

/-- Mutual-group order is preserved, with exact helper transformation and self-reference. -/
def RecursiveGroup (h b : Declaration) : Prop :=
  b.all ≠ #[] ∧ h.all = b.all.map (fun n => Name.str n "_unsafe_rec") ∧
  h.name ∈ b.all.map (fun n => Name.str n "_unsafe_rec") ∧ h.name ∈ h.valueConstants
instance (h b : Declaration) : Decidable (RecursiveGroup h b) := by unfold RecursiveGroup; infer_instance

/-- Every recursive-helper guard is required for one base and the same unique command. -/
def RecursiveHelperOK (ds : Array Declaration) (ts : Array Transcript) (h : Declaration) : Prop :=
  RecursiveHelperShape h ∧ h ∈ ds ∧ ∃ b ∈ ds,
    h.unsafeRecBase = some b.name ∧ RecursiveBaseShape h b ∧ RecursiveGroup h b ∧
    ∃ br ∈ declarationRange? b,
      ExactlyOne ((moduleCommands ts h.module).filter (fun c => c.added.contains h.name)) (fun c =>
        IntroducingCommand ts b.module b.name c ∧ RecursiveCommand c b br ∧
        (∀ n ∈ b.all, n ∈ c.added) ∧
        ∀ n ∈ b.all.map (fun n => Name.str n "_unsafe_rec"), n ∈ c.added)
instance (ds : Array Declaration) (ts : Array Transcript) (h : Declaration) :
    Decidable (RecursiveHelperOK ds ts h) := by unfold RecursiveHelperOK; infer_instance

end RegulaPolicy
