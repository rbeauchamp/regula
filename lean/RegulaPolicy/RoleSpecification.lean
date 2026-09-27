module

public import RegulaPolicy.NativeAxiom

/-! # Generated-role relations

Generated-role relations over the complete observation inventory. Each component
states exact metadata, value/equation observations, ordered attribution, and uniqueness.
These finite decidable relations do not attest that a compiler observation is truthful. -/

@[expose] public section

namespace RegulaPolicy
open Lean (Name)
open Frontend

/-- Only declaration kinds that could receive a generated-role exception need
the extra fresh frontend transcript. This core works over primitive fields so
a batched harness can apply the identical predicate to raw environment
constant records before paying any environment load. -/
def declarationNeedsTranscript (isUnsafe isPartial : Bool) (kind : DeclarationKind)
    (name : Name) : Bool :=
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

/-- The key of native evaluator `e`: its pinned tactic elaborator and syntax kind. -/
def NativeEvaluator.evaluatorKey (e : NativeEvaluator) : EvaluatorKey :=
  ⟨.tactic, e.elaborator, e.syntaxKind⟩

/-- The declaration command, then its `by` block and single-step tactic sequence. -/
def byBlockKeys : Array EvaluatorKey := #[
  ⟨.command, declarationElaborator, declarationKind⟩,
  ⟨.tactic, .anonymous, `Lean.Parser.Term.byTactic⟩,
  ⟨.tactic, .anonymous, `by⟩,
  ⟨.tactic, `Lean.Elab.Tactic.evalTacticSeq, `Lean.Parser.Tactic.tacticSeq⟩,
  ⟨.tactic, `Lean.Elab.Tactic.evalTacticSeq1Indented,
    `Lean.Parser.Tactic.tacticSeq1Indented⟩]

/-- The two ways a `by` block's single tactic enters `grind`'s interactive mode, each followed by
its single-step `grind` sequence (`evalGrindSeq`, `evalGrindSeq1Indented`, private to
`Lean.Elab.Tactic.Grind.BuiltinTactic`). -/
def grindModeKeys : List (Array EvaluatorKey) :=
  [⟨.tactic, `Lean.Elab.Tactic.evalGrind, `Lean.Parser.Tactic.grind⟩,
    ⟨.tactic, `Lean.Elab.Tactic.evalSym, `Lean.Parser.Tactic.sym⟩].map fun entry => #[entry,
      ⟨.tactic, Lean.mkPrivateNameCore `Lean.Elab.Tactic.Grind.BuiltinTactic
        `Lean.Elab.Tactic.Grind.evalGrindSeq, `Lean.Parser.Tactic.Grind.grindSeq⟩,
      ⟨.tactic, Lean.mkPrivateNameCore `Lean.Elab.Tactic.Grind.BuiltinTactic
        `Lean.Elab.Tactic.Grind.evalGrindSeq1Indented, `Lean.Parser.Tactic.Grind.grindSeq1Indented⟩]

/-- The built-in expansion of a declaration named `A.b` into `namespace A`, the declaration `b`
and `end A` (`expandNamespacedDeclaration`, `Lean/Elab/Declaration.lean:150`), around the keys
of that inner declaration. -/
def namespacedKeys (inner : Array EvaluatorKey) : Array EvaluatorKey :=
  #[⟨.command, namespacedDeclarationElaborator, declarationKind⟩,
    ⟨.command, `Lean.Elab.Command.elabNamespace, `Lean.Parser.Command.namespace⟩,
    ⟨.command, `Lean.Elab.Command.elabEndLocalScope,
      `Lean.Parser.Command.InternalSyntax.end_local_scope⟩] ++ inner ++
  #[⟨.command, `Lean.Elab.Command.elabEnd, `Lean.Parser.Command.end⟩]

/-- The only non-term evaluator sequences `NativeCommand e` accepts: the declaration command, its
`by` block and tactic sequence, then the tactic of `e` alone, or for a grind-mode `e`, `grind =>`
or `sym =>` alone with the tactic of `e` as its whole sequence, in that order; each also inside
the built-in expansion of a namespaced declaration name. -/
def nativeTacticChains (e : NativeEvaluator) : List (Array EvaluatorKey) :=
  let direct := if e.grindMode then grindModeKeys.map fun keys => byBlockKeys ++ keys.push
      e.evaluatorKey
    else [byBlockKeys.push e.evaluatorKey]
  direct ++ direct.map namespacedKeys

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

/-- The native observation must match exactly one added axiom in exactly one command: the same
generated origin (the recognized prefix `pfx`, in the same privacy form, and tactic `t`) and the
same asserted statement. The statement names the tactic run's own auxiliary definitions by their
unindexed base (`nativeStatement`), since a fresh transcript and an asynchronous build can index
generated names differently. -/
def NativeIntroducingCommand (ts : Array Transcript) (a : Declaration) (t : NativeTactic)
    (pfx : Name) (c : Command) : Prop :=
  (moduleCommands ts a.module).filter (fun cmd =>
    (cmd.addedDeclarations.filter (fun d => nativeAxiomOrigin? d.name == some (pfx, t) &&
      d.kind == .«axiom» && d.nativeStatement == a.nativeStatement)).size == 1) = #[c]
instance (ts : Array Transcript) (a : Declaration) (t : NativeTactic) (pfx : Name) (c : Command) :
    Decidable (NativeIntroducingCommand ts a t pfx c) := by
        unfold NativeIntroducingCommand; infer_instance

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
instance (e : Evaluator) : Decidable (PinnedEvaluator e) := by
    unfold PinnedEvaluator; infer_instance

/-- Nested binders require exact selection attribution as well as source containment. -/
def RecursiveCommand (c : Command) (base : Declaration) (r : SyntaxRange) : Prop :=
  (LiteralDeclaration c r ∨
    ∃ outer ∈ c.commandRange, ∃ ranges ∈ base.ranges,
      LiteralDeclaration c outer ∧ PositionLE outer.start r.start ∧ PositionLE r.end outer.end ∧
      ∃ b ∈ c.bindings, b.name = base.name ∧
        b.range = some ⟨ranges.selectionRange.start, ranges.selectionRange.end⟩) ∧
  ∀ e ∈ c.evaluators, PinnedEvaluator e
instance (c : Command) (b : Declaration) (r : SyntaxRange) : Decidable
    (RecursiveCommand c b r) := by
  unfold RecursiveCommand; infer_instance

/-- Native teaching permits exactly a pinned complete non-term evaluator sequence of `e`. -/
def NativeCommand (e : NativeEvaluator) (c : Command) (r : SyntaxRange) : Prop :=
  LiteralDeclaration c r ∧ (∀ v ∈ c.evaluators, PinnedEvaluator v) ∧
  (c.evaluators.filter (·.role != .term)).map key ∈ nativeTacticChains e
instance (e : NativeEvaluator) (c : Command) (r : SyntaxRange) :
    Decidable (NativeCommand e c r) := by
  unfold NativeCommand; infer_instance

/-- The evaluator `e` is the command's complete pinned evaluator sequence over the parent's range
`pr`, and exactly one observation of it has the axiom's range `ar`. -/
def NativeEvaluatorCommand (e : NativeEvaluator) (c : Command) (pr ar : SyntaxRange) : Prop :=
  NativeCommand e c pr ∧
    ExactlyOne (c.evaluators.filter (fun v => v.role == .tactic &&
      v.elaborator == e.elaborator && v.kind == e.syntaxKind)) (fun v => v.range = some ar)
instance (e : NativeEvaluator) (c : Command) (pr ar : SyntaxRange) :
    Decidable (NativeEvaluatorCommand e c pr ar) := by
  unfold NativeEvaluatorCommand; infer_instance

/-- Native axiom shape, the asserted statement of its tactic and successful independent replay
observations. -/
def NativeAxiomShape (a : Declaration) : Prop :=
  a.kind = .«axiom» ∧ a.internal = true ∧ a.isProp = true ∧
  a.isUnsafe = false ∧ a.isPartial = false ∧ a.implementedBy = none ∧ a.extern = false ∧
  a.nativeStatement.isSome = true ∧ a.nativeReplay = some true ∧ a.name ∈ a.axioms ∧
  ∀ n ∈ a.axioms, n = a.name ∨ Permitted .standardLogical n
instance (a : Declaration) : Decidable (NativeAxiomShape a) := by
    unfold NativeAxiomShape; infer_instance

/-- Exact supported parent, with no safety/runtime escape. -/
def NativeParentShape (a p : Declaration) : Prop :=
  p.isProp = true ∧ p.kind ∈ #[DeclarationKind.theorem, .opaque, .definition] ∧
  p.module = a.module ∧ a.name ∈ p.axioms ∧
  p.isUnsafe = false ∧ p.isPartial = false ∧ p.implementedBy = none ∧ p.extern = false
instance (a p : Declaration) : Decidable (NativeParentShape a p) := by
    unfold NativeParentShape; infer_instance

/-- The auxiliary theorem into which `grind`'s `abstractProof` moves the proof of the parent `p`
(`Grind.main`'s `finalize`, `Lean/Meta/Tactic/Grind/Main.lean:491-495`, through `mkAuxLemma`,
which names it with the generator's `_proof` infix under the same prefix `pfx`): a safe internal
proposition theorem of `p`'s module, used by `p` alone. -/
def NativeAuxProof (ds : Array Declaration) (pfx : Name) (p u : Declaration) : Prop :=
  generatedAuxParent? "_proof" u.name = some pfx ∧ u.kind = .theorem ∧ u.internal = true ∧
  u.isProp = true ∧ u.module = p.module ∧ u.isUnsafe = false ∧ u.isPartial = false ∧
  u.implementedBy = none ∧ u.extern = false ∧
  (ds.filter (fun d => d.valueConstants.contains u.name)) = #[p]
instance (ds : Array Declaration) (pfx : Name) (p u : Declaration) :
    Decidable (NativeAuxProof ds pfx p u) := by
  unfold NativeAuxProof; infer_instance

/-- The declaration `u` whose proof uses the axiom `a`: its unique direct user and unique
exact-bridge user, which is the parent `p` itself or, for a grind-mode evaluator `e`, `p`'s
auxiliary proof. -/
def NativeUser (ds : Array Declaration) (e : NativeEvaluator) (pfx : Name) (a p u : Declaration) :
    Prop :=
  a.nativeUseParents = #[u.name] ∧ (ds.filter (fun d => d.valueConstants.contains a.name)) = #[u] ∧
  (u = p ∨ (e.grindMode = true ∧ NativeAuxProof ds pfx p u))
instance (ds : Array Declaration) (e : NativeEvaluator) (pfx : Name) (a p u : Declaration) :
    Decidable (NativeUser ds e pfx a p u) := by
  unfold NativeUser; infer_instance

/-- The native role of `a` for the parent `p`, the generated prefix `pfx` and tactic `t` of `a`'s
name, and the evaluator `e`: `e` passes `t`, `pfx` is a generated prefix of `p` in its own module,
the parent and user shapes hold, the ranges nest, and exactly one command introduces `p`, adding
the one matching axiom under the complete pinned evaluator sequence of `e`. -/
def NativeRoleOK (ds : Array Declaration) (ts : Array Transcript) (a p : Declaration) (pfx : Name)
    (t : NativeTactic) (e : NativeEvaluator) : Prop :=
  e.family = t ∧ GeneratedPrefix p.module p.name pfx ∧ NativeParentShape a p ∧
    (∃ u ∈ ds, NativeUser ds e pfx a p u) ∧
    ∃ pr ∈ declarationRange? p, ∃ ar ∈ declarationRange? a,
      PositionLE pr.start ar.start ∧ PositionLE ar.end pr.end ∧
      ExactlyOne ((moduleCommands ts p.module).filter (fun c => c.added.contains p.name)) (fun c =>
        NativeIntroducingCommand ts a t pfx c ∧ p.name ∈ c.added ∧ NativeEvaluatorCommand e c pr ar)
instance (ds : Array Declaration) (ts : Array Transcript) (a p : Declaration) (pfx : Name)
    (t : NativeTactic) (e : NativeEvaluator) : Decidable (NativeRoleOK ds ts a p pfx t e) := by
  unfold NativeRoleOK; infer_instance

/-- All native teaching requirements jointly hold, including unique use and introduction.
The name locates a generated prefix of the parent in its own module and a native tactic
(`nativeAxiomOrigin?`, `GeneratedPrefix`); the remaining relations supply the required
data-level evidence, including an evaluator of that tactic's name family. -/
def NativeTeachingOK (ds : Array Declaration) (ts : Array Transcript) (a : Declaration) : Prop :=
  NativeAxiomShape a ∧ a ∈ ds ∧ ∃ p ∈ ds, ∃ o ∈ nativeAxiomOrigin? a.name, ∃ e : NativeEvaluator,
    NativeRoleOK ds ts a p o.1 o.2 e
instance (ds : Array Declaration) (ts : Array Transcript) (a : Declaration) :
    Decidable (NativeTeachingOK ds ts a) := by unfold NativeTeachingOK; infer_instance

/-- Range-less generated partial helper with all value and equation checks retained. -/
def RecursiveHelperShape (h : Declaration) : Prop :=
  h.kind = .definition ∧ h.internal = true ∧ h.ranges = none ∧ h.isPartial = true ∧
  h.isUnsafe = false ∧ h.hints = some .opaque ∧ h.implementedBy = none ∧ h.extern = false ∧
  h.unsafeRecValueOrigin.isSome = true ∧ h.unsafeRecValueExact = some true ∧
  h.unsafeRecValueDefeq = some true ∧ h.unsafeRecEquationExact = some true ∧
  h.unsafeRecEquationDefeq = some true
instance (h : Declaration) : Decidable (RecursiveHelperShape h) := by
    unfold RecursiveHelperShape; infer_instance

/-- Safe recursive base, exact type/universes, and bounded helper/equation dependencies. -/
def RecursiveBaseShape (h b : Declaration) : Prop :=
  b.kind = .definition ∧ h.module = b.module ∧ b.isPartial = false ∧ b.isUnsafe = false ∧
  b.hints = some .regular ∧ b.recursive = true ∧ b.implementedBy = none ∧ b.extern = false ∧
  h.type = b.type ∧ h.levelParams = b.levelParams ∧ (∀ n ∈ h.axioms, n ∈ b.axioms) ∧
  ∃ eqAxioms ∈ h.unsafeRecEquationAxioms,
    ∀ n ∈ eqAxioms, Permitted .standardLogical n ∨ n ∈ b.axioms
instance (h b : Declaration) : Decidable (RecursiveBaseShape h b) := by
    unfold RecursiveBaseShape; infer_instance

/-- Mutual-group order is preserved, with exact helper transformation and self-reference. -/
def RecursiveGroup (h b : Declaration) : Prop :=
  b.all ≠ #[] ∧ h.all = b.all.map (fun n => Name.str n "_unsafe_rec") ∧
  h.name ∈ b.all.map (fun n => Name.str n "_unsafe_rec") ∧ h.name ∈ h.valueConstants
instance (h b : Declaration) : Decidable (RecursiveGroup h b) := by
    unfold RecursiveGroup; infer_instance

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
