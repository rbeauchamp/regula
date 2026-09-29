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

/-- `c` is the one command of `a`'s module that adds an axiom of the generated origin `(pfx, t)`
(the recognized prefix, in the same privacy form, and tactic) with `a`'s asserted statement. The
match is by origin and statement, never by exact name: the statement names the tactic run's own
auxiliary definitions by their unindexed base (`nativeStatement`), since a fresh transcript and an
asynchronous build can index generated names differently. -/
def NativeIntroducingCommand (ts : Array Transcript) (a : Declaration) (t : NativeTactic)
    (pfx : Name) (c : Command) : Prop :=
  (moduleCommands ts a.module).filter (fun cmd =>
    cmd.addedDeclarations.any (fun d => nativeAxiomOrigin? d.name == some (pfx, t) &&
      d.kind == .«axiom» && d.nativeStatement == a.nativeStatement)) = #[c]
instance (ts : Array Transcript) (a : Declaration) (t : NativeTactic) (pfx : Name) (c : Command) :
    Decidable (NativeIntroducingCommand ts a t pfx c) := by
        unfold NativeIntroducingCommand; infer_instance

/-- Lean's command elaborator for a `mutual … end` block. -/
def mutualElaborator := `Lean.Elab.Command.elabMutual
/-- The syntax kind of a `mutual … end` block. -/
def mutualKind := `Lean.Parser.Command.mutual

/-- Literal declaration origin, including the exact built-in dotted-name expansion, or a literal
`mutual … end` block, which Lean's built-in `elabMutual` elaborates as one command. -/
def LiteralDeclaration (c : Command) (r : SyntaxRange) : Prop :=
  c.commandRange = some r ∧
  ((c.commandKind = declarationKind ∧
    (c.commandElaborator = declarationElaborator ∨
      (c.commandElaborator = namespacedDeclarationElaborator ∧
        (c.evaluators.filter (fun e => e.role == .command &&
          e.elaborator == declarationElaborator && e.kind == declarationKind &&
          e.range == some r)).size = 1))) ∨
   (c.commandKind = mutualKind ∧ c.commandElaborator = mutualElaborator))
instance (c : Command) (r : SyntaxRange) : Decidable (LiteralDeclaration c r) := by
  unfold LiteralDeclaration; infer_instance

/-- Every recorded evaluator is pinned and excludes audited-source metaprogram execution. -/
def PinnedEvaluator (e : Evaluator) : Prop :=
  e.pinned = true ∧ e.elaborator ≠ `Lean.Elab.Tactic.evalRunTac ∧
    e.elaborator ≠ `Lean.Elab.Term.elabRunElab
instance (e : Evaluator) : Decidable (PinnedEvaluator e) := by
    unfold PinnedEvaluator; infer_instance

/-- The base is the literal declaration, a nested one bound at its exact selection range, or,
contained in the literal command, one that elaboration generated from syntax with no canonical
source range (every binder record of its name has no range, as for a derived instance's
function). Every recorded evaluator is pinned, and no audited-source code can have run
unrecorded (`Command.sourceLocalCode` is empty): such code could have produced or rewritten the
records, and some of it runs without a record, as inside `simp` or where Lean elaborates a derived
`DecidableEq` comparison with information trees disabled. -/
def RecursiveCommand (c : Command) (base : Declaration) (r : SyntaxRange) : Prop :=
  (LiteralDeclaration c r ∨
    ∃ outer ∈ c.commandRange, ∃ ranges ∈ base.ranges,
      LiteralDeclaration c outer ∧ PositionLE outer.start r.start ∧ PositionLE r.end outer.end ∧
      ((∃ b ∈ c.bindings, b.name = base.name ∧
        b.range = some ⟨ranges.selectionRange.start, ranges.selectionRange.end⟩) ∨
       ∀ b ∈ c.bindings, b.name = base.name → b.range = none)) ∧
  (∀ e ∈ c.evaluators, PinnedEvaluator e) ∧ c.sourceLocalCode = #[]
instance (c : Command) (b : Declaration) (r : SyntaxRange) : Decidable
    (RecursiveCommand c b r) := by
  unfold RecursiveCommand; infer_instance

/-- Native axiom shape, the asserted statement of its tactic and successful independent replay
observations. -/
def NativeAxiomShape (a : Declaration) : Prop :=
  a.kind = .«axiom» ∧ a.internal = true ∧ a.isProp = true ∧
  a.isUnsafe = false ∧ a.isPartial = false ∧ a.implementedBy = none ∧ a.extern = false ∧
  a.nativeStatement.isSome = true ∧ a.nativeReplay = some true ∧ a.name ∈ a.axioms ∧
  ∀ n ∈ a.axioms, n = a.name ∨ Permitted .standardLogical n
instance (a : Declaration) : Decidable (NativeAxiomShape a) := by
    unfold NativeAxiomShape; infer_instance

/-- A native-proof axiom `a` is authenticated exactly when three observations hold.

1. Name: `a`'s name is one the pinned `nativeEqTrue` scheme generates for a native tactic
   (`nativeAxiomOrigin?`, characterized by `nativeAxiomOrigin?_isSome_iff`), under a prefix that
   is the name of a declaration `p` of `a`'s module or its module-private form
   (`GeneratedPrefix`, characterized by `generatedPrefix_iff`).
2. Statement and replay: `a` is a safe internal proposition axiom asserting `e = true` with `e` in
   that tactic family's shape (`nativeStatement`), an independent native evaluation of `e`
   returned `true`, and `a` depends on no other axiom outside the standard logical set
   (`NativeAxiomShape`).
3. Provenance: in a fresh re-elaboration of the source, the one command introducing `p` is the one
   command adding an axiom of that origin and statement (`NativeIntroducingCommand`), and no
   `axiom` declaration node occurs in that command's syntax, in a command its information tree
   records or in a macro expansion there, quoted syntax included (`Command.declaresAxiom`).

Soundness. By (2), whatever code added `a`, it asserts only a closed Boolean fact that compiled
evaluation confirms, so trusting it is exactly trusting the compiler: an authenticated axiom is
at worst compiler-trusting, never a hidden logical assumption. By (3), a user's own `axiom`
declaration, written directly or produced by a macro, is never attributed to a native proof: in a
separate command it fails the shared-command condition, and in the same command it is present in
syntax that Lean records whether or not elaborating it succeeds. The check matches no names, so a
macro cannot separate the declared name from it; its only cost is that a command which both
declares an axiom and uses a native tactic has no native axiom authenticated. A custom tactic,
elaborator or metaprogram that adds such an axiom without declaring it relies on (2) alone and is
classified compiler-trusting, which (2) makes accurate. No command, evaluator or proof-term shape
is required beyond (1)-(3), so wrappers (namespaced names, attributes, `set_option … in`, `where`
clauses, parameters, `grind =>` and `sym =>` blocks, module-private names) do not change the
classification. `native_provenance` states what an authenticated role extracts from these
observations; it does not make them truthful. -/
def NativeTeachingOK (ds : Array Declaration) (ts : Array Transcript) (a : Declaration) : Prop :=
  NativeAxiomShape a ∧ a ∈ ds ∧ ∃ p ∈ ds, ∃ o ∈ nativeAxiomOrigin? a.name,
    p.module = a.module ∧ GeneratedPrefix p.module p.name o.1 ∧
    ExactlyOne ((moduleCommands ts p.module).filter (fun c => c.added.contains p.name)) (fun c =>
      NativeIntroducingCommand ts a o.2 o.1 c ∧ c.declaresAxiom = false)
instance (ds : Array Declaration) (ts : Array Transcript) (a : Declaration) :
    Decidable (NativeTeachingOK ds ts a) := by unfold NativeTeachingOK; infer_instance

/-- Range-less generated partial helper whose whole value is the compiler transformation of its
base's stored predefinition up to proofs (`Declaration.unsafeRecValueUpToProofs`), with the
equation checks retained. -/
def RecursiveHelperShape (h : Declaration) : Prop :=
  h.kind = .definition ∧ h.internal = true ∧ h.ranges = none ∧ h.isPartial = true ∧
  h.isUnsafe = false ∧ h.hints = some .opaque ∧ h.implementedBy = none ∧ h.extern = false ∧
  h.unsafeRecValueOrigin.isSome = true ∧ h.unsafeRecValueUpToProofs = some true ∧
  h.unsafeRecEquationExact = some true ∧ h.unsafeRecEquationDefeq = some true
instance (h : Declaration) : Decidable (RecursiveHelperShape h) := by
    unfold RecursiveHelperShape; infer_instance

/-- Safe recursive base, exact type/universes, and bounded helper/equation dependencies. The base
is regular-hinted, or abbreviation-hinted for a recursive `abbrev`. -/
def RecursiveBaseShape (h b : Declaration) : Prop :=
  b.kind = .definition ∧ h.module = b.module ∧ b.isPartial = false ∧ b.isUnsafe = false ∧
  (b.hints = some .regular ∨ b.hints = some .abbrev) ∧ b.recursive = true ∧
  b.implementedBy = none ∧ b.extern = false ∧
  h.type = b.type ∧ h.levelParams = b.levelParams ∧ (∀ n ∈ h.axioms, n ∈ b.axioms) ∧
  ∃ eqAxioms ∈ h.unsafeRecEquationAxioms,
    ∀ n ∈ eqAxioms, Permitted .standardLogical n ∨ n ∈ b.axioms
instance (h b : Declaration) : Decidable (RecursiveBaseShape h b) := by
    unfold RecursiveBaseShape; infer_instance

/-- Mutual-group order is preserved, with exact helper transformation, and the helper calls a
helper of its group: itself, or in a mutual block possibly only another member's helper. -/
def RecursiveGroup (h b : Declaration) : Prop :=
  b.all ≠ #[] ∧ h.all = b.all.map (fun n => Name.str n "_unsafe_rec") ∧
  h.name ∈ b.all.map (fun n => Name.str n "_unsafe_rec") ∧ ∃ n ∈ h.all, n ∈ h.valueConstants
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
