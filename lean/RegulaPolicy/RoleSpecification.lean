module

public import RegulaPolicy.NativeAxiom

/-! # Generated-role relations

Generated-role relations over the complete observation inventory. A native-proof axiom needs
exact metadata, replay and command provenance; a recursion helper needs exact metadata and the
observation that Lean's own recursion compiler regenerates its base from it. A constructor-index
wrapper has a separate structural observation linked to an owned safe parent and base. These finite
decidable relations do not attest that a compiler observation is truthful. -/

@[expose] public section

namespace RegulaPolicy
open Lean (Name)
open Frontend

/-- Only a declaration that could receive the native-proof exception needs the extra fresh
frontend transcript; the helper exceptions read no transcript. This core works over
primitive fields so a batched harness can apply the identical predicate to raw environment
constant records before paying any environment load. -/
def declarationNeedsTranscript (kind : DeclarationKind) (name : Name) : Bool :=
  kind == .«axiom» && (nativeParent? name).isSome

/-- Only declaration kinds that could receive a generated-role exception need
the extra fresh frontend transcript. -/
def needsFrontendTranscript (decls : Array Declaration) : Bool :=
  decls.any fun decl =>
    declarationNeedsTranscript decl.kind decl.name

/-- Preserve command occurrence order and multiplicity, including duplicate observations. -/
def moduleCommands (ts : Array Transcript) (m : Name) : Array Command :=
  (ts.filter (fun t => t.module == m)).flatMap (·.commands)

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

/-- Range-less generated partial helper whose group Lean's own recursion compiler regenerates into
the observed base and its auxiliary definitions (`Declaration.unsafeRecRegenerated`). -/
def RecursiveHelperShape (h : Declaration) : Prop :=
  h.kind = .definition ∧ h.internal = true ∧ h.ranges = none ∧ h.isPartial = true ∧
  h.isUnsafe = false ∧ h.hints = some .opaque ∧ h.implementedBy = none ∧ h.extern = false ∧
  h.unsafeRecRegenerated.isSome = true
instance (h : Declaration) : Decidable (RecursiveHelperShape h) := by
    unfold RecursiveHelperShape; infer_instance

/-- Safe base of the same module, type and universes, whose own axioms are all within
Standard-Logical, so that the decreasing proofs its kernel-checked value carries are real (a base
proved with `sorryAx` or a project axiom does not qualify), and whose axioms bound the helper's. -/
def RecursiveBaseShape (h b : Declaration) : Prop :=
  b.kind = .definition ∧ h.module = b.module ∧ b.isPartial = false ∧ b.isUnsafe = false ∧
  b.implementedBy = none ∧ b.extern = false ∧ h.type = b.type ∧ h.levelParams = b.levelParams ∧
  (∀ n ∈ h.axioms, n ∈ b.axioms) ∧ ∀ n ∈ b.axioms, Permitted .standardLogical n
instance (h b : Declaration) : Decidable (RecursiveBaseShape h b) := by
    unfold RecursiveBaseShape; infer_instance

/-- Mutual-group order is preserved, with Lean's exact `._unsafe_rec` helper transformation. -/
def RecursiveGroup (h b : Declaration) : Prop :=
  b.all ≠ #[] ∧ h.all = b.all.map (fun n => Name.str n "_unsafe_rec") ∧
  h.name ∈ b.all.map (fun n => Name.str n "_unsafe_rec")
instance (h b : Declaration) : Decidable (RecursiveGroup h b) := by
    unfold RecursiveGroup; infer_instance

/-- A recursion helper is admitted exactly when its record, its Lean-linked base's record and their
group meet every component. No transcript, provenance or elaborator record is consulted: the
regeneration observation makes the base, up to compilation erasure, what Lean's recursion compiler
produces from the helper's own recursion, whoever added it. -/
def RecursiveHelperOK (ds : Array Declaration) (h : Declaration) : Prop :=
  RecursiveHelperShape h ∧ h ∈ ds ∧ ∃ b ∈ ds,
    h.unsafeRecBase = some b.name ∧ RecursiveBaseShape h b ∧ RecursiveGroup h b
instance (ds : Array Declaration) (h : Declaration) : Decidable (RecursiveHelperOK ds h) := by
  unfold RecursiveHelperOK; infer_instance

/-- A constructor-index implementation retains its unsafe status. Its observation names a
safe inductive parent and safe base in the same inventory and module. The base replaces its
runtime implementation with precisely this closed wrapper; neither may add another replacement
or an external implementation. The observed structural comparison is a trusted producer boundary. -/
def ConstructorIndexHelperOK (ds : Array Declaration) (h : Declaration) : Prop :=
  h.kind = .definition ∧ h.internal = true ∧ h.ranges = none ∧
  h.isUnsafe = true ∧ h.isPartial = false ∧ h.hints = some .opaque ∧
  h.implementedBy = none ∧ h.extern = false ∧ h.all = #[h.name] ∧ h ∈ ds ∧
  ∃ t ∈ ds, ∃ b ∈ ds,
    h.constructorIndex = some (t.name, b.name) ∧
    b.name = t.name.str "ctorIdx" ∧ h.name = b.name.str "_impl" ∧
    t.kind = .inductive ∧ t.isUnsafe = false ∧ t.isPartial = false ∧
    t.module = h.module ∧ b.module = h.module ∧ b.kind = .definition ∧
    b.isUnsafe = false ∧ b.isPartial = false ∧ b.implementedBy = some h.name ∧
    b.extern = false ∧ b.all = #[b.name] ∧ b.hints = some .regular ∧
    h.type = b.type ∧ h.levelParams = b.levelParams ∧
    (∀ a ∈ h.axioms, a ∈ b.axioms) ∧ ∀ a ∈ b.axioms, Permitted .standardLogical a

instance (ds : Array Declaration) (h : Declaration) :
    Decidable (ConstructorIndexHelperOK ds h) := by
  unfold ConstructorIndexHelperOK; infer_instance

end RegulaPolicy
