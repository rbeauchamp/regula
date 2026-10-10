module

public import RegulaPolicy.NativeAxiom

/-! # Generated-role relations

Generated-role relations over the complete observation inventory. A native-proof axiom needs
exact metadata, replay and command provenance; a recursion helper needs exact metadata and the
observation that Lean's own recursion compiler regenerates its base from it and that Lean's kernel
checks the base's recursion equation for it. No unsafe constructor-index wrapper is a role: the
pinned compiler generates none, and the exception for one was removed until a port to a compiler
that generates it. These finite decidable relations do not attest that an observation is truthful.
They take the role part of each record (`Declaration.Role`): the inspected part and the three
project-written marks they read, the replacement, the `extern` mark and the recorded ranges, and no
other field. -/

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

/-- A declaration could receive the native-proof exception, as a proposition: it is an axiom and
its name has a native parent. `declarationNeedsTranscript` decides it
(`declarationNeedsTranscript_iff`). -/
def NeedsTranscript (kind : DeclarationKind) (name : Name) : Prop :=
  kind = .«axiom» ∧ ∃ parent, nativeParent? name = some parent

/-- The executed test accepts exactly the declarations that `NeedsTranscript` holds of. -/
theorem declarationNeedsTranscript_iff (kind : DeclarationKind) (name : Name) :
    declarationNeedsTranscript kind name = true ↔ NeedsTranscript kind name := by
  cases kind <;> simp [declarationNeedsTranscript, NeedsTranscript, Option.isSome_iff_exists]

instance (kind : DeclarationKind) (name : Name) : Decidable (NeedsTranscript kind name) :=
  decidable_of_iff _ (declarationNeedsTranscript_iff kind name)

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
def NativeIntroducingCommand (ts : Array Transcript) (a : Declaration.Role) (t : NativeTactic)
    (pfx : Name) (c : Command) : Prop :=
  (moduleCommands ts a.module).filter (fun cmd =>
    cmd.addedDeclarations.any (fun d => nativeAxiomOrigin? d.name == some (pfx, t) &&
      d.kind == .«axiom» && d.nativeStatement == a.nativeStatement)) = #[c]
instance (ts : Array Transcript) (a : Declaration.Role) (t : NativeTactic) (pfx : Name)
    (c : Command) : Decidable (NativeIntroducingCommand ts a t pfx c) := by
        unfold NativeIntroducingCommand; infer_instance

/-- Native axiom shape, the asserted statement of its tactic and successful independent replay
observations. -/
def NativeAxiomShape (a : Declaration.Role) : Prop :=
  a.kind = .«axiom» ∧ a.internal = true ∧ a.isProp = true ∧
  a.isUnsafe = false ∧ a.isPartial = false ∧ a.implementedBy = none ∧ a.extern = false ∧
  a.nativeStatement.isSome = true ∧ a.nativeReplay = some true ∧ a.name ∈ a.axioms ∧
  ∀ n ∈ a.axioms, n = a.name ∨ Permitted .standardLogical n
instance (a : Declaration.Role) : Decidable (NativeAxiomShape a) := by
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
def NativeTeachingOK (ds : Array Declaration.Role) (ts : Array Transcript) (a : Declaration.Role) :
    Prop :=
  NativeAxiomShape a ∧ a ∈ ds ∧ ∃ p ∈ ds, ∃ o ∈ nativeAxiomOrigin? a.name,
    p.module = a.module ∧ GeneratedPrefix p.module p.name o.1 ∧
    ExactlyOne ((moduleCommands ts p.module).filter (fun c => c.added.contains p.name)) (fun c =>
      NativeIntroducingCommand ts a o.2 o.1 c ∧ c.declaresAxiom = false)
instance (ds : Array Declaration.Role) (ts : Array Transcript) (a : Declaration.Role) :
    Decidable (NativeTeachingOK ds ts a) := by unfold NativeTeachingOK; infer_instance

/-- Range-less generated partial helper whose group Lean's own recursion compiler regenerates into
the observed base and its auxiliary definitions, and for which Lean's kernel checks the recursion
equation of each base of the group (`Declaration.unsafeRecRegenerated`, which records both). -/
def RecursiveHelperShape (h : Declaration.Role) : Prop :=
  h.kind = .definition ∧ h.internal = true ∧ h.recordedRanges = none ∧ h.isPartial = true ∧
  h.isUnsafe = false ∧ h.hints = some .opaque ∧ h.implementedBy = none ∧ h.extern = false ∧
  h.unsafeRecRegenerated.isSome = true
instance (h : Declaration.Role) : Decidable (RecursiveHelperShape h) := by
    unfold RecursiveHelperShape; infer_instance

/-- Safe base of the same module, type and universes, whose own axioms are all within
Standard-Logical, so that the decreasing proofs its kernel-checked value carries are real (a base
proved with `sorryAx` or a project axiom does not qualify), and whose axioms bound the helper's. -/
def RecursiveBaseShape (h b : Declaration.Role) : Prop :=
  b.kind = .definition ∧ h.module = b.module ∧ b.isPartial = false ∧ b.isUnsafe = false ∧
  b.implementedBy = none ∧ b.extern = false ∧ h.type = b.type ∧ h.levelParams = b.levelParams ∧
  (∀ n ∈ h.axioms, n ∈ b.axioms) ∧ ∀ n ∈ b.axioms, Permitted .standardLogical n
instance (h b : Declaration.Role) : Decidable (RecursiveBaseShape h b) := by
    unfold RecursiveBaseShape; infer_instance

/-- Mutual-group order is preserved, with Lean's exact `._unsafe_rec` helper transformation. -/
def RecursiveGroup (h b : Declaration.Role) : Prop :=
  b.all ≠ #[] ∧ h.all = b.all.map (fun n => Name.str n "_unsafe_rec") ∧
  h.name ∈ b.all.map (fun n => Name.str n "_unsafe_rec")
instance (h b : Declaration.Role) : Decidable (RecursiveGroup h b) := by
    unfold RecursiveGroup; infer_instance

/-- A recursion helper is admitted exactly when its record, its Lean-linked base's record and their
group meet every component. No transcript, provenance or elaborator record is consulted: the
recorded observation makes the base, up to compilation erasure, what Lean's recursion compiler
produces from the helper's own recursion, and a definition the kernel checked to satisfy the
helper's recursion equation, whoever added it. -/
def RecursiveHelperOK (ds : Array Declaration.Role) (h : Declaration.Role) : Prop :=
  RecursiveHelperShape h ∧ h ∈ ds ∧ ∃ b ∈ ds,
    h.unsafeRecBase = some b.name ∧ RecursiveBaseShape h b ∧ RecursiveGroup h b
instance (ds : Array Declaration.Role) (h : Declaration.Role) :
    Decidable (RecursiveHelperOK ds h) := by
  unfold RecursiveHelperOK; infer_instance

/-- The marks of a native-proof axiom can refuse its role but never grant it: a role that holds
in an inventory holds for the axiom's neutral form in the inventory of neutral forms
(`Declaration.Role.neutral`), where no record has a replacement, an `extern` implementation or
a recorded range. -/
theorem NativeTeachingOK.neutral {ds : Array Declaration.Role} {ts : Array Transcript}
    {a : Declaration.Role} (ok : NativeTeachingOK ds ts a) :
    NativeTeachingOK (ds.map Declaration.Role.neutral) ts a.neutral := by
  obtain ⟨⟨s1, s2, s3, s4, s5, -, -, s8, s9, s10, s11⟩, ha, p, hp, o, ho, hmodule, hprefix,
    hone⟩ := ok
  exact ⟨⟨s1, s2, s3, s4, s5, rfl, rfl, s8, s9, s10, s11⟩, Array.mem_map_of_mem ha, p.neutral,
    Array.mem_map_of_mem hp, o, ho, hmodule, hprefix, hone⟩

/-- The marks of a recursion helper and of its base can refuse the helper's role but never grant
it: a role that holds in an inventory holds for the helper's neutral form in the inventory of
neutral forms (`Declaration.Role.neutral`). -/
theorem RecursiveHelperOK.neutral {ds : Array Declaration.Role} {h : Declaration.Role}
    (ok : RecursiveHelperOK ds h) :
    RecursiveHelperOK (ds.map Declaration.Role.neutral) h.neutral := by
  obtain ⟨⟨s1, s2, -, s4, s5, s6, -, -, s9⟩, hh, b, hb, hbase,
    ⟨b1, b2, b3, b4, -, -, b7, b8, b9, b10⟩, group⟩ := ok
  exact ⟨⟨s1, s2, rfl, s4, s5, s6, rfl, rfl, s9⟩, Array.mem_map_of_mem hh, b.neutral,
    Array.mem_map_of_mem hb, hbase, ⟨b1, b2, b3, b4, rfl, rfl, b7, b8, b9, b10⟩, group⟩

end RegulaPolicy
