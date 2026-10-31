import Regula.Rules
import RegulaSpecification.CasesExecution

/-!
# The link from the implementation's input to the specification's

The checker runs over `Regula.Closed.Input`, and the specification states each rule over
`RegulaSpecification.Input`: two types with the same fields, so that the specification is written
independently of the code. `toSpec` carries an input of the checker to the specification's, and each
theorem of this directory is stated about the function that the checker runs on an input `i` and the
predicate of the specification at `toSpec i`.

Two fields differ.

- `Decl.axioms` is the checker's: it holds what `Lean.collectAxioms` gives in the loader, and the
  specification states the axiom set as `Input.AxiomOf`. `AxiomsRead` states that they agree, as a
  hypothesis of each theorem that reads the set. No proof examines `Lean.collectAxioms`, so this is
  an assumption about Lean and it stays one (the specification's trusted base).
- `Input.proved` of the checker holds only correspondences, and `inventory` and `confirmed` are not
  in its input: they are RG6001's, which leaf #485 implements.

`ofSpec` goes the other way, so that a function of the checker is a checker of the specification's
input (`Checker`) and can meet a rule's intent record. It keeps every field that a rule reads. It is
noncomputable, because it fills `Decl.axioms` with the set that `AxiomOf` states, and it is used
only in statements.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Link

/-- The implementation's kind of target in the specification. -/
def kind : Regula.Closed.TargetKind → TargetKind
  | .library => .library
  | .executable => .executable

/-- The specification's kind of target in the implementation. -/
def kind' : TargetKind → Regula.Closed.TargetKind
  | .library => .library
  | .executable => .executable

/-- The implementation's profile in the specification. -/
def profile : Regula.Closed.Profile → Profile
  | .kernelOnly => .kernelOnly
  | .choiceFree => .choiceFree
  | .standardLogical => .standardLogical

/-- The specification's profile in the implementation. -/
def profile' : Profile → Regula.Closed.Profile
  | .kernelOnly => .kernelOnly
  | .choiceFree => .choiceFree
  | .standardLogical => .standardLogical

/-- The implementation's execution mode in the specification. -/
def execution : Regula.Closed.Execution → Execution
  | .report => .report
  | .checked => .checked

/-- The specification's execution mode in the implementation. -/
def execution' : Execution → Regula.Closed.Execution
  | .report => .report
  | .checked => .checked

/-- The implementation's classification in the specification. -/
def classification : Regula.Closed.Classification → Classification
  | .claimed p e => .claimed (profile p) (execution e)
  | .excluded => .excluded

/-- The specification's classification in the implementation. -/
def classification' : Classification → Regula.Closed.Classification
  | .claimed p e => .claimed (profile' p) (execution' e)
  | .excluded => .excluded

/-- The implementation's entry of the claim in the specification. -/
def entry (e : Regula.Closed.Entry) : Entry := ⟨e.target, classification e.classification⟩

/-- The specification's entry of the claim in the implementation. -/
def entry' (e : Entry) : Regula.Closed.Entry := ⟨e.target, classification' e.classification⟩

/-- The implementation's target in the specification. -/
def target (t : Regula.Closed.Target) : Target :=
  ⟨t.name, kind t.kind, t.modules, t.options, t.extras, t.isDefault⟩

/-- The specification's target in the implementation. -/
def target' (t : Target) : Regula.Closed.Target :=
  ⟨t.name, kind' t.kind, t.modules, t.options, t.extras, t.isDefault⟩

/-- The implementation's module record in the specification. -/
def record (r : Regula.Closed.ModuleRecord) : ModuleRecord := ⟨r.name, r.imports, r.extensions⟩

/-- The specification's module record in the implementation. -/
def record' (r : ModuleRecord) : Regula.Closed.ModuleRecord := ⟨r.name, r.imports, r.extensions⟩

/-- The implementation's kind of constant in the specification. -/
def constKind : Regula.Closed.Kind → Kind
  | .axiom => .axiom
  | .definition => .definition
  | .theorem => .theorem
  | .opaque => .opaque
  | .quotient => .quotient
  | .inductive => .inductive
  | .constructor => .constructor
  | .recursor => .recursor

/-- The specification's kind of constant in the implementation. -/
def constKind' : Kind → Regula.Closed.Kind
  | .axiom => .axiom
  | .definition => .definition
  | .theorem => .theorem
  | .opaque => .opaque
  | .quotient => .quotient
  | .inductive => .inductive
  | .constructor => .constructor
  | .recursor => .recursor

/-- The implementation's departure in the specification. -/
def departure (x : Regula.Closed.Departure) : Departure := ⟨x.reference, x.runs, x.inToolchain⟩

/-- The specification's departure in the implementation. -/
def departure' (x : Departure) : Regula.Closed.Departure := ⟨x.reference, x.runs, x.inToolchain⟩

/-- The implementation's constant in the specification. It has no axiom set: `Input.AxiomOf` states
that. -/
def decl (d : Regula.Closed.Decl) : Decl where
  name := d.name
  module := d.module
  kind := constKind d.kind
  isUnsafe := d.isUnsafe
  isPartial := d.isPartial
  uses := d.uses
  implementedBy := d.implementedBy
  compiled := d.compiled
  departures := d.departures.map departure
  isExtern := d.isExtern
  isInitialized := d.isInitialized
  isNoncomputable := d.isNoncomputable
  isBoolTest := d.isBoolTest
  inToolchain := d.inToolchain

/-- The implementation's decision kind in the specification. -/
def contractKind : Regula.Closed.ContractKind → ContractKind
  | .decides => .decides
  | .decidesSoundly => .decidesSoundly
  | .decidesCompletely => .decidesCompletely
  | .other => .other

/-- The specification's decision kind in the implementation. -/
def contractKind' : ContractKind → Regula.Closed.ContractKind
  | .decides => .decides
  | .decidesSoundly => .decidesSoundly
  | .decidesCompletely => .decidesCompletely
  | .other => .other

/-- The implementation's contract in the specification. -/
def contract (k : Regula.Closed.Contract) : Contract :=
  ⟨k.theorem_, k.impl, k.fixedArgs, contractKind k.kind, k.spec, k.accept⟩

/-- The specification's contract in the implementation. -/
def contract' (k : Contract) : Regula.Closed.Contract :=
  ⟨k.theorem_, k.impl, k.fixedArgs, contractKind' k.kind, k.spec, k.accept⟩

/-- The correspondence of the implementation as a statement that a theorem proves. -/
def proof (q : Regula.Closed.Correspondence) : Proof :=
  ⟨.corresponds q.reference q.runs, q.theorem_⟩

/-- The input of the checker as the specification's input. -/
def toSpec (i : Regula.Closed.Input) : Input where
  targets := i.targets.map target
  manifest := i.manifest.map entry
  modules := i.modules.map record
  decls := i.decls.map decl
  loads := i.loads
  contracts := i.contracts.map contract
  decisions := i.decisions
  decidableResults := i.decidableResults
  inventory := none
  proved := i.proved.map proof
  confirmed := []

open Classical in
/-- The axiom set that `AxiomOf` states for `c`, as a list. -/
noncomputable def axiomList (s : Input) (c : Name) : List Name :=
  (s.decls.map (·.name)).filter fun a => decide (s.AxiomOf c a)

/-- The specification's constant in the implementation, with the set that `AxiomOf` states. -/
noncomputable def decl' (s : Input) (d : Decl) : Regula.Closed.Decl where
  name := d.name
  module := d.module
  kind := constKind' d.kind
  isUnsafe := d.isUnsafe
  isPartial := d.isPartial
  uses := d.uses
  axioms := some (axiomList s d.name)
  implementedBy := d.implementedBy
  compiled := d.compiled
  departures := d.departures.map departure'
  isExtern := d.isExtern
  isInitialized := d.isInitialized
  isNoncomputable := d.isNoncomputable
  isBoolTest := d.isBoolTest
  inToolchain := d.inToolchain

/-- The correspondence that a proof states, when it states one. -/
def correspondence' (q : Proof) : Option Regula.Closed.Correspondence :=
  match q.statement with
  | .corresponds reference runs => some ⟨reference, runs, q.theorem_⟩
  | _ => none

/-- The specification's input as the input of the checker: every field that a rule reads. -/
noncomputable def ofSpec (s : Input) : Regula.Closed.Input where
  targets := s.targets.map target'
  manifest := s.manifest.map entry'
  modules := s.modules.map record'
  decls := s.decls.map (decl' s)
  loads := s.loads
  contracts := s.contracts.map contract'
  decisions := s.decisions
  decidableResults := s.decidableResults
  proved := s.proved.filterMap correspondence'

/-- The specification's input, as `ofSpec` keeps it: the correspondences of what its theorems prove,
and no record of the owner's. -/
def restrict (s : Input) : Input :=
  { s with
    proved := (s.proved.filterMap correspondence').map proof
    inventory := none
    confirmed := [] }

theorem target_target' (t : Target) : target (target' t) = t := by
  rcases t with ⟨n, k, m, o, x, d⟩
  cases k <;> rfl

theorem entry_entry' (e : Entry) : entry (entry' e) = e := by
  rcases e with ⟨t, c⟩
  rcases c with ⟨p, x⟩ | _
  · rcases p <;> rcases x <;> rfl
  · rfl

theorem record_record' (r : ModuleRecord) : record (record' r) = r := by
  cases r; rfl

theorem departure_departure' (x : Departure) : departure (departure' x) = x := by
  cases x; rfl

theorem decl_decl' (s : Input) (d : Decl) : decl (decl' s d) = d := by
  rcases d with ⟨_, _, k, _, _, _, _, _, xs, _, _, _, _, _⟩
  have hx : xs.map (departure ∘ departure') = xs := by
    simp [Function.comp_def, departure_departure']
  cases k <;> simp [decl, decl', constKind, constKind', List.map_map, hx]

theorem contract_contract' (k : Contract) : contract (contract' k) = k := by
  rcases k with ⟨_, _, _, k, _, _⟩
  cases k <;> rfl

theorem toSpec_ofSpec (s : Input) : toSpec (ofSpec s) = restrict s := by
  simp only [toSpec, ofSpec, restrict, List.map_map, Function.comp_def, target_target',
    entry_entry', record_record', decl_decl', contract_contract', List.map_id']

/-- The constant of the specification's input and the checker's constant have one name. -/
theorem mem_decls {i : Regula.Closed.Input} {x : Decl} :
    x ∈ (toSpec i).decls ↔ ∃ d ∈ i.decls, decl d = x := by simp [toSpec]

theorem mem_targets {i : Regula.Closed.Input} {x : Target} :
    x ∈ (toSpec i).targets ↔ ∃ t ∈ i.targets, target t = x := by simp [toSpec]

theorem mem_manifest {i : Regula.Closed.Input} {x : Entry} :
    x ∈ (toSpec i).manifest ↔ ∃ e ∈ i.manifest, entry e = x := by simp [toSpec]

theorem mem_modules {i : Regula.Closed.Input} {x : ModuleRecord} :
    x ∈ (toSpec i).modules ↔ ∃ r ∈ i.modules, record r = x := by simp [toSpec]

theorem mem_contracts {i : Regula.Closed.Input} {x : Contract} :
    x ∈ (toSpec i).contracts ↔ ∃ k ∈ i.contracts, contract k = x := by simp [toSpec]

theorem classification_inj {a b : Regula.Closed.Classification}
    (h : classification a = classification b) : a = b := by
  rcases a with ⟨p, e⟩ | _ <;> rcases b with ⟨q, x⟩ | _ <;> simp_all [classification]
  · rcases p <;> rcases q <;> rcases e <;> rcases x <;> simp_all [profile, execution]

theorem target_inj : Function.Injective target := by
  rintro ⟨n, k, m, o, x, d⟩ ⟨n2, k2, m2, o2, x2, d2⟩ h
  cases k <;> cases k2 <;> simp_all [target, kind]

theorem entry_inj : Function.Injective entry := by
  rintro ⟨t, c⟩ ⟨t2, c2⟩ h
  simp only [entry, Entry.mk.injEq] at h
  rw [h.1, classification_inj h.2]

theorem record_inj : Function.Injective record := by
  rintro ⟨n, i, e⟩ ⟨n2, i2, e2⟩ h
  simpa [record] using h

theorem profile_inj {a b : Regula.Closed.Profile} (h : profile a = profile b) : a = b := by
  cases a <;> cases b <;> simp_all [profile]

theorem execution_inj {a b : Regula.Closed.Execution} (h : execution a = execution b) : a = b := by
  cases a <;> cases b <;> simp_all [execution]

theorem toSpec_ofSpec_targets (i : Input) : (toSpec (ofSpec i)).targets = i.targets := by
  simp [toSpec_ofSpec, restrict]

theorem toSpec_ofSpec_manifest (i : Input) : (toSpec (ofSpec i)).manifest = i.manifest := by
  simp [toSpec_ofSpec, restrict]

theorem toSpec_ofSpec_modules (i : Input) : (toSpec (ofSpec i)).modules = i.modules := by
  simp [toSpec_ofSpec, restrict]

/-- What the theorems that read an axiom set assume of the input. Each constant that a rule reads
the set of has one, and each set is the one that `AxiomOf` states: the loader computes it with
`Lean.collectAxioms`, and no proof examines that function. -/
structure AxiomsRead (i : Regula.Closed.Input) : Prop where
  /-- Each constant of a claimed module, and each theorem that states a correspondence, has a
  set. -/
  present : ∀ d ∈ i.decls, ((toSpec i).ClaimedModule d.module ∨ ∃ q ∈ i.proved, q.theorem_ = d.name) →
    d.axioms.isSome = true
  /-- Each set holds exactly the axioms of the constant. -/
  faithful : ∀ d ∈ i.decls, ∀ as, d.axioms = some as → ∀ a, a ∈ as ↔ (toSpec i).AxiomOf d.name a

/-- What the theorems of this directory assume of an input: it has the closed form, and it holds
the axiom sets that `AxiomOf` states. -/
structure Admitted (i : Regula.Closed.Input) : Prop where
  /-- The specification's admission. -/
  wf : (toSpec i).WellFormed
  /-- The axiom sets. -/
  axioms : AxiomsRead i

end Link

end RegulaSpecification
