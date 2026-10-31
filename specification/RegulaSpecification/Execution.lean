import RegulaSpecification.Foundation

/-!
# Escape hatches and execution: RG1006, RG3001 and RG3002

RG1006 reads each constant's safety. The one partial constant it admits is the recursion helper
Lean's elaborator adds for a safe recursive definition (`f._unsafe_rec`, observed at v4.34.1 as a
partial definition beside its safe base). That a helper computes what its base does is an
execution question, which RG3002 decides under a checked execution claim.

RG3001 and RG3002 read the execution closure of an executable target: from its `main`, the
constants that the build's compiled code runs (`Decl.compiled`). Compiled code departs from a
kernel value where it runs a constant other than the one the kernel value has there
(`Departure`): a runtime replacement, a `@[csimp]` rewrite at a call site, local or global, a
recursion helper, or any other. Each departure that the toolchain's own library does not make is
a boundary. Under a checked execution claim it needs a correspondence, which counts only when the
theorem that proves it is safe and uses only axioms that the claim's profile admits.
-/

namespace RegulaSpecification

open Lean (Name)

namespace Input

variable (i : Input)

/-- `d` is the recursion helper of a safe base in the same module: a partial, safe-flagged
definition named `f._unsafe_rec` beside a safe, total definition `f` with no `@[implemented_by]`.
The base of a `partial def` is an opaque constant, so its helper is not one. -/
def RecursionHelper (d : Decl) : Prop :=
  d.isPartial = true ∧ d.isUnsafe = false ∧ d.implementedBy = none ∧ d.isExtern = false ∧
    ∃ base ∈ i.decls, d.name = Name.str base.name "_unsafe_rec" ∧ base.kind = .definition ∧
      base.module = d.module ∧ base.isUnsafe = false ∧ base.isPartial = false ∧
      base.implementedBy = none ∧ base.isExtern = false

/-- `c` is in the execution closure of `r`: `r`, or a constant that the compiled code of a
constant of the closure runs. -/
inductive Executes : Name → Name → Prop
  | root (r : Name) : Executes r r
  | step {r c n : Name} (d : Decl) : Executes r c → d ∈ i.decls → d.name = c → n ∈ d.compiled →
      Executes r n

/-- Compiled code runs `n` in place of a different constant `c` at a departure of the input. -/
def Departs (c n : Name) : Prop :=
  ∃ d ∈ i.decls, ∃ x ∈ d.departures, x.reference = c ∧ x.runs = n ∧ c ≠ n

/-- `c` reaches `n` through one or more departures, each to a different constant. -/
inductive DepartsTo : Name → Name → Prop
  | one {c n : Name} : i.Departs c n → DepartsTo c n
  | more {c m n : Name} : i.Departs c m → DepartsTo m n → DepartsTo c n

/-- This environment loads the root module of target `t`, with each module that the root imports.
Lake links an executable from its root and the modules that the root imports, so the `main` of such
an environment is the `main` that Lake links, in whichever of those modules it is declared: one
environment holds one constant of each name. -/
def LoadsRoot (t : Target) : Prop := ∃ m ∈ t.modules, m ∈ i.loads

/-- `r` is the `main` of an executable target claimed with profile `p` and execution mode `e`, read
in an environment that loads its root module (`LoadsRoot`). -/
def ExecutableRoot (r : Name) (p : Profile) (e : Execution) : Prop :=
  ∃ t ∈ i.targets, t.kind = .executable ∧ ⟨t.name, .claimed p e⟩ ∈ i.manifest ∧
    ∃ d ∈ i.decls, d.name = r ∧ r = `main ∧ i.LoadsRoot t

/-- `t` is a claimed executable with no root: this environment loads its root module and holds no
`main`. Each claimed executable thus has exactly one root or fails: one environment holds at most
one `main`, and each environment that loads the root module holds the same one, because Lean refuses
an environment in which two imported modules declare one name. -/
def MissingRoot (t : Name) : Prop :=
  ∃ x ∈ i.targets, x.name = t ∧ x.kind = .executable ∧ (∃ p e, ⟨x.name, .claimed p e⟩ ∈ i.manifest) ∧
    i.LoadsRoot x ∧ ¬ i.Resolves `main

/-- `d` is code whose run no theorem of Lean can bind to a kernel value: foreign code (`@[extern]`),
a partial definition that is not a recursion helper, whose kernel value is opaque, or a value that
an initializer sets when the program starts. -/
def Unbindable (d : Decl) : Prop :=
  d.isExtern = true ∨ (d.isPartial = true ∧ ¬ i.RecursionHelper d) ∨ d.isInitialized = true

/-- `c` is a constant outside the toolchain whose code no correspondence theorem can bind. -/
def UnbindableBoundary (c : Name) : Prop :=
  ∃ d ∈ i.decls, d.name = c ∧ d.inToolchain = false ∧ i.Unbindable d

/-- `x` is a boundary in the compiled code of `c`: a departure there that the toolchain's own
library does not make. -/
def BoundaryAt (c : Name) (x : Departure) : Prop :=
  ∃ d ∈ i.decls, d.name = c ∧ x ∈ d.departures ∧ x.inToolchain = false

/-- The theorem `t` is safe, neither unsafe nor partial, and profile `p` admits each axiom of its
transitive axiom set. -/
def AdmittedProof (p : Profile) (t : Name) : Prop :=
  (∃ d ∈ i.decls, d.name = t ∧ d.isUnsafe = false ∧ d.isPartial = false) ∧
    ∀ a, i.AxiomOf t a → i.Admits p a

/-- The departure `x` has a correspondence under profile `p`: a theorem that `AdmittedProof`
admits proves it. A `@[csimp]` lemma is one such theorem for the departure it makes. -/
def Corresponds (p : Profile) (x : Departure) : Prop :=
  ∃ q ∈ i.proved, q.statement = .corresponds x.reference x.runs ∧ i.AdmittedProof p q.theorem_

end Input

/-- RG1006: a constant of a claimed module is unsafe or partial, and is not a recursion helper. -/
def Violates1006 (i : Input) (c : Name) : Prop :=
  ∃ d ∈ i.decls, d.name = c ∧ i.ClaimedModule d.module ∧ (d.isUnsafe = true ∨ d.isPartial = true) ∧
    ¬ i.RecursionHelper d

/-- RG3001: the execution closure of a claimed executable reaches a name the input does not
resolve, or a constant on a cycle of departures, which runs no definition, or a claimed executable
has no root. -/
def Violates3001 (i : Input) (c : Name) : Prop :=
  (∃ r p e, i.ExecutableRoot r p e ∧ i.Executes r c ∧ (¬ i.Resolves c ∨ i.DepartsTo c c)) ∨
    i.MissingRoot c

/-- RG3002: under a checked execution claim with profile `p`, the closure reaches code that no
theorem can bind (`Unbindable`), or a constant whose compiled code has a boundary with no
correspondence that `p` admits. -/
def Violates3002 (i : Input) (c : Name) : Prop :=
  ∃ r p, i.ExecutableRoot r p .checked ∧ i.Executes r c ∧
    (i.UnbindableBoundary c ∨ ∃ x, i.BoundaryAt c x ∧ ¬ i.Corresponds p x)

/-- The intent record of RG1006. -/
def rg1006 := ruleRecord "RG1006" Violates1006
/-- The intent record of RG3001. -/
def rg3001 := ruleRecord "RG3001" Violates3001
/-- The intent record of RG3002. -/
def rg3002 := ruleRecord "RG3002" Violates3002

end RegulaSpecification
