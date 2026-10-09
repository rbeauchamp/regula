import RegulaCore.Policy
import RegulaPolicy.Acceptance

/-! # Accepted-run report account

The single report account of an accepted run. Every human and machine rendering of a
mechanical success projects this account, and the account is a function of one
`AcceptedRun`: there is no second acceptance evaluator. It separates three things that a
success must not blur:

* the exact formal relation Lean checked (`CompleteFor ∧ AllPolicyOK` for the claim's
  plan, the right side of `acceptanceTheorem`), with each registered `ExecutableContract`'s
  implementation and rendered
  requirement;
* the trusted mechanisms and execution boundaries that relation assumes (`Trusted`, and
  the per-environment execution counts, whose trusted boundaries are reported, not verified);
* the semantic-review obligations it leaves open (`Residual`, each with its one
  `Residual.description`). Emitting an identifier is not a completed review, and this module has
  no way to record one.

`Status.completed` requires an `Account`, and every `Account` is the projection of some
accepted run (`Account.accepted`). So no rendered status reads `completed` without an
accepted run: missing, incomplete or unsupported evidence has none. That the run is the
current request's, rather than another accepted run, is each caller's binding. `Coverage` keeps
local, incremental, file,
documentation and editor feedback distinct from fresh whole-project acceptance
(`AccountContract`). None of this authenticates the IO observations the run consumed. -/

namespace Regula.Checker.Account

open RegulaPolicy

/-- The semantic-review obligations a mechanical result never discharges. Each is stated once,
by `Residual.description`, which the rule reference and `regula explain` show, and carries the
checklist rows `Residual.rows`. -/
inductive Residual where
  /-- `R-INTENT` (`Residual.description`). -/
  | intent
  /-- `R-INVARIANT` (`Residual.description`). -/
  | invariant
  /-- `R-LAWS` (`Residual.description`). -/
  | laws
  /-- `R-BOUNDARY` (`Residual.description`). -/
  | boundary
  /-- `R-NONVACUITY` (`Residual.description`). -/
  | nonvacuity
  /-- `R-DOC` (`Residual.description`). -/
  | doc
  /-- `R-COST` (`Residual.description`). -/
  | cost
  /-- `R-QUALIFY` (`Residual.description`). -/
  | qualify
  /-- `R-GRAPH` (`Residual.description`). -/
  | graph
  deriving Repr, DecidableEq

/-- The identifier of each obligation, such as `R-INTENT`. -/
def Residual.spelling : Residual → String
  | .intent => "R-INTENT" | .invariant => "R-INVARIANT" | .laws => "R-LAWS"
  | .boundary => "R-BOUNDARY" | .nonvacuity => "R-NONVACUITY" | .doc => "R-DOC"
  | .cost => "R-COST" | .qualify => "R-QUALIFY" | .graph => "R-GRAPH"

/-- What each obligation requires a reviewer to establish: the one statement of it. -/
def Residual.description : Residual → String
  | .intent => "each material proposition and its explanation match the written intent in its \
      declaration's Intent section: quantifiers and their order, hypotheses, domains, existence \
      or construction, conditional or open status, and limits. No proof or presence check \
      discharges it, and the requirement owner confirms that the intent states what is needed"
  | .invariant => "the intended invariants (admitted values, transitions, frames, reachability and \
      composition) are stated, and every admission, write and caller path is covered by a \
      proof-bearing interface or theorem"
  | .laws => "the chosen structures and instances carry the intended algebra or order, and custom \
      definitions are justified"
  | .boundary => "the enforced abstraction boundary is the intended one: module modes, exported \
      constructors, recursors and projections, coercions, equations and actual callers"
  | .nonvacuity => "the claim is non-vacuous at the strength claimed (inhabitance, joint \
      satisfiability or reachability); a conditional or deliberately empty claim needs no \
      unrelated witness"
  | .doc => "material-claim registration is complete, and module documentation and docstrings are \
      faithful to the declarations and requirements; presence or length alone is not enough"
  | .cost => "a cost claim names its domain and rests on a mathematical argument or a bounded \
      observation that preserves semantic and effect order; no timing or sample is universal \
      evidence"
  | .qualify => "the checker's detection is qualified for this invocation, toolchain and \
      capability: claim-scoped positive controls, intended-reason mutations and exact invocation \
      evidence"
  | .graph => "a claimed serialized graph (`freshChecker`, standard §7.9) covers every selected \
      root"

/-- The compliance-checklist rows (standard module 8) whose review each obligation carries, in the
checklist's order. Every obligation carries a row, each a checklist row, and every checklist row
carries an obligation (`Regula.Site.residual_rows_listed`, `Regula.Site.residualsOfRow_ne_nil`). -/
def Residual.rows : Residual → List String
  | .intent => ["SCOPE-01", "SCOPE-02", "SCOPE-03", "SCOPE-04", "SCOPE-05", "TYPE-02", "TYPE-03",
      "TYPE-04", "THEOREM-01", "THEOREM-05", "THEOREM-06", "THEOREM-08", "THEOREM-09", "FOUND-01",
      "COMP-01", "COMP-04", "DOC-02", "DOC-04"]
  | .invariant => ["SCOPE-03", "SCOPE-05", "TYPE-01", "THEOREM-01", "THEOREM-03", "THEOREM-07",
      "THEOREM-08", "COMP-03", "BUILD-03"]
  | .laws => ["TYPE-05", "THEOREM-02"]
  | .boundary => ["TYPE-06"]
  | .nonvacuity => ["THEOREM-04", "THEOREM-09"]
  | .doc => ["DOC-01", "DOC-02"]
  | .cost => ["THEOREM-05", "THEOREM-10"]
  | .qualify => ["THEOREM-06", "FOUND-02", "FOUND-03", "FOUND-04", "FOUND-05", "DECL-01", "DECL-02",
      "DECL-03", "DECL-04", "COMP-02", "COMP-03", "BUILD-01", "BUILD-02", "BUILD-03", "BUILD-04",
      "DOC-03", "DOC-04", "DOC-05", "MUT-01", "MUT-02", "MUT-03", "MUT-04"]
  | .graph => ["MUT-05"]

/-- Every obligation once (`Residual.mem_all`). -/
def Residual.all : List Residual :=
  [.intent, .invariant, .laws, .boundary, .nonvacuity, .doc, .cost, .qualify, .graph]

theorem Residual.mem_all (r : Residual) : r ∈ all := by cases r <;> decide

/-- Distinct obligations have distinct machine identifiers. -/
theorem Residual.spelling_injective : Function.Injective Residual.spelling := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- What the accepted run's claim covers. Only a fresh project claim is whole-project
acceptance; incremental, file, documentation, graph and editor results are not. -/
inductive Coverage where
  /-- A fresh audit of the whole project from empty build output. -/
  | freshWholeProject
  /-- A project audit over existing build state. -/
  | incrementalProject
  /-- A fresh audit of a single file. -/
  | freshFile
  /-- An audit of documentation examples. -/
  | documentation
  /-- A recheck of the serialized declaration graph. -/
  | serializedGraph
  /-- The editor's partial snapshot of the current file. -/
  | editorSnapshot
  deriving Repr, DecidableEq

/-- The coverage a claim of each evidence mode has; `coverageOf_fresh_iff` shows only a fresh
project claim has fresh whole-project coverage. -/
def coverageOf : EvidenceMode → Coverage
  | .freshProject => .freshWholeProject
  | .incrementalProject => .incrementalProject
  | .freshFile => .freshFile
  | .documentationExample => .documentation
  | .serializedGraph => .serializedGraph
  | .editorSnapshot => .editorSnapshot

/-- The machine name of each coverage in rendered results. -/
def Coverage.spelling : Coverage → String
  | .freshWholeProject => "freshWholeProject" | .incrementalProject => "incrementalProject"
  | .freshFile => "freshFile" | .documentation => "documentation"
  | .serializedGraph => "serializedGraph" | .editorSnapshot => "editorSnapshot"

/-- Human wording. Only the fresh whole-project text speaks of whole-project acceptance. -/
def Coverage.text : Coverage → String
  | .freshWholeProject => "fresh whole-project acceptance of the claimed Lake surfaces"
  | .incrementalProject =>
      "incremental project acceptance over existing build state, not a fresh-source audit"
  | .freshFile => "fresh single-file acceptance, not project acceptance"
  | .documentation => "documentation-example acceptance"
  | .serializedGraph => "serialized-graph recheck acceptance"
  | .editorSnapshot => "partial editor-snapshot acceptance, not project acceptance"

/-- The rendered text is the fresh whole-project text only for that coverage. -/
theorem Coverage.text_eq_fresh_iff (x : Coverage) :
    x.text = Coverage.freshWholeProject.text ↔ x = .freshWholeProject := by
  cases x <;> decide

/-- A fresh-project claim is always a project-scope claim (`ScopeModeCompatible`). -/
theorem fresh_scope (c : Claim) (h : c.val.mode = .freshProject) : c.val.scope = .project := by
  have compatible := c.property.1
  rw [h] at compatible
  cases hs : c.val.scope <;> simp_all [ScopeModeCompatible]

/-- Mechanisms every accepted run relies on without verifying. -/
inductive Trusted where
  /-- Lean's elaborator, kernel and compiler at the snapshot's toolchain identity. -/
  | toolchain
  /-- Manifest parsing, Lake loading, and acquisition of source, configuration and
  dependencies. -/
  | acquisition
  /-- Environment extraction, compiler and worker processes, and JSON transport. -/
  | extraction
  /-- The native runtime and every execution boundary reported as trusted. -/
  | runtime
  deriving Repr, DecidableEq

/-- Every trusted mechanism, the list each account reports. -/
def Trusted.all : List Trusted := [.toolchain, .acquisition, .extraction, .runtime]

/-- The machine name of each mechanism in the result's `trusted` entries. -/
def Trusted.spelling : Trusted → String
  | .toolchain => "toolchain" | .acquisition => "acquisition"
  | .extraction => "extraction" | .runtime => "runtime"

/-- The human description of each mechanism, as the result and account lines show it. -/
def Trusted.detail : Trusted → String
  | .toolchain => "Lean elaborator, kernel and compiler at the snapshot's toolchain identity"
  | .acquisition =>
      "manifest parsing, Lake loading, and source, configuration and dependency acquisition"
  | .extraction => "environment extraction, compiler and worker processes, and JSON transport"
  | .runtime => "native runtime and every execution boundary reported as trusted"

/-- The theorem whose right side, `CompleteFor ∧ AllPolicyOK`, is the relation an accepted
run establishes; `Account.accepted` proves that relation for the run behind any account. -/
def acceptanceTheorem : Lean.Name := ``RegulaPolicy.accept_iff

/-- One registered `ExecutableContract` of the accepted inventory: the registration, the
implementation it names, the collector's rendering of the requirement Lean checked about
that implementation, and the decision kind the requirement states, if any. Its adequacy and
caller coverage are `ContractAccount.unresolved`. -/
structure ContractAccount where
  /-- The declaration that registers the `ExecutableContract`. -/
  registration : Lean.Name
  /-- The module that declares the registration. -/
  «module» : Lean.Name
  /-- The implementation the contract names. -/
  implementation : Lean.Name
  /-- The collector's rendering of the requirement Lean checked about the implementation. -/
  requirement : String
  /-- The decision kind the collector read from the requirement's head constant: which
  directions Lean checked about the implementation. `none` for a requirement that is not a
  `Regula.DecidesSoundly`, `Regula.DecidesCompletely` or `Regula.Decides`. -/
  kind : Option DecisionKind := none
  /-- The functions that the specification of a decision kind shares with the implementation
  or the acceptance predicate, by class, as the collector recorded them
  (`RegulaPolicy.ExecutableContract.shared`): the kind does not establish that these definitions
  are the intended ones. -/
  shared : RegulaPolicy.SharedNames := {}
  deriving Repr, DecidableEq

/-- RG1007 checks the registration's shape and Lean checks `R f`; whether `R` is the intended
requirement (R-INTENT) and whether callers run it (R-INVARIANT) remain review. A decision kind
changes neither: it states which directions were proved against the written specification, not
that the specification is the intended one or that every checker is registered. -/
def ContractAccount.unresolved : List Residual := [.intent, .invariant]

/-- The account's statement of a contract's decision kind: what the kind establishes about the
implementation and, for a one-way kind, the direction it does not establish
(`DecisionKind.leavesOpen`, `some` for exactly the one-way kinds:
`DecisionKind.leavesOpen_eq_none_iff`). Empty for a contract that states no kind. -/
def ContractAccount.decision (k : ContractAccount) : String :=
  match k.kind with
  | none => ""
  | some kind =>
    s!"; decision kind {kind.spelling}: the implementation {kind.establishes}" ++
      (match kind.leavesOpen with
        | some direction => s!"; not established: it {direction}"
        | none => "")

/-- The account's statement of the functions that a contract's specification shares with the
other side of its kind, which is the implementation with the acceptance predicate: the
definitions by name, those with a result of `Bool` or `BEq` first and marked as such. A kind
compares `accepts (f x)` with `spec x`, so a function that `spec` and `accepts` both use is on
the two sides of that statement as one that `spec` and `f` both use is, and the line says
"the implementation or the acceptance predicate". A proof of the kind that goes through a named
function on the two sides can stay valid when that function changes, so the line says that the
kind does not establish that these definitions are the intended ones. Empty for a contract
whose record names none. A registration whose record names a function with a result of `Bool` or
`BEq` is refused before the account (`RegulaPolicy.sharedTestFailure`), and none is refused for a
function of the other class. -/
def ContractAccount.sharing (k : ContractAccount) : String :=
  if k.shared.isEmpty then "" else
    let names (list : Array Lean.Name) := ", ".intercalate (list.toList.map (s!"{·}"))
    let booleans := if k.shared.booleans.isEmpty then []
      else [s!"{names k.shared.booleans} (each with a result of Bool or BEq)"]
    let others := if k.shared.others.isEmpty then [] else [names k.shared.others]
    s!"; the specification, and the implementation or the acceptance predicate, both use \
      {" and ".intercalate (booleans ++ others)}: the kind does not establish that these \
      definitions are the intended ones"

-- Controls of the account line of the shared functions. The line names the side that shares
-- them as "the implementation or the acceptance predicate", marks the functions with a result
-- of `Bool` or `BEq`, and does not say that the kind establishes them. A contract whose record
-- names no function has no such line.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard
  (⟨`c, `M, `f, "R", some .«sound», ⟨#[`small], #[`evens, `odds]⟩⟩ : ContractAccount).sharing ==
  "; the specification, and the implementation or the acceptance predicate, both use small \
    (each with a result of Bool or BEq) and evens, odds: the kind does not establish that these \
    definitions are the intended ones"
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard (⟨`c, `M, `f, "R", some .«sound», ⟨#[], #[`evens]⟩⟩ : ContractAccount).sharing ==
  "; the specification, and the implementation or the acceptance predicate, both use evens: \
    the kind does not establish that these definitions are the intended ones"
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard (⟨`c, `M, `f, "R", some .«sound», {}⟩ : ContractAccount).sharing == ""

/-- Fence expectations of an accepted documentation claim, by kind. Only positive fences are
conforming evidence; expected rejections and trusted teaching are not interchangeable with it. -/
structure FenceAccount where
  /-- Unmarked fences expected to elaborate and pass: the only conforming evidence. -/
  positive : Nat
  /-- `lean-fail` fences expected to fail elaboration with a matching error. -/
  compilerRejection : Nat
  /-- Fences expected to be rejected by the policy with listed diagnostics. -/
  policyRejection : Nat
  /-- `lean-trusted-compiler` teaching fences. -/
  trustedTeaching : Nat
  deriving Repr, DecidableEq

/-- The fence expects to elaborate and pass: a conforming positive. -/
def isPositive (f : FenceKey) : Bool := f.expectation matches .positive
/-- The fence expects an elaboration error that matches its pattern. -/
def isCompilerRejection (f : FenceKey) : Bool := f.expectation matches .compilerRejection ..
/-- The fence expects rejection by the policy with listed diagnostics. -/
def isPolicyRejection (f : FenceKey) : Bool := f.expectation matches .policyRejection ..
/-- The fence is a trusted-compiler teaching example. -/
def isTrustedTeaching (f : FenceKey) : Bool := f.expectation matches .trustedTeaching

/-- An owned declaration for which Lean's `collectAxioms` omits axioms that it reaches in the
replayed kernel: its name and module, its axioms and the omissions
(`RegulaPolicy.Declaration.tableOmissions`). The audit reports it and does not fail it. -/
structure OmissionAccount where
  /-- The declaration. -/
  declaration : Lean.Name
  /-- Its module. -/
  «module» : Lean.Name
  /-- The axioms it reaches in the replayed kernel. -/
  axioms : Array Lean.Name
  /-- The axioms `collectAxioms` omits, with where each omission comes from. -/
  omissions : Array RegulaPolicy.TableOmission

/-- The report account's data. Construct it only through `account`. -/
structure AccountData where
  /-- The claim's evidence mode. -/
  mode : EvidenceMode
  /-- The claim's scope. -/
  scope : Scope
  /-- The claim's surfaces with their assigned profiles. -/
  surfaces : Array SurfaceAssignment
  /-- The toolchain identity of the claim's snapshot. -/
  toolchain : ToolchainIdentity
  /-- The number of required jobs the run completed. -/
  jobs : Nat
  /-- What the claim covers, from its mode. -/
  coverage : Coverage
  /-- Every `ExecutableContract` registration of the accepted inventory. -/
  contracts : Array ContractAccount
  /-- The execution counts of each accepted environment, in order. -/
  execution : Array ExecutionSummary
  /-- The accepted fences counted by expectation. -/
  fences : FenceAccount
  /-- The mechanisms the run relies on without verifying. -/
  trusted : List Trusted
  /-- The semantic-review obligations left open. -/
  unresolved : List Residual
  /-- Each owned declaration of the accepted inventory for which Lean's `collectAxioms` omits axioms
  it reaches in the replayed kernel. -/
  omissions : Array OmissionAccount

/-- Every `ExecutableContract` registration among the census's declarations, with its module,
implementation, rendered requirement, decision kind and shared functions, environment by
environment. -/
def contractsOf (i : Census) : Array ContractAccount :=
  i.environments.flatMap fun e => e.policy.declarations.filterMap fun d =>
    d.executableContract.map fun k =>
      ⟨d.name, d.module, k.root, k.requirement, k.kind, k.shared⟩

/-- Every declaration among the census's declarations that records an omission of Lean's
`collectAxioms`, with its module, axioms and omissions, environment by environment. -/
def omissionsOf (i : Census) : Array OmissionAccount :=
  i.environments.flatMap fun e => e.policy.declarations.filterMap fun d =>
    if d.tableOmissions.isEmpty then none
    else some ⟨d.name, d.module, d.axioms, d.tableOmissions⟩

/-- Required meaning of the account, for every claim and accepted run. Mode, scope,
surfaces, toolchain and job count are the accepted report's own. Coverage is `coverageOf` the
claim's mode (`coverage_fresh_iff`: fresh whole-project exactly for a fresh project claim). The
contracts are exactly the inventory's
registrations, each with the decision kind and the shared functions the collector recorded.
Execution counts are
`executionSummary` of each accepted environment, in order. The fence counts partition the
accepted fences by expectation. Every residual obligation stays unresolved, R-GRAPH exactly
when a serialized graph is claimed. The omissions are exactly the inventory's declarations that
record one, each with its module, axioms and omissions. -/
def AccountContract (project : {c : Claim} → AcceptedRun c → AccountData) : Prop :=
  ∀ (c : Claim) (run : AcceptedRun c),
    (project run).mode = c.val.mode ∧ (project run).scope = c.val.scope ∧
    (project run).surfaces = c.val.surfaces ∧
    (project run).toolchain = c.val.snapshot.toolchain ∧
    (project run).jobs = run.report.jobs.size ∧
    (project run).coverage = coverageOf c.val.mode ∧
    (∀ x, x ∈ (project run).contracts ↔
      ∃ e ∈ run.report.census.environments, ∃ d ∈ e.policy.declarations,
        ∃ k, d.executableContract = some k ∧
          x = ⟨d.name, d.module, k.root, k.requirement, k.kind, k.shared⟩) ∧
    (project run).execution = run.report.census.environments.map (executionSummary ·.execution) ∧
    ((project run).fences.positive = (run.report.census.fences.filter isPositive).size ∧
      (project run).fences.compilerRejection =
        (run.report.census.fences.filter isCompilerRejection).size ∧
      (project run).fences.policyRejection =
        (run.report.census.fences.filter isPolicyRejection).size ∧
      (project run).fences.trustedTeaching =
        (run.report.census.fences.filter isTrustedTeaching).size ∧
      (project run).fences.positive + (project run).fences.compilerRejection +
        (project run).fences.policyRejection + (project run).fences.trustedTeaching =
        run.report.census.fences.size) ∧
    (project run).trusted = Trusted.all ∧
    (∀ r, r ∈ (project run).unresolved ↔ (r = .graph → c.val.mode = .serializedGraph)) ∧
    (∀ x, x ∈ (project run).omissions ↔
      ∃ e ∈ run.report.census.environments, ∃ d ∈ e.policy.declarations,
        d.tableOmissions ≠ #[] ∧ x = ⟨d.name, d.module, d.axioms, d.tableOmissions⟩)

private def accountImpl {c : Claim} (run : AcceptedRun c) : AccountData :=
  let report := run.report
  let fences := report.census.fences
  { mode := report.claim.val.mode, scope := report.claim.val.scope
    surfaces := report.claim.val.surfaces, toolchain := report.claim.val.snapshot.toolchain
    jobs := report.jobs.size, coverage := coverageOf report.claim.val.mode
    contracts := contractsOf report.census
    execution := report.census.environments.map (checked_summary.run ·.execution)
    fences := ⟨fences.countP isPositive, fences.countP isCompilerRejection,
      fences.countP isPolicyRejection, fences.countP isTrustedTeaching⟩
    trusted := Trusted.all
    unresolved := Residual.all.filter fun r => r != .graph || report.claim.val.mode ==
                                                .serializedGraph
    omissions := omissionsOf report.census }

private theorem fence_partition (fences : Array FenceKey) :
    fences.countP isPositive + fences.countP isCompilerRejection +
      fences.countP isPolicyRejection + fences.countP isTrustedTeaching = fences.size := by
  rcases fences with ⟨fences⟩
  induction fences with
  | nil => simp
  | cons f fs ih =>
    simp only [List.countP_toArray, List.size_toArray, List.countP_cons, List.length_cons] at *
    rcases f with ⟨_, _, _, _, expectation, _, _, _⟩
    cases expectation <;> simp [isPositive, isCompilerRejection, isPolicyRejection,
      isTrustedTeaching] <;> omega

theorem coverageOf_fresh_iff (m : EvidenceMode) :
    coverageOf m = .freshWholeProject ↔ m = .freshProject := by
  cases m <;> decide

/-- Registers `AccountContract` about the executed projection. -/
theorem checked_account : Regula.ExecutableContract @accountImpl AccountContract := by
  refine ⟨fun c run => ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_, rfl, ?_, ?_⟩
  · intro x
    simp only [accountImpl, contractsOf, Array.mem_flatMap, Array.mem_filterMap,
      Option.map_eq_some_iff]
    constructor
    · rintro ⟨e, he, d, hd, k, hk, rfl⟩
      exact ⟨e, he, d, hd, k, hk, rfl⟩
    · rintro ⟨e, he, d, hd, k, hk, rfl⟩
      exact ⟨e, he, d, hd, k, hk, rfl⟩
  · exact ⟨Array.countP_eq_size_filter .., Array.countP_eq_size_filter ..,
      Array.countP_eq_size_filter .., Array.countP_eq_size_filter .., fence_partition _⟩
  · intro r
    simp only [accountImpl, List.mem_filter, Residual.mem_all, true_and, Bool.or_eq_true,
      bne_iff_ne, ne_eq, beq_iff_eq]
    cases r <;> simp [AcceptedRun.report, Finalized.report, Accepted.report]
  · intro x
    simp only [accountImpl, omissionsOf, Array.mem_flatMap, Array.mem_filterMap]
    constructor
    · rintro ⟨e, he, d, hd, hx⟩
      by_cases hempty : d.tableOmissions.isEmpty = true
      · simp [hempty] at hx
      · simp only [hempty, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hx
        exact ⟨e, he, d, hd, fun h => hempty (by simp [h]), hx.symm⟩
    · rintro ⟨e, he, d, hd, hne, rfl⟩
      refine ⟨e, he, d, hd, ?_⟩
      have : d.tableOmissions.isEmpty = false := by
        simpa [Array.isEmpty_iff] using hne
      simp [this]

/-- An executed account reads fresh whole-project coverage exactly for a fresh project claim. -/
theorem coverage_fresh_iff {c : Claim} (run : AcceptedRun c) :
    (checked_account.run run).coverage = .freshWholeProject ↔
      c.val.mode = .freshProject ∧ c.val.scope = .project := by
  change (accountImpl run).coverage = .freshWholeProject ↔ _
  rw [(checked_account.evidence c run).2.2.2.2.2.1, coverageOf_fresh_iff]
  exact ⟨fun h => ⟨h, fresh_scope c h⟩, And.left⟩

/-- An account is the projection of some accepted run, never independently assembled data. -/
def _root_.Regula.Checker.Account : Type :=
  { a : AccountData // ∃ c, ∃ run : AcceptedRun c, checked_account.run run = a }

/-- The account of an accepted run, through `checked_account`. -/
def account {c : Claim} (run : AcceptedRun c) : Account :=
  ⟨checked_account.run run, c, run, rfl⟩

/-- Every account is the projection of a run that is complete for its plan and meets every
stage policy: the right side of `acceptanceTheorem`, for the run this account's data came from. -/
theorem accepted (a : Account) :
    ∃ c, ∃ run : AcceptedRun c, checked_account.run run = a.val ∧
      CompleteFor run.plan run.result.table ∧ AllPolicyOK run.plan run.roles run.result.table := by
  obtain ⟨c, run, h⟩ := a.property
  exact ⟨c, run, h, run.result.accepted.complete, run.result.accepted.policy⟩

/-- Rendered result status. `completed` requires an accepted account; the refusals carry none. -/
inductive Status where
  /-- The run was accepted; `account` is its report account. -/
  | completed (account : Account)
  /-- The run completed and found a violation. -/
  | rejected
  /-- Evidence is missing or incomplete, so no verdict was reached. -/
  | incomplete
  /-- The run found no violation, but its result classifies rather than conforms: for example
  expected-rejection or teaching fences, or a file audit without a conforming claim. -/
  | classified

/-- The status text of the result protocol; `completed` only for an accepted account
(`Status.spelling_eq_completed_iff`). -/
def Status.spelling : Status → String
  | .completed _ => "completed" | .rejected => "rejected"
  | .incomplete => "incomplete" | .classified => "classified"

/-- The status reads `completed` exactly for an accepted account. -/
theorem Status.spelling_eq_completed_iff (s : Status) :
    s.spelling = "completed" ↔ ∃ a, s = .completed a := by
  cases s <;> simp [spelling]

/-- A `completed` status therefore always has an accepted run behind it. -/
theorem Status.completed_accepted (s : Status) (h : s.spelling = "completed") :
    ∃ a, s = .completed a ∧ ∃ c, ∃ run : AcceptedRun c, checked_account.run run = a.val ∧
      CompleteFor run.plan run.result.table ∧ AllPolicyOK run.plan run.roles run.result.table := by
  obtain ⟨a, rfl⟩ := (spelling_eq_completed_iff s).mp h
  exact ⟨a, rfl, a.accepted⟩

private def residualList (rs : List Residual) : String := ", ".intercalate (rs.map (·.spelling))

/-- An accepted account's coverage. -/
def pass (label : String) (a : Account) : String :=
  s!"{label}: PASS — \
    {a.val.coverage.text}"

/-- Human account lines: the checked relation, each contract with its decision kind
(`ContractAccount.decision`), its shared functions (`ContractAccount.sharing`) and its open
review, the execution counts, fence kinds, the count of declarations whose axiom tables omit
axioms (the `--verbose` line of each lists its omissions), trusted mechanisms, and the unresolved review identifiers. -/
def lines (a : Account) : Array String :=
  let d := a.val
  let checked :=
      s!"checked: {acceptanceTheorem} — each of the {d.jobs} required jobs has exactly one " ++
    "completed observation meeting its stage policy (CompleteFor ∧ AllPolicyOK)"
  let contracts := d.contracts.map fun k =>
    s!"{RuleId.executableContract.spelling} contract {k.registration}: Lean checked the \
      requirement about implementation " ++
      s!"{k.implementation}: {k.requirement}{k.decision}{k.sharing}; unresolved review: " ++
      s!"{residualList ContractAccount.unresolved} (adequacy of the requirement, caller coverage)"
  let execution := d.execution.mapIdx fun i s =>
    s!"execution environment {i}: {s.roots} root(s), {s.boundaries} boundary observation(s) " ++
      s!"({s.checked} checked, {s.trusted} trusted and reported, not verified), {s.unresolved} \
        unresolved"
  let f := d.fences
  let fences := if f.positive + f.compilerRejection + f.policyRejection + f.trustedTeaching =
      0 then #[]
    else
        #[s!"fences: {f.positive} conforming positive; {f.compilerRejection} compiler-rejection " ++
      s!"and {f.policyRejection} policy-rejection expectations; {f.trustedTeaching} trusted \
        teaching. " ++
      "Only positive fences are conforming evidence."]
  let trusted :=
      s!"trusted, not verified: Lean {d.toolchain.leanVersion} ({d.toolchain.compilerCommit}); " ++
    "; ".intercalate (d.trusted.map (·.detail))
  let unresolved :=
      s!"unresolved semantic review, where applicable: {residualList d.unresolved}. " ++
    "These identifiers name open obligations, not completed reviews."
  let passed := (d.omissions.filter fun o => o.omissions.any (·.via.isSome)).size
  let omissions := if d.omissions.isEmpty then #[] else
    #[s!"axiom tables: {d.omissions.size} declaration(s) for which Lean's collectAxioms omits \
      axioms they reach in the replayed kernel, {passed} with an omission passed on from a \
      constant they use; reported, not failed (listed with --verbose and in --json-out)"]
  #[checked] ++ contracts ++ execution ++ fences ++ omissions ++ #[trusted, unresolved]


end Regula.Checker.Account
