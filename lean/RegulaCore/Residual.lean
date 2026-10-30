/-! # Review obligations and trusted mechanisms

What a pass of Regula's checker leaves open, stated once for the rule reference and the agent
guide: the semantic-review obligations that no mechanical result discharges (`Residual`), each
with the compliance-checklist rows that carry it, and the mechanisms the checker relies on without
verifying them (`Trusted`). -/

namespace Regula.Review

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
  | .graph => "a claimed serialized graph (standard §7.9) covers every selected root"

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


/-- The mechanisms that a pass of Regula's checker relies on without verifying them. -/
inductive Trusted where
  /-- Lean's elaborator, kernel and compiler of the build's toolchain, which made the `.olean`
  files that the checker reads. -/
  | toolchain
  /-- Lake's load of the workspace: its targets, their modules, options and paths, and the
  manifest's parse. -/
  | acquisition
  /-- Lean's read of the `.olean` files and its import of the environments. -/
  | extraction
  /-- The native runtime and every execution boundary that the rules accept. -/
  | runtime
  deriving Repr, DecidableEq

/-- Every trusted mechanism. -/
def Trusted.all : List Trusted := [.toolchain, .acquisition, .extraction, .runtime]

/-- The machine name of each mechanism. -/
def Trusted.spelling : Trusted → String
  | .toolchain => "toolchain" | .acquisition => "acquisition"
  | .extraction => "extraction" | .runtime => "runtime"

/-- The description of each mechanism, as the rule reference shows it. -/
def Trusted.detail : Trusted → String
  | .toolchain => "Lean's elaborator, kernel and compiler of the build's toolchain, which made \
      the .olean files that the checker reads"
  | .acquisition => "Lake's load of the workspace (its targets, their modules, options and \
      paths) and the parse of foundation_manifest.json"
  | .extraction => "Lean's read of the .olean files and its import of the environments"
  | .runtime => "the native runtime and every execution boundary that the rules accept"

end Regula.Review
