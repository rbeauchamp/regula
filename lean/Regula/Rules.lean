import Regula.Input
import Regula.Reach
import RegulaCore.RuleId
import RegulaCore.Verdict

/-!
# The rules over the closed input

Each kept rule as a pure, total function from the closed input (`Regula.Closed.Input`) to the
subjects that violate it, named after the rule and in the order of the specification of the smaller
Regula (`specification/RegulaSpecification/`): `Foundation.lean` (RG1001 to RG1005), `Execution.lean`
(RG1006, RG3001, RG3002), `Contracts.lean` (RG1007 to RG1009) and `Project.lean` (RG2002, RG2004,
RG2006, RG2007). Each reads only fields of the input. `specification/RegulaSpecification/Proofs/`
proves of each that it reports a subject exactly when the violation predicate of the specification
holds of it.

`Input.check` matches the closed type `RuleId` exhaustively, so a rule that the registry gains stops
this build until it has a function, and each rule that the specification hands to Lean or retires
has none.

The rules read the axiom set of a constant from `Decl.axioms`, which the loader computes with
`Lean.collectAxioms`. An input without the set of a constant that a rule reads is refused before any
rule runs (`Input.refusal?`), so a missing set is never read as an empty one. A search over the
input's graph of constants is `Regula.Closed.reach`, which ends with the exact answer on every input
(`mem_reach`), so a search has no way to fail.

`run` gives the verdict of a bundle (`Gate.lean`'s `gateRecord`): a bundle that the admission
refuses is `incomplete`; a well-formed one passes exactly when no rule reports a subject.
-/

namespace Regula.Closed

open Lean (Name)

/-- The three axioms of Lean's logic that a profile can admit. -/
def logicalAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- The axioms of the toolchain by which Lean's kernel trusts the compiler: none at v4.35.0. -/
def compilerAxioms : List Name := []

/-- Whether `a` has the name form of the axiom a native proof adds:
`<declaration>._native.<tactic>.<suffix>`. -/
def nativeProofAxiom : Name → Bool
  | .str (.str (.str _ "_native") _) _ => true
  | _ => false

/-- One finding: a rule and the subject that violates it, with the module of the subject when it is
a constant or a module, and a detail. -/
structure Finding where
  /-- The rule that the subject violates. -/
  rule : RuleId
  /-- The constant, module or target that violates it. -/
  subject : Name
  /-- The module of the subject, when it is a constant or a module. -/
  module : Option Name
  /-- What the rule found. -/
  detail : String
  deriving Inhabited

/-- The two closed allowlists of RG2006 and RG2007, as Boolean decisions on names. The checker runs
with `Regula.Allowlist`'s members (`Regula.Shell.allowlists`). -/
structure Allowlists where
  /-- The option names a claimed target may set (RG2006). -/
  options : Name → Bool
  /-- The environment extensions a claimed module may have entries of (RG2007). -/
  extensions : Name → Bool

/-- What the rules read of one input, computed once: its indexes and its searches. -/
structure Tables where
  /-- The constants by name. -/
  index : Std.HashMap Name Decl
  /-- The profile and execution mode of each claim of each module (`Input.claimsOf`). -/
  claims : Std.HashMap Name (List (Profile × Execution))
  /-- The constants of claimed modules. -/
  claimed : List Decl
  /-- What `usesOf` gives over the constants, the weight of a search through it (`reach`). -/
  usesWeight : Nat
  /-- What `compiledOf` gives over the constants, the weight of a search through it. -/
  compiledWeight : Nat
  /-- The different constants that compiled code runs in place of each constant. -/
  departs : Std.HashMap Name (List Name)
  /-- What `departsOf` gives over the references of the departures, the weight of a search through
  it. -/
  departsWeight : Nat

namespace Input

variable (i : Input)

/-- The constants of the different departures of the input, by the constant that each replaces. -/
def departsTable : Std.HashMap Name (List Name) :=
  (i.decls.flatMap (·.departures)).foldl (init := {}) fun m x =>
    if x.reference == x.runs then m
    else m.insert x.reference (x.runs :: m.getD x.reference [])

/-- The tables of the input. -/
def tables : Tables :=
  let claims := i.claimTable
  let index := i.index
  let departs := i.departsTable
  let names := i.decls.map (·.name)
  { index, claims
    claimed := i.decls.filter fun d => !(claims.getD d.module []).isEmpty
    usesWeight := (names.map fun n => (index[n]?.elim [] (·.uses)).length).sum
    compiledWeight := (names.map fun n => (index[n]?.elim [] (·.compiled)).length).sum
    departs
    departsWeight :=
      ((i.decls.flatMap (·.departures)).map fun x => (departs.getD x.reference []).length).sum }

end Input

namespace Tables

variable (t : Tables)

/-- The constants a constant mentions. -/
def usesOf (n : Name) : List Name := t.index[n]?.elim [] (·.uses)

/-- The constants the compiled code of a constant runs. -/
def compiledOf (n : Name) : List Name := t.index[n]?.elim [] (·.compiled)

/-- The constants that compiled code runs in place of a constant. -/
def departsOf (n : Name) : List Name := t.departs.getD n []

/-- `Reaches`: the constants that `seeds` reach through the constants each mentions. -/
def mentions (seeds : List Name) : Std.HashSet Name := reach t.usesOf t.usesWeight seeds

/-- `a` is one of the three logical axioms and is the toolchain's own constant of that name. -/
def known (a : Name) : Bool :=
  logicalAxioms.contains a && (t.index[a]?).any (·.inToolchain)

/-- Profile `p` admits axiom `a`. -/
def admits : Profile → Name → Bool
  | .kernelOnly, _ => false
  | .choiceFree, a => t.known a && (a == ``propext || a == ``Quot.sound)
  | .standardLogical, a => t.known a

/-- The profile and execution mode of each claim of module `m`. -/
def claimsFor (m : Name) : List (Profile × Execution) := t.claims.getD m []

/-- Whether the name is a constant of a claimed module. -/
def claimedName (c : Name) : Bool :=
  (t.index[c]?).any fun d => !(t.claimsFor d.module).isEmpty

/-- The base `f` of a name of the form `f._unsafe_rec`. -/
def helperBase? : Name → Option Name
  | .str base "_unsafe_rec" => some base
  | _ => none

/-- `d` has the name of a recursion helper, and its base is a safe, total definition in its module. The
base is a definition: the base of a `partial def` is an opaque constant, so its helper is no
exception. -/
def helperBaseFits (d : Decl) : Bool :=
  match helperBase? d.name with
  | some base => t.index[base]?.any fun b =>
      b.kind == .definition && b.module == d.module && !b.isUnsafe && !b.isPartial &&
        b.implementedBy.isNone && !b.isExtern
  | none => false

/-- `d` is the recursion helper of a safe recursive definition in the same module. -/
def recursionHelper (d : Decl) : Bool :=
  d.isPartial && !d.isUnsafe && d.implementedBy.isNone && !d.isExtern && t.helperBaseFits d

/-- `f` is a safe, total, computable constant of the input. -/
def safeComputable (f : Name) : Bool :=
  (t.index[f]?).any fun d => !d.isUnsafe && !d.isPartial && !d.isNoncomputable

/-- A Boolean test outside the toolchain. -/
def projectTest (c : Name) : Bool :=
  (t.index[c]?).any fun d => d.isBoolTest && !d.inToolchain

/-- Code whose run no theorem can bind to a kernel value. -/
def unbindable (d : Decl) : Bool :=
  d.isExtern || (d.isPartial && !t.recursionHelper d) || d.isInitialized

end Tables

/-- A finding whose subject is the constant `d`. -/
def finding (rule : RuleId) (d : Decl) (detail : String) : Finding :=
  { rule, subject := d.name, module := some d.module, detail }

/-- A finding whose subject is the constant named `c`. -/
def theoremFinding (t : Tables) (rule : RuleId) (c : Name) (detail : String) : Finding :=
  { rule, subject := c, module := (t.index[c]?).map (·.module), detail }

/-- The axiom set of constant `d` (`Input.AxiomOf`), as the loader computed it with
`Lean.collectAxioms`. The admission refuses an input without the set of a constant that a rule
reads (`Input.axiomsMissing?`). -/
def Decl.axiomSet (d : Decl) : List Name := d.axioms.getD []

namespace Tables

variable (t : Tables)

/-- RG1001: a constant of a claimed module is an axiom. -/
def rg1001 : List Finding :=
  t.claimed.filterMap fun d =>
    if d.kind == .axiom then some (finding .projectAxiom d "declares an axiom") else none

/-- RG1002: a constant of a claimed module depends on `sorryAx`. -/
def rg1002 : List Finding :=
  t.claimed.filterMap fun d =>
    if d.axiomSet.contains ``sorryAx then some (finding .proofHole d "depends on sorryAx") else none

/-- RG1003: a constant of a claimed module depends on an axiom that is not known, and that RG1002
and RG1004 do not name. -/
def rg1003 : List Finding :=
  t.claimed.filterMap fun d =>
    let unknown := d.axiomSet.filter fun a => !t.known a && a != ``sorryAx && !nativeProofAxiom a &&
      !compilerAxioms.contains a
    if !unknown.isEmpty then
      some (finding .unknownAxiom d s!"depends on the unknown axioms {unknown}")
    else none

/-- RG1004: a constant of a claimed module depends on a native proof's axiom or on an axiom by which
the kernel trusts the compiler. -/
def rg1004 : List Finding :=
  t.claimed.filterMap fun d =>
    let compiler := d.axiomSet.filter fun a => nativeProofAxiom a || compilerAxioms.contains a
    if !compiler.isEmpty then
      some (finding .compilerTrusting d s!"depends on the native-proof axioms {compiler}")
    else none

/-- RG1005: a constant of a claimed module depends on an axiom that a profile of its module does not
admit. -/
def rg1005 : List Finding :=
  t.claimed.flatMap fun d =>
    (t.claimsFor d.module).filterMap fun (p, _) =>
      let excess := d.axiomSet.filter (!t.admits p ·)
      if !excess.isEmpty then
        some (finding .profileExceeded d s!"depends on {excess}, outside its profile")
      else none

/-- RG1006: a constant of a claimed module is unsafe or partial, and is no recursion helper. -/
def rg1006 : List Finding :=
  t.claimed.filterMap fun d =>
    if (d.isUnsafe || d.isPartial) && !t.recursionHelper d then
      some (finding .escapeHatch d s!"is {if d.isUnsafe then "unsafe" else "partial"}")
    else none

/-- Whether a contract is a decision contract. -/
def isDecision (k : Contract) : Bool := k.kind != .other

/-- RG1007: an executable contract of a claimed module fixes an argument of its implementation,
names an implementation that is not safe and computable, or, as a decision contract, states its
specification through its implementation. -/
def rg1007 (contracts : List Contract) : List Finding :=
  contracts.filterMap fun k =>
    let thm := theoremFinding t .executableContract k.theorem_
    if !t.claimedName k.theorem_ then none
    else if k.fixedArgs != 0 then some (thm s!"fixes {k.fixedArgs} arguments of {k.impl}")
    else if !t.safeComputable k.impl then
      some (thm s!"names {k.impl}, which is not a safe, total, computable constant")
    else if isDecision k && (t.mentions k.spec).contains k.impl then
      some (thm s!"states its specification through its implementation {k.impl}")
    else none

/-- RG1008: a registered decision function of a claimed module has no decision contract in a claimed
module and no `Decidable` result type. -/
def rg1008 (contracts : List Contract) (decisions decidableResults : List Name) : List Finding :=
  decisions.filterMap fun f =>
    if t.claimedName f && !decidableResults.contains f &&
        !contracts.any (fun k => k.impl == f && isDecision k && t.claimedName k.theorem_) then
      some (theoremFinding t .decisionContract f
        "is registered as a decision and has no decision contract in a claimed module")
    else none

/-- RG1009: the specification of a decision contract of a claimed module and its implementation or
acceptance predicate reach one Boolean test outside the toolchain. -/
def rg1009 (contracts : List Contract) : List Finding :=
  contracts.filterMap fun k =>
    if t.claimedName k.theorem_ && isDecision k then
      let implementation := t.mentions (k.impl :: k.accept)
      let shared := (t.mentions k.spec).toList.filter
        fun c => t.projectTest c && implementation.contains c
      if !shared.isEmpty then
        some (theoremFinding t .sharedTest k.theorem_
          s!"its specification and its implementation or acceptance share the tests {shared}")
      else none
    else none

end Tables

namespace Input

variable (i : Input)

/-- Whether this environment loads a module of target `x`: for an executable, its root module, so
that the `main` of the environment is the `main` that Lake links for it. -/
def loadsTarget (x : Target) : Bool := x.modules.any i.loads.contains

/-- The profile and execution mode of each claim of each executable whose root this environment
loads. -/
def rootClaims : List (Profile × Execution) :=
  i.targets.flatMap fun x =>
    if x.kind == .executable && i.loadsTarget x then
      i.manifest.filterMap fun e =>
        if e.target == x.name then
          match e.classification with
          | .claimed p m => some (p, m)
          | .excluded => none
        else none
    else []

/-- RG3001, a missing root: a claimed executable whose root this environment loads has no `main`. -/
def missingRoots (t : Tables) : List Finding :=
  if t.index.contains `main then []
  else i.targets.filterMap fun x =>
    if x.kind == .executable && i.claimedTarget x.name && i.loadsTarget x then
      some { rule := .executionUnresolved, subject := x.name, module := none
             detail := "is a claimed executable whose environment has no `main`" }
    else none

/-- The execution closure of the executable of this environment, when it has a claimed root: the
constants that the compiled code of `main`, and of each constant that it reaches, runs. -/
def closure (t : Tables) : Std.HashSet Name :=
  if !i.rootClaims.isEmpty && t.index.contains `main then
    reach t.compiledOf t.compiledWeight [`main]
  else {}

/-- RG3001: the execution closure of a claimed executable reaches a name that the input does not
resolve or a constant on a cycle of departures, or the executable has no root. -/
def rg3001 (t : Tables) : List Finding :=
  i.missingRoots t ++ (i.closure t).toList.filterMap fun c =>
    match t.index[c]? with
    | none => some {
        rule := .executionUnresolved, subject := c, module := none
        detail := "is run by the compiled code of an executable and is no constant" }
    | some d =>
      if (reach t.departsOf t.departsWeight (t.departsOf c)).contains c then
        some (finding .executionUnresolved d "is on a cycle of departures")
      else none

/-- The departure `x` has a correspondence under profile `p`: a safe theorem, each of whose axioms
`p` admits, states it. -/
def corresponds (t : Tables) (p : Profile) (x : Departure) : Bool :=
  i.proved.any fun q =>
    q.reference == x.reference && q.runs == x.runs &&
      (t.index[q.theorem_]?).any fun d =>
        !d.isUnsafe && !d.isPartial && d.axiomSet.all (t.admits p)

/-- RG3002: under a checked execution claim, the closure reaches code outside the toolchain that no
theorem can bind, or a boundary with no correspondence that the claim's profile admits. -/
def rg3002 (t : Tables) : List Finding :=
  (i.rootClaims.filter (·.2 == .checked)).flatMap fun (p, _) =>
    (i.closure t).toList.filterMap fun c =>
      (t.index[c]?).bind fun d =>
        if !d.inToolchain && t.unbindable d then
          some (finding .executionBoundary d "is code that no theorem can bind")
        else
          match d.departures.filter fun x => !x.inToolchain && !i.corresponds t p x with
          | [] => none
          | x :: _ => some (finding .executionBoundary d
              s!"runs {x.runs} in place of {x.reference} with no admitted correspondence")

/-- The library targets that contain module `m`. -/
def librariesOf (m : Name) : List Target :=
  i.targets.filter fun t => t.kind == .library && t.modules.contains m

/-- A finding whose subject is a target. -/
def project (rule : RuleId) (subject : Name) (detail : String) : Finding :=
  { rule, subject, module := none, detail }

/-- The number of entries of the claim that name target `t`. -/
def entriesFor (t : Name) : Nat := (i.manifest.filter (·.target == t)).length

/-- RG2002: the claim does not classify a target exactly once, names a target Lake does not have,
classifies an executable differently from a library that contains its root, or claims a target that
is not a default target. -/
def manifestFindings : List Finding :=
  (i.targets.filterMap fun t =>
    if i.entriesFor t.name != 1 then
      some (project .configuration t.name s!"the claim classifies it {i.entriesFor t.name} times")
    else none) ++
  (i.manifest.filterMap fun e =>
    if !(i.targets.map (·.name)).contains e.target then
      some (project .configuration e.target "the claim names a target Lake does not have")
    else none) ++
  (i.targets.filterMap fun x =>
    if x.kind == .executable && i.targets.any fun l =>
        l.kind == .library && x.modules.any l.modules.contains &&
          i.manifest.any fun a => a.target == x.name &&
            i.manifest.any fun b => b.target == l.name && a.classification != b.classification then
      some (project .configuration x.name
        "classified differently from a library that contains its root")
    else none) ++
  (i.targets.filterMap fun x =>
    if i.claimedTarget x.name && !x.isDefault then
      some (project .configuration x.name "is claimed but is not a default target")
    else none)

/-- The RG2006 findings of the target `t`, whichever classification it has: an option of automatic
implicits that it does not set to `false`, one that it sets to another value, an option outside
the allowlist `allowed`, and any other way it changes Lean's process. -/
def targetOptionFindings (allowed : Name → Bool) (t : Target) : List Finding :=
  let project (detail : String) : Finding :=
    { rule := .communityConfiguration, subject := t.name, module := none, detail }
  let implicit : List Name := [`autoImplicit, `relaxedAutoImplicit]
  (implicit.filter fun o => !t.options.contains (o, "false")).map
      (fun o => project s!"does not set {o} to false") ++
    (t.options.filter fun o => implicit.contains o.1 && o.2 != "false").map
      (fun o => project s!"sets {o.1} to {o.2}") ++
    (t.options.filter fun o => !allowed o.1).map
      (fun o => project s!"sets {o.1} to {o.2}, outside the allowlist") ++
    if t.extras.isEmpty then [] else [project s!"changes Lean's process with {t.extras}"]

/-- RG2006: the findings of each claimed target, with the option allowlist `allowed`. -/
def optionFindings (allowed : Name → Bool) : List Finding :=
  i.targets.flatMap fun t =>
    if i.claimedTarget t.name then targetOptionFindings allowed t else []

/-- RG2007: a claimed module with entries of an environment extension outside the allowlist
`allowed`. A name that the allowlist does not name is refused, whatever it registers, so an
extension that this revision of Regula has not read is refused too. -/
def extensionFindings (allowed : Name → Bool) : List Finding :=
  i.modules.flatMap fun r =>
    if i.claimedModule r.name then
      (r.extensions.filter (!allowed ·)).map fun x =>
        { rule := .closedSubset, subject := r.name, module := some r.name
          detail := s!"has entries of the environment extension {x}, outside the allowlist" }
    else []

/-- RG2004: each module of the root package that Lake builds is in exactly one library, or in none
and the root of an executable, and no claimed module imports a module of an excluded target. -/
def coverageFindings : List Finding :=
  i.modules.flatMap fun r =>
    let libs := i.librariesOf r.name
    let covered := libs.length == 1 || (libs.isEmpty &&
      i.targets.any fun t => t.kind == .executable && t.modules.contains r.name)
    (if covered then [] else [{
      rule := .coverage, subject := r.name, module := some r.name
      detail := s!"is in {libs.length} libraries" }]) ++
    if i.claimedModule r.name then
      (r.imports.filter i.excludedModule).map fun n =>
        { rule := .coverage, subject := r.name, module := some r.name
          detail := s!"is claimed and imports {n}, a module of an excluded target" }
    else []

/-- RG2002 and RG2006, with the option allowlist `allowed`: they read only Lake's targets and the
claim, so a project with no build has them too (`regula doctor`). -/
def configurationFindings (allowed : Name → Bool) : List Finding :=
  i.manifestFindings ++ i.optionFindings allowed

/-- The findings of one rule, matched exhaustively over the closed type of the rules. The rules that
read no constant and the ones that the specification does not keep have none here: RG2001 is the
admission (`Bundle.refusal?`), RG2003 and RG2005 are Lean's (`lake build --wfail`, `lake check`), and
RG4001 to RG4004 and RG5001 to RG5003 are retired to written guidance. -/
def check (a : Allowlists) (t : Tables) : RuleId → List Finding
  | .projectAxiom => t.rg1001
  | .proofHole => t.rg1002
  | .unknownAxiom => t.rg1003
  | .compilerTrusting => t.rg1004
  | .profileExceeded => t.rg1005
  | .escapeHatch => t.rg1006
  | .executableContract => t.rg1007 i.contracts
  | .decisionContract => t.rg1008 i.contracts i.decisions i.decidableResults
  | .sharedTest => t.rg1009 i.contracts
  | .environment => []
  | .configuration => i.manifestFindings
  | .sourceBuild => []
  | .coverage => i.coverageFindings
  | .admission => []
  | .communityConfiguration => i.optionFindings a.options
  | .closedSubset => i.extensionFindings a.extensions
  | .executionUnresolved => i.rg3001 t
  | .executionBoundary => i.rg3002 t
  | .fenceStructure | .positiveExample | .negativeExample | .trustedExample
  | .moduleDocumentation | .materialDocumentation | .materialIntent => []

/-- Every finding of one environment, with the allowlists `a`. -/
def findings (a : Allowlists) : List Finding :=
  let t := i.tables
  RuleId.all.flatMap (i.check a t)

end Input

/-- The findings of a bundle, each once, by rule, subject and module, in the order found. -/
def dedupe (fs : List Finding) : List Finding :=
  (fs.foldl (init := (({} : Std.HashSet String), ([] : List Finding))) fun (seen, acc) f =>
    let key := s!"{f.rule.spelling}|{f.subject}|{f.module}|{f.detail}"
    if seen.contains key then (seen, acc) else (seen.insert key, f :: acc)).2.reverse

/-- The verdict of a run and its findings, or the reason the run is incomplete. An input that the
admission refuses is incomplete; a well-formed input passes exactly when no rule reports a
subject. -/
def run (a : Allowlists) (b : Bundle) : Verdict × List Finding × Option String :=
  match b.refusal? with
  | some why => (.incomplete, [], some why)
  | none =>
    let fs := dedupe (b.envs.flatMap (·.findings a))
    (if fs.isEmpty then .pass else .fail, fs, none)

end Regula.Closed
