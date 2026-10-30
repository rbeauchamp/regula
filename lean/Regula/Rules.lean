import Std.Data.HashSet
import Regula.Input
import RegulaCore.RuleId
import RegulaCore.Verdict

/-!
# The rules over the closed input

Each kept rule as an executable function from the closed input (`Regula.Closed.Input`) to the
subjects that violate it, in the order of the specification of the smaller Regula
(`specification/RegulaSpecification/`): `Foundation.lean` (RG1001 to RG1005), `Execution.lean`
(RG1006, RG3001, RG3002), `Contracts.lean` (RG1007 to RG1009) and `Project.lean` (RG2002, RG2004,
RG2006, RG2007). Each function reads only fields of the input. `specification/RegulaSpecification/
ClosedSubset.lean` proves that `optionFindings` and `extensionFindings` report a subject exactly
when `Violates2006` and `Violates2007` hold of it. That each other function does the same is #487's
obligation; this module states no theorem about it.

The axiom set of a constant is the one that `Lean.collectAxioms` computed in the loader
(`Decl.axioms`); a rule that needs the axiom set of a constant that has none gives an error, and
the run is `incomplete`. A search over the input's graph of constants (`reach`) runs with a step
budget of the size of the input. A search that exhausts it cannot report its answer, so it gives an
error, and the run is `incomplete`, never a pass.

`run` gives the verdict of a bundle (`Gate.lean`'s `gateRecord`): a bundle that the admission
refuses is `incomplete`; a well-formed one passes exactly when no rule reports a subject.
-/

namespace Regula.Closed

open Lean (Name NameMap NameSet)

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

namespace Input

variable (i : Input) (idx : NameMap Decl)

/-- A step budget for a search over the input: the number of constants and of the names each
constant mentions, runs and departs to. A breadth-first search pops each name it visits once and
each other name at most once for each time a visited name gives it, so it ends within this many
steps plus the number of its seeds. -/
def budget : Nat :=
  i.decls.foldl (fun n d => n + 1 + d.uses.length + d.compiled.length + d.departures.length) 0

/-- Every name reachable from `seeds` through `next`, the seeds included: a breadth-first search
whose step budget is the number of names it can visit. An exhausted budget is an error. -/
def reach (next : Name → List Name) (seeds : List Name) (bound : Nat) :
    Except String NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut work := seeds
  for _ in [0:bound + seeds.length + 1] do
    match work with
    | [] => return .ok seen
    | n :: rest =>
      work := rest
      unless seen.contains n do
        seen := seen.insert n
        work := next n ++ work
  return .error "a search over the constants exhausted its budget"

/-- The constants a constant mentions. -/
def usesOf (n : Name) : List Name := (idx.find? n).elim [] (·.uses)

/-- `a` is one of the three logical axioms and is the toolchain's own constant of that name. -/
def known (a : Name) : Bool :=
  logicalAxioms.contains a && (idx.find? a).any (·.inToolchain)

/-- Profile `p` admits axiom `a`. -/
def admits : Profile → Name → Bool
  | .kernelOnly, _ => false
  | .choiceFree, a => known idx a && (a == ``propext || a == ``Quot.sound)
  | .standardLogical, a => known idx a

/-- The constants of claimed modules. -/
def claimedDecls : List Decl := i.decls.filter (i.claimedModule ·.module)

/-- `d` is the recursion helper of a safe recursive definition in the same module. The base is a
definition: the base of a `partial def` is an opaque constant, so its helper is no exception. -/
def recursionHelper (d : Decl) : Bool :=
  d.isPartial && !d.isUnsafe && d.implementedBy.isNone && !d.isExtern &&
    match d.name with
    | .str base "_unsafe_rec" => match idx.find? base with
      | some b => b.kind == .definition && b.module == d.module && !b.isUnsafe && !b.isPartial &&
          b.implementedBy.isNone && !b.isExtern
      | none => false
    | _ => false

private def finding (rule : RuleId) (d : Decl) (detail : String) : Finding :=
  { rule, subject := d.name, module := some d.module, detail }

/-- The axiom set of constant `d` (`Input.AxiomOf`), as the loader computed it with
`Lean.collectAxioms`; an error when the loader computed none. -/
def axiomsOf (d : Decl) : Except String (List Name) :=
  match d.axioms with
  | some axioms => .ok axioms
  | none => .error s!"the loader computed no axiom set of {d.name}"

/-- RG1001 to RG1006 for each constant of a claimed module. -/
def declarationFindings : Except String (List Finding) := do
  let mut out := []
  let table := i.claimTable
  for d in i.decls do
    let claims := (table.find? d.module).getD []
    if claims.isEmpty then continue
    if d.kind == .axiom then
      out := out ++ [finding .projectAxiom d "declares an axiom"]
    let axioms ← axiomsOf d
    if axioms.contains ``sorryAx then
      out := out ++ [finding .proofHole d "depends on sorryAx"]
    let unknown := axioms.filter fun a => !known idx a && a != ``sorryAx &&
      !nativeProofAxiom a && !compilerAxioms.contains a
    unless unknown.isEmpty do
      out := out ++ [finding .unknownAxiom d s!"depends on the unknown axioms {unknown}"]
    let compiler := axioms.filter fun a => nativeProofAxiom a || compilerAxioms.contains a
    unless compiler.isEmpty do
      out := out ++ [finding .compilerTrusting d s!"depends on the native-proof axioms {compiler}"]
    for (p, _) in claims do
      let excess := axioms.filter (!admits idx p ·)
      unless excess.isEmpty do
        out := out ++ [finding .profileExceeded d s!"depends on {excess}, outside its profile"]
    if (d.isUnsafe || d.isPartial) && !recursionHelper idx d then
      out := out ++ [finding .escapeHatch d
        s!"is {if d.isUnsafe then "unsafe" else "partial"}"]
  return out

/-- `f` is a safe, total, computable constant of the input. -/
def safeComputable (f : Name) : Bool :=
  (idx.find? f).any fun d => !d.isUnsafe && !d.isPartial && !d.isNoncomputable

/-- Whether the name is a constant of a claimed module. -/
def claimedName (c : Name) : Bool := (idx.find? c).any (i.claimedModule ·.module)

/-- RG1007 to RG1009. -/
def contractFindings : Except String (List Finding) := do
  let mut out := []
  let bound := i.budget
  for k in i.contracts do
    unless claimedName i idx k.theorem_ do continue
    let some thm := idx.find? k.theorem_ | continue
    let isDecision := k.kind != .other
    let specReach ← reach (usesOf idx) k.spec bound
    if k.fixedArgs != 0 then
      out := out ++ [finding .executableContract thm s!"fixes {k.fixedArgs} arguments of {k.impl}"]
    else if !safeComputable idx k.impl then
      out := out ++ [finding .executableContract thm
        s!"names {k.impl}, which is not a safe, total, computable constant"]
    else if isDecision && specReach.contains k.impl then
      out := out ++ [finding .executableContract thm
        s!"states its specification through its implementation {k.impl}"]
    if isDecision then
      let implReach ← reach (usesOf idx) (k.impl :: k.accept) bound
      let shared := specReach.toList.filter fun t => implReach.contains t &&
        (idx.find? t).any fun d => d.isBoolTest && !d.inToolchain
      unless shared.isEmpty do
        out := out ++ [finding .sharedTest thm
          s!"its specification and its implementation or acceptance share the tests {shared}"]
  for f in i.decisions do
    unless claimedName i idx f do continue
    if i.decidableResults.contains f then continue
    let decided := i.contracts.any fun k =>
      k.impl == f && k.kind != .other && claimedName i idx k.theorem_
    unless decided do
      if let some d := idx.find? f then
        out := out ++ [finding .decisionContract d
          "is registered as a decision and has no decision contract in a claimed module"]
  return out

/-- Whether `t` is the `main` of an executable target, claimed with `p` and `e`. -/
def executableRoots : List (Decl × Profile × Execution) :=
  i.targets.foldl (init := []) fun acc t =>
    if t.kind != .executable then acc else
    match i.classificationOf t.name, idx.find? `main with
    | some (.claimed p e), some d => if t.modules.contains d.module then acc ++ [(d, p, e)] else acc
    | _, _ => acc

/-- Code whose run no theorem can bind to a kernel value. -/
def unbindable (d : Decl) : Bool :=
  d.isExtern || (d.isPartial && !recursionHelper idx d) || d.isInitialized

/-- RG3001 and RG3002. -/
def executionFindings : Except String (List Finding) := do
  let mut out := []
  let departs : NameMap (List Name) := i.decls.foldl (init := {}) fun m d =>
    d.departures.foldl (init := m) fun m x =>
      if x.reference == x.runs then m
      else m.insert x.reference (x.runs :: (m.find? x.reference).getD [])
  let bound := i.budget
  for (root, p, e) in executableRoots i idx do
    let closure ← reach (fun n => (idx.find? n).elim [] (·.compiled)) [root.name] bound
    for c in closure.toList do
      match idx.find? c with
      | none =>
        out := out ++ [{
          rule := .executionUnresolved, subject := c, module := none
          detail := s!"is run by the compiled code of {root.module}.main and is no constant" }]
      | some d =>
        let onward ← reach (fun n => (departs.find? n).getD []) ((departs.find? c).getD []) bound
        if onward.contains c then
          out := out ++ [finding .executionUnresolved d "is on a cycle of departures"]
        if e == .checked then
          if !d.inToolchain && unbindable idx d then
            out := out ++ [finding .executionBoundary d "is code that no theorem can bind"]
          for x in d.departures do
            unless x.inToolchain do
              let corresponds ← i.proved.anyM fun q => do
                if q.reference != x.reference || q.runs != x.runs then return false
                let some t := idx.find? q.theorem_ | return false
                if t.isUnsafe || t.isPartial then return false
                let axioms ← axiomsOf t
                return axioms.all (admits idx p ·)
              unless corresponds do
                out := out ++ [finding .executionBoundary d
                  s!"runs {x.runs} in place of {x.reference} with no admitted correspondence"]
  return out

/-- The library targets that contain module `m`. -/
def librariesOf (m : Name) : List Target :=
  i.targets.filter fun t => t.kind == .library && t.modules.contains m

/-- RG2002: it reads only Lake's targets and the claim. -/
def manifestFindings : List Finding := Id.run do
  let mut out := []
  let project (rule : RuleId) (subject : Name) (detail : String) : Finding :=
    { rule, subject, module := none, detail }
  -- RG2002
  let names := i.targets.map (·.name)
  for t in i.targets do
    let n := (i.manifest.filter (·.target == t.name)).length
    if n != 1 then
      out := out ++ [project .configuration t.name s!"the claim classifies it {n} times"]
  for e in i.manifest do
    unless names.contains e.target do
      out := out ++ [project .configuration e.target "the claim names a target Lake does not have"]
  for x in i.targets do
    if x.kind == .executable then
      let mine := i.manifest.filter (·.target == x.name)
      for l in i.targets do
        if l.kind == .library && x.modules.any (l.modules.contains ·) then
          let theirs := i.manifest.filter (·.target == l.name)
          if mine.any fun a => theirs.any fun b => a.classification != b.classification then
            out := out ++ [project .configuration x.name
              s!"classified differently from the library {l.name} that contains its root"]
    if i.claimedTarget x.name && !x.isDefault then
      out := out ++ [project .configuration x.name "is claimed but is not a default target"]
  return out

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
    let libs := librariesOf i r.name
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

/-- RG2002, RG2004, RG2006 and RG2007, with the allowlists `a`. -/
def projectFindings (a : Allowlists) : List Finding :=
  i.configurationFindings a.options ++ i.coverageFindings ++ i.extensionFindings a.extensions

end Input

/-- Every finding of one environment, with the allowlists `a`. -/
def Input.findings (a : Allowlists) (i : Input) : Except String (List Finding) := do
  let idx := i.index
  return (← i.declarationFindings idx) ++ (← i.contractFindings idx) ++
    (← i.executionFindings idx) ++ i.projectFindings a

/-- The findings of a bundle, each once, by rule, subject and module, in the order found. -/
def dedupe (fs : List Finding) : List Finding :=
  (fs.foldl (init := (({} : Std.HashSet String), ([] : List Finding))) fun (seen, acc) f =>
    let key := s!"{f.rule.spelling}|{f.subject}|{f.module}|{f.detail}"
    if seen.contains key then (seen, acc) else (seen.insert key, f :: acc)).2.reverse

/-- The verdict of a run and its findings, or the reason the run is incomplete. A refused input,
a search that exhausted its budget, or a constant without the axiom set a rule reads is incomplete;
a well-formed input passes exactly when no rule reports a subject. -/
def run (a : Allowlists) (b : Bundle) : Verdict × List Finding × Option String :=
  match b.refusal? with
  | some why => (.incomplete, [], some why)
  | none =>
    match b.envs.mapM (Input.findings a) with
    | .error why => (.incomplete, [], some why)
    | .ok fs =>
      let fs := dedupe fs.flatten
      (if fs.isEmpty then .pass else .fail, fs, none)

end Regula.Closed
