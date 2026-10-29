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
RG2006). Each function reads only fields of the input. That each function reports a subject exactly
when the specification's violation predicate holds of it is #487's obligation; this module states
no theorem about it.

A search over the input's graph of constants (`reach`, `axiomsOf`) runs with a step budget of the
size of the input. A search that exhausts it cannot report its answer, so it gives an error, and
the run is `incomplete`, never a pass.

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

/-- The state of the axiom search: the transitive axiom set of each constant whose search
completed, and the depth of each constant on the search's stack. -/
structure AxiomSearch where
  /-- The transitive axiom set of each constant whose search completed. -/
  done : NameMap (List Name) := {}
  /-- The depth of each constant on the stack of the search. -/
  onStack : NameMap Nat := {}

private def addAll (acc axs : List Name) : List Name :=
  axs.foldl (fun l a => if l.contains a then l else a :: l) acc

/-- The axioms of the input that `n` reaches through the constants each mentions, but those that it
reaches only through a constant on the stack, and the least depth of such a constant. A constant's
set is stored once its search reached no constant below it on the stack, so each strongly connected
set of constants is searched to its end from its first constant. The budget `fuel` bounds the
depth, which the number of constants bounds; an exhausted budget is an error. -/
def axiomVisit :
    Nat → Name → Nat → StateT AxiomSearch (Except String) (List Name × Option Nat)
  | 0, _, _ => throw "the axiom search exhausted its budget"
  | fuel + 1, n, depth => do
    let s ← get
    if let some axs := s.done.find? n then return (axs, none)
    if let some d := s.onStack.find? n then return ([], some d)
    let some decl := idx.find? n | return ([], none)
    modify fun s => { s with onStack := s.onStack.insert n depth }
    let mut acc : List Name := if decl.kind == .axiom then [n] else []
    let mut low : Option Nat := none
    for u in decl.uses do
      let (axs, l) ← axiomVisit fuel u (depth + 1)
      acc := addAll acc axs
      low := match low, l with
        | some a, some b => some (min a b)
        | a, b => a <|> b
    modify fun s => { s with onStack := s.onStack.erase n }
    match low with
    | some l =>
      if l < depth then return (acc, some l)
      modify fun s => { s with done := s.done.insert n acc }
      return (acc, none)
    | none =>
      modify fun s => { s with done := s.done.insert n acc }
      return (acc, none)

/-- The transitive axiom set of `c` (`Input.AxiomOf`), continuing the search state. -/
def axiomsWith (c : Name) : StateT AxiomSearch (Except String) (List Name) := do
  return (← axiomVisit idx (idx.size + 1) c 0).1

/-- The transitive axiom set of `c` (`Input.AxiomOf`): each axiom of the input that `c` reaches
through the constants each mentions. -/
def axiomsOf (c : Name) : Except String (List Name) :=
  (axiomsWith idx c).run' {}

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

/-- RG1001 to RG1006 for each constant of a claimed module. -/
def declarationFindingsM : StateT AxiomSearch (Except String) (List Finding) := do
  let mut out := []
  let table := i.claimTable
  for d in i.decls do
    let claims := (table.find? d.module).getD []
    if claims.isEmpty then continue
    if d.kind == .axiom then
      out := out ++ [finding .projectAxiom d "declares an axiom"]
    let axioms ← axiomsWith idx d.name
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

/-- RG1001 to RG1006 for each constant of a claimed module, with one axiom search. -/
def declarationFindings : Except String (List Finding) := (declarationFindingsM i idx).run' {}

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
                let axioms ← axiomsOf idx q.theorem_
                return axioms.all (admits idx p ·)
              unless corresponds do
                out := out ++ [finding .executionBoundary d
                  s!"runs {x.runs} in place of {x.reference} with no admitted correspondence"]
  return out

/-- The library targets that contain module `m`. -/
def librariesOf (m : Name) : List Target :=
  i.targets.filter fun t => t.kind == .library && t.modules.contains m

/-- RG2002 and RG2006, with the option allowlist `allowed`: they read only Lake's targets and the
claim, so a project with no build has them too (`regula doctor`). -/
def configurationFindings (allowed : Name × String → Bool) : List Finding := Id.run do
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
  -- RG2006
  for t in i.targets do
    unless i.claimedTarget t.name do continue
    let unset := [`autoImplicit, `relaxedAutoImplicit].filter fun o =>
      !t.options.contains (o, "false")
    unless unset.isEmpty do
      out := out ++ [project .communityConfiguration t.name s!"does not set {unset} to false"]
    for o in t.options do
      if (o.1 == `autoImplicit || o.1 == `relaxedAutoImplicit) && o.2 != "false" then
        out := out ++ [project .communityConfiguration t.name s!"sets {o.1} to {o.2}"]
      else unless allowed o do
        out := out ++ [project .communityConfiguration t.name
          s!"sets {o.1} to {o.2}, outside the allowlist"]
    unless t.extras.isEmpty do
      out := out ++ [project .communityConfiguration t.name
        s!"changes Lean's process with {t.extras}"]
  return out

/-- RG2004: each module of the root package that Lake builds is in exactly one library, or in none
and the root of an executable, and no claimed module imports a module of an excluded target. -/
def coverageFindings : List Finding := Id.run do
  let mut out := []
  for r in i.modules do
    let libs := librariesOf i r.name
    let covered := libs.length == 1 || (libs.isEmpty &&
      i.targets.any fun t => t.kind == .executable && t.modules.contains r.name)
    unless covered do
      out := out ++ [{
        rule := .coverage, subject := r.name, module := some r.name
        detail := s!"is in {libs.length} libraries" }]
    if i.claimedModule r.name then
      for n in r.imports do
        if i.excludedModule n then
          out := out ++ [{
            rule := .coverage, subject := r.name, module := some r.name
            detail := s!"is claimed and imports {n}, a module of an excluded target" }]
  return out

/-- RG2002, RG2004 and RG2006, with the option allowlist `allowed`. -/
def projectFindings (allowed : Name × String → Bool) : List Finding :=
  i.configurationFindings allowed ++ i.coverageFindings

end Input

/-- Every finding of one environment, with the option allowlist `allowed`. -/
def Input.findings (allowed : Name × String → Bool) (i : Input) :
    Except String (List Finding) := do
  let idx := i.index
  return (← i.declarationFindings idx) ++ (← i.contractFindings idx) ++
    (← i.executionFindings idx) ++ i.projectFindings allowed

/-- The findings of a bundle, each once, by rule, subject and module, in the order found. -/
def dedupe (fs : List Finding) : List Finding :=
  (fs.foldl (init := (({} : Std.HashSet String), ([] : List Finding))) fun (seen, acc) f =>
    let key := s!"{f.rule.spelling}|{f.subject}|{f.module}|{f.detail}"
    if seen.contains key then (seen, acc) else (seen.insert key, f :: acc)).2.reverse

/-- The verdict of a run and its findings, or the reason the run is incomplete. A refused input,
or a search that exhausted its budget, is incomplete; a well-formed input passes exactly when no
rule reports a subject. -/
def run (allowed : Name × String → Bool) (b : Bundle) :
    Verdict × List Finding × Option String :=
  match b.refusal? with
  | some why => (.incomplete, [], some why)
  | none =>
    match b.envs.mapM (Input.findings allowed) with
    | .error why => (.incomplete, [], some why)
    | .ok fs =>
      let fs := dedupe fs.flatten
      (if fs.isEmpty then .pass else .fail, fs, none)

end Regula.Closed
