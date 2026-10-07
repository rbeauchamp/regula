module

public import Regula.Diagnostic
public import RegulaPolicy.Decision
public import Std.Data.HashMap.Basic
import Std.Data.HashMap.Lemmas

/-! # Diagnostic finding adapters

Import-safe adapters to the canonical diagnostic schema. Policy decisions
remain in the policy core; these functions preserve identity and mode, and attribute a declaration
Lean generated to the declaration it generated it from (`sourceName?`), locating it there when it
has no range of its own (`findingLocation`). -/

public section

namespace Regula.Findings
open Lean

/-- New diagnostic identity is recovered from the original structural Name only. -/
def declarationName (decl : RegulaPolicy.Declaration) : Except String Name := do
  unless decl.name != .anonymous do throw "anonymous declaration identity"
  return decl.name

/-- The detail of a declaration finding where no classification line of the declaration is
printed, as in the editor and in the self-audit: the applicability of rule `id` and, for the
shared-test rule, the names of the shared functions with a result of `Bool` or `BEq` that the
record of the declaration's contract holds (`RegulaPolicy.SharedNames.booleansText`), as the
classification line of a project finding prints them. -/
def ruleDetail (id : RuleId) (decl : RegulaPolicy.Declaration) : String :=
  (descriptor id).applicability ++
    match id, decl.executableContract with
    | .sharedTest, some contract => " " ++ contract.shared.booleansText
    | _, _ => ""

/-- The violation finding of a declaration-scoped rule `id` for declaration `name`, with its
detail, location, mode and claim, the declaration it is attributed to, if any
(`sourceName?`), and related locations. A rule outside the declaration domain, or a mode
the rule does not support, is refused. -/
def declarationFinding (id : RuleId) (name : Name) (detail : String)
    (location : Location) (mode : EvidenceMode) (claim : Option String)
    (sourceDeclaration : Option Name := none) (related : Array RelatedLocation := #[]) :
    Except String Finding :=
  let a : DeclarationArguments := { declaration := name, sourceDeclaration, detail }
  match id with
  | .projectAxiom => (fun d => ⟨.projectAxiom, d⟩) <$> makeDiagnostic .projectAxiom a location mode
                      claim .violation (related := related)
  | .proofHole => (fun d => ⟨.proofHole, d⟩) <$> makeDiagnostic .proofHole a location mode claim
                   .violation (related := related)
  | .unknownAxiom => (fun d => ⟨.unknownAxiom, d⟩) <$> makeDiagnostic .unknownAxiom a location mode
                      claim .violation (related := related)
  | .compilerTrusting => (fun d => ⟨.compilerTrusting, d⟩) <$> makeDiagnostic .compilerTrusting a
                          location mode claim .violation (related := related)
  | .profileExceeded =>
      (fun d => ⟨.profileExceeded, d⟩) <$> makeDiagnostic .profileExceeded a location mode claim
          .violation (related := related)
  | .escapeHatch => (fun d => ⟨.escapeHatch, d⟩) <$> makeDiagnostic .escapeHatch a location mode
                     claim .violation (related := related)
  | .executableContract =>
      (fun d => ⟨.executableContract, d⟩) <$> makeDiagnostic .executableContract a location mode
          claim .violation (related := related)
  | .decisionContract =>
      (fun d => ⟨.decisionContract, d⟩) <$> makeDiagnostic .decisionContract a location mode
          claim .violation (related := related)
  | .sharedTest =>
      (fun d => ⟨.sharedTest, d⟩) <$> makeDiagnostic .sharedTest a location mode claim .violation
          (related := related)
  | .materialDocumentation =>
      (fun d => ⟨.materialDocumentation, d⟩) <$> makeDiagnostic .materialDocumentation a location
          mode claim .violation (related := related)
  | .materialIntent => (fun d => ⟨.materialIntent, d⟩) <$> makeDiagnostic .materialIntent a location
                        mode claim .violation (related := related)
  | _ => .error s!"rule {id} is not a declaration policy diagnostic"

/-- Known context conditions keep their ID; unknown conditions remain incomplete. -/
def contextFinding (id : RuleId) (subject detail : String) (mode : EvidenceMode)
    (impact : Impact) : Except String Finding :=
  let a : ContextArguments := ⟨subject, detail⟩
  let location := Location.project subject
  match id with
  | .environment => (fun d => ⟨.environment, d⟩) <$> makeDiagnostic .environment a location mode
                     none impact
  | .configuration => (fun d => ⟨.configuration, d⟩) <$> makeDiagnostic .configuration a location
                       mode none impact
  | .sourceBuild => (fun d => ⟨.sourceBuild, d⟩) <$> makeDiagnostic .sourceBuild a location mode
                     none impact
  | .coverage => (fun d => ⟨.coverage, d⟩) <$> makeDiagnostic .coverage a location mode none impact
  | .admission => (fun d => ⟨.admission, d⟩) <$> makeDiagnostic .admission a location mode
                   none impact
  | .fenceStructure => (fun d => ⟨.fenceStructure, d⟩) <$> makeDiagnostic .fenceStructure a location
                        mode none impact
  | .positiveExample =>
      (fun d => ⟨.positiveExample, d⟩) <$> makeDiagnostic .positiveExample a location mode
          none impact
  | .negativeExample =>
      (fun d => ⟨.negativeExample, d⟩) <$> makeDiagnostic .negativeExample a location mode
          none impact
  | .trustedExample => (fun d => ⟨.trustedExample, d⟩) <$> makeDiagnostic .trustedExample a location
                        mode none impact
  | _ => .error s!"rule {id} requires another argument domain"

/-- A missing range has honest module attribution. A bad supplied range is an error. -/
def declarationLocation (decl : RegulaPolicy.Declaration) (snapshot : Option SourceSnapshot) :
    Except String Location := do
  match decl.ranges, snapshot with
  | some ranges, some source => return .source (← sourceFromReport source ranges)
  | _, _ => return .module decl.module

/-- The declarations of `ds` by name; the first of a name wins (`declarationIndex_get`). -/
def declarationIndex (ds : Array RegulaPolicy.Declaration) :
    Std.HashMap Name RegulaPolicy.Declaration :=
  ds.foldr (fun p index => index.insert p.name p) {}

/-- Looking a name up in `declarationIndex ds` is finding the first declaration of `ds` with that
name. -/
theorem declarationIndex_get (ds : Array RegulaPolicy.Declaration) (n : Name) :
    (declarationIndex ds)[n]? = ds.find? fun p => p.name == n := by
  unfold declarationIndex
  rw [← Array.foldr_toList, ← Array.find?_toList]
  generalize ds.toList = l
  induction l with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldr_cons, List.find?_cons]
    rw [← ih]
    cases hn : (p.name == n) <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Std.HashMap.getElem?_insert, hn]

/-- One step of the generation relation for the declaration `d`: the declaration Lean generated it
from as the collector read it from the environment (`Declaration.generatedFrom`); otherwise, when
`d` is one of the admitted recursion helpers `helpers` (callers pass the admitted scope's,
`RegulaPolicy.authorizedUnsafeRecHelpers`), the definition `f` its `f._unsafe_rec` compiles
(`Declaration.unsafeRecBase`, which `helperStep_base` ties to Lean's observed regeneration of the
helper). -/
def stepOf (helpers : Array Name) (d : RegulaPolicy.Declaration) : Option Name :=
  d.generatedFrom.or (if helpers.contains d.name then d.unsafeRecBase else none)

/-- `stepOf` relates `d` to `b` exactly when the collector recorded that Lean generated `d` from
`b`, or recorded no such declaration and `d` is an admitted recursion helper whose base is `b`. -/
theorem stepOf_eq_some_iff (helpers : Array Name) (d : RegulaPolicy.Declaration) (b : Name) :
    stepOf helpers d = some b ↔ d.generatedFrom = some b ∨
      (d.generatedFrom = none ∧ d.name ∈ helpers ∧ d.unsafeRecBase = some b) := by
  unfold stepOf
  cases d.generatedFrom with
  | some g => simp
  | none => by_cases hmem : d.name ∈ helpers <;> simp [hmem]

/-- The recursion-helper step leads from an admitted helper `d` of an inventory `ds` with distinct
names to a definition of `ds` in `d`'s module with `d`'s type, and Lean's own recursion compiler
was observed to regenerate `d` (`RegulaPolicy.authorizedUnsafeRecHelpers_base`); that observation,
not the name `f._unsafe_rec`, is what makes `f` the declaration Lean generated `d` from. -/
theorem helperStep_base {ds : Array RegulaPolicy.Declaration}
    (unique : RegulaPolicy.UniqueNames (ds.map (·.name))) {d : RegulaPolicy.Declaration}
    (hd : d ∈ ds) (hn : d.name ∈ RegulaPolicy.authorizedUnsafeRecHelpers ds) {b : Name}
    (hb : d.unsafeRecBase = some b) :
    d.unsafeRecRegenerated.isSome = true ∧ ∃ base ∈ ds, base.name = b ∧
      base.kind = .definition ∧ base.module = d.module ∧ base.type = d.type := by
  obtain ⟨h, hh, hname, hregen, base, hbase, hub, hkind, hmod, htype, -⟩ :=
    RegulaPolicy.authorizedUnsafeRecHelpers_base ds d.name hn
  obtain rfl := RegulaPolicy.eq_of_name_eq unique hh hd hname
  refine ⟨hregen, base, hbase, ?_, hkind, hmod, htype⟩
  rw [hb] at hub
  exact (Option.some.inj hub).symm

/-- One step of the generation relation a report records: `stepOf` for the declaration named `n`,
when `index` holds one. -/
def generatedStep (index : Std.HashMap Name RegulaPolicy.Declaration) (helpers : Array Name)
    (n : Name) : Option Name :=
  (index[n]?).bind (stepOf helpers)

/-- The name `k` steps of `step` lead to from `n`, when each of them exists. -/
def walk (step : Name → Option Name) : Nat → Name → Option Name
  | 0, n => some n
  | k + 1, n => (step n).bind (walk step k)

/-- The first name on the way `step` leads from `n` that it relates to no other, within `fuel`
steps (`chainEnd_eq_some_iff`); `none` when there is no such name that near. -/
def chainEnd (step : Name → Option Name) : Nat → Name → Option Name
  | 0, _ => none
  | fuel + 1, n => match step n with
    | none => some n
    | some m => chainEnd step fuel m

/-- `chainEnd step fuel n` is `r` exactly when fewer than `fuel` steps lead from `n` to `r` and
`step` relates `r` to no other name. -/
theorem chainEnd_eq_some_iff (step : Name → Option Name) (fuel : Nat) (n r : Name) :
    chainEnd step fuel n = some r ↔ ∃ k < fuel, walk step k n = some r ∧ step r = none := by
  induction fuel generalizing n with
  | zero => simp [chainEnd]
  | succ fuel ih =>
    unfold chainEnd
    cases h : step n with
    | none =>
      constructor
      · rintro ⟨⟩; exact ⟨0, by omega, rfl, h⟩
      · rintro ⟨k, _, hk, hr⟩
        cases k with
        | zero => simpa [walk] using hk
        | succ k => simp [walk, h] at hk
    | some m =>
      simp only
      rw [ih]
      constructor
      · rintro ⟨k, hk, hw, hr⟩; exact ⟨k + 1, by omega, by simp [walk, h, hw], hr⟩
      · rintro ⟨k, hk, hw, hr⟩
        cases k with
        | zero =>
          simp only [walk, Option.some.injEq] at hw
          subst hw; simp [h] at hr
        | succ k => exact ⟨k, by omega, by simpa [walk, h] using hw, hr⟩

private theorem walk_add (step : Name → Option Name) (i j : Nat) (n : Name) :
    walk step (i + j) n = (walk step i n).bind (walk step j) := by
  induction i generalizing n with
  | zero => simp [walk]
  | succ i ih =>
    rw [Nat.add_right_comm]
    simp only [walk]
    cases step n with
    | none => rfl
    | some m => simp [ih]

/-- Every name a walk passes before its last has a step. -/
private theorem walk_before_end {step : Name → Option Name} {k : Nat} {n r : Name}
    (hw : walk step k n = some r) {i : Nat} (hi : i < k) :
    ∃ a b, walk step i n = some a ∧ step a = some b := by
  have := walk_add step i (k - i) n
  rw [Nat.add_sub_cancel' (Nat.le_of_lt hi), hw] at this
  cases hwi : walk step i n with
  | none => simp [hwi] at this
  | some a =>
    rw [hwi] at this
    obtain ⟨j, hj⟩ : ∃ j, k - i = j + 1 := ⟨k - i - 1, by omega⟩
    rw [hj] at this
    simp only [Option.bind_some, walk] at this
    cases hs : step a with
    | none => simp [hs] at this
    | some b => exact ⟨a, b, rfl, hs⟩

/-- A walk to a name `step` relates to no other visits no name twice before it: a repeated name
would lead to the end sooner, where the walk still has a step. -/
private theorem walk_nodup {step : Name → Option Name} {k : Nat} {n r : Name}
    (hw : walk step k n = some r) (hr : step r = none) :
    ((List.range k).map fun i => walk step i n).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_map]
  refine List.nodup_range.imp_of_mem ?_
  intro i j hi hj hne heq
  simp only [List.mem_range] at hi hj
  rcases Nat.lt_trichotomy i j with h | h | h
  · have e1 := walk_add step i (k - j) n
    have e2 := walk_add step j (k - j) n
    rw [Nat.add_sub_cancel' (Nat.le_of_lt hj), hw, ← heq] at e2
    rw [← e2] at e1
    obtain ⟨_, b, hb, hs⟩ := walk_before_end hw (i := i + (k - j)) (by omega)
    rw [e1] at hb
    cases hb; simp [hs] at hr
  · exact hne h
  · have e1 := walk_add step j (k - i) n
    have e2 := walk_add step i (k - i) n
    rw [Nat.add_sub_cancel' (Nat.le_of_lt hi), hw, heq] at e2
    rw [← e2] at e1
    obtain ⟨_, b, hb, hs⟩ := walk_before_end hw (i := j + (k - i)) (by omega)
    rw [e1] at hb
    cases hb; simp [hs] at hr

/-- A walk to a name `step` relates to no other is no longer than any list of the names `step`
relates to another. -/
private theorem walk_length_le {step : Name → Option Name} {keys : List Name}
    (hkeys : ∀ a b, step a = some b → a ∈ keys) {k : Nat} {n r : Name}
    (hw : walk step k n = some r) (hr : step r = none) : k ≤ keys.length := by
  have hsub : ((List.range k).map fun i => walk step i n) ⊆ keys.map some := by
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨a, b, ha, hs⟩ := walk_before_end hw hi
    rw [ha]
    exact List.mem_map_of_mem (hkeys a b hs)
  simpa using (walk_nodup hw hr).length_le_of_subset hsub

private theorem generatedStep_mem (index : Std.HashMap Name RegulaPolicy.Declaration)
    (helpers : Array Name) (a b : Name) (h : generatedStep index helpers a = some b) :
    a ∈ index.keys := by
  rw [Std.HashMap.mem_keys]
  unfold generatedStep at h
  cases hi : index[a]? with
  | none => simp [hi] at h
  | some _ => exact Std.HashMap.mem_iff_isSome_getElem?.mpr (by simp [hi])

/-- The name of the declaration a finding about `decl` is attributed to: the end of the chain of
declarations Lean generated `decl` from, one step at a time, as the declarations `index` holds
record it (`generatedStep`, `stepOf`); `none` when Lean did not generate `decl` from another
declaration. The chain ends at a declaration Lean did not generate from another or at a name
`index` does not hold. It follows at most as many steps as `index` holds declarations, never fewer
than such a chain has (`sourceName?_eq_some_iff`). -/
def sourceName? (index : Std.HashMap Name RegulaPolicy.Declaration) (helpers : Array Name)
    (decl : RegulaPolicy.Declaration) : Option Name :=
  (stepOf helpers decl).bind (chainEnd (generatedStep index helpers) (index.size + 1))

/-- A finding about `decl` is attributed to `r` exactly when the recorded generation relation
leads from `decl` to `r` and relates `r` to nothing further: Lean generated `decl` from a
declaration `m`, and `m` from another, and so on, `k` times, to `r`, which it did not generate
from another declaration `index` holds. -/
theorem sourceName?_eq_some_iff (index : Std.HashMap Name RegulaPolicy.Declaration)
    (helpers : Array Name) (decl : RegulaPolicy.Declaration) (r : Name) :
    sourceName? index helpers decl = some r ↔ ∃ m k, stepOf helpers decl = some m ∧
      walk (generatedStep index helpers) k m = some r ∧ generatedStep index helpers r = none := by
  unfold sourceName?
  cases stepOf helpers decl with
  | none => simp
  | some m =>
    rw [Option.bind_some, chainEnd_eq_some_iff]
    constructor
    · rintro ⟨k, _, hw, hr⟩; exact ⟨m, k, rfl, hw, hr⟩
    · rintro ⟨_, k, ⟨⟩, hw, hr⟩
      have := walk_length_le (generatedStep_mem index helpers) hw hr
      rw [Std.HashMap.length_keys] at this
      exact ⟨k, by omega, hw, hr⟩

/-- The declaration a finding is attributed to is not itself attributed to another: its finding
groups under its own name, with those attributed to it. -/
theorem sourceName?_source {index : Std.HashMap Name RegulaPolicy.Declaration}
    {helpers : Array Name} {decl p : RegulaPolicy.Declaration} {r : Name}
    (h : sourceName? index helpers decl = some r) (hp : index[r]? = some p) :
    sourceName? index helpers p = none := by
  obtain ⟨_, _, _, _, hr⟩ := (sourceName?_eq_some_iff index helpers decl r).mp h
  simp only [generatedStep, hp, Option.bind_some] at hr
  simp [sourceName?, hr]

/-- An RG1005 finding built for a subject `name` attributed to `source` groups under `source`, or
under `name` itself when it is attributed to none. The checkers pass the attribution of the
subject (`attribution`), so such a finding groups under a declaration other than its subject
exactly when the recorded generation relation leads to it (`sourceName?_eq_some_iff`). -/
theorem declarationFinding_groupUnder? {name : Name} {detail : String} {location : Location}
    {mode : EvidenceMode} {claim : Option String} {source : Option Name}
    {related : Array RelatedLocation} {f : Finding}
    (h : declarationFinding .profileExceeded name detail location mode claim source related =
      .ok f) : f.groupUnder? = some (source.getD name) := by
  simp only [declarationFinding, makeDiagnostic] at h
  split at h
  · cases h; rfl
  · cases h

/-- The location of a finding about `decl`: its own (`declarationLocation`) when it has a recorded
range; when it has none, the range of the declaration it is attributed to (`sourceName?`) when
`index` holds that declaration with a recorded range and its module has a snapshot, else its
module. So a constructor or field with a range of its own keeps it while grouping under its type.
`snapshotFor` gives the source of a module whose ranges can be admitted. -/
def findingLocation (index : Std.HashMap Name RegulaPolicy.Declaration) (helpers : Array Name)
    (decl : RegulaPolicy.Declaration) (snapshotFor : Name → Option SourceSnapshot) :
    Except String Location := do
  if decl.ranges.isNone then
    if let some p := (sourceName? index helpers decl).bind (index[·]?) then
      if let (some ranges, some source) := (p.ranges, snapshotFor p.module) then
        return .source (← sourceFromReport source ranges)
  declarationLocation decl (snapshotFor decl.module)

/-- The attribution of a finding about `decl`: the declaration it is attributed to
(`sourceName?`), and, when `decl` has no recorded range of its own, a related location naming the
module `decl` belongs to, since its finding is then located at that declaration's range where
that one has a range (`findingLocation`). -/
def attribution (index : Std.HashMap Name RegulaPolicy.Declaration) (helpers : Array Name)
    (decl : RegulaPolicy.Declaration) : Option Name × Array RelatedLocation :=
  match sourceName? index helpers decl with
  | some source => (some source, if decl.ranges.isSome then #[] else
      #[{ relation := "declared in module", location := .module decl.module }])
  | none => (none, #[])

end Regula.Findings
