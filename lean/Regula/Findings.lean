module

public import Regula.Diagnostic
public import Lean.PrivateName
public import Std.Data.HashMap.Basic
import Std.Data.HashMap.Lemmas

/-! # Diagnostic finding adapters

Import-safe adapters to the canonical diagnostic schema. Policy decisions
remain in the policy core; these functions preserve identity and mode, and locate a declaration
without a source range at the declaration it is attributed to (`findingLocation`). -/

public section

namespace Regula.Findings
open Lean

/-- New diagnostic identity is recovered from the original structural Name only. -/
def declarationName (decl : RegulaPolicy.Declaration) : Except String Name := do
  unless decl.name != .anonymous do throw "anonymous declaration identity"
  return decl.name

/-- The violation finding of a declaration-scoped rule `id` for declaration `name`, with its
detail, location, mode and claim, the declaration it is attributed to, if any
(`sourceDeclaration?`), and related locations. A rule outside the declaration domain, or a mode
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

/-- The proper prefixes of a name, nearest first, without the anonymous name. -/
def properPrefixes : Name → List Name
  | .anonymous => []
  | .str p _ | .num p _ => if p.isAnonymous then [] else p :: properPrefixes p

/-- The names a declaration without a source range is attributed to, nearest first: at each
depth, the proper prefix of `name` and then that of its user name (`Lean.privateToUserName`), the
two spellings Lean's own equation-lemma lookup tries (`Lean.Meta.declFromEqLikeName`), since a
declaration's equation lemmas can be private when it is not. A private name's nearest prefixes
correspond one for one to its user name's, so interleaving them keeps the nearest first. Lean
names most declarations it generates inside the one it generates them from, such as `f.eq_1`,
`f.match_1`, `f._proof_1`, `T.rec` and `T.casesOn`; that naming is Lean's convention, assumed
here, not established. -/
def sourceCandidates (name : Name) : List Name :=
  interleave (properPrefixes name) (properPrefixes (privateToUserName name))
where
  /-- The elements of both lists, alternately, then the rest of the longer one. -/
  interleave : List Name → List Name → List Name
    | a :: as, b :: bs => a :: b :: interleave as bs
    | as, [] => as
    | [], bs => bs

/-- The declarations of `ds` that Lean recorded a declaration range for, by name; the first wins
(`rangedIndex_get`). -/
def rangedIndex (ds : Array RegulaPolicy.Declaration) :
    Std.HashMap Name RegulaPolicy.Declaration :=
  ds.foldr (fun p index => if p.ranges.isSome then index.insert p.name p else index) {}

/-- Looking a name up in `rangedIndex ds` is finding the first declaration of `ds` with that name
and a recorded range. -/
theorem rangedIndex_get (ds : Array RegulaPolicy.Declaration) (n : Name) :
    (rangedIndex ds)[n]? = ds.find? fun p => p.ranges.isSome && p.name == n := by
  unfold rangedIndex
  rw [← Array.foldr_toList, ← Array.find?_toList]
  generalize ds.toList = l
  induction l with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldr_cons, List.find?_cons]
    rw [← ih]
    cases p.ranges.isSome <;> cases hn : (p.name == n) <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Std.HashMap.getElem?_insert, hn, Bool.true_and,
        Bool.false_and]

/-- The declaration a finding about `decl` is attributed to, among those `index` holds
(`rangedIndex`): none when Lean recorded a declaration range for `decl` itself; otherwise the
declaration named by the nearest of its `sourceCandidates` that has a recorded range. Lean records
no range for most declarations it generates, such as equation lemmas, matchers, auxiliary proofs,
recursors and `casesOn`; under the naming convention `sourceCandidates` assumes, this is the
declaration they were generated from. A metaprogram can also add a declaration without a range;
it is attributed to the nearest enclosing name all the same. Lean-generated declarations with a
range, such as a structure's default constructor, projections and derived instances, keep their
own. -/
def sourceDeclaration? (index : Std.HashMap Name RegulaPolicy.Declaration)
    (decl : RegulaPolicy.Declaration) : Option RegulaPolicy.Declaration :=
  if decl.ranges.isSome then none else (sourceCandidates decl.name).findSome? (index[·]?)

/-- Over `rangedIndex ds`, the source is the first declaration of `ds` that has a recorded range
and is named by the nearest candidate that names one. -/
theorem sourceDeclaration?_rangedIndex (ds : Array RegulaPolicy.Declaration)
    (decl : RegulaPolicy.Declaration) :
    sourceDeclaration? (rangedIndex ds) decl =
      if decl.ranges.isSome then none
      else (sourceCandidates decl.name).findSome? fun n =>
        ds.find? fun p => p.ranges.isSome && p.name == n := by
  simp only [sourceDeclaration?, rangedIndex_get]

/-- The declaration a finding is attributed to is a declaration of `ds` with a recorded range,
named by one of the candidates of a declaration that has none; having a range, it is never itself
attributed to another. -/
theorem sourceDeclaration?_spec {ds : Array RegulaPolicy.Declaration}
    {decl p : RegulaPolicy.Declaration} (h : sourceDeclaration? (rangedIndex ds) decl = some p) :
    decl.ranges = none ∧ p ∈ ds ∧ p.ranges.isSome ∧ p.name ∈ sourceCandidates decl.name ∧
      sourceDeclaration? (rangedIndex ds) p = none := by
  rw [sourceDeclaration?_rangedIndex] at h
  by_cases hd : decl.ranges.isSome = true
  · simp [hd] at h
  · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨n, hn, hfind⟩ := List.exists_of_findSome?_eq_some h
    have hp := Array.mem_of_find?_eq_some hfind
    have hpred := Array.find?_some hfind
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred
    refine ⟨Option.not_isSome_iff_eq_none.mp hd, hp, hpred.1, hpred.2 ▸ hn, ?_⟩
    simp [sourceDeclaration?, hpred.1]

/-- The location of a finding about `decl`: its own recorded range, else the range of the
declaration it is attributed to (`sourceDeclaration?`) when that declaration's module has a
snapshot, else its module. `snapshotFor` gives the source of a module whose ranges can be
admitted. -/
def findingLocation (index : Std.HashMap Name RegulaPolicy.Declaration)
    (decl : RegulaPolicy.Declaration) (snapshotFor : Name → Option SourceSnapshot) :
    Except String Location := do
  match sourceDeclaration? index decl with
  | some p => match p.ranges, snapshotFor p.module with
    | some ranges, some source => return .source (← sourceFromReport source ranges)
    | _, _ => declarationLocation decl (snapshotFor decl.module)
  | none => declarationLocation decl (snapshotFor decl.module)

/-- The attribution of a finding about `decl`: the declaration it is attributed to
(`sourceDeclaration?`), and then a related location naming the module `decl` belongs to, which the
finding's location no longer states when it is that declaration's range (`findingLocation`). -/
def attribution (index : Std.HashMap Name RegulaPolicy.Declaration)
    (decl : RegulaPolicy.Declaration) : Option Name × Array RelatedLocation :=
  match sourceDeclaration? index decl with
  | some p => (some p.name, #[{ relation := "declared in module", location := .module decl.module }])
  | none => (none, #[])

end Regula.Findings
