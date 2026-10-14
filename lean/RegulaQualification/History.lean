import RegulaQualification.Json
import RegulaCore.JsonAgreement
import RegulaPolicy.Guards
import Regula.StructuralName
import Regula.Decision
import RegulaQualification.Member

/-! # History observation requirements

Source-bound history observation requirements. Checks compare the supplied report
with exact source, invocation, requests, and both overwritten replacement targets.
`checked_decoded` supplies sound/complete refusal semantics for the decoded requirement
list. These are predicates on observations, not proofs of source evaluator behavior. -/
namespace RegulaQualification.History
open Lean RegulaPolicy.Guards
open Regula.JsonAgreement (Conforms Regular)

private def object (value : Json) (name : String) : Except String Json := Member.object value name
private def value (value : Json) (name : String) : Except String Json := Member.value value name
private def array (value : Json) (name : String) : Except String (Array Json) :=
    Member.array value name
private def text (value : Json) (name : String) : Except String String := Member.text value name
/-- A dotted Lean name as result documents write it (`Regula.RegistryCodec.printedNameJson`). -/
private def nameJson (name : String) : Json := Regula.RegistryCodec.printedNameJson name.toName

/-- The report account the public protocol selects: the file report, or the first
surface's report for a project invocation. -/
def account (report : Json) (fileMode : Bool) : Except String Json := do
  let scope ← object report "scope"
  if fileMode then object scope "report" else do
    let surfaces ← array scope "surfaces"
    let some surface := surfaces[0]? | throw "missing history surface"
    object surface "report"

/-- The audited module: the first census module. -/
def ownModule (account : Json) : Except String Json := do
  let modules ← array (← object account "census") "modules"
  let some ownModule := modules[0]? | throw "missing history module"
  return ownModule

/-- The imported registered root `Nat.add` executed, attributed to a module other than
the audited one. -/
def importedRootExecuted (execution : Array Json) (ownModule : Json) : Bool :=
  execution.any fun entry =>
    (entry.getObjVal? "name").toOption.any (fun name => decide (Conforms name (nameJson "Nat.add")))
      && (entry.getObjVal? "module").toOption.any
        (fun moduleName => !decide (Conforms moduleName ownModule))

/-- The imported registered root `Nat.add` executed, attributed to a module other than the
audited one, as a proposition: some entry of `execution` has a name that conforms to `Nat.add`
and a module that does not conform to `ownModule` (`Regula.JsonAgreement.Conforms`), and
`importedRootExecuted` decides the proposition (`importedRootExecuted_iff`). A module that is not
a value with search trees conforms to nothing; `requirements` refuses such a report as a whole. -/
def ImportedRootExecuted (execution : Array Json) (ownModule : Json) : Prop :=
  ∃ entry ∈ execution,
    (∃ name, (entry.getObjVal? "name").toOption = some name ∧ Conforms name (nameJson "Nat.add")) ∧
      ∃ moduleName, (entry.getObjVal? "module").toOption = some moduleName ∧
        ¬Conforms moduleName ownModule

/-- The executed test accepts exactly the execution lists that `ImportedRootExecuted` holds
of. -/
theorem importedRootExecuted_iff (execution : Array Json) (ownModule : Json) :
    importedRootExecuted execution ownModule = true ↔
      ImportedRootExecuted execution ownModule := by
  simp [importedRootExecuted, ImportedRootExecuted, -Array.any_eq_true, Array.any_eq_true',
    Option.any_eq_true]

instance (execution : Array Json) (ownModule : Json) :
    Decidable (ImportedRootExecuted execution ownModule) :=
  decidable_of_iff _ (importedRootExecuted_iff execution ownModule)

/-- Every root requested from the audited module has an execution entry with nonempty
unresolved evidence. -/
def requestedRootsUnresolved (requests execution : Array Json) (ownModule : Json) :
    Except String Bool := do
  let ownRequests ← requests.toList.filterMapM fun request => do
    let pair ← request.getArr?
    let [root, moduleName] := pair.toList | throw "invalid history request pair"
    return if decide (Conforms moduleName ownModule) then some root else none
  return ownRequests.all fun root => execution.any fun entry =>
    (entry.getObjVal? "name").toOption.any (fun name => decide (Conforms name root)) &&
      (entry.getObjValAs? (Array Json) "unresolved").toOption.any (! ·.isEmpty)

/-- Reached-closure traversal witnesses for one execution root, and whether it retains
the recursive IR call. Every parent index refers backward to an actually retained edge;
the exact node/visit account is retained. -/
private def rootChecks (unsupported : Bool) (root : Json) : Except String (List Check × Bool) := do
  let closure ← object root "closure"
  let nodes ← array closure "nodes"
  let visits ← array closure "visits"
  let names ← visits.mapM (value · "name")
  let compiler ← array root "compilerEdges"
  let mut edges := compiler
  for key in
      #["logicalEdges", "candidateEdges", "historyEdges", "currentReplacementEdges",
          "helperEdges"] do
    edges := edges ++ (← array closure key)
  -- The visits name each node once: no two visit names conform, and each name conforms to a
  -- node and each node to a name (the report is checked as a value with search trees).
  let mut checks :=
      [Check.mk "exact unique closure visits"
        (decide (names.toList.Pairwise fun a b => ¬Conforms a b) &&
          names.all (fun name => nodes.any (decide <| Conforms · name)) &&
          nodes.all (fun node => names.any (decide <| Conforms · node)))]
  for i in [:visits.size] do
    let visit := visits[i]!
    let parent ← value visit "parent"
    let name ← value visit "name"
    if parent matches .null then
      checks := checks ++
        [⟨"root visit has no parent", i == 0 && decide (Conforms name (← value root "name"))⟩]
    else
      let index ← parent.getNat?
      let predecessor ← match visits[index]? with
        | some predecessor => value predecessor "name"
        | none => throw "parent outside traversal"
      checks := checks ++
          [⟨"backward retained parent edge", index < i && edges.any
              (decide <| Conforms · (toJson #[predecessor, name]))⟩]
  for edge in edges do
    let pair ← edge.getArr?
    let [a, b] := pair.toList | throw "invalid closure edge"
    checks := checks ++ [⟨"edge endpoints covered",
      nodes.any (decide <| Conforms · a) && nodes.any (decide <| Conforms · b)⟩]
  if decide (Conforms (← value root "name") (nameJson "reference")) then
    let current ← array closure "currentReplacementEdges"
    let history ← array closure "historyEdges"
    let earlier := toJson #[nameJson "reference", nameJson "earlier"]
    checks := checks ++
        [⟨"current replacement retained", current.any
            (decide <| Conforms · (toJson #[nameJson "reference", nameJson "target"]))⟩,
      ⟨"earlier replacement remains historical", unsupported ||
          (history.any (decide <| Conforms · earlier) &&
        !current.any (decide <| Conforms · earlier))⟩]
  return (checks, compiler.any
      (decide <| Conforms · (toJson #[nameJson "recursiveSum", nameJson "recursiveSum"])))

/-- Source binding, registered private/imported roots, and reached-closure traversal
witnesses added upstream. -/
def closureRequirements (account ownModule : Json) (source : String) (unsupported : Bool) :
    Except String (List Check) := do
  let bindings ← array account "sourceBindings"
  let snapshots ← bindings.toList.filterMapM fun entry => do
    if decide (Conforms (← value entry "moduleName") ownModule) then
      return some (← text entry "sourceText")
    return none
  let declarations ← array account "declarations"
  let some contract := declarations.find? (fun entry => (entry.getObjVal? "name").toOption.any
      (decide <| Conforms · (nameJson "privateContract")))
    | throw "missing private contract"
  let privateRoot ← value (← object contract "executableContract") "root"
  let census ← array (← object account "census") "declarations"
  let unregistered ← declarations.toList.filterMapM fun entry => do
    let name ← Regula.RegistryCodec.parsePrintedNameJson (← value entry "name")
    return if name matches .str _ "unregistered" then some entry else none
  let [unregistered] := unregistered | throw "missing or repeated private unregistered root"
  let hidden ← value unregistered "name"
  let execution ← array account "execution"
  let isPrivate ← Member.bool unregistered "private"
  let fixed := [
    Check.mk "exact source snapshot" (snapshots == [source]),
    ⟨"registered private root executed", execution.any
        (fun entry => (entry.getObjVal? "name").toOption.any (decide <| Conforms · privateRoot))⟩,
    ⟨"registered private root inventoried",
      census.any (decide <| Conforms · (toJson #[ownModule, privateRoot]))⟩,
    ⟨"unregistered root private", isPrivate⟩,
    ⟨"unregistered private root inventoried",
      census.any (decide <| Conforms · (toJson #[ownModule, hidden]))⟩,
    ⟨"unregistered private root not executed", execution.all
        (fun entry => !(entry.getObjVal? "name").toOption.any (decide <| Conforms · hidden))⟩,
    ⟨"registered imported root executed", decide (ImportedRootExecuted execution ownModule)⟩]
  let perRoot ← execution.toList.mapM (rootChecks unsupported)
  return fixed ++ (perRoot.map (·.1)).flatten ++
      [⟨"recursive IR calls retained", perRoot.any (·.2)⟩]

/-- Unsupported evaluators require explicit unavailability, never a successful empty
history, and unresolved execution evidence for every requested root. -/
def unsupportedRequirements (account ownModule history : Json) (requests : Array Json) :
    Except String (List Check) := do
  let execution ← array account "execution"
  let coverage ← requestedRootsUnresolved requests execution ownModule
  let requested ← execution.toList.filterMapM fun entry => do
    let name ← value entry "name"
    if requests.any (decide <| Conforms · (toJson #[name, ownModule])) then
      return some (← array entry "unresolved")
    return none
  return [
    ⟨"unsupported history explicitly unavailable", (← text history "kind") == "unavailable"⟩,
    ⟨"unsupported evaluator reason",
        (← text history "detail").contains "unsupported replacement-history evaluators"⟩,
    ⟨"every requested root has unresolved execution evidence", coverage⟩,
    ⟨"requested execution unresolved", requested.all (! ·.isEmpty)⟩]

/-- A completed history binds the exact source and retains both replacement targets. -/
def completedRequirements (history : Json) (source : String) : Except String (List Check) := do
  let replacements ← array history "replacements"
  return [
    ⟨"history completed", (← text history "kind") == "completed"⟩,
    ⟨"history before binds source", (← text (← object history "before") "sourceText") == source⟩,
    ⟨"history after binds source", (← text (← object history "after") "sourceText") == source⟩,
    ⟨"history has Lean source path", (← text history "path").endsWith ".lean"⟩,
    ⟨"earlier replacement retained", replacements.any
        (decide <| Conforms · (toJson #[nameJson "reference", nameJson "earlier"]))⟩,
    ⟨"current replacement retained", replacements.any
        (decide <| Conforms · (toJson #[nameJson "reference", nameJson "target"]))⟩]

/-- Mandatory decoding plus all preserved history assertions. `fileMode` selects the
actual public report shape; unsupported evaluators require explicit unavailability,
never a successful empty history. -/
def requirements (report : Json) (code : Nat) (mode source : String)
    (fileMode unsupported : Bool) : Except String (List Check) := do
  let account ← account report fileMode
  let requests ← array (← object account "census") "historyRequests"
  let ownModule ← ownModule account
  let histories ← array account "histories"
  let owned ← histories.toList.filterMapM fun entry => do
    let pair ← entry.getArr?
    let some moduleName := pair[0]? | throw "missing history owner"
    let some history := pair[1]? | throw "missing history payload"
    return if decide (Conforms moduleName ownModule) then some history else none
  let [history] := owned | throw "expected exactly one own history"
  let diagnostics ← array report "diagnostics"
  let ids ← diagnostics.toList.mapM (fun d => text d "id")
  let base : List Check := [
    -- Each comparison below conforms one value of the report to another value: the report
    -- being a value with search trees makes it equality of the two values.
    ⟨"history report with search trees", decide (Regular report)⟩,
    ⟨"history exit", code == (if unsupported then 3 else 0)⟩,
    ⟨"history mode", (← text report "mode") == mode⟩,
    ⟨"history diagnostics", ids.eraseDups == (if unsupported then ["RG3001"] else [])⟩,
    ⟨"history status", (← text report "status") ==
        (if unsupported then "incomplete" else "completed")⟩,
    ⟨"nonempty unique history requests", !requests.isEmpty &&
        decide (requests.toList.Pairwise fun a b => ¬Conforms a b)⟩,
    ⟨"all three requested roots", ["reference", "first", "second"].all
      (fun root => requests.any (decide <| Conforms · (toJson #[nameJson root, ownModule])))⟩]
  let modeChecks ← if unsupported then unsupportedRequirements account ownModule history requests
    else completedRequirements history source
  return base ++ modeChecks ++ (← closureRequirements account ownModule source unsupported)

/-- Exact admission contract for the decoded history requirements. Missing fields
refuse before assertion evaluation; all predicates in `requirements` must hold. -/
@[regula_decision]
def validate (report : Json) (code : Nat) (mode source : String)
    (fileMode unsupported : Bool) : Except String Unit :=
  checked_decoded.run (requirements report code mode source fileMode unsupported)

/-- The application cannot replace the history oracle with an always-successful or
always-refusing implementation while retaining this required equivalence. -/
theorem checked_validation : Regula.ExecutableContract validate
    (fun run => ∀ report code mode source fileMode unsupported,
      run report code mode source fileMode unsupported = .ok () ↔
        ∃ checks, requirements report code mode source fileMode unsupported = .ok checks ∧
            Satisfied checks) :=
  ⟨fun _ _ _ _ _ _ => validateDecoded_exact _⟩

/-- `validate` is a complete decision of its requirements: it accepts every report whose
requirements decode and all hold, and it refuses a `null` report. Soundness also holds
(`checked_validation` registers the equivalence), but the kind is one-way because a sound kind
requires a report the function accepts, and a conforming history report is a result document
that only an audit produces; accepted reports are observed by the `history` diagnostic. -/
theorem checked_validation_complete : Regula.ExecutableContract validate (fun run =>
    Regula.DecidesCompletely (· = .ok ())
      (fun input : ((((Json × Nat) × String) × String) × Bool) × Bool =>
        ∃ checks, requirements input.1.1.1.1.1 input.1.1.1.1.2 input.1.1.1.2 input.1.1.2
          input.1.2 input.2 = .ok checks ∧ Satisfied checks)
      (Function.uncurry (Function.uncurry (Function.uncurry (Function.uncurry
        (Function.uncurry run)))))) :=
  ⟨{ complete := fun input holds =>
       (checked_validation.evidence input.1.1.1.1.1 input.1.1.1.1.2 input.1.1.1.2 input.1.1.2
         input.1.2 input.2).mpr holds
     refused := ⟨(((((.null, 0), ""), ""), false), false),
       fun accepted => absurd (congrArg Except.isOk accepted) (by decide +kernel)⟩ }⟩

/-- `validate` accepts exactly the reports whose requirements decode and all hold, as a law
(`Regula.DecisionEquivalence`) on the product of its six arguments, from `checked_validation`.
The complete kind `checked_validation_complete` is kept: it adds the report the function refuses,
which the law does not supply. -/
theorem checked_validation_law : Regula.ExecutableContract validate (fun run =>
    Regula.DecisionEquivalence (· = .ok ())
      (fun input : ((((Json × Nat) × String) × String) × Bool) × Bool =>
        ∃ checks, requirements input.1.1.1.1.1 input.1.1.1.1.2 input.1.1.1.2 input.1.1.2
          input.1.2 input.2 = .ok checks ∧ Satisfied checks)
      (Function.uncurry (Function.uncurry (Function.uncurry (Function.uncurry
        (Function.uncurry run)))))) :=
  ⟨⟨fun input => checked_validation.evidence input.1.1.1.1.1 input.1.1.1.1.2 input.1.1.1.2
    input.1.1.2 input.1.2 input.2⟩⟩

/-! ### What an admitted history report establishes

These replace the former sampled oracle mutations (a dropped imported-root module and
dropped or emptied execution entries): every admitted report, not only the mutated
ones, satisfies the stated relation. They concern supplied JSON only. -/

/-- A successful closure account contains the imported-root check over its execution list. -/
theorem closureRequirements_imported {account ownModule : Json} {source : String}
    {unsupported : Bool}
    {checks : List Check}
        (h : closureRequirements account ownModule source unsupported = .ok checks) :
    ∃ execution, account.getObjValAs? (Array Json) "execution" = .ok execution ∧
      ⟨"registered imported root executed",
        decide (ImportedRootExecuted execution ownModule)⟩ ∈ checks := by
  unfold closureRequirements at h
  simp only [bind_eq_ok] at h
  obtain ⟨_, _, _, _, _, _, h⟩ := h
  split at h
  · simp only [bind_eq_ok] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := h
    split at h
    · simp only [bind_eq_ok, pure_eq_ok] at h
      obtain ⟨_, _, execution, hexec, _, _, _, _, rfl⟩ := h
      exact ⟨execution, (Member.array_eq_ok_iff _ _ _).mp hexec, by simp⟩
    · simp at h
  · simp at h

/-- A successful unsupported-evaluator account contains the unresolved-coverage check. -/
theorem unsupportedRequirements_unresolved {account ownModule history : Json}
    {requests : Array Json}
    {checks : List Check}
        (h : unsupportedRequirements account ownModule history requests = .ok checks) :
    ∃ execution coverage, account.getObjValAs? (Array Json) "execution" = .ok execution ∧
      requestedRootsUnresolved requests execution ownModule = .ok coverage ∧
      ⟨"every requested root has unresolved execution evidence", coverage⟩ ∈ checks := by
  unfold unsupportedRequirements at h
  simp only [bind_eq_ok, pure_eq_ok] at h
  obtain ⟨execution, hexec, coverage, hcov, _, _, _, _, _, _, rfl⟩ := h
  exact ⟨execution, coverage, (Member.array_eq_ok_iff _ _ _).mp hexec, hcov, by simp⟩

/-- An admitted requirement list contains the closure checks and, for an unsupported
evaluator, the unsupported-evaluator checks. -/
theorem requirements_parts {report : Json} {code : Nat} {mode source : String}
    {fileMode unsupported : Bool}
    {checks : List Check}
        (h : requirements report code mode source fileMode unsupported = .ok checks) :
    ∃ acc own requests, History.account report fileMode = .ok acc ∧
        History.ownModule acc = .ok own ∧
      (acc.getObjVal? "census" >>= fun census => census.getObjValAs?
                                                  (Array Json) "historyRequests") =
        .ok requests ∧
      (∃ closure, closureRequirements acc own source unsupported = .ok closure ∧ ∀ c ∈ closure,
          c ∈ checks) ∧
      (unsupported = true → ∃ history modeChecks,
        unsupportedRequirements acc own history requests = .ok modeChecks ∧ ∀ c ∈ modeChecks,
            c ∈ checks) := by
  unfold requirements at h
  simp only [bind_eq_ok] at h
  obtain ⟨acc, hacc, census, hcensus, requests, hrequests, own, hown, _, _, owned, _, h⟩ := h
  refine
      ⟨acc, own, requests, hacc, hown, by
        simpa [bind_eq_ok] using ⟨census, ((Member.object_eq_ok_iff _ _ _).mp hcensus).1,
          (Member.array_eq_ok_iff _ _ _).mp hrequests⟩, ?_⟩
  split at h
  next history _ =>
    simp only [bind_eq_ok] at h
    obtain ⟨_, _, _, _, _, _, _, _, h⟩ := h
    cases unsupported
    · simp only [Bool.false_eq_true, ite_false, bind_eq_ok, pure_eq_ok] at h
      obtain ⟨_, _, closure, hclosure, rfl⟩ := h
      exact ⟨⟨closure, hclosure, fun c hc => by simp [hc]⟩, by simp⟩
    · simp only [ite_true, bind_eq_ok, pure_eq_ok] at h
      obtain ⟨modeChecks, hmode, closure, hclosure, rfl⟩ := h
      exact ⟨⟨closure, hclosure, fun c hc => by simp [hc]⟩,
        fun _ => ⟨history, modeChecks, hmode, fun c hc => by simp [hc]⟩⟩
  next => simp at h

/-- Every admitted history report's own account executes the imported registered root
`Nat.add` attributed to a module other than the audited one. -/
theorem validate_importedRootExecuted {report : Json} {code : Nat} {mode source : String}
    {fileMode unsupported : Bool}
        (h : validate report code mode source fileMode unsupported = .ok ()) :
    ∃ acc own execution, History.account report fileMode = .ok acc ∧
        History.ownModule acc = .ok own ∧
      acc.getObjValAs? (Array Json) "execution" = .ok execution ∧
      ImportedRootExecuted execution own := by
  obtain ⟨checks, hreq, hsat⟩ := (validateDecoded_exact _).mp h
  obtain ⟨acc, own, _, hacc, hown, _, ⟨closure, hclosure, hsub⟩, _⟩ := requirements_parts hreq
  obtain ⟨execution, hexec, hmem⟩ := closureRequirements_imported hclosure
  exact ⟨acc, own, execution, hacc, hown, hexec, of_decide_eq_true (hsat _ (hsub _ hmem))⟩

/-- Every admitted unsupported-evaluator report leaves every root requested from the
audited module with nonempty unresolved execution evidence. -/
theorem validate_unsupported_unresolved {report : Json} {code : Nat} {mode source : String}
    {fileMode : Bool} (h : validate report code mode source fileMode true = .ok ()) :
    ∃ acc own requests execution, History.account report fileMode = .ok acc ∧
      History.ownModule acc = .ok own ∧
      (acc.getObjVal? "census" >>= fun census => census.getObjValAs?
                                                  (Array Json) "historyRequests") =
        .ok requests ∧
      acc.getObjValAs? (Array Json) "execution" = .ok execution ∧
      requestedRootsUnresolved requests execution own = .ok true := by
  obtain ⟨checks, hreq, hsat⟩ := (validateDecoded_exact _).mp h
  obtain ⟨acc, own, requests, hacc, hown, hrequests, _, hmode⟩ := requirements_parts hreq
  obtain ⟨_, modeChecks, hmodeChecks, hsub⟩ := hmode rfl
  obtain ⟨execution, coverage, hexec, hcov, hmem⟩ := unsupportedRequirements_unresolved hmodeChecks
  have : coverage = true := hsat _ (hsub _ hmem)
  exact ⟨acc, own, requests, execution, hacc, hown, hrequests, hexec, this ▸ hcov⟩

end RegulaQualification.History
