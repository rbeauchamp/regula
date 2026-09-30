import RegulaQualification.Json
import RegulaPolicy.Guards

/-! # History observation requirements

Source-bound history observation requirements. Checks compare the supplied report
with exact source, invocation, requests, and both overwritten replacement targets.
`checked_decoded` supplies sound/complete refusal semantics for the decoded requirement
list. These are predicates on observations, not proofs of source evaluator behavior. -/
namespace RegulaQualification.History
open Lean RegulaPolicy.Guards

private def field (value : Json) (name : String) : Except String Json := value.getObjVal? name
private def array (value : Json) (name : String) : Except String (Array Json) :=
    value.getObjValAs? _ name
private def text (value : Json) (name : String) : Except String String := value.getObjValAs? _ name
private def nameJson (name : String) : Json := toJson
    (name.splitOn "." |>.map fun part => #["str", part])

/-- The report account the public protocol selects: the file report, or the first
surface's report for a project invocation. -/
def account (report : Json) (fileMode : Bool) : Except String Json := do
  let scope ← field report "scope"
  if fileMode then field scope "report" else do
    let surfaces ← array scope "surfaces"
    let some surface := surfaces[0]? | throw "missing history surface"
    field surface "report"

/-- The audited module: the first census module. -/
def ownModule (account : Json) : Except String Json := do
  let modules ← array (← field account "census") "modules"
  let some ownModule := modules[0]? | throw "missing history module"
  return ownModule

/-- The imported registered root `Nat.add` executed, attributed to a module other than
the audited one. -/
def importedRootExecuted (execution : Array Json) (ownModule : Json) : Bool :=
  execution.any fun entry =>
    (entry.getObjVal? "name").toOption == some (toJson #[#["str", "add"], #["str", "Nat"]]) &&
      (entry.getObjVal? "module").toOption.any (fun moduleName => moduleName != ownModule)

/-- Every root requested from the audited module has an execution entry with nonempty
unresolved evidence. -/
def requestedRootsUnresolved (requests execution : Array Json) (ownModule : Json) :
    Except String Bool := do
  let ownRequests ← requests.toList.filterMapM fun request => do
    let pair ← request.getArr?
    let [root, moduleName] := pair.toList | throw "invalid history request pair"
    return if moduleName == ownModule then some root else none
  return ownRequests.all fun root => execution.any fun entry =>
    (entry.getObjVal? "name").toOption == some root &&
      (entry.getObjValAs? (Array Json) "unresolved").toOption.any (! ·.isEmpty)

/-- Reached-closure traversal witnesses for one execution root, and whether it retains
the recursive IR call. Every parent index refers backward to an actually retained edge;
the exact node/visit account is retained. -/
private def rootChecks (unsupported : Bool) (root : Json) : Except String (List Check × Bool) := do
  let closure ← field root "closure"
  let nodes ← array closure "nodes"
  let visits ← array closure "visits"
  let names ← visits.mapM (field · "name")
  let compiler ← array root "compilerEdges"
  let mut edges := compiler
  for key in
      #["logicalEdges", "candidateEdges", "historyEdges", "currentReplacementEdges",
          "helperEdges"] do
    edges := edges ++ (← array closure key)
  let mut checks :=
      [Check.mk "exact unique closure visits" (names.size == nodes.toList.eraseDups.length &&
    names.all nodes.contains && nodes.all names.contains)]
  for i in [:visits.size] do
    let visit := visits[i]!
    let parent ← field visit "parent"
    let name ← field visit "name"
    if parent == Json.null then
      checks := checks ++ [⟨"root visit has no parent", i == 0 && name == (← field root "name")⟩]
    else
      let index ← parent.getNat?
      let predecessor ← match visits[index]? with
        | some value => field value "name"
        | none => throw "parent outside traversal"
      checks := checks ++
          [⟨"backward retained parent edge", index < i && edges.contains
              (toJson #[predecessor, name])⟩]
  for edge in edges do
    let pair ← edge.getArr?
    let [a, b] := pair.toList | throw "invalid closure edge"
    checks := checks ++ [⟨"edge endpoints covered", nodes.contains a && nodes.contains b⟩]
  if (← field root "name") == nameJson "reference" then
    let current ← array closure "currentReplacementEdges"
    let history ← array closure "historyEdges"
    checks := checks ++
        [⟨"current replacement retained", current.contains
            (toJson #[nameJson "reference", nameJson "target"])⟩,
      ⟨"earlier replacement remains historical", unsupported ||
          (history.contains (toJson #[nameJson "reference", nameJson "earlier"]) &&
        !current.contains (toJson #[nameJson "reference", nameJson "earlier"]))⟩]
  return (checks, compiler.any
      (fun edge => edge == toJson #[nameJson "recursiveSum", nameJson "recursiveSum"]))

/-- Source binding, registered private/imported roots, and reached-closure traversal
witnesses added upstream. -/
def closureRequirements (account ownModule : Json) (source : String) (unsupported : Bool) :
    Except String (List Check) := do
  let bindings ← array account "sourceBindings"
  let snapshots ← bindings.toList.filterMapM fun entry => do
    if (← field entry "moduleName") == ownModule then return some (← text entry "content")
    return none
  let declarations ← array account "declarations"
  let some contract := declarations.find?
      (fun entry => (entry.getObjVal? "name").toOption == some (nameJson "privateContract"))
    | throw "missing private contract"
  let privateRoot ← field (← field contract "executableContract") "root"
  let census ← array (← field account "census") "declarations"
  let unregistered ← declarations.toList.filterMapM fun entry => do
    let names ← array entry "name"
    return if names[0]? == some (toJson #["str", "unregistered"]) then some entry else none
  let [unregistered] := unregistered | throw "missing or repeated private unregistered root"
  let hidden ← field unregistered "name"
  let execution ← array account "execution"
  let isPrivate ← unregistered.getObjValAs? Bool "private"
  let fixed := [
    Check.mk "exact source snapshot" (snapshots == [source]),
    ⟨"registered private root executed", execution.any
        (fun entry => (entry.getObjVal? "name").toOption == some privateRoot)⟩,
    ⟨"registered private root inventoried", census.contains (toJson #[ownModule, privateRoot])⟩,
    ⟨"unregistered root private", isPrivate⟩,
    ⟨"unregistered private root inventoried", census.contains (toJson #[ownModule, hidden])⟩,
    ⟨"unregistered private root not executed", execution.all
        (fun entry => (entry.getObjVal? "name").toOption != some hidden)⟩,
    ⟨"registered imported root executed", importedRootExecuted execution ownModule⟩]
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
    let name ← field entry "name"
    if requests.contains (toJson #[name, ownModule]) then return some (← array entry "unresolved")
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
    ⟨"history before binds source", (← text history "before") == source⟩,
    ⟨"history after binds source", (← text history "after") == source⟩,
    ⟨"history has Lean source path", (← text history "path").endsWith ".lean"⟩,
    ⟨"earlier replacement retained", replacements.contains
        (toJson #[nameJson "reference", nameJson "earlier"])⟩,
    ⟨"current replacement retained", replacements.contains
        (toJson #[nameJson "reference", nameJson "target"])⟩]

/-- Mandatory decoding plus all preserved history assertions. `fileMode` selects the
actual public report shape; unsupported evaluators require explicit unavailability,
never a successful empty history. -/
def requirements (report : Json) (code : Nat) (mode source : String)
    (fileMode unsupported : Bool) : Except String (List Check) := do
  let account ← account report fileMode
  let requests ← array (← field account "census") "historyRequests"
  let ownModule ← ownModule account
  let histories ← array account "histories"
  let owned ← histories.toList.filterMapM fun entry => do
    let pair ← entry.getArr?
    let some moduleName := pair[0]? | throw "missing history owner"
    let some history := pair[1]? | throw "missing history payload"
    return if moduleName == ownModule then some history else none
  let [history] := owned | throw "expected exactly one own history"
  let diagnostics ← array report "diagnostics"
  let ids ← diagnostics.toList.mapM (fun d => text d "id")
  let base : List Check := [
    ⟨"history exit", code == (if unsupported then 3 else 0)⟩,
    ⟨"history mode", (← text report "mode") == mode⟩,
    ⟨"history diagnostics", ids.eraseDups == (if unsupported then ["RG3001"] else [])⟩,
    ⟨"history status", (← text report "status") ==
        (if unsupported then "incomplete" else "completed")⟩,
    ⟨"nonempty unique history requests", !requests.isEmpty && requests.toList.eraseDups.length ==
        requests.size⟩,
    ⟨"all three requested roots", ["reference", "first", "second"].all
      (fun root => requests.contains (toJson #[nameJson root, ownModule]))⟩]
  let modeChecks ← if unsupported then unsupportedRequirements account ownModule history requests
    else completedRequirements history source
  return base ++ modeChecks ++ (← closureRequirements account ownModule source unsupported)

/-- Exact admission contract for the decoded history requirements. Missing fields
refuse before assertion evaluation; all predicates in `requirements` must hold. -/
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
      ⟨"registered imported root executed", importedRootExecuted execution ownModule⟩ ∈ checks := by
  unfold closureRequirements at h
  simp only [bind_eq_ok] at h
  obtain ⟨_, _, _, _, _, _, h⟩ := h
  split at h
  · simp only [bind_eq_ok] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := h
    split at h
    · simp only [bind_eq_ok, pure_eq_ok] at h
      obtain ⟨_, _, execution, hexec, _, _, _, _, rfl⟩ := h
      exact ⟨execution, hexec, by simp⟩
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
  exact ⟨execution, coverage, hexec, hcov, by simp⟩

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
      ⟨acc, own, requests, hacc, hown, by simpa [bind_eq_ok] using ⟨census, hcensus, hrequests⟩, ?_⟩
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
      importedRootExecuted execution own = true := by
  obtain ⟨checks, hreq, hsat⟩ := (validateDecoded_exact _).mp h
  obtain ⟨acc, own, _, hacc, hown, _, ⟨closure, hclosure, hsub⟩, _⟩ := requirements_parts hreq
  obtain ⟨execution, hexec, hmem⟩ := closureRequirements_imported hclosure
  exact ⟨acc, own, execution, hacc, hown, hexec, hsat _ (hsub _ hmem)⟩

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
