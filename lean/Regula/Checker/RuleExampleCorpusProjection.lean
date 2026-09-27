import Regula.Checker.RuleExampleProjection

/-! # Corpus qualifier projection

Exact transport of the unchanged corpus qualifier through the qualification-only
result view. The private proof decomposition is definitionally the actual qualifier;
it neither replaces execution nor changes scan order, completeness, or refusal text. -/
open Lean Regula.Checker.RuleExampleQualification
namespace Regula.Checker.RuleExampleProjection
variable {α β : Type}

private theorem filterAuxM_map (f : α → β) (p : β → Except String Bool)
    (xs acc : List α) :
    List.filterAuxM p (xs.map f) (acc.map f) =
      (List.filterAuxM (fun x => p (f x)) xs acc).map (List.map f) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.filterAuxM]
    cases hp : p (f x) with
    | error e => rfl
    | ok b =>
      cases b
      · simpa [bind, Bind.bind, Except.bind] using ih acc
      · simpa [bind, Bind.bind, Except.bind] using ih (x :: acc)

private theorem filterM_map (f : α → β) (p : β → Except String Bool) (xs : Array α) :
    (xs.map f).filterM p = (xs.filterM (fun x => p (f x))).map (Array.map f) := by
  cases xs with | mk xs =>
    rw [show Array.map f { toList := xs } = (xs.map f).toArray by simp]
    rw [List.filterM_toArray, List.filterM_toArray]
    unfold List.filterM
    rw [show List.filterAuxM p (xs.map f) [] =
      (List.filterAuxM (fun x => p (f x)) xs []).map (List.map f) from filterAuxM_map f p xs []]
    generalize List.filterAuxM (fun x => p (f x)) xs [] = res
    cases res <;> simp [bind, Bind.bind, Except.bind, Except.map, Functor.map, pure, Pure.pure, Except.pure, List.map_reverse]

private def phaseCheck (records : Array Json) (rule phase : String) : Except String (ForInStep PUnit) := do
  let matching ← records.filterM fun record => do
    return (← string record "rule") == rule && (← string record "phase") == phase
  unless matching.size == 1 do throw "missing or repeated fixture phase"
  let some record := matching[0]? | throw "missing fixture record"
  unless ((← string record "kind") == "positive") == (phase != "Violation") do
    throw "fixture phase classification mismatch"
  qualify record
  pure (.yield PUnit.unit)

private theorem phaseCheck_congr (xs : Array α) (f g : α → Json) (rule phase : String)
    (hr : ∀ x, string (f x) "rule" = string (g x) "rule")
    (hp : ∀ x, string (f x) "phase" = string (g x) "phase")
    (hk : ∀ x, string (f x) "kind" = string (g x) "kind")
    (hq : ∀ x, qualify (f x) = qualify (g x)) :
    phaseCheck (xs.map f) rule phase = phaseCheck (xs.map g) rule phase := by
  unfold phaseCheck
  rw [filterM_map, filterM_map]
  simp only [hr, hp]
  generalize xs.filterM (fun x => do
    return (← string (g x) "rule") == rule && (← string (g x) "phase") == phase) = matching
  cases matching with
  | error e => rfl
  | ok ys =>
    simp only [Except.map, bind, Bind.bind, Except.bind, Array.size_map, Array.getElem?_map]
    cases ys[0]? <;> simp [hk, hq, Option.map]

private def corpusBody (json : Json) : Except String Unit := do
  unless (← field json "schemaVersion") == toJson (1 : Nat) do throw "unsupported corpus schema"
  let selected ← (← (← field json "selected").getArr?).mapM Regula.RegistryCodec.parseRule
  unless decide selected.toList.Nodup do throw "duplicate selected rule"
  let complete ← (← field json "completeCorpus").getBool?
  if complete then
    unless selected.size == Regula.RuleId.all.length && Regula.RuleId.all.all selected.contains do
      throw "incomplete rule corpus: not every registered rule"
  let checkerBefore ← field json "checkerBefore"
  unless checkerBefore == (← field json "checkerAfter") do throw "checker sources changed"
  let checkerFiles ← sources checkerBefore
  unless !checkerFiles.isEmpty do throw "missing checker source state"
  let records := (← (← field json "records").getArr?).map
    (fun record => record.setObjVal! "checkerSources" checkerBefore)
  unless records.size == selected.size * 2 do throw "missing or extra fixture phase"
  for rule in selected do
    let _ ← forIn #["Fixed", "Violation"] PUnit.unit fun phase _ =>
      phaseCheck records rule.spelling phase
    pure ()

private theorem corpusBody_eq (json : Json) : qualifyCorpus json = corpusBody json := by
  rfl

/-- Canonical corpus construction. All metadata and phase order are unchanged. -/
def corpus (fields : List (String × Json)) (records : Array Json) : Json :=
  (Json.mkObj fields).setObjVal! "records" (.arr records)

theorem qualifyCorpus_congr (fields : List (String × Json)) (xs : Array α) (f g : α → Json)
    (hr : ∀ x checker, string ((f x).setObjVal! "checkerSources" checker) "rule" =
      string ((g x).setObjVal! "checkerSources" checker) "rule")
    (hp : ∀ x checker, string ((f x).setObjVal! "checkerSources" checker) "phase" =
      string ((g x).setObjVal! "checkerSources" checker) "phase")
    (hk : ∀ x checker, string ((f x).setObjVal! "checkerSources" checker) "kind" =
      string ((g x).setObjVal! "checkerSources" checker) "kind")
    (hq : ∀ x checker, qualify ((f x).setObjVal! "checkerSources" checker) =
      qualify ((g x).setObjVal! "checkerSources" checker)) :
    qualifyCorpus (corpus fields (xs.map f)) = qualifyCorpus (corpus fields (xs.map g)) := by
  simp only [corpusBody_eq, corpusBody, corpus,
    field_set (Json.mkObj fields) Std.TreeMap.Raw.WF.ofList]
  simp only [show ("records" = "schemaVersion") = False by decide,
    show ("records" = "selected") = False by decide,
    show ("records" = "completeCorpus") = False by decide,
    show ("records" = "checkerBefore") = False by decide,
    show ("records" = "checkerAfter") = False by decide,
    ite_false, ite_true, Json.getArr?, bind, Bind.bind, Except.bind,
    pure, Pure.pure, Except.pure, Array.map_map, Array.size_map, Function.comp_def]
  simp only [phaseCheck_congr xs _ _ _ _ (fun x => hr x _) (fun x => hp x _)
    (fun x => hk x _) (fun x => hq x _)]

/-- Exact full-corpus decision equality, including ordered prechecks, phase scans,
every per-record admission, and the first refusal. No hypothesis constrains metadata,
producer JSON, rule order, phase completeness, or validity of the supplied records. -/
theorem qualifyCorpus_records (fields : List (String × Json))
    (inputs : Array (List (String × Json) × Json)) :
    qualifyCorpus (corpus fields (inputs.map fun (metadata, result) => record metadata (resultView result))) =
    qualifyCorpus (corpus fields (inputs.map fun (metadata, result) => record metadata result)) := by
  apply qualifyCorpus_congr
  · intro item checker
    exact congrArg (fun x => x.bind Json.getStr?)
      (recordRel_set _ _ (record_wf _ _) (record_wf _ _) (record_rel _ _ _)
        "checkerSources" checker "rule" (by decide))
  · intro item checker
    exact congrArg (fun x => x.bind Json.getStr?)
      (recordRel_set _ _ (record_wf _ _) (record_wf _ _) (record_rel _ _ _)
        "checkerSources" checker "phase" (by decide))
  · intro item checker
    exact congrArg (fun x => x.bind Json.getStr?)
      (recordRel_set _ _ (record_wf _ _) (record_wf _ _) (record_rel _ _ _)
        "checkerSources" checker "kind" (by decide))
  · intro item checker
    exact qualify_record_checkerSources item.1 item.2 checker

end Regula.Checker.RuleExampleProjection
