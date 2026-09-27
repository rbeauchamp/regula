import Regula.Screen.Claim
import Regula.Screen.Corpus

/-! # Intent screen calibration

The calibration measurement of `docs/guides/intent-screening.md`: run the labelled corpus
through the same questions the screen asks and report, per judgment, false-negative and
false-positive rates at fixed thresholds and the threshold-free ranking accuracy (AUC).

A *defect* is a labelled failure in the judged respect (an uncovered clause; a weaker or
incomparable claim; a failed targeted check; a formal clause that does not state its English
clause). A false negative is a defect whose support probability is at or above the threshold
(no finding); a false positive is a non-defect whose support is below it. These are sampled
observations about this corpus and this pinned model, not guarantees about other claims. -/

namespace Regula.Screen.Calibrate

open Lean
open RegulaPolicy.Screening
open Regula.Screen.Corpus
open Questions

/-- Whether the explanation describes the item's own statement or its base's. -/
inductive Variant where
  /-- The item's own explanation, which describes its own statement. -/
  | faithful
  /-- The base item's explanation paired with a mutant's statement, so the mutation shows
  only in the Lean statement. -/
  | stale
  deriving Repr, DecidableEq

/-- The variant's name in the report and evidence rows: `faithful` or `stale`. -/
def Variant.spelling : Variant → String
  | .faithful => "faithful" | .stale => "stale"

/-- One labelled judged answer. -/
structure Row where
  /-- The corpus item judged; for a correspondence row, the formal definition. -/
  item : Name
  /-- The item's mutation kind; `formalCorrect` or `formalWrong` for a correspondence row. -/
  mutation : Mutation
  /-- The corpus split the item belongs to. -/
  split : Split
  /-- The state mode the question was asked under. -/
  mode : StateMode
  /-- Whether the explanation sent was the item's own or its base's. -/
  variant : Variant
  /-- The judgment this answer is for. -/
  judgment : Judgment
  /-- What was judged: `clause i` for coverage, `claim` for the claim-level judgments, or the
  English clause for a correspondence row. -/
  subject : String
  /-- Whether the corpus labels this subject a defect in the judged respect. -/
  defect : Bool
  /-- The model's support probability; a value below the threshold is a finding. -/
  support : Decimal
  /-- The digest of the request that produced the answer (its cache key). -/
  digest : String
  /-- For strength: the most probable option and the labelled option. -/
  strength? : Option (String × Strength) := none

/-- The strength option's name, as the question offers it and the evidence rows record it. -/
def Strength.spelling : Strength → String
  | .equivalent => "equivalent" | .stronger => "stronger" | .weaker => "weaker"
  | .incomparable => "incomparable"

/-- A strength label is a defect when the claim is weaker than the intent or incomparable
with it. -/
def isDefectStrength : Strength → Bool
  | .weaker | .incomparable => true
  | .equivalent | .stronger => false

private def argmax (ps : List (String × Probability)) : String :=
  (ps.foldl (fun (best : Option (String × Decimal)) (o, p) => match best with
    | some (_, b) => if b < p.val then some (o, p.val) else best
    | none => some (o, p.val)) none).map (·.1) |>.getD ""

/-- Judge one item under one state mode and explanation variant. -/
def judgeItem (cache : System.FilePath) (model : PinnedModel) (item : Item) (text : ClaimText)
    (mode : StateMode) (variant : Variant) (limit : Nat) : StateT Usage IO (List Row) := do
  let questions := claimQuestions mode text
  let r ← Jev.ask cache model (state mode text) questions limit
  modify (·.add r)
  let row (judgment : Judgment) (subject : String) (defect : Bool) (support : Decimal) : Row :=
    { item := item.name, mutation := item.mutation, split := item.split, mode, variant, judgment,
      subject, defect, support, digest := r.digest }
  let mut rows := #[]
  for i in [0:text.clauses.length] do
    let p ← noulOf r s!"coverage_{i}"
    rows := rows.push (row .coverage s!"clause {i}" (item.uncovered.contains i) p.val)
  let (support, _) ← strengthOf r
  let chosen := match r.answers.lookup "strength" with
    | some (.choice ps _) => argmax ps
    | _ => ""
  rows := rows.push { row .strength "claim" (isDefectStrength item.strength) support with
    strength? := some (chosen, item.strength) }
  for (id, judgment, label) in [("quantifier_order", Judgment.quantifierOrder, item.quantifierOrder),
      ("totalization", .totalization, item.totalization), ("exclusions", .exclusions, item.exclusions)] do
    let p ← noulOf r id
    rows := rows.push (row judgment "claim" (!label) p.val)
  return rows.toList

/-- Rates at one threshold: false negatives among defects, false positives among the rest. -/
structure Rates where
  /-- How many rows are labelled defects. -/
  defects : Nat
  /-- How many rows are not labelled defects. -/
  clean : Nat
  /-- Defect rows whose support is at or above the threshold, so no finding is raised. -/
  falseNegatives : Nat
  /-- Clean rows whose support is below the threshold, so a finding is raised. -/
  falsePositives : Nat

/-- The counts of `Rates` for `rows` at `threshold`. -/
def rates (rows : List Row) (threshold : Decimal) : Rates :=
  let defects := rows.filter (·.defect)
  let clean := rows.filter (!·.defect)
  { defects := defects.length, clean := clean.length
    falseNegatives := (defects.filter fun r => decide (threshold ≤ r.support)).length
    falsePositives := (clean.filter fun r => decide (r.support < threshold)).length }

/-- Twice the Mann–Whitney count: pairs (defect, clean) where the defect has lower support
count 2, ties count 1. AUC is this over `2 * defects * clean`. -/
def aucTwice (rows : List Row) : Nat × Nat :=
  let defects := rows.filter (·.defect)
  let clean := rows.filter (!·.defect)
  let pairs := defects.foldl (fun acc d => clean.foldl (fun acc c =>
    acc + (if d.support < c.support then 2 else if c.support < d.support then 0 else 1)) acc) 0
  (pairs, 2 * defects.length * clean.length)

/-- `k/n` followed by `k / n` rounded to three decimals, as in `3/8 (0.375)`; `n/a`
when `n` is 0. -/
def ratio (k n : Nat) : String :=
  if n = 0 then "n/a" else
    let permille := (k * 1000 + n / 2) / n
    s!"{k}/{n} ({permille / 1000}.{"".pushn '0' (3 - (toString (permille % 1000)).length)}{permille % 1000})"

/-- The thresholds the report tabulates, with their labels: 0.2, 0.5 and 0.6. -/
def thresholds : List (String × Decimal) := [("0.2", ⟨2, 1⟩), ("0.5", ⟨5, 1⟩), ("0.6", ⟨6, 1⟩)]

/-- AUC in thousandths, rounded; `none` without both defects and clean rows. -/
def aucPermille (rows : List Row) : Option Nat :=
  let (pairs, total) := aucTwice rows
  if total = 0 then none else some ((pairs * 1000 + total / 2) / total)

/-- The pre-registered criteria for one group (`docs/guides/intent-screening.md`):
C3 at least 5 defects and 10 clean rows; C1 at warning threshold 0.5, FNR ≤ 0.25 and
FPR ≤ 0.15; C2 at error threshold 0.2, FPR ≤ 0.05. -/
def meetsCriteria (rows : List Row) : Bool × String :=
  let w := rates rows ⟨5, 1⟩
  let e := rates rows ⟨2, 1⟩
  let c3 := decide (5 ≤ w.defects) && decide (10 ≤ w.clean)
  let c1 := decide (w.falseNegatives * 4 ≤ w.defects) && decide (w.falsePositives * 100 ≤ 15 * w.clean)
  let c2 := decide (e.falsePositives * 20 ≤ e.clean)
  (c1 && c2 && c3, s!"C1 {if c1 then "pass" else "fail"}, C2 {if c2 then "pass" else "fail"}, " ++
    s!"C3 {if c3 then "pass" else "fail"}")

/-- One markdown table row for a group of rows. -/
def tableRow (label : String) (rows : List Row) : String :=
  let (auc, total) := aucTwice rows
  let cells := thresholds.map fun (_, t) =>
    let r := rates rows t
    s!"{ratio r.falseNegatives r.defects} | {ratio r.falsePositives r.clean}"
  s!"| {label} | {rows.filter (·.defect) |>.length} / {rows.filter (!·.defect) |>.length} | " ++
    " | ".intercalate cells ++ s!" | {ratio auc total} |"

/-- The Markdown header and separator rows of a rates table: false-negative and false-positive
rates at each threshold, then AUC. -/
def tableHeader : String :=
  "| group | defects / clean | FNR@0.2 | FPR@0.2 | FNR@0.5 | FPR@0.5 | FNR@0.6 | FPR@0.6 | AUC |\n" ++
  "| --- | --- | --- | --- | --- | --- | --- | --- | --- |"

/-- A row as one evidence record: its labels, the rendered support probability, the request
digest and, for a strength row, the most probable option and the labelled one. -/
def rowJson (r : Row) : Json :=
  Json.mkObj ([("item", .str r.item.toString), ("mutation", .str r.mutation.spelling),
    ("split", .str (if r.split == .dev then "dev" else "test")), ("state", .str r.mode.spelling),
    ("explanation", .str r.variant.spelling), ("judgment", .str r.judgment.spelling),
    ("subject", .str r.subject), ("defect", .bool r.defect), ("probability", .str r.support.render),
    ("inputsDigest", .str r.digest)] ++
    match r.strength? with
    | some (chosen, label) => [("chosen", .str chosen), ("label", .str (Strength.spelling label))]
    | none => [])

/-- The pre-registered budget of requests sent in one calibration run. -/
def requestBudget : Nat := 300

/-- Refuse before a request once the budget is spent; otherwise the POSTs the next request may
send (retries included), so no run sends more than the budget. -/
def checkBudget (usage : Usage) : IO Nat := do
  if usage.requests ≥ requestBudget then
    throw <| IO.userError s!"calibration budget reached: {requestBudget} requests sent"
  return requestBudget - usage.requests

/-- Run the corpus of one split and write the report and the evidence rows. -/
def run (cache : System.FilePath) (model : PinnedModel) (split : Split) (env : Environment)
    (report records : System.FilePath) : IO Unit := do
  let selected := items.filter (·.split == split)
  let mut texts : Std.HashMap Name ClaimText := {}
  for item in items do
    let input ← runMeta env (readClaim item.name)
    texts := texts.insert item.name input.text
  let mut rows : Array Row := #[]
  let mut usage : Usage := {}
  for item in selected do
    let some own := texts.get? item.name | throw <| IO.userError "unread item"
    let some base := texts.get? item.base | throw <| IO.userError "unread base"
    unless own.clauses == base.clauses do
      throw <| IO.userError s!"{item.name} does not share its base's Intent clauses"
    let mutant := item.mutation != .base && item.mutation != .rewrite
    let variants := if mutant then [Variant.faithful, .stale] else [.faithful]
    for mode in [StateMode.full, .statement, .explanation] do
      for variant in variants do
        if mode == .statement && variant == .stale then continue
        let text := if variant == .stale then { own with explanation := base.explanation } else own
        let limit ← checkBudget usage
        let (rs, u) ← (judgeItem cache model item text mode variant limit).run usage
        rows := rows ++ rs.toArray
        usage := u
  let mut correspondenceRows : Array Row := #[]
  if split == .test then
    for c in correspondenceItems do
      let formal ← runMeta env do
        let some info := (← getEnv).find? c.formal | throwError "unknown {c.formal}"
        pretty (statementExpr info)
      let limit ← checkBudget usage
      let q := [("correspondence", Questions.correspondence)]
      let r ← Jev.ask cache model (correspondenceState c.clause formal) q limit
      usage := usage.add r
      let p ← noulOf r "correspondence"
      correspondenceRows := correspondenceRows.push
        { item := c.formal, mutation := if c.label then .formalCorrect else .formalWrong, split := .test,
          mode := .statement, variant := .faithful, judgment := .correspondence, subject := c.clause,
          defect := !c.label, support := p.val, digest := r.digest }
  let all := rows ++ correspondenceRows
  IO.FS.writeFile records (Json.arr (all.map rowJson)).pretty
  let group (j : Judgment) (m : StateMode) (v : Option Variant) :=
    rows.toList.filter fun r => r.judgment == j && r.mode == m && (v.all (r.variant == ·) || r.mutation == .base || r.mutation == .rewrite)
  let mut lines : Array String := #[s!"Model `{model.val}`, split `{if split == .dev then "dev" else "test"}`: " ++
    s!"{usage.requests} requests sent, {usage.cached} answered from cache, {usage.tokensText} input tokens billed.", ""]
  for j in [Judgment.coverage, .strength, .quantifierOrder, .totalization, .exclusions] do
    lines := lines ++ #[s!"### {j.spelling}", "", tableHeader]
    for m in [StateMode.full, .statement, .explanation] do
      if m == .statement then
        lines := lines.push (tableRow s!"{m.spelling}" (group j m none))
      else
        for v in [Variant.faithful, .stale] do
          lines := lines.push (tableRow s!"{m.spelling}, {v.spelling} explanation" (group j m (some v)))
    lines := lines.push ""
  let strengthRows := rows.toList.filter fun r => r.judgment == .strength && r.mode == .full
  let exact := strengthRows.filter fun r => match r.strength? with
    | some (chosen, label) => chosen == Strength.spelling label
    | none => false
  lines := lines ++ #[s!"Strength exact option agreement (full state, both explanations): {ratio exact.length strengthRows.length}", ""]
  if split == .test then
    lines := lines ++ #["### correspondence", "", tableHeader,
      tableRow "clause pair" correspondenceRows.toList, ""]
  -- Pre-registered decisions, computed from the rows above.
  lines := lines ++ #["### Decisions (pre-registered rules)", ""]
  for j in [Judgment.coverage, .strength, .quantifierOrder, .totalization, .exclusions] do
    let (okF, whyF) := meetsCriteria (group j .full (some .faithful))
    let (okS, whyS) := meetsCriteria (group j .full (some .stale))
    lines := lines.push (s!"- {j.spelling}: {if okF && okS then "calibrated thresholds (error 0.2, warning 0.5)" else "no calibrated thresholds"}" ++
      s!" — full/faithful: {whyF}; full/stale: {whyS}")
  if split == .test then
    let (ok, why) := meetsCriteria correspondenceRows.toList
    lines := lines.push s!"- correspondence: {if ok then "calibrated thresholds (error 0.2, warning 0.5)" else "no calibrated thresholds"} — {why}"
  let mean (gs : List (List Row)) : Nat :=
    let xs := gs.filterMap aucPermille
    if xs.isEmpty then 0 else xs.foldl (· + ·) 0 / xs.length
  let modeScore (m : StateMode) : Nat := mean <| [Judgment.coverage, .strength].flatMap fun j =>
    if m == .statement then [group j m none, group j m none] else [group j m (some .faithful), group j m (some .stale)]
  let scores := [StateMode.full, .statement, .explanation].map fun m => (m, modeScore m)
  let best := scores.foldl (fun (b : StateMode × Nat) s => if b.2 < s.2 then s else b) (.full, modeScore .full)
  lines := lines.push (s!"- default state: `{best.1.spelling}` (mean coverage and strength AUC in thousandths: " ++
    ", ".intercalate (scores.map fun (m, s) => s!"{m.spelling} {s}") ++ "; ties keep full)")
  for j in [Judgment.coverage, .strength] do
    let st := (aucPermille (group j .statement none)).getD 0
    let fs := (aucPermille (group j .full (some .stale))).getD 0
    lines := lines.push (s!"- {j.spelling} reads the Lean statement: {decide (800 ≤ st) && decide (800 ≤ fs)} " ++
      s!"(statement-only AUC {st}, full-state stale-explanation AUC {fs}; rule: both at least 800)")
  lines := lines.push ""
  IO.FS.writeFile report ("\n".intercalate lines.toList)
  IO.println ("\n".intercalate lines.toList)

end Regula.Screen.Calibrate
