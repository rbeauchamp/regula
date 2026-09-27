module

public import RegulaCore.Rule

/-! # Agent-first finding text

Every finding a Regula run prints is rendered here from the rule registry (`descriptor`), so
the checker needs no website or other tool to say how to comply. A finding's text states what
is wrong and where (`messageLine`), the rule's one-line remedy, and the rule's page and offline
`lake exe regula explain` command as pointers. The first time a rule fires in a run its finding
also carries the requirement, the rationale, the common compliant rewrites and a minimal
compliant example (or, where the checked files are qualification inputs, the correction
they demonstrate). Later findings of the same rule carry their own message and remedy and
point back to that first finding by rule ID, so a run with hundreds of findings prints each
rule's guidance once.

## Main declarations

- `standalone`, `firstText`, `laterText`: the three text forms of one finding. `standalone`
  is `Regula.Diagnostic.text` (editor messages and the JSON `text` field); `firstText`
  extends it (`firstText_extends`).
- `Entry`, `Entry.cmp`, `sortEntries`: the total order of a run's findings (project scope,
  then modules, then source files by position, then rule and message).
- `sortEntries_perm`, `sortEntries_sorted`, `sortEntries_eq_of_perm`: every finding is
  reported exactly once, in that order, and the order does not depend on detection order.
- `tagFirst`, `render`, `step`: a run's text, with guidance on exactly the findings whose rule
  no earlier finding has (`tagFirst_append`). `step` is the streaming form the checker's
  emitter executes (`renderFrom_cons`).
- `mem_firsts`, `firsts_nodup`, `firsts_length_le`: the rules that receive guidance are
  exactly the rules that fired, each once, so a run prints at most one guidance block per
  registered rule whatever its number of findings.

## Boundaries

These are properties of the rendered text as a function of the findings a run supplies. That
the checker supplies every finding it established, and that the process writes these lines to
its output, are properties of the operational checker (`Regula.Checker.RunFeedback`), not of
these definitions. The text's adequacy as guidance is review of the registry prose.
-/

@[expose] public section

namespace Regula.Feedback

/-- The offline command that prints the full rule. -/
def explainCommand (id : RuleId) : String := "lake exe regula explain " ++ id.spelling

/-- The one-line remedy of a finding of `id`. -/
def fixLine (id : RuleId) : String := "  fix: " ++ (descriptor id).remedy

/-- Pointers to the full rule: the rule page for humans and the offline command. -/
def ruleLine (id : RuleId) : String :=
  "  rule: " ++ helpUrl id ++ " (offline: " ++ explainCommand id ++ ")"

/-- The lines of `text`, without the empty line after a final line break. -/
def textLines (text : String) : List String :=
  let ls := text.splitOn "\n"
  if ls.getLast? == some "" then ls.dropLast else ls

/-- `text` with `pre` before every line, so the block has no empty line: tools that treat an
empty line as the end of a finding never split one. -/
def indented (pre text : String) : String :=
  "\n".intercalate ((textLines text).map (pre ++ ·))

/-- The rule's compliant example when an adopter can apply it as shown, otherwise the
correction it demonstrates (`ExamplePair.adopterExample`). -/
def compliantForm (id : RuleId) : String :=
  let e := (descriptor id).examples
  match e.adopterExample with
  | some text => "  compliant example (" ++ e.compliantPath id ++ "):\n" ++ indented "    " text
  | none => "  compliant form: " ++ e.correction

/-- The rule's guidance, printed once per run under its first finding. -/
def guidance (id : RuleId) : String :=
  let d := descriptor id
  "  requirement: " ++ d.requirement ++ "\n" ++
  "  why: " ++ d.rationale ++ "\n" ++
  "  common rewrites:\n" ++ String.join (d.rewrites.map fun r => "  - " ++ r ++ "\n") ++
  compliantForm id

/-- A finding's complete text on its own: what and where, the remedy, and the pointers.
`message` is the finding's `messageLine`. -/
def standalone (id : RuleId) (message : String) : String :=
  message ++ "\n" ++ fixLine id ++ "\n" ++ ruleLine id

/-- The text of the first finding of `id` in a run: the standalone text and the guidance. -/
def firstText (id : RuleId) (message : String) : String :=
  standalone id message ++ "\n" ++ guidance id

/-- The text of a later finding of `id` in the same run. -/
def laterText (id : RuleId) (message : String) : String :=
  message ++ "\n" ++ fixLine id ++ " (full guidance: first " ++ id.spelling ++ " finding above)"

/-- The first finding's text begins with its standalone text, so a consumer matching the
standalone text also matches the first finding. -/
theorem firstText_extends (id : RuleId) (message : String) :
    firstText id message = standalone id message ++ "\n" ++ guidance id := rfl

/-- Where a finding is, for ordering: a project or configuration scope, a module without a
source range, or a byte offset in a source file. -/
inductive Place where
  | project (identity : String)
  | module (name : String)
  | source (uri : String) (start : Nat)
  deriving DecidableEq

/-- Project findings first, then module findings, then source findings. -/
def Place.rank : Place → Nat
  | .project _ => 0 | .module _ => 1 | .source .. => 2

def Place.name : Place → String
  | .project s => s | .module n => n | .source u _ => u

def Place.start : Place → Nat
  | .source _ s => s | _ => 0

/-- A place is determined by its rank, name and start. -/
theorem Place.ext_key {p q : Place} (hr : p.rank = q.rank) (hn : p.name = q.name)
    (hs : p.start = q.start) : p = q := by
  cases p <;> cases q <;> simp_all [Place.rank, Place.name, Place.start]

/-- One finding of a run: its rule, its place and its `messageLine`. -/
structure Entry where
  rule : RuleId
  place : Place
  message : String
  deriving DecidableEq

/-- The run order: by place (rank, name, start), then rule ID, then message. -/
def Entry.cmp : Entry → Entry → Ordering :=
  compareLex (compareOn fun e : Entry => e.place.rank) <|
  compareLex (compareOn fun e : Entry => e.place.name) <|
  compareLex (compareOn fun e : Entry => e.place.start) <|
  compareLex (compareOn fun e : Entry => e.rule.spelling) (compareOn fun e : Entry => e.message)

instance : Std.TransCmp Entry.cmp := by
  unfold Entry.cmp; infer_instance

/-- `a` may precede `b` in a run. -/
def Entry.le (a b : Entry) : Bool := (Entry.cmp a b).isLE

/-- Equal in the run order means equal. -/
theorem Entry.eq_of_cmp {a b : Entry} (h : Entry.cmp a b = .eq) : a = b := by
  simp only [Entry.cmp, compareLex_eq_eq, compareOn, Std.LawfulEqCmp.compare_eq_iff_eq] at h
  obtain ⟨hr, hn, hs, hid, hm⟩ := h
  cases a; cases b
  simp only at hr hn hs hid hm
  rw [Place.ext_key hr hn hs, RuleId.spelling_injective hid, hm]

theorem Entry.le_trans (a b c : Entry) (hab : Entry.le a b) (hbc : Entry.le b c) :
    Entry.le a c :=
  Std.TransCmp.isLE_trans hab hbc

theorem Entry.le_total (a b : Entry) : Entry.le a b || Entry.le b a := by
  unfold Entry.le
  rw [Std.OrientedCmp.eq_swap (cmp := Entry.cmp) (a := b) (b := a)]
  cases Entry.cmp a b <;> rfl

/-- A run's findings in run order. -/
def sortEntries (l : List Entry) : List Entry := l.mergeSort Entry.le

/-- Every finding appears exactly as often as it was supplied: none is dropped or repeated. -/
theorem sortEntries_perm (l : List Entry) : List.Perm (sortEntries l) l := List.mergeSort_perm l _

/-- The findings are in run order. -/
theorem sortEntries_sorted (l : List Entry) :
    (sortEntries l).Pairwise (fun a b => Entry.le a b = true) :=
  List.pairwise_mergeSort Entry.le_trans Entry.le_total l

/-- The printed order is a function of the supplied findings alone, not of the order in
which the checker detected them. -/
theorem sortEntries_eq_of_perm {l₁ l₂ : List Entry} (h : List.Perm l₁ l₂) :
    sortEntries l₁ = sortEntries l₂ := by
  apply List.Perm.eq_of_pairwise (le := fun a b => Entry.le a b = true)
  · intro a b _ _ hab hba
    exact Entry.eq_of_cmp (Std.OrientedCmp.isLE_antisymm hab hba)
  · exact sortEntries_sorted l₁
  · exact sortEntries_sorted l₂
  · exact (sortEntries_perm l₁).trans (h.trans (sortEntries_perm l₂).symm)

/-- Mark each finding: `true` when no earlier finding (nor a rule in `seen`) has its rule. -/
def tagFirst : List RuleId → List Entry → List (Entry × Bool)
  | _, [] => []
  | seen, e :: es => (e, !seen.contains e.rule) :: tagFirst (e.rule :: seen) es

/-- The text of one marked finding. -/
def lineOf : Entry × Bool → String
  | (e, true) => firstText e.rule e.message
  | (e, false) => laterText e.rule e.message

/-- One streaming step: the text of `e` after the rules in `seen` were explained, and the
rules explained afterwards. -/
def step (seen : List RuleId) (e : Entry) : String × List RuleId :=
  (lineOf (e, !seen.contains e.rule), e.rule :: seen)

/-- The texts of `l` after the rules in `seen` were explained. -/
def renderFrom (seen : List RuleId) (l : List Entry) : List String :=
  (tagFirst seen l).map lineOf

/-- A run's complete text: every finding, in run order, with each rule's guidance once. -/
def render (l : List Entry) : List String := renderFrom [] (sortEntries l)

/-- Emitting findings one `step` at a time produces exactly `renderFrom`. -/
theorem renderFrom_cons (seen : List RuleId) (e : Entry) (es : List Entry) :
    renderFrom seen (e :: es) = (step seen e).1 :: renderFrom (step seen e).2 es := rfl

theorem contains_eq (l : List RuleId) (r : RuleId) : l.contains r = decide (r ∈ l) := by
  rw [Bool.eq_iff_iff]; simp

/-- Marking keeps every finding, in order. -/
theorem tagFirst_fst (seen : List RuleId) (l : List Entry) :
    (tagFirst seen l).map Prod.fst = l := by
  induction l generalizing seen with
  | nil => rfl
  | cons e es ih => simp [tagFirst, ih]

/-- One line per finding. -/
theorem render_length (l : List Entry) : (render l).length = l.length := by
  rw [render, renderFrom, List.length_map, ← List.length_map (f := Prod.fst), tagFirst_fst,
    (sortEntries_perm l).length_eq]

/-- Marking after a prefix `a` continues from the rules `a` introduced: the mark of a finding
depends exactly on whether `seen` or an earlier finding has its rule. -/
theorem tagFirst_append (seen : List RuleId) (a b : List Entry) :
    tagFirst seen (a ++ b) = tagFirst seen a ++ tagFirst ((a.map Entry.rule).reverse ++ seen) b := by
  induction a generalizing seen with
  | nil => rfl
  | cons e es ih => simp [tagFirst, ih]

/-- A finding is marked for guidance exactly when no earlier finding in the run has its rule;
otherwise an earlier finding of the same rule exists for the back-reference. -/
theorem tag_of_prefix (a b : List Entry) (e : Entry) :
    tagFirst [] (a ++ e :: b) =
      tagFirst [] a ++ (e, decide (e.rule ∉ a.map Entry.rule)) ::
        tagFirst (e.rule :: ((a.map Entry.rule).reverse)) b := by
  rw [tagFirst_append]
  simp [tagFirst, ← decide_not]

/-- The rules marked for guidance, in order. -/
def firstsFrom (seen : List RuleId) (l : List Entry) : List RuleId :=
  ((tagFirst seen l).filter (·.2)).map (·.1.rule)

/-- The rules that receive guidance in a run of `l`. -/
def firsts (l : List Entry) : List RuleId := firstsFrom [] (sortEntries l)

theorem firstsFrom_cons (seen : List RuleId) (e : Entry) (es : List Entry) :
    firstsFrom seen (e :: es) =
      (if e.rule ∈ seen then [] else [e.rule]) ++ firstsFrom (e.rule :: seen) es := by
  by_cases h : e.rule ∈ seen <;> simp [firstsFrom, tagFirst, h]

theorem mem_firstsFrom (seen : List RuleId) (l : List Entry) (r : RuleId) :
    r ∈ firstsFrom seen l ↔ r ∉ seen ∧ r ∈ l.map Entry.rule := by
  induction l generalizing seen with
  | nil => simp [firstsFrom, tagFirst]
  | cons e es ih =>
    rw [firstsFrom_cons, List.mem_append, ih]
    by_cases hs : e.rule ∈ seen <;> by_cases he : r = e.rule <;> simp_all

theorem firstsFrom_nodup (seen : List RuleId) (l : List Entry) : (firstsFrom seen l).Nodup := by
  induction l generalizing seen with
  | nil => simp [firstsFrom, tagFirst]
  | cons e es ih =>
    rw [firstsFrom_cons]
    by_cases hs : e.rule ∈ seen
    · simpa [hs] using ih (e.rule :: seen)
    · simp only [hs, ↓reduceIte, List.singleton_append, List.nodup_cons]
      exact ⟨fun h => ((mem_firstsFrom _ _ _).mp h).1 List.mem_cons_self, ih _⟩

/-- Every rule that fired receives guidance, and no other rule does. -/
theorem mem_firsts (l : List Entry) (r : RuleId) : r ∈ firsts l ↔ r ∈ l.map Entry.rule := by
  rw [firsts, mem_firstsFrom]
  simp only [List.not_mem_nil, not_false_eq_true, true_and, List.mem_map]
  exact exists_congr fun e => and_congr_left' (sortEntries_perm l).mem_iff

/-- Each rule receives guidance at most once in a run. -/
theorem firsts_nodup (l : List Entry) : (firsts l).Nodup := firstsFrom_nodup [] _

/-- A run prints at most one guidance block per registered rule, however many findings it has. -/
theorem firsts_length_le (l : List Entry) : (firsts l).length ≤ RuleId.all.length :=
  List.Nodup.length_le_of_subset (firsts_nodup l) (fun r _ => RuleId.mem_all r)

end Regula.Feedback
