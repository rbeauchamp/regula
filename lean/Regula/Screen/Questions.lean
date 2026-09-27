import Lean.Data.Json
import RegulaPolicy.Screening

/-! # Intent screen questions and state

The exact questions and state of an intent screen. Each question is narrow and states its
yes/no or option meanings in its criteria; every question text is recorded as evidence.

The state holds only what a judgment needs: the intent clauses, and, by `StateMode`, the
elaborated Lean statement and the §5.2 English explanation. The declaration's name is never
sent, because a name can announce the answer. The calibration protocol in
`docs/guides/intent-screening.md` measured which state mode to use by default. -/

namespace Regula.Screen.Questions

open Lean
open RegulaPolicy.Screening

/-- Which description of the formal claim the model sees. -/
inductive StateMode where
  /-- The elaborated Lean statement and the English explanation. -/
  | full
  /-- The elaborated Lean statement only. -/
  | statement
  /-- The English explanation only. -/
  | explanation
  deriving Repr, DecidableEq, Inhabited

/-- The mode's name in the configuration's `state` field and in reports. -/
def StateMode.spelling : StateMode → String
  | .full => "full" | .statement => "statement" | .explanation => "explanation"

/-- The mode `spelling` names; `none` for any other text. -/
def StateMode.parse? : String → Option StateMode
  | "full" => some .full | "statement" => some .statement | "explanation" => some .explanation
  | _ => none

/-- One claim as the screen reads it. `clauses` have any discharge marker removed. -/
structure ClaimText where
  /-- The Intent section's clauses, in order. -/
  clauses : List String
  /-- The docstring's English explanation: its text before the Intent section. -/
  explanation : String
  /-- The claim's elaborated Lean statement, pretty-printed by `Regula.Screen.statementText`. -/
  statement : String

/-- The request state for `mode`: the intent clauses, with the statement, the explanation or
both. -/
def state (mode : StateMode) (c : ClaimText) : Json :=
  let intent := ("intent", toJson c.clauses)
  match mode with
  | .full =>
      Json.mkObj [intent, ("statement", .str c.statement), ("explanation", .str c.explanation)]
  | .statement => Json.mkObj [intent, ("statement", .str c.statement)]
  | .explanation => Json.mkObj [intent, ("explanation", .str c.explanation)]

/-- How a question refers to the formal claim in each state mode. -/
def claimReference : StateMode → String
  | .full => "The formal claim is the Lean proposition `statement`; `explanation` describes it in \
    English. Where they differ, the Lean proposition is the claim."
  | .statement => "The formal claim is the Lean proposition `statement`."
  | .explanation => "The formal claim is described in English by `explanation`."

/-- The intent is the requirement the claim must meet. -/
def intentReference : String :=
  "`intent` lists the requirement clauses the formal claim is meant to establish."

/-- A Noul (true/false) question with `instructions`, answered true when `yes` describes the
case and false when `no` does. -/
def noul (instructions : Json) (yes no : String) : Json :=
  Json.mkObj [("type", "noul"), ("instructions", instructions),
    ("criteria", Json.mkObj [("true", .str yes), ("false", .str no)])]

/-- Per-clause coverage: does the claim guarantee this clause? -/
def coverage (mode : StateMode) (clause : String) : Json :=
  noul (Json.mkObj [("claim", .str (claimReference mode)), ("clause", .str clause),
      ("intent", .str "`clause` is one clause of `intent`; read it in the context of the other \
        clauses, so a word such as \"this\" refers to what they say."),
      ("question", "Taken exactly as stated, does the formal claim guarantee `clause`? It does \
        when every case the clause requires is a case the claim establishes.")])
    "The claim, exactly as stated, implies the clause, in every case the clause requires."
    "Some case the clause requires is not established by the claim: for example a missing \
      conclusion, an extra hypothesis, a looser bound, a changed quantifier order, or a case the \
      clause excludes being asserted anyway."

/-- Strength of the whole claim against the whole intent. -/
def strength (mode : StateMode) : Json :=
  Json.mkObj [("type", "choice"),
    ("instructions", Json.mkObj
        [("claim", .str (claimReference mode)), ("intent", .str intentReference),
      ("question", "Compare what the formal claim establishes with everything `intent` requires, \
        taken together.")]),
    ("criteria", Json.mkObj [
      ("equivalent", "The claim establishes exactly what the intent requires: nothing required is \
        missing and nothing beyond it is asserted."),
      ("stronger", "The claim establishes everything the intent requires and more, for example \
        with fewer hypotheses, a tighter bound or an extra conclusion, without asserting anything \
        the intent excludes."),
      ("weaker", "The claim establishes less than the intent requires, for example a missing \
        requirement, an added hypothesis or a looser bound, and asserts nothing the intent \
        excludes."),
      ("incomparable", "The claim misses something the intent requires and also asserts something \
        the intent does not require or excludes, or it is about a different property.")])]

/-- Targeted check: quantifier order and dependence. -/
def quantifierOrder (mode : StateMode) : Json :=
  noul (Json.mkObj [("claim", .str (claimReference mode)), ("intent", .str intentReference),
      ("question", "Does the formal claim keep the quantifier structure `intent` requires: which \
        values are universal (for all) and which are shown to exist (there exists), in the same \
        order, so each existing value depends on the same things? Answer yes when they agree or \
        when the intent involves no such structure.")])
    "The quantifier order and dependence agree with the intent, or none is at stake."
    "A quantifier is swapped, reordered or changed, so a value that must exist depends on \
      different things, or a universal requirement became existential, or the reverse."

/-- Targeted check: meaning changed by a totalized partial operation. -/
def totalization (mode : StateMode) : Json :=
  noul (Json.mkObj [("claim", .str (claimReference mode)), ("intent", .str intentReference),
      ("question", "Does the formal claim avoid depending on a conventional value of a partial \
        operation in a case that `intent` treats as undefined or excluded, such as division by \
        zero giving 0, natural-number subtraction stopping at 0, or a default value for an empty \
        list or a missing element?")])
    "No such dependence: in every case the claim covers, each operation has its intended meaning, \
      or the intent explicitly accepts the conventional value."
    "The claim covers a case the intent treats as undefined or excluded, and there it holds or \
      says something only because of a conventional value."

/-- Targeted check: stated exclusions and limits. -/
def exclusions (mode : StateMode) : Json :=
  noul (Json.mkObj [("claim", .str (claimReference mode)), ("intent", .str intentReference),
      ("question", "Does the formal claim honor every exclusion and limit that `intent` states, \
        such as cases the claim must not cover, restrictions on its inputs, or things it must not \
        assert? Answer yes when the intent states none.")])
    "Every exclusion or limit the intent states is respected, or the intent states none."
    "The claim covers or asserts something the intent explicitly excludes, or ignores a limit the \
      intent states."

/-- Correspondence of a discharged clause's formal statement to its English text. Its state
is only the clause pair, not the claim. -/
def correspondenceState (clause formal : String) : Json :=
  Json.mkObj [("clause", .str clause), ("formal_clause", .str formal)]

/-- The correspondence question, asked of a `correspondenceState`: does the formal clause state
exactly the English clause? -/
def correspondence : Json :=
  noul
      (Json.mkObj
          [("question", "Does the Lean proposition `formal_clause` state exactly the requirement \
            in `clause`, with the same quantifiers, hypotheses, cases and conclusion?")])
    "The Lean proposition says exactly what the English clause requires, no more and no less."
    "The Lean proposition differs from the English clause: a missing or extra hypothesis, a \
      different conclusion or bound, a different quantifier order, or a case the clause excludes."

/-- Question ids of one claim request, in order: one coverage question per clause not formally
discharged (keeping the clause index), then the
strength Choice and the three targeted checks. Ids are sent as the request's question keys;
they carry no claim or declaration information. -/
def claimQuestions (mode : StateMode) (c : ClaimText) (discharged : Nat → Bool := fun _ => false) :
    List (String × Json) :=
  (c.clauses.zipIdx.filterMap fun (clause, i) =>
    if discharged i then none else some (s!"coverage_{i}", coverage mode clause)) ++
    [("strength", strength mode), ("quantifier_order", quantifierOrder mode),
      ("totalization", totalization mode), ("exclusions", exclusions mode)]

/-- The judgment of each non-coverage question id. -/
def targetedJudgments : List (String × Judgment) :=
  [("quantifier_order", .quantifierOrder), ("totalization", .totalization),
      ("exclusions", .exclusions)]

/-- The recorded question text: the instructions and criteria as compact JSON. -/
def questionText (q : Json) : String := q.compress

end Regula.Screen.Questions
