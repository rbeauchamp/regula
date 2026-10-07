import RegulaCore.Site
import Regula.Decision

/-! # Rule IDs in prose

Every rule ID that a page mentions in prose is a link to that rule's page. This module defines
what prose is in a rendered HTML page, decides whether a page has a rule ID in prose that is not
such a link, and rewrites generated prose so that it has none.

## Main declarations

- `tokenAt`, `splitTokens`: a rule-ID token is `RG` and four digits with no ASCII letter or digit
  directly before or after it, so emphasis such as `_RG2003_` does not hide one.
- `TokenAt`, `tokenAt_eq_some_iff`, `TokenAt.apart`, `mem_tokenOffsets_iff`: that statement of a
  token as a proposition, with no function of this module, and the theorem that `splitTokens`
  returns the tokens of a text and no others, each at its place.
- `Run`, `Mention`, `Run.mentions`: a run is a maximal piece of prose with the destination of the
  link it lies in, if any; a mention is one token of a run.
- `Mention.Linked`, `Run.Linked`, `Run.mentions_linked_iff`, `bareMentions`,
  `bareMentions_nil_iff`, `checked_bareMentions`: a mention is linked when its token is a
  registered rule ID and its link's destination is that rule's page. A run is linked when each
  rule-ID token of its text (`TokenAt`) is such a token in such a link. The executed check
  returns nothing exactly when every run is linked.
- `pageTarget`, `pageTarget_iff`: the page of a rule for a rendered page of an edition (the rule's
  page file of that edition).
- `htmlRuns`, `ownPage`: the prose of an HTML page, and the one place a rule ID is not written as
  a link, a rule page's own title and top heading.
- `htmlErrors`, `htmlErrors_nil_iff`: the executed page check, reporting the file, the line and the
  ID.
- `relativeCitation`, `rewriteIds`, `linkIds`, `linkVerso`: the link a generated page gives a
  rule, relative to its edition's root (`RuleId.route`), and the rewriting of generated prose that
  inserts it.

## What prose is

In an HTML page, prose is the text outside the `code`, `pre`, `script` and `style` elements
(`exemptElement`). Pasted tool output is a `pre` element; a Lean identifier is code. A rule table
that is the index of rule pages names each rule as a link to its page, so its IDs are linked
mentions. A heading is prose. The one rule ID that is not written as a link is a rule page's own,
in that page's `title` and `h1`, because a page cannot usefully link to itself (`ownPage`): those
two elements are read as text linked to the page they name.

## Boundaries

`bareMentions_nil_iff` is about the runs it is given. `htmlRuns` is a small scanner for the
builder's own output, not an HTML parser. An element, comment or script that is never closed
would hide the text after it, so `htmlErrors` refuses such a page; an element closed and reopened
out of order is not detected. Markdown documents are not read here: `Regula.Markdown`
(`RegulaCore/Markdown.lean`) decides the same question for a tracked Markdown document from a
CommonMark parser's reading of it, with this module's tokens and `Mention.Linked`. `linkIds`
rewrites generated prose outside its code spans, inline links and bare URLs (`scanGenerated`);
that its output has no bare rule ID is established by `htmlErrors` on the rendered pages, not by a
theorem about the rewriting. The Markdown agent briefing (`Regula.Guidance.briefRule`) links its
rule IDs itself (`Regula.Guidance.citation`); the generated agent skill the repository tracks is
checked as a Markdown document.
-/

namespace Regula.Prose

open Regula.Site

/-! ## Rule-ID tokens -/

/-- A character that continues a word: an ASCII letter or digit. `_` is not one, so a rule ID in
`_` emphasis is a token; an identifier that contains a rule ID is written as code. -/
def isWordChar (c : Char) : Bool := c.isAlphanum

/-- The rule-ID token at the head of `text`, when `prev` is the character before it: `RG` and
four digits, with no word character directly before or after. -/
def tokenAt (prev : Option Char) : List Char → Option String
  | 'R' :: 'G' :: a :: b :: c :: d :: rest =>
    if !prev.any isWordChar && a.isDigit && b.isDigit && c.isDigit && d.isDigit &&
        !rest.head?.any isWordChar then
      some (String.ofList ['R', 'G', a, b, c, d])
    else none
  | _ => none

private def textPart (acc : List Char) : List (String ⊕ String) :=
  if acc.isEmpty then [] else [.inl (String.ofList acc.reverse)]

/-- `text` split at its rule-ID tokens, in order: `.inl` the text between tokens and `.inr` each
token. `prev` is the character before `text`, `skip` the number of characters of a token still to
pass, and `acc` the text since the last token, reversed. -/
def splitTokens : Option Char → Nat → List Char → List Char → List (String ⊕ String)
  | _, _, acc, [] => textPart acc
  | _, skip + 1, acc, c :: rest => splitTokens (some c) skip acc rest
  | prev, 0, acc, c :: rest =>
    match tokenAt prev (c :: rest) with
    | some token => textPart acc ++ .inr token :: splitTokens (some c) 5 [] rest
    | none => splitTokens (some c) 0 (c :: acc) rest

/-! ## What a rule-ID token is -/

/-- `chars` is a rule-ID token after the character `prev`, if any, and before the text `after`:
`RG` and four digits, with no ASCII letter or digit directly before or after it. The statement
uses Lean's own `Char.isDigit` and `Char.isAlphanum` and no function of this module. `tokenAt`
decides it (`tokenAt_eq_some_iff`). -/
def TokenAt (prev : Option Char) (chars after : List Char) : Prop :=
  ∃ a b c d, chars = ['R', 'G', a, b, c, d] ∧ a.isDigit = true ∧ b.isDigit = true ∧
    c.isDigit = true ∧ d.isDigit = true ∧ (∀ p, prev = some p → p.isAlphanum = false) ∧
    ∀ n, after.head? = some n → n.isAlphanum = false

/-- `tokenAt` returns a token exactly when the text starts with a rule-ID token, and returns
that token. -/
theorem tokenAt_eq_some_iff (prev : Option Char) (text : List Char) (token : String) :
    tokenAt prev text = some token ↔
      ∃ chars after, text = chars ++ after ∧ token = String.ofList chars ∧
        TokenAt prev chars after := by
  unfold tokenAt
  split
  · rename_i a b c d rest
    constructor
    · intro found
      split at found
      · rename_i holds
        cases found
        simp only [Bool.and_eq_true, Bool.not_eq_true', Option.any_eq_false, isWordChar] at holds
        obtain ⟨⟨⟨⟨⟨hp, ha⟩, hb⟩, hc⟩, hd⟩, hn⟩ := holds
        exact ⟨['R', 'G', a, b, c, d], rest, rfl, rfl, a, b, c, d, rfl, ha, hb, hc, hd,
          fun p hp' => hp p hp', fun n hn' => hn n hn'⟩
      · cases found
    · rintro ⟨chars, after, split, rfl, a', b', c', d', rfl, ha, hb, hc, hd, hp, hn⟩
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at split
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := split
      have hp' : prev.any isWordChar = false := by
        cases prev with
        | none => rfl
        | some p => simpa [isWordChar] using hp p rfl
      have hn' : rest.head?.any isWordChar = false := by
        cases h : rest.head? with
        | none => rfl
        | some n => simpa [isWordChar] using hn n h
      simp [hp', hn', ha, hb, hc, hd]
  · rename_i unmatched
    constructor
    · intro found
      cases found
    · rintro ⟨chars, after, rfl, -, a, b, c, d, rfl, -⟩
      exact absurd rfl (unmatched a b c d after)

theorem tokenAt_length {prev : Option Char} {text : List Char} {token : String}
    (found : tokenAt prev text = some token) : token.length = 6 := by
  obtain ⟨chars, after, -, rfl, a, b, c, d, rfl, -⟩ :=
    (tokenAt_eq_some_iff prev text token).mp found
  rw [String.length_ofList]
  rfl

/-- Two rule-ID tokens of one text do not overlap: a token that starts after the start of an
other token starts after its end. `splitTokens` passes the five characters after the start of a
token for this reason. -/
theorem TokenAt.apart {prev prev' : Option Char} {chars after chars' after' before : List Char}
    {c : Char} (first : TokenAt prev chars after) (second : TokenAt prev' chars' after')
    (same : chars ++ after = c :: before ++ chars' ++ after') : 5 ≤ before.length := by
  obtain ⟨a, b, c₀, d, rfl, ha, hb, hc, hd, -, -⟩ := first
  obtain ⟨a', b', c', d', rfl, -⟩ := second
  match before, same with
  | [], same => simp at same
  | [_], same =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at same
    obtain ⟨-, -, rfl, -⟩ := same
    simp at ha
  | [_, _], same =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at same
    obtain ⟨-, -, -, rfl, -⟩ := same
    simp at hb
  | [_, _, _], same =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at same
    obtain ⟨-, -, -, -, rfl, -⟩ := same
    simp at hc
  | [_, _, _, _], same =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at same
    obtain ⟨-, -, -, -, -, rfl, -⟩ := same
    simp at hd
  | _ :: _ :: _ :: _ :: _ :: _, _ => simp

/-- The tokens of `parts`, in order, each with the number of characters of the parts before it,
counted from `start`. The theorems about `splitTokens` use it; no executed function does. -/
def tokenOffsets (start : Nat) : List (String ⊕ String) → List (Nat × String)
  | [] => []
  | .inl text :: rest => tokenOffsets (start + text.length) rest
  | .inr token :: rest => (start, token) :: tokenOffsets (start + token.length) rest

private theorem tokenOffsets_textPart (start : Nat) (acc : List Char)
    (rest : List (String ⊕ String)) :
    tokenOffsets start (textPart acc ++ rest) = tokenOffsets (start + acc.length) rest := by
  unfold textPart
  split
  · rename_i empty
    simp [List.isEmpty_iff.mp empty]
  · simp [tokenOffsets, String.length_ofList]

/-- The invariant of `splitTokens`: with `pre` the text already read, the tokens it returns are
the rule-ID tokens of `text` that start at or after `skip`, each at its place. -/
private theorem mem_tokenOffsets_splitTokens (text : List Char) :
    ∀ (pre : List Char) (skip : Nat) (acc : List Char) (start o : Nat) (token : String),
      (o, token) ∈ tokenOffsets start (splitTokens pre.getLast? skip acc text) ↔
        ∃ before chars after, text = before ++ chars ++ after ∧ token = String.ofList chars ∧
          TokenAt (pre ++ before).getLast? chars after ∧ skip ≤ before.length ∧
          o + skip = start + acc.length + before.length := by
  induction text with
  | nil =>
    intro pre skip acc start o token
    have none : tokenOffsets start (splitTokens pre.getLast? skip acc []) = [] := by
      have := tokenOffsets_textPart start acc []
      simpa [splitTokens, tokenOffsets] using this
    rw [none]
    constructor
    · intro h
      cases h
    · rintro ⟨before, chars, after, split, -, ⟨a, b, c, d, rfl, -⟩, -⟩
      simp at split
  | cons c rest ih =>
    intro pre skip acc start o token
    have last : some c = (pre ++ [c]).getLast? := by simp
    have step : ∀ (skip' : Nat) (acc' : List Char) (start' : Nat),
        (o, token) ∈ tokenOffsets start' (splitTokens (some c) skip' acc' rest) ↔
          ∃ before chars after, c :: rest = c :: before ++ chars ++ after ∧
            token = String.ofList chars ∧ TokenAt (pre ++ c :: before).getLast? chars after ∧
            skip' ≤ before.length ∧ o + skip' = start' + acc'.length + before.length := by
      intro skip' acc' start'
      rw [last, ih]
      constructor
      · rintro ⟨before, chars, after, rfl, rfl, at', hskip, ho⟩
        exact ⟨before, chars, after, rfl, rfl, by simpa using at', hskip, ho⟩
      · rintro ⟨before, chars, after, split, rfl, at', hskip, ho⟩
        exact ⟨before, chars, after, by simpa using split, rfl, by simpa using at', hskip, ho⟩
    cases skip with
    | succ skip =>
      rw [splitTokens, step]
      constructor
      · rintro ⟨before, chars, after, split, rfl, at', hskip, ho⟩
        exact ⟨c :: before, chars, after, split, rfl, at', by simp; omega, by simp; omega⟩
      · rintro ⟨before, chars, after, split, rfl, at', hskip, ho⟩
        cases before with
        | nil => simp at hskip
        | cons b before =>
          obtain ⟨rfl, -⟩ : b = c ∧ _ := by simpa using split.symm
          exact ⟨before, chars, after, split, rfl, at', by simpa using hskip,
            by simp at ho; omega⟩
    | zero =>
      rw [splitTokens]
      cases found : tokenAt pre.getLast? (c :: rest) with
      | none =>
        simp only []
        rw [step]
        constructor
        · rintro ⟨before, chars, after, split, rfl, at', -, ho⟩
          exact ⟨c :: before, chars, after, split, rfl, at', Nat.zero_le _, by simp at ho ⊢; omega⟩
        · rintro ⟨before, chars, after, split, rfl, at', -, ho⟩
          cases before with
          | nil =>
            have := (tokenAt_eq_some_iff pre.getLast? (c :: rest) (String.ofList chars)).mpr
              ⟨chars, after, by simpa using split, rfl, by simpa using at'⟩
            rw [found] at this
            cases this
          | cons b before =>
            obtain ⟨rfl, -⟩ : b = c ∧ _ := by simpa using split.symm
            exact ⟨before, chars, after, split, rfl, at', Nat.zero_le _, by simp at ho ⊢; omega⟩
      | some token' =>
        simp only [tokenOffsets_textPart, tokenOffsets, List.mem_cons, Prod.mk.injEq]
        rw [step]
        obtain ⟨chars', after', split', rfl, at''⟩ :=
          (tokenAt_eq_some_iff pre.getLast? (c :: rest) token').mp found
        have six : chars'.length = 6 := by
          rw [← String.length_ofList]
          exact tokenAt_length found
        constructor
        · rintro (⟨rfl, rfl⟩ | ⟨before, chars, after, split, rfl, at', hskip, ho⟩)
          · exact ⟨[], chars', after', by simpa using split', rfl, by simpa using at'',
              Nat.zero_le _, by simp⟩
          · exact ⟨c :: before, chars, after, split, rfl, at', Nat.zero_le _,
              by simp at ho ⊢; omega⟩
        · rintro ⟨before, chars, after, split, rfl, at', -, ho⟩
          cases before with
          | nil =>
            left
            have same : chars' ++ after' = chars ++ after := by
              rw [← split']; simpa using split
            obtain ⟨a, b, c₀, d, rfl, -⟩ := at'
            obtain ⟨a', b', c', d', rfl, -⟩ := at''
            simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at same
            obtain ⟨rfl, rfl, rfl, rfl, -⟩ := same
            exact ⟨by simp at ho; omega, rfl⟩
          | cons b before =>
            right
            obtain ⟨rfl, -⟩ : b = c ∧ _ := by simpa using split.symm
            have far : 5 ≤ before.length :=
              TokenAt.apart at'' at' (by rw [← split']; exact split)
            exact ⟨before, chars, after, split, rfl, at', far, by simp at ho ⊢; omega⟩

/-- The tokens that `splitTokens` returns for a text are the rule-ID tokens of that text
(`TokenAt`) and no others, each with the number of characters before it. -/
theorem mem_tokenOffsets_iff (text : List Char) (o : Nat) (token : String) :
    (o, token) ∈ tokenOffsets 0 (splitTokens none 0 [] text) ↔
      ∃ before chars after, text = before ++ chars ++ after ∧ token = String.ofList chars ∧
        TokenAt before.getLast? chars after ∧ o = before.length := by
  have invariant := mem_tokenOffsets_splitTokens text [] 0 [] 0 o token
  simp only [List.getLast?_nil, List.nil_append, Nat.zero_le, true_and, Nat.add_zero,
    List.length_nil, Nat.zero_add] at invariant
  exact invariant

private def newlines (s : String) : Nat := s.toList.count '\n'

/-! ## Mentions and the decision -/

/-- A maximal piece of a document's prose. -/
structure Run where
  /-- The 1-based line on which the run starts. -/
  line : Nat
  /-- The run's text. -/
  text : String
  /-- The destination of the link whose text the run lies in, if any. -/
  link : Option String
  deriving DecidableEq, Repr

/-- One rule-ID token in prose. -/
structure Mention where
  /-- The 1-based line of the token. -/
  line : Nat
  /-- The token, such as `RG1001`. -/
  token : String
  /-- The destination of the link whose text the token lies in, if any. -/
  link : Option String
  deriving DecidableEq, Repr

/-- The rule-ID tokens of a run, in order, each on its own line of the document. -/
def Run.mentions (r : Run) : List Mention :=
  ((splitTokens none 0 [] r.text.toList).foldl (fun (acc : Nat × List Mention) part =>
    match part with
    | .inl text => (acc.1 + newlines text, acc.2)
    | .inr token => (acc.1, ⟨acc.1, token, r.link⟩ :: acc.2)) (r.line, [])).2.reverse

/-- Mention `m` is linked: its token is the spelling of a registered rule ID, and it lies in the
text of a link whose destination `target` accepts as that rule's page. The token is stated with
`RuleId.spelling`, the written form of a rule ID, and not with the parser that the function
calls (`RuleId.parse_spelling`, `RuleId.spelling_of_parse`). -/
def Mention.Linked (target : RuleId → String → Bool) (m : Mention) : Prop :=
  ∃ id destination, m.token = id.spelling ∧ m.link = some destination ∧
    target id destination = true

/-- `Mention.Linked`, decided. -/
def Mention.linked (target : RuleId → String → Bool) (m : Mention) : Bool :=
  match RuleId.parse? m.token, m.link with
  | some id, some destination => target id destination
  | _, _ => false

theorem Mention.linked_iff (target : RuleId → String → Bool) (m : Mention) :
    m.linked target = true ↔ m.Linked target := by
  unfold Mention.linked Mention.Linked
  split
  · rename_i id destination hid hlink
    constructor
    · intro h
      exact ⟨id, destination, (RuleId.spelling_of_parse hid).symm, hlink, h⟩
    · rintro ⟨id', destination', written, hlink', h⟩
      have hid' : RuleId.parse? m.token = some id' := written ▸ RuleId.parse_spelling id'
      rw [hid] at hid'
      rw [hlink] at hlink'
      cases hid'
      cases hlink'
      exact h
  · rename_i hnot
    constructor
    · intro h
      cases h
    · rintro ⟨id, destination, written, hlink, _⟩
      exact (hnot id destination (written ▸ RuleId.parse_spelling id) hlink).elim

/-- Every rule-ID token of run `r` is linked: at each place where the text of `r` has a rule-ID
token (`TokenAt`), that token is the spelling of a registered rule ID, and `r` lies in the text
of a link whose destination `target` accepts as that rule's page. The statement names no
function that reads tokens. `Run.mentions` computes them (`Run.mentions_linked_iff`). -/
def Run.Linked (target : RuleId → String → Bool) (r : Run) : Prop :=
  ∀ before chars after, r.text.toList = before ++ chars ++ after →
    TokenAt before.getLast? chars after →
      ∃ id destination, String.ofList chars = id.spelling ∧ r.link = some destination ∧
        target id destination = true

private theorem mentions_fold (link : Option String) (parts : List (String ⊕ String)) :
    ∀ (line start : Nat) (found : List Mention),
      ((parts.foldl (fun (acc : Nat × List Mention) part =>
          match part with
          | .inl text => (acc.1 + newlines text, acc.2)
          | .inr token => (acc.1, ⟨acc.1, token, link⟩ :: acc.2)) (line, found)).2).map
          (fun m => (m.token, m.link)) =
        ((tokenOffsets start parts).map fun p => (p.2, link)).reverse ++
          found.map fun m => (m.token, m.link) := by
  induction parts with
  | nil =>
    intro line start found
    simp [tokenOffsets]
  | cons part parts ih =>
    intro line start found
    cases part with
    | inl text =>
      rw [List.foldl_cons]
      simpa [tokenOffsets] using ih (line + newlines text) (start + text.length) found
    | inr token =>
      rw [List.foldl_cons]
      simp only []
      rw [ih line (start + token.length)]
      simp [tokenOffsets]

/-- The mentions of a run are linked exactly when the run is: `Run.mentions` returns the rule-ID
tokens of the run's text and no others (`mem_tokenOffsets_iff`), each with the run's link. -/
theorem Run.mentions_linked_iff (target : RuleId → String → Bool) (r : Run) :
    (∀ m ∈ r.mentions, m.Linked target) ↔ r.Linked target := by
  have tokens := mentions_fold r.link (splitTokens none 0 [] r.text.toList) r.line 0 []
  have viaTokens : (∀ m ∈ r.mentions, m.Linked target) ↔
      ∀ p ∈ r.mentions.map (fun m => (m.token, m.link)),
        ∃ id destination, p.1 = id.spelling ∧ p.2 = some destination ∧
          target id destination = true := by
    rw [List.forall_mem_map]
    exact Iff.rfl
  rw [viaTokens]
  unfold Run.mentions
  rw [List.map_reverse, tokens]
  simp only [List.map_nil, List.append_nil, List.reverse_reverse, List.forall_mem_map]
  constructor
  · intro h before chars after split at'
    exact h (before.length, String.ofList chars)
      ((mem_tokenOffsets_iff _ _ _).mpr ⟨before, chars, after, split, rfl, at', rfl⟩)
  · rintro h ⟨o, token⟩ found
    obtain ⟨before, chars, after, split, rfl, at', -⟩ := (mem_tokenOffsets_iff _ _ _).mp found
    exact h before chars after split at'

/-- The mentions of `runs` that are not linked, in document order. -/
@[regula_decision]
def bareMentions (target : RuleId → String → Bool) (runs : List Run) : List Mention :=
  (runs.flatMap Run.mentions).filter fun m => !m.linked target

/-- The executed check returns nothing exactly when every rule-ID token of every run is a
registered rule ID inside a link to that rule's page (`Run.Linked`). -/
theorem bareMentions_nil_iff (target : RuleId → String → Bool) (runs : List Run) :
    bareMentions target runs = [] ↔ ∀ run ∈ runs, run.Linked target := by
  simp only [bareMentions, List.filter_eq_nil_iff, List.mem_flatMap, Bool.not_eq_true',
    Bool.not_eq_false]
  constructor
  · intro h run hr
    exact (Run.mentions_linked_iff target run).mp fun m hm =>
      (Mention.linked_iff target m).mp (h m ⟨run, hr, hm⟩)
  · rintro h m ⟨run, hr, hm⟩
    exact (Mention.linked_iff target m).mpr
      ((Run.mentions_linked_iff target run).mpr (h run hr) m hm)

/-- Registered contract of the executed prose check, as a two-way decision over the page
predicate and the runs (`bareMentions_nil_iff`): it reports nothing for no run, and reports a
bare rule ID in a run outside every link. -/
theorem checked_bareMentions : Regula.ExecutableContract bareMentions (fun run =>
    Regula.Decides (· = [])
      (fun input : (RuleId → String → Bool) × List Run =>
        ∀ r ∈ input.2, r.Linked input.1)
      (Function.uncurry run)) :=
  ⟨.of_iff (fun input => bareMentions_nil_iff input.1 input.2)
    ⟨(fun _ _ => false, []), (bareMentions_nil_iff _ []).mpr (by simp)⟩
    ⟨(fun _ _ => false, [⟨1, "RG1001", none⟩]),
      (by decide +kernel : ¬ bareMentions (fun _ _ => false) [⟨1, "RG1001", none⟩] = [])⟩⟩

/-- Why a mention that is not linked is refused. -/
def Mention.reason (m : Mention) : String :=
  match RuleId.parse? m.token, m.link with
  | none, _ => "is not a registered rule ID"
  | some _, none => "is a bare rule ID in prose; make it a link to its rule page"
  | some _, some destination => s!"is linked to {destination}, which is not its rule page"

/-- What a refused mention reports: the file, the line, the ID and why it is refused. -/
def Mention.describe (file : String) (m : Mention) : String :=
  s!"{file}:{m.line}: {m.token} " ++ m.reason

/-! ## Rule pages -/

/-- Whether `destination`, a link of the rendered page `page`, resolves to rule `id`'s page file
in the edition whose artifact root is `root`, with any fragment. -/
def pageTarget (root : String) (page : Page) (id : RuleId) (destination : String) : Bool :=
  match resolve page destination with
  | .internal file _ => file == root ++ id.route ++ "index.html"
  | _ => false

/-- In edition `e`, the accepted destinations are exactly those that resolve to the rule's page
file of that edition (`Edition.pageFile`), so a rendered page links within its own edition. -/
theorem pageTarget_iff (e : Edition) (page : Page) (id : RuleId) (destination : String) :
    pageTarget e.root page id destination = true ↔
      ∃ fragment, resolve page destination = .internal (e.pageFile id) fragment := by
  unfold pageTarget
  cases resolve page destination with
  | external => simp
  | invalid reason => simp
  | internal file fragment =>
    simp only [beq_iff_eq, Target.internal.injEq, Edition.pageFile, Edition.pagePath]
    constructor
    · intro h
      exact ⟨fragment, h, rfl⟩
    · rintro ⟨_, h, _⟩
      exact h

/-! ## HTML prose -/

/-- The elements whose text is not prose: code and pasted output. The text of `script` and `style`
elements is never read. -/
def exemptElement (name : String) : Bool := ["code", "pre"].contains name

/-- The elements that name the page itself: its title and its top heading. -/
def namingElement (name : String) : Bool := ["title", "h1"].contains name

/-- The destination that the title and top heading of the rendered file `path` are read as linked
to, in the edition whose artifact root is `root`: the file itself when it is a rule's page, and
none otherwise. A page cannot usefully link to itself, so a rule's own ID in its own page's title
and top heading is the one rule ID in prose that is not written as a link. A heading of any other
page, any other heading of a rule's page and any other rule's ID are prose like the rest. -/
def ownPage (root path : String) : Option String :=
  if RuleId.all.any fun id => path == root ++ id.route ++ "index.html" then
    some (basePath ++ path)
  else none

/-- The state of the prose scan of an HTML page. -/
structure HtmlScan where
  /-- Whether the scan is in markup, a comment or a raw-text element. -/
  mode : ScanMode
  /-- The number of open exempt elements. -/
  exempt : Nat
  /-- The number of open elements that name the page (`namingElement`). -/
  naming : Nat
  /-- The destination the text of those elements is read as linked to (`ownPage`), if any. -/
  own : Option String
  /-- The `href` of the open `a` element, if there is one. -/
  link : Option String
  /-- The 1-based line at the scan position. -/
  line : Nat
  /-- The runs found so far, last first. -/
  runs : List Run

private def HtmlScan.withText (s : HtmlScan) (line : Nat) (text : String) : List Run :=
  if s.exempt == 0 && !text.isEmpty then
    ⟨line, text, s.link <|> (if s.naming == 0 then none else s.own)⟩ :: s.runs
  else s.runs

private def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\t' || c == '\r' || c == '\x0c'

/-- Read `chunk`, the text between one `<` and the next: the tag, comment or raw text it
continues, and then the text after it. -/
def htmlStep (s : HtmlScan) (chunk : String) : HtmlScan :=
  let next := s.line + newlines chunk
  let body := tagBody chunk.toList none
  let text := String.ofList (chunk.toList.drop (body.length + 1))
  let textLine := s.line + body.count '\n'
  let afterComment : Option (Nat × String) :=
    match chunk.splitOn "-->" with
    | before :: after :: rest => some (s.line + newlines before, "-->".intercalate (after :: rest))
    | _ => none
  let endComment (s : HtmlScan) : HtmlScan :=
    match afterComment with
    | some (line, text) => { s with mode := .markup, line := next, runs := s.withText line text }
    | none => { s with mode := .comment, line := next }
  let endTag (s : HtmlScan) : HtmlScan :=
    let name := (String.ofList ((body.drop 1).takeWhile fun c => !isSpace c)).toLower
    let closed := { s with
      mode := .markup,
      exempt := if exemptElement name then s.exempt - 1 else s.exempt,
      naming := if namingElement name then s.naming - 1 else s.naming,
      link := if name == "a" then none else s.link }
    { closed with line := next, runs := closed.withText textLine text }
  match s.mode with
  | .comment => endComment s
  | .raw element =>
    if chunk.toLower.startsWith ("/" ++ element) then endTag s else { s with line := next }
  | .markup =>
    if chunk.startsWith "!--" then endComment s
    else if chunk.startsWith "/" then endTag s
    else if chunk.startsWith "!" || chunk.startsWith "?" then
      { s with line := next, runs := s.withText textLine text }
    else
      let name := (String.ofList (body.takeWhile fun c => !(isSpace c || c == '/'))).toLower
      if name.isEmpty then { s with line := next, runs := s.withText s.line ("<" ++ chunk) } else
      let rest := body.drop name.length
      let tag : Tag := ⟨name, parseAttributes (rest.length + 1) rest⟩
      if name == "script" || name == "style" then { s with mode := .raw name, line := next } else
      let opened := { s with
        exempt := if exemptElement name && body.getLast? != some '/' then s.exempt + 1
          else s.exempt,
        naming := if namingElement name && body.getLast? != some '/' then s.naming + 1
          else s.naming,
        link := if name == "a" then tag.get? "href" else s.link }
      { opened with line := next, runs := opened.withText textLine text }

/-- The prose scan of a whole HTML page, whose title and top heading are read as linked to `own`. -/
def htmlScan (own : Option String) (html : String) : HtmlScan :=
  let start : HtmlScan :=
    { mode := .markup, exempt := 0, naming := 0, own, link := none, line := 1, runs := [] }
  match html.splitOn "<" with
  | [] => start
  | first :: chunks =>
    chunks.foldl htmlStep { start with line := 1 + newlines first, runs := start.withText 1 first }

/-- The prose of an HTML page: its text outside `exemptElement` elements, comments and `script`
and `style` elements, each run with the `href` of the `a` element it lies in or, in the title and
top heading (`namingElement`) outside an `a` element, with `own`. -/
def htmlRuns (own : Option String) (html : String) : List Run := (htmlScan own html).runs.reverse

/-- Whether the page's scan ends in markup with every exempt and naming element closed. An
unclosed `code` element, comment or script would hide the text after it, and an unclosed title or
top heading would read it as naming the page, so such a page is refused instead of read short. -/
def htmlClosed (html : String) : Bool :=
  match (htmlScan none html).mode with
  | .markup => (htmlScan none html).exempt == 0 && (htmlScan none html).naming == 0
  | _ => false

/-- What the rendered page `html` at artifact path `path` is refused for: an element, comment or
script that hides text and is never closed, and each rule ID in its prose that is not a link to
its page in the edition whose artifact root is `root`, reported with the path, its line and the
ID. A rule page's own title and top heading name its rule without a link (`ownPage`). -/
def htmlErrors (root path html : String) : List String :=
  (if htmlClosed html then [] else
    [s!"{path}: a code, pre, title or h1 element, a comment or a script is not closed, so the \
      text after it cannot be read as prose"]) ++
  (bareMentions (pageTarget root (Page.ofHtml path html)) (htmlRuns (ownPage root path) html)).map
    (·.describe path)

/-- The page check reports nothing exactly when the page's scan is closed and every rule-ID token
in the page's prose is a registered rule ID linked to its page under `root`, where the title and
top heading of a rule's own page count as linked to that page (`ownPage`). -/
theorem htmlErrors_nil_iff (root path html : String) :
    htmlErrors root path html = [] ↔ htmlClosed html = true ∧
      ∀ run ∈ htmlRuns (ownPage root path) html,
        run.Linked (pageTarget root (Page.ofHtml path html)) := by
  unfold htmlErrors
  cases htmlClosed html <;> simp [bareMentions_nil_iff]

/-! ## Generated prose -/

/-- Rule `id`'s ID as a link to its page, relative to the edition root (`RuleId.route`), in the
link syntax that Markdown and Verso share. A generated page resolves it through its
`<base href>`, so the same page links within whichever edition it is published in. -/
def relativeCitation (id : RuleId) : String := "[" ++ id.spelling ++ "](" ++ id.route ++ ")"

/-- `text` with each registered rule ID replaced by `rule` of it and all other text passed
through `plain`. -/
def rewriteIds (plain : String → String) (rule : RuleId → String) (text : String) : String :=
  String.join ((splitTokens none 0 [] text.toList).map fun
    | .inl between => plain between
    | .inr token => match RuleId.parse? token with
      | some id => rule id
      | none => plain token)

/-- One piece of generated prose. The pieces' texts, in order, are the text. -/
inductive Piece where
  /-- Prose, whose rule IDs `linkIds` makes links. -/
  | prose (text : String)
  /-- Text kept as written: a code span, an inline link or a bare URL. -/
  | kept (text : String)
  deriving DecidableEq, Repr

private def flush (acc : List Char) : List Piece :=
  if acc.isEmpty then [] else [.prose (String.ofList acc.reverse)]

/-- The number of characters through the end of the first run of exactly `n` backticks; `run` is
the length of the backtick run in progress. -/
def codeClose (n : Nat) : Nat → List Char → Option Nat
  | run, [] => if run == n then some 0 else none
  | run, c :: rest =>
    if c == '`' then (codeClose n (run + 1) rest).map (· + 1)
    else if run == n then some 0
    else (codeClose n 0 rest).map (· + 1)

/-- The index of the `closer` that matches an opener already read, counting nested pairs and
skipping each character a backslash escapes; `depth` is the number of nested openers still open. -/
def closeIndex (opener closer : Char) : Nat → List Char → Option Nat
  | _, [] => none
  | depth, '\\' :: _ :: rest => (closeIndex opener closer depth rest).map (· + 2)
  | depth, c :: rest =>
    if c == closer then
      match depth with
      | 0 => some 0
      | d + 1 => (closeIndex opener closer d rest).map (· + 1)
    else (closeIndex opener closer (if c == opener then depth + 1 else depth) rest).map (· + 1)

/-- Whether `chars` starts a bare URL. -/
def startsUrl (chars : List Char) : Bool :=
  "https://".toList.isPrefixOf chars || "http://".toList.isPrefixOf chars

/-- The length of the URL at the head of `chars`: up to whitespace, a bracket, a quote or a
backtick. -/
def urlLength (chars : List Char) : Nat :=
  (chars.takeWhile fun c => !(c.isWhitespace || c == '<' || c == '>' || c == '(' || c == ')' ||
    c == '[' || c == ']' || c == '`' || c == '"')).length

/-- The number of characters after a `[` through the end of the inline link `[text](target)` it
opens, when it opens one. -/
def linkLength (rest : List Char) : Option Nat :=
  (closeIndex '[' ']' 0 rest).bind fun i =>
    match rest.drop (i + 1) with
    | '(' :: tail => (closeIndex '(' ')' 0 tail).map (i + · + 3)
    | _ => none

/-- The pieces of generated prose: its prose and, kept as written, its code spans, inline links
and bare URLs. `acc` is the prose since the last piece, reversed; the first argument bounds the
steps and is at least the text's length. A backslash keeps the character after it as prose. -/
def scanGenerated : Nat → List Char → List Char → List Piece
  | 0, _, acc => flush acc
  | _, [], acc => flush acc
  | fuel + 1, c :: rest, acc =>
    let keep (n : Nat) : List Piece := flush acc ++
      Piece.kept (String.ofList ((c :: rest).take n)) :: scanGenerated fuel ((c :: rest).drop n) []
    if c == '\\' then
      match rest with
      | d :: tail => scanGenerated fuel tail (d :: c :: acc)
      | [] => flush (c :: acc)
    else if c == '`' then
      let n := 1 + (rest.takeWhile (· == '`')).length
      match codeClose n 0 (rest.drop (n - 1)) with
      | some k => keep (n + k)
      | none => scanGenerated fuel (rest.drop (n - 1)) (List.replicate n '`' ++ acc)
    else if startsUrl (c :: rest) then keep (urlLength (c :: rest))
    else if c == '[' then
      match linkLength rest with
      | some k => keep (k + 1)
      | none => scanGenerated fuel rest (c :: acc)
    else scanGenerated fuel rest (c :: acc)

/-- Generated prose, in the link syntax Markdown and Verso share, with each registered rule ID in
its prose (`scanGenerated`) replaced by `rule` of it. Code spans, inline links and bare URLs are
kept as written. -/
def linkIds (rule : RuleId → String) (text : String) : String :=
  String.join ((scanGenerated (text.length + 1) text.toList []).map fun
    | .prose between => rewriteIds id rule between
    | .kept raw => raw)

/-- Generated Verso prose with each registered rule ID in prose made a link to its page in the
same edition (`relativeCitation`). -/
def linkVerso (text : String) : String := linkIds relativeCitation text

/-! Evaluated controls (observations of the compiled scanners, not proofs). A bare ID in a page's
prose is refused with its file and line; a link to another page is refused; a heading is prose, so
a bare ID in one is refused, except a rule's own ID in the title and top heading of its own page;
and each exempt construct is accepted: code, pasted tool output, a rule index table whose IDs are
links, comments and scripts. -/
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard htmlErrors "dev/" "dev/enforcement/index.html"
    "<base href=\"./../\"><title>RG2003</title><h1>About RG2003</h1><h2>RG2003 and warnings</h2>" ==
  List.replicate 3
    "dev/enforcement/index.html:1: RG2003 is a bare rule ID in prose; make it a link to its rule \
      page"
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard htmlErrors "dev/" "dev/rules/RG1001/index.html"
    "<base href=\"./../../\"><h1>RG1001: like RG1002</h1><h2>RG1001 again</h2>" ==
  ["dev/rules/RG1001/index.html:1: RG1002 is linked to /regula/dev/rules/RG1001/index.html, \
      which is not its rule page",
    "dev/rules/RG1001/index.html:1: RG1001 is a bare rule ID in prose; make it a link to its rule \
      page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard htmlErrors "dev/" "dev/enforcement/index.html"
    "<base href=\"./../\"><p>It is\nreported as RG2003.</p>" ==
  ["dev/enforcement/index.html:2: RG2003 is a bare rule ID in prose; make it a link to its rule \
    page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard htmlErrors "dev/" "dev/enforcement/index.html"
    "<base href=\"./../\"><p>See <a href=\"rules/RG2003/\">RG2003</a> and \
      <a href=\"rules/RG2003/#RG2003-fix\">the RG2003 fix</a>.</p>" == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard htmlErrors "dev/" "dev/enforcement/index.html"
    "<base href=\"./../\"><p><a href=\"rules/RG2002/\">RG2003</a> and \
      <a href=\"https://rbeauchamp.github.io/regula/dev/rules/RG2003/\">RG2003</a></p>" != []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard htmlErrors "dev/" "dev/rules/RG1001/index.html"
    "<base href=\"./../../\"><title>RG1001: Axioms</title><h1>RG1001: Axioms</h1>\
      <p><code>RG1001</code> <code class=\"hl lean\">Regula.RG1001</code></p>\
      <pre>RG1001 [violation]</pre><script>var a = \"RG1001\";</script><!-- RG1001 -->\
      <table><tr><th><a href=\"rules/RG1002/\"><code>RG1002</code></a></th>\
      <td><a href=\"rules/RG1002/\">RG1002</a></td></tr></table>" == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard htmlErrors "dev/" "dev/index.html" "<p>Text <code>x</p><p>RG1001</p>" != []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkVerso "RG2003 rejects `RG1002` code, [RG1005's page](rules/RG1005/) and \
    https://x/rules/RG1001/; RG9999 stays." ==
  "[RG2003](rules/RG2003/) rejects `RG1002` code, [RG1005's page](rules/RG1005/) and \
    https://x/rules/RG1001/; RG9999 stays."
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard htmlErrors "" "6-code-organization/index.html"
    ("<base href=\"./../\"><p><a href=\"" ++ RuleId.sourceBuild.route ++ "\">RG2003</a></p>") == []

end Regula.Prose
